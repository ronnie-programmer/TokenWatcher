const express = require('express');
const fs = require('fs');
const path = require('path');
const readline = require('readline');
const chokidar = require('chokidar');
const os = require('os');

const TERMINAL_MODE = process.argv.includes('--terminal') || process.argv.includes('-t');

const app = express();
const PORT = 3737;
const HOST = '127.0.0.1';
const PROJECTS_DIR = path.join(os.homedir(), '.claude', 'projects');

// Public Anthropic API list prices, USD per 1M tokens.
// cacheWrite is the 5-minute TTL rate; a 1h-TTL cache write costs more and is
// not distinguished here (the JSONL does not record the TTL).
const PRICING = {
  'claude-fable-5-1':  { input: 10.00, output: 50.00, cacheWrite: 12.50, cacheRead: 0.25 },
  'claude-fable-5':    { input: 10.00, output: 50.00, cacheWrite: 12.50, cacheRead: 1.00 },
  'claude-opus-5':     { input: 5.00,  output: 25.00, cacheWrite: 6.25,  cacheRead: 0.50 },
  'claude-opus-4-8':   { input: 5.00,  output: 25.00, cacheWrite: 6.25,  cacheRead: 0.50 },
  'claude-opus-4-7':   { input: 5.00,  output: 25.00, cacheWrite: 6.25,  cacheRead: 0.50 },
  'claude-opus-4-6':   { input: 5.00,  output: 25.00, cacheWrite: 6.25,  cacheRead: 0.50 },
  'claude-sonnet-5':   { input: 2.00,  output: 10.00, cacheWrite: 2.50,  cacheRead: 0.20 },
  'claude-sonnet-4-6': { input: 3.00,  output: 15.00, cacheWrite: 3.75,  cacheRead: 0.30 },
  'claude-sonnet-4-5': { input: 3.00,  output: 15.00, cacheWrite: 3.75,  cacheRead: 0.30 },
  'claude-haiku-4-5':  { input: 1.00,  output: 5.00,  cacheWrite: 1.25,  cacheRead: 0.10 },
};

// Used when a model id matches nothing above. Kept separate from PRICING so an
// unpriced model can never be silently mistaken for a real match.
const FALLBACK_PRICING = { input: 3.00, output: 15.00, cacheWrite: 3.75, cacheRead: 0.30 };

// Longest prefix first, so 'claude-fable-5-1' is not swallowed by 'claude-fable-5'.
const PRICING_KEYS = Object.keys(PRICING).sort((a, b) => b.length - a.length);

// Model ids seen in the logs that we have no published price for. Surfaced in
// the payload so the UI can mark those numbers as guesses instead of hiding it.
const unpricedModels = new Set();

const EDIT_TOOLS = new Set(['Edit', 'Write', 'MultiEdit', 'NotebookEdit']);

function getPricing(model) {
  if (!model) return FALLBACK_PRICING;
  for (const key of PRICING_KEYS) {
    if (model.startsWith(key)) return PRICING[key];
  }
  unpricedModels.add(model);
  return FALLBACK_PRICING;
}

function calcCost(usage, model) {
  const p = getPricing(model);
  const M = 1_000_000;
  return (
    (usage.input_tokens || 0) / M * p.input +
    (usage.output_tokens || 0) / M * p.output +
    (usage.cache_creation_input_tokens || 0) / M * p.cacheWrite +
    (usage.cache_read_input_tokens || 0) / M * p.cacheRead
  );
}

// Convert a ~/.claude/projects folder name into a readable project name.
// Folder format: absolute path with every / replaced by -, e.g. -Users-ron-Coding-Practice
function projectDisplayName(folderName) {
  const homeEncoded = os.homedir().slice(1).replace(/\//g, '-');
  let name = folderName.startsWith('-' + homeEncoded + '-')
    ? folderName.slice(homeEncoded.length + 2)
    : folderName;
  name = name.replace(/--claude-worktrees-[\w-]+$/, '');
  name = name.replace(/^Coding-Projects-/, '').replace(/^Coding-/, '');
  return name || folderName;
}

const emptyHeatmap = () => Array.from({ length: 7 }, () => new Array(24).fill(0));

// Calendar date in THIS machine's timezone. Timestamps in the JSONL are UTC, so
// slicing the ISO string would roll the day over at UTC midnight and disagree
// with the heatmap (which has always been local). Everything buckets local now.
function localDate(d) {
  return `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, '0')}-${String(d.getDate()).padStart(2, '0')}`;
}

// Pull readable text out of a user message; '' if it's a tool result / non-text.
function userPromptText(msg) {
  const c = msg.content;
  if (typeof c === 'string') return c.trim();
  if (Array.isArray(c)) {
    const texts = c.filter(b => b && b.type === 'text').map(b => b.text || '');
    return texts.join(' ').trim();
  }
  return '';
}

// A "real" user prompt = a typed message, not a tool_result and not a system-injected block.
function isUserPrompt(record) {
  const msg = record.message;
  if (!msg || msg.role !== 'user') return false;
  if (record.isSidechain || record.isMeta) return false;
  const text = userPromptText(msg);
  if (!text) return false;
  // Skip slash-command wrappers and harness-injected blocks
  if (/^<(command|local-command|user-prompt-submit)/i.test(text)) return false;
  if (/^Caveat: The messages below/i.test(text)) return false;
  return true;
}

// `seenMsgIds` is owned by the caller so a response that Claude Code replayed
// into a second .jsonl (resumed sessions copy their history) is counted once
// across the whole scan, not once per file.
async function parseSessionFile(filePath, projectName, seenMsgIds) {
  const sessions = {};
  const daily = {};
  const tasks = [];
  const messages = [];          // assistant messages: { sid, project, ts, out, cost }
  const toolCounts = {};        // name -> { count, outTokens }
  const fileEdits = {};         // `${sid}::${file}` -> { sid, project, file, edits }
  const byModel = {};           // model -> token/cost rollup, attributed per message
  const heatmapCost = emptyHeatmap();
  const heatmapMsgs = emptyHeatmap();
  const seenPrompts = new Set();

  let currentTask = null;
  const closeTask = () => {
    if (currentTask && (currentTask.cost > 0 || currentTask.toolCalls > 0)) tasks.push(currentTask);
    currentTask = null;
  };

  const stream = fs.createReadStream(filePath, { encoding: 'utf8' });
  const rl = readline.createInterface({ input: stream, crlfDelay: Infinity });

  for await (const line of rl) {
    if (!line.trim()) continue;
    let record;
    try { record = JSON.parse(line); } catch { continue; }

    const sessionId = record.sessionId || 'unknown';
    const ts = record.timestamp || null;

    // ── User prompt → starts a new task ──────────────────────────────────────
    if (isUserPrompt(record)) {
      const text = userPromptText(record.message);
      // Branch-duplicated prompts share a timestamp; a genuinely retyped prompt
      // ("continue", "yes", "fix it") does not. Keying on text alone dropped the
      // repeat AND folded its tokens into the previous task.
      const key = sessionId + '::' + (ts || '') + '::' + text.slice(0, 120);
      if (seenPrompts.has(key)) continue; // dedup branch-duplicated prompts
      seenPrompts.add(key);
      closeTask();
      currentTask = {
        sid: sessionId, project: projectName, ts,
        promptPreview: text.replace(/\s+/g, ' ').slice(0, 90),
        cost: 0, inputTokens: 0, outputTokens: 0,
        toolCalls: 0, assistantTurns: 0, endTs: ts,
      };
      continue;
    }

    // ── Assistant message with usage ─────────────────────────────────────────
    const msg = record.message;
    if (!msg || !msg.usage) continue;
    if (msg.id) {
      if (seenMsgIds.has(msg.id)) continue; // dedup branch-duplicated responses
      seenMsgIds.add(msg.id);
    }

    const model = msg.model || 'unknown';
    const usage = msg.usage;
    const out = usage.output_tokens || 0;
    const cost = calcCost(usage, model);

    // Session rollup
    if (!sessions[sessionId]) {
      sessions[sessionId] = {
        sessionId, model, firstSeen: ts, lastSeen: ts,
        inputTokens: 0, outputTokens: 0, cacheWriteTokens: 0,
        cacheReadTokens: 0, totalCost: 0, messageCount: 0, project: projectName,
        modelCounts: {},
      };
    }
    const s = sessions[sessionId];
    s.modelCounts[model] = (s.modelCounts[model] || 0) + 1;

    // Per-model rollup is done per message, not per session: a session that
    // switches Opus -> Sonnet mid-run used to dump every token on whichever
    // model happened to answer first.
    if (!byModel[model]) {
      byModel[model] = {
        model, inputTokens: 0, outputTokens: 0, cacheWriteTokens: 0,
        cacheReadTokens: 0, totalCost: 0, sessionIds: new Set(),
      };
    }
    const bm = byModel[model];
    bm.inputTokens += usage.input_tokens || 0;
    bm.outputTokens += out;
    bm.cacheWriteTokens += usage.cache_creation_input_tokens || 0;
    bm.cacheReadTokens += usage.cache_read_input_tokens || 0;
    bm.totalCost += cost;
    bm.sessionIds.add(sessionId);
    s.inputTokens += usage.input_tokens || 0;
    s.outputTokens += out;
    s.cacheWriteTokens += usage.cache_creation_input_tokens || 0;
    s.cacheReadTokens += usage.cache_read_input_tokens || 0;
    s.totalCost += cost;
    s.messageCount++;

    // Tool calls in this assistant message
    const toolUses = Array.isArray(msg.content)
      ? msg.content.filter(b => b && b.type === 'tool_use')
      : [];
    const nTools = toolUses.length;
    const perToolOut = nTools ? out / nTools : 0;
    for (const tu of toolUses) {
      const name = tu.name || 'unknown';
      if (!toolCounts[name]) toolCounts[name] = { count: 0, outTokens: 0 };
      toolCounts[name].count++;
      toolCounts[name].outTokens += perToolOut;

      if (EDIT_TOOLS.has(name)) {
        const file = (tu.input && (tu.input.file_path || tu.input.notebook_path)) || 'unknown';
        const fk = sessionId + '::' + file;
        if (!fileEdits[fk]) fileEdits[fk] = { sid: sessionId, project: projectName, file, edits: 0 };
        fileEdits[fk].edits++;
      }
    }

    // Per-message record (runaway detection + live burn rate)
    messages.push({ sid: sessionId, project: projectName, ts, out, cost, tools: nTools });

    // Attach to the open task
    if (currentTask) {
      currentTask.cost += cost;
      currentTask.inputTokens += usage.input_tokens || 0;
      currentTask.outputTokens += out;
      currentTask.toolCalls += nTools;
      currentTask.assistantTurns++;
      if (ts) currentTask.endTs = ts;
    }

    // Time series + heatmaps
    if (ts) {
      if (!s.firstSeen || ts < s.firstSeen) s.firstSeen = ts;
      if (!s.lastSeen || ts > s.lastSeen) s.lastSeen = ts;
      const d = new Date(ts);            // local time of this machine
      const date = localDate(d);
      if (!daily[date]) daily[date] = { date, cost: 0, inputTokens: 0, outputTokens: 0, messages: 0 };
      daily[date].cost += cost;
      daily[date].inputTokens += usage.input_tokens || 0;
      daily[date].outputTokens += out;
      daily[date].messages++;

      const dow = d.getDay(), hr = d.getHours();
      heatmapCost[dow][hr] += cost;
      heatmapMsgs[dow][hr] += 1;
    }
  }
  closeTask();

  // Label each session with the model that answered most of its messages, and
  // keep the full list so a mixed session is visibly mixed.
  for (const s of Object.values(sessions)) {
    const entries = Object.entries(s.modelCounts).sort((a, b) => b[1] - a[1]);
    if (entries.length) s.model = entries[0][0];
    s.models = entries.map(([m]) => m);
    delete s.modelCounts;
  }

  return { sessions: Object.values(sessions), daily, tasks, messages, toolCounts, fileEdits, byModel, heatmapCost, heatmapMsgs };
}

function mergeHeatmap(target, src) {
  for (let d = 0; d < 7; d++) for (let h = 0; h < 24; h++) target[d][h] += src[d][h];
}

async function scanAll() {
  const all = {
    sessions: [], daily: {}, tasks: [], messages: [],
    toolCounts: {}, fileEdits: {}, byModel: {},
    heatmapCost: emptyHeatmap(), heatmapMsgs: emptyHeatmap(),
  };
  if (!fs.existsSync(PROJECTS_DIR)) return all;

  // Shared across every file in the scan so replayed history is not double-counted.
  const seenMsgIds = new Set();

  for (const proj of fs.readdirSync(PROJECTS_DIR)) {
    const projPath = path.join(PROJECTS_DIR, proj);
    let files;
    try { files = fs.readdirSync(projPath); }
    catch (err) { console.warn(`Skipped project ${proj}: ${err.message}`); continue; }
    const projectName = projectDisplayName(proj);

    for (const file of files) {
      if (!file.endsWith('.jsonl')) continue;
      try {
        const r = await parseSessionFile(path.join(projPath, file), projectName, seenMsgIds);
        all.sessions.push(...r.sessions);
        all.tasks.push(...r.tasks);
        all.messages.push(...r.messages);
        for (const [date, d] of Object.entries(r.daily)) {
          if (!all.daily[date]) all.daily[date] = { date, cost: 0, inputTokens: 0, outputTokens: 0, messages: 0 };
          all.daily[date].cost += d.cost;
          all.daily[date].inputTokens += d.inputTokens;
          all.daily[date].outputTokens += d.outputTokens;
          all.daily[date].messages += d.messages;
        }
        for (const [name, t] of Object.entries(r.toolCounts)) {
          if (!all.toolCounts[name]) all.toolCounts[name] = { count: 0, outTokens: 0 };
          all.toolCounts[name].count += t.count;
          all.toolCounts[name].outTokens += t.outTokens;
        }
        for (const [fk, fe] of Object.entries(r.fileEdits)) {
          if (!all.fileEdits[fk]) all.fileEdits[fk] = { ...fe, edits: 0 };
          all.fileEdits[fk].edits += fe.edits;
        }
        for (const [name, m] of Object.entries(r.byModel)) {
          if (!all.byModel[name]) {
            all.byModel[name] = {
              model: name, inputTokens: 0, outputTokens: 0, cacheWriteTokens: 0,
              cacheReadTokens: 0, totalCost: 0, sessionIds: new Set(),
            };
          }
          const t = all.byModel[name];
          t.inputTokens += m.inputTokens;
          t.outputTokens += m.outputTokens;
          t.cacheWriteTokens += m.cacheWriteTokens;
          t.cacheReadTokens += m.cacheReadTokens;
          t.totalCost += m.totalCost;
          for (const sid of m.sessionIds) t.sessionIds.add(sid);
        }
        mergeHeatmap(all.heatmapCost, r.heatmapCost);
        mergeHeatmap(all.heatmapMsgs, r.heatmapMsgs);
      } catch (err) {
        console.warn(`Skipped session file ${file}: ${err.message}`);
      }
    }
  }
  return all;
}

function aggregateStats(scan) {
  const { sessions, daily, tasks, messages, toolCounts, fileEdits, byModel, heatmapCost, heatmapMsgs } = scan;

  const totals = {
    inputTokens: 0, outputTokens: 0, cacheWriteTokens: 0,
    cacheReadTokens: 0, totalCost: 0, messageCount: 0,
    sessionCount: sessions.length,
  };
  const byProject = {};

  for (const s of sessions) {
    totals.inputTokens += s.inputTokens;
    totals.outputTokens += s.outputTokens;
    totals.cacheWriteTokens += s.cacheWriteTokens;
    totals.cacheReadTokens += s.cacheReadTokens;
    totals.totalCost += s.totalCost;
    totals.messageCount += s.messageCount;

    const p = s.project || 'unknown';
    if (!byProject[p]) byProject[p] = { project: p, inputTokens: 0, outputTokens: 0, totalCost: 0, sessions: 0 };
    byProject[p].inputTokens += s.inputTokens;
    byProject[p].outputTokens += s.outputTokens;
    byProject[p].totalCost += s.totalCost;
    byProject[p].sessions++;
  }

  const byTool = Object.entries(toolCounts)
    .map(([tool, t]) => ({ tool, count: t.count, avgOutputTokens: t.count ? Math.round(t.outTokens / t.count) : 0 }))
    .sort((a, b) => b.count - a.count);

  // Top tasks by cost (keep payload reasonable)
  const topTasks = tasks.slice().sort((a, b) => b.cost - a.cost).slice(0, 100);

  // File edits worth sending (>= 2 so the thrash slider can go as low as 2)
  const editList = Object.values(fileEdits)
    .filter(f => f.edits >= 2)
    .sort((a, b) => b.edits - a.edits)
    .slice(0, 100);

  const dailyArr = Object.values(daily).sort((a, b) => a.date.localeCompare(b.date));

  const modelList = Object.values(byModel)
    .map(({ sessionIds, ...m }) => ({ ...m, sessions: sessionIds.size, estimated: unpricedModels.has(m.model) }))
    .sort((a, b) => b.totalCost - a.totalCost);

  return {
    totals,
    byModel: modelList,
    unpricedModels: [...unpricedModels],
    byProject: Object.values(byProject).sort((a, b) => b.totalCost - a.totalCost),
    byTool,
    sessions,
    daily: dailyArr,
    tasks: topTasks,
    taskCount: tasks.length,
    messages,
    fileEdits: editList,
    heatmap: { cost: heatmapCost, messages: heatmapMsgs },
  };
}

const clients = new Set();

function broadcast(data) {
  const msg = `data: ${JSON.stringify(data)}\n\n`;
  for (const res of clients) { try { res.write(msg); } catch {} }
}

let lastStats = null;
let isScanning = false;
let rescanQueued = false;

// A file change landing mid-scan used to be dropped outright, leaving the
// dashboard stale until the *next* write. Queue it and loop instead.
async function withScan(onStats, onError) {
  if (isScanning) { rescanQueued = true; return; }
  isScanning = true;
  try {
    do {
      rescanQueued = false;
      const scan = await scanAll();
      lastStats = { ...aggregateStats(scan), updatedAt: new Date().toISOString() };
      onStats(lastStats);
    } while (rescanQueued);
  } catch (err) {
    onError(err);
  } finally {
    isScanning = false;
  }
}

function refresh() {
  return withScan(
    stats => broadcast({ type: 'update', ...stats }),
    err => console.error('Scan error:', err.message),
  );
}

// chokidar fires repeatedly while a session file is being appended to; coalesce.
function debounce(fn, ms) {
  let timer = null;
  return () => { clearTimeout(timer); timer = setTimeout(fn, ms); };
}

function watchProjects(handler) {
  const onChange = debounce(handler, 300);
  return chokidar.watch(PROJECTS_DIR, {
    ignored: /[/\\]\./,
    persistent: true,
    ignoreInitial: true,
    depth: 2,
    usePolling: false,
  }).on('add', onChange).on('change', onChange);
}

app.use(express.static(path.join(__dirname, 'public')));

app.get('/api/stats', async (req, res) => {
  if (lastStats) return res.json(lastStats);
  const scan = await scanAll();
  lastStats = { ...aggregateStats(scan), updatedAt: new Date().toISOString() };
  res.json(lastStats);
});

app.get('/api/events', (req, res) => {
  res.setHeader('Content-Type', 'text/event-stream');
  res.setHeader('Cache-Control', 'no-cache');
  res.setHeader('Connection', 'keep-alive');
  res.flushHeaders();
  clients.add(res);
  if (lastStats) res.write(`data: ${JSON.stringify({ type: 'update', ...lastStats })}\n\n`);
  req.on('close', () => clients.delete(res));
});

// Comment-only keepalive: without traffic an idle SSE connection gets reaped and
// the dashboard silently falls back to its 3s reconnect loop.
setInterval(() => {
  for (const res of clients) { try { res.write(': ping\n\n'); } catch {} }
}, 25_000).unref();

// ── Terminal UI ──────────────────────────────────────────────────────────────

const C = {
  reset:   '\x1b[0m',
  bold:    '\x1b[1m',
  dim:     '\x1b[2m',
  green:   '\x1b[32m',
  cyan:    '\x1b[36m',
  yellow:  '\x1b[33m',
  magenta: '\x1b[35m',
  blue:    '\x1b[34m',
  white:   '\x1b[37m',
  bgBlack: '\x1b[40m',
  red:     '\x1b[31m',
};

function fmt$(n)   { return `${C.green}${C.bold}$${n.toFixed(4)}${C.reset}`; }
function fmtM(n)   { return `${C.cyan}${(n / 1_000_000).toFixed(3)}M${C.reset}`; }
function bar(val, max, width = 20) {
  const filled = max > 0 ? Math.round((val / max) * width) : 0;
  return C.green + '█'.repeat(filled) + C.dim + '░'.repeat(width - filled) + C.reset;
}
function pad(str, len) {
  const plain = str.replace(/\x1b\[[0-9;]*m/g, '');
  return str + ' '.repeat(Math.max(0, len - plain.length));
}

function renderTerminal(stats) {
  const { totals, byProject, byModel, byTool, daily, sessions } = stats;
  const cols = process.stdout.columns || 80;
  const divider = C.dim + '─'.repeat(cols) + C.reset;

  const lines = [];
  const push = (...parts) => lines.push(parts.join(''));

  // Header
  push(C.bold + C.bgBlack + C.cyan, '  Claude Token Tracker  ', C.reset,
       C.dim, '  live • ', new Date().toLocaleTimeString(), C.reset);
  push(divider);

  // Totals row
  push(
    C.bold, '  Total Cost: ', fmt$(totals.totalCost), '   ',
    'Sessions: ', C.yellow, totals.sessionCount, C.reset, '   ',
    'Messages: ', C.yellow, totals.messageCount, C.reset,
  );
  push(
    '  Input: ', fmtM(totals.inputTokens), '  ',
    'Output: ', fmtM(totals.outputTokens), '  ',
    'Cache Read: ', fmtM(totals.cacheReadTokens),
  );
  push(divider);

  // Projects
  const topProjects = (byProject || []).slice(0, 8);
  if (topProjects.length) {
    const maxCost = topProjects[0].totalCost || 1;
    push(C.bold + C.white, '  Projects', C.reset);
    for (const p of topProjects) {
      push(
        '  ', pad(C.cyan + (p.project || 'unknown').slice(0, 30) + C.reset, 42),
        bar(p.totalCost, maxCost, 16), '  ',
        fmt$(p.totalCost), C.dim, `  (${p.sessions} sess)`, C.reset,
      );
    }
    push(divider);
  }

  // Models
  const topModels = (byModel || []).sort((a, b) => b.totalCost - a.totalCost).slice(0, 4);
  if (topModels.length) {
    push(C.bold + C.white, '  Models', C.reset);
    for (const m of topModels) {
      const label = (m.model || 'unknown').replace('claude-', '').slice(0, 28);
      push(
        '  ', pad(C.magenta + label + C.reset, 42),
        fmt$(m.totalCost), C.dim, `  in:${(m.inputTokens/1e6).toFixed(2)}M  out:${(m.outputTokens/1e6).toFixed(2)}M`, C.reset,
      );
    }
    push(divider);
  }

  // Top tools
  const topTools = (byTool || []).slice(0, 6);
  if (topTools.length) {
    push(C.bold + C.white, '  Top Tools', C.reset);
    const maxCount = topTools[0].count || 1;
    for (const t of topTools) {
      push(
        '  ', pad(C.yellow + (t.tool || '?').slice(0, 22) + C.reset, 34),
        bar(t.count, maxCount, 12), '  ',
        C.dim, String(t.count).padStart(5), ' calls', C.reset,
      );
    }
    push(divider);
  }

  // Recent daily costs (last 7 days)
  const recentDays = (daily || []).slice(-7);
  if (recentDays.length) {
    push(C.bold + C.white, '  Daily (last 7 days)', C.reset);
    const maxDay = Math.max(...recentDays.map(d => d.cost), 0.001);
    for (const d of recentDays) {
      push(
        '  ', C.dim, d.date, C.reset, '  ',
        bar(d.cost, maxDay, 18), '  ',
        fmt$(d.cost), C.dim, `  ${d.messages} msgs`, C.reset,
      );
    }
    push(divider);
  }

  push(C.dim, '  Press Ctrl+C to exit  •  Auto-refreshes on file change', C.reset);

  return lines.join('\n');
}

function drawTerminal(stats) {
  process.stdout.write('\x1b[2J\x1b[H'); // clear screen, cursor home
  process.stdout.write(renderTerminal(stats) + '\n');
}

// ── Launch ───────────────────────────────────────────────────────────────────

if (TERMINAL_MODE) {
  const termRefresh = () => withScan(
    drawTerminal,
    err => process.stderr.write('Scan error: ' + err.message + '\n'),
  );

  watchProjects(termRefresh);

  process.on('SIGINT', () => {
    process.stdout.write('\x1b[?25h\n');
    process.exit(0);
  });

  termRefresh();
} else {
  watchProjects(refresh);

  // Loopback only. The payload includes prompt previews, project names and
  // spend; binding 0.0.0.0 published all of that to anyone on the network.
  app.listen(PORT, HOST, async () => {
    const url = `http://localhost:${PORT}`;
    console.log(`Claude Token Tracker → ${url}`);
    await refresh();
    import('open').then(m => m.default(url)).catch(() => {});
  });
}
