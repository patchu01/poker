/* ════════════════════════════════════════════════════════════════════
   THE RIVER CLUB — room server
   Serves poker.html and runs the dealing engine for every table.
   Deployable to Render as-is (PORT is read from the environment).

     local:  npm install ws   →   node server.js   →   http://localhost:8787
     cloud:  push to GitHub → Render web service (see package.json)
   ════════════════════════════════════════════════════════════════════ */
const http = require('http');
const fs   = require('fs');
const path = require('path');
const os   = require('os');
const { WebSocketServer } = require('ws');

const PORT = process.env.PORT || 8787;
const PAGE = path.join(__dirname, 'poker.html');

/* ── shared helpers ── */
const esc = s => String(s).replace(/[&<>"']/g, c => ({'&':'&amp;','<':'&lt;','>':'&gt;','"':'&quot;',"'":'&#39;'}[c]));
const uid = () => Math.random().toString(36).slice(2, 10);
const fmt = n => (n || 0).toLocaleString('en-US');
const cleanName = s => esc(String(s || '').replace(/[<>&]/g, '').trim().slice(0, 14));

const SUITS = { s:'♠', h:'♥', d:'♦', c:'♣' };
const RCH = { 11:'J', 12:'Q', 13:'K', 14:'A' };
const rStr = r => RCH[r] || String(r);
const c2s = c => rStr(c.r) + SUITS[c.s];
const isRed = c => c.s === 'h' || c.s === 'd';
const cardTag = c => `<b class="ct ${isRed(c) ? 'r' : ''}">${c2s(c)}</b>`;

/* ── hand evaluation ── */
function score5(a, b, c, d, e){
  const cs = [a, b, c, d, e];
  const rs = cs.map(x => x.r).sort((x, y) => y - x);
  const flush = cs.every(x => x.s === cs[0].s);
  let stHigh = 0;
  if(rs[0] !== rs[1] && rs[1] !== rs[2] && rs[2] !== rs[3] && rs[3] !== rs[4]){
    if(rs[0] - rs[4] === 4) stHigh = rs[0];
    else if(rs[0] === 14 && rs[1] === 5 && rs[1] - rs[4] === 3) stHigh = 5;
  }
  const cnt = {};
  for(const x of rs) cnt[x] = (cnt[x] || 0) + 1;
  const g = Object.keys(cnt).map(r => ({ r:+r, n:cnt[r] })).sort((x, y) => y.n - x.n || y.r - x.r);
  let cat, k;
  if(flush && stHigh){ cat = 8; k = [stHigh]; }
  else if(g[0].n === 4){ cat = 7; k = [g[0].r, g[1].r]; }
  else if(g[0].n === 3 && g[1].n === 2){ cat = 6; k = [g[0].r, g[1].r]; }
  else if(flush){ cat = 5; k = rs; }
  else if(stHigh){ cat = 4; k = [stHigh]; }
  else if(g[0].n === 3){ cat = 3; k = [g[0].r, g[1].r, g[2].r]; }
  else if(g[0].n === 2 && g[1].n === 2){ cat = 2; k = [g[0].r, g[1].r, g[2].r]; }
  else if(g[0].n === 2){ cat = 1; k = [g[0].r, g[1].r, g[2].r]; }
  else { cat = 0; k = rs; }
  let s = cat;
  for(let i = 0; i < 5; i++) s = s * 15 + (k[i] || 0);
  return { s, cat, k };
}
const RW = {2:'Deuce',3:'Three',4:'Four',5:'Five',6:'Six',7:'Seven',8:'Eight',9:'Nine',10:'Ten',11:'Jack',12:'Queen',13:'King',14:'Ace'};
const pl = r => r === 6 ? 'Sixes' : RW[r] + 's';
function handName(cat, k){
  switch(cat){
    case 8: return k[0] === 14 ? 'a Royal Flush' : `a Straight Flush, ${RW[k[0]]} high`;
    case 7: return `Four of a Kind, ${pl(k[0])}`;
    case 6: return `a Full House, ${pl(k[0])} full of ${pl(k[1])}`;
    case 5: return `a Flush, ${RW[k[0]]} high`;
    case 4: return `a Straight, ${RW[k[0]]} high`;
    case 3: return `Three of a Kind, ${pl(k[0])}`;
    case 2: return `Two Pair, ${pl(k[0])} & ${pl(k[1])}`;
    case 1: return `a Pair of ${pl(k[0])}`;
    default: return `${RW[k[0]]} high`;
  }
}
function best5(cards){
  const N = cards.length;
  let bs = -1, bcat = 0, bk = null;
  for(let a = 0; a < N - 4; a++) for(let b = a + 1; b < N - 3; b++) for(let c = b + 1; c < N - 2; c++)
  for(let d = c + 1; d < N - 1; d++) for(let e = d + 1; e < N; e++){
    const r = score5(cards[a], cards[b], cards[c], cards[d], cards[e]);
    if(r.s > bs){ bs = r.s; bcat = r.cat; bk = r.k; }
  }
  return { score: bs, name: handName(bcat, bk) };
}
function newDeck(){
  const d = [];
  for(const s of 'shdc') for(let r = 2; r <= 14; r++) d.push({ r, s });
  for(let i = d.length - 1; i > 0; i--){
    const j = (Math.random() * (i + 1)) | 0;
    [d[i], d[j]] = [d[j], d[i]];
  }
  return d;
}

/* ── rooms ── */
const rooms = new Map();
let R = null;
const BOTNAMES = ['Dutch','Ruby','Marlowe','Slim','Cleo','Otis','Vee','Frankie','Nadia','Sol','Junie','Brick'];

function newCode(){
  let c;
  do { c = String(1000 + Math.floor(Math.random() * 9000)); } while(rooms.has(c));
  return c;
}
function createRoom(){
  const r = {
    code: newCode(), hostPid: null, players: [], phase: 'lobby', handNo: 0,
    sb: 10, bb: 20, buttonPid: null, deck: [], board: [], stage: '',
    potCollected: 0, currentBet: 0, minRaise: 20, turnPid: null,
    log: [], result: null, countdown: 0, timers: [], cdTimer: null, closed: false
  };
  rooms.set(r.code, r);
  console.log(`[room ${r.code}] opened`);
  return r;
}
function addPlayer(pid, name, bot){
  const p = {
    pid, name, bot, stack: 1000, bet: 0, committed: 0, cards: [],
    dealt: false, folded: true, allIn: false, out: false, acted: false,
    revealed: false, connected: true, lastSeen: Date.now(), ws: null
  };
  R.players.push(p);
  return p;
}
const byId = pid => R.players.find(p => p.pid === pid);
const actives = () => R.players.filter(p => p.dealt && !p.folded);
function nextAfter(pid, fn){
  const n = R.players.length;
  if(!n) return null;
  const i = pid ? R.players.findIndex(p => p.pid === pid) : -1;
  for(let k = 1; k <= n; k++){
    const q = R.players[(i + k) % n];
    if(fn(q)) return q;
  }
  return null;
}
function commit(p, amt){
  amt = Math.min(amt, p.stack);
  p.stack -= amt; p.bet += amt; p.committed += amt;
  if(p.stack === 0) p.allIn = true;
  return amt;
}
function hlog(html){ R.log.push(html); if(R.log.length > 80) R.log.splice(0, R.log.length - 80); }
function later(ms, fn){
  const r = R;
  r.timers.push(setTimeout(() => { if(!r.closed){ R = r; fn(); } }, ms));
}
function bcast(t, x){
  const msg = JSON.stringify({ t, from:'H', _i: uid(), ...(x || {}) });
  R.players.forEach(p => { if(p.ws && p.ws.readyState === 1) p.ws.send(msg); });
}
function sendState(){ bcast('state', { S: publicState() }); }
function sendTo(p, t, x){
  if(p.ws && p.ws.readyState === 1) p.ws.send(JSON.stringify({ t, _i: uid(), ...(x || {}) }));
}
function publicState(){
  const bets = R.players.reduce((s, p) => s + p.bet, 0);
  return {
    phase: R.phase, code: R.code, handNo: R.handNo, sb: R.sb, bb: R.bb, stage: R.stage,
    board: R.board.slice(), pot: R.potCollected + bets, currentBet: R.currentBet,
    minRaise: R.minRaise, turnPid: R.turnPid, log: R.log.slice(-16),
    result: R.result, countdown: R.countdown,
    seats: R.players.map(p => ({
      pid: p.pid, name: p.name, bot: p.bot, stack: p.stack, bet: p.bet,
      dealt: p.dealt, folded: p.folded, allIn: p.allIn, out: p.out,
      dealer: p.pid === R.buttonPid,
      cards: (p.revealed && p.dealt && !p.folded) ? p.cards.slice() : null
    }))
  };
}

/* ── message intake ── */
function handle(ws, m){
  if(!m || typeof m !== 'object') return;
  if(ws.room){
    const r = rooms.get(ws.room);
    if(r){ R = r; const p = byId(m.pid); if(p) p.lastSeen = Date.now(); }
  }
  switch(m.t){
    case 'host': {
      const r = createRoom();
      R = r;
      ws.room = r.code; ws.pid = m.pid;
      const p = addPlayer(m.pid, cleanName(m.name) || 'Dealer', false);
      r.hostPid = m.pid; p.ws = ws;
      hlog('<span class="dim">Table opened — waiting for players.</span>');
      sendTo(p, 'welcome', { to: m.pid, ok: true, code: r.code, host: true });
      sendState();
      break;
    }
    case 'hello': {
      const code = String(m.code || '').trim();
      const r = rooms.get(code);
      if(!r){ sendTo({ ws }, 'welcome', { to: m.pid, ok: false, reason: 'No table with code ' + code + ' is open right now.' }); return; }
      R = r;
      ws.room = code; ws.pid = m.pid;
      let p = byId(m.pid);
      if(!p){
        if(r.players.length >= 8){ sendTo({ ws }, 'welcome', { to: m.pid, ok: false, reason: 'That table is full (8 seats).' }); return; }
        p = addPlayer(m.pid, cleanName(m.name) || 'Player ' + (r.players.length + 1), false);
        hlog(`<b>${esc(p.name)}</b> sits down.`);
        console.log(`[room ${r.code}] ${p.name} joined`);
      } else {
        p.lastSeen = Date.now();          // refresh / reconnect — seat and stack kept
      }
      p.ws = ws;
      sendTo(p, 'welcome', { to: m.pid, ok: true, code, host: m.pid === r.hostPid });
      sendState();                        // state first, so a mid-hand reconnect keeps its hole cards
      if(r.phase === 'play' && p.dealt && !p.bot) sendTo(p, 'hole', { to: p.pid, cards: p.cards });
      break;
    }
    case 'act':   { const p = byId(m.pid); if(p) hostAct(p, m); break; }
    case 'ctrl':  {
      if(!R || m.pid !== R.hostPid) return;
      if(m.cmd === 'start') hostStart();
      else if(m.cmd === 'bot') hostBot();
      else if(m.cmd === 'next' && R.phase === 'handend'){
        if(R.cdTimer){ clearInterval(R.cdTimer); R.cdTimer = null; }
        nextHand();
      }
      break;
    }
    case 'ping':  break;
    case 'leave': hostLeave(m.pid); break;
  }
}

/* ── room lifecycle ── */
function hostStart(){
  if(R.phase !== 'lobby') return;
  const ready = R.players.filter(p => !p.out && p.stack > 0);
  if(ready.length < 2){ hlog('<span class="dim">Need at least two seated players to start.</span>'); sendState(); return; }
  hlog('<span class="dim">Game on. Blinds ' + R.sb + '/' + R.bb + ', stacks 1,000.</span>');
  startHand();
}
function hostBot(){
  if(R.players.length >= 8) return;
  const used = new Set(R.players.map(p => p.name));
  const nm = BOTNAMES.find(n => !used.has(n)) || ('House ' + uid().slice(0, 2).toUpperCase());
  addPlayer(uid(), nm, true);
  hlog(`<b>${esc(nm)}</b> <span class="dim">(house player)</span> sits down.`);
  sendState();
}
function hostLeave(pid){
  const p = byId(pid);
  if(!p) return;
  if(pid === R.hostPid){ closeRoom('The host closed the table.'); return; }
  const wasIn = R.phase === 'play' && p.dealt && !p.folded;
  p.folded = true;
  hlog(`<b>${esc(p.name)}</b> leaves the table.`);
  R.players = R.players.filter(x => x.pid !== pid);
  if(wasIn) afterAct(p); else sendState();
  if(R.players.length === 0) closeRoom(null, true);
}
function closeRoom(reason, silent){
  const r = R;
  if(!r || r.closed) return;
  r.closed = true;
  r.timers.forEach(clearTimeout);
  if(r.cdTimer) clearInterval(r.cdTimer);
  rooms.delete(r.code);
  console.log(`[room ${r.code}] closed`);
  if(!silent) bcast('dead', { reason: reason || 'The table has closed.' });
}
function hostSweep(){
  for(const r of [...rooms.values()]){
    R = r;
    if(r.closed) continue;
    const now = Date.now();
    let dirty = false;
    r.players.slice().forEach(p => {
      if(p.bot) return;
      if(p.connected && now - p.lastSeen > 12000){
        p.connected = false; dirty = true;
        if(r.phase === 'play' && p.dealt && !p.folded){
          p.folded = true;
          hlog(`<span class="dim">${esc(p.name)} dropped — hand mucked.</span>`);
          const a = actives();
          if(a.length === 1) foldWin();
          else if(r.turnPid === p.pid) afterAct(p);
        }
      }
      if(!p.connected && r.phase === 'lobby' && now - p.lastSeen > 25000){
        r.players = r.players.filter(x => x !== p); dirty = true;
      }
      if(!p.connected && now - p.lastSeen > 90000 && !(r.phase === 'play' && p.dealt && !p.folded)){
        r.players = r.players.filter(x => x !== p); dirty = true;
        hlog(`<span class="dim">${esc(p.name)}'s seat was released.</span>`);
      }
    });
    if(dirty || r.phase === 'play') sendState();
    if(r.players.length === 0) closeRoom(null, true);
  }
}

/* ── one hand ── */
function startHand(){
  R.timers.forEach(clearTimeout); R.timers = [];
  if(R.cdTimer){ clearInterval(R.cdTimer); R.cdTimer = null; }
  R.result = null; R.countdown = 0; R.handNo++;
  R.deck = newDeck(); R.board = []; R.potCollected = 0;
  R.currentBet = 0; R.minRaise = R.bb; R.stage = 'preflop'; R.turnPid = null;
  R.players.forEach(p => {
    p.bet = 0; p.committed = 0; p.cards = []; p.dealt = false;
    p.folded = true; p.allIn = false; p.acted = false; p.revealed = false;
  });
  const elig = R.players.filter(p => !p.out && p.stack > 0 && (p.bot || p.connected));
  if(elig.length < 2){
    R.phase = 'lobby';
    hlog('<span class="dim">Not enough players to deal — back to the lobby.</span>');
    sendState(); return;
  }
  R.phase = 'play';
  hlog(`<span class="dim">— HAND #${R.handNo} —</span>`);
  R.buttonPid = (nextAfter(R.buttonPid, q => elig.includes(q)) || elig[0]).pid;
  const btn = byId(R.buttonPid);
  let sbP, bbP;
  if(elig.length === 2){ sbP = btn; bbP = nextAfter(btn.pid, q => elig.includes(q)); }
  else { sbP = nextAfter(btn.pid, q => elig.includes(q)); bbP = nextAfter(sbP.pid, q => elig.includes(q)); }
  postBlind(sbP, R.sb, 'small blind');
  postBlind(bbP, R.bb, 'big blind');
  elig.forEach(p => { p.cards = [R.deck.pop(), R.deck.pop()]; p.dealt = true; p.folded = false; });
  R.currentBet = Math.max(R.currentBet, R.bb);
  R.turnPid = nextAfter(bbP.pid, q => elig.includes(q)).pid;
  sendState();
  sendHole();
  scheduleTurn();
}
function postBlind(p, amt, label){
  const pay = commit(p, amt);
  hlog(`<b>${esc(p.name)}</b> posts ${label} ${pay}${p.allIn ? ' <span class="dim">(all-in)</span>' : ''}`);
}
function sendHole(){
  R.players.forEach(p => { if(p.dealt && !p.bot) sendTo(p, 'hole', { to: p.pid, cards: p.cards }); });
}
function scheduleTurn(){
  const p = byId(R.turnPid);
  if(!p) return;
  if(p.bot) later(900 + Math.random() * 1100, () => { if(R.phase === 'play' && R.turnPid === p.pid) botAct(p); });
  else if(!p.connected) later(700, () => {
    if(R.phase === 'play' && R.turnPid === p.pid){
      p.folded = true;
      hlog(`<span class="dim">${esc(p.name)} is away — folds.</span>`);
      afterAct(p);
    }
  });
}
function hostAct(p, m){
  if(R.phase !== 'play' || R.turnPid !== p.pid) return;
  const toCall = R.currentBet - p.bet;
  if(m.action === 'fold'){ p.folded = true; hlog(`<b>${esc(p.name)}</b> folds`); afterAct(p); }
  else if(m.action === 'check'){
    if(toCall > 0) return;
    p.acted = true; hlog(`<b>${esc(p.name)}</b> checks`); afterAct(p);
  }
  else if(m.action === 'call'){
    if(toCall <= 0) return;
    const pay = commit(p, toCall); p.acted = true;
    hlog(`<b>${esc(p.name)}</b> ${p.allIn ? 'calls all-in ' : 'calls '}${pay}`);
    afterAct(p);
  }
  else if(m.action === 'raise'){
    const maxTo = p.bet + p.stack;
    const minTo = Math.min(R.currentBet + R.minRaise, maxTo);
    let to = Math.round(Number(m.to) || 0);
    if(to >= maxTo) to = maxTo; else if(to < minTo) return;
    const pay = to - p.bet;
    if(pay <= 0) return;
    const prev = R.currentBet;
    commit(p, pay); p.acted = true;
    if(to > prev){
      const raise = to - prev;
      if(raise >= R.minRaise){
        R.players.forEach(o => { if(o !== p && o.dealt && !o.folded && !o.allIn) o.acted = false; });
        R.minRaise = Math.max(raise, R.bb);
      }
      R.currentBet = to;
    }
    hlog(`<b>${esc(p.name)}</b> ${p.allIn ? 'is all-in ' : (prev === 0 ? 'bets ' : 'raises to ')}${fmt(to)}`);
    afterAct(p);
  }
}
function afterAct(p){
  const act = actives();
  if(act.length === 1){ foldWin(); return; }
  const need = act.filter(x => !x.allIn && (x.bet < R.currentBet || !x.acted));
  if(!need.length){ endStreet(); return; }
  const i = R.players.indexOf(p);
  let np = null;
  for(let k = 1; k <= R.players.length; k++){
    const q = R.players[(i + k) % R.players.length];
    if(need.includes(q)){ np = q; break; }
  }
  R.turnPid = np.pid;
  sendState(); scheduleTurn();
}
function refundUncalled(){
  let mx = 0, top = null;
  R.players.forEach(p => { if(p.bet > mx){ mx = p.bet; top = p; } });
  if(!top || mx === 0) return;
  const others = Math.max(0, ...R.players.filter(q => q !== top).map(q => q.bet));
  if(mx > others){
    const refund = mx - others;
    top.bet -= refund; top.stack += refund; top.committed -= refund;
    hlog(`<span class="dim">${fmt(refund)} returned to ${esc(top.name)} (uncalled).</span>`);
  }
}
function endStreet(){
  if(R.phase !== 'play') return;
  const st = R.stage;
  refundUncalled();
  let c = 0;
  R.players.forEach(p => { c += p.bet; p.bet = 0; p.acted = false; });
  R.potCollected += c;
  if(st === 'river'){ showdown(); return; }
  if(st === 'preflop'){
    R.stage = 'flop';
    const a = [R.deck.pop(), R.deck.pop(), R.deck.pop()];
    R.board.push(...a);
    hlog(`Flop &nbsp;${a.map(cardTag).join(' ')}`);
  } else if(st === 'flop'){
    R.stage = 'turn';
    const a = R.deck.pop(); R.board.push(a);
    hlog(`Turn &nbsp;${cardTag(a)}`);
  } else {
    R.stage = 'river';
    const a = R.deck.pop(); R.board.push(a);
    hlog(`River &nbsp;${cardTag(a)}`);
  }
  R.currentBet = 0; R.minRaise = R.bb;
  const canAct = actives().filter(p => !p.allIn);
  if(canAct.length <= 1){
    R.turnPid = null; sendState();
    later(1100, () => { if(R.phase === 'play' && !R.result) endStreet(); });
    return;
  }
  const first = nextAfter(R.buttonPid, q => q.dealt && !q.folded && !q.allIn);
  R.turnPid = first ? first.pid : null;
  sendState(); scheduleTurn();
}
function foldWin(){
  refundUncalled();
  let pot = R.potCollected;
  R.players.forEach(p => { pot += p.bet; p.bet = 0; });
  const w = actives()[0];
  w.stack += pot;
  hlog(`<b>${esc(w.name)}</b> wins ${fmt(pot)} — pot uncontested.`);
  R.result = { winners: [{ pid: w.pid, name: w.name, amount: pot, handName: null, cards: null }], pot, showdown: false };
  R.potCollected = 0;
  endHand();
}
function buildPots(){
  const lv = [...new Set(R.players.filter(p => p.committed > 0).map(p => p.committed))].sort((a, b) => a - b);
  const pots = [];
  let prev = 0;
  for(const L of lv){
    let amt = 0;
    R.players.forEach(p => { amt += Math.max(0, Math.min(p.committed, L) - prev); });
    const elig = actives().filter(p => p.committed >= L).map(p => p.pid);
    if(amt > 0 && elig.length) pots.push({ amt, elig });
    prev = L;
  }
  return pots;
}
function showdown(){
  refundUncalled();
  let c = 0;
  R.players.forEach(p => { c += p.bet; p.bet = 0; });
  R.potCollected += c;
  const cont = actives();
  cont.forEach(p => p.revealed = true);
  const ev = new Map();
  cont.forEach(p => ev.set(p.pid, best5(p.cards.concat(R.board))));
  const pots = buildPots();
  const tally = new Map();
  pots.forEach(pot => {
    let best = -1, ws = [];
    pot.elig.forEach(pid => {
      const sc = ev.get(pid).score;
      if(sc > best){ best = sc; ws = [pid]; }
      else if(sc === best) ws.push(pid);
    });
    const share = Math.floor(pot.amt / ws.length);
    let rem = pot.amt - share * ws.length;
    ws.forEach(pid => {
      const t = tally.get(pid) || 0;
      tally.set(pid, t + share + (rem-- > 0 ? 1 : 0));
    });
  });
  const winners = [];
  let total = 0;
  [...tally.entries()].sort((a, b) => b[1] - a[1]).forEach(([pid, amt]) => {
    const p = byId(pid);
    p.stack += amt; total += amt;
    winners.push({ pid, name: p.name, amount: amt, handName: ev.get(pid).name, cards: p.cards.map(c2s) });
    hlog(`<b>${esc(p.name)}</b> wins ${fmt(amt)} with ${ev.get(pid).name}.`);
  });
  R.result = { winners, pot: total, showdown: true };
  R.potCollected = 0;
  endHand();
}
function endHand(){
  R.phase = 'handend';
  R.players.slice().forEach(p => {
    if(!p.out && p.stack <= 0){
      p.out = true;
      hlog(`<span class="dim">${esc(p.name)} is out of chips.</span>`);
      if(p.bot) R.players = R.players.filter(x => x !== p);
    }
  });
  sendState();
  const r = R;
  r.countdown = 8;
  r.cdTimer = setInterval(() => {
    if(r.closed){ clearInterval(r.cdTimer); return; }
    R = r;
    r.countdown--;
    if(r.countdown <= 0){ clearInterval(r.cdTimer); r.cdTimer = null; nextHand(); }
    else sendState();
  }, 1000);
}
function nextHand(){ startHand(); }

/* ── house players ── */
function chenScore(cards){
  const [hi, lo] = cards.map(c => c.r).sort((a, b) => b - a);
  const vp = r => ({14:10, 13:8, 12:7, 11:6}[r] || r / 2);
  if(hi === lo) return Math.max(5, vp(hi) * 2);
  let s = vp(hi);
  if(cards[0].s === cards[1].s) s += 2;
  const g = hi - lo;
  if(g === 1 && hi < 13) s += 1;
  s -= ({0:0, 1:0, 2:1, 3:2, 4:2}[g] ?? 3);
  return s;
}
function equity(my, board, opps){
  const used = new Set();
  my.concat(board).forEach(c => used.add(c.r + c.s));
  const pool = [];
  for(const s of 'shdc') for(let r = 2; r <= 14; r++) if(!used.has(r + s)) pool.push({ r, s });
  let win = 0, tie = 0;
  const N = 140;
  for(let i = 0; i < N; i++){
    const need = opps * 2 + (5 - board.length);
    for(let j = 0; j < need; j++){
      const k = j + ((Math.random() * (pool.length - j)) | 0);
      const t = pool[j]; pool[j] = pool[k]; pool[k] = t;
    }
    const draw = pool.slice(0, need);
    const rb = board.concat(draw.slice(opps * 2));
    const myS = best5(my.concat(rb)).score;
    let lost = false, t = false;
    for(let o = 0; o < opps; o++){
      const os = best5(draw.slice(o * 2, o * 2 + 2).concat(rb)).score;
      if(os > myS){ lost = true; break; }
      if(os === myS) t = true;
    }
    if(!lost){ if(t) tie++; else win++; }
  }
  return (win + tie * .5) / N;
}
function botAct(p){
  const toCall = R.currentBet - p.bet;
  try{
    const pot = R.potCollected + R.players.reduce((s, x) => s + x.bet, 0);
    const opps = Math.max(1, actives().filter(x => x !== p).length);
    let mode = 'check', to = 0;
    if(R.stage === 'preflop'){
      const s = chenScore(p.cards);
      if(toCall <= 0){
        if(s >= 10 && Math.random() < .7){ mode = 'raise'; to = Math.round(2.5 + Math.random() * 1.5) * R.bb; }
      } else {
        if(s >= 11 && Math.random() < .55){ mode = 'raise'; to = R.currentBet + Math.max(R.minRaise, Math.round(pot * .8)); }
        else if(s >= 7 || (s >= 5 && toCall <= R.bb * 2) || Math.random() < .08) mode = 'call';
        else mode = 'fold';
      }
    } else {
      const eq = equity(p.cards, R.board, opps);
      if(toCall <= 0){
        if(eq > .6 && Math.random() < .85){ mode = 'raise'; to = Math.max(R.bb * 2, Math.round(pot * (.5 + Math.random() * .35))); }
        else if(eq > .44 && Math.random() < .28){ mode = 'raise'; to = Math.max(R.bb * 2, Math.round(pot * .4)); }
      } else {
        const t = toCall / (pot + toCall);
        if(eq > t + .02){
          if(eq > .78 && Math.random() < .55){ mode = 'raise'; to = R.currentBet + Math.round(pot * .9); }
          else mode = 'call';
        }
        else if(Math.random() < .06 && toCall <= pot * .6){ mode = 'raise'; to = R.currentBet + Math.round(pot * .7); }
        else mode = 'fold';
      }
    }
    if(mode === 'raise'){
      const maxTo = p.bet + p.stack;
      to = Math.round(to);
      if(to > maxTo) to = maxTo;
      const minTo = Math.min(R.currentBet + R.minRaise, maxTo);
      if(to < minTo) mode = toCall > 0 ? 'call' : 'check';
      else { hostAct(p, { action:'raise', to }); return; }
    }
    if(mode === 'call'){ hostAct(p, { action:'call' }); return; }
    if(mode === 'fold'){ hostAct(p, { action:'fold' }); return; }
    hostAct(p, { action:'check' });
  }catch(e){
    hostAct(p, { action: toCall > 0 ? 'call' : 'check' });
  }
}

/* ── HTTP + WebSocket wiring ── */
const server = http.createServer((req, res) => {
  const u = new URL(req.url, 'http://localhost');
  if(u.pathname === '/' || u.pathname === '/poker.html'){
    fs.readFile(PAGE, (err, buf) => {
      if(err){ res.writeHead(500); res.end('poker.html not found next to server.js'); return; }
      res.writeHead(200, { 'Content-Type': 'text/html; charset=utf-8' });
      res.end(buf);
    });
  } else if(u.pathname === '/healthz'){
    res.writeHead(200); res.end('ok');
  } else {
    res.writeHead(404); res.end('Not found');
  }
});
const wss = new WebSocketServer({ server });
wss.on('connection', ws => {
  ws.on('message', data => {
    try { handle(ws, JSON.parse(data)); } catch(e){}
  });
  ws.on('close', () => {
    const r = ws.room && rooms.get(ws.room);
    if(r){
      R = r;
      const p = byId(ws.pid);
      if(p && p.ws === ws) p.ws = null;
    }
  });
});

setInterval(hostSweep, 4000);
setInterval(() => { for(const r of rooms.values()){ R = r; bcast('hb', {}); } }, 3000);

server.listen(PORT, () => {
  console.log('\n  The River Club — room server');
  console.log('  ─────────────────────────────');
  console.log(`  listening on port ${PORT}`);
  Object.values(os.networkInterfaces()).flat()
    .filter(n => n && n.family === 'IPv4' && !n.internal)
    .forEach(n => console.log(`  same network   http://${n.address}:${PORT}`));
  console.log('\n  Host a table, share the 4-digit code, and play.\n');
});