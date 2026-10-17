// 카프카 퀘스트 — 엔진
// 왼쪽 발사대(프로듀서)에서 메시지(미사일)를 쏘면 가운데 레인(파티션 로그)에 붙고, 오른쪽 로봇(컨슈머)이 가져가 처리한다.
// 시뮬레이션은 고정 60Hz, 대화·오버레이가 떠 있는 동안은 멈춘다.
(() => {
  "use strict";
  const CHAPTERS = window.CHAPTERS;
  const $ = (id) => document.getElementById(id);
  const canvas = $("world"), ctx = canvas.getContext("2d");
  const reduceMotion = matchMedia("(prefers-reduced-motion: reduce)").matches;
  const F_DISPLAY = '"Do Hyeon","Apple SD Gothic Neo","Malgun Gothic",sans-serif';
  const F_BODY = '"IBM Plex Sans KR","Apple SD Gothic Neo","Malgun Gothic",sans-serif';
  const BW = 34, PITCH = 38;          // 로그 칸 크기와 간격
  const CONS_COLORS = ["#74c0fc", "#69db7c", "#f783ac", "#ffa94d", "#b197fc", "#63e6be", "#ffe066", "#99e9f2"];
  const KEY_COLORS = ["#4dabf7", "#ff8787", "#ffd43b", "#69db7c", "#da77f2", "#ffa94d", "#63e6be"];

  // ------------------------------------------------------------------ 저장
  const store = {
    load() { try { return JSON.parse(localStorage.getItem("kafkaQuest.v1") || "null"); } catch { return null; } },
    save(s) { try { localStorage.setItem("kafkaQuest.v1", JSON.stringify(s)); } catch {} },
  };
  const saved = store.load();
  const state = { cleared: saved?.cleared || [], ch: saved?.ch ?? 0, hearts: 5, started: false, inChapter: false, goal: "" };
  function persist() { store.save({ cleared: state.cleared, ch: state.ch }); }

  // ------------------------------------------------------------------ 월드
  let world = null, msgs = [], pops = [], sparks = [];
  let elapsed = 0, shakeT = 0, idSeq = 0;
  let busy = false;                   // 대화·오버레이 중
  let mission = null;                 // 지금 쏠 메시지 { spec, lanes, wrong, wait, script, flying, resolve }
  let pending = null;                 // 기다리는 조건 { kind, root, resolve }
  let aim = 0;                        // 조준 중인 파티션 레인 번호
  const L = { top: 120, bottom: 400, launcherX: 70, x0: 150, x1: 600, consX: 700, W: 0, H: 0, small: false };

  const pLanes = () => world.lanes.filter(l => l.kind === "p");
  const lane = (id) => world.lanes.find(l => l.id === id);
  const groupConsumers = (g) => world.consumers.filter(c => c.kind === "group" && c.group === g && c.alive);
  const groups = () => [...new Set(world.consumers.filter(c => c.kind === "group").map(c => c.group))];

  function makeWorld(cfg) {
    world = {
      cfg: { ...cfg }, lanes: [], consumers: [], brokers: [], committed: {},
      acks: cfg.acks || "1", idem: !!cfg.idem, retry: cfg.retry || "block", maxTries: cfg.maxTries || 3,
      commit: cfg.commit || "auto", compact: !!cfg.compact, keyTable: cfg.keyTable || null,
      replication: cfg.replication || 0, speed: cfg.speed || 1, tools: cfg.tools || null,
      rebalanceT: 0, rebalanceMsg: "", seq: 0, consSeq: 0, burst: null,
    };
    msgs = []; pops = [];
    for (let i = 0; i < (cfg.partitions || 1); i++) addLane("p");
    if (world.replication) {
      world.brokers = Array.from({ length: world.replication }, (_, i) => ({ id: i, alive: true }));
      const p0 = pLanes()[0]; p0.leader = 0; p0.repLogs = world.brokers.map(() => new Set()); p0.lost = [];
    }
    if (cfg.retryLane) addLane("retry");
    if (cfg.dlqLane) addLane("dlq");
    for (let i = 0; i < (cfg.consumers || 0); i++) addConsumer("A", true);
    if (cfg.retryLane) ensureRetryConsumer();
    assign();
    aim = 0;
    layout(); renderConf();
  }
  function addLane(kind) {
    const ln = { kind, log: [], y: 0, h: 0, label: "", seqs: new Set() };
    if (kind === "p") {
      ln.id = pLanes().length; ln.label = "P" + ln.id;
      const idx = world.lanes.findIndex(l => l.kind !== "p");
      if (idx < 0) world.lanes.push(ln); else world.lanes.splice(idx, 0, ln);
    } else {
      ln.id = kind; ln.label = kind.toUpperCase();
      if (kind === "retry") { const d = world.lanes.findIndex(l => l.kind === "dlq"); if (d < 0) world.lanes.push(ln); else world.lanes.splice(d, 0, ln); }
      else world.lanes.push(ln);
    }
    layout();
    return ln;
  }
  function addConsumer(group = "A", silent = false) {
    const n = world.consumers.filter(c => c.kind === "group" && c.group === group).length + 1;
    const c = { id: world.consSeq++, group, kind: "group", name: group === "A" ? "로봇 " + n : "배송팀 로봇", color: CONS_COLORS[world.consSeq % CONS_COLORS.length],
      lanes: [], pos: {}, alive: true, busy: null, procT: 0, retryT: 0, x: L.consX + 80, y: L.top, tx: 0, ty: 0 };
    world.consumers.push(c);
    if (silent) assign(); else rebalance(c.name + " 참여");
    return c;
  }
  function ensureRetryConsumer() {
    if (world.consumers.some(c => c.kind === "retry")) return;
    world.consumers.push({ id: world.consSeq++, group: "retry", kind: "retry", name: "재시도 로봇", color: "#ffa94d", lanes: ["retry"], pos: { retry: 0 }, alive: true, busy: null, procT: 0, retryT: 0, x: L.consX + 80, y: L.bottom, tx: 0, ty: 0 });
  }
  // RangeAssignor 흉내: 파티션을 이어진 덩어리로 나눠 준다. 컨슈머가 더 많으면 뒤쪽은 빈손
  function assign() {
    const ps = pLanes();
    for (const g of groups()) {
      const cs = groupConsumers(g);
      const per = Math.floor(ps.length / cs.length), extra = ps.length % cs.length;
      let i = 0;
      cs.forEach((c, k) => {
        const cnt = per + (k < extra ? 1 : 0);
        c.lanes = ps.slice(i, i + cnt).map(l => l.id); i += cnt;
        for (const id of c.lanes) if (c.pos[id] === undefined) c.pos[id] = committedOf(g, id);
      });
    }
    for (const c of world.consumers) if (c.kind === "retry") c.lanes = world.lanes.some(l => l.kind === "retry") ? ["retry"] : [];
    layout();
  }
  const committedOf = (g, id) => (world.committed[g] || {})[id] || 0;
  function setCommitted(g, id, off) { (world.committed[g] ||= {})[id] = Math.max(committedOf(g, id), off); }
  function rebalance(reason) {
    world.rebalanceT = 1.7; world.rebalanceMsg = reason;
    for (const c of world.consumers) if (c.kind === "group") release(c);   // eager: 하던 일도 내려놓는다
    for (const c of world.consumers) if (c.kind === "group") c.pos = {};   // 배정이 바뀌면 커밋된 자리부터 다시
    assign();
  }
  const isIdle = () => !(world.rebalanceT > 0) && !msgs.some(m => ["fly", "pick", "proc", "retrywait", "return"].includes(m.state)) && !world.consumers.some(c => c.alive && nextFor(c)) && !(world.burst && world.burst.fired < world.burst.n);

  // ------------------------------------------------------------------ 메시지
  function keyColor(key) { let h = 0; for (const ch of key) h = (h * 31 + ch.charCodeAt(0)) >>> 0; return KEY_COLORS[h % KEY_COLORS.length]; }
  function shortLabel(m) {
    if (m.tomb) return "∅";
    if (m.key) return m.key.slice(0, 3);
    const t = m.text || "";
    const n = /#\s?(\d+)/.exec(t); if (n) return "#" + n[1];
    const tail = /(?:^|\s)([A-Z])\s*$/.exec(t); if (tail) return tail[1];
    return t.replace(/\s/g, "").slice(0, 2);
  }
  function newMsg(spec, extra = {}) {
    const m = { id: ++idSeq, key: spec.key || null, text: spec.text, tomb: !!spec.tomb, fail: spec.fail || 0, poison: !!spec.poison, tries: 0,
      lane: null, offset: null, state: "fly", x: 0, y: 0, hw: false, acked: false, color: spec.key ? keyColor(spec.key) : "#4dabf7", ...extra };
    m.root ??= m.id;
    msgs.push(m);
    return m;
  }
  // 2차 베지어로 날아가기. 도착하면 onArrive
  function flyTo(m, from, to, dur, onArrive, ctrl) {
    m.state = m.state === "fly" || m.state === "logged" ? "fly" : m.state;
    m.fly = { from, to, ctrl: ctrl || { x: (from.x + to.x) / 2, y: Math.min(from.y, to.y) - 40 }, t: 0, dur, onArrive };
    m.x = from.x; m.y = from.y;
  }
  const bez = (a, c, b, t) => ({ x: (1 - t) ** 2 * a.x + 2 * (1 - t) * t * c.x + t * t * b.x, y: (1 - t) ** 2 * a.y + 2 * (1 - t) * t * c.y + t * t * b.y });
  const launcherY = () => (L.top + L.bottom) / 2;
  const muzzle = () => ({ x: L.launcherX + 30, y: launcherY() });
  function slotCenter(ln, i) {
    const cap = Math.max(1, Math.floor((L.x1 - L.x0 - 70) / PITCH));
    const start = Math.max(0, ln.log.length - cap + (i >= ln.log.length ? 1 : 0));
    return { x: L.x0 + 62 + (i - start) * PITCH + BW / 2, y: railY(ln, ln.leader ?? 0), start, cap };
  }
  const railY = (ln, broker) => { if (!(world.replication && ln.kind === "p")) return ln.y; const sp = Math.min(36, (ln.h - 24) / 3); return ln.y - sp + broker * sp; };

  // 발사대에서 레인으로: 입구까지 곡선, 그다음 칸까지 직선
  function launch(m, ln, onEnter) {
    const mz = muzzle(), entry = { x: L.x0 + 6, y: railY(ln, ln.leader ?? 0) };
    flyTo(m, mz, entry, 0.42, () => {
      if (onEnter && onEnter() === false) return;
      const slot = slotCenter(ln, ln.log.length);
      flyTo(m, entry, slot, Math.max(0.12, (slot.x - entry.x) / 900), () => appendMsg(m, ln), { x: (entry.x + slot.x) / 2, y: entry.y });
    }, { x: L.x0 - 30, y: mz.y + (entry.y - mz.y) * 0.25 });
  }
  function appendMsg(m, ln) {
    m.fly = null;
    if (m.seq != null && world.idem && ln.seqs.has(m.seq)) {   // 멱등 프로듀서: 같은 시퀀스는 버린다
      m.state = "rejected"; m.rejT = 0; m.lane = ln;
      pop("시퀀스 " + m.seq + " 이미 있음 → 버림", m.x, m.y - 22, "#ffd43b");
      ackIn(m, 0.5, "ACK ✓ (이미 저장됨)");
      resolveWait(m, "resolved");
      return;
    }
    m.offset = ln.log.length; ln.log.push(m); ln.seqs.add(m.seq); m.lane = ln; m.state = "logged"; m.loggedAt = elapsed;
    const slot = slotCenter(ln, m.offset); m.x = slot.x; m.y = slot.y;
    if (m.dupOf) { m.dup = true; m.dupOf.dup = true; pop("같은 메시지가 두 번!", m.x, m.y - 22, "#ff8787"); }
    if (ln.kind === "p" && world.replication) {
      ln.repLogs[ln.leader].add(m.id); m.copyT = 0.6;
      if (world.acks === "1") ackIn(m, 0.2);
      if (m.script === "crashLeader" && !m.crashDone) { m.crashDone = true; m.crashT = 0.35; }
    } else {
      m.hw = true;
      if (!m.noAck) ackIn(m, 0.2);
    }
    if (ln.kind === "dlq") { m.state = "dlq"; pop("DLQ 격리", m.x, m.y - 22, "#ff8787"); resolveWait(m, "resolved"); }
    resolveWait(m, "appended");
  }
  function ackIn(m, delay, label) { m.ackT = delay; m.ackLabel = label; }
  function deliverAck(m) {
    const mz = muzzle();
    if (m.script === "ackLost" && !m.ackLostDone) {
      m.ackLostDone = true; m.acked = false; shake();
      pop("✕ ACK 유실", mz.x + 50, mz.y + 22, "#ff8787");
      resolveWait(m, "ackLost");
      return;
    }
    m.acked = true;
    pop(m.ackLabel || "ACK ✓", mz.x + 50, mz.y + 22, "#69db7c");
  }
  // 재시도 토픽 · DLQ 로 옮기기: 원본은 '옮겨짐'으로 남기고 복제본이 날아간다
  function moveTo(m, kind, from, delay) {
    const ln = lane(kind); if (!ln) return;
    m.state = "moved"; m.movedTo = kind;
    const c = newMsg({ key: m.key, text: m.text, fail: m.fail, poison: m.poison }, { tries: m.tries, root: m.root, noAck: true, color: m.color });
    const slot = slotCenter(ln, ln.log.length);
    flyTo(c, from, slot, 0.55, () => { appendMsg(c, ln); if (delay) c.readyAt = elapsed + delay; });
  }
  function refire(m, ln, label) {   // 프로듀서 재전송 (retries / 재전송 이벤트)
    pop(label, muzzle().x + 60, muzzle().y + 22, "#ffd43b");
    const c = newMsg({ key: m.key, text: m.text }, { seq: m.seq, root: m.root, script: m.script, dupOf: m.dupOf, color: m.color, crashDone: true });
    launch(c, ln);
    return c;
  }

  // ------------------------------------------------------------------ 컨슈머
  // 로그의 기록(record)은 레인에 그대로 남고, 로봇은 '토큰'(복사본)을 들고 가 처리한다. 그래서 다른 그룹이나 재시작한 로봇이 같은 기록을 다시 읽을 수 있다
  function nextFor(c) {
    for (const id of c.lanes) {
      const ln = lane(id); if (!ln) continue;
      let p = c.pos[id] || 0;
      while (p < ln.log.length && ["compacted", "moved", "lost", "dlq"].includes(ln.log[p].state)) p++;
      c.pos[id] = p;
      const m = ln.log[p];
      if (m && (m.state === "logged" || m.state === "done") && m.hw && !m.holder) return m;
    }
    return null;
  }
  function release(c) {   // 들고 있던 걸 내려놓는다 (리밸런싱 · 재시작 · 죽음)
    const t = c.busy; if (!t) return;
    t.rec.holder = null; msgs.splice(msgs.indexOf(t), 1); c.busy = null;
  }
  function updateConsumers(dt) {
    for (const c of world.consumers) {
      if (!c.alive) continue;
      if (c.kind === "group" && world.rebalanceT > 0) continue;
      if (!c.busy) {
        const m = nextFor(c);
        if (m && (m.readyAt == null || m.readyAt <= elapsed)) {
          const t = newMsg({ key: m.key, text: m.text, tomb: m.tomb }, { token: true, rec: m, root: m.root, color: m.color, state: "pick" });
          m.holder = c; c.busy = t;
          flyTo(t, { x: m.x, y: m.y }, { x: c.x, y: c.y }, 0.35, () => { t.state = "proc"; c.procT = 0; }, { x: (m.x + c.x) / 2, y: m.y - 16 });
        }
        continue;
      }
      const t = c.busy;
      if (t.state === "proc") { c.procT += dt; if (c.procT >= world.speed) finish(c, t); }
      else if (t.state === "retrywait") { c.retryT -= dt; if (c.retryT <= 0) { t.state = "proc"; c.procT = 0; } }
    }
  }
  function finish(c, t) {
    const m = t.rec, ln = m.lane, p = { x: c.x, y: c.y };
    if (!(m.poison || m.fail > 0)) {
      const again = m.doneBy?.has(c.group);
      (m.doneBy ||= new Set()).add(c.group);
      m.state = "done"; m.holder = null; c.busy = null;
      c.pos[ln.id] = m.offset + 1;
      if (world.commit === "auto" && c.kind === "group") setCommitted(c.group, ln.id, m.offset + 1);
      if (m.dup) { pop("중복 처리! 두 번 결제됨", p.x - 40, p.y - 40, "#ff8787"); shake(); }
      else if (again) { pop("또 처리했다! (중복)", p.x - 40, p.y - 40, "#ff8787"); shake(); }
      else pop("처리 완료 ✓", p.x - 20, p.y - 40, "#69db7c");
      t.state = "return";
      flyTo(t, p, slotCenter(ln, m.offset), 0.3, () => msgs.splice(msgs.indexOf(t), 1));
      resolveWait(m, "consumed");
      return;
    }
    if (m.fail > 0) m.fail--;
    m.tries++;
    shake();
    pop(`실패 ✕ (${m.tries}번째)`, p.x - 30, p.y - 40, "#ff8787");
    if (world.retry === "block" || !lane("retry")) { t.state = "retrywait"; c.retryT = 1.4; return; }
    c.pos[ln.id] = m.offset + 1; m.holder = null; c.busy = null; msgs.splice(msgs.indexOf(t), 1);
    if (world.commit === "auto" && c.kind === "group") setCommitted(c.group, ln.id, m.offset + 1);
    if (lane("dlq") && m.tries >= world.maxTries) moveTo(m, "dlq", p);
    else moveTo(m, "retry", p, 1.8);
  }

  // ------------------------------------------------------------------ 이벤트
  function crashLeader(ln) {
    const dead = ln.leader;
    world.brokers[dead].alive = false;
    const next = world.brokers.find(b => b.alive && ln.repLogs[b.id]);
    if (!next) return;
    shake();
    pop(`브로커 ${dead} 다운!`, L.x0 + 90, railY(ln, dead) - 26, "#ff8787");
    ln.leader = next.id;
    const keep = [], drop = [];
    for (const m of ln.log) (ln.repLogs[next.id].has(m.id) ? keep : drop).push(m);
    ln.log = keep;
    for (const m of drop) {
      ln.seqs.delete(m.seq);
      m.lostRail = dead; m.fly = null; ln.lost.push(m);
      if (m.acked) { m.state = "lost"; m.lostLabel = "유실"; pop("유실! 프로듀서는 성공인 줄 안다", m.x, m.y - 24, "#ff8787"); setTimeout(() => resolveWait(m, "resolved"), 900); }
      else { m.state = "lost"; m.lostLabel = "재전송됨"; m.ackT = null; setTimeout(() => refire(m, ln, "응답 없음 → 새 리더에게 재전송"), 700); }
    }
    for (const c of world.consumers) for (const id of Object.keys(c.pos)) if (id == ln.id) c.pos[id] = Math.min(c.pos[id], ln.log.length);
    pop(`브로커 ${next.id} 가 새 리더`, L.x0 + 90, railY(ln, next.id) - 26, "#ffd43b");
  }
  function recoverBroker() {
    for (const b of world.brokers) b.alive = true;
    for (const ln of pLanes()) if (ln.repLogs) for (const m of ln.log) for (const s of ln.repLogs) s.add(m.id);
    for (const ln of pLanes()) if (ln.lost) ln.lost = [];
  }
  function restartConsumer() {
    for (const c of world.consumers) if (c.kind === "group") {
      release(c);
      c.pos = {}; for (const id of c.lanes) c.pos[id] = committedOf(c.group, id);
      pop("재시작 → 깃발 자리부터", c.x - 50, c.y - 44, "#ffd43b");
    }
  }
  function commitAll() {
    for (const c of world.consumers) if (c.kind === "group") for (const id of c.lanes) setCommitted(c.group, id, c.pos[id] || 0);
    pop("커밋!", L.x0 + 80, pLanes()[0].y - 30, "#69db7c");
  }
  function compact() {
    for (const ln of pLanes()) {
      const last = new Map();
      ln.log.forEach((m, i) => { if (m.key && m.state !== "compacted") last.set(m.key, i); });
      ln.log.forEach((m, i) => { if (m.key && m.state !== "compacted" && last.get(m.key) !== i) { m.state = "compacted"; m.fadeT = 1.0; } });
      // 툼스톤은 잠시 남았다가 키와 함께 사라진다
      for (const [, i] of last) { const m = ln.log[i]; if (m.tomb) setTimeout(() => { m.state = "compacted"; m.fadeT = 1.0; }, 1400); }
    }
    pop("컴팩션: 키별 마지막만 남김", L.x0 + 120, pLanes()[0].y - 34, "#ffd43b");
  }
  function killConsumer() {
    const cs = groupConsumers("A"); const c = cs[cs.length - 1]; if (!c) return;
    c.alive = false; release(c);
    pop(c.name + " 다운", c.x - 30, c.y - 44, "#ff8787"); shake();
    rebalance(c.name + " 이탈");
  }
  function applySet(set) {
    if (!set) return;
    if (set.acks) world.acks = set.acks;
    if (set.idem !== undefined) world.idem = set.idem;
    if (set.retry) world.retry = set.retry;
    if (set.retryLane && !lane("retry")) { addLane("retry"); ensureRetryConsumer(); assign(); }
    if (set.commit) world.commit = set.commit;
    renderConf();
  }

  // ------------------------------------------------------------------ 자동 발사 (8장)
  function startBurst(b) {
    world.burst = { n: b.n, interval: b.interval, t: b.interval * 0.5, fired: 0, rr: 0, startAt: elapsed };
    renderTools();
  }
  function updateBurst(dt) {
    const b = world.burst; if (!b) return;
    if (b.fired < b.n) {
      b.t += dt;
      if (b.t >= b.interval) {
        b.t = 0; b.fired++;
        const ps = pLanes(); const ln = ps[b.rr++ % ps.length];
        launch(newMsg({ text: "주문 #" + b.fired }), ln);
      }
    } else if (isIdle() && pending?.kind === "burst") { const r = pending; pending = null; world.burst = null; renderTools(); r.resolve(); }
    renderToolsLag();
  }
  const backlog = () => pLanes().reduce((s, ln) => s + ln.log.filter(m => ["logged", "pick", "proc", "retrywait"].includes(m.state)).length, 0) + msgs.filter(m => m.state === "fly" && !m.lane).length;
  function renderTools() {
    const t = $("tools");
    if (!world.burst || !world.tools) { t.hidden = true; return; }
    t.hidden = false;
    t.innerHTML = `<span class="lag">밀림 <b id="lagN">0</b></span>` +
      (world.tools.includes("addConsumer") ? `<button type="button" id="tAddC">로봇 추가 (${groupConsumers("A").length}대)</button>` : "") +
      (world.tools.includes("addPartition") ? `<button type="button" id="tAddP">레인 추가 (${pLanes().length}개)</button>` : "");
    $("tAddC")?.addEventListener("click", () => { addConsumer("A"); renderTools(); const cs = groupConsumers("A").length, ps = pLanes().length; if (cs > ps) toast(`레인 ${ps}개라 로봇 ${ps + 1}부터는 놀아요`); });
    $("tAddP")?.addEventListener("click", () => { if (pLanes().length >= 6) { toast("이 화면에선 6개까지만"); return; } addLane("p"); rebalance("파티션 추가"); renderTools(); toast("레인 추가. 키 → 레인 배정이 바뀝니다"); });
  }
  function renderToolsLag() { const el = $("lagN"); if (el) el.textContent = backlog(); }

  // ------------------------------------------------------------------ 시뮬레이션
  function update(dt) {
    if (world.rebalanceT > 0) { world.rebalanceT -= dt; if (world.rebalanceT <= 0) pop("리밸런싱 끝. 다시 출발", L.x0 + 120, L.top - 8, "#69db7c"); }
    for (let i = msgs.length - 1; i >= 0; i--) {
      const m = msgs[i];
      if (m.fly) {
        const f = m.fly; f.t += dt;
        const t = Math.min(1, f.t / f.dur); const p = bez(f.from, f.ctrl, f.to, t); m.x = p.x; m.y = p.y;
        if (t >= 1) { const cb = f.onArrive; m.fly = null; cb && cb(); }
      }
      if (m.ackT != null) { m.ackT -= dt; if (m.ackT <= 0) { m.ackT = null; deliverAck(m); } }
      if (m.copyT != null) {
        m.copyT -= dt;
        if (m.copyT <= 0) {
          m.copyT = null; const ln = m.lane;
          if (ln && ln.repLogs && m.state !== "lost") {
            for (const b of world.brokers) if (b.alive) ln.repLogs[b.id].add(m.id);
            m.hw = true;
            if (world.acks === "all" && !m.acked) ackIn(m, 0.15);
          }
        }
      }
      if (m.crashT != null) { m.crashT -= dt; if (m.crashT <= 0) { m.crashT = null; if (m.lane && m.lane.repLogs) crashLeader(m.lane); } }
      if (m.state === "rejected") { m.rejT += dt; m.x -= 60 * dt; m.y += 20 * dt; if (m.rejT > 1.2) msgs.splice(i, 1); }
      if (m.fadeT != null) { m.fadeT -= dt; if (m.fadeT <= 0) m.fadeT = null; }
      if (m.state === "bounce") { m.bT += dt; m.x -= 220 * dt; m.y += 40 * dt; if (m.bT > 0.5) { msgs.splice(i, 1); onWrongDone(m); } }
    }
    updateConsumers(dt);
    updateBurst(dt);
    if (pending?.kind === "idle" && isIdle()) { const r = pending; pending = null; r.resolve(); }
    for (const c of world.consumers) { c.x += (c.tx - c.x) * Math.min(1, dt * 8); c.y += (c.ty - c.y) * Math.min(1, dt * 8); }
  }
  function resolveWait(m, kind) {
    if (!pending || pending.root !== m.root) return;
    if (pending.kind !== kind && !(pending.kind === "resolved" && kind === "consumed")) return;   // 'resolved' 는 처리·유실·DLQ·거부 중 무엇이든 끝나면
    const r = pending; pending = null; r.resolve();
  }

  // ------------------------------------------------------------------ 발사 (플레이어)
  function fire() {
    if (!mission || mission.flying || busy) return;
    const ps = pLanes(); const ln = ps[Math.min(aim, ps.length - 1)];
    mission.flying = true;
    const m = newMsg(mission.spec, { seq: ++world.seq, script: mission.script });
    mission.msg = m;
    const ok = !mission.lanes || mission.lanes.includes(ln.id);
    if (ok && pending) pending.root = m.root;
    launch(m, ln, () => {
      if (ok) return true;
      m.state = "bounce"; m.bT = 0; m.lane = ln; ln.flashT = 0.6; shake();
      pop("잘못된 레인!", m.x + 10, m.y - 26, "#ff8787");
      return false;
    });
    syncUi();
  }
  async function onWrongDone(m) {
    busy = true; syncUi();
    await say("땡!", mission.wrong + "  (하트 -1)", "bad");
    const alive = await loseHeart();
    if (!alive) return;
    closeDialog();
    if (mission) mission.flying = false;
    syncUi();
  }
  function setAim(i) { const n = pLanes().length; aim = Math.max(0, Math.min(n - 1, i)); }

  // ------------------------------------------------------------------ HUD · 대화 · 카드 (OIDC 퀘스트와 같은 조작)
  const chapter = () => CHAPTERS[state.ch];
  function renderHud() {
    $("chTitle").textContent = chapter().title;
    $("goal").textContent = state.goal || chapter().intro;
    $("hearts").innerHTML = "하트 " + Array.from({ length: 5 }, (_, i) => `<span class="${i < state.hearts ? "" : "lost"}">♥</span>`).join("");
  }
  function renderConf() {
    if (!world) return;
    const cfg = world.cfg, chips = [];
    if (world.replication) chips.push(["acks", world.acks, world.acks === "all" ? "#69db7c" : "#ffa94d"]);
    if (cfg.idem !== undefined) chips.push(["멱등 프로듀서", world.idem ? "켬" : "끔", world.idem ? "#69db7c" : "#ff8787"]);
    if (cfg.retry) chips.push(["재시도", world.retry === "topic" ? "재시도 토픽" : "제자리", world.retry === "topic" ? "#69db7c" : "#ffa94d"]);
    if (cfg.maxTries) chips.push(["최대 재시도", world.maxTries + "회", "#ffa94d"]);
    if (cfg.commit) chips.push(["커밋", world.commit === "manual" ? "수동" : "자동", "#74c0fc"]);
    if (cfg.compact) chips.push(["cleanup.policy", "compact", "#da77f2"]);
    if (world.replication) chips.push(["복제", world.replication + " (ISR " + world.brokers.filter(b => b.alive).length + ")", "#74c0fc"]);
    $("conf").innerHTML = chips.map(([k, v, c]) => `<span class="chip"><i style="background:${c}"></i>${k} <b>${v}</b></span>`).join("");
  }
  let toastTimer = 0;
  function toast(msg) { const t = $("toast"); t.textContent = msg; t.classList.add("show"); clearTimeout(toastTimer); toastTimer = setTimeout(() => t.classList.remove("show"), 1800); }

  const dlg = $("dialog"), dlgText = $("dlgText"), dlgWho = $("dlgWho"), dlgChoices = $("dlgChoices"), dlgMore = $("dlgMore");
  let advance = null, typing = null, choicePick = null, choiceMove = null;
  function say(who, text, cls = "") {
    return new Promise((resolve) => {
      busy = true; syncUi();
      dlg.hidden = false; dlgChoices.innerHTML = ""; dlgMore.hidden = true;
      dlgWho.textContent = who; dlgWho.className = "who " + (cls || (who === "나" ? "me" : ""));
      let i = 0; dlgText.textContent = "";
      const finishTyping = () => { clearInterval(typing); typing = null; dlgText.textContent = text; dlgMore.hidden = false; };
      if (reduceMotion) finishTyping();
      else typing = setInterval(() => { i += 2; dlgText.textContent = text.slice(0, i); if (i >= text.length) finishTyping(); }, 18);
      advance = () => { if (typing) { finishTyping(); return; } advance = null; resolve(); };
    });
  }
  function ask(q, opts) {
    return new Promise((resolve) => {
      busy = true; syncUi();
      dlg.hidden = false; dlgMore.hidden = true; advance = null;
      dlgWho.textContent = "퀴즈"; dlgWho.className = "who";
      dlgText.textContent = q;
      const shuffled = opts.map(o => ({ o, r: Math.random() })).sort((a, b) => a.r - b.r).map(x => x.o);
      dlgChoices.innerHTML = "";
      shuffled.forEach((o, i) => {
        const b = document.createElement("button"); b.type = "button";
        b.innerHTML = `<kbd>${i + 1}</kbd><span></span>`; b.lastChild.textContent = o.t;
        b.addEventListener("click", (e) => { e.stopPropagation(); choicePick = null; choiceMove = null; resolve(o); });
        b.addEventListener("mouseenter", () => highlight(i));
        dlgChoices.appendChild(b);
      });
      let sel = 0;
      const highlight = (i) => { sel = (i + shuffled.length) % shuffled.length; [...dlgChoices.children].forEach((el, j) => el.classList.toggle("sel", j === sel)); dlgChoices.children[sel].focus({ preventScroll: true }); };
      choicePick = (n) => { if (shuffled[n]) { choicePick = null; choiceMove = null; resolve(shuffled[n]); } };
      const askedAt = performance.now();
      choiceMove = (d) => { if (d !== 0) highlight(sel + d); else if (performance.now() - askedAt > 250) choicePick(sel); };
      highlight(0);
    });
  }
  function closeDialog() { dlg.hidden = true; advance = null; choicePick = null; choiceMove = null; if ($("overlay").hidden) busy = false; syncUi(); }
  dlg.addEventListener("click", () => advance && advance());

  async function loseHeart() {
    state.hearts = Math.max(0, state.hearts - 1); renderHud();
    if (state.hearts === 0) {
      closeDialog();
      showCard(`<h2>하트가 다 떨어졌어요</h2><p>괜찮아요. 방금 본 해설을 떠올리면서 이 장을 처음부터 다시 해 봐요.</p>
        <div class="row-btns"><button class="btn primary" id="retryBtn" type="button">이 장 다시 하기</button><button class="btn" id="toMenuH" type="button">장 선택</button></div>`);
      $("retryBtn").onclick = () => { hideCard(); startChapter(state.ch); };
      $("toMenuH").onclick = showMenu;
      return false;
    }
    return true;
  }

  function showCard(html) {
    busy = true; syncUi(); $("card").innerHTML = html; $("overlay").hidden = false;
    cardShownAt = performance.now();
    cardButtons().forEach((b, i) => b.addEventListener("mouseenter", () => cardFocus(i)));
    cardFocus(0);
  }
  let cardShownAt = 0;
  const cardButtons = () => [...$("card").querySelectorAll("button")];
  function cardFocus(i) {
    const btns = cardButtons(); if (!btns.length) return;
    const n = (i + btns.length) % btns.length;
    btns.forEach((b, j) => b.classList.toggle("sel", j === n));
    btns[n].focus({ preventScroll: true }); btns[n].scrollIntoView({ block: "nearest" });
  }
  function cardKey(e) {
    const btns = cardButtons(); if (!btns.length) return false;
    const cur = Math.max(0, btns.findIndex(b => b.classList.contains("sel")));
    const d = { ArrowUp: -1, KeyW: -1, ArrowLeft: -1, KeyA: -1, ArrowDown: 1, KeyS: 1, ArrowRight: 1, KeyD: 1, Tab: e.shiftKey ? -1 : 1 }[e.code];
    if (d !== undefined) { cardFocus(cur + d); return true; }
    if (e.code === "Space" || e.code === "Enter" || e.code === "NumpadEnter") { if (!e.repeat && performance.now() - cardShownAt > 250) btns[cur].click(); return true; }
    return false;
  }
  function hideCard() { $("overlay").hidden = true; if (dlg.hidden) busy = false; syncUi(); document.activeElement?.blur(); }

  function showMenu() {
    let html = "", part = "";
    CHAPTERS.forEach((c, i) => {
      if (c.part !== part) { part = c.part; html += `<h3>${part}</h3>`; }
      const mark = state.cleared.includes(c.id) ? "완료" : (state.inChapter && i === state.ch ? "진행 중" : "");
      html += `<button type="button" data-i="${i}"><span class="num">${i + 1}</span><span><b>${c.title.replace(/^\d+장\.\s*/, "")}</b><small>${c.intro}</small></span><span class="mark">${mark}</span></button>`;
    });
    showCard(`<h1>카프카 퀘스트</h1>
      <p class="sub">당신은 메시지입니다. 프로듀서 발사대에서 토픽의 파티션 레인으로 날아가고, 컨슈머 로봇이 당신을 가져갑니다. 기본편에서 오프셋·파티션·커밋·복제를, 심화편에서 재시도·DLQ·리밸런싱·랙·멱등·컴팩션을 몸으로 익혀요.</p>
      <div class="chapters">${html}</div>
      <div class="row-btns">${state.inChapter ? `<button class="btn primary" id="resume" type="button">하던 장으로 돌아가기</button>` : ""}<button class="btn" id="howBtn" type="button">조작법</button></div>
      <p class="foot">진행 상황(완료한 장)은 이 브라우저에만 저장됩니다. 장을 고르면 그 장을 처음부터 시작해요.</p>`);
    $("card").querySelectorAll(".chapters button").forEach(b => b.onclick = () => { state.started = true; startChapter(+b.dataset.i); });
    $("resume")?.addEventListener("click", hideCard);
    $("howBtn").onclick = showHelp;
  }
  function showHelp() {
    showCard(`<h2>조작법</h2>
      <div class="keys">
        <kbd>↑ ↓ · W S</kbd><span>조준할 레인(파티션)을 고릅니다. 레인을 클릭·탭해도 됩니다</span>
        <kbd>Space · Enter</kbd><span>발사. 발사대를 클릭하거나 오른쪽 아래 '발사' 버튼도 같습니다. 대사도 Space 로 넘겨요</span>
        <kbd>퀴즈</kbd><span>방향키로 옮기고 Space 로 고르기, 또는 숫자 1~4</span>
        <kbd>메뉴 · 완료 화면</kbd><span>방향키로 버튼을 옮기고 Space(또는 Enter)로 누르기</span>
        <kbd>화면 위 버튼</kbd><span>8장에서만 '로봇 추가', '레인 추가' 버튼이 나옵니다</span>
      </div>
      <p class="sub">잘못된 레인으로 쏘거나 퀴즈를 틀리면 하트가 하나 줄고 이유를 알려 줘요. 하트 다섯 개를 다 쓰면 그 장을 처음부터 다시 합니다. 지켜보는 단계에서는 그냥 기다리면 돼요.</p>
      <div class="row-btns"><button class="btn primary" id="okHelp" type="button">닫기</button><button class="btn" id="helpMenu" type="button">장 선택</button></div>`);
    $("okHelp").onclick = () => { if (!state.inChapter) showMenu(); else hideCard(); };
    $("helpMenu").onclick = showMenu;
  }
  $("menuBtn").onclick = () => { if (!dlg.hidden) return; showMenu(); };
  $("helpBtn").onclick = () => { if (!dlg.hidden) return; showHelp(); };

  // ------------------------------------------------------------------ 장 진행
  let runToken = 0;
  function startChapter(i) {
    state.ch = i; state.hearts = 5; state.inChapter = true; state.goal = ""; persist();
    const ch = CHAPTERS[i];
    mission = null; pending = null; world && (world.burst = null);
    makeWorld(ch.world);
    renderHud(); renderTools();
    const token = ++runToken;
    showCard(`<h2>${ch.title}</h2><p class="sub">${ch.part}</p><p>${ch.intro}</p>
      <div class="row-btns"><button class="btn primary" id="goBtn" type="button">출발</button></div>`);
    $("goBtn").onclick = () => { hideCard(); runChapter(token); };
  }
  async function runChapter(token) {
    const ch = chapter();
    for (const step of ch.steps) {
      if (step.goal) { state.goal = step.goal; renderHud(); }
      await runStep(step, token);
      if (token !== runToken) return;
    }
    chapterClear();
  }
  const waitFor = (kind, root = null) => new Promise(resolve => { pending = { kind, root, resolve }; });
  const sleep = (s) => new Promise(r => setTimeout(r, s * 1000));
  async function runStep(step, token) {
    if (step.say) { for (const [w, t] of step.say) { await say(w, t); if (token !== runToken) return; } closeDialog(); return; }
    if (step.quiz) {
      for (;;) {
        const pick = await ask(step.quiz.q, step.quiz.opts);
        if (token !== runToken) return;
        if (pick.ok) { celebrate(); await say("정답!", pick.fb, "ok"); applySet(pick.set); break; }
        shake();
        await say("땡!", pick.fb + "  (하트 -1)", "bad");
        if (!(await loseHeart())) return;
      }
      closeDialog(); return;
    }
    if (step.fire) {
      const f = step.fire;
      await new Promise(resolve => {
        mission = { spec: f.msg, lanes: f.lanes || null, wrong: f.wrong || "그 레인이 아니에요.", script: f.script || null, flying: false };
        pending = { kind: f.wait || "consumed", root: null, resolve };
        if (f.lanes && f.lanes.length === 1) setAim(f.lanes[0] === aim ? aim : aim);   // 조준은 그대로 둔다 (플레이어가 고른다)
        syncUi();
      });
      mission = null; syncUi();
      await sleep(0.35);
      return;
    }
    if (step.wait) { state.goal = step.goal || "지켜보자"; renderHud(); await waitFor("idle"); await sleep(0.4); return; }
    if (step.burst) { startBurst(step.burst); await waitFor("burst"); await sleep(0.3); return; }
    if (step.event) {
      const ev = step.event;
      const lines = async () => { for (const [w, t] of step.lines || []) { await say(w, t); if (token !== runToken) return false; } closeDialog(); return true; };
      if (ev === "commit") { commitAll(); await sleep(0.5); await lines(); return; }
      if (!(await lines())) return;
      if (ev === "addConsumer") { addConsumer("A"); await sleep(0.2); await waitRebalance(); }
      else if (ev === "addGroup") { addConsumer("B", true); }
      else if (ev === "killConsumer") { killConsumer(); await sleep(0.2); await waitRebalance(); }
      else if (ev === "restartConsumer") { restartConsumer(); }
      else if (ev === "recoverBroker") { recoverBroker(); renderConf(); await sleep(0.4); }
      else if (ev === "compact") { compact(); await sleep(2.2); }
      else if (ev === "clear") { for (const ln of world.lanes) { ln.log = []; ln.seqs.clear(); } msgs = msgs.filter(m => m.state === "fly"); for (const c of world.consumers) { release(c); c.pos = {}; } world.committed = {}; assign(); }
      else if (ev === "set") { makeWorld(step.world); renderConf(); await sleep(0.3); }
      else if (ev === "resend") {
        const src = [...msgs].reverse().find(m => m.ackLostDone);
        if (src) { const c = refire(src, src.lane, "재전송 (retries)"); c.dupOf = src; }
        await sleep(0.3);
      }
      return;
    }
  }
  async function waitRebalance() { while (world.rebalanceT > 0) await sleep(0.1); }

  function chapterClear() {
    const ch = chapter();
    if (!state.cleared.includes(ch.id)) state.cleared.push(ch.id);
    state.inChapter = false; mission = null; persist();
    closeDialog();
    const next = state.ch + 1 < CHAPTERS.length ? state.ch + 1 : null;
    showCard(`<h2>${ch.title} 완료!</h2>
      <ul>${ch.takeaways.map(t => `<li>${t}</li>`).join("")}</ul>
      <p class="sub">게임 속 표현과 진짜 이름</p>
      <div class="terms"><table><thead><tr><th>게임에서</th><th>진짜 이름</th><th>뜻</th></tr></thead>
      <tbody>${(ch.terms || []).map(([a, b, c]) => `<tr><td>${a}</td><td><b>${b}</b></td><td>${c}</td></tr>`).join("")}</tbody></table></div>
      <div class="row-btns">${next !== null ? `<button class="btn primary" id="nextCh" type="button">${CHAPTERS[next].title}</button>` : `<button class="btn primary" id="endBtn" type="button">엔딩 보기</button>`}
      <button class="btn" id="toMenu" type="button">장 선택</button></div>`);
    if (next !== null) $("nextCh").onclick = () => { hideCard(); startChapter(next); };
    else $("endBtn").onclick = showEnding;
    $("toMenu").onclick = showMenu;
  }
  function showEnding() {
    showCard(`<h2>모두 끝!</h2><p>오프셋, 파티션과 키, 컨슈머 그룹과 커밋, 복제와 acks, 재시도, DLQ, 리밸런싱, 랙과 파티션 확장, 멱등 프로듀서, 컴팩션까지 직접 날아가 봤어요.</p>
      <p class="sub">한 문장 요약: 카프카는 '지우지 않는 로그'다. 파티션이 순서와 병렬의 단위, 오프셋 커밋이 진행 상황, 복제와 acks 가 내구성, 재시도·DLQ·멱등이 실패를 다루는 방법이다.</p>
      <div class="row-btns"><button class="btn primary" id="toMenu2" type="button">장 선택</button></div>`);
    $("toMenu2").onclick = showMenu;
  }

  // ------------------------------------------------------------------ 입력
  addEventListener("keydown", (e) => {
    if (!$("overlay").hidden) { if (cardKey(e)) e.preventDefault(); return; }
    if (choicePick && /^(Digit|Numpad)[1-4]$/.test(e.code)) { choicePick(+e.code.slice(-1) - 1); e.preventDefault(); return; }
    if (choiceMove) {
      if (e.repeat && (e.code === "Space" || e.code === "Enter")) { e.preventDefault(); return; }
      const d = { ArrowUp: -1, KeyW: -1, ArrowLeft: -1, KeyA: -1, ArrowDown: 1, KeyS: 1, ArrowRight: 1, KeyD: 1, Space: 0, Enter: 0, NumpadEnter: 0 }[e.code];
      if (d !== undefined) { choiceMove(d); e.preventDefault(); return; }
    }
    if (e.code === "Space" || e.code === "Enter" || e.code === "NumpadEnter") {
      if (advance) { advance(); e.preventDefault(); return; }
      if (!e.repeat && !busy && document.activeElement?.tagName !== "BUTTON") { fire(); e.preventDefault(); }
      return;
    }
    if (busy) return;
    if (e.code === "ArrowUp" || e.code === "KeyW") { setAim(aim - 1); e.preventDefault(); }
    if (e.code === "ArrowDown" || e.code === "KeyS") { setAim(aim + 1); e.preventDefault(); }
  });
  addEventListener("keyup", (e) => { if ((choiceMove || !$("overlay").hidden) && (e.code === "Space" || e.code === "Enter")) e.preventDefault(); });
  canvas.addEventListener("pointerdown", (e) => {
    if (busy || !world) return;
    const x = e.clientX, y = e.clientY;
    const ps = pLanes();
    const hit = ps.findIndex(ln => Math.abs(y - ln.y) < ln.h / 2);
    if (x < L.x0 - 12 && Math.abs(y - launcherY()) < 70) { fire(); return; }
    if (hit >= 0) { setAim(hit); if (x > L.x0 && mission && !mission.flying && !document.body.classList.contains("touch")) fire(); }
  });
  $("fireBtn").addEventListener("click", fire);
  $("upBtn").addEventListener("click", () => setAim(aim - 1));
  $("downBtn").addEventListener("click", () => setAim(aim + 1));
  addEventListener("touchstart", () => document.body.classList.add("touch"), { once: true, passive: true });
  function syncUi() {
    document.body.classList.toggle("busy", busy);
    const armed = !!mission && !mission.flying && !busy;
    $("fireBtn").hidden = !armed; $("pad").hidden = !armed;
  }

  // ------------------------------------------------------------------ 배치
  function layout() {
    const W = innerWidth, H = innerHeight, small = W < 600;
    L.W = W; L.H = H; L.small = small;
    const toolsH = world && world.burst && world.tools ? 46 : 0;
    L.top = (small ? 130 : 124) + toolsH;
    L.bottom = H - (small ? 150 : 170);
    L.launcherX = small ? 34 : 60;
    L.x0 = L.launcherX + (small ? 60 : 92);
    L.consX = W - (small ? 50 : 90);
    L.x1 = L.consX - (small ? 46 : 72);
    if (!world) return;
    const weight = (ln) => ln.kind === "p" ? (world.replication ? 2.3 : 1) : ln.kind === "retry" ? 1 : 0.9;
    const total = world.lanes.reduce((s, l) => s + weight(l), 0);
    const unit = Math.min(88, (L.bottom - L.top) / Math.max(total, 1));
    let y = L.top + Math.max(0, (L.bottom - L.top - unit * total) / 2) * 0.7;
    for (const ln of world.lanes) { const h = unit * weight(ln); ln.h = h; ln.y = y + h / 2; y += h; }
    // 컨슈머 자리: 맡은 레인들의 가운데. 그룹이 여럿이면 위아래로 벌린다. 빈손 로봇은 아래쪽
    const gs = groups();
    let idleK = 0;
    const lastY = world.lanes.length ? world.lanes[world.lanes.length - 1].y : L.bottom;
    for (const c of world.consumers) {
      if (c.kind === "retry") { const r = lane("retry"); c.tx = L.consX; c.ty = r ? r.y : L.bottom; continue; }
      const g = gs.indexOf(c.group);
      if (!c.alive) { c.tx = L.consX + 60; continue; }
      if (c.lanes.length) {
        const ys = c.lanes.map(id => lane(id).y);
        c.tx = L.consX; c.ty = ys.reduce((a, b) => a + b, 0) / ys.length + (g - (gs.length - 1) / 2) * 44;
      } else { c.tx = L.consX; c.ty = Math.min(H - 120, lastY + 56 + idleK++ * 46); }
      if (c.x === 0) { c.x = c.tx; c.y = c.ty; }
    }
  }
  function resize() {
    const dpr = Math.min(2, devicePixelRatio || 1);
    canvas.width = Math.round(innerWidth * dpr); canvas.height = Math.round(innerHeight * dpr);
    ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
    layout();
  }
  addEventListener("resize", resize);

  // ------------------------------------------------------------------ 그리기
  const stars = Array.from({ length: 90 }, (_, i) => ({ x: (i * 97.3) % 1, y: (i * 61.7) % 1, r: 0.6 + (i % 3) * 0.5, p: i }));
  function rrect(x, y, w, h, r) { ctx.beginPath(); ctx.roundRect(x, y, w, h, r); }
  function text(s, x, y, { size = 13, color = "#f1f3ff", font = F_BODY, align = "left", base = "middle", weight = "" } = {}) {
    ctx.font = `${weight} ${size}px ${font}`.trim(); ctx.fillStyle = color; ctx.textAlign = align; ctx.textBaseline = base; ctx.fillText(s, x, y);
  }
  function pop(t, x, y, color = "#ffd43b") { pops.push({ t, x, y, life: 1.6, color }); }
  function celebrate() {
    const mz = muzzle(), cols = ["#ffd43b", "#69db7c", "#74c0fc", "#f783ac", "#ffffff"];
    for (let i = 0; i < 36; i++) { const a = Math.random() * Math.PI * 2, v = 60 + Math.random() * 90; sparks.push({ x: mz.x, y: mz.y, vx: Math.cos(a) * v, vy: Math.sin(a) * v - 60, life: 0.9 + Math.random() * 0.4, c: cols[i % cols.length] }); }
  }
  function shake() { if (!reduceMotion) shakeT = 0.3; }

  function drawBlock(m, x, y, w, h, small) {
    const st = m.state;
    const alpha = st === "compacted" ? Math.max(0, m.fadeT ?? 0) : st === "done" ? 0.55 : st === "moved" ? 0.35 : 1;
    if (st === "compacted" && !m.fadeT) { ctx.setLineDash([3, 3]); ctx.strokeStyle = "#3b4a8c"; rrect(x - w / 2, y - h / 2, w, h, 4); ctx.stroke(); ctx.setLineDash([]); return; }
    ctx.globalAlpha = alpha;
    ctx.fillStyle = m.tomb ? "#343a5a" : m.color; rrect(x - w / 2, y - h / 2, w, h, 4); ctx.fill();
    if (m.dup) { ctx.strokeStyle = "#ff8787"; ctx.lineWidth = 2; ctx.stroke(); }
    if (!small) {
      text(shortLabel(m), x, y - 1, { size: 12, color: m.tomb ? "#aab3dd" : "#0b1020", font: F_DISPLAY, align: "center", weight: "" });
      if (st === "done") { ctx.fillStyle = "#69db7c"; ctx.beginPath(); ctx.arc(x + w / 2 - 4, y - h / 2 + 4, 3, 0, Math.PI * 2); ctx.fill(); }
      if (st === "moved") text(m.movedTo === "dlq" ? "→DLQ" : "→RETRY", x, y - h / 2 - 8, { size: 10, color: m.movedTo === "dlq" ? "#ff8787" : "#ffa94d", align: "center", font: F_DISPLAY });
      if (m.readyAt && m.readyAt > elapsed && st === "logged") text((m.readyAt - elapsed).toFixed(1) + "s", x, y - h / 2 - 8, { size: 11, color: "#ffa94d", align: "center", font: F_DISPLAY });
    }
    ctx.globalAlpha = 1; ctx.lineWidth = 1;
  }
  function drawLane(ln) {
    const x0 = L.x0, x1 = L.x1, h = ln.h;
    const col = ln.kind === "retry" ? "#ffa94d" : ln.kind === "dlq" ? "#ff6b6b" : "#4b5aa8";
    const armedHere = mission && !mission.flying && ln.kind === "p" && pLanes()[aim] === ln;
    // 레인 바탕
    ctx.fillStyle = ln.kind === "dlq" ? "rgba(60,20,30,.6)" : ln.kind === "retry" ? "rgba(60,40,20,.55)" : "rgba(20,26,46,.75)";
    rrect(x0, ln.y - h / 2 + 5, x1 - x0, h - 10, 8); ctx.fill();
    ctx.strokeStyle = ln.flashT > 0 ? "#ff8787" : armedHere ? "#ffd43b" : col; ctx.lineWidth = armedHere || ln.flashT > 0 ? 3 : 2; ctx.stroke(); ctx.lineWidth = 1;
    if (ln.flashT > 0) ln.flashT -= 1 / 60;
    text(ln.label, x0 + 10, ln.y - h / 2 + 18, { size: 14, color: armedHere ? "#ffd43b" : col, font: F_DISPLAY });
    if (ln.kind === "p" && mission && mission.lanes && mission.lanes.includes(ln.id) && !mission.flying && world.keyTable == null) { /* 힌트 없음: 플레이어가 고른다 */ }
    if (ln.kind === "dlq") { text("🗑", x1 + 6, ln.y, { size: 18, align: "left" }); text("사람이 확인", x1 + 30, ln.y, { size: 11, color: "#ff8787", font: F_DISPLAY }); }
    // 로그 칸
    const rails = world.replication && ln.kind === "p" ? world.brokers.map(b => b.id) : [null];
    for (const b of rails) {
      const ry = railY(ln, b ?? 0);
      if (b !== null) {
        const br = world.brokers[b], isLeader = ln.leader === b;
        ctx.fillStyle = br.alive ? "rgba(255,255,255,.04)" : "rgba(120,20,30,.45)";
        rrect(x0 + 48, ry - 11, x1 - x0 - 56, 22, 5); ctx.fill();
        text((isLeader ? "👑 " : "") + "브로커 " + b + (br.alive ? "" : " ✕"), x0 + 52, ry - 18, { size: 10, color: br.alive ? (isLeader ? "#ffd43b" : "#aab3dd") : "#ff8787", font: F_DISPLAY });
        if (!br.alive) { for (const m of ln.lost) if (m.lostRail === b) { const s = slotCenter(ln, m.offset); ctx.globalAlpha = .5; drawBlock({ ...m, state: "logged" }, s.x, ry, BW, 18, false); ctx.globalAlpha = 1; text(m.lostLabel, s.x, ry + 16, { size: 9, color: "#ff8787", align: "center", font: F_DISPLAY }); } }
        if (!isLeader) {
          const { start, cap } = slotCenter(ln, ln.log.length);
          ln.log.forEach((m, i) => { if (i < start || !ln.repLogs[b].has(m.id)) return; const sx = x0 + 62 + (i - start) * PITCH + BW / 2; drawBlock(m, sx, ry, BW - 8, 14, true); });
          continue;
        }
      }
      const { start } = slotCenter(ln, ln.log.length);
      ln.log.forEach((m, i) => {
        if (i < start) return;
        const sx = x0 + 62 + (i - start) * PITCH + BW / 2;
        if (m.holder) {   // 로봇이 들고 있는 동안 빈 칸
          ctx.setLineDash([3, 3]); ctx.strokeStyle = m.holder.color; rrect(sx - BW / 2, ry - 11, BW, 22, 4); ctx.stroke(); ctx.setLineDash([]);
        } else drawBlock(m, sx, ry, BW, 22, false);
        text(String(m.offset), sx, ry + 20, { size: 10, color: "#6c7bd1", align: "center", font: F_DISPLAY });
      });
      if (start > 0) text("… +" + start, x0 + 50, ry + 20, { size: 10, color: "#6c7bd1", font: F_DISPLAY });
      // 컨슈머 위치 ▲ 와 커밋 깃발
      if (ln.kind !== "dlq") for (const c of world.consumers) {
        if (!c.alive || !c.lanes.includes(ln.id)) continue;
        const p = c.pos[ln.id] || 0; const s = slotCenter(ln, Math.min(p, ln.log.length)); if (p < start) continue;
        text("▲", s.x, ry + 30, { size: 10, color: c.color, align: "center" });
      }
      if (ln.kind === "p") for (const g of groups()) {
        const cm = committedOf(g, ln.id); const { start: st } = slotCenter(ln, ln.log.length); if (cm < st && cm !== 0) continue;
        const s = slotCenter(ln, cm); const gi = groups().indexOf(g); const col2 = g === "A" ? "#ffd43b" : "#f783ac";
        ctx.fillStyle = col2; ctx.fillRect(s.x - BW / 2 - 1, ry - 30 + gi * 6, 2, 16); ctx.beginPath(); ctx.moveTo(s.x - BW / 2 + 1, ry - 30 + gi * 6); ctx.lineTo(s.x - BW / 2 + 13, ry - 26 + gi * 6); ctx.lineTo(s.x - BW / 2 + 1, ry - 22 + gi * 6); ctx.fill();
      }
    }
  }
  function drawKeyTable() {
    if (!world.keyTable) return;
    const rows = Object.entries(world.keyTable); const x = 12, y = L.bottom + 8, w = 128, h = 18 + rows.length * 18;
    ctx.fillStyle = "rgba(20,26,46,.9)"; rrect(x, y, w, h, 6); ctx.fill(); ctx.strokeStyle = "#6c7bd1"; ctx.stroke();
    text("키 → 레인", x + 8, y + 10, { size: 11, color: "#aab3dd", font: F_DISPLAY });
    rows.forEach(([k, v], i) => { ctx.fillStyle = keyColor(k); ctx.fillRect(x + 8, y + 22 + i * 18, 8, 8); text(`${k}  →  P${v}`, x + 22, y + 26 + i * 18, { size: 12, font: F_DISPLAY }); });
  }
  function drawLauncher() {
    const x = L.launcherX, y = launcherY();
    const ps = pLanes(); const target = ps[Math.min(aim, ps.length - 1)];
    const ang = target ? Math.atan2(railY(target, target.leader ?? 0) - y, (L.x0 + 6) - x) * 0.55 : 0;
    // 받침과 몸통
    ctx.fillStyle = "#2a3463"; rrect(x - 22, y + 14, 44, 10, 3); ctx.fill();
    ctx.fillStyle = "#3b4a8c"; ctx.beginPath(); ctx.arc(x, y + 8, 20, Math.PI, 0); ctx.fill();
    ctx.save(); ctx.translate(x, y); ctx.rotate(ang);
    ctx.fillStyle = "#6c7bd1"; rrect(0, -7, 34, 14, 4); ctx.fill();
    ctx.fillStyle = "#ffd43b"; ctx.fillRect(28, -8, 6, 16);
    ctx.restore();
    text("프로듀서", x, y + 36, { size: 12, color: "#aab3dd", align: "center", font: F_DISPLAY });
    if (world.replication || world.cfg.acks) text("acks=" + world.acks, x, y + 50, { size: 11, color: world.acks === "all" ? "#69db7c" : "#ffa94d", align: "center", font: F_DISPLAY });
    if (world.cfg.idem !== undefined) text("멱등 " + (world.idem ? "ON" : "OFF"), x, y + 50, { size: 11, color: world.idem ? "#69db7c" : "#ff8787", align: "center", font: F_DISPLAY });
    // 장전된 메시지 카드
    if (mission && !mission.flying) {
      const s = mission.spec, label = s.tomb ? (s.key + " = (빈 값)") : s.text;
      ctx.font = `13px ${F_BODY}`; const w = Math.min(L.small ? 150 : 230, ctx.measureText(label).width + 20);
      const cx = x - 20, cy = y - 66;
      ctx.fillStyle = "rgba(20,26,46,.95)"; rrect(cx, cy, w, s.key ? 42 : 28, 6); ctx.fill(); ctx.strokeStyle = "#ffd43b"; ctx.stroke();
      ctx.save(); ctx.beginPath(); ctx.rect(cx, cy, w, 44); ctx.clip();
      text(label, cx + 10, cy + 14, { size: 13 });
      if (s.key) { ctx.fillStyle = keyColor(s.key); ctx.fillRect(cx + 10, cy + 27, 8, 8); text("키: " + s.key, cx + 22, cy + 31, { size: 11, color: "#aab3dd", font: F_DISPLAY }); }
      ctx.restore();
      text(L.small ? "▲▼ 조준 · 발사" : "↑↓ 조준 · Space 발사", x - 20, cy - 10, { size: 11, color: "#ffd43b", font: F_DISPLAY });
    }
  }
  function drawConsumer(c) {
    const { x, y } = c;
    // 배정선
    if (c.alive) for (const id of c.lanes) {
      const ln = lane(id); if (!ln) continue;
      const ry = railY(ln, ln.leader ?? 0);
      ctx.strokeStyle = c.color; ctx.globalAlpha = world.rebalanceT > 0 && c.kind === "group" ? 0.25 : 0.6;
      if (world.rebalanceT > 0 && c.kind === "group") ctx.setLineDash([4, 4]);
      ctx.beginPath(); ctx.moveTo(L.x1, ry); ctx.bezierCurveTo(L.x1 + 30, ry, x - 40, y, x - 18, y); ctx.stroke();
      ctx.setLineDash([]); ctx.globalAlpha = 1;
    }
    // 몸통
    ctx.globalAlpha = c.alive ? 1 : 0.35;
    ctx.fillStyle = c.color; rrect(x - 16, y - 16, 32, 32, 8); ctx.fill();
    ctx.fillStyle = "#0b1020"; ctx.fillRect(x - 9, y - 6, 6, 6); ctx.fillRect(x + 3, y - 6, 6, 6);
    ctx.fillRect(x - 6, y + 5, 12, 3);
    ctx.strokeStyle = c.color; ctx.beginPath(); ctx.moveTo(x, y - 16); ctx.lineTo(x, y - 24); ctx.stroke(); ctx.beginPath(); ctx.arc(x, y - 26, 3, 0, Math.PI * 2); ctx.fill();
    if (c.busy && c.busy.state === "proc") { ctx.strokeStyle = "#ffd43b"; ctx.lineWidth = 3; ctx.beginPath(); ctx.arc(x, y, 22, -Math.PI / 2, -Math.PI / 2 + Math.PI * 2 * Math.min(1, c.procT / world.speed)); ctx.stroke(); ctx.lineWidth = 1; }
    ctx.globalAlpha = 1;
    const status = !c.alive ? "죽음" : c.kind === "group" && world.rebalanceT > 0 ? "대기" : c.busy ? (c.busy.state === "retrywait" ? "재시도 " + Math.max(0, c.retryT).toFixed(1) + "s" : c.busy.state === "proc" ? "처리 중" : "가져오는 중") : c.lanes.length ? "" : "놀고 있음";
    text(c.name + (c.kind === "group" && groups().length > 1 ? "" : ""), x, y + 28, { size: 11, color: c.color, align: "center", font: F_DISPLAY });
    if (status) text(status, x, y + 41, { size: 11, color: status === "놀고 있음" || status === "죽음" ? "#ff8787" : status.startsWith("재시도") ? "#ffa94d" : "#aab3dd", align: "center", font: F_DISPLAY });
  }
  function drawMissile(m) {
    const f = m.fly; let ang = 0;
    if (f) { const p2 = bez(f.from, f.ctrl, f.to, Math.min(1, f.t / f.dur + 0.02)); ang = Math.atan2(p2.y - m.y, p2.x - m.x); }
    if (m.state === "bounce") ang = Math.PI - 0.3;
    if (!reduceMotion && (m.state === "fly" || m.state === "bounce")) sparks.push({ x: m.x - Math.cos(ang) * 14, y: m.y - Math.sin(ang) * 14, vx: -Math.cos(ang) * 40 + (Math.random() - .5) * 30, vy: -Math.sin(ang) * 40 + (Math.random() - .5) * 30, life: 0.35, c: Math.random() < .5 ? "#ffd43b" : "#ffa94d" });
    ctx.save(); ctx.translate(m.x, m.y); ctx.rotate(ang);
    ctx.fillStyle = m.state === "bounce" || m.state === "rejected" ? "#ff8787" : m.color;
    rrect(-14, -7, 22, 14, 4); ctx.fill();
    ctx.beginPath(); ctx.moveTo(8, -8); ctx.lineTo(18, 0); ctx.lineTo(8, 8); ctx.fill();
    ctx.fillStyle = "#0b1020"; ctx.fillRect(-10, -3, 14, 6);
    ctx.fillStyle = "#f1f3ff"; ctx.fillRect(-14, -9, 4, 18);
    ctx.restore();
    if (m.state === "fly" || m.state === "pick") text(shortLabel(m), m.x, m.y - 16, { size: 11, color: "#f1f3ff", align: "center", font: F_DISPLAY });
  }
  function drawSparks(dt) {
    for (let i = sparks.length - 1; i >= 0; i--) {
      const p = sparks[i]; p.life -= dt; if (p.life <= 0) { sparks.splice(i, 1); continue; }
      p.vy += 120 * dt; p.x += p.vx * dt; p.y += p.vy * dt;
      ctx.fillStyle = p.c; ctx.globalAlpha = Math.min(1, p.life * 2); ctx.fillRect(p.x, p.y, 3, 3);
    }
    ctx.globalAlpha = 1;
  }
  function drawPops(dt) {
    for (let i = pops.length - 1; i >= 0; i--) {
      const p = pops[i]; p.life -= dt; if (p.life <= 0) { pops.splice(i, 1); continue; }
      p.y -= 18 * dt;
      ctx.globalAlpha = Math.min(1, p.life * 1.5);
      ctx.font = `14px ${F_DISPLAY}`; const w = ctx.measureText(p.t).width + 14;
      const x = Math.max(6, Math.min(L.W - w - 6, p.x - w / 2));
      ctx.fillStyle = "rgba(11,16,32,.85)"; rrect(x, p.y - 11, w, 22, 5); ctx.fill();
      text(p.t, x + 7, p.y, { size: 14, color: p.color, font: F_DISPLAY });
    }
    ctx.globalAlpha = 1;
  }
  function draw(dt) {
    const W = L.W, H = L.H;
    ctx.save();
    if (shakeT > 0) { shakeT -= dt; ctx.translate((Math.random() - .5) * 6, (Math.random() - .5) * 6); }
    const g = ctx.createLinearGradient(0, 0, 0, H); g.addColorStop(0, "#0b1020"); g.addColorStop(1, "#141b38");
    ctx.fillStyle = g; ctx.fillRect(-10, -10, W + 20, H + 20);
    for (const s of stars) { ctx.globalAlpha = 0.35 + 0.35 * Math.sin(elapsed * 1.3 + s.p); ctx.fillStyle = "#c5cdf5"; ctx.fillRect(s.x * W, s.y * H, s.r, s.r); }
    ctx.globalAlpha = 1;
    if (!world) { ctx.restore(); return; }
    text("토픽: " + (world.compact ? "inventory-state" : "orders"), L.x0, L.top - 10, { size: 12, color: "#6c7bd1", font: F_DISPLAY });
    for (const ln of world.lanes) drawLane(ln);
    drawKeyTable();
    drawLauncher();
    for (const c of world.consumers) drawConsumer(c);
    for (const m of msgs) if ((m.fly && m.state !== "return") || ["bounce", "rejected"].includes(m.state)) drawMissile(m);
    for (const m of msgs) if (m.fly && m.state === "return") drawBlock(m, m.x, m.y, BW, 22, false);
    for (const c of world.consumers) if (c.busy && !c.busy.fly && ["proc", "retrywait"].includes(c.busy.state)) drawBlock({ ...c.busy, state: "logged" }, c.x, c.y - 44, BW + 6, 22, false);
    if (world.rebalanceT > 0) {
      const w = Math.min(420, W - 40); ctx.fillStyle = "rgba(60,30,10,.92)"; rrect(W / 2 - w / 2, L.top - 30, w, 34, 8); ctx.fill(); ctx.strokeStyle = "#ffa94d"; ctx.stroke();
      text("리밸런싱 중… " + world.rebalanceMsg + " → 레인을 다시 나눕니다. 모두 멈춤", W / 2, L.top - 13, { size: 13, color: "#ffa94d", align: "center", font: F_DISPLAY });
    }
    drawSparks(dt); drawPops(dt);
    ctx.restore();
  }

  // ------------------------------------------------------------------ 루프
  let last = performance.now(), acc = 0;
  const STEP = 1 / 60;
  function frame(now) {
    const dt = Math.min(0.25, (now - last) / 1000); last = now;
    if (world && !busy) { acc += dt; while (acc >= STEP) { update(STEP); elapsed += STEP; acc -= STEP; } }
    else acc = 0;
    draw(dt);
    requestAnimationFrame(frame);
  }
  resize();
  renderHud();
  state.started = !!saved;
  showMenu();
  requestAnimationFrame(frame);
  window.__kq = { get busy() { return busy; }, get world() { return world; }, get msgs() { return msgs; }, state, fire, setAim, startChapter, tick: (n) => { for (let i = 0; i < n; i++) { update(STEP); elapsed += STEP; } }, get mission() { return mission; }, get pending() { return pending; } };   // 디버그용
})();
