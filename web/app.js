/* PayMexBTC · plataforma: cotizador, rutas, FSM, tesorería, cumplimiento y comprobantes */
(() => {
  'use strict';

  /* ================= utilidades ================= */
  const $ = (s, r = document) => r.querySelector(s);
  const $$ = (s, r = document) => Array.from(r.querySelectorAll(s));
  const esc = (s) => String(s).replace(/[&<>"']/g, (c) => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' }[c]));
  const nf = (d) => new Intl.NumberFormat('es-MX', { minimumFractionDigits: d, maximumFractionDigits: d });
  const N0 = nf(0), N2 = nf(2), N4 = nf(4), N6 = nf(6);
  const SYM = { MXN: '$', HKD: 'HK$', CNH: 'CN¥' };
  const money = (v, c = 'MXN') => SYM[c] + N2.format(v);
  const fbtc = (v) => N6.format(v) + ' BTC';
  const parseNum = (s) => { const v = parseFloat(String(s).replace(/[^\d.]/g, '')); return Number.isFinite(v) ? v : NaN; };
  const pad = (n, w = 2) => String(n).padStart(w, '0');
  const hms = (d) => `${pad(d.getHours())}:${pad(d.getMinutes())}:${pad(d.getSeconds())}`;
  const fdate = (d) => d.toLocaleDateString('es-MX', { day: '2-digit', month: 'short', year: 'numeric' });
  const fdt = (d) => `${fdate(d)} ${pad(d.getHours())}:${pad(d.getMinutes())}`;
  const ymd = (d) => `${String(d.getFullYear()).slice(2)}${pad(d.getMonth() + 1)}${pad(d.getDate())}`;
  const SUP = { '0': '⁰', '1': '¹', '2': '²', '3': '³', '4': '⁴', '5': '⁵', '6': '⁶', '7': '⁷', '8': '⁸', '9': '⁹', '-': '⁻' };
  const sci = (p) => {
    if (p >= 0.001) return p.toFixed(4);
    if (p <= 0) return '0';
    const e = Math.floor(Math.log10(p));
    const m = p / Math.pow(10, e);
    return `${m.toFixed(1)} × 10${String(e).split('').map((c) => SUP[c]).join('')}`;
  };
  const sleep = (ms) => new Promise((r) => setTimeout(r, ms));
  const reduced = window.matchMedia('(prefers-reduced-motion: reduce)').matches;
  const gauss = () => { let u = 0, v = 0; while (!u) u = Math.random(); while (!v) v = Math.random(); return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v); };

  /* ================= SHA-256 (síncrono) ================= */
  const K = [
    0x428a2f98, 0x71374491, 0xb5c0fbcf, 0xe9b5dba5, 0x3956c25b, 0x59f111f1, 0x923f82a4, 0xab1c5ed5,
    0xd807aa98, 0x12835b01, 0x243185be, 0x550c7dc3, 0x72be5d74, 0x80deb1fe, 0x9bdc06a7, 0xc19bf174,
    0xe49b69c1, 0xefbe4786, 0x0fc19dc6, 0x240ca1cc, 0x2de92c6f, 0x4a7484aa, 0x5cb0a9dc, 0x76f988da,
    0x983e5152, 0xa831c66d, 0xb00327c8, 0xbf597fc7, 0xc6e00bf3, 0xd5a79147, 0x06ca6351, 0x14292967,
    0x27b70a85, 0x2e1b2138, 0x4d2c6dfc, 0x53380d13, 0x650a7354, 0x766a0abb, 0x81c2c92e, 0x92722c85,
    0xa2bfe8a1, 0xa81a664b, 0xc24b8b70, 0xc76c51a3, 0xd192e819, 0xd6990624, 0xf40e3585, 0x106aa070,
    0x19a4c116, 0x1e376c08, 0x2748774c, 0x34b0bcb5, 0x391c0cb3, 0x4ed8aa4a, 0x5b9cca4f, 0x682e6ff3,
    0x748f82ee, 0x78a5636f, 0x84c87814, 0x8cc70208, 0x90befffa, 0xa4506ceb, 0xbef9a3f7, 0xc67178f2,
  ];
  const H0 = [0x6a09e667, 0xbb67ae85, 0x3c6ef372, 0xa54ff53a, 0x510e527f, 0x9b05688c, 0x1f83d9ab, 0x5be0cd19];
  const rotr = (x, n) => (x >>> n) | (x << (32 - n));
  function sha256(msg) {
    const H = H0.slice();
    const l = msg.length;
    const padLen = ((l + 9 + 63) >> 6) << 6;
    const buf = new Uint8Array(padLen);
    buf.set(msg); buf[l] = 0x80;
    const dv = new DataView(buf.buffer);
    const bits = l * 8;
    dv.setUint32(padLen - 8, Math.floor(bits / 0x100000000));
    dv.setUint32(padLen - 4, bits >>> 0);
    const W = new Uint32Array(64);
    for (let off = 0; off < padLen; off += 64) {
      for (let i = 0; i < 16; i++) W[i] = dv.getUint32(off + i * 4);
      for (let i = 16; i < 64; i++) {
        const a = W[i - 15], b = W[i - 2];
        const s0 = rotr(a, 7) ^ rotr(a, 18) ^ (a >>> 3);
        const s1 = rotr(b, 17) ^ rotr(b, 19) ^ (b >>> 10);
        W[i] = (W[i - 16] + s0 + W[i - 7] + s1) >>> 0;
      }
      let [a, b, c, d, e, f, g, h] = H;
      for (let i = 0; i < 64; i++) {
        const S1 = rotr(e, 6) ^ rotr(e, 11) ^ rotr(e, 25);
        const ch = (e & f) ^ (~e & g);
        const t1 = (h + S1 + ch + K[i] + W[i]) >>> 0;
        const S0 = rotr(a, 2) ^ rotr(a, 13) ^ rotr(a, 22);
        const mj = (a & b) ^ (a & c) ^ (b & c);
        const t2 = (S0 + mj) >>> 0;
        h = g; g = f; f = e; e = (d + t1) >>> 0; d = c; c = b; b = a; a = (t1 + t2) >>> 0;
      }
      H[0] = (H[0] + a) >>> 0; H[1] = (H[1] + b) >>> 0; H[2] = (H[2] + c) >>> 0; H[3] = (H[3] + d) >>> 0;
      H[4] = (H[4] + e) >>> 0; H[5] = (H[5] + f) >>> 0; H[6] = (H[6] + g) >>> 0; H[7] = (H[7] + h) >>> 0;
    }
    const out = new Uint8Array(32);
    const odv = new DataView(out.buffer);
    H.forEach((v, i) => odv.setUint32(i * 4, v));
    return out;
  }
  const utf8 = (s) => new TextEncoder().encode(s);
  const hex = (b) => Array.from(b, (x) => x.toString(16).padStart(2, '0')).join('');
  const unhex = (h) => new Uint8Array(h.match(/../g).map((x) => parseInt(x, 16)));
  const dsha = (b) => sha256(sha256(b));
  const cat = (a, b) => { const o = new Uint8Array(a.length + b.length); o.set(a); o.set(b, a.length); return o; };
  const randBytes = (n) => { const b = new Uint8Array(n); crypto.getRandomValues(b); return b; };
  const hashOf = (s) => hex(sha256(utf8(s)));
  const short = (h, n = 10) => `${h.slice(0, n)}…${h.slice(-6)}`;
  const digits = (seed, n) => { const h = hashOf(seed); let s = ''; for (let i = 0; s.length < n; i++) s += parseInt(h.slice(i * 2, i * 2 + 2), 16) % 10; return s; };

  /* ================= mercado ================= */
  const SIGMA = 0.55; // vol anual BTC
  const R = { btcMxn: 1782400, mxnPerUsd: 18.42, hkdPerUsd: 7.79, cnhPerUsd: 7.12, feeRate: 9 };
  const mxnPerHkd = () => R.mxnPerUsd / R.hkdPerUsd;
  const btcHkd = () => R.btcMxn / mxnPerHkd();
  const toHkd = (amt, ccy) => (ccy === 'HKD' ? amt : amt * (R.hkdPerUsd / R.cnhPerUsd));

  // historia por minuto, 120 puntos
  const HIST = (() => {
    const out = new Array(120);
    out[119] = R.btcMxn;
    const dt = 1 / 525600;
    for (let i = 118; i >= 0; i--) out[i] = out[i + 1] / Math.exp(-0.5 * SIGMA * SIGMA * dt + SIGMA * Math.sqrt(dt) * gauss());
    return out;
  })();

  /* ================= tesorería ================= */
  const T = { hot: 4.82, cold: 31.4, lnLocal: 0.85, lnRemote: 0.4, hkd: 3280000, mxn: 2940000 };

  /* ================= proveedores y evidencia ================= */
  const SUPPLIERS = [
    { id: 'hengli', name: 'Shenzhen Hengli Garment Co., Ltd.', bank: 'HSBC', code: '004', fps: '163 820 47', prev: 14, ev: [] },
    { id: 'tsuen', name: 'Tsuen Wan Knit Works Ltd.', bank: 'Hang Seng Bank', code: '024', fps: '117 290 35', prev: 6, ev: [] },
    { id: 'pearl', name: 'Pearl Delta Cotton Works', bank: 'Bank of China (HK)', code: '012', fps: '129 044 18', prev: 1, ev: [] },
    { id: 'lantau', name: 'Lantau Fabric Supply Co.', bank: 'Standard Chartered HK', code: '003', fps: '150 337 92', prev: 0, ev: ['nuevo', 'estructura'] },
    { id: 'harbour', name: 'Harbourline Apparel Trading', bank: 'DBS Bank (HK)', code: '016', fps: '184 401 72', prev: 0, ev: ['nuevo', 'mixer', 'estructura', 'sinped'] },
  ];
  const supById = (id) => SUPPLIERS.find((s) => s.id === id);

  const EVIDENCE = [
    { id: 'mixer', t: 'Fondos a 2 saltos o menos de un mixer', pi: 0.62, pl: 0.02 },
    { id: 'sanc', t: 'Contraparte o banco en jurisdicción sancionada', pi: 0.4, pl: 0.004 },
    { id: 'estructura', t: 'Estructuración: pagos fraccionados bajo umbral en 24 h', pi: 0.55, pl: 0.04 },
    { id: 'nuevo', t: 'Proveedor sin historial con el importador', pi: 0.7, pl: 0.3 },
    { id: 'atipico', t: 'Monto mayor a 3σ del perfil transaccional', pi: 0.5, pl: 0.06 },
    { id: 'sinped', t: 'Factura comercial sin pedimento asociado', pi: 0.45, pl: 0.1 },
  ];
  const PRIOR = 0.01;
  const THETA = 0.75;
  function posterior(evSet) {
    let li = PRIOR, ll = 1 - PRIOR;
    for (const e of EVIDENCE) {
      const on = evSet.includes(e.id);
      li *= on ? e.pi : 1 - e.pi;
      ll *= on ? e.pl : 1 - e.pl;
    }
    return li / (li + ll);
  }
  const verdict = (p) => (p > THETA ? 'crit' : p >= 0.25 ? 'warn' : 'ok');
  const evFor = (sup, mid) => {
    const ev = sup.ev.slice();
    if (mid > 2500000 && !ev.includes('atipico')) ev.push('atipico');
    return ev;
  };

  /* ================= Lightning: Dijkstra con −η ln p(a) ================= */
  const LN_NAMES = { PMX: 'PayMex MX', PMA: 'PayMex Asia', HUBN: 'Hub Norteamérica', HUBE: 'Hub Europa', HUBS: 'Hub Singapur' };
  const LN_EDGES = () => [
    { u: 'PMX', v: 'PMA', cap: T.lnLocal, base: 0, ppm: 0, own: true },
    { u: 'PMX', v: 'HUBN', cap: 3.0, base: 1, ppm: 150 },
    { u: 'HUBN', v: 'HUBS', cap: 2.5, base: 1, ppm: 300 },
    { u: 'HUBS', v: 'PMA', cap: 2.0, base: 0, ppm: 100 },
    { u: 'PMX', v: 'HUBE', cap: 1.6, base: 1, ppm: 80 },
    { u: 'HUBE', v: 'PMA', cap: 1.4, base: 1, ppm: 220 },
    { u: 'HUBE', v: 'HUBS', cap: 4.0, base: 1, ppm: 50 },
  ];
  function lnRoute(aBtc) {
    const aSat = aBtc * 1e8, eta = 5000;
    const edges = LN_EDGES();
    const nodes = Object.keys(LN_NAMES);
    const dist = Object.fromEntries(nodes.map((n) => [n, Infinity]));
    const prev = {};
    const done = new Set();
    dist.PMX = 0;
    while (done.size < nodes.length) {
      let u = null;
      for (const n of nodes) if (!done.has(n) && (u === null || dist[n] < dist[u])) u = n;
      if (u === null || dist[u] === Infinity) break;
      done.add(u);
      for (const e of edges) {
        if (e.u !== u) continue;
        const p = e.own ? (aBtc <= e.cap ? 1 : 0) : Math.max(0, (e.cap - aBtc) / e.cap);
        if (p <= 0) continue;
        const fee = e.base + (aSat * e.ppm) / 1e6;
        const w = fee - eta * Math.log(p);
        if (dist[u] + w < dist[e.v]) { dist[e.v] = dist[u] + w; prev[e.v] = { from: u, fee, p }; }
      }
    }
    if (dist.PMA === Infinity) return null;
    const path = ['PMA'];
    let feeSat = 0, prob = 1, cur = 'PMA';
    while (cur !== 'PMX') { const st = prev[cur]; feeSat += st.fee; prob *= st.p; cur = st.from; path.unshift(cur); }
    return { path, feeSat, prob };
  }

  /* ================= cotización y flujo a costo mínimo ================= */
  const varBps = (hMin, sigma = SIGMA) => (1 - Math.exp(-2.326 * sigma * Math.sqrt(hMin / 525600))) * 1e4;
  const spreadBps = (hMin) => 18 + 0.25 * varBps(hMin);
  const COMM = 0.005, IVA = 0.16;
  const satToMxn = (s) => (s / 1e8) * R.btcMxn;

  function buildQuote(amount, ccy, supId) {
    const hkd = toHkd(amount, ccy);
    const mid = hkd * mxnPerHkd();
    const usd = mid / R.mxnPerUsd;
    const aBtc = mid / R.btcMxn;
    const z = usd > 50000 ? 6 : 3;
    const chainMin = z * 10 + 5;
    const chainFeeSat = R.feeRate * 111;
    const otcBps = usd > 20000 ? 0.7 * (SIGMA / Math.sqrt(365)) * Math.sqrt(aBtc / 250) * 1e4 : 0;
    const routes = [];

    const ln = lnRoute(aBtc);
    const lnOk = !!ln && ln.prob >= 0.35;
    const lnSpread = (mid * spreadBps(2)) / 1e4;
    routes.push({
      key: 'ln', name: 'Lightning', ok: lnOk,
      leg: ln ? ln.path.map((n) => LN_NAMES[n]).join(' → ') : 'Sin ruta con capacidad',
      time: 'segundos', prob: ln ? ln.prob : 0,
      netMxn: ln ? satToMxn(ln.feeSat) : 0, spreadMxn: lnSpread, spreadB: spreadBps(2),
      why: !ln ? 'Monto mayor a la capacidad de los canales' : ln.prob < 0.35 ? `Probabilidad de entrega ${(ln.prob * 100).toFixed(0)}% < 35%` : '',
      path: ln ? ln.path : null, lnFeeSat: ln ? ln.feeSat : 0,
    });

    routes.push({
      key: 'chain', name: 'On-chain Taproot', ok: true,
      leg: `MuSig2 key-path · ${z} confirmaciones`, time: `≈ ${chainMin} min`, prob: 1,
      netMxn: satToMxn(chainFeeSat), spreadMxn: (mid * spreadBps(chainMin)) / 1e4, spreadB: spreadBps(chainMin), why: '',
    });

    const lnPart = Math.min(aBtc, T.lnLocal * 0.95);
    const hybOk = aBtc > T.lnLocal * 0.95 && lnPart > 0.01;
    const share = hybOk ? lnPart / aBtc : 0;
    const hybSpreadB = share * spreadBps(2) + (1 - share) * spreadBps(chainMin);
    routes.push({
      key: 'hybrid', name: 'Híbrido', ok: hybOk,
      leg: hybOk ? `${fbtc(lnPart)} por canal directo + ${fbtc(aBtc - lnPart)} on-chain` : 'El monto cabe en el canal directo',
      time: `parcial en segundos, resto ≈ ${chainMin} min`, prob: 1,
      netMxn: satToMxn(chainFeeSat), spreadMxn: (mid * hybSpreadB) / 1e4, spreadB: hybSpreadB,
      why: hybOk ? '' : 'No aplica', lnPart,
    });

    routes.forEach((r) => { r.cost = r.netMxn + r.spreadMxn; });
    const best = routes.filter((r) => r.ok).sort((a, b) => a.cost - b.cost)[0];
    const otcMxn = (mid * otcBps) / 1e4;
    const comm = mid * COMM;
    const iva = comm * IVA;
    const total = mid + best.cost + otcMxn + comm + iva;
    const sup = supById(supId) || SUPPLIERS[0];
    const ev = evFor(sup, mid);
    const aml = posterior(ev);
    const balance = best.key === 'ln' ? T.lnLocal : best.key === 'hybrid' ? T.lnLocal + T.hot : T.hot;
    return { amount, ccy, hkd, mid, usd, aBtc, z, chainMin, otcBps, otcMxn, comm, iva, total, routes, best, sup, ev, aml, balance, rateMid: mxnPerHkd(), at: Date.now() };
  }

  /* ================= operaciones ================= */
  let opSeq = 412;
  const OPS = [];
  const clabe = (seed) => {
    const base = '646180' + digits(seed, 11);
    const w = [3, 7, 1];
    let s = 0;
    for (let i = 0; i < 17; i++) s += (parseInt(base[i], 10) * w[i % 3]) % 10;
    return base + ((10 - (s % 10)) % 10);
  };

  function makeOp(q, routeKey, date, extra = {}) {
    const route = q.routes.find((r) => r.key === routeKey) || q.best;
    const id = `PMX-${ymd(date)}-${pad(opSeq++, 4)}`;
    const total = q.mid + route.cost + q.otcMxn + q.comm + q.iva;
    const preimage = hashOf(id + ':R');
    const op = {
      id, date, sup: q.sup, invoice: extra.invoice || '', amount: q.amount, ccy: q.ccy, hkd: q.hkd, mid: q.mid,
      total, rate: total / q.amount, btc: q.aBtc, route: route.key, routeName: route.name, z: q.z,
      spreadMxn: route.spreadMxn, netMxn: route.netMxn, otcMxn: q.otcMxn, comm: q.comm, iva: q.iva,
      ev: q.ev.slice(), aml: q.aml, state: extra.state || 'HKD_SETTLED',
      preimage, paymentHash: hex(sha256(unhex(preimage))),
      txid: hex(dsha(utf8(id + ':tx'))), block: 921000 + (parseInt(hashOf(id).slice(0, 4), 16) % 4000),
      fps: `FRN${ymd(date)}${digits(id + 'fps', 10)}`,
      clave: `PMX${ymd(date)}${digits(id + 'sp', 8)}`,
      clabe: clabe(id),
      pedimento: extra.pedimento || '',
      lnPath: route.path || (route.key === 'hybrid' ? ['PMX', 'PMA'] : null),
    };
    return op;
  }

  function seedOps() {
    const day = (d, h, m) => { const x = new Date(Date.now() - d * 86400000); x.setHours(h, m, 12, 0); return x; };
    const keepLn = T.lnLocal;
    T.lnLocal = 0.85;
    const seeds = [
      { d: 9, h: 10, m: 14, sup: 'hengli', inv: 'HL-2026-0362', amt: 612500, ccy: 'HKD', route: 'chain', ped: '26 16 3165 6004417' },
      { d: 6, h: 12, m: 41, sup: 'tsuen', inv: 'TWK/26/1187', amt: 138400, ccy: 'HKD', route: 'ln', ped: '26 43 3165 6004682' },
      { d: 4, h: 9, m: 5, sup: 'pearl', inv: 'PDC-88412', amt: 254000, ccy: 'CNH', route: 'ln', ped: '' },
      { d: 2, h: 16, m: 22, sup: 'lantau', inv: 'LFS-2026-0733', amt: 1960000, ccy: 'HKD', route: 'hybrid', state: 'REVIEW' },
      { d: 1, h: 11, m: 37, sup: 'harbour', inv: 'HAT-1102', amt: 395000, ccy: 'HKD', route: 'ln', state: 'REVERTED' },
    ];
    for (const s of seeds) {
      const q = buildQuote(s.amt, s.ccy, s.sup);
      const op = makeOp(q, s.route, day(s.d, s.h, s.m), { invoice: s.inv, state: s.state, pedimento: s.ped });
      if (s.state === 'REVIEW') { op.ev = q.ev; op.aml = posterior(op.ev); }
      OPS.unshift(op);
    }
    T.lnLocal = keepLn;
  }

  /* ================= toast ================= */
  let toastT;
  function toast(msg) {
    const t = $('#toast');
    t.textContent = msg;
    t.hidden = false;
    clearTimeout(toastT);
    toastT = setTimeout(() => { t.hidden = true; }, 3600);
  }
  async function copyText(text, btn) {
    try { await navigator.clipboard.writeText(text); if (btn) { const o = btn.textContent; btn.textContent = 'Copiado'; setTimeout(() => { btn.textContent = o; }, 1400); } }
    catch (e) { toast('No se pudo copiar. Selecciona el texto y cópialo manualmente.'); }
  }

  /* ================= ticker ================= */
  function renderTicker(prev) {
    const set = (id, txt, dir) => {
      const b = $(id); if (!b) return;
      b.textContent = txt;
      if (dir) { b.classList.remove('up', 'down'); b.classList.add(dir); setTimeout(() => b.classList.remove(dir), 700); }
    };
    const dir = prev == null ? null : R.btcMxn > prev ? 'up' : R.btcMxn < prev ? 'down' : null;
    set('#tkBtcMxn', '$' + N0.format(R.btcMxn), dir);
    set('#tkBtcHkd', 'HK$' + N0.format(btcHkd()), dir);
    set('#tkHkdMxn', N4.format(mxnPerHkd()));
    set('#tkFee', `${R.feeRate} sat/vB`);
    const hr = $('#hqRateLabel'); if (hr) hr.textContent = `HKD/MXN ${N4.format(mxnPerHkd())}`;
  }
  let tickN = 0;
  function tick() {
    const dt = 2 / (365 * 86400);
    const prev = R.btcMxn;
    R.btcMxn *= Math.exp(-0.5 * SIGMA * SIGMA * dt + SIGMA * Math.sqrt(dt) * gauss());
    R.mxnPerUsd *= Math.exp(0.11 * Math.sqrt(dt) * gauss());
    if (++tickN % 9 === 0) R.feeRate = Math.min(22, Math.max(5, R.feeRate + Math.round(gauss())));
    if (tickN % 30 === 0) { HIST.shift(); HIST.push(R.btcMxn); } else HIST[HIST.length - 1] = R.btcMxn;
    renderTicker(prev);
    renderHeroQuote();
    if (current === 'tesoreria') { renderChart(); renderVar(); renderPositions(); }
  }

  /* ================= hero cotizador ================= */
  function renderHeroQuote() {
    const inp = $('#hqHkd'); if (!inp || $('#landing').hidden) return;
    const v = parseNum(inp.value);
    const rows = $('#hqRows');
    if (!(v > 0)) { rows.innerHTML = '<div class="qrow"><span>Captura un monto mayor a cero</span><span></span></div>'; $('#hqTotal').textContent = '—'; $('#hqRoute').textContent = ''; return; }
    const q = buildQuote(v, 'HKD', 'hengli');
    rows.innerHTML = [
      ['Tipo de referencia', `${N4.format(q.rateMid)} MXN/HKD`],
      ['Spread de ruta + impacto OTC', money(q.best.spreadMxn + q.otcMxn)],
      ['Red Bitcoin', money(q.best.netMxn)],
      ['Comisión 0.50% + IVA', money(q.comm + q.iva)],
    ].map(([a, b]) => `<div class="qrow"><span>${a}</span><span>${b}</span></div>`).join('');
    $('#hqTotal').textContent = money(q.total);
    $('#hqRoute').innerHTML = `Ruta elegida: <b>${esc(q.best.name)}</b> · ${fbtc(q.aBtc)} en tránsito · tipo todo incluido ${N4.format(q.total / q.hkd)}`;
  }

  /* ================= router ================= */
  const VIEWS = ['pagar', 'tesoreria', 'cumplimiento', 'comprobantes'];
  let current = 'inicio';
  function route() {
    const h = (location.hash || '#inicio').slice(1);
    if (VIEWS.includes(h)) {
      $('#landing').hidden = true;
      $('#app').hidden = false;
      current = h;
      VIEWS.forEach((v) => { $('#view-' + v).hidden = v !== h; });
      $$('.side__link').forEach((a) => { if (a.dataset.view === h) a.setAttribute('aria-current', 'page'); else a.removeAttribute('aria-current'); });
      window.scrollTo(0, 0);
      RENDER[h]();
    } else {
      $('#app').hidden = true;
      $('#landing').hidden = false;
      current = 'inicio';
      renderHeroQuote();
      const target = h !== 'inicio' ? document.getElementById(h) : null;
      if (target) target.scrollIntoView(); else window.scrollTo(0, 0);
    }
  }
  const go = (h) => { if (location.hash === '#' + h) route(); else location.hash = h; };

  /* ================= PAGAR ================= */
  let Q = null;            // cotización vigente
  let lockStart = 0, lockTimer = null, running = false;
  const LOCK_S = 10;

  function initPay() {
    const sel = $('#pfSupplier');
    sel.innerHTML = SUPPLIERS.map((s) => `<option value="${s.id}">${esc(s.name)}</option>`).join('');
    const meta = () => {
      const s = supById(sel.value);
      $('#pfSupplierMeta').textContent = `${s.bank} · código ${s.code} · FPS ID ${s.fps} · ${s.prev ? s.prev + ' pagos previos' : 'alta reciente'}`;
    };
    sel.addEventListener('change', () => { meta(); invalidateQuote(); });
    meta();
    $$('input[name="ccy"]').forEach((r) => r.addEventListener('change', () => { $('#pfAffix').textContent = SYM[r.value]; invalidateQuote(); }));
    const amt = $('#pfAmount');
    amt.addEventListener('input', invalidateQuote);
    amt.addEventListener('blur', () => { const v = parseNum(amt.value); if (v > 0) amt.value = N2.format(v).replace(/\.00$/, ''); });
    $('#payForm').addEventListener('submit', (e) => { e.preventDefault(); doQuote(); });
    $('#qConfirm').addEventListener('click', confirmQuote);
    $('#qRequote').addEventListener('click', doQuote);
    $('#trackNew').addEventListener('click', () => {
      $('#trackPanel').hidden = true;
      Q = null; showQuote();
      $('#pfAmount').focus();
    });
  }

  function invalidateQuote() {
    if (running || !Q) return;
    stopLock();
    Q = null;
    showQuote();
  }

  function doQuote() {
    if (running) return;
    const amtEl = $('#pfAmount');
    const ctl = amtEl.closest('.field__control');
    const err = $('#pfError');
    const v = parseNum(amtEl.value);
    const ccy = $('input[name="ccy"]:checked').value;
    let msg = '';
    if (!(v > 0)) msg = 'Captura el monto de la factura. Usa solo números, como 480,000.';
    else if (toHkd(v, ccy) > 20000000) msg = 'El monto supera HK$20,000,000 por operación. Divide la factura o contacta a la mesa OTC.';
    else if (!$('#pfInvoice').value.trim()) msg = 'Captura el número de Commercial Invoice. Se imprime en el comprobante para aduana.';
    if (msg) { err.textContent = msg; err.hidden = false; ctl.setAttribute('aria-invalid', 'true'); return; }
    err.hidden = true; ctl.removeAttribute('aria-invalid');
    Q = buildQuote(v, ccy, $('#pfSupplier').value);
    showQuote();
    startLock();
  }

  function lockValid() { return !!Q && (Date.now() - lockStart) / 1000 < LOCK_S; }

  function startLock() {
    stopLock();
    lockStart = Date.now();
    renderAuth();
    const lock = $('#lock');
    lock.classList.remove('is-off', 'is-low');
    const bar = $('#lockBar');
    const upd = () => {
      const rem = Math.max(0, LOCK_S - (Date.now() - lockStart) / 1000);
      $('#lockN').textContent = Math.ceil(rem);
      bar.style.strokeDashoffset = String(119.4 * (1 - rem / LOCK_S));
      lock.classList.toggle('is-low', rem <= 3 && rem > 0);
      if (rem <= 0) {
        stopLock();
        lock.classList.add('is-off');
        $('#qConfirm').disabled = true;
        $('#qRequote').hidden = false;
        renderAuth();
        $('#qReceive').textContent = 'Cotización vencida. Recotiza para fijar un nuevo tipo de cambio.';
      }
    };
    upd();
    lockTimer = setInterval(upd, 200);
  }
  function stopLock() { clearInterval(lockTimer); lockTimer = null; }

  function renderAuth() {
    if (!Q) return;
    const b = Q.balance >= Q.aBtc, a = Q.aml < THETA, l = lockValid() || running;
    const t = (ok) => `<span class="${ok ? 't' : 'f'}">${ok ? '1' : '0'}</span>`;
    $('#qAuth').innerHTML =
      `Auth = (Saldo<sub>BTC</sub> ${N6.format(Q.balance)} ≥ ${N6.format(Q.aBtc)}) ${t(b)}<br>` +
      `&nbsp;&nbsp;∧ (AML ${Q.aml < 0.001 ? sci(Q.aml) : Q.aml.toFixed(4)} &lt; ${THETA}) ${t(a)}<br>` +
      `&nbsp;&nbsp;∧ (Rate_Lock_Valid) ${t(l)}<br>` +
      `&nbsp;&nbsp;= ${t(b && a && l)}`;
    if (!running) $('#qConfirm').disabled = !(b && l);
  }

  function showQuote() {
    const has = !!Q;
    $('#quoteEmpty').hidden = has;
    $('#quoteBody').hidden = !has;
    if (!has) return;
    const q = Q;
    $('#qTotal').textContent = money(q.total);
    $('#qReceive').textContent = `${q.sup.name.split(' ').slice(0, 3).join(' ')} recibe ${money(q.amount, q.ccy)} · tipo todo incluido ${N4.format(q.total / q.amount)} MXN/${q.ccy}`;
    const rows = [
      [`Tipo de referencia ${q.ccy}/MXN`, N4.format(q.mid / q.amount)],
      ['Principal a tipo medio', money(q.mid)],
      [`Spread dinámico, ${q.best.name} (${q.best.spreadB.toFixed(1)} pb)`, money(q.best.spreadMxn)],
    ];
    if (q.otcMxn > 0) rows.push([`Impacto de mercado OTC √(Q/V) (${q.otcBps.toFixed(1)} pb)`, money(q.otcMxn)]);
    rows.push(
      ['Red Bitcoin', money(q.best.netMxn)],
      ['Comisión de plataforma 0.50%', money(q.comm)],
      ['IVA 16% sobre comisión', money(q.iva)],
      ['BTC en tránsito', fbtc(q.aBtc)],
    );
    $('#qBreak').innerHTML = rows.map(([a, b]) => `<div><dt>${a}</dt><dd>${b}</dd></div>`).join('');
    $('#qRoutes').innerHTML =
      '<thead><tr><th scope="col">Ruta</th><th scope="col">Tramo</th><th scope="col">Tiempo</th><th scope="col" class="num">P(entrega)</th><th scope="col" class="num">Red</th><th scope="col" class="num">Spread</th><th scope="col" class="num">Costo</th></tr></thead><tbody>' +
      q.routes.map((r) => `<tr class="${r === q.best ? 'is-best' : ''} ${r.ok ? '' : 'is-off'}">
        <td>${esc(r.name)}${r === q.best ? ' <span class="chip chip--accent">Elegida</span>' : ''}</td>
        <td>${esc(r.ok ? r.leg : r.why || r.leg)}</td>
        <td>${esc(r.time)}</td>
        <td class="num">${r.ok || r.key === 'ln' ? (r.prob * 100).toFixed(1) + '%' : '—'}</td>
        <td class="num">${r.ok ? money(r.netMxn) : '—'}</td>
        <td class="num">${r.ok ? money(r.spreadMxn) : '—'}</td>
        <td class="num">${r.ok ? money(r.cost) : '—'}</td></tr>`).join('') + '</tbody>';
    $('#qConfirm').hidden = false;
    $('#qConfirm').disabled = false;
    $('#qRequote').hidden = true;
    renderAuth();
  }

  /* ---------- FSM ---------- */
  const STATES = ['INIT', 'KYC_OK', 'SPEI_LOCKED', 'BTC_ROUTED', 'HKD_SETTLED'];
  function setFsm(idx, fail) {
    $('#fsm').innerHTML = STATES.map((s, i) => {
      let c = i < idx ? 'is-done' : i === idx ? (fail ? 'is-fail' : 'is-now') : '';
      if (i === idx && s === 'HKD_SETTLED') c = 'is-done';
      return `<li class="${c}"><span>${s}</span></li>`;
    }).join('');
  }
  function chipFor(state) {
    const map = { HKD_SETTLED: ['ok', 'Liquidada'], REVERTED: ['crit', 'Congelada'], REVIEW: ['warn', 'En revisión'] };
    const m = map[state] || ['accent', state];
    return `<span class="chip chip--${m[0]}">${m[1]}</span>`;
  }
  function log(msg, cls = '') {
    const li = document.createElement('li');
    if (cls) li.className = cls;
    li.innerHTML = `<time>${hms(new Date())}</time><span>${msg}</span>`;
    const ol = $('#trackLog');
    ol.appendChild(li);
    ol.scrollTop = ol.scrollHeight;
  }
  const step = (ms) => sleep(reduced ? Math.min(ms, 250) : ms);

  async function confirmQuote() {
    if (!Q || running || !lockValid()) return;
    running = true;
    stopLock();
    $('#lock').classList.add('is-off');
    const q = Q;
    const now = new Date();
    const op = makeOp(q, q.best.key, now, { invoice: $('#pfInvoice').value.trim(), state: 'INIT' });
    op.state = 'INIT';
    $('#qConfirm').disabled = true;
    $('#qConfirm').hidden = true;
    const tp = $('#trackPanel');
    tp.hidden = false;
    $('#trackTitle').textContent = `${q.sup.name}`;
    $('#trackId').textContent = `${op.id} · ${op.invoice} · ${money(op.amount, op.ccy)}`;
    $('#trackLog').innerHTML = '';
    $('#speiBox').hidden = true;
    $('#trackDone').hidden = true;
    const chip = $('#trackChip');
    const setChip = (s, cls) => { chip.className = 'chip chip--' + cls; chip.textContent = s; };
    setChip('INIT', 'accent');
    setFsm(0);
    tp.scrollIntoView({ behavior: reduced ? 'auto' : 'smooth', block: 'start' });
    log(`Orden creada. Tipo fijado ${N4.format(op.rate)} MXN/${op.ccy}, total ${money(op.total)}.`);

    await step(700);
    log(`KYB vigente · Textiles Altamira, S.A. de C.V.`);
    log(`AML bayesiano: P(ilícito | E) = ${op.aml < 0.001 ? sci(op.aml) : op.aml.toFixed(4)} con ${op.ev.length} evidencia(s).`);
    if (op.aml > THETA) {
      setFsm(1, true);
      op.state = 'REVERTED';
      setChip('REVERTED', 'crit');
      log('Operación congelada antes de recibir el SPEI. Reporte de operación inusual preparado para la UIF.', 'bad');
      OPS.unshift(op);
      afterOpsChange();
      running = false;
      $('#trackDone').hidden = false;
      $('#trackReceipt').textContent = 'Revisar en Cumplimiento';
      $('#trackReceipt').setAttribute('href', '#cumplimiento');
      bayesSel = op.id;
      return;
    }
    setFsm(1); setChip('KYC_OK', 'accent');

    await step(600);
    const box = $('#speiBox');
    box.hidden = false;
    box.innerHTML = `
      <p class="mono-label">Instrucción SPEI</p>
      <div class="spei__row"><span>CLABE</span><span class="mono">${op.clabe}</span><button type="button" class="copy" data-copy="${op.clabe}">Copiar</button></div>
      <div class="spei__row"><span>Beneficiario</span><span class="mono">PayMex Tech, S.A. de C.V.</span></div>
      <div class="spei__row"><span>Concepto</span><span class="mono">${op.id}</span></div>
      <div class="spei__row"><span>Monto exacto</span><span class="mono">${money(op.total)}</span></div>`;
    log('Esperando SPEI desde la cuenta del importador…');
    await step(2200);
    log(`SPEI recibido · clave de rastreo ${op.clave}.`, 'ok');
    T.mxn += op.total;
    setFsm(2); setChip('SPEI_LOCKED', 'accent');

    await step(800);
    if (op.route === 'ln' || op.route === 'hybrid') {
      const lnAmt = op.route === 'ln' ? op.btc : q.best.lnPart;
      log(`PayMex Asia genera preimagen R y entrega H = SHA256(R) = ${short(op.paymentHash, 12)}.`);
      await step(600);
      const path = (op.lnPath || ['PMX', 'PMA']).map((n) => LN_NAMES[n]).join(' → ');
      log(`HTLC fijado por ${fbtc(lnAmt)} · ruta ${path} · T_lock = +144 bloques.`);
      await step(900);
      log(`Preimagen revelada · SHA256(R) = H verificado · ${fbtc(lnAmt)} liquidados.`, 'ok');
      if (op.route === 'ln') { T.lnLocal -= lnAmt; T.lnRemote += lnAmt; }
      else { T.lnLocal -= lnAmt; T.lnRemote += lnAmt; }
    }
    if (op.route === 'chain' || op.route === 'hybrid') {
      const chainAmt = op.route === 'chain' ? op.btc : op.btc - q.best.lnPart;
      T.hot -= chainAmt;
      log(`Transacción Taproot difundida · ${fbtc(chainAmt)} · txid ${short(op.txid, 12)}.`);
      for (let c = 1; c <= op.z; c++) {
        await step(520);
        log(`Confirmación ${c}/${op.z} · bloque ${op.block - op.z + c} · P(reversión, q = 0.10) = ${sci(attackerSuccess(0.1, c))}.`);
      }
      log(`${op.z} confirmaciones alcanzadas. Autorizado el embarque.`, 'ok');
    }
    setFsm(3); setChip('BTC_ROUTED', 'accent');

    await step(900);
    log(`PayMex Asia permuta ${fbtc(op.btc)} por ${money(op.amount, op.ccy)}.`);
    await step(700);
    log(`FPS enviado a ${op.sup.bank} (${op.sup.code}) · FPS ID ${op.sup.fps} · ref ${op.fps}.`, 'ok');
    T.hkd -= op.hkd;
    op.state = 'HKD_SETTLED';
    setFsm(4); setChip('HKD_SETTLED', 'ok');
    OPS.unshift(op);
    afterOpsChange();
    running = false;
    rcSel = op.id;
    $('#trackReceipt').textContent = 'Ver comprobante';
    $('#trackReceipt').setAttribute('href', '#comprobantes');
    $('#trackDone').hidden = false;
    toast(`Liquidada. ${op.sup.name.split(' ').slice(0, 3).join(' ')} recibió ${money(op.amount, op.ccy)}.`);
  }

  function renderOps() {
    $('#opsTable').innerHTML =
      '<thead><tr><th scope="col">Folio</th><th scope="col">Fecha</th><th scope="col">Proveedor</th><th scope="col">Factura</th><th scope="col" class="num">Monto</th><th scope="col" class="num">Pagado</th><th scope="col">Ruta</th><th scope="col">Estado</th></tr></thead><tbody>' +
      OPS.map((o) => `<tr tabindex="0" data-op="${o.id}">
        <td class="mono">${o.id}</td><td>${fdate(o.date)}</td><td>${esc(o.sup.name)}</td><td class="mono">${esc(o.invoice)}</td>
        <td class="num">${money(o.amount, o.ccy)}</td><td class="num">${o.state === 'REVERTED' ? '—' : money(o.total)}</td>
        <td>${esc(o.routeName)}</td><td>${chipFor(o.state)}</td></tr>`).join('') + '</tbody>';
  }
  function openOp(id) {
    const o = OPS.find((x) => x.id === id); if (!o) return;
    if (o.state === 'HKD_SETTLED') { rcSel = id; go('comprobantes'); }
    else { bayesSel = id; go('cumplimiento'); }
  }

  function afterOpsChange() {
    renderOps();
    const frozen = OPS.filter((o) => o.state === 'REVERTED').length;
    const b = $('#frozenBadge');
    b.hidden = frozen === 0;
    b.textContent = frozen;
  }

  /* ================= TESORERÍA ================= */
  function renderPositions() {
    const eq = (b) => money(b * R.btcMxn);
    const items = [
      ['Bóveda caliente', fbtc(T.hot), eq(T.hot)],
      ['Bóveda fría · 2 de 3', fbtc(T.cold), eq(T.cold)],
      ['Lightning · canal directo', fbtc(T.lnLocal), `remoto ${N6.format(T.lnRemote)} BTC`],
      ['PayMex Asia · FPS', money(T.hkd, 'HKD'), money(T.hkd * mxnPerHkd())],
      ['IFPE · SPEI', money(T.mxn), 'MXN por dispersar'],
    ];
    $('#positions').innerHTML = items.map(([a, b, c]) => `<div class="pos"><span class="mono-label">${a}</span><span class="pos__v">${b}</span><span class="pos__s">${c}</span></div>`).join('');
  }

  const varState = () => ({ sigma: parseFloat($('#varSigma').value), h: parseInt($('#varH').value, 10) });
  function renderVar() {
    const { sigma, h } = varState();
    $('#varSigmaV').textContent = `${Math.round(sigma * 100)}%`;
    $('#varHV').textContent = `${h} min`;
    const E = (T.hot + T.lnLocal) * R.btcMxn;
    const ht = h / 525600;
    const drift = -0.5 * sigma * sigma * ht;
    const v = E * (1 - Math.exp(drift - 2.326 * sigma * Math.sqrt(ht)));
    $('#varOut').innerHTML = [
      ['Exposición (caliente + Lightning)', money(E)],
      ['VaR 99%, horizonte ' + h + ' min', money(v), 'em'],
      ['VaR relativo', ((v / E) * 100).toFixed(3) + '%'],
      ['Deriva de Itô (μ − σ²/2)·h, μ = 0', drift.toExponential(2)],
      ['Spread Lightning / on-chain z = 6', `${spreadBps(2).toFixed(1)} pb / ${spreadBps(65).toFixed(1)} pb`],
    ].map(([a, b, c]) => `<div><dt>${a}</dt><dd class="${c || ''}">${b}</dd></div>`).join('');
    $('#chartLabel').textContent = `σ ${Math.round(sigma * 100)}% · h ${h} min`;
  }

  function renderChart() {
    const svg = $('#priceSvg');
    const { sigma, h } = varState();
    const W = 640, H = 240, L = 70, Rr = 12, Tp = 14, B = 26;
    const k = Math.exp(-2.326 * sigma * Math.sqrt(h / 525600));
    const lows = HIST.map((p) => p * k);
    const min = Math.min(...lows), max = Math.max(...HIST);
    const padv = (max - min) * 0.08 || 1;
    const y0 = min - padv, y1 = max + padv;
    const X = (i) => L + (i / (HIST.length - 1)) * (W - L - Rr);
    const Y = (v) => Tp + (1 - (v - y0) / (y1 - y0)) * (H - Tp - B);
    const line = HIST.map((p, i) => `${i ? 'L' : 'M'}${X(i).toFixed(1)},${Y(p).toFixed(1)}`).join('');
    const area = `${line}L${X(HIST.length - 1).toFixed(1)},${H - B}L${L},${H - B}Z`;
    const vline = lows.map((p, i) => `${i ? 'L' : 'M'}${X(i).toFixed(1)},${Y(p).toFixed(1)}`).join('');
    let grid = '';
    for (let g = 0; g <= 4; g++) {
      const v = y0 + ((y1 - y0) * g) / 4;
      const y = Y(v);
      grid += `<line class="ch-grid" x1="${L}" x2="${W - Rr}" y1="${y.toFixed(1)}" y2="${y.toFixed(1)}"/><text class="ch-axis" x="${L - 8}" y="${(y + 3).toFixed(1)}" text-anchor="end">${N0.format(v / 1000)}k</text>`;
    }
    const xl = [[0, '−120 min'], [60, '−60 min'], [119, 'ahora']];
    grid += xl.map(([i, t]) => `<text class="ch-axis" x="${X(i).toFixed(1)}" y="${H - 8}" text-anchor="${i === 0 ? 'start' : i === 119 ? 'end' : 'middle'}">${t}</text>`).join('');
    const lx = X(HIST.length - 1), ly = Y(HIST[HIST.length - 1]), lvy = Y(lows[lows.length - 1]);
    svg.innerHTML = `${grid}<path class="ch-area" d="${area}"/><path class="ch-line" d="${line}"/><path class="ch-var" d="${vline}"/>
      <circle class="ch-dot" cx="${lx.toFixed(1)}" cy="${ly.toFixed(1)}" r="4"/>
      <text class="ch-label" x="${(lx - 8).toFixed(1)}" y="${(ly - 10).toFixed(1)}" text-anchor="end">$${N0.format(HIST[HIST.length - 1])}</text>
      <text class="ch-label ch-label--var" x="${(lx - 8).toFixed(1)}" y="${(Math.min(H - B - 4, lvy + 14)).toFixed(1)}" text-anchor="end">VaR 99%</text>`;
  }

  let refill = 0;
  function renderInventory() {
    const mu = parseFloat($('#invMu').value), sd = parseFloat($('#invSd').value), Lh = parseInt($('#invL').value, 10);
    const zA = parseFloat($('input[name="sl"]:checked').value);
    $('#invMuV').textContent = `${mu.toFixed(2)} BTC/h`;
    $('#invSdV').textContent = `${sd.toFixed(2)} BTC/h`;
    $('#invLV').textContent = `${Lh} h`;
    const s = mu * Lh + zA * sd * Math.sqrt(Lh);
    const S = s + mu * 24;
    const max = Math.max(S, T.hot) * 1.08;
    const low = T.hot < s;
    refill = low ? S - T.hot : 0;
    $('#invGauge').innerHTML = `
      <div class="gauge__bar"><span class="gauge__fill ${low ? 'is-low' : ''}" style="width:${((T.hot / max) * 100).toFixed(1)}%"></span><i class="gauge__mark" style="left:${((s / max) * 100).toFixed(1)}%"></i></div>
      <div class="gauge__legend"><span>saldo ${N2.format(T.hot)} BTC</span><span>s = ${N2.format(s)} BTC</span><span>S = ${N2.format(S)} BTC</span></div>
      <p>${low ? `<span class="chip chip--warn">Bajo punto de reorden</span> Reponer ${N2.format(refill)} BTC hasta S.` : `<span class="chip chip--ok">Cubierto</span> Margen de ${N2.format(T.hot - s)} BTC sobre s con z<sub>α</sub> = ${zA}.`}</p>`;
    $('#invRefill').hidden = !low;
    $('#invRefill').textContent = `Preparar reposición de ${N2.format(refill)} BTC desde bóveda fría`;
  }

  /* ---------- MPC: Shamir 2 de 3, firma con Lagrange ---------- */
  const QF = (1n << 127n) - 1n;
  const md = (a) => ((a % QF) + QF) % QF;
  function inv(a) {
    let t = 0n, nt = 1n, r = QF, nr = md(a);
    while (nr) { const qq = r / nr; [t, nt] = [nt, t - qq * nt]; [r, nr] = [nr, r - qq * nr]; }
    return md(t);
  }
  const randBig = () => md(BigInt('0x' + hex(randBytes(16))));
  const SECRET = randBig(), A1 = randBig();
  const SHARES = [
    { x: 1, name: 'CDMX', meta: 'HSM de operaciones, PayMex Tech' },
    { x: 2, name: 'Hong Kong', meta: 'HSM de PayMex Asia Limited' },
    { x: 3, name: 'Recuperación', meta: 'Fragmento frío fuera de línea' },
  ].map((s) => ({ ...s, y: md(SECRET + A1 * BigInt(s.x)) }));
  const SUB = ['₀', '₁', '₂', '₃'];
  let mpcAmount = 2;

  function lagrange(xs, i) {
    let num = 1n, den = 1n;
    const xi = BigInt(xs[i]);
    xs.forEach((xj, j) => { if (j !== i) { num *= -BigInt(xj); den *= xi - BigInt(xj); } });
    return { v: md(num * inv(md(den))), frac: fracStr(Number(num), Number(den)) };
  }
  function fracStr(n, d) {
    const g = (a, b) => (b ? g(b, a % b) : Math.abs(a));
    const k = g(n, d) || 1;
    let a = n / k, b = d / k;
    if (b < 0) { a = -a; b = -b; }
    const s = a < 0 ? '−' : '';
    return b === 1 ? `${s}${Math.abs(a)}` : `${s}${Math.abs(a)}/${b}`;
  }
  const bhex = (b) => b.toString(16).padStart(32, '0');

  function initMpc() {
    $('#shares').innerHTML = SHARES.map((s) => `
      <label class="share" for="sh${s.x}"><input type="checkbox" id="sh${s.x}" value="${s.x}">
        <span><span class="share__name">${s.name}</span><span class="share__meta">${s.meta} · f(x) = ${bhex(s.y).slice(0, 10)}…</span></span>
        <span class="share__x">x = ${s.x}</span></label>`).join('');
    $$('#shares input').forEach((c) => c.addEventListener('change', () => {
      const on = $$('#shares input:checked');
      if (on.length > 2) { c.checked = false; toast('El esquema es 2 de 3. Desmarca un fragmento para elegir otro.'); }
      renderMpc();
    }));
    $('#mpcSign').addEventListener('click', signMpc);
    $('#invRefill').addEventListener('click', () => {
      mpcAmount = Math.max(0.01, Math.round(refill * 100) / 100);
      renderMpc();
      $('#shares').scrollIntoView({ behavior: reduced ? 'auto' : 'smooth', block: 'center' });
      toast(`Retiro de ${N2.format(mpcAmount)} BTC preparado. Elige dos fragmentos para firmar.`);
    });
  }
  function chosen() { return $$('#shares input:checked').map((c) => parseInt(c.value, 10)); }
  function renderMpc() {
    const xs = chosen();
    const btn = $('#mpcSign');
    btn.textContent = `Firmar retiro · ${N2.format(mpcAmount)} BTC`;
    btn.disabled = xs.length !== 2;
    if (xs.length !== 2) { $('#mpcOut').innerHTML = xs.length ? 'Falta un fragmento.' : 'Sin fragmentos elegidos.'; return; }
    const ls = xs.map((_, i) => lagrange(xs, i));
    $('#mpcOut').innerHTML = xs.map((x, i) => `ℓ${SUB[x]}(0) = ∏ −x<sub>j</sub>/(x<sub>i</sub> − x<sub>j</sub>) = ${ls[i].frac}`).join('<br>');
  }
  async function signMpc() {
    const xs = chosen();
    if (xs.length !== 2) return;
    const btn = $('#mpcSign');
    btn.dataset.state = 'loading';
    btn.textContent = 'Firmando…';
    await step(500);
    const e = md(BigInt('0x' + hashOf('retiro:' + Date.now()).slice(0, 32)));
    const parts = xs.map((x, i) => {
      const sh = SHARES.find((s) => s.x === x);
      const ki = randBig();
      const l = lagrange(xs, i);
      return { x, ki, si: md(ki + e * l.v * sh.y), frac: l.frac };
    });
    const kSum = md(parts.reduce((a, p) => a + p.ki, 0n));
    const s = md(parts.reduce((a, p) => a + p.si, 0n));
    const ok = s === md(kSum + e * SECRET);
    $('#mpcOut').innerHTML =
      parts.map((p) => `s${SUB[p.x]} = k${SUB[p.x]} + e·ℓ${SUB[p.x]}·f(x${SUB[p.x]}) = ${bhex(p.si).slice(0, 16)}…`).join('<br>') +
      `<br>s = Σ sᵢ = ${bhex(s).slice(0, 16)}…<br>` +
      `<span class="${ok ? 'ok' : ''}">${ok ? 's ≡ k + e·d (mod q) · firma válida · d nunca se reconstruyó' : 'Firma inválida'}</span>`;
    delete btn.dataset.state;
    if (ok) {
      const amt = Math.min(mpcAmount, T.cold);
      T.cold -= amt; T.hot += amt;
      mpcAmount = 2;
      $$('#shares input').forEach((c) => { c.checked = false; });
      btn.disabled = true;
      btn.textContent = `Firmar retiro · ${N2.format(mpcAmount)} BTC`;
      renderPositions(); renderInventory(); renderVar();
      toast(`Retiro firmado. ${N2.format(amt)} BTC movidos a bóveda caliente.`);
    }
  }

  /* ---------- Bellman-Ford ---------- */
  function bfGraph() {
    const btcUsd = R.btcMxn / R.mxnPerUsd;
    return [
      ['MXN', 'BTC·MX', 1 / R.btcMxn, 0.001, 'Liquidez institucional MX'],
      ['MXN', 'USDT·MX', 1 / R.mxnPerUsd, 0.0008, 'Mesa OTC MX'],
      ['USDT·MX', 'BTC·MX', 1 / btcUsd, 0.0006, 'Libro USDT/BTC'],
      ['BTC·MX', 'BTC·HK', 1, 0.0001, 'Lightning entre entidades'],
      ['USDT·MX', 'USDT·HK', 1, 0.0004, 'Transferencia USDT'],
      ['BTC·HK', 'HKD', btcHkd(), 0.0012, 'Liquidez PayMex Asia'],
      ['BTC·HK', 'USDT·HK', btcUsd, 0.0006, 'Libro BTC/USDT HK'],
      ['USDT·HK', 'HKD', R.hkdPerUsd, 0.001, 'OTC HK'],
      ['HKD', 'CNH', R.cnhPerUsd / R.hkdPerUsd, 0.0015, 'Conversión offshore'],
    ].map(([u, v, r, c, n]) => ({ u, v, r, c, n, w: -Math.log(r * (1 - c)) }));
  }
  function bellmanFord(edges, src) {
    const nodes = [...new Set(edges.flatMap((e) => [e.u, e.v]))];
    const d = Object.fromEntries(nodes.map((n) => [n, Infinity]));
    const p = {};
    d[src] = 0;
    for (let i = 0; i < nodes.length - 1; i++) for (const e of edges) if (d[e.u] + e.w < d[e.v]) { d[e.v] = d[e.u] + e.w; p[e.v] = e; }
    const neg = edges.some((e) => d[e.u] + e.w < d[e.v] - 1e-12);
    return { d, p, neg };
  }
  function renderBf() {
    const edges = bfGraph();
    const { d, p, neg } = bellmanFord(edges, 'MXN');
    const path = [];
    const used = new Set();
    let cur = 'HKD';
    while (cur !== 'MXN' && p[cur]) { used.add(p[cur]); path.unshift(cur); cur = p[cur].u; }
    path.unshift('MXN');
    const eff = Math.exp(-d.HKD);
    const mid = 1 / mxnPerHkd();
    const costBp = (1 - eff / mid) * 1e4;
    $('#bfPath').innerHTML = path.map((n, i) => `${i ? '<span class="bf-arrow">→</span>' : ''}<span class="bf-node">${n}</span>`).join('') +
      `<p class="bf-sum">1 MXN rinde <b>${eff.toFixed(6)} HKD</b> · ${costBp.toFixed(1)} pb bajo el tipo medio · ${neg ? '<b>ciclo negativo: arbitraje disponible</b>' : 'sin ciclos negativos'}</p>`;
    $('#bfEdges').innerHTML = '<thead><tr><th scope="col">Arista</th><th scope="col">Contraparte</th><th scope="col" class="num">c</th><th scope="col" class="num">w(u,v)</th></tr></thead><tbody>' +
      edges.map((e) => `<tr class="${used.has(e) ? 'on' : ''}"><td class="mono">${e.u} → ${e.v}</td><td>${e.n}</td><td class="num">${(e.c * 100).toFixed(2)}%</td><td class="num">${e.w.toFixed(4)}</td></tr>`).join('') + '</tbody>';
  }

  function initTreasury() {
    ['#varSigma', '#varH'].forEach((s) => $(s).addEventListener('input', () => { renderVar(); renderChart(); }));
    ['#invMu', '#invSd', '#invL'].forEach((s) => $(s).addEventListener('input', renderInventory));
    $$('input[name="sl"]').forEach((r) => r.addEventListener('change', renderInventory));
    initMpc();
  }

  /* ================= CUMPLIMIENTO ================= */
  let bayesSel = null;
  let bayesEv = [];
  function initCompliance() {
    $('#bayesOp').addEventListener('change', (e) => { bayesSel = e.target.value; loadBayes(); });
    $('#umaVal').addEventListener('input', renderUif);
    $('#postFreeze').addEventListener('click', () => {
      const o = OPS.find((x) => x.id === bayesSel); if (!o) return;
      o.state = 'REVERTED'; o.ev = bayesEv.slice(); o.aml = posterior(bayesEv);
      afterOpsChange(); renderCompliance();
      toast(`${o.id} congelada. Reporte de operación inusual listo para la UIF.`);
    });
  }
  function loadBayes() {
    const o = OPS.find((x) => x.id === bayesSel) || OPS[0];
    bayesSel = o.id;
    bayesEv = o.ev.slice();
    $('#evidence').innerHTML = EVIDENCE.map((e) => `
      <li><label class="ev" for="ev-${e.id}"><input type="checkbox" id="ev-${e.id}" value="${e.id}" ${bayesEv.includes(e.id) ? 'checked' : ''}>
        <span class="ev__t">${e.t}</span><span class="ev__lr">LR ${(e.pi / e.pl).toFixed(1)}×</span></label></li>`).join('');
    $$('#evidence input').forEach((c) => c.addEventListener('change', () => {
      bayesEv = $$('#evidence input:checked').map((x) => x.value);
      renderPosterior();
    }));
    renderPosterior();
    renderTravel(o);
  }
  function renderPosterior() {
    const p = posterior(bayesEv);
    const v = verdict(p);
    const fill = $('#postFill');
    fill.style.width = `${Math.max(1, p * 100).toFixed(1)}%`;
    fill.className = v === 'crit' ? 'is-crit' : v === 'warn' ? 'is-warn' : '';
    $('#postVal').textContent = p < 0.001 ? sci(p) : p.toFixed(4);
    const o = OPS.find((x) => x.id === bayesSel);
    const txt = {
      ok: '<span class="chip chip--ok">Liberar</span> Riesgo bajo. La operación continúa sin intervención.',
      warn: '<span class="chip chip--warn">Revisión manual</span> Un oficial de cumplimiento valida antes de liberar.',
      crit: '<span class="chip chip--crit">Congelar</span> Supera θ = 0.75. Se retienen fondos y se prepara reporte de operación inusual.',
    }[v];
    $('#postVerdict').innerHTML = txt;
    $('#postFreeze').hidden = !(v === 'crit' && o && o.state !== 'REVERTED');
  }
  function renderKyb() {
    const items = [
      ['Acta constitutiva inscrita en RPC', 'ok', 'Vigente'],
      ['Constancia de Situación Fiscal', 'ok', 'Emitida hace 12 días'],
      ['Beneficiario controlador identificado', 'ok', 'Verificado'],
      ['Contrato de comisión mercantil', 'ok', 'Firmado'],
      ['Comprobante de domicilio fiscal', 'warn', 'Renovar en 21 días'],
      ['Alta de PayMex Tech en Portal PLD del SAT', 'ok', 'Activa'],
    ];
    $('#kyb').innerHTML = items.map(([t, c, s]) => `<li><span>${t}</span><span class="chip chip--${c}">${s}</span></li>`).join('');
  }
  function renderUif() {
    const uma = parseNum($('#umaVal').value);
    const thr = 210 * (uma > 0 ? uma : 0);
    const now = new Date();
    const month = OPS.filter((o) => o.date.getMonth() === now.getMonth() && o.date.getFullYear() === now.getFullYear() && o.state !== 'REVERTED');
    const over = month.filter((o) => o.total >= thr);
    const due = new Date(now.getFullYear(), now.getMonth() + 1, 17);
    const days = Math.ceil((due - now) / 86400000);
    $('#uifOut').innerHTML = [
      ['Umbral de aviso, 210 UMA', money(thr)],
      ['Operaciones del mes sobre umbral', String(over.length)],
      ['Monto a reportar', money(over.reduce((a, o) => a + o.total, 0))],
      ['Fecha límite del aviso', `${fdate(due)} · ${days} días`],
      ['Resguardo de expediente', '5 años desde la operación'],
    ].map(([a, b]) => `<div><dt>${a}</dt><dd>${b}</dd></div>`).join('');
  }
  function renderQueue() {
    $('#queueTable').innerHTML =
      '<thead><tr><th scope="col">Folio</th><th scope="col">Proveedor</th><th scope="col" class="num">Monto</th><th scope="col" class="num">P(ilícito | E)</th><th scope="col">Dictamen</th><th scope="col">Estado</th></tr></thead><tbody>' +
      OPS.map((o) => {
        const v = verdict(o.aml);
        const lab = { ok: 'Liberar', warn: 'Revisión manual', crit: 'Congelar' }[v];
        return `<tr tabindex="0" data-bayes="${o.id}"><td class="mono">${o.id}</td><td>${esc(o.sup.name)}</td><td class="num">${money(o.amount, o.ccy)}</td>
          <td class="num">${o.aml < 0.001 ? sci(o.aml) : o.aml.toFixed(4)}</td><td><span class="chip chip--${v}">${lab}</span></td><td>${chipFor(o.state)}</td></tr>`;
      }).join('') + '</tbody>';
  }
  function renderTravel(o) {
    const k = (s) => `<span class="k">"${s}"</span>`;
    const s = (v) => `<span class="s">"${esc(v)}"</span>`;
    const js = `<span class="p">{</span>
  ${k('ivms101')}: <span class="p">{</span>
    ${k('originator')}: <span class="p">{</span> ${k('name')}: ${s('Textiles Altamira, S.A. de C.V.')}, ${k('rfc')}: ${s('TAL150312AB7')}, ${k('country')}: ${s('MX')} <span class="p">}</span>,
    ${k('originatingVASP')}: ${s('PayMex Tech, S.A. de C.V.')},
    ${k('beneficiary')}: <span class="p">{</span> ${k('name')}: ${s(o.sup.name)}, ${k('bank')}: ${s(o.sup.bank + ' ' + o.sup.code)}, ${k('fpsId')}: ${s(o.sup.fps)} <span class="p">}</span>,
    ${k('beneficiaryVASP')}: ${s('PayMex Asia Limited')}
  <span class="p">}</span>,
  ${k('transfer')}: <span class="p">{</span> ${k('ref')}: ${s(o.id)}, ${k('asset')}: ${s('BTC')}, ${k('amount')}: ${s(o.btc.toFixed(8))}, ${k('rail')}: ${s(o.routeName)} <span class="p">}</span>,
  ${k('encryption')}: ${s('X25519 + ChaCha20-Poly1305')},
  ${k('digest')}: ${s(hashOf(o.id + ':travel'))}
<span class="p">}</span>`;
    $('#travelRule').innerHTML = js;
  }
  function renderCompliance() {
    const sel = $('#bayesOp');
    if (!bayesSel || !OPS.find((o) => o.id === bayesSel)) bayesSel = (OPS.find((o) => o.state !== 'HKD_SETTLED') || OPS[0]).id;
    sel.innerHTML = OPS.map((o) => `<option value="${o.id}" ${o.id === bayesSel ? 'selected' : ''}>${o.id} · ${esc(o.sup.name.split(' ').slice(0, 2).join(' '))}</option>`).join('');
    loadBayes(); renderKyb(); renderUif(); renderQueue();
  }

  /* ================= COMPROBANTES ================= */
  let rcSel = null;
  function initReceipts() {
    $('#rcOp').addEventListener('change', (e) => { rcSel = e.target.value; renderReceiptOnly(); });
    ['#inC', '#inV', '#in0', '#in1'].forEach((s) => $(s).addEventListener('input', renderInpc));
    $('#receipt').addEventListener('click', (e) => {
      const c = e.target.closest('[data-copy]'); if (c) copyText(c.dataset.copy, c);
      if (e.target.id === 'pedLink') {
        const o = OPS.find((x) => x.id === rcSel);
        const v = $('#pedInput').value.trim();
        if (!/^\d{2}\s?\d{2}\s?\d{4}\s?\d{7}$/.test(v)) { $('#pedErr').hidden = false; return; }
        o.pedimento = v.replace(/\s/g, '').replace(/^(\d{2})(\d{2})(\d{4})(\d{7})$/, '$1 $2 $3 $4');
        renderReceiptOnly();
        toast('Pedimento vinculado al comprobante.');
      }
    });
  }
  function receiptHash(o) {
    const canon = JSON.stringify({ id: o.id, invoice: o.invoice, pedimento: o.pedimento, amount: o.amount.toFixed(2), ccy: o.ccy, total: o.total.toFixed(2), fps: o.fps, tx: o.route === 'ln' ? o.paymentHash : o.txid });
    return hashOf(canon);
  }
  function renderReceiptOnly() {
    const o = OPS.find((x) => x.id === rcSel);
    if (!o) { $('#receipt').innerHTML = '<div class="empty"><p class="mono-label">Sin liquidaciones</p><p>Las operaciones liquidadas aparecen aquí con su comprobante.</p></div>'; return; }
    const h = receiptHash(o);
    const railRows = o.route === 'ln'
      ? `<dl><dt>Payment hash</dt><dd class="mono">${short(o.paymentHash, 16)}</dd></dl><dl><dt>Ruta Lightning</dt><dd>${(o.lnPath || ['PMX', 'PMA']).map((n) => LN_NAMES[n]).join(' → ')}</dd></dl>`
      : `<dl><dt>txid</dt><dd class="mono">${short(o.txid, 16)}</dd></dl><dl><dt>Bloque · confirmaciones</dt><dd class="mono">${o.block} · ${o.z}</dd></dl>`;
    $('#receipt').innerHTML = `
      <div class="receipt__head">
        <div><p class="receipt__h">${o.id}</p><p class="mono-label">${fdt(o.date)} · ${o.routeName}</p></div>
        ${chipFor(o.state)}
      </div>
      <div class="receipt__grid">
        <dl><dt>Ordenante</dt><dd>Textiles Altamira, S.A. de C.V.<br><span class="mono">RFC TAL150312AB7</span></dd></dl>
        <dl><dt>Beneficiario</dt><dd>${esc(o.sup.name)}<br><span class="mono">${esc(o.sup.bank)} ${o.sup.code} · FPS ${o.sup.fps}</span></dd></dl>
        <dl><dt>Commercial Invoice</dt><dd class="mono">${esc(o.invoice)}</dd></dl>
        <dl><dt>Pedimento</dt><dd class="mono">${o.pedimento ? esc(o.pedimento) : `
          <span class="field__control" style="min-height:36px"><input id="pedInput" placeholder="26 16 3165 6000000" aria-label="Número de pedimento"></span>
          <button type="button" class="copy" id="pedLink" style="margin-top:6px">Vincular</button>
          <span class="field__error" id="pedErr" hidden>Formato: año, aduana, patente y 7 dígitos.</span>`}</dd></dl>
        <dl><dt>Liquidado al proveedor</dt><dd class="mono">${money(o.amount, o.ccy)}</dd></dl>
        <dl><dt>Pagado por SPEI</dt><dd class="mono">${money(o.total)}</dd></dl>
        <dl><dt>Tipo todo incluido</dt><dd class="mono">${N4.format(o.rate)} MXN/${o.ccy}</dd></dl>
        <dl><dt>Clave de rastreo SPEI</dt><dd class="mono">${o.clave}</dd></dl>
        <dl><dt>Referencia FPS</dt><dd class="mono">${o.fps}</dd></dl>
        ${railRows}
      </div>
      <div class="cfdi">
        <p class="mono-label">CFDI de ingresos · PayMex Tech, S.A. de C.V.</p>
        <div class="kv">
          <div><dt>Servicio de intermediación tecnológica</dt><dd>${money(o.comm)}</dd></div>
          <div><dt>IVA trasladado 16%</dt><dd>${money(o.iva)}</dd></div>
          <div><dt>Total CFDI</dt><dd class="em">${money(o.comm + o.iva)}</dd></div>
          <div><dt>Principal por cuenta de terceros, RMF 2.7.1.12</dt><dd>${money(o.total - o.comm - o.iva)}</dd></div>
        </div>
      </div>
      <div class="receipt__hash"><span class="mono-label">SHA-256 del comprobante</span><code>${h}</code><button type="button" class="copy" data-copy="${h}">Copiar</button></div>`;
    renderProof(o);
    $('#inC').value = N2.format(o.mid * 0.9875);
    $('#inV').value = N2.format(o.mid);
    renderInpc();
  }
  function renderProof(o) {
    const title = $('#merkle').closest('.panel').querySelector('.panel__title');
    const note = $('#merkle').closest('.panel').querySelector('.panel__note');
    if (o.route === 'ln') {
      title.textContent = 'Verificación del pago Lightning';
      note.textContent = 'El proveedor revela R para cobrar. Cualquiera verifica que SHA256(R) coincide con el hash del HTLC.';
      const calc = hex(sha256(unhex(o.preimage)));
      $('#merkle').innerHTML = `<li><b>R</b><span>${o.preimage}</span></li><li><b>SHA256(R)</b><span>${calc}</span></li><li class="root"><b>H</b><span>${o.paymentHash}</span></li>`;
      $('#merkleOk').textContent = calc === o.paymentHash ? 'SHA256(R) = H · pago verificado' : 'La preimagen no coincide';
      return;
    }
    title.textContent = 'Verificación SPV';
    note.textContent = 'Ruta Merkle del pago dentro de su bloque, verificada aquí con Double-SHA256 en log₂ k pasos.';
    const k = 8;
    const idx = parseInt(o.txid.slice(0, 2), 16) % k;
    let level = Array.from({ length: k }, (_, i) => (i === idx ? unhex(o.txid) : dsha(utf8(`${o.block}:${i}`))));
    const proof = [];
    let pos = idx;
    while (level.length > 1) {
      const sib = pos ^ 1;
      proof.push({ h: level[sib], left: sib < pos });
      const next = [];
      for (let i = 0; i < level.length; i += 2) next.push(dsha(cat(level[i], level[i + 1])));
      level = next; pos >>= 1;
    }
    const root = level[0];
    let acc = unhex(o.txid);
    proof.forEach((p) => { acc = p.left ? dsha(cat(p.h, acc)) : dsha(cat(acc, p.h)); });
    $('#merkle').innerHTML = `<li><b>tx #${idx}</b><span>${o.txid}</span></li>` +
      proof.map((p, i) => `<li><b>nivel ${i + 1}</b><span>${p.left ? '◀ ' : '▶ '}${hex(p.h)}</span></li>`).join('') +
      `<li class="root"><b>raíz</b><span>${hex(root)}</span></li>`;
    $('#merkleOk').textContent = hex(acc) === hex(root) ? `Raíz recalculada coincide · ${proof.length} hashes para ${k} transacciones` : 'La ruta no coincide con la raíz';
  }
  function renderInpc() {
    const C = parseNum($('#inC').value), V = parseNum($('#inV').value), i0 = parseNum($('#in0').value), i1 = parseNum($('#in1').value);
    if (![C, V, i0, i1].every((x) => x > 0)) { $('#inpcOut').innerHTML = '<div><dt>Captura los cuatro valores</dt><dd>—</dd></div>'; return; }
    const F = i1 / i0;
    const Ca = C * Math.max(1, F);
    const G = V - Ca;
    $('#inpcOut').innerHTML = [
      ['Factor de actualización F', F.toFixed(4)],
      ['Costo actualizado C·max(1, F)', money(Ca)],
      [G >= 0 ? 'Ganancia gravable G' : 'Pérdida G', money(Math.abs(G)), 'em'],
    ].map(([a, b, c]) => `<div><dt>${a}</dt><dd class="${c || ''}">${b}</dd></div>`).join('');
  }
  function renderReceipts() {
    const settled = OPS.filter((o) => o.state === 'HKD_SETTLED');
    if (!rcSel || !settled.find((o) => o.id === rcSel)) rcSel = settled[0] ? settled[0].id : null;
    $('#rcOp').innerHTML = settled.map((o) => `<option value="${o.id}" ${o.id === rcSel ? 'selected' : ''}>${o.id} · ${money(o.amount, o.ccy)}</option>`).join('');
    renderReceiptOnly();
  }

  /* ================= Nakamoto ================= */
  function attackerSuccess(q, z) {
    const p = 1 - q;
    const lambda = z * (q / p);
    let sum = 1;
    for (let k = 0; k <= z; k++) {
      let poisson = Math.exp(-lambda);
      for (let i = 1; i <= k; i++) poisson *= lambda / i;
      sum -= poisson * (1 - Math.pow(q / p, z - k));
    }
    return Math.max(0, sum);
  }
  function renderNakamoto() {
    const q = parseFloat($('#nkQ').value), z = parseInt($('#nkZ').value, 10);
    $('#nkQv').textContent = `q = ${q.toFixed(2)}`;
    $('#nkZv').textContent = `z = ${z}`;
    const P = attackerSuccess(q, z);
    $('#nkP').textContent = sci(P);
    let need = null;
    for (let zz = 0; zz <= 400; zz++) if (attackerSuccess(q, zz) < 1e-8) { need = zz; break; }
    $('#nkNote').textContent = P < 1e-8
      ? `Bajo 10⁻⁸. Con q = ${q.toFixed(2)} bastan ${need} confirmaciones para ese nivel.`
      : need != null
        ? `Para bajar de 10⁻⁸ con q = ${q.toFixed(2)} se requieren ${need} confirmaciones. La plataforma exige z ≥ 6 sobre USD 50,000 y ajusta z al riesgo de red.`
        : 'Con esta fracción el atacante termina alcanzando a la red honesta.';
    const svg = $('#nkSvg');
    const W = 420, H = 240, L = 40, Rr = 12, Tp = 12, B = 26;
    const vals = Array.from({ length: 13 }, (_, i) => Math.max(-16, Math.log10(Math.max(attackerSuccess(q, i), 1e-16))));
    const ymin = Math.min(-8, Math.floor(Math.min(...vals) / 2) * 2);
    const X = (i) => L + (i / 12) * (W - L - Rr);
    const Y = (v) => Tp + (v / ymin) * (H - Tp - B);
    let g = '';
    for (let v = 0; v >= ymin; v -= ymin <= -12 ? 4 : 2) g += `<line class="nk-grid" x1="${L}" x2="${W - Rr}" y1="${Y(v).toFixed(1)}" y2="${Y(v).toFixed(1)}"/><text class="nk-axis" x="${L - 6}" y="${(Y(v) + 3).toFixed(1)}" text-anchor="end">${v}</text>`;
    for (let i = 0; i <= 12; i += 3) g += `<text class="nk-axis" x="${X(i).toFixed(1)}" y="${H - 8}" text-anchor="middle">${i}</text>`;
    const line = vals.map((v, i) => `${i ? 'L' : 'M'}${X(i).toFixed(1)},${Y(v).toFixed(1)}`).join('');
    const area = `${line}L${X(12).toFixed(1)},${Y(0).toFixed(1)}L${X(0).toFixed(1)},${Y(0).toFixed(1)}Z`;
    svg.innerHTML = `${g}<line class="nk-thr" x1="${L}" x2="${W - Rr}" y1="${Y(-8).toFixed(1)}" y2="${Y(-8).toFixed(1)}"/>
      <text class="nk-axis" x="${W - Rr}" y="${(Y(-8) - 5).toFixed(1)}" text-anchor="end">10⁻⁸</text>
      <path class="nk-area" d="${area}"/><path class="nk-line" d="${line}"/>
      <circle class="nk-dot" cx="${X(z).toFixed(1)}" cy="${Y(vals[z]).toFixed(1)}" r="5"/>`;
  }

  /* ================= paleta ⌘K ================= */
  const CMDS = [
    { t: 'Pagar a proveedor', k: 'Módulo', run: () => go('pagar') },
    { t: 'Tesorería', k: 'Módulo', run: () => go('tesoreria') },
    { t: 'Cumplimiento', k: 'Módulo', run: () => go('cumplimiento') },
    { t: 'Comprobantes', k: 'Módulo', run: () => go('comprobantes') },
    { t: 'Cotizar factura de HK$480,000', k: 'Acción', run: () => { go('pagar'); setTimeout(() => { $('#pfAmount').value = '480,000'; $('#ccyHkd').checked = true; $('#pfAffix').textContent = 'HK$'; doQuote(); }, 30); } },
    { t: 'Cotizar lote grande de HK$2,400,000', k: 'Acción', run: () => { go('pagar'); setTimeout(() => { $('#pfAmount').value = '2,400,000'; $('#ccyHkd').checked = true; $('#pfAffix').textContent = 'HK$'; doQuote(); }, 30); } },
    { t: 'Firmar retiro 2 de 3', k: 'Acción', run: () => { go('tesoreria'); setTimeout(() => $('#shares').scrollIntoView({ block: 'center' }), 30); } },
    { t: 'Revisar operación congelada', k: 'Acción', run: () => { const o = OPS.find((x) => x.state === 'REVERTED'); if (o) bayesSel = o.id; go('cumplimiento'); } },
    { t: 'Último comprobante', k: 'Acción', run: () => { rcSel = null; go('comprobantes'); } },
    { t: 'Inicio', k: 'Página', run: () => go('inicio') },
    { t: 'Ruta del pago', k: 'Página', run: () => { go('inicio'); setTimeout(() => $('#corredor').scrollIntoView(), 30); } },
    { t: 'Motor matemático', k: 'Página', run: () => { go('inicio'); setTimeout(() => $('#motor').scrollIntoView(), 30); } },
    { t: 'Marco legal', k: 'Página', run: () => { go('inicio'); setTimeout(() => $('#legal').scrollIntoView(), 30); } },
  ];
  let palIdx = 0, palItems = CMDS, palReturn = null;
  const norm = (s) => s.toLowerCase().normalize('NFD').replace(/[\u0300-\u036f]/g, '');
  function openPalette() {
    palReturn = document.activeElement;
    $('#palette').hidden = false;
    const i = $('#palInput');
    i.value = '';
    filterPalette();
    i.focus();
  }
  function closePalette() {
    $('#palette').hidden = true;
    if (palReturn && palReturn.focus) palReturn.focus();
  }
  function filterPalette() {
    const qy = norm($('#palInput').value.trim());
    palItems = CMDS.filter((c) => !qy || norm(c.t + ' ' + c.k).includes(qy));
    palIdx = 0;
    drawPalette();
  }
  function drawPalette() {
    const ul = $('#palList');
    if (!palItems.length) { ul.innerHTML = '<li class="none">Sin coincidencias. Escribe “tesorería” o “cotizar”.</li>'; $('#palInput').removeAttribute('aria-activedescendant'); return; }
    ul.innerHTML = palItems.map((c, i) => `<li role="option" id="pal-${i}" aria-selected="${i === palIdx}" data-i="${i}"><span>${c.t}</span><span>${c.k}</span></li>`).join('');
    $('#palInput').setAttribute('aria-activedescendant', 'pal-' + palIdx);
    const sel = $('#pal-' + palIdx); if (sel) sel.scrollIntoView({ block: 'nearest' });
  }
  function runPalette(i) { const c = palItems[i]; if (!c) return; closePalette(); c.run(); }
  function initPalette() {
    $$('[data-open-palette]').forEach((b) => b.addEventListener('click', openPalette));
    $('[data-close-palette]').addEventListener('click', closePalette);
    $('#palInput').addEventListener('input', filterPalette);
    $('#palInput').addEventListener('keydown', (e) => {
      if (e.key === 'ArrowDown') { e.preventDefault(); palIdx = Math.min(palItems.length - 1, palIdx + 1); drawPalette(); }
      else if (e.key === 'ArrowUp') { e.preventDefault(); palIdx = Math.max(0, palIdx - 1); drawPalette(); }
      else if (e.key === 'Enter') { e.preventDefault(); runPalette(palIdx); }
      else if (e.key === 'Escape') { e.preventDefault(); closePalette(); }
      else if (e.key === 'Tab') { e.preventDefault(); }
    });
    $('#palList').addEventListener('click', (e) => { const li = e.target.closest('[data-i]'); if (li) runPalette(parseInt(li.dataset.i, 10)); });
    document.addEventListener('keydown', (e) => {
      if ((e.metaKey || e.ctrlKey) && e.key.toLowerCase() === 'k') { e.preventDefault(); if ($('#palette').hidden) openPalette(); else closePalette(); }
      else if (e.key === 'Escape' && !$('#palette').hidden) closePalette();
    });
  }

  /* ================= render por vista ================= */
  const RENDER = {
    pagar: () => { renderOps(); if (!running && Q && !lockValid()) { /* vencida: se mantiene visible */ } },
    tesoreria: () => { renderPositions(); renderVar(); renderChart(); renderInventory(); renderMpc(); renderBf(); },
    cumplimiento: renderCompliance,
    comprobantes: renderReceipts,
  };

  /* ================= arranque ================= */
  function init() {
    seedOps();
    initPay(); initTreasury(); initCompliance(); initReceipts(); initPalette();
    afterOpsChange();
    renderTicker();
    renderNakamoto();
    ['#nkQ', '#nkZ'].forEach((s) => $(s).addEventListener('input', renderNakamoto));

    const hq = $('#hqHkd');
    hq.addEventListener('input', renderHeroQuote);
    hq.addEventListener('blur', () => { const v = parseNum(hq.value); if (v > 0) hq.value = N2.format(v).replace(/\.00$/, ''); });
    $('#heroQuote').addEventListener('submit', (e) => {
      e.preventDefault();
      const v = parseNum(hq.value);
      if (!(v > 0)) { hq.focus(); return; }
      $('#pfAmount').value = N2.format(v).replace(/\.00$/, '');
      $('#ccyHkd').checked = true; $('#pfAffix').textContent = 'HK$';
      $('#pfSupplier').value = 'hengli'; $('#pfSupplier').dispatchEvent(new Event('change'));
      go('pagar');
      setTimeout(doQuote, 30);
    });

    $$('[data-scroll]').forEach((b) => b.addEventListener('click', () => {
      const t = document.getElementById(b.dataset.scroll);
      if (t) t.scrollIntoView({ behavior: reduced ? 'auto' : 'smooth', block: 'start' });
    }));
    document.addEventListener('click', (e) => {
      const c = e.target.closest('#speiBox [data-copy]'); if (c) copyText(c.dataset.copy, c);
      const tr = e.target.closest('#opsTable tr[data-op]'); if (tr) openOp(tr.dataset.op);
      const qr = e.target.closest('#queueTable tr[data-bayes]'); if (qr) { bayesSel = qr.dataset.bayes; renderCompliance(); $('#evidence').scrollIntoView({ behavior: reduced ? 'auto' : 'smooth', block: 'center' }); }
    });
    document.addEventListener('keydown', (e) => {
      if (e.key !== 'Enter') return;
      const tr = e.target.closest && e.target.closest('tr[data-op], tr[data-bayes]');
      if (tr) tr.click();
    });

    // corredor: resalta tramos en secuencia
    if (!reduced) {
      const nodes = $$('.corridor__node');
      let ci = 0;
      setInterval(() => { nodes.forEach((n, i) => n.classList.toggle('is-hot', i === ci)); ci = (ci + 1) % nodes.length; }, 1400);
    }

    window.addEventListener('hashchange', route);
    route();
    setInterval(tick, 2000);
  }

  if (document.readyState === 'loading') document.addEventListener('DOMContentLoaded', init); else init();
})();
