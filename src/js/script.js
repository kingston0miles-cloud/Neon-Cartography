'use strict';
/* =====================================================================
ДВИЖОК: утилиты, геометрия, шум, генерация мира
===================================================================== */
const TAU = Math.PI * 2;
const clamp = (v, a, b) => v < a ? a : (v > b ? b : v);
const lerp = (a, b, t) => a + (b - a) * t;
const smoothstep = (a, b, x) => {
    const t = clamp((x - a) / (b - a), 0, 1);
    return t * t * (3 - 2 * t);
};

function mulberry32(a) {
    return function () {
        a |= 0;
        a = a + 0x6D2B79F5 | 0;
        let t = Math.imul(a ^ a >>> 15, 1 | a);
        t = t + Math.imul(t ^ t >>> 7, 61 | t) ^ t;
        return ((t ^ t >>> 14) >>> 0) / 4294967296;
    };
}

const rrange = (r, a, b) => a + (b - a) * r();
const rint = (r, a, b) => Math.floor(a + (b - a + 1) * r());
const pick = (r, arr) => arr[Math.floor(r() * arr.length)];
const clone = o => JSON.parse(JSON.stringify(o));

function shuffle(r, a) {
    a = a.slice();
    for (let i = a.length - 1; i > 0; i--) {
        const j = Math.floor(r() * (i + 1));
        [a[i], a[j]] = [a[j], a[i]];
    }
    return a;
}

function hex2rgb(h) {
    h = h.replace('#', '');
    if (h.length === 3) h = h.split('').map(c => c + c).join('');
    const n = parseInt(h, 16);
    return [(n >> 16) & 255, (n >> 8) & 255, n & 255];
}

function rgb2hex(r, g, b) {
    return '#' + [r, g, b].map(v => clamp(Math.round(v), 0, 255).toString(16).padStart(2, '0')).join('');
}

function luminance(h) {
    const [r, g, b] = hex2rgb(h);
    return (0.2126 * r + 0.7152 * g + 0.0722 * b) / 255;
}

function mixHex(a, b, t) {
    const A = hex2rgb(a), B = hex2rgb(b);
    return rgb2hex(lerp(A[0], B[0], t), lerp(A[1], B[1], t), lerp(A[2], B[2], t));
}

function makeNoise(seed) {
    const r = mulberry32(seed >>> 0), g = new Float32Array(65536);
    for (let i = 0; i < 65536; i++) g[i] = r();

    function v2(x, y) {
        const xi = Math.floor(x), yi = Math.floor(y);
        let fx = x - xi, fy = y - yi;
        fx = fx * fx * (3 - 2 * fx);
        fy = fy * fy * (3 - 2 * fy);
        const x0 = xi & 255, y0 = yi & 255, x1 = (xi + 1) & 255, y1 = (yi + 1) & 255;
        const a = g[y0 * 256 + x0], b = g[y0 * 256 + x1], c = g[y1 * 256 + x0], d = g[y1 * 256 + x1];
        return a + (b - a) * fx + (c - a) * fy + (a - b - c + d) * fx * fy;
    }

    function fbm(x, y, o) {
        o = o || 3;
        let s = 0, a = 0.5, f = 1, n = 0;
        for (let i = 0; i < o; i++) {
            s += a * v2(x * f + i * 17.3, y * f - i * 9.1);
            n += a;
            a *= 0.5;
            f *= 2.03;
        }
        return s / n;
    }

    return {v2, fbm};
}

/* ---------- геометрия ---------- */
function pip(x, y, poly) {
    let inside = false;
    for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
        const xi = poly[i][0], yi = poly[i][1], xj = poly[j][0], yj = poly[j][1];
        if (((yi > y) !== (yj > y)) && (x < (xj - xi) * (y - yi) / (yj - yi) + xi)) inside = !inside;
    }
    return inside;
}

function bboxOf(poly) {
    let a = 1e9, b = 1e9, c = -1e9, d = -1e9;
    for (const p of poly) {
        if (p[0] < a) a = p[0];
        if (p[0] > c) c = p[0];
        if (p[1] < b) b = p[1];
        if (p[1] > d) d = p[1];
    }
    return [a, b, c, d];
}

function polyArea(p) {
    let s = 0;
    for (let i = 0, j = p.length - 1; i < p.length; j = i++) s += p[j][0] * p[i][1] - p[i][0] * p[j][1];
    return s / 2;
}

function ensureCCW(p) {
    if (polyArea(p) < 0) p.reverse();
    return p;
}

function polyCentroid(p) {
    let a = 0, cx = 0, cy = 0;
    for (let i = 0, j = p.length - 1; i < p.length; j = i++) {
        const f = p[j][0] * p[i][1] - p[i][0] * p[j][1];
        a += f;
        cx += (p[j][0] + p[i][0]) * f;
        cy += (p[j][1] + p[i][1]) * f;
    }
    if (Math.abs(a) < 1e-6) {
        let sx = 0, sy = 0;
        for (const q of p) {
            sx += q[0];
            sy += q[1];
        }
        return [sx / p.length, sy / p.length];
    }
    a *= 3;
    return [cx / a, cy / a];
}

function distSeg(px, py, ax, ay, bx, by) {
    const dx = bx - ax, dy = by - ay;
    const L = dx * dx + dy * dy;
    let t = L ? ((px - ax) * dx + (py - ay) * dy) / L : 0;
    t = t < 0 ? 0 : t > 1 ? 1 : t;
    const x = ax + t * dx - px, y = ay + t * dy - py;
    return Math.sqrt(x * x + y * y);
}

function distPoly(x, y, poly) {
    let m = 1e18;
    for (let i = 0, j = poly.length - 1; i < poly.length; j = i++) {
        const d = distSeg(x, y, poly[j][0], poly[j][1], poly[i][0], poly[i][1]);
        if (d < m) m = d;
    }
    return m;
}

function clipHalf(poly, nx, ny, c) {
    const out = [], n = poly.length;
    for (let i = 0; i < n; i++) {
        const a = poly[i], b = poly[(i + 1) % n];
        const da = nx * a[0] + ny * a[1] - c, db = nx * b[0] + ny * b[1] - c;
        if (da <= 0) out.push(a);
        if ((da < 0 && db > 0) || (da > 0 && db < 0)) {
            const t = da / (da - db);
            out.push([a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t]);
        }
    }
    return out;
}

function catmull(pts, step) {
    if (pts.length < 2) return pts.map(p => p.slice());
    const out = [], P = i => pts[clamp(i, 0, pts.length - 1)];
    for (let i = 0; i < pts.length - 1; i++) {
        const p0 = P(i - 1), p1 = P(i), p2 = P(i + 1), p3 = P(i + 2);
        const L = Math.hypot(p2[0] - p1[0], p2[1] - p1[1]);
        const n = Math.max(1, Math.ceil(L / step));
        for (let k = 0; k < n; k++) {
            const t = k / n, t2 = t * t, t3 = t2 * t;
            out.push([
                0.5 * ((2 * p1[0]) + (-p0[0] + p2[0]) * t + (2 * p0[0] - 5 * p1[0] + 4 * p2[0] - p3[0]) * t2 + (-p0[0] + 3 * p1[0] - 3 * p2[0] + p3[0]) * t3),
                0.5 * ((2 * p1[1]) + (-p0[1] + p2[1]) * t + (2 * p0[1] - 5 * p1[1] + 4 * p2[1] - p3[1]) * t2 + (-p0[1] + 3 * p1[1] - 3 * p2[1] + p3[1]) * t3)]);
        }
    }
    out.push(pts[pts.length - 1].slice());
    return out;
}

function rdp(pts, eps) {
    const n = pts.length / 2;
    if (n < 3) return pts.slice();
    const keep = new Uint8Array(n);
    keep[0] = keep[n - 1] = 1;
    const stack = [[0, n - 1]];
    while (stack.length) {
        const [a, b] = stack.pop();
        let maxd = 0, idx = -1;
        const ax = pts[a * 2], ay = pts[a * 2 + 1], bx = pts[b * 2], by = pts[b * 2 + 1];
        const dx = bx - ax, dy = by - ay, L2 = dx * dx + dy * dy;
        for (let i = a + 1; i < b; i++) {
            const px = pts[i * 2], py = pts[i * 2 + 1];
            let d;
            if (L2 === 0) d = Math.hypot(px - ax, py - ay);
            else {
                let t = ((px - ax) * dx + (py - ay) * dy) / L2;
                t = t < 0 ? 0 : t > 1 ? 1 : t;
                d = Math.hypot(px - (ax + t * dx), py - (ay + t * dy));
            }
            if (d > maxd) {
                maxd = d;
                idx = i;
            }
        }
        if (maxd > eps && idx > 0) {
            keep[idx] = 1;
            stack.push([a, idx], [idx, b]);
        }
    }
    const out = [];
    for (let i = 0; i < n; i++) if (keep[i]) out.push(pts[i * 2], pts[i * 2 + 1]);
    return out;
}

function flatLen(f) {
    let L = 0;
    for (let i = 2; i < f.length; i += 2) L += Math.hypot(f[i] - f[i - 2], f[i + 1] - f[i - 1]);
    return L;
}

function subPath(f, s0, s1) {
    const out = [];
    let acc = 0;
    for (let i = 0; i < f.length - 2; i += 2) {
        const ax = f[i], ay = f[i + 1], bx = f[i + 2], by = f[i + 3];
        const L = Math.hypot(bx - ax, by - ay);
        if (L === 0) continue;
        const a0 = acc, a1 = acc + L;
        if (a1 >= s0 && a0 <= s1) {
            if (!out.length) {
                const t = clamp((s0 - a0) / L, 0, 1);
                out.push([ax + (bx - ax) * t, ay + (by - ay) * t]);
            }
            if (a1 <= s1) out.push([bx, by]); else {
                const t = (s1 - a0) / L;
                out.push([ax + (bx - ax) * t, ay + (by - ay) * t]);
                break;
            }
        }
        acc = a1;
    }
    return out;
}

/* ---------- пространственная сетка точек ---------- */
class PGrid {
    constructor(cell) {
        this.c = cell;
        this.m = new Map();
    }

    add(x, y) {
        const k = (Math.floor(x / this.c) + 512) * 2048 + (Math.floor(y / this.c) + 512);
        let a = this.m.get(k);
        if (!a) {
            a = [];
            this.m.set(k, a);
        }
        a.push(x, y);
    }

    nearest(x, y, r) {
        const c = this.c, ix = Math.floor(x / c), iy = Math.floor(y / c), rng = Math.ceil(r / c);
        let bd = r * r, bx = 0, by = 0, f = false;
        for (let dx = -rng; dx <= rng; dx++) for (let dy = -rng; dy <= rng; dy++) {
            const a = this.m.get((ix + dx + 512) * 2048 + (iy + dy + 512));
            if (!a) continue;
            for (let k = 0; k < a.length; k += 2) {
                const ex = a[k] - x, ey = a[k + 1] - y, d2 = ex * ex + ey * ey;
                if (d2 < bd) {
                    bd = d2;
                    bx = a[k];
                    by = a[k + 1];
                    f = true;
                }
            }
        }
        return f ? [bx, by] : null;
    }
}

/* ---------- потоковые линии (улицы) ---------- */
function traceStreams(o) {
    const grid = o.grid || new PGrid(o.dtest), rng = o.rng, step = o.step, sep = o.sep, dtest = o.dtest;
    const inside = o.inside, ang = o.angle, fam = o.fam;
    const lines = [], queue = [];
    let qi = 0;
    const maxSteps = o.maxSteps || Math.ceil(2200 / step), maxLines = o.maxLines || 5000;
    const jit0 = o.jit0 || 0.95, jit1 = o.jit1 || 1.6;

    function trace(x0, y0, sign, lim) {
        const pts = [];
        let x = x0, y = y0;
        const L = Math.min(maxSteps, lim || maxSteps);
        for (let i = 0; i < L; i++) {
            let a = ang(x, y, fam);
            const mx = x + Math.cos(a) * sign * step * 0.5, my = y + Math.sin(a) * sign * step * 0.5;
            a = ang(mx, my, fam);
            const nx = x + Math.cos(a) * sign * step, ny = y + Math.sin(a) * sign * step;
            if (!inside(nx, ny)) {
                let lo = 0, hi = 1;
                for (let k = 0; k < 8; k++) {
                    const m = (lo + hi) / 2;
                    if (inside(x + (nx - x) * m, y + (ny - y) * m)) lo = m; else hi = m;
                }
                if (lo > 0.02) pts.push(x + (nx - x) * lo, y + (ny - y) * lo);
                break;
            }
            const nr = grid.nearest(nx, ny, dtest);
            if (nr) {
                pts.push(nr[0], nr[1]);
                break;
            }
            pts.push(nx, ny);
            x = nx;
            y = ny;
            if (o.closeLoops && i > 12 && (x - x0) * (x - x0) + (y - y0) * (y - y0) < step * step * 1.7) {
                pts.push(x0, y0);
                break;
            }
        }
        return pts;
    }

    function build(x0, y0, lim) {
        const f = trace(x0, y0, 1, lim), b = trace(x0, y0, -1, lim), pts = [];
        for (let i = b.length - 2; i >= 0; i -= 2) pts.push(b[i], b[i + 1]);
        pts.push(x0, y0);
        for (let i = 0; i < f.length; i++) pts.push(f[i]);
        return pts;
    }

    function addLine(pts) {
        for (let i = 0; i < pts.length; i += 2) grid.add(pts[i], pts[i + 1]);
        lines.push(pts);
        if (o.noSeeds) return;
        let acc = 0, px = pts[0], py = pts[1];
        for (let i = 2; i < pts.length; i += 2) {
            const x = pts[i], y = pts[i + 1];
            acc += Math.hypot(x - px, y - py);
            if (acc >= sep * 0.8) {
                acc = 0;
                const tx = x - px, ty = y - py, L = Math.hypot(tx, ty) || 1, nx = -ty / L, ny = tx / L;
                const d1 = sep * (jit0 + (jit1 - jit0) * rng()), d2 = sep * (jit0 + (jit1 - jit0) * rng());
                queue.push(x + nx * d1, y + ny * d1, x - nx * d2, y - ny * d2);
            }
            px = x;
            py = y;
        }
    }

    function tryseed(x, y) {
        if (!inside(x, y) || grid.nearest(x, y, dtest)) return;
        const pts = build(x, y, o.lenFn ? Math.ceil(o.lenFn() / step) : 0);
        if (pts.length >= (o.minPts || 6)) addLine(pts);
    }

    function drain() {
        while (qi < queue.length && lines.length < maxLines) {
            const x = queue[qi], y = queue[qi + 1];
            qi += 2;
            tryseed(x, y);
        }
    }

    const sd = o.seeds || [];
    for (let i = 0; i < sd.length; i += 2) {
        tryseed(sd[i], sd[i + 1]);
        drain();
    }
    const bb = o.bbox;
    for (let t = 0; t < (o.randomTries === undefined ? 260 : o.randomTries) && lines.length < maxLines; t++) {
        tryseed(bb[0] + rng() * (bb[2] - bb[0]), bb[1] + rng() * (bb[3] - bb[1]));
        drain();
    }
    return lines;
}

/* ---------- поля и контуры ---------- */
function sampleField(F, gw, gh, cell, x, y) {
    const fx = x / cell - 0.5, fy = y / cell - 0.5, i = Math.floor(fx), j = Math.floor(fy), tx = fx - i, ty = fy - j;
    const i0 = clamp(i, 0, gw - 1), i1 = clamp(i + 1, 0, gw - 1), j0 = clamp(j, 0, gh - 1),
        j1 = clamp(j + 1, 0, gh - 1);
    const a = F[j0 * gw + i0], b = F[j0 * gw + i1], c = F[j1 * gw + i0], d = F[j1 * gw + i1];
    return a + (b - a) * tx + (c - a) * ty + (a - b - c + d) * tx * ty;
}

function boxBlur(src, gw, gh, r, iter) {
    let a = Float32Array.from(src);
    const b = new Float32Array(src.length);
    for (let it = 0; it < iter; it++) {
        for (let j = 0; j < gh; j++) {
            let sum = 0;
            const row = j * gw;
            for (let i = -r; i <= r; i++) sum += a[row + clamp(i, 0, gw - 1)];
            for (let i = 0; i < gw; i++) {
                b[row + i] = sum / (2 * r + 1);
                sum += a[row + clamp(i + r + 1, 0, gw - 1)] - a[row + clamp(i - r, 0, gw - 1)];
            }
        }
        for (let i = 0; i < gw; i++) {
            let sum = 0;
            for (let j = -r; j <= r; j++) sum += b[clamp(j, 0, gh - 1) * gw + i];
            for (let j = 0; j < gh; j++) {
                a[j * gw + i] = sum / (2 * r + 1);
                sum += b[clamp(j + r + 1, 0, gh - 1) * gw + i] - b[clamp(j - r, 0, gh - 1) * gw + i];
            }
        }
    }
    return a;
}

function marching(F, gw, gh, cell, level) {
    const out = [], g = (i, j) => F[clamp(j, 0, gh - 1) * gw + clamp(i, 0, gw - 1)];
    const seg = (p, q) => out.push(p[0], p[1], q[0], q[1]);
    for (let j = -1; j < gh; j++) for (let i = -1; i < gw; i++) {
        const a = g(i, j), b = g(i + 1, j), c = g(i + 1, j + 1), d = g(i, j + 1);
        const idx = (a > level ? 1 : 0) | (b > level ? 2 : 0) | (c > level ? 4 : 0) | (d > level ? 8 : 0);
        if (idx === 0 || idx === 15) continue;
        const x0 = (i + 0.5) * cell, y0 = (j + 0.5) * cell, x1 = x0 + cell, y1 = y0 + cell;
        const T = (va, vb) => (level - va) / (vb - va);
        const top = [x0 + cell * T(a, b), y0], right = [x1, y0 + cell * T(b, c)], bottom = [x0 + cell * T(d, c), y1],
            left = [x0, y0 + cell * T(a, d)];
        switch (idx) {
            case 1:
            case 14:
                seg(left, top);
                break;
            case 2:
            case 13:
                seg(top, right);
                break;
            case 3:
            case 12:
                seg(left, right);
                break;
            case 4:
            case 11:
                seg(right, bottom);
                break;
            case 5:
                seg(left, top);
                seg(right, bottom);
                break;
            case 6:
            case 9:
                seg(top, bottom);
                break;
            case 7:
            case 8:
                seg(left, bottom);
                break;
            case 10:
                seg(top, right);
                seg(left, bottom);
                break;
        }
    }
    return out;
}

/* =====================================================================
    КОНСТАНТЫ: палитры, типы районов, пресеты, имена
    ===================================================================== */
const PALETTES = {
    neon: {
        name: 'Неон-нуар',
        bg: '#04060c',
        water: '#0b6b7a',
        coast: '#22e6d6',
        bathy: '#12909a',
        river: '#2ad8e8',
        mountain: '#7a8cff',
        farm: '#1d7a72',
        farmDot: '#ffb84d',
        highway: '#ffe3f1',
        avenue: '#ffb3d9',
        street: '#ff8fc0',
        rail: '#ffffff',
        label: '#f6ecff',
        labelStreet: '#dff6ff',
        icon: '#3ee6d6',
        ship: '#ff5b8d',
        types: {
            center: '#62f3e2',
            commerce: '#ff4d84',
            residential: '#b56bff',
            industrial: '#ff8d2b',
            harbor: '#c8f03a',
            slums: '#ff6a3d',
            park: '#37e6a4',
            suburb: '#9a86ff',
            tech: '#3ec8ff'
        }
    },
    synth: {
        name: 'Синтвейв',
        bg: '#0b0220',
        water: '#2a1470',
        coast: '#00f0ff',
        bathy: '#5a34c8',
        river: '#00e5ff',
        mountain: '#ff5fd2',
        farm: '#5a2d9a',
        farmDot: '#f9f871',
        highway: '#fff0ff',
        avenue: '#ff9ff3',
        street: '#c98bff',
        rail: '#00f0ff',
        label: '#ffe8ff',
        labelStreet: '#d7f8ff',
        icon: '#00f0ff',
        ship: '#ff2a9d',
        types: {
            center: '#00f0ff',
            commerce: '#ff2a9d',
            residential: '#9d4dff',
            industrial: '#ff8a00',
            harbor: '#f9f871',
            slums: '#ff2a6d',
            park: '#05ffa1',
            suburb: '#7b61ff',
            tech: '#01cdfe'
        }
    },
    vice: {
        name: 'Майами-вайс',
        bg: '#0a0818',
        water: '#0e5a78',
        coast: '#01cdfe',
        bathy: '#0b8ab0',
        river: '#01cdfe',
        mountain: '#b967ff',
        farm: '#2a7f8a',
        farmDot: '#fffb96',
        highway: '#fff5fb',
        avenue: '#ff9ce0',
        street: '#ffb0e8',
        rail: '#fffb96',
        label: '#fff5fb',
        labelStreet: '#d5f7ff',
        icon: '#05ffa1',
        ship: '#ff71ce',
        types: {
            center: '#ff71ce',
            commerce: '#01cdfe',
            residential: '#b967ff',
            industrial: '#ffb86c',
            harbor: '#05ffa1',
            slums: '#ff6b81',
            park: '#7dffb3',
            suburb: '#8f9bff',
            tech: '#fffb96'
        }
    },
    amber: {
        name: 'Янтарный терминал',
        bg: '#0a0500',
        water: '#7a3a00',
        coast: '#ffb000',
        bathy: '#8a4c00',
        river: '#ffc040',
        mountain: '#c47400',
        farm: '#6b3c00',
        farmDot: '#ffd35c',
        highway: '#fff1c2',
        avenue: '#ffd166',
        street: '#ffb000',
        rail: '#ffe9a8',
        label: '#ffe9b0',
        labelStreet: '#ffd98a',
        icon: '#ffb000',
        ship: '#ff8c00',
        types: {
            center: '#ffd166',
            commerce: '#ffb000',
            residential: '#e89a00',
            industrial: '#ff7a00',
            harbor: '#ffe07a',
            slums: '#ff6a1a',
            park: '#c8a200',
            suburb: '#d68400',
            tech: '#ffc94d'
        }
    },
    phosphor: {
        name: 'Зелёный фосфор',
        bg: '#010803',
        water: '#0a5a2a',
        coast: '#39ff88',
        bathy: '#12a84e',
        river: '#4dff9a',
        mountain: '#2ec46a',
        farm: '#0f5a2a',
        farmDot: '#c6ff6b',
        highway: '#e2ffe9',
        avenue: '#9dffb8',
        street: '#5dff95',
        rail: '#d4ffe0',
        label: '#d8ffe4',
        labelStreet: '#b5ffcc',
        icon: '#39ff88',
        ship: '#b5ff5a',
        types: {
            center: '#7dffb0',
            commerce: '#39ff88',
            residential: '#22d96b',
            industrial: '#a5ff3a',
            harbor: '#d4ff5a',
            slums: '#5aff5a',
            park: '#1fbf6a',
            suburb: '#2fe88a',
            tech: '#4dffc4'
        }
    },
    blade: {
        name: 'Дождь и неон',
        bg: '#05090f',
        water: '#0a4a66',
        coast: '#3fd0ff',
        bathy: '#0f78a0',
        river: '#3fd0ff',
        mountain: '#5f7fb0',
        farm: '#1f5a63',
        farmDot: '#ffb14d',
        highway: '#fff2e0',
        avenue: '#ffc48a',
        street: '#ff9f5a',
        rail: '#e0f4ff',
        label: '#ffeedd',
        labelStreet: '#d8f0ff',
        icon: '#3fd0ff',
        ship: '#ff6a3d',
        types: {
            center: '#3fd0ff',
            commerce: '#ff7a3d',
            residential: '#ff4d6a',
            industrial: '#ffa53d',
            harbor: '#8ff0e0',
            slums: '#ff5a2a',
            park: '#3fe0b0',
            suburb: '#6a8cff',
            tech: '#8fd8ff'
        }
    },
    blueprint: {
        name: 'Синька',
        bg: '#06214f',
        water: '#0b3f8a',
        coast: '#bfe6ff',
        bathy: '#4f8fd8',
        river: '#9fd6ff',
        mountain: '#7fb2ff',
        farm: '#2f68b8',
        farmDot: '#ffffff',
        highway: '#ffffff',
        avenue: '#e6f4ff',
        street: '#cfe8ff',
        rail: '#ffffff',
        label: '#ffffff',
        labelStreet: '#e6f4ff',
        icon: '#ffffff',
        ship: '#bfe6ff',
        types: {
            center: '#ffffff',
            commerce: '#bfe6ff',
            residential: '#8ec8ff',
            industrial: '#d6ecff',
            harbor: '#a6dcff',
            slums: '#7fb8f5',
            park: '#9fe8ff',
            suburb: '#6fa8ee',
            tech: '#c8f0ff'
        }
    }
};
const COLOR_LABELS = {
    bg: 'Фон',
    water: 'Море и озёра',
    coast: 'Береговая линия',
    bathy: 'Глубины',
    river: 'Реки',
    mountain: 'Горы',
    farm: 'Поля',
    farmDot: 'Фермы',
    highway: 'Магистрали',
    avenue: 'Проспекты',
    street: 'Нарисованные улицы',
    rail: 'Железная дорога',
    label: 'Названия районов',
    labelStreet: 'Названия улиц',
    icon: 'Якоря и значки',
    ship: 'Корабли'
};
const TYPES = {
    center: {
        n: 'Центр',
        sepK: .85,
        style: 'organic',
        curv: .55,
        alleys: .6,
        parks: .25,
        ragged: 0,
        popDensity: 0.60,
        bldDensity: 0.85,
        bldForm: 'block'
    },
    commerce: {
        n: 'Деловой квартал',
        sepK: .9,
        style: 'grid',
        curv: .12,
        alleys: .5,
        parks: .08,
        ragged: 0,
        popDensity: 0.30,
        bldDensity: 0.75,
        bldForm: 'tower'
    },
    residential: {
        n: 'Жилой район',
        sepK: 1.0,
        style: 'grid',
        curv: .2,
        alleys: .55,
        parks: .15,
        ragged: 0,
        popDensity: 0.45,
        bldDensity: 0.65,
        bldForm: 'block'
    },
    industrial: {
        n: 'Промзона',
        sepK: 1.25,
        style: 'grid',
        curv: .08,
        alleys: .2,
        parks: .3,
        ragged: 0,
        popDensity: 0.075,
        bldDensity: 0.45,
        bldForm: 'hall'
    },
    harbor: {
        n: 'Порт',
        sepK: 1.3,
        style: 'grid',
        curv: .1,
        alleys: .15,
        parks: 0,
        ragged: 0,
        popDensity: 0.10,
        bldDensity: 0.50,
        bldForm: 'hall'
    },
    slums: {
        n: 'Трущобы',
        sepK: .7,
        style: 'organic',
        curv: 1.0,
        alleys: .9,
        parks: .05,
        ragged: .15,
        popDensity: 1.50,
        bldDensity: 0.95,
        bldForm: 'blob'
    },
    park: {
        n: 'Парк',
        sepK: 1.7,
        style: 'organic',
        curv: 1.1,
        alleys: 0,
        parks: .5,
        ragged: 0,
        popDensity: 0,
        bldDensity: 0,
        bldForm: 'none'
    },
    suburb: {
        n: 'Пригород',
        sepK: 1.15,
        style: 'organic',
        curv: .6,
        alleys: .3,
        parks: .1,
        ragged: .85,
        popDensity: 0.05,
        bldDensity: 0.30,
        bldForm: 'house'
    },
    tech: {
        n: 'Технопарк',
        sepK: 1.1,
        style: 'grid',
        curv: .05,
        alleys: .3,
        parks: .2,
        ragged: 0,
        popDensity: 0.15,
        bldDensity: 0.55,
        bldForm: 'block'
    },
    cemetery: {
        n: 'Кладбище',
        sepK: .78,
        style: 'grid',
        curv: .06,
        alleys: .35,
        parks: .4,
        ragged: 0,
        popDensity: 0,
        bldDensity: 0,
        bldForm: 'none'
    }
};
const PRESETS = {
    metropolis: {
        name: 'Мегаполис',
        W: 2400,
        H: 2760,
        R: 860,
        nd: 9,
        sep: 17,
        farm: 36,
        hw: 4,
        ring: true,
        rail: 2,
        ships: 6,
        rw: 13,
        av: 5,
        pop: 500000
    },
    city: {
        name: 'Город',
        W: 1800,
        H: 2050,
        R: 600,
        nd: 6,
        sep: 17,
        farm: 26,
        hw: 3,
        ring: false,
        rail: 1,
        ships: 4,
        rw: 10,
        av: 3,
        pop: 120000
    },
    village: {
        name: 'Деревня',
        W: 1000,
        H: 1150,
        R: 175,
        nd: 2,
        sep: 24,
        farm: 18,
        hw: 2,
        ring: false,
        rail: 0,
        ships: 2,
        rw: 6,
        av: 0,
        pop: 3000
    }
};
/* Формы города. arx/ary — множители к базовому радиусу P.R.
    angle: 'random' — угол главной оси зависит от берега, 'fixed0' — всегда 0 (для grid)
    grid:  квадратные клетки + принудительная сетка улиц
    spine: рисовать главное шоссе вдоль длинной оси города */
const CITY_SHAPES = {
    round: {n: 'Круглый', arx: 1.00, ary: 1.00, angle: 'random', grid: false, spine: false},
    elongated: {n: 'Вытянутый', arx: 1.85, ary: 0.55, angle: 'random', grid: false, spine: true},
    linear: {n: 'Линейный (трасса)', arx: 2.60, ary: 0.32, angle: 'random', grid: false, spine: true},
    grid: {n: 'Сетка (NYC)', arx: 1.15, ary: 1.15, angle: 'fixed0', grid: true, spine: false}
};

/* =====================================================================
    ДВИЖОК ИМЁН: библиотека + сборка из паттернов
    Формат паттернов: строка с {токенами} или [строка, вес].
    Токены: {adj_m} {adj_f} {adj_n} {noun_m} {noun_f} {noun_n} {noun_pl}
    {gen_pl} {name_m} {name_f} {num}
    {num} — магическое: rint(rng, 2, 99)
    ===================================================================== */
function patternOk(p, spec) {
    const m = p.match(/\{(\w+)\}/g) || [];
    return m.every(t => {
        const k = t.slice(1, -1);
        if (k === 'num') return true;
        return Array.isArray(spec[k]) && spec[k].length > 0;
    });
}

function pickPattern(spec, rng) {
    const list = (spec.patterns || []).map(p => Array.isArray(p) ? p : [p, 1]).filter(([p]) => patternOk(p, spec));
    if (!list.length) return null;
    const total = list.reduce((s, [, w]) => s + w, 0);
    let r = rng() * total;
    for (const [p, w] of list) {
        r -= w;
        if (r <= 0) return p;
    }
    return list[list.length - 1][0];
}

function fillPattern(p, spec, rng) {
    return p.replace(/\{(\w+)\}/g, (_, k) => {
        if (k === 'num') return String(rint(rng, 2, 99));
        const v = spec[k];
        return Array.isArray(v) && v.length ? pick(rng, v) : '';
    });
}

function nameFromSpec(spec, rng) {
    if (!spec) return null;
    const p = pickPattern(spec, rng);
    if (!p) return null;
    return fillPattern(p, spec, rng).replace(/\s+/g, ' ').trim();
}

function pickLib(S, key) {
    const lib = (S && S.nameLib) || NEON_LIB;
    return lib[key] || null;
}

/* ---------- библиотека NEON (встроенная, дефолтная) ---------- */
const _ADJ = [['Старый', 'Старая', 'Старое'], ['Нижний', 'Нижняя', 'Нижнее'], ['Верхний', 'Верхняя', 'Верхнее'], ['Неоновый', 'Неоновая', 'Неоновое'], ['Стальной', 'Стальная', 'Стальное'], ['Медный', 'Медная', 'Медное'], ['Туманный', 'Туманная', 'Туманное'], ['Тёмный', 'Тёмная', 'Тёмное'], ['Хромовый', 'Хромовая', 'Хромовое'], ['Ржавый', 'Ржавая', 'Ржавое'], ['Кислотный', 'Кислотная', 'Кислотное'], ['Чёрный', 'Чёрная', 'Чёрное'], ['Северный', 'Северная', 'Северное'], ['Южный', 'Южная', 'Южное'], ['Западный', 'Западная', 'Западное'], ['Восточный', 'Восточная', 'Восточное'], ['Серебряный', 'Серебряная', 'Серебряное'], ['Забытый', 'Забытая', 'Забытое'], ['Гудящий', 'Гудящая', 'Гудящее'], ['Красный', 'Красная', 'Красное'], ['Кожевенный', 'Кожевенная', 'Кожевенное'], ['Соляной', 'Соляная', 'Соляное'], ['Стеклянный', 'Стеклянная', 'Стеклянное'], ['Электрический', 'Электрическая', 'Электрическое']];
const _ADJ_M = _ADJ.map(a => a[0]), _ADJ_F = _ADJ.map(a => a[1]), _ADJ_N = _ADJ.map(a => a[2]);
const _STREET_G = ['Кузнецов', 'Ткачей', 'Литейщиков', 'Часовщиков', 'Стеклодувов', 'Механиков', 'Связистов', 'Сварщиков', 'Оружейников', 'Гончаров', 'Контрабандистов', 'Рыбаков', 'Торговцев', 'Шестерёнок', 'Электриков', 'Диспетчеров', 'Ремонтников', 'Лампочников'];
const _PAT = [['{adj_m} {noun_m}', 4], ['{adj_f} {noun_f}', 2], ['{adj_n} {noun_n}', 1], ['{noun_m} {num}', 2], ['{noun_f} {num}', 1], ['{noun_pl} {num}', 2]];

function _dt(nm, nf, nn, npl) {
    return {
        patterns: _PAT,
        adj_m: _ADJ_M,
        adj_f: _ADJ_F,
        adj_n: _ADJ_N,
        noun_m: nm || [],
        noun_f: nf || [],
        noun_n: nn || [],
        noun_pl: npl || []
    };
}

const NEON_LIB = {
    id: 'neon', name: 'Неон-нуар (стандарт)', lang: 'ru',
    district: {
        generic: _dt(['Район', 'Квартал'], ['Слобода'], [], ['Трущобы']),
        types: {
            center: _dt(['Центр', 'Город'], ['Площадь'], ['Ядро'], []),
            commerce: _dt(['Рынок', 'Квартал', 'Пассаж'], ['Биржа'], [], []),
            residential: _dt(['Район', 'Квартал', 'Двор'], ['Слобода'], [], []),
            industrial: _dt(['Завод', 'Цех'], ['Промзона'], ['Депо'], []),
            harbor: _dt(['Порт', 'Пирс', 'Док'], ['Гавань'], [], []),
            slums: _dt(['Ярус'], ['Слобода', 'Яма'], [], ['Трущобы']),
            park: _dt(['Парк', 'Сад'], ['Роща', 'Аллея'], [], []),
            suburb: _dt(['Пригород', 'Посёлок'], ['Окраина'], ['Предместье'], []),
            tech: _dt(['Технопарк', 'Кластер', 'Кампус', 'Сектор'], [], [], []),
            cemetery: _dt(['Некрополь', 'Склеп', 'Погост', 'Колумбарий'], [], ['Кладбище'], [])
        }
    },
    street: {
        patterns: [['{adj_f} улица', 3], ['Улица {gen_pl}', 2], ['Проспект {gen_pl}', 1.5], ['Переулок {gen_pl}', 1.5], ['{adj_m} проспект', 1], ['{adj_m} переулок', 1]],
        adj_m: _ADJ_M, adj_f: _ADJ_F, gen_pl: _STREET_G
    },
    river: {
        patterns: ['Река {adj_f}', 'Река {name_f}', '{adj_f} река'],
        adj_f: _ADJ_F,
        name_f: ['Волга', 'Нева', 'Ока', 'Кама', 'Лена']
    },
    city: {
        patterns: ['{prefix}{suffix}'],
        prefix: ['Дон', 'Нейро', 'Красно', 'Сталь', 'Ново', 'Черно', 'Вер', 'Мор', 'Хром', 'Аль', 'Тер', 'Кор'],
        suffix: ['форд', 'град', 'бург', 'полис', 'гард', 'мор', 'сити', 'вилль']
    },
    park: {
        patterns: [['Парк {gen_pl}', 3], ['Сквер {gen_pl}', 2], ['Сад {name_m}', 2], ['{adj_m} сад', 1], ['{adj_f} роща', 1], ['Бульвар {gen_pl}', 1]],
        adj_m: _ADJ_M, adj_f: _ADJ_F, gen_pl: _STREET_G, name_m: ['Теней', 'Отдыха', 'Ветров', 'Сирени']
    },
    waste: {
        patterns: [['Свалка {adj_f}', 2], ['Полигон {adj_m}', 2], ['Отвал {adj_m}', 1], ['Пустырь {adj_m}', 1]],
        adj_m: _ADJ_M, adj_f: _ADJ_F
    },
    special: {
        capitol: {
            patterns: [['Капитолий {name_m}', 2], ['{adj_m} дом', 1], ['Совет {name_m}', 1]],
            adj_m: _ADJ_M,
            name_m: ['Синты', 'Демиурга', 'Совета', 'Основателей']
        },
        monument: {
            patterns: [['Монумент {gen_pl}', 2], ['Обелиск {gen_pl}', 2], ['Стела {gen_pl}', 1]],
            gen_pl: _STREET_G
        },
        gov: {
            patterns: [['Дом {gen_pl}', 2], ['Комитет {name_m}', 1], ['Управление {name_m}', 1]],
            adj_m: _ADJ_M,
            gen_pl: _STREET_G,
            name_m: ['Синты', 'Порядка', 'Севера']
        },
        temple: {
            patterns: [['Обитель {name_f}', 2], ['Храм {name_m}', 2], ['Святилище {name_n}', 1]],
            name_m: ['Теней', 'Света', 'Тишины'],
            name_f: ['Тишины', 'Молитвы'],
            name_n: []
        },
        stadium: {
            patterns: [['Арена {name_f}', 2], ['Стадион {name_m}', 2], ['Колизей {name_m}', 1]],
            name_m: ['Синты', 'Великого Круга', 'Пепла'],
            name_f: ['Синты', 'Ночи']
        },
        landmark: {
            patterns: [['Звезда {name_m}', 1], ['Око {name_n}', 1], ['{adj_f} башня', 1]],
            adj_f: _ADJ_F,
            name_m: ['Севера', 'Восхода', 'Судьбы'],
            name_n: ['Провидения', 'Синты']
        }
    }
};

/* ---------- SLAVIC: славянские корни ---------- */
const SLAVIC_LIB = {
    id: 'slavic', name: 'Славянский', lang: 'ru',
    district: {
        generic: {
            patterns: _PAT,
            adj_m: ['Верхний', 'Нижний', 'Заречный', 'Старший', 'Малый', 'Кривой', 'Сухой', 'Светлый', 'Тёмный'],
            adj_f: ['Верхняя', 'Нижняя', 'Заречная', 'Старшая', 'Малая', 'Кривая', 'Сухая', 'Светлая', 'Тёмная'],
            adj_n: ['Верхнее', 'Нижнее', 'Заречное', 'Малое', 'Кривое', 'Сухое'],
            noun_m: ['Посад', 'Конец', 'Острог'],
            noun_f: ['Слобода', 'Застава'],
            noun_n: ['Заречье', 'Поместье'],
            noun_pl: ['Выселки', 'Пески']
        },
        types: {
            center: {
                patterns: _PAT,
                adj_m: ['Верхний', 'Княжий', 'Государев', 'Соборный'],
                adj_f: ['Верхняя', 'Княжья', 'Соборная'],
                adj_n: ['Государево'],
                noun_m: ['Кремль', 'Детинец', 'Двор', 'Торг'],
                noun_f: ['Площадь'],
                noun_n: ['Городище'],
                noun_pl: []
            },
            commerce: {
                patterns: _PAT,
                adj_m: ['Купеческий', 'Гостиный', 'Торговый'],
                adj_f: ['Гостиная', 'Купеческая'],
                adj_n: ['Торжище'],
                noun_m: ['Ряд', 'Торг', 'Гостинец'],
                noun_f: ['Ярмарка'],
                noun_n: [],
                noun_pl: ['Лавки']
            },
            residential: {
                patterns: _PAT,
                adj_m: ['Стрелецкий', 'Пушкарский', 'Ремесленный', 'Кузнечный', 'Гончарный'],
                adj_f: ['Стрелецкая', 'Пушкарская', 'Ремесленная'],
                adj_n: [],
                noun_m: ['Посад', 'Конец', 'Двор', 'Приказ'],
                noun_f: ['Слобода', 'Застава'],
                noun_n: ['Село'],
                noun_pl: []
            },
            industrial: {
                patterns: _PAT,
                adj_m: ['Кузнечный', 'Литейный', 'Кожевенный', 'Мыловаренный'],
                adj_f: ['Кузнечная'],
                adj_n: [],
                noun_m: ['Завод', 'Двор'],
                noun_f: ['Мастерская', 'Кузня'],
                noun_n: [],
                noun_pl: ['Рудники']
            },
            harbor: {
                patterns: _PAT,
                adj_m: ['Речной', 'Морской', 'Рыбацкий'],
                adj_f: ['Речная', 'Рыбацкая'],
                adj_n: [],
                noun_m: ['Причал', 'Порт'],
                noun_f: ['Пристань', 'Гавань'],
                noun_n: [],
                noun_pl: []
            },
            slums: {
                patterns: _PAT,
                adj_m: ['Кривой', 'Гнилой', 'Нищий', 'Пьяный'],
                adj_f: ['Кривая', 'Гнилая', 'Нищая'],
                adj_n: [],
                noun_m: ['Закоулок', 'Угол'],
                noun_f: ['Яма', 'Слободка'],
                noun_n: [],
                noun_pl: ['Трущобы', 'Выселки']
            },
            park: {
                patterns: _PAT,
                adj_m: ['Государев', 'Соборный', 'Митрополичий'],
                adj_f: ['Соборная', 'Липовая', 'Берёзовая'],
                adj_n: [],
                noun_m: ['Сад', 'Луг'],
                noun_f: ['Роща', 'Дубрава'],
                noun_n: [],
                noun_pl: []
            },
            suburb: {
                patterns: _PAT,
                adj_m: ['Заречный', 'Дальний', 'Выселочный'],
                adj_f: ['Заречная', 'Дальняя'],
                adj_n: [],
                noun_m: ['Посад'],
                noun_f: ['Слободка'],
                noun_n: ['Заречье', 'Выселок'],
                noun_pl: ['Выселки']
            },
            tech: {
                patterns: _PAT,
                adj_m: ['Учёный', 'Книжный'],
                adj_f: ['Учёная', 'Книжная'],
                adj_n: [],
                noun_m: ['Двор', 'Приказ'],
                noun_f: ['Школа', 'Библиотека'],
                noun_n: [],
                noun_pl: []
            },
            cemetery: {
                patterns: _PAT,
                adj_m: ['Старческий', 'Монастырский'],
                adj_f: ['Монастырская'],
                adj_n: [],
                noun_m: ['Погост', 'Скит'],
                noun_f: ['Обитель', 'Усыпальница'],
                noun_n: ['Кладбище'],
                noun_pl: []
            }
        }
    },
    street: {
        patterns: [['{adj_f} улица', 4], ['Улица {gen_pl}', 3], ['Переулок {gen_pl}', 2], ['Проезд {gen_pl}', 1], ['{adj_m} проезд', 1], ['Площадь {gen_pl}', 1]],
        adj_m: ['Кузнечный', 'Гончарный', 'Столярный', 'Плотницкий', 'Кожевенный', 'Старший'],
        adj_f: ['Кузнечная', 'Гончарная', 'Столярная', 'Плотницкая', 'Кожевенная', 'Кривая', 'Тихая', 'Садовая'],
        gen_pl: ['Кузнецов', 'Гончаров', 'Плотников', 'Столяров', 'Кожевников', 'Мясников', 'Ткачей', 'Ямщиков', 'Стрельцов', 'Пушкарей', 'Рыбаков', 'Мельников']
    },
    river: {
        patterns: ['Река {adj_f}', 'Река {name_f}'],
        adj_f: ['Тихая', 'Быстрая', 'Тёмная', 'Светлая', 'Мутная'],
        name_f: ['Волга', 'Ока', 'Кама', 'Вятка', 'Двина', 'Днепр', 'Дон', 'Урал', 'Обь', 'Енисей']
    },
    city: {
        patterns: ['{prefix}{suffix}'],
        prefix: ['Ново', 'Старо', 'Красно', 'Бело', 'Велико', 'Свето', 'Верхо', 'Черно'],
        suffix: ['град', 'славль', 'озерск', 'борск', 'полис', 'вец', 'холм', 'устье']
    },
    park: {
        patterns: [['Сад {gen_pl}', 2], ['{adj_f} роща', 2], ['Берёзовая роща', 1], ['Липовый сад', 1], ['Луг {gen_pl}', 1]],
        adj_f: ['Дубовая', 'Берёзовая', 'Липовая', 'Тихая'],
        gen_pl: ['Кузнецов', 'Мельников', 'Ямщиков', 'Гончаров']
    },
    waste: {
        patterns: [['Выселки {num}', 2], ['Пустошь {adj_f}', 2], ['Заброшенное поле', 1]],
        adj_f: ['Кривая', 'Гнилая', 'Дальняя', 'Сухая']
    },
    special: {
        capitol: {patterns: [['Государев двор', 2], ['Княжий терем', 1], ['Детинец', 1]], name_m: []},
        monument: {
            patterns: [['Памятник {gen_pl}', 2], ['Обелиск {name_m}', 1]],
            name_m: ['Основателям', 'Победы', 'Князю'],
            gen_pl: ['Кузнецов', 'Плотников', 'Стрельцов']
        },
        gov: {patterns: [['Приказ {name_m}', 2], ['Двор {name_m}', 1]], name_m: ['Казённый', 'Судный', 'Земский']},
        temple: {
            patterns: [['Храм {name_m}', 2], ['Обитель {name_f}', 2], ['Монастырь {name_m}', 1]],
            name_m: ['Спаса', 'Покрова', 'Николы'],
            name_f: ['Пречистая', 'Тихвинская']
        },
        stadium: {patterns: [['Ратное поле', 2], ['Ипподром', 1], ['Сборное место', 1]], name_m: []},
        landmark: {
            patterns: [['Красные ворота', 1], ['{adj_f} башня', 1], ['Звонница {name_f}', 1]],
            adj_f: ['Великая', 'Крепостная', 'Сторожевая'],
            name_f: ['Ивана', 'Софии', 'Дмитрия']
        }
    }
};

/* ---------- TECH: техно-утопия / sci-fi ---------- */
const TECH_LIB = {
    id: 'tech', name: 'Техно-утопия', lang: 'ru',
    district: {
        generic: {
            patterns: _PAT,
            adj_m: ['Северный', 'Южный', 'Центральный', 'Внешний', 'Кольцевой'],
            adj_f: ['Северная', 'Центральная', 'Внешняя'],
            adj_n: ['Ядровое'],
            noun_m: ['Сектор', 'Кластер', 'Квартал'],
            noun_f: ['Зона', 'Платформа'],
            noun_n: ['Кольцо'],
            noun_pl: []
        },
        types: {
            center: {
                patterns: _PAT,
                adj_m: ['Нулевой', 'Главный', 'Центральный', 'Административный'],
                adj_f: ['Нулевая', 'Центральная'],
                adj_n: ['Ядровое'],
                noun_m: ['Хаб', 'Узел', 'Кластер', 'Сектор'],
                noun_f: ['Платформа', 'Площадь'],
                noun_n: ['Ядро'],
                noun_pl: []
            },
            commerce: {
                patterns: _PAT,
                adj_m: ['Торговый', 'Деловой', 'Финансовый'],
                adj_f: ['Деловая', 'Торговая'],
                adj_n: [],
                noun_m: ['Сектор', 'Обменник', 'Терминал', 'Узел'],
                noun_f: ['Биржа'],
                noun_n: [],
                noun_pl: []
            },
            residential: {
                patterns: _PAT,
                adj_m: ['Жилой', 'Спальный', 'Модульный', 'Кластерный'],
                adj_f: ['Жилая'],
                adj_n: [],
                noun_m: ['Сектор', 'Модуль', 'Кластер', 'Массив'],
                noun_f: ['Станция', 'Платформа'],
                noun_n: [],
                noun_pl: []
            },
            industrial: {
                patterns: _PAT,
                adj_m: ['Промышленный', 'Заводской', 'Реакторный'],
                adj_f: ['Промышленная'],
                adj_n: [],
                noun_m: ['Реактор', 'Массив', 'Терминал', 'Узел'],
                noun_f: ['Станция', 'Фабрика'],
                noun_n: [],
                noun_pl: []
            },
            harbor: {
                patterns: _PAT,
                adj_m: ['Портовый', 'Грузовой', 'Логистический'],
                adj_f: ['Портовая'],
                adj_n: [],
                noun_m: ['Терминал', 'Причал', 'Док'],
                noun_f: ['Гавань', 'Платформа'],
                noun_n: [],
                noun_pl: []
            },
            slums: {
                patterns: _PAT,
                adj_m: ['Ржавый', 'Грязный', 'Забытый', 'Сборочный'],
                adj_f: ['Ржавая', 'Забытая'],
                adj_n: [],
                noun_m: ['Ярус', 'Свалка', 'Остов', 'Сектор'],
                noun_f: ['Руина'],
                noun_n: [],
                noun_pl: []
            },
            park: {
                patterns: _PAT,
                adj_m: ['Биокупол', 'Оранжерейный', 'Гидропонный'],
                adj_f: ['Биокупол', 'Оранжерейная'],
                adj_n: [],
                noun_m: ['Сад', 'Биокупол', 'Оазис'],
                noun_f: ['Роща', 'Теплица'],
                noun_n: [],
                noun_pl: []
            },
            suburb: {
                patterns: _PAT,
                adj_m: ['Внешний', 'Пригородный', 'Спальный'],
                adj_f: ['Внешняя', 'Пригородная'],
                adj_n: [],
                noun_m: ['Массив', 'Пояс'],
                noun_f: ['Зона', 'Окраина'],
                noun_n: [],
                noun_pl: []
            },
            tech: {
                patterns: _PAT,
                adj_m: ['Научный', 'Исследовательский', 'Технический', 'Квантовый'],
                adj_f: ['Научная', 'Квантовая'],
                adj_n: [],
                noun_m: ['Кампус', 'Кластер', 'Институт', 'Сектор'],
                noun_f: ['Лаборатория', 'Станция'],
                noun_n: [],
                noun_pl: []
            },
            cemetery: {
                patterns: _PAT,
                adj_m: ['Цифровой', 'Архивный', 'Мемориальный'],
                adj_f: ['Архивная'],
                adj_n: [],
                noun_m: ['Архив', 'Мемориал'],
                noun_f: ['Усыпальница'],
                noun_n: ['Хранилище'],
                noun_pl: []
            }
        }
    },
    street: {
        patterns: [['{adj_f} линия', 3], ['{adj_f} платформа', 2], ['Коридор {gen_pl}', 2], ['Проспект {gen_pl}', 2], ['Трасса {gen_pl}', 1], ['Линия {gen_pl}', 2]],
        adj_m: ['Нулевой', 'Квантовый', 'Первый', 'Второй', 'Внешний', 'Центральный'],
        adj_f: ['Нулевая', 'Квантовая', 'Первая', 'Вторая', 'Внешняя', 'Центральная'],
        gen_pl: ['Инженеров', 'Операторов', 'Пилотов', 'Механиков', 'Техников', 'Программистов', 'Строителей', 'Диспетчеров', 'Энергетиков', 'Реакторщиков']
    },
    river: {
        patterns: ['Поток {adj_m}', 'Канал {adj_m}', 'Протока {adj_f}', '{adj_m} поток'],
        adj_m: ['Нулевой', 'Первый', 'Технический', 'Реакторный'],
        adj_f: ['Техническая', 'Охлаждающая'],
        name_f: ['Артерия', 'Магистраль']
    },
    city: {
        patterns: ['{prefix}{suffix}'],
        prefix: ['Нейро', 'Кибер', 'Техно', 'Крипто', 'Кванто', 'Электро', 'Био', 'Мега'],
        suffix: ['полис', 'сити', 'форт', 'холл', 'град', 'хаб', 'станция', 'улей']
    },
    park: {
        patterns: [['Биокупол {num}', 2], ['Оазис {name_m}', 2], ['Сад {gen_pl}', 1], ['Гидропоника {num}', 1]],
        name_m: ['Ноль', 'Один', 'Света', 'Тени'],
        gen_pl: ['Инженеров', 'Операторов']
    },
    waste: {
        patterns: [['Полигон {num}', 2], ['Отвал {adj_m}', 2], ['Свалка {adj_f}', 1]],
        adj_m: ['Ржавый', 'Технический', 'Северный'],
        adj_f: ['Ржавая', 'Техническая']
    },
    special: {
        capitol: {
            patterns: [['Капитолий {name_m}', 2], ['Ядро {name_n}', 1], ['Совет {name_m}', 1]],
            name_m: ['Синты', 'Системы'],
            name_n: ['Ядра', 'Управления']
        },
        monument: {
            patterns: [['Монумент {name_m}', 2], ['Стела {name_f}', 2]],
            name_m: ['Нулю', 'Основателям', 'Запуску'],
            name_f: ['Нулевая', 'Квантовая']
        },
        gov: {
            patterns: [['Комитет {name_m}', 2], ['Управление {name_n}', 2]],
            name_m: ['Безопасности', 'Порядка'],
            name_n: ['Синты', 'Системы']
        },
        temple: {patterns: [['Храм {name_n}', 2], ['Серверная {num}', 1]], name_n: ['Данных', 'Машины', 'Провидения']},
        stadium: {patterns: [['Арена {num}', 2], ['Купол {num}', 2]], name_m: []},
        landmark: {
            patterns: [['Обелиск {name_m}', 1], ['Око {name_n}', 1]],
            name_m: ['Наблюдателя'],
            name_n: ['Синты', 'Провидения']
        }
    }
};

const NAME_LIBS = {neon: NEON_LIB, slavic: SLAVIC_LIB, tech: TECH_LIB};

/* ---------- сборка конкретных имён ---------- */
function districtName(S, rng, type, used) {
    const lib = pickLib(S, 'district') || NEON_LIB.district;
    const spec = (lib.types && lib.types[type]) || lib.generic;
    for (let t = 0; t < 30; t++) {
        const name = nameFromSpec(spec, rng);
        if (name && !used.has(name)) {
            used.add(name);
            return name;
        }
    }
    const base = (spec.noun_m && spec.noun_m[0]) || 'Район';
    const name = base + ' ' + rint(rng, 100, 999);
    used.add(name);
    return name;
}

function streetName(S, rng) {
    const s = pickLib(S, 'street') || NEON_LIB.street;
    return nameFromSpec(s, rng) || 'Улица ' + rint(rng, 1, 99);
}

function riverName(S, rng) {
    const s = pickLib(S, 'river') || NEON_LIB.river;
    return nameFromSpec(s, rng) || 'Река ' + rint(rng, 1, 99);
}

function cityName(S, rng) {
    const s = pickLib(S, 'city') || NEON_LIB.city;
    return nameFromSpec(s, rng) || 'Город ' + rint(rng, 1, 99);
}

function objectName(S, rng, kind, sub) {
    const lib = pickLib(S, kind) || NEON_LIB[kind];
    if (!lib) return null;
    const spec = sub ? (lib[sub] || null) : lib;
    if (!spec) return null;
    return nameFromSpec(spec, rng);
}

/* =====================================================================
    МИР: оболочка, методы
    ===================================================================== */
function attachMethods(S) {
    S.noise = makeNoise(S.seed);
    S.waterAt = (x, y) => sampleField(S.water, S.gw, S.gh, S.cell, x, y);
    S.heightAt = (x, y) => sampleField(S.height, S.gw, S.gh, S.cell, x, y);
    S.deepAt = (x, y) => S.waterBlur ? sampleField(S.waterBlur, S.gw, S.gh, S.cell, x, y) : 0;
    S.inRiver = (x, y) => {
        if (!S.rb.size) return false;
        const ix = Math.floor(x / 24), iy = Math.floor(y / 24);
        for (let dx = -1; dx <= 1; dx++) for (let dy = -1; dy <= 1; dy++) {
            const a = S.rb.get((ix + dx + 64) * 4096 + (iy + dy + 64));
            if (!a) continue;
            for (let k = 0; k < a.length; k += 3) {
                const ex = a[k] - x, ey = a[k + 1] - y, r = a[k + 2];
                if (ex * ex + ey * ey < r * r) return true;
            }
        }
        return false;
    };
}

function defaultStyle() {
    return {glow: 1, line: 1, tint: .06, grain: .5, scan: .35, vignette: .55, labelScale: 1, labelFont: 'Exo 2'};
}

function defaultLayers() {
    return {
        farm: true,
        water: true,
        mountains: true,
        rivers: true,
        buildings: true,
        streets: true,
        boundaries: true,
        parks: true,
        waste: true,
        roads: true,
        rails: true,
        icons: true,
        districtNames: true,
        streetNames: true,
        roadNames: true,
        objectNames: true
    };
}

function newShell(preset, seed) {
    const P = PRESETS[preset];
    const S = {
        v: 1,
        preset,
        seed: seed >>> 0,
        W: P.W,
        H: P.H,
        cell: 10,
        nextId: 1,
        name: '',
        center: [P.W / 2, P.H / 2],
        ell: {rx: P.R, ry: P.R, rot: 0},
        seaSide: null,
        rivers: [],
        districts: [],
        roads: [],
        labels: [],
        icons: [],
        farm: [],
        green: [],
        waste: [],
        rb: new Map(),
        pal: clone(PALETTES.neon),
        nameLib: clone(NEON_LIB),
        style: defaultStyle(),
        layers: defaultLayers()
    };
    S.gw = Math.ceil(S.W / S.cell);
    S.gh = Math.ceil(S.H / S.cell);
    S.water = new Float32Array(S.gw * S.gh);
    S.height = new Float32Array(S.gw * S.gh);
    attachMethods(S);
    return S;
}

/* ---------- ландшафт ---------- */
function genWater(S, rng, g) {
    const {W, H, gw, gh, cell} = S, nz = S.noise, so = rng() * 100, kind = g.terrain;
    S.seaSide = null;
    if (kind === 'coast' || kind === 'bay') {
        const side = g.seaSide === 'random' ? pick(rng, ['right', 'left', 'top', 'bottom']) : g.seaSide;
        S.seaSide = side;
        const horiz = side === 'right' || side === 'left';
        const dim = horiz ? W : H, len = horiz ? H : W;
        const base = dim * rrange(rng, 0.13, 0.19), bayT = len * rrange(rng, 0.3, 0.7);
        for (let j = 0; j < gh; j++) for (let i = 0; i < gw; i++) {
            const x = (i + .5) * cell, y = (j + .5) * cell;
            let d, t;
            if (side === 'right') {
                d = W - x;
                t = y;
            } else if (side === 'left') {
                d = x;
                t = y;
            } else if (side === 'top') {
                d = y;
                t = x;
            } else {
                d = H - y;
                t = x;
            }
            let coastD = base + (nz.fbm(t * 0.0013 + so, so * .3, 4) - 0.5) * dim * 0.30;
            if (kind === 'bay') {
                const q = (t - bayT) / (len * 0.11);
                coastD += dim * 0.22 * Math.exp(-q * q);
            }
            coastD += (nz.fbm(x * 0.006 + so, y * 0.006, 3) - 0.5) * 70;
            S.water[j * gw + i] = clamp(0.5 + (coastD - d) / 26, 0, 1);
        }
    } else if (kind === 'lake') {
        const m = Math.min(W, H), R0 = m * rrange(rng, .11, .17);
        S.lake = [W * rrange(rng, .25, .75), H * rrange(rng, .25, .75), R0];
        for (let j = 0; j < gh; j++) for (let i = 0; i < gw; i++) {
            const x = (i + .5) * cell, y = (j + .5) * cell;
            const dist = Math.hypot(x - S.lake[0], y - S.lake[1]);
            const rr = R0 * (0.85 + (nz.fbm(x * .005 + so, y * .005, 3) - .5) * 1.0);
            S.water[j * gw + i] = clamp(0.5 + (rr - dist) / 26, 0, 1);
        }
    } else S.lake = null;
}

function pickCenter(S, rng, P, g) {
    const {W, H} = S, R = P.R;
    const shape = (g && CITY_SHAPES[g.cityShape]) || CITY_SHAPES.round;
    const side = S.seaSide;

    // 1. Угол главной оси. Если город у моря — ось вдоль берега.
    let mainAngle;
    if (shape.angle === 'fixed0') mainAngle = 0;
    else {
        let base = 0;
        if (side === 'right' || side === 'left') base = Math.PI / 2;
        mainAngle = base + rrange(rng, -0.35, 0.35);
    }

    // 2. Размеры эллипса с сохранением примерно равной площади
    const areaK = 1 / Math.sqrt(shape.arx * shape.ary);
    let rx = R * shape.arx * areaK;
    let ry = R * shape.ary * areaK;

    // 3. Ограничиваем габариты, чтобы не вылезало за карту
    const maxDim = Math.min(W, H) * 0.92;
    if (rx * 2 > maxDim) {
        const s = maxDim / (rx * 2);
        rx *= s;
        ry *= s;
    }
    if (ry * 2 > maxDim) {
        const s = maxDim / (ry * 2);
        ry *= s;
        rx *= s;
    }

    // 4. Позиция центра
    const safeR = Math.max(rx, ry);
    let cx = W * rrange(rng, .45, .55), cy = H * rrange(rng, .45, .55);
    if (side === 'right') {
        cy = H * rrange(rng, .38, .6);
        let x = W - 1;
        while (x > 0 && S.waterAt(x, cy) > 0.5) x -= 4;
        cx = x - rx * 0.6;
    } else if (side === 'left') {
        cy = H * rrange(rng, .38, .6);
        let x = 1;
        while (x < W && S.waterAt(x, cy) > 0.5) x += 4;
        cx = x + rx * 0.6;
    } else if (side === 'top') {
        cx = W * rrange(rng, .4, .6);
        let y = 1;
        while (y < H && S.waterAt(cx, y) > 0.5) y += 4;
        cy = y + ry * 0.6;
    } else if (side === 'bottom') {
        cx = W * rrange(rng, .4, .6);
        let y = H - 1;
        while (y > 0 && S.waterAt(cx, y) > 0.5) y -= 4;
        cy = y - ry * 0.6;
    } else if (S.lake) {
        const a = rng() * TAU, dd = S.lake[2] + safeR * .45;
        cx = S.lake[0] + Math.cos(a) * dd;
        cy = S.lake[1] + Math.sin(a) * dd;
    }
    cx = clamp(cx, safeR * .7, W - safeR * .7);
    cy = clamp(cy, safeR * .7, H - safeR * .7);

    S.center = [cx, cy];
    S.ell = {rx, ry, rot: mainAngle};
}

function genMountains(S, rng, g) {
    const n = g.mountains;
    if (!n) return;
    const {gw, gh, cell} = S, m0 = Math.min(S.W, S.H);
    for (let m = 0; m < n; m++) {
        let cx, cy, tries = 0;
        do {
            cx = rng() * S.W;
            cy = rng() * S.H;
            tries++;
        } while (tries < 300 && (Math.hypot((cx - S.center[0]) / (S.ell.rx * 1.4), (cy - S.center[1]) / (S.ell.ry * 1.4)) < 1 || S.waterAt(cx, cy) > 0.3));
        const ang = rng() * Math.PI, len = rrange(rng, .12, .24) * m0, sig = rrange(rng, .05, .085) * m0;
        const bumps = [], nb = rint(rng, 5, 9);
        for (let k = 0; k < nb; k++) {
            const t = (k / (nb - 1) - .5) * len;
            bumps.push({
                x: cx + Math.cos(ang) * t + (rng() - .5) * sig,
                y: cy + Math.sin(ang) * t + (rng() - .5) * sig,
                s: sig * rrange(rng, .6, 1.2),
                h: rrange(rng, .55, 1)
            });
        }
        for (let j = 0; j < gh; j++) for (let i = 0; i < gw; i++) {
            const x = (i + .5) * cell, y = (j + .5) * cell;
            let h = 0;
            for (const b of bumps) {
                const dx = x - b.x, dy = y - b.y;
                if (Math.abs(dx) > b.s * 3.5 || Math.abs(dy) > b.s * 3.5) continue;
                h += b.h * Math.exp(-(dx * dx + dy * dy) / (2 * b.s * b.s));
            }
            if (h < 0.02) continue;
            h *= 0.75 + 0.5 * S.noise.fbm(x * .012 + m * 7, y * .012, 3);
            const idx = j * gw + i;
            if (h > S.height[idx]) S.height[idx] = Math.min(1, h);
        }
    }
    for (let i = 0; i < S.height.length; i++) if (S.water[i] > 0.5) S.height[i] = 0;
}

function riverPath(S, rng, k) {
    const c = S.center, R = (S.ell.rx + S.ell.ry) / 2, L = Math.hypot(S.W, S.H);
    let ang;
    if (S.seaSide) {
        const base = {right: 0, left: Math.PI, bottom: Math.PI / 2, top: -Math.PI / 2}[S.seaSide];
        ang = base + rrange(rng, -.7, .7);
    } else ang = rng() * Math.PI;
    const nx = -Math.sin(ang), ny = Math.cos(ang), off = (k === 0 ? rrange(rng, -.25, .25) : rrange(rng, -.9, .9)) * R;
    const ax = c[0] + nx * off, ay = c[1] + ny * off, n = Math.ceil(2 * L / 70), seed = rng() * 50;
    let cur = [], best = [];
    for (let i = 0; i <= n; i++) {
        const t = i / n, s = (t - .5) * 2 * L, m = (S.noise.fbm(t * 6 + seed, k * 3.3 + .5, 3) - .5) * 2 * R * .5;
        const x = ax + Math.cos(ang) * s + nx * m, y = ay + Math.sin(ang) * s + ny * m;
        if (x > 4 && y > 4 && x < S.W - 4 && y < S.H - 4) cur.push([x, y]); else {
            if (cur.length > best.length) best = cur;
            cur = [];
        }
    }
    if (cur.length > best.length) best = cur;
    return best;
}

function genRivers(S, rng, g, P) {
    const n = g.rivers + (g.terrain === 'river' ? 1 : 0);
    for (let k = 0; k < n; k++) {
        const path = riverPath(S, rng, k);
        if (path.length >= 3) S.rivers.push({
            id: S.nextId++,
            name: riverName(S, rng),
            pts: path,
            width: P.rw * rrange(rng, .8, 1.25)
        });
    }
}

/* ---------- районы ---------- */
function makeDistrict(S, type, poly, rng, name) {
    const T = TYPES[type];
    const d = {
        id: S.nextId++,
        name,
        type,
        poly,
        color: null,
        seed: Math.floor(rng() * 1e9),
        angle: rrange(rng, 0, Math.PI),
        style: T.style,
        curv: T.curv,
        sep: Math.round((S.baseSep * T.sepK) * 10) / 10,
        ratio: Math.round(rrange(rng, 1, 1.6) * 100) / 100,
        alleys: T.alleys,
        parks: T.parks,
        ragged: T.ragged,
        warp: Math.round(T.style === 'organic' ? rrange(rng, 140, 260) : rrange(rng, 300, 520)),
        lblScale: 1,
        showLabel: true,
        density: T.bldDensity,
        pop: 0,
        bldForm: T.bldForm
    };
    return d;
}

function computeLabel(d) {
    const poly = d.poly, bb = bboxOf(poly), N = 18;
    let best = null, bd = -1;
    for (let i = 0; i < N; i++) for (let j = 0; j < N; j++) {
        const x = bb[0] + (i + .5) / N * (bb[2] - bb[0]), y = bb[1] + (j + .5) / N * (bb[3] - bb[1]);
        if (!pip(x, y, poly)) continue;
        const dd = distPoly(x, y, poly);
        if (dd > bd) {
            bd = dd;
            best = [x, y];
        }
    }
    if (!best) best = polyCentroid(poly);
    const n = poly.length;
    let mx = 0, my = 0;
    for (const p of poly) {
        mx += p[0];
        my += p[1];
    }
    mx /= n;
    my /= n;
    let sxx = 0, syy = 0, sxy = 0;
    for (const p of poly) {
        const dx = p[0] - mx, dy = p[1] - my;
        sxx += dx * dx;
        syy += dy * dy;
        sxy += dx * dy;
    }
    sxx /= n;
    syy /= n;
    sxy /= n;
    let th = 0.5 * Math.atan2(2 * sxy, sxx - syy);
    if (th > Math.PI / 2) th -= Math.PI;
    if (th < -Math.PI / 2) th += Math.PI;
    const tr = sxx + syy, det = sxx * syy - sxy * sxy, l1 = tr / 2 + Math.sqrt(Math.max(0, tr * tr / 4 - det));
    const L = 3.2 * Math.sqrt(l1), ang = Math.abs(th) > 0.6 ? 0 : th, chars = Math.max(4, d.name.length);
    d.lbl = {x: best[0], y: best[1], ang, size: clamp(0.62 * L / (chars * 0.95), 11, 48)};
}

function genDistricts(S, rng, g, P) {
    const c = S.center, ell = S.ell, nd = g.nd, cr = Math.cos(ell.rot), sr = Math.sin(ell.rot);
    const toW = (ex, ey) => [c[0] + ex * cr - ey * sr, c[1] + ex * sr + ey * cr];
    const shape = (g && CITY_SHAPES[g.cityShape]) || CITY_SHAPES.round;

    // Базовая форма городской застройки: для grid — прямоугольник, иначе — эллипс
    let base = [];
    if (shape.grid) {
        const N = 40;
        for (let k = 0; k < N; k++) {
            const t = k / N * TAU, m = Math.max(Math.abs(Math.cos(t)), Math.abs(Math.sin(t))) || 1;
            base.push(toW(Math.cos(t) / m * ell.rx, Math.sin(t) / m * ell.ry));
        }
    } else {
        for (let k = 0; k < 72; k++) {
            const a = k / 72 * TAU;
            base.push(toW(Math.cos(a) * ell.rx, Math.sin(a) * ell.ry));
        }
    }
    base = clipHalf(base, -1, 0, 0);
    base = clipHalf(base, 1, 0, S.W);
    base = clipHalf(base, 0, -1, 0);
    base = clipHalf(base, 0, 1, S.H);

    // Seeds: для grid — регулярная квадратная сетка, иначе — Poisson-диск
    const seeds = [];
    let dmin = Math.sqrt(Math.PI * ell.rx * ell.ry / nd) * 0.85;
    if (shape.grid) {
        const n3 = Math.max(2, Math.ceil(Math.sqrt(nd)));
        const step = 1.8 / n3;
        for (let ix = 0; ix < n3 && seeds.length < nd; ix++) for (let iy = 0; iy < n3 && seeds.length < nd; iy++) {
            const u = (ix + 0.5) * step - 0.9;
            const v = (iy + 0.5) * step - 0.9;
            seeds.push(toW(u * ell.rx, v * ell.ry));
        }
    } else {
        seeds.push([c[0] + rrange(rng, -.05, .05) * ell.rx, c[1] + rrange(rng, -.05, .05) * ell.ry]);
        let tries = 0;
        while (seeds.length < nd && tries < 4000) {
            tries++;
            const a = rng() * TAU, rr = Math.sqrt(rng()) * 0.92;
            const p = toW(Math.cos(a) * rr * ell.rx, Math.sin(a) * rr * ell.ry);
            let ok = true;
            for (const s of seeds) if (Math.hypot(s[0] - p[0], s[1] - p[1]) < dmin) {
                ok = false;
                break;
            }
            if (ok) seeds.push(p);
            if (tries % 200 === 0) dmin *= 0.9;
        }
    }
    const wts = seeds.map((s, i) => i === 0 ? dmin * .25 : rng() * dmin * .35);
    const cells = seeds.map((s, i) => {
        let poly = base.map(p => p.slice());
        for (let j = 0; j < seeds.length; j++) {
            if (j === i) continue;
            const sj = seeds[j];
            const nx = sj[0] - s[0], ny = sj[1] - s[1],
                c2 = ((sj[0] * sj[0] + sj[1] * sj[1]) - (s[0] * s[0] + s[1] * s[1]) + wts[i] * wts[i] - wts[j] * wts[j]) / 2;
            poly = clipHalf(poly, nx, ny, c2);
            if (poly.length < 3) break;
        }
        return poly;
    });
    const amp = ell.rx * 0.055, Ls = clamp(S.baseSep * 1.3, 10, 26);
    const disp = (x, y) => [(S.noise.fbm(x / 230 + 11, y / 230 + 3, 3) - .5) * 2 * amp, (S.noise.fbm(x / 230 + 37, y / 230 + 91, 3) - .5) * 2 * amp];
    const refine = poly => {
        const out = [], n = poly.length;
        for (let i = 0; i < n; i++) {
            const a = poly[i], b = poly[(i + 1) % n], L = Math.hypot(b[0] - a[0], b[1] - a[1]),
                m = Math.max(1, Math.ceil(L / Ls));
            for (let k = 0; k < m; k++) {
                const t = k / m;
                out.push([a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t]);
            }
        }
        return out.map(p => {
            const dd = disp(p[0], p[1]);
            return [p[0] + dd[0], p[1] + dd[1]];
        });
    };
    // информация о клетках
    const info = cells.map((poly, i) => {
        if (poly.length < 3) return null;
        const cen = polyCentroid(poly);
        const rho = Math.sqrt(Math.pow((cen[0] - c[0]), 2) / (ell.rx * ell.rx) + Math.pow((cen[1] - c[1]), 2) / (ell.ry * ell.ry));
        let wet = 0;
        for (const p of poly) {
            if (S.waterAt(p[0], p[1]) > 0.5) wet++;
        }
        let coast = 0;
        for (let k = 0; k < 8; k++) {
            const a = k / 8 * TAU;
            if (S.waterAt(cen[0] + Math.cos(a) * 180, cen[1] + Math.sin(a) * 180) > 0.5) coast++;
        }
        return {poly, i, rho, outer: rho > 0.72, wet: wet / poly.length + coast * 0.1, cen};
    }).filter(Boolean);
    info.sort((a, b) => a.rho - b.rho);
    const types = new Map();
    const used = new Set();
    if (info.length) types.set(info[0].i, nd >= 3 ? 'center' : 'commerce');
    if (S.seaSide || S.lake) {
        const wetc = info.filter(o => o !== info[0]).sort((a, b) => b.wet - a.wet);
        if (wetc.length && wetc[0].wet > 0.05) types.set(wetc[0].i, 'harbor');
    }
    const inner = shuffle(rng, ['commerce', 'residential', 'tech', 'industrial', 'residential', 'slums', 'park', 'cemetery']);
    let ii = 0;
    for (const o of info) {
        if (types.has(o.i)) continue;
        if (o.outer && info.length > 3) types.set(o.i, rng() < .5 ? 'suburb' : pick(rng, ['industrial', 'residential', 'suburb']));
        else types.set(o.i, inner[ii++ % inner.length]);
    }
    if (nd === 2 && info.length > 1) types.set(info[1].i, 'suburb');
    const dsetup = g.sep;
    S.baseSep = dsetup;
    for (const o of info) {
        const type = types.get(o.i), poly = ensureCCW(refine(o.poly)), name = districtName(S, rng, type, used);
        const d = makeDistrict(S, type, poly, rng, name);
        // NYC-стиль: всем районам — одна сетка, минимум извилистости
        if (shape.grid) {
            d.style = 'grid';
            d.angle = 0;
            d.curv = 0.02;
            d.ratio = 1;
            d.warp = 9999;
            d.ragged = 0;
        } else if (type === 'suburb' || (o.outer && (type === 'industrial' || type === 'residential'))) {
            d.ragged = Math.max(d.ragged, .7);
        }
        computeLabel(d);
        S.districts.push(d);
    }
    // распределить население по районам
    S.targetPop = g.targetPop || PRESETS[S.preset].pop;
    allocatePopulation(S, S.targetPop);
}

/* ---------- парки и зелёные зоны ---------- */
function genGreen(S, rng, g) {
    const c = S.center, ell = S.ell;
    const N = Math.max(4, Math.round((g.nd || 6) * 1.1));
    for (let k = 0; k < N; k++) {
        let x, y, tries = 0;
        do {
            x = rng() * S.W;
            y = rng() * S.H;
            tries++;
        }
        while (tries < 40 && (S.waterAt(x, y) > 0.35 || S.heightAt(x, y) > 0.35 || S.inRiver(x, y)));
        if (tries >= 40) continue;
        // стараемся держаться в пределах города
        const dd = Math.hypot(x - c[0], y - c[1]);
        if (dd > Math.max(ell.rx, ell.ry) * 1.35) continue;
        const clusterR = 26 + rng() * 46;
        const nm = 1 + Math.floor(rng() * 3);
        for (let i = 0; i < nm; i++) {
            const a = rng() * TAU, rr = rng() * clusterR;
            addBlobEntity(S, x + Math.cos(a) * rr, y + Math.sin(a) * rr, 'green', rng);
        }
        // одна осмысленная зона на кластер — с именем
        const firstOfCluster = S.green[S.green.length - nm];
        if (firstOfCluster) {
            firstOfCluster.name = objectName(S, rng, 'park') || 'Парк';
            firstOfCluster.showLabel = true;
        }
    }
}

/* ---------- свалки ---------- */
function genWaste(S, rng, g) {
    const cands = S.districts.filter(d => d.type === 'industrial' || d.type === 'harbor');
    if (!cands.length) return;
    const n = 1 + Math.floor(rng() * 2);
    for (let k = 0; k < n; k++) {
        const target = cands[Math.floor(rng() * cands.length)];
        const bb = bboxOf(target.poly);
        for (let t = 0; t < 25; t++) {
            // часто кладём чуть снаружи промзоны — на пустырях
            const x = bb[0] - 40 + rng() * (bb[2] - bb[0] + 80);
            const y = bb[1] - 40 + rng() * (bb[3] - bb[1] + 80);
            if (S.waterAt(x, y) > 0.3 || S.heightAt(x, y) > 0.35) continue;
            const clusterR = 26 + rng() * 36;
            const nm = 2 + Math.floor(rng() * 3);
            for (let i = 0; i < nm; i++) {
                const a = rng() * TAU, rr = rng() * clusterR;
                addBlobEntity(S, x + Math.cos(a) * rr, y + Math.sin(a) * rr, 'waste', rng);
            }
            const first = S.waste[S.waste.length - nm];
            if (first) {
                first.name = objectName(S, rng, 'waste') || 'Свалка';
                first.showLabel = true;
            }
            break;
        }
    }
}

/* ---------- особые здания ---------- */
const SPECIAL_FOR_TYPE = {
    center: ['monument', 'gov', 'temple'],
    commerce: ['monument', 'gov', 'landmark'],
    residential: ['temple', 'stadium'],
    suburb: ['stadium', 'temple'],
    tech: ['stadium', 'landmark', 'gov'],
    park: ['monument'],
    industrial: [],
    harbor: [],
    slums: [],
    cemetery: []
};

function genSpecial(S, rng, g) {
    if (!S.districts.length) return;
    const okSpot = (x, y, d) => { // Проверка суша + не река + район(при необходимости)
        if (S.waterAt(x, y) > 0.4 || S.inRiver(x, y)) return false;
        if (d && !pip(x, y, d.poly)) return false;
        return true;
    };
    const byRho = S.districts.map(d => {
        const c = polyCentroid(d.poly);
        return {d, c, rho: Math.hypot(c[0] - S.center[0], c[1] - S.center[1]) / Math.max(S.ell.rx, S.ell.ry)};
    }).sort((a, b) => a.rho - b.rho);
    const seat = byRho[0];
    if (seat && (seat.d.type === 'center' || seat.d.type === 'commerce')) {
        let capX = seat.c[0], capY = seat.c[1], capOk = okSpot(capX, capY, seat.d);
        if (!capOk) { // Точка под капитолий ищется без любой воды
            const bb = bboxOf(seat.d.poly);
            for (let t = 0; t < 60 && !capOk; t++) {
                const x = bb[0] + rng() * (bb[2] - bb[0]);
                const y = bb[1] + rng() * (bb[3] - bb[1]);
                if (okSpot(x, y, seat.d)) { capX = x; capY = y; capOk = true; }
            }
        }
        if (capOk) {
            S.icons.push({
                id: S.nextId++,
                type: 'capitol',
                x: capX, y: capY, ang: 0,
                size: ICON_SIZES.capitol,
                name: objectName(S, rng, 'special', 'capitol') || 'Капитолий',
                showLabel: true
            });
            for (let k = 0; k < 2; k++) {
                let mx = 0, my = 0, found = false;
                for (let t = 0; t < 24 && !found; t++) {
                    const a = rng() * TAU, dd = 70 + rng() * 110;
                    const x = capX + Math.cos(a) * dd, y = capY + Math.sin(a) * dd;
                    if (okSpot(x, y, null)) { mx = x; my = y; found = true; }
                }
                if (!found) continue;
                S.icons.push({
                    id: S.nextId++,
                    type: 'monument',
                    x: mx, y: my, ang: 0,
                    size: ICON_SIZES.monument,
                    name: objectName(S, rng, 'special', 'monument'),
                    showLabel: true
                });
            }
        }
    }
    // 2. По районам — 1–2 особых здания там, где это уместно
    for (const d of S.districts) {
        if (d === seat.d) continue;
        const pool = SPECIAL_FOR_TYPE[d.type] || [];
        if (!pool.length) continue;
        if (rng() > 0.55) continue;
        const cnt = 1 + Math.floor(rng() * 2);
        const bb = bboxOf(d.poly);
        for (let k = 0; k < cnt; k++) {
            const ty = pool[Math.floor(rng() * pool.length)];
            for (let t = 0; t < 30; t++) {
                const x = bb[0] + rng() * (bb[2] - bb[0]);
                const y = bb[1] + rng() * (bb[3] - bb[1]);
                if (!pip(x, y, d.poly)) continue;
                if (S.waterAt(x, y) > 0.4 || S.inRiver(x, y)) continue;
                if (S.icons.some(ic => Math.hypot(ic.x - x, ic.y - y) < 40)) continue;
                S.icons.push({
                    id: S.nextId++,
                    type: ty,
                    x,
                    y,
                    ang: 0,
                    size: ICON_SIZES[ty],
                    name: objectName(S, rng, 'special', ty),
                    showLabel: true
                });
                break;
            }
        }
    }
}

/* ---------- распределение населения ---------- */
function allocatePopulation(S, target) {
    const caps = S.districts.map(d => {
        const T = TYPES[d.type] || {};
        const a = Math.abs(polyArea(d.poly));
        const bd = T.bldDensity || 0;
        const pd = T.popDensity || 0;
        return {d, a, bd, pd, cap: a * bd * pd};
    });
    const totalCap = caps.reduce((s, c) => s + c.cap, 0);
    const k = totalCap > 0 ? clamp(target / totalCap, 0, 1) : 0;
    let total = 0;
    for (const c of caps) {
        c.d.density = Math.round(clamp(c.bd * k, 0, 1) * 1000) / 1000;
        c.d.pop = Math.round(c.a * c.d.density * c.pd);
        total += c.d.pop;
    }
    S.totalPop = total;
}

/* ---------- улицы района ---------- */
function genDistrictRaw(d, S) {
    const rng = mulberry32(d.seed), poly = d.poly, bb = bboxOf(poly), c = polyCentroid(poly),
        area = Math.abs(polyArea(poly));
    const inside = (x, y) => x >= bb[0] && x <= bb[2] && y >= bb[1] && y <= bb[3] && pip(x, y, poly);
    const amp = 0.04 + d.curv * 1.15, freq = 1 / d.warp, ox = (d.seed % 997) * 1.7, oy = (d.seed % 613) * 2.9,
        nz = S.noise;
    const angle = (x, y, fam) => {
        let a;
        if (d.style === 'radial') a = Math.atan2(y - c[1], x - c[0]) + (nz.fbm(x * freq + ox, y * freq + oy, 2) - .5) * amp * .8;
        else a = d.angle + (nz.fbm(x * freq + ox, y * freq + oy, 2) - .5) * 2 * amp;
        return fam ? a + Math.PI / 2 : a;
    };
    const sepB = d.sep, sepA = d.sep * d.ratio, seeds = [];
    if (inside(c[0], c[1])) seeds.push(c[0], c[1]);
    for (let t = 0; t < 60 && seeds.length < 10; t++) {
        const x = bb[0] + rng() * (bb[2] - bb[0]), y = bb[1] + rng() * (bb[3] - bb[1]);
        if (inside(x, y)) seeds.push(x, y);
    }
    const mk = (fam, sep) => traceStreams({
        inside,
        angle,
        fam,
        sep,
        dtest: sep * .55,
        step: clamp(sep * .3, 3, 7),
        rng,
        bbox: bb,
        seeds,
        jit0: .95,
        jit1: 1.55,
        closeLoops: d.style === 'radial'
    });
    const A = mk(0, sepA), B = mk(1, sepB);
    // переулки
    let al = [];
    if (d.alleys > 0.02) {
        const smin = Math.min(sepA, sepB), g2 = new PGrid(smin * .3);
        for (const l of A) for (let i = 0; i < l.length; i += 2) g2.add(l[i], l[i + 1]);
        for (const l of B) for (let i = 0; i < l.length; i += 2) g2.add(l[i], l[i + 1]);
        const cnt = Math.floor(area / (smin * smin) * d.alleys * 0.35), sd = [];
        for (let k = 0; k < cnt; k++) {
            const x = bb[0] + rng() * (bb[2] - bb[0]), y = bb[1] + rng() * (bb[3] - bb[1]);
            if (inside(x, y)) sd.push(x, y);
        }
        const fam = rng() < .5 ? 0 : 1;
        const mkA = f => traceStreams({
            inside,
            angle,
            fam: f,
            sep: smin,
            dtest: smin * .3,
            step: 3,
            rng,
            bbox: bb,
            seeds: [],
            randomTries: 0,
            grid: g2,
            noSeeds: true,
            lenFn: () => 18 + rng() * 70,
            minPts: 4
        });
        // засев вручную: чередуем семейства
        const grid = g2;
        for (let k = 0; k < sd.length; k += 2) {
            const f = ((k >> 1) % 2) ? fam : 1 - fam;
            const x = sd[k], y = sd[k + 1];
            if (grid.nearest(x, y, smin * .3)) continue;
            const one = traceStreams({
                inside,
                angle,
                fam: f,
                sep: smin,
                dtest: smin * .3,
                step: 3,
                rng,
                bbox: bb,
                seeds: [x, y],
                randomTries: 0,
                grid: g2,
                noSeeds: true,
                lenFn: () => 18 + rng() * 70,
                minPts: 4
            });
            for (const l of one) al.push(l);
        }
    }
    // парки
    const parks = [], blocks = area / (sepA * sepB), np = Math.round(blocks * d.parks * 0.06);
    for (let k = 0; k < np; k++) {
        for (let t = 0; t < 4; t++) {
            const x = bb[0] + rng() * (bb[2] - bb[0]), y = bb[1] + rng() * (bb[3] - bb[1]);
            if (!inside(x, y)) continue;
            const r = d.sep * rrange(rng, .7, 2.0), pp = [], n = 12;
            let ok = true;
            for (let q = 0; q < n; q++) {
                const a = q / n * TAU, rr = r * rrange(rng, .72, 1.25);
                const px = x + Math.cos(a) * rr, py = y + Math.sin(a) * rr;
                if (!inside(px, py)) {
                    ok = false;
                    break;
                }
                pp.push([px, py]);
            }
            if (ok) {
                parks.push({poly: pp, bb: bboxOf(pp), c: [x, y]});
                break;
            }
        }
    }
    return {A, B, al, parks};
}

/* =====================================================================
    ФИНАЛИЗАЦИЯ: геометрия для отрисовки
    ===================================================================== */
function cutLine(pts, hard, soft, out) {
    let run = [], prevX = 0, prevY = 0, prevOk = false, prevHard = false;
    const n = pts.length / 2;
    const flush = () => {
        if (run.length >= 4) out.push(run);
        run = [];
    };
    for (let i = 0; i < n; i++) {
        const x = pts[2 * i], y = pts[2 * i + 1], h = hard(x, y), ok = h && (!soft || soft(x, y));
        if (i > 0) {
            if (prevHard && !h) {
                let lo = 0, hi = 1;
                for (let k = 0; k < 6; k++) {
                    const m = (lo + hi) / 2;
                    if (hard(prevX + (x - prevX) * m, prevY + (y - prevY) * m)) lo = m; else hi = m;
                }
                if (prevOk) run.push(prevX + (x - prevX) * lo, prevY + (y - prevY) * lo);
                flush();
            } else if (!prevHard && h) {
                let lo = 0, hi = 1;
                for (let k = 0; k < 6; k++) {
                    const m = (lo + hi) / 2;
                    if (hard(prevX + (x - prevX) * m, prevY + (y - prevY) * m)) hi = m; else lo = m;
                }
                if (ok) run.push(prevX + (x - prevX) * hi, prevY + (y - prevY) * hi);
            }
        }
        if (ok) run.push(x, y); else if (run.length) flush();
        prevX = x;
        prevY = y;
        prevHard = h;
        prevOk = ok;
    }
    flush();
}

function blobPath(P, poly) {
    const n = poly.length, mid = (a, b) => [(a[0] + b[0]) / 2, (a[1] + b[1]) / 2];
    const m0 = mid(poly[0], poly[1]);
    P.moveTo(m0[0], m0[1]);
    for (let i = 1; i <= n; i++) {
        const p = poly[i % n], m = mid(p, poly[(i + 1) % n]);
        P.quadraticCurveTo(p[0], p[1], m[0], m[1]);
    }
    P.closePath();
}

function edgeFlags(S, d, idx) {
    const poly = d.poly, n = poly.length, flags = [];
    for (let i = 0; i < n; i++) {
        const a = poly[i], b = poly[(i + 1) % n], dx = b[0] - a[0], dy = b[1] - a[1], L = Math.hypot(dx, dy) || 1;
        const mx = (a[0] + b[0]) / 2 + dy / L * 6, my = (a[1] + b[1]) / 2 - dx / L * 6;
        let free = true;
        for (let k = 0; k < S.districts.length; k++) {
            if (k === idx) continue;
            const o = S.districts[k], bb = o._bb;
            if (mx < bb[0] || mx > bb[2] || my < bb[1] || my > bb[3]) continue;
            if (pip(mx, my, o.poly)) {
                free = false;
                break;
            }
        }
        flags.push(free);
    }
    return flags;
}

/* ---------- генерация зданий района ---------- */
function genBuildings(S, d, sharedGrid) {
    const T = TYPES[d.type];
    if (!T || T.bldForm === 'none' || (d.density || 0) < 0.02 || !d._bb) {
        d.fin.buildings = [];
        d.fin.buildPath = null;
        return;
    }
    const poly = d.poly, bb = d._bb, c = polyCentroid(poly), sep = d.sep, rng = mulberry32((d.seed ^ 0xB1D5EED) >>> 0);
    const ca = Math.cos(d.angle), sa = Math.sin(d.angle);
    const form = d.bldForm || T.bldForm || 'block';
    // Габариты одного здания в долях от sep, и минимальный зазор от чужих объектов
    const SPEC = {
        block: {w: .30, h: .24, minClear: .55, jitter: .12, varAng: .08, keepAligned: true},
        tower: {w: .34, h: .30, minClear: .62, jitter: .08, varAng: .04, keepAligned: true},
        hall: {w: .62, h: .42, minClear: .70, jitter: .18, varAng: .22, keepAligned: false},
        blob: {w: .18, h: .16, minClear: .34, jitter: .28, varAng: .55, keepAligned: false},
        house: {w: .16, h: .13, minClear: .95, jitter: .30, varAng: .40, keepAligned: false}
    };
    const spec = SPEC[form] || SPEC.block;
    const density = d.density;
    // Шаг сетки: плотнее — меньше шаг
    const step = sep * (1.25 - density * 0.75);
    const minClear = sep * spec.minClear;
    // Общая коллизионная сетка: чужие здания + свои улицы/границы/парки
    const grid = sharedGrid;
    const addPt = (x, y) => grid.add(x, y);
    // свои улицы
    for (const l of d.fin.lines) for (let i = 0; i < l.pts.length; i += 2) addPt(l.pts[i], l.pts[i + 1]);
    // граница района (густо)
    for (let i = 0; i < poly.length; i++) {
        const a = poly[i], b = poly[(i + 1) % poly.length], L = Math.hypot(b[0] - a[0], b[1] - a[1]);
        const m = Math.max(1, Math.ceil(L / 6));
        for (let k = 0; k <= m; k++) addPt(a[0] + (b[0] - a[0]) * k / m, a[1] + (b[1] - a[1]) * k / m);
    }
    // парки
    for (const pk of d.fin.parksV) for (const q of pk.poly) addPt(q[0], q[1]);
    // бокс дистанция
    const halfDiag = Math.hypot(bb[2] - bb[0], bb[3] - bb[1]) * .5;
    const R = Math.ceil(halfDiag / step) + 1;
    const MAXB = 2400;
    const out = [];
    for (let iu = -R; iu <= R && out.length < MAXB; iu++) {
        for (let iv = -R; iv <= R && out.length < MAXB; iv++) {
            if (rng() > density + 0.03) continue;
            const u = iu * step + (rng() - .5) * step * spec.jitter;
            const v = iv * step + (rng() - .5) * step * spec.jitter;
            const x = c[0] + u * ca - v * sa;
            const y = c[1] + u * sa + v * ca;
            if (x < bb[0] - step || x > bb[2] + step || y < bb[1] - step || y > bb[3] + step) continue;
            if (!pip(x, y, poly)) continue;
            // не в воде / не на реке / не в горах
            if (S.waterAt(x, y) > 0.5 || S.heightAt(x, y) > 0.6 || S.inRiver(x, y)) continue;
            // отступ от границы района
            if (distPoly(x, y, poly) < sep * .35) continue;
            // не в парке
            let inPark = false;
            for (const pk of d.fin.parksV) {
                if (x >= pk.bb[0] - 5 && x <= pk.bb[2] + 5 && y >= pk.bb[1] - 5 && y <= pk.bb[3] + 5 && pip(x, y, pk.poly)) {
                    inPark = true;
                    break;
                }
            }
            if (inPark) continue;
            // размеры здания
            const bw = sep * spec.w * rrange(rng, .78, 1.25);
            const bh = sep * spec.h * rrange(rng, .78, 1.25);
            const reach = Math.hypot(bw, bh) * .5 + sep * .10;
            // проверка расстояния до всего «чужого»
            if (grid.nearest(x, y, reach + minClear * .5)) continue;
            const ang = spec.keepAligned ? d.angle + (rng() - .5) * spec.varAng : (rng() - .5) * TAU;
            out.push([x, y, bw, bh, ang]);
            // положить в общую сетку — грубо как круг вокруг центра
            const rr = Math.max(bw, bh) * .5;
            addPt(x, y);
            // добавить углы как точки для лучшего покрытия
            const ca2 = Math.cos(ang), sa2 = Math.sin(ang), hw = bw / 2, hh = bh / 2;
            for (const [ox, oy] of [[-hw, -hh], [hw, -hh], [hw, hh], [-hw, hh]]) addPt(x + ox * ca2 - oy * sa2, y + ox * sa2 + oy * ca2);
        }
    }
    d.fin.buildings = out;
    // Path2D со всеми прямоугольниками
    const P = new Path2D();
    for (const [x, y, w, h, a] of out) {
        const ca2 = Math.cos(a), sa2 = Math.sin(a), hw = w / 2, hh = h / 2;
        P.moveTo(x + (-hw * ca2 - -hh * sa2), y + (-hw * sa2 + -hh * ca2));
        P.lineTo(x + (hw * ca2 - -hh * sa2), y + (hw * sa2 + -hh * ca2));
        P.lineTo(x + (hw * ca2 - hh * sa2), y + (hw * sa2 + hh * ca2));
        P.lineTo(x + (-hw * ca2 - hh * sa2), y + (-hw * sa2 + hh * ca2));
        P.closePath();
    }
    d.fin.buildPath = P;
}

function rebuildBuildings(S, d) {
    finalizeAll(S);
}

function finDistrict(S, d, idx) {
    if (!S._bg) S._bg = new PGrid(Math.max(6, (d.sep || 12) * 0.25));
    const fin = d.fin = {
        groups: {},
        lines: [],
        park: null,
        tint: null,
        bound: null,
        parksV: [],
        buildings: [],
        buildPath: null
    };
    const poly = d.poly, tint = new Path2D();
    tint.moveTo(poly[0][0], poly[0][1]);
    for (let i = 1; i < poly.length; i++) tint.lineTo(poly[i][0], poly[i][1]);
    tint.closePath();
    fin.tint = tint;
    const raw = d.raw;
    if (!raw) return;
    const later = [];
    for (let k = idx + 1; k < S.districts.length; k++) later.push({poly: S.districts[k].poly, bb: S.districts[k]._bb});
    const terrainOk = (x, y) => S.waterAt(x, y) <= 0.5 && S.heightAt(x, y) <= 0.6 && !S.inRiver(x, y);
    const pv = raw.parks.filter(pk => terrainOk(pk.c[0], pk.c[1]) && !later.some(o => pk.c[0] >= o.bb[0] && pk.c[0] <= o.bb[2] && pk.c[1] >= o.bb[1] && pk.c[1] <= o.bb[3] && pip(pk.c[0], pk.c[1], o.poly)));
    fin.parksV = pv;
    const hard = (x, y) => {
        if (!terrainOk(x, y)) return false;
        for (let i = 0; i < pv.length; i++) {
            const pk = pv[i];
            if (x >= pk.bb[0] && x <= pk.bb[2] && y >= pk.bb[1] && y <= pk.bb[3] && pip(x, y, pk.poly)) return false;
        }
        for (let i = 0; i < later.length; i++) {
            const o = later[i];
            if (x >= o.bb[0] && x <= o.bb[2] && y >= o.bb[1] && y <= o.bb[3] && pip(x, y, o.poly)) return false;
        }
        return true;
    };
    const flags = edgeFlags(S, d, idx);
    fin.edgeFree = flags;
    let soft = null;
    if (d.ragged > 0.01) {
        const segs = [];
        for (let i = 0; i < poly.length; i++) if (flags[i]) {
            const a = poly[i], b = poly[(i + 1) % poly.length];
            segs.push(a[0], a[1], b[0], b[1]);
        }
        const B = 25 + 150 * d.ragged, ox = (d.seed % 331) * 1.3, oy = (d.seed % 173) * 2.1;
        if (segs.length) soft = (x, y) => {
            let m = 1e9;
            for (let i = 0; i < segs.length; i += 4) {
                const dd = distSeg(x, y, segs[i], segs[i + 1], segs[i + 2], segs[i + 3]);
                if (dd < m) m = dd;
            }
            if (m >= B) return true;
            const thr = Math.pow(1 - m / B, 0.8) * d.ragged * 1.05;
            return !(S.noise.v2(x * 0.045 + ox, y * 0.045 + oy) < thr);
        };
    }
    const G = k => fin.groups[k] || (fin.groups[k] = new Path2D());
    const tone = (x, y) => (((Math.floor(x * 7.3) * 73856093) ^ (Math.floor(y * 5.1) * 19349663)) >>> 0) % 3;
    const runs = [];
    const doFam = (lines, key, fam, useTone) => {
        for (const pts of lines) {
            runs.length = 0;
            cutLine(pts, hard, soft, runs);
            for (const r0 of runs) {
                const r = rdp(r0, 0.35);
                if (r.length < 4) continue;
                const P = G(useTone ? key + tone(r[0], r[1]) : key);
                P.moveTo(r[0], r[1]);
                for (let i = 2; i < r.length; i += 2) P.lineTo(r[i], r[i + 1]);
                if (fam >= 0) fin.lines.push({pts: r, fam});
            }
        }
    };
    doFam(raw.A, 'a', 0, true);
    doFam(raw.B, 'b', 1, true);
    doFam(raw.al, 'al', -1, false);
    // парки
    if (pv.length) {
        const P = new Path2D();
        for (const pk of pv) blobPath(P, pk.poly);
        fin.park = P;
    }
    // границы
    const hb = (x, y) => S.waterAt(x, y) <= 0.5 && S.heightAt(x, y) <= 0.6 && !S.inRiver(x, y);
    const bp = new Path2D();
    let any = false;
    const n = poly.length;
    for (let i = 0; i < n; i++) {
        if (flags[i] && d.ragged >= 0.3) continue;
        const a = poly[i], b = poly[(i + 1) % n], L = Math.hypot(b[0] - a[0], b[1] - a[1]),
            m = Math.max(1, Math.ceil(L / 6)), dense = [];
        for (let k = 0; k <= m; k++) dense.push(a[0] + (b[0] - a[0]) * k / m, a[1] + (b[1] - a[1]) * k / m);
        runs.length = 0;
        cutLine(dense, hb, null, runs);
        for (const r of runs) {
            bp.moveTo(r[0], r[1]);
            for (let q = 2; q < r.length; q += 2) bp.lineTo(r[q], r[q + 1]);
            any = true;
        }
    }
    fin.bound = any ? bp : null;
    // --- здания ---
    genBuildings(S, d, S._bg);
}

function buildRiver(S, r) {
    const dense = catmull(r.pts, 4), n = dense.length, out = [];
    for (let i = 0; i < n; i++) {
        const t = i / (n - 1 || 1), w = r.width * (0.7 + 0.5 * t) * (0.85 + 0.3 * S.noise.v2(i * 0.07 + r.id, 3));
        out.push([dense[i][0], dense[i][1], w / 2]);
    }
    let a = 0, b = n - 1;
    while (a < n && S.waterAt(out[a][0], out[a][1]) > 0.5) a++;
    while (b > a && S.waterAt(out[b][0], out[b][1]) > 0.5) b--;
    const samp = out.slice(a, b + 1);
    r.samp = samp;
    const L = [], R = [];
    for (let i = 0; i < samp.length; i++) {
        const p0 = samp[Math.max(i - 1, 0)], p1 = samp[Math.min(i + 1, samp.length - 1)], tx = p1[0] - p0[0],
            ty = p1[1] - p0[1], l = Math.hypot(tx, ty) || 1, nx = -ty / l, ny = tx / l, hw = samp[i][2];
        L.push([samp[i][0] + nx * hw, samp[i][1] + ny * hw]);
        R.push([samp[i][0] - nx * hw, samp[i][1] - ny * hw]);
    }
    const fill = new Path2D(), banks = new Path2D();
    if (samp.length > 1) {
        fill.moveTo(L[0][0], L[0][1]);
        for (let i = 1; i < L.length; i++) fill.lineTo(L[i][0], L[i][1]);
        for (let i = R.length - 1; i >= 0; i--) fill.lineTo(R[i][0], R[i][1]);
        fill.closePath();
        banks.moveTo(L[0][0], L[0][1]);
        for (let i = 1; i < L.length; i++) banks.lineTo(L[i][0], L[i][1]);
        banks.moveTo(R[0][0], R[0][1]);
        for (let i = 1; i < R.length; i++) banks.lineTo(R[i][0], R[i][1]);
    }
    r.fill = fill;
    r.banks = banks;
    for (const s of samp) {
        const k = (Math.floor(s[0] / 24) + 64) * 4096 + (Math.floor(s[1] / 24) + 64);
        let arr = S.rb.get(k);
        if (!arr) {
            arr = [];
            S.rb.set(k, arr);
        }
        arr.push(s[0], s[1], s[2] + 3);
    }
}

function finTerrain(S) {
    const {gw, gh, cell} = S;
    S._wc = null;
    S.waterBlur = boxBlur(S.water, gw, gh, 5, 3);
    const mk = (F, level) => {
        const segs = marching(F, gw, gh, cell, level), p = new Path2D();
        for (let i = 0; i < segs.length; i += 4) {
            p.moveTo(segs[i], segs[i + 1]);
            p.lineTo(segs[i + 2], segs[i + 3]);
        }
        return {p, segs};
    };
    const c = mk(S.water, 0.5);
    S.coastPath = c.p;
    S.coastSegs = c.segs;
    S.bathyPaths = [0.62, 0.74, 0.86, 0.95].map(l => mk(S.waterBlur, l).p);
    let hmax = 0;
    for (let i = 0; i < S.height.length; i++) if (S.height[i] > hmax) hmax = S.height[i];
    S.mountMinor = new Path2D();
    S.mountMajor = new Path2D();
    S.peaks = [];
    if (hmax > 0.1) {
        let li = 0;
        for (let l = 0.1; l <= 1.0; l += 0.09, li++) {
            if (hmax <= l) break;
            const segs = marching(S.height, gw, gh, cell, l), P = (li % 3 === 2) ? S.mountMajor : S.mountMinor;
            for (let i = 0; i < segs.length; i += 4) {
                P.moveTo(segs[i], segs[i + 1]);
                P.lineTo(segs[i + 2], segs[i + 3]);
            }
        }
        const cand = [];
        for (let j = 4; j < gh - 4; j++) for (let i = 4; i < gw - 4; i++) {
            const v = S.height[j * gw + i];
            if (v < 0.7) continue;
            let ok = true;
            for (let dj = -4; dj <= 4 && ok; dj += 2) for (let di = -4; di <= 4; di += 2) if (S.height[(j + dj) * gw + i + di] > v) {
                ok = false;
                break;
            }
            if (ok) cand.push([(i + .5) * cell, (j + .5) * cell, v]);
        }
        cand.sort((a, b) => b[2] - a[2]);
        for (const c2 of cand) {
            if (S.peaks.length >= 14) break;
            if (S.peaks.every(p => Math.hypot(p[0] - c2[0], p[1] - c2[1]) > 80)) S.peaks.push(c2);
        }
    }
}

function finPiers(S) {
    const p = new Path2D(), placed = [];
    for (const d of S.districts) {
        if (d.type !== 'harbor') continue;
        const bb = bboxOf(d.poly), cs = S.coastSegs;
        for (let i = 0; i < cs.length; i += 4) {
            const mx = (cs[i] + cs[i + 2]) / 2, my = (cs[i + 1] + cs[i + 3]) / 2;
            if (mx < bb[0] - 30 || mx > bb[2] + 30 || my < bb[1] - 30 || my > bb[3] + 30) continue;
            if (!pip(mx, my, d.poly) && distPoly(mx, my, d.poly) > 18) continue;
            const nv = S.noise.v2(mx * 0.31 + 5, my * 0.31 + 9);
            if (nv < 0.62) continue;
            if (placed.some(q => Math.hypot(q[0] - mx, q[1] - my) < 26)) continue;
            const gx = S.waterAt(mx + 4, my) - S.waterAt(mx - 4, my),
                gy = S.waterAt(mx, my + 4) - S.waterAt(mx, my - 4), gl = Math.hypot(gx, gy);
            if (gl < 1e-4) continue;
            const nx = gx / gl, ny = gy / gl, len = 12 + (nv - 0.62) * 120, tx = -ny, ty = nx, ex = mx + nx * len,
                ey = my + ny * len;
            p.moveTo(mx + tx * 1.8, my + ty * 1.8);
            p.lineTo(ex + tx * 1.8, ey + ty * 1.8);
            p.moveTo(mx - tx * 1.8, my - ty * 1.8);
            p.lineTo(ex - tx * 1.8, ey - ty * 1.8);
            p.moveTo(ex + tx * 5, ey + ty * 5);
            p.lineTo(ex - tx * 5, ey - ty * 5);
            placed.push([mx, my]);
        }
    }
    S.pierPath = p;
}

function segInter(ax, ay, bx, by, cx, cy, dx, dy) {
    const r = (bx - ax) * (dy - cy) - (by - ay) * (dx - cx);
    if (Math.abs(r) < 1e-9) return null;
    const t = ((cx - ax) * (dy - cy) - (cy - ay) * (dx - cx)) / r,
        u = ((cx - ax) * (by - ay) - (cy - ay) * (bx - ax)) / r;
    if (t < 0 || t > 1 || u < 0 || u > 1) return null;
    return [ax + t * (bx - ax), ay + t * (by - ay)];
}

function finRoads(S) {
    const bridges = new Path2D();
    for (const r of S.roads) {
        r.dense = catmull(r.pts, 6);
        const P = new Path2D();
        if (r.dense.length) {
            P.moveTo(r.dense[0][0], r.dense[0][1]);
            for (let i = 1; i < r.dense.length; i++) P.lineTo(r.dense[i][0], r.dense[i][1]);
        }
        r.path = P;
        r.flat = [];
        for (const q of r.dense) r.flat.push(q[0], q[1]);
        for (const rv of S.rivers) {
            const sp = rv.samp;
            if (!sp || sp.length < 2) continue;
            for (let i = 0; i < r.dense.length - 1; i++) {
                const a = r.dense[i], b = r.dense[i + 1];
                for (let j = 0; j < sp.length - 1; j++) {
                    if (Math.abs(sp[j][0] - a[0]) > 60 || Math.abs(sp[j][1] - a[1]) > 60) continue;
                    const h = segInter(a[0], a[1], b[0], b[1], sp[j][0], sp[j][1], sp[j + 1][0], sp[j + 1][1]);
                    if (h) {
                        const dx = b[0] - a[0], dy = b[1] - a[1], l = Math.hypot(dx, dy) || 1, ux = dx / l, uy = dy / l,
                            len = sp[j][2] * 2 + 12, nx = -uy, ny = ux;
                        bridges.moveTo(h[0] - ux * len / 2, h[1] - uy * len / 2);
                        bridges.lineTo(h[0] + ux * len / 2, h[1] + uy * len / 2);
                        for (const s of [-1, 1]) {
                            const ex = h[0] + ux * s * len / 2, ey = h[1] + uy * s * len / 2;
                            bridges.moveTo(ex + nx * 4, ey + ny * 4);
                            bridges.lineTo(ex - nx * 4, ey - ny * 4);
                        }
                    }
                }
            }
        }
    }
    S.bridgePath = bridges;
}

function finFarm(S) {
    const P = new Path2D(), D = new Path2D();
    for (const f of S.farm) {
        const rng = mulberry32(f.seed), ca = Math.cos(f.ang), sa = Math.sin(f.ang),
            cols = Math.max(1, Math.round(f.w / f.cw)), rows = Math.max(1, Math.round(f.h / f.ch));
        const T = (lx, ly) => [f.x + lx * ca - ly * sa, f.y + lx * sa + ly * ca];
        for (let r = 0; r < rows; r++) for (let c = 0; c < cols; c++) {
            const lx = (c - cols / 2) * f.cw, ly = (r - rows / 2) * f.ch, g = 1.2, jx = (rng() - .5) * 3,
                jy = (rng() - .5) * 3;
            const cc = T(lx + f.cw / 2, ly + f.ch / 2);
            if (rng() < 0.1) continue;
            if (S.waterAt(cc[0], cc[1]) > 0.4 || S.heightAt(cc[0], cc[1]) > 0.4 || S.inRiver(cc[0], cc[1])) continue;
            let blocked = false;
            for (const d of S.districts) {
                const bb = d._bb;
                if (cc[0] < bb[0] - 25 || cc[0] > bb[2] + 25 || cc[1] < bb[1] - 25 || cc[1] > bb[3] + 25) continue;
                if (pip(cc[0], cc[1], d.poly) || distPoly(cc[0], cc[1], d.poly) < 22) {
                    blocked = true;
                    break;
                }
            }
            if (blocked) continue;
            const p1 = T(lx + g, ly + g), p2 = T(lx + f.cw - g + jx, ly + g),
                p3 = T(lx + f.cw - g + jx, ly + f.ch - g + jy), p4 = T(lx + g, ly + f.ch - g + jy);
            P.moveTo(p1[0], p1[1]);
            P.lineTo(p2[0], p2[1]);
            P.lineTo(p3[0], p3[1]);
            P.lineTo(p4[0], p4[1]);
            P.closePath();
            if (rng() < 0.1) {
                D.moveTo(p1[0] + 3.5, p1[1]);
                D.arc(p1[0] + 2.5, p1[1] + 2.5, 1.3, 0, TAU);
            }
        }
    }
    S.farmPath = P;
    S.farmDots = D;
}

function finalizeAll(S) {
    for (const d of S.districts) d._bb = bboxOf(d.poly);
    S.rb = new Map();
    S._bg = null;
    finTerrain(S);
    for (const r of S.rivers) buildRiver(S, r);
    for (let i = 0; i < S.districts.length; i++) finDistrict(S, S.districts[i], i);
    finRoads(S);
    finFarm(S);
    finPiers(S);
    S._bg = null;
}

function retraceDistrict(S, d) {
    d.raw = genDistrictRaw(d, S);
    computeLabel(d);
}

/* ---------- дороги, поля, значки ---------- */
function walkRoad(S, rng, x, y, ang, o) {
    const pts = [[x, y]], off = rng() * 100;
    for (let i = 0; i < o.maxLen / o.step; i++) {
        const a = ang + (S.noise.fbm(i * o.step * 0.0022 + off, o.k, 3) - .5) * o.turn * 3;
        x += Math.cos(a) * o.step;
        y += Math.sin(a) * o.step;
        if (x < -20 || y < -20 || x > S.W + 20 || y > S.H + 20) {
            pts.push([clamp(x, 0, S.W), clamp(y, 0, S.H)]);
            break;
        }
        if (S.waterAt(x, y) > 0.5 || S.heightAt(x, y) > 0.5) break;
        pts.push([x, y]);
    }
    return pts;
}

function genRoads(S, rng, P, g) {
    const c = S.center, ell = S.ell, R = (ell.rx + ell.ry) / 2, N = P.hw, pairs = Math.ceil(N / 2),
        base = rng() * Math.PI;
    let n = 1;
    const shape = (g && CITY_SHAPES[g.cityShape]) || CITY_SHAPES.round;

    // Главное шоссе вдоль длинной оси (Волгоград / линейные города)
    if (shape.spine) {
        const a = ell.rot;
        const f = walkRoad(S, rng, c[0], c[1], a, {step: 14, maxLen: 4600, turn: .12, k: 777});
        const b = walkRoad(S, rng, c[0], c[1], a + Math.PI, {step: 14, maxLen: 4600, turn: .12, k: 778});
        const line = b.slice(1).reverse().concat(f);
        if (line.length >= 6) S.roads.push({
            id: S.nextId++,
            kind: 'highway',
            pts: line,
            name: 'Главная магистраль',
            lblT: 0.5
        });
    }

    for (let k = 0; k < pairs; k++) {
        const a = base + k * (Math.PI / pairs) + (rng() - .5) * .35, jx = (rng() - .5) * R * .12,
            jy = (rng() - .5) * R * .12;
        const f = walkRoad(S, rng, c[0] + jx, c[1] + jy, a, {step: 14, maxLen: 3600, turn: .35, k});
        let line = f;
        if (!(N % 2 === 1 && k === pairs - 1)) {
            const b = walkRoad(S, rng, c[0] + jx, c[1] + jy, a + Math.PI, {
                step: 14,
                maxLen: 3600,
                turn: .35,
                k: k + 9
            });
            line = b.slice(1).reverse().concat(f);
        }
        if (line.length >= 6) S.roads.push({
            id: S.nextId++,
            kind: 'highway',
            pts: line,
            name: 'Магистраль ' + (n++),
            lblT: rrange(rng, .3, .7)
        });
    }
    if (P.ring && !shape.grid) {
        let run = [], n2 = 1;
        for (let k = 0; k <= 96; k++) {
            const a = k / 96 * TAU,
                r = 0.6 * (1 + 0.12 * (S.noise.fbm(Math.cos(a) * 1.5 + 7, Math.sin(a) * 1.5 + 3, 2) - .5));
            const ex = Math.cos(a) * ell.rx * r, ey = Math.sin(a) * ell.ry * r,
                x = c[0] + ex * Math.cos(ell.rot) - ey * Math.sin(ell.rot),
                y = c[1] + ex * Math.sin(ell.rot) + ey * Math.cos(ell.rot);
            if (S.waterAt(x, y) > 0.5 || S.heightAt(x, y) > 0.5) {
                if (run.length >= 4) S.roads.push({
                    id: S.nextId++,
                    kind: 'avenue',
                    pts: run,
                    name: 'Кольцевая ' + (n2++),
                    lblT: .5
                });
                run = [];
                continue;
            }
            run.push([x, y]);
        }
        if (run.length >= 4) S.roads.push({
            id: S.nextId++,
            kind: 'avenue',
            pts: run,
            name: 'Кольцевая ' + n2,
            lblT: .5
        });
    }
    for (let k = 0; k < P.av; k++) {
        const a = rng() * TAU,
            line = walkRoad(S, rng, c[0], c[1], a, {step: 12, maxLen: R * 1.05, turn: .3, k: k + 30});
        if (line.length >= 5) S.roads.push({
            id: S.nextId++,
            kind: 'avenue',
            pts: line,
            name: streetName(S, rng),
            lblT: rrange(rng, .35, .65)
        });
    }
    for (let k = 0; k < P.rail; k++) {
        const a = base + 1.0 + k * 1.9,
            line = walkRoad(S, rng, c[0] + Math.cos(a + 1.5) * R * .08, c[1] + Math.sin(a + 1.5) * R * .08, a, {
                step: 16,
                maxLen: 3600,
                turn: .12,
                k: k + 60
            });
        if (line.length >= 5) {
            S.roads.push({id: S.nextId++, kind: 'rail', pts: line, name: 'Линия ' + (k + 1), lblT: .6});
            S.icons.push({id: S.nextId++, type: 'station', x: line[0][0], y: line[0][1], ang: 0, size: 26});
        }
    }
}

function genFarm(S, rng, g) {
    const n = g.farm;
    let tries = 0;
    while (S.farm.length < n && tries < n * 60) {
        tries++;
        const x = rng() * S.W, y = rng() * S.H, w = rrange(rng, 90, 220), h = rrange(rng, 80, 200),
            r = Math.hypot(w, h) / 2;
        if (S.waterAt(x, y) > 0.3 || S.heightAt(x, y) > 0.3) continue;
        let dd = 1e9;
        for (const d of S.districts) {
            const v = pip(x, y, d.poly) ? 0 : distPoly(x, y, d.poly);
            if (v < dd) dd = v;
        }
        if (dd < r * 0.7 + 20) continue;
        if (S.farm.some(f => Math.hypot(f.x - x, f.y - y) < (Math.hypot(f.w, f.h) / 2 + r) * 0.72)) continue;
        let wet = false;
        for (const [ux, uy] of [[1, 1], [1, -1], [-1, 1], [-1, -1]]) if (S.waterAt(x + ux * w / 2, y + uy * h / 2) > 0.3) wet = true;
        if (wet) continue;
        S.farm.push({
            x,
            y,
            w,
            h,
            cw: rrange(rng, 14, 26),
            ch: rrange(rng, 14, 26),
            ang: rng() * Math.PI / 2,
            seed: Math.floor(rng() * 1e9)
        });
    }
}

function genIcons(S, rng, P) {
    if (!(S.seaSide || S.lake)) return;
    const c = S.center;
    const cand = [];
    for (let t = 0; t < 600; t++) {
        const x = rng() * S.W, y = rng() * S.H;
        if (S.waterAt(x, y) > 0.98 && S.deepAt(x, y) > 0.9) cand.push([x, y, Math.hypot(x - c[0], y - c[1])]);
    }
    cand.sort((a, b) => a[2] - b[2]);
    const ships = [];
    for (const q of cand) {
        if (ships.length >= P.ships) break;
        if (ships.every(s => Math.hypot(s[0] - q[0], s[1] - q[1]) > 110)) ships.push(q);
    }
    for (const s of ships) S.icons.push({id: S.nextId++, type: 'ship', x: s[0], y: s[1], ang: rng() * TAU, size: 44});
    const hb = S.districts.find(d => d.type === 'harbor');
    if (hb) {
        const bb = bboxOf(hb.poly);
        let n = 0;
        for (let t = 0; t < 400 && n < 3; t++) {
            const x = bb[0] - 60 + rng() * (bb[2] - bb[0] + 120), y = bb[1] - 60 + rng() * (bb[3] - bb[1] + 120);
            if (S.waterAt(x, y) > 0.95 && S.deepAt(x, y) > 0.7 && S.deepAt(x, y) < 0.9 && !S.icons.some(i => i.type === 'anchor' && Math.hypot(i.x - x, i.y - y) < 70)) {
                S.icons.push({id: S.nextId++, type: 'anchor', x, y, ang: 0, size: 40});
                n++;
            }
        }
    }
}

/* ---------- подписи улиц ---------- */
function pathFromLine(flat, s, len) {
    return subPath(flat, s - len / 2, s + len / 2);
}

function nearestStreet(S, x, y, maxD) {
    let best = null, bd = maxD;
    const test = (flat, tag) => {
        for (let i = 0; i < flat.length - 2; i += 2) {
            const d = distSeg(x, y, flat[i], flat[i + 1], flat[i + 2], flat[i + 3]);
            if (d < bd) {
                bd = d;
                best = {flat, i, tag};
            }
        }
    };
    for (const d of S.districts) if (d.fin) for (const l of d.fin.lines) test(l.pts, d);
    for (const r of S.roads) if (r.flat) test(r.flat, r);
    if (!best) return null;
    const f = best.flat;
    let s = 0;
    for (let i = 0; i < best.i; i += 2) s += Math.hypot(f[i + 2] - f[i], f[i + 3] - f[i + 1]);
    const a = [f[best.i], f[best.i + 1]], b = [f[best.i + 2], f[best.i + 3]],
        L = Math.hypot(b[0] - a[0], b[1] - a[1]) || 1;
    let t = clamp(((x - a[0]) * (b[0] - a[0]) + (y - a[1]) * (b[1] - a[1])) / (L * L), 0, 1);
    s += t * L;
    return {flat: f, s, total: flatLen(f), tag: best.tag};
}

function makeStreetLabel(S, hit, text, size) {
    const tw = text.length * size * 0.66 + 6;
    let path = pathFromLine(hit.flat, hit.s, tw * 1.15);
    if (path.length < 2) return null;
    if (path[path.length - 1][0] < path[0][0]) path.reverse();
    return {id: S.nextId++, kind: 'street', text, path, size};
}

function autoStreetLabels(S, rng, count) {
    const cand = [];
    for (const d of S.districts) if (d.fin) for (const l of d.fin.lines) {
        const L = flatLen(l.pts);
        if (L > 90) cand.push({flat: l.pts, L, size: clamp(d.sep * 0.55, 7, 12)});
    }
    for (const r of S.roads) if (r.flat && r.kind !== 'rail' && !r.name) cand.push({
        flat: r.flat,
        L: flatLen(r.flat),
        size: 11
    });
    const order = shuffle(rng, cand);
    let made = 0;
    const centers = [];
    for (const c of order) {
        if (made >= count) break;
        const text = streetName(S, rng), tw = text.length * c.size * 0.66 + 6, need = tw * 1.15;
        if (c.L < need + 20) continue;
        const s = rrange(rng, need / 2 + 8, c.L - need / 2 - 8), path = pathFromLine(c.flat, s, need);
        if (path.length < 2) continue;
        let bad = false;
        for (let i = 2; i < path.length; i++) {
            const a1 = Math.atan2(path[i][1] - path[i - 1][1], path[i][0] - path[i - 1][0]),
                a0 = Math.atan2(path[i - 1][1] - path[Math.max(i - 2, 0)][1], path[i - 1][0] - path[Math.max(i - 2, 0)][0]);
            let da = Math.abs(a1 - a0);
            if (da > Math.PI) da = TAU - da;
            if (da > 0.4) bad = true;
        }
        if (bad) continue;
        const mid = path[Math.floor(path.length / 2)];
        if (centers.some(q => Math.hypot(q[0] - mid[0], q[1] - mid[1]) < Math.max(70, tw * 1.4))) continue;
        if (path[path.length - 1][0] < path[0][0]) path.reverse();
        S.labels.push({id: S.nextId++, kind: 'street', text, path, size: c.size, auto: true});
        centers.push(mid);
        made++;
    }
    return made;
}

/* ---------- сборка мира ---------- */
function generateWorld(g) {
    const P = PRESETS[g.preset], seed = g.seed >>> 0, rng = mulberry32(seed);
    const S = newShell(g.preset, seed);
    S.baseSep = g.sep;
    genWater(S, rng, g);
    pickCenter(S, rng, P, g);
    genMountains(S, rng, g);
    genRivers(S, rng, g, P);
    for (const r of S.rivers) buildRiver(S, r);
    genDistricts(S, rng, g, P);
    for (const d of S.districts) d.raw = genDistrictRaw(d, S);
    genRoads(S, rng, P, g);
    genFarm(S, rng, g);
    finTerrain(S);
    genIcons(S, rng, P);
    genGreen(S, rng, g);
    genWaste(S, rng, g);
    genSpecial(S, rng, g);
    finalizeAll(S);
    S.gen = clone(g);
    return S;
}

function regenStreets(S, newSeeds) {
    const rng = mulberry32((S.seed ^ Date.now()) >>> 0);
    for (const d of S.districts) {
        if (newSeeds) {
            d.seed = Math.floor(rng() * 1e9);
            d.angle = rrange(rng, 0, Math.PI);
        }
        d.raw = genDistrictRaw(d, S);
    }
    finalizeAll(S);
}

/* ---------- снимки и сохранение ---------- */
function snapshot(S) {
    return {
        seed: S.seed,
        preset: S.preset,
        W: S.W,
        H: S.H,
        gw: S.gw,
        gh: S.gh,
        name: S.name,
        nextId: S.nextId,
        center: S.center.slice(),
        ell: clone(S.ell),
        seaSide: S.seaSide,
        lake: S.lake ? S.lake.slice() : null,
        baseSep: S.baseSep,
        totalPop: S.totalPop || 0,
        targetPop: S.targetPop || 0,
        water: Float32Array.from(S.water),
        height: Float32Array.from(S.height),
        rivers: S.rivers.map(r => ({id: r.id, name: r.name, pts: clone(r.pts), width: r.width})),
        districts: S.districts.map(d => {
            const o = {};
            for (const k in d) if (k !== 'fin' && k !== '_bb' && k !== 'raw') o[k] = (typeof d[k] === 'object' && d[k]) ? clone(d[k]) : d[k];
            o.raw = d.raw;
            return o;
        }),
        roads: S.roads.map(r => ({id: r.id, kind: r.kind, pts: clone(r.pts), name: r.name, lblT: r.lblT})),
        labels: clone(S.labels),
        icons: clone(S.icons),
        farm: clone(S.farm),
        green: (S.green || []).map(e => ({
            id: e.id,
            x: e.x,
            y: e.y,
            r: e.r,
            seed: e.seed,
            name: e.name,
            showLabel: e.showLabel
        })),
        waste: (S.waste || []).map(e => ({
            id: e.id,
            x: e.x,
            y: e.y,
            r: e.r,
            seed: e.seed,
            name: e.name,
            showLabel: e.showLabel
        })),
        pal: clone(S.pal),
        style: clone(S.style),
        layers: clone(S.layers),
        nameLib: clone(S.nameLib || NEON_LIB),
        gen: S.gen ? clone(S.gen) : null
    };
}

function restore(S, sn) {
    S.seed = sn.seed;
    S.preset = sn.preset;
    S.W = sn.W;
    S.H = sn.H;
    S.gw = sn.gw;
    S.gh = sn.gh;
    S.name = sn.name;
    S.nextId = sn.nextId;
    S.center = sn.center.slice();
    S.ell = clone(sn.ell);
    S.seaSide = sn.seaSide;
    S.lake = sn.lake ? sn.lake.slice() : null;
    S.baseSep = sn.baseSep;
    S.totalPop = sn.totalPop || 0;
    S.targetPop = sn.targetPop || 0;
    S.noise = makeNoise(S.seed);
    S.water = Float32Array.from(sn.water);
    S.height = Float32Array.from(sn.height);
    S.rivers = sn.rivers.map(r => ({id: r.id, name: r.name, pts: clone(r.pts), width: r.width}));
    S.districts = sn.districts.map(d => {
        const o = {};
        for (const k in d) o[k] = (typeof d[k] === 'object' && d[k] && k !== 'raw') ? clone(d[k]) : d[k];
        return o;
    });
    S.roads = sn.roads.map(r => ({id: r.id, kind: r.kind, pts: clone(r.pts), name: r.name, lblT: r.lblT}));
    S.labels = clone(sn.labels);
    S.icons = clone(sn.icons);
    S.farm = clone(sn.farm);
    S.pal = clone(sn.pal);
    S.style = clone(sn.style);
    S.layers = clone(sn.layers);
    if (S.layers.objectNames === undefined) S.layers.objectNames = true;
    S.nameLib = sn.nameLib ? clone(sn.nameLib) : clone(NEON_LIB);
    S.gen = sn.gen ? clone(sn.gen) : null;
    S.green = (sn.green || []).map(e => ({
        id: e.id,
        x: e.x,
        y: e.y,
        r: e.r,
        seed: e.seed,
        name: e.name,
        showLabel: e.showLabel
    }));
    S.waste = (sn.waste || []).map(e => ({
        id: e.id,
        x: e.x,
        y: e.y,
        r: e.r,
        seed: e.seed,
        name: e.name,
        showLabel: e.showLabel
    }));
    finalizeAll(S);
}

function b64FromF32(F) {
    const u = new Uint8Array(F.length);
    for (let i = 0; i < F.length; i++) u[i] = clamp(Math.round(F[i] * 255), 0, 255);
    let s = '';
    for (let i = 0; i < u.length; i += 8192) s += String.fromCharCode.apply(null, u.subarray(i, i + 8192));
    return btoa(s);
}

function f32FromB64(b, n) {
    const s = atob(b), F = new Float32Array(n);
    for (let i = 0; i < n && i < s.length; i++) F[i] = s.charCodeAt(i) / 255;
    return F;
}

function toProject(S) {
    const sn = snapshot(S);
    const o = {};
    for (const k in sn) o[k] = sn[k];
    o.water = b64FromF32(S.water);
    o.height = b64FromF32(S.height);
    o.districts = o.districts.map(d => {
        const c = Object.assign({}, d);
        delete c.raw;
        return c;
    });
    o.format = 'neon-city-1';
    return o;
}

function fromProject(o) {
    const S = newShell(o.preset in PRESETS ? o.preset : 'city', o.seed);
    const sn = Object.assign({}, o);
    sn.water = f32FromB64(o.water, o.gw * o.gh);
    sn.height = f32FromB64(o.height, o.gw * o.gh);
    sn.districts = o.districts.map(d => Object.assign({}, d));
    S.rb = new Map();
    restoreNoFin(S, sn);
    return S;
}

function restoreNoFin(S, sn) {
    S.seed = sn.seed;
    S.preset = sn.preset;
    S.W = sn.W;
    S.H = sn.H;
    S.gw = sn.gw;
    S.gh = sn.gh;
    S.name = sn.name;
    S.nextId = sn.nextId;
    S.center = sn.center;
    S.ell = sn.ell;
    S.seaSide = sn.seaSide;
    S.lake = sn.lake;
    S.baseSep = sn.baseSep;
    S.noise = makeNoise(S.seed);
    S.water = sn.water;
    S.height = sn.height;
    S.rivers = sn.rivers;
    S.districts = sn.districts;
    S.roads = sn.roads;
    S.labels = sn.labels;
    S.icons = sn.icons;
    S.farm = sn.farm;
    S.green = (sn.green || []).map(e => ({
        id: e.id,
        x: e.x,
        y: e.y,
        r: e.r,
        seed: e.seed,
        name: e.name,
        showLabel: e.showLabel
    }));
    S.waste = (sn.waste || []).map(e => ({
        id: e.id,
        x: e.x,
        y: e.y,
        r: e.r,
        seed: e.seed,
        name: e.name,
        showLabel: e.showLabel
    }));
    S.totalPop = sn.totalPop || 0;
    S.targetPop = sn.targetPop || 0;
    S.pal = sn.pal;
    S.style = Object.assign(defaultStyle(), sn.style);
    S.layers = Object.assign(defaultLayers(), sn.layers);
    if (S.layers.objectNames === undefined) S.layers.objectNames = true;
    S.nameLib = sn.nameLib ? clone(sn.nameLib) : clone(NEON_LIB);
    S.gen = sn.gen;
    for (const d of S.districts) if (!d.raw) d.raw = genDistrictRaw(d, S);
    finalizeAll(S);
}

/* =====================================================================
    ОТРИСОВКА
    ===================================================================== */
const ICONS = {};

function iconPath(type) {
    if (ICONS[type]) return ICONS[type];
    const P = new Path2D();
    if (type === 'anchor') {
        P.moveTo(.07, -.36);
        P.arc(0, -.36, .07, 0, TAU);
        P.moveTo(0, -.29);
        P.lineTo(0, .4);
        P.moveTo(-.2, -.17);
        P.lineTo(.2, -.17);
        P.moveTo(-.36, .1);
        P.quadraticCurveTo(-.3, .42, 0, .4);
        P.quadraticCurveTo(.3, .42, .36, .1);
        P.moveTo(-.36, .1);
        P.lineTo(-.28, .16);
        P.moveTo(.36, .1);
        P.lineTo(.28, .16);
    } else if (type === 'ship') {
        P.moveTo(0, -.5);
        P.lineTo(.13, -.15);
        P.lineTo(.13, .42);
        P.lineTo(-.13, .42);
        P.lineTo(-.13, -.15);
        P.closePath();
        P.moveTo(-.07, .02);
        P.lineTo(.07, .02);
        P.lineTo(.07, .24);
        P.lineTo(-.07, .24);
        P.closePath();
    } else if (type === 'poi') {
        P.moveTo(0, -.4);
        P.lineTo(.3, 0);
        P.lineTo(0, .4);
        P.lineTo(-.3, 0);
        P.closePath();
        P.moveTo(.06, 0);
        P.arc(0, 0, .06, 0, TAU);
    } else if (type === 'tower') {
        P.moveTo(0, -.45);
        P.lineTo(.13, .42);
        P.lineTo(-.13, .42);
        P.closePath();
        P.moveTo(-.09, .1);
        P.lineTo(.09, .1);
        P.moveTo(-.05, -.18);
        P.lineTo(.05, -.18);
        P.moveTo(.2, -.35);
        P.quadraticCurveTo(.3, -.45, .2, -.55);
        P.moveTo(-.2, -.35);
        P.quadraticCurveTo(-.3, -.45, -.2, -.55);
    } else if (type === 'monument') {
        // обелиск/стела
        P.moveTo(-.13, -.36);
        P.lineTo(.13, -.36);
        P.lineTo(.09, -.46);
        P.lineTo(-.09, -.46);
        P.closePath();
        P.moveTo(-.06, -.36);
        P.lineTo(-.06, .34);
        P.lineTo(.06, .34);
        P.lineTo(.06, -.36);
        P.closePath();
        P.moveTo(-.2, .34);
        P.lineTo(.2, .34);
        P.lineTo(.16, .46);
        P.lineTo(-.16, .46);
        P.closePath();
    } else if (type === 'capitol') {
        // купол с крыльями
        P.moveTo(-.44, .38);
        P.lineTo(-.44, .02);
        P.lineTo(.44, .02);
        P.lineTo(.44, .38);
        P.closePath();
        P.moveTo(-.3, .02);
        P.lineTo(-.3, -.08);
        P.lineTo(.3, -.08);
        P.lineTo(.3, .02);
        P.closePath();
        P.moveTo(-.2, -.08);
        P.quadraticCurveTo(0, -.38, .2, -.08);
        P.moveTo(-.02, -.38);
        P.lineTo(.02, -.38);
        P.lineTo(.02, -.5);
        P.lineTo(-.02, -.5);
        P.closePath();
        P.moveTo(-.48, .38);
        P.lineTo(.48, .38);
    } else if (type === 'gov') {
        // правительственное здание с колоннами
        P.moveTo(-.38, .4);
        P.lineTo(-.38, .05);
        P.lineTo(.38, .05);
        P.lineTo(.38, .4);
        P.closePath();
        P.moveTo(-.44, .05);
        P.lineTo(.44, .05);
        P.lineTo(.38, -.02);
        P.lineTo(-.38, -.02);
        P.closePath();
        P.moveTo(-.08, -.02);
        P.lineTo(-.08, -.18);
        P.lineTo(.08, -.18);
        P.lineTo(.08, -.02);
        P.closePath();
        P.moveTo(-.28, .4);
        P.lineTo(-.28, .1);
        P.moveTo(-.14, .4);
        P.lineTo(-.14, .1);
        P.moveTo(.14, .4);
        P.lineTo(.14, .1);
        P.moveTo(.28, .4);
        P.lineTo(.28, .1);
        P.moveTo(-.44, .4);
        P.lineTo(.44, .4);
    } else if (type === 'temple') {
        // храм со шпилем
        P.moveTo(-.32, .42);
        P.lineTo(-.32, .08);
        P.lineTo(.32, .08);
        P.lineTo(.32, .42);
        P.closePath();
        P.moveTo(-.4, .08);
        P.lineTo(.4, .08);
        P.lineTo(.34, -.02);
        P.lineTo(-.34, -.02);
        P.closePath();
        P.moveTo(0, -.02);
        P.lineTo(0, -.3);
        P.moveTo(-.09, -.3);
        P.lineTo(.09, -.3);
        P.lineTo(0, -.46);
        P.closePath();
        P.moveTo(-.05, -.18);
        P.lineTo(.05, -.18);
        P.moveTo(0, -.24);
        P.lineTo(0, -.12);
    } else if (type === 'stadium') {
        // овал стадиона
        P.ellipse(0, 0, .48, .42, 0, 0, TAU);
        P.moveTo(.28, 0);
        P.ellipse(0, 0, .28, .24, 0, 0, TAU);
        P.moveTo(-.62, 0);
        P.lineTo(-.48, 0);
        P.moveTo(.62, 0);
        P.lineTo(.48, 0);
    } else if (type === 'landmark') {
        // звезда
        P.moveTo(0, -.5);
        P.lineTo(.13, -.14);
        P.lineTo(.5, -.1);
        P.lineTo(.22, .16);
        P.lineTo(.3, .5);
        P.lineTo(0, .3);
        P.lineTo(-.3, .5);
        P.lineTo(-.22, .16);
        P.lineTo(-.5, -.1);
        P.lineTo(-.13, -.14);
        P.closePath();
    } else { // station
        P.moveTo(.32, 0);
        P.arc(0, 0, .32, 0, TAU);
        P.moveTo(.12, 0);
        P.arc(0, 0, .12, 0, TAU);
    }
    return ICONS[type] = P;
}

const ICON_NAMES = {
    anchor: 'Якорь',
    ship: 'Корабль',
    poi: 'Точка интереса',
    tower: 'Вышка',
    station: 'Станция',
    monument: 'Монумент',
    capitol: 'Капитолий',
    gov: 'Правительство',
    temple: 'Храм',
    stadium: 'Стадион',
    landmark: 'Достопримечательность'
};
const ICON_SIZES = {
    anchor: 40, ship: 44, poi: 26, tower: 34, station: 26,
    monument: 40, capitol: 100, gov: 52, temple: 44, stadium: 76, landmark: 32
};
const SPECIAL_ICONS = {monument: 1, capitol: 1, gov: 1, temple: 1, stadium: 1, landmark: 1};

const _wcache = new Map();

function charW(ctx, ch) {
    const k = ctx.font + '|' + ch;
    let w = _wcache.get(k);
    if (w === undefined) {
        w = ctx.measureText(ch).width;
        _wcache.set(k, w);
    }
    return w;
}

function textOnPath(ctx, text, pts, size, o) {
    if (pts.length < 2) return;
    ctx.font = (o.weight || 600) + ' ' + size + 'px "' + o.family + '", sans-serif';
    ctx.textBaseline = 'middle';
    const chars = Array.from(text), sp = size * (o.spacing || 0);
    const ws = chars.map(ch => charW(ctx, ch));
    const total = ws.reduce((a, b) => a + b, 0) + sp * (chars.length - 1);
    const cum = [0];
    for (let i = 1; i < pts.length; i++) cum.push(cum[i - 1] + Math.hypot(pts[i][0] - pts[i - 1][0], pts[i][1] - pts[i - 1][1]));
    const Lp = cum[cum.length - 1];
    if (Lp <= 0) return;
    const at = s => {
        let i = 1;
        if (s <= 0) i = 1; else if (s >= Lp) i = pts.length - 1; else {
            while (i < pts.length - 1 && cum[i] < s) i++;
        }
        const a = pts[i - 1], b = pts[i], l = cum[i] - cum[i - 1] || 1, t = (s - cum[i - 1]) / l;
        return [a[0] + (b[0] - a[0]) * t, a[1] + (b[1] - a[1]) * t, Math.atan2(b[1] - a[1], b[0] - a[0])];
    };
    let s = (Lp - total) / 2;
    ctx.lineJoin = 'round';
    for (let i = 0; i < chars.length; i++) {
        const w = ws[i], q = at(s + w / 2);
        ctx.save();
        ctx.translate(q[0], q[1]);
        ctx.rotate(q[2]);
        if (o.halo) {
            ctx.strokeStyle = o.halo;
            ctx.globalAlpha = 0.85;
            ctx.lineWidth = size * 0.3;
            ctx.strokeText(chars[i], -w / 2, 0);
        }
        ctx.globalAlpha = 1;
        ctx.fillStyle = o.color;
        ctx.fillText(chars[i], -w / 2, 0);
        ctx.restore();
        s += w + sp;
    }
}

function textWidth(ctx, text, size, family, spacing, weight) {
    ctx.font = (weight || 600) + ' ' + size + 'px "' + family + '", sans-serif';
    let t = 0;
    const ch = Array.from(text);
    for (const c of ch) t += charW(ctx, c);
    return t + size * (spacing || 0) * (ch.length - 1);
}

function buildWaterBitmap(S) {
    const c = document.createElement('canvas');
    c.width = S.gw;
    c.height = S.gh;
    const x = c.getContext('2d'), img = x.createImageData(S.gw, S.gh), [r, g, b] = hex2rgb(S.pal.water);
    for (let i = 0; i < S.water.length; i++) {
        const w = smoothstep(0.42, 0.58, S.water[i]), bl = S.waterBlur ? S.waterBlur[i] : 1;
        img.data[i * 4] = r;
        img.data[i * 4 + 1] = g;
        img.data[i * 4 + 2] = b;
        img.data[i * 4 + 3] = Math.round(255 * w * (0.35 + 0.65 * bl) * 0.55);
    }
    x.putImageData(img, 0, 0);
    S._wc = c;
}

let _grain = null;

function grainTile() {
    if (_grain) return _grain;
    const c = document.createElement('canvas');
    c.width = c.height = 128;
    const x = c.getContext('2d'), im = x.createImageData(128, 128);
    for (let i = 0; i < 128 * 128; i++) {
        const v = Math.random() * 255;
        im.data[i * 4] = im.data[i * 4 + 1] = im.data[i * 4 + 2] = v;
        im.data[i * 4 + 3] = 255;
    }
    x.putImageData(im, 0, 0);
    return _grain = c;
}

const dcol = (S, d) => d.color || S.pal.types[d.type] || '#ffffff';
const _coreCache = new Map();

function core(c) {
    let v = _coreCache.get(c);
    if (!v) {
        v = mixHex(c, '#ffffff', 0.28);
        _coreCache.set(c, v);
    }
    return v;
}

/* ---------- объектные блобы (парки, свалки) ---------- */
function blobEntityPath(e) {
    const rng = mulberry32((e.seed >>> 0) ^ 0x9E3779B9);
    const P = new Path2D();
    const N = 12, pts = [];
    for (let i = 0; i < N; i++) {
        const a = i / N * TAU;
        const rr = e.r * (0.68 + 0.55 * rng());
        pts.push([e.x + Math.cos(a) * rr, e.y + Math.sin(a) * rr]);
    }
    const mid = (a, b) => [(a[0] + b[0]) / 2, (a[1] + b[1]) / 2];
    const m0 = mid(pts[N - 1], pts[0]);
    P.moveTo(m0[0], m0[1]);
    for (let i = 0; i < N; i++) {
        const a = pts[i], b = pts[(i + 1) % N], m = mid(a, b);
        P.quadraticCurveTo(a[0], a[1], m[0], m[1]);
    }
    P.closePath();
    return P;
}

function addBlobEntity(S, x, y, kind, rng) {
    const list = kind === 'waste' ? S.waste : S.green;
    const baseR = kind === 'waste' ? 32 : 34;
    const r = baseR * (0.7 + 0.7 * rng());
    list.push({id: S.nextId++, x, y, r, seed: Math.floor(rng() * 1e9)});
}

function renderScene(ctx, S, v, o) {
    o = o || {};
    const pal = S.pal, st = S.style, LY = S.layers, fast = !!o.fast;
    const sCss = v.s / v.pxk, lwk = Math.pow(sCss / 0.34, 0.55) * st.line, additive = luminance(pal.bg) < 0.3,
        glow = fast ? 0 : st.glow, W = S.W, H = S.H;
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    ctx.globalCompositeOperation = 'source-over';
    ctx.globalAlpha = 1;
    ctx.setLineDash([]);
    if (o.transparent) ctx.clearRect(0, 0, v.w, v.h); else {
        ctx.fillStyle = pal.bg;
        ctx.fillRect(0, 0, v.w, v.h);
    }
    ctx.setTransform(v.s, 0, 0, v.s, v.tx, v.ty);
    ctx.save();
    ctx.beginPath();
    ctx.rect(0, 0, W, H);
    ctx.clip();
    if (!o.transparent) {
        const g = ctx.createRadialGradient(S.center[0], S.center[1], 0, S.center[0], S.center[1], Math.max(W, H) * .7);
        g.addColorStop(0, mixHex(pal.bg, pal.types.center, .07));
        g.addColorStop(1, pal.bg);
        ctx.fillStyle = g;
        ctx.fillRect(0, 0, W, H);
    }
    const lw = b => b * lwk * v.pxk / v.s;
    ctx.lineCap = 'round';
    ctx.lineJoin = 'round';
    const neon = (path, color, wb, alpha, noGlow) => {
        if (!path) return;
        const w = lw(wb);
        if (glow > 0 && !noGlow) {
            ctx.strokeStyle = color;
            ctx.lineWidth = w * 5;
            ctx.globalAlpha = alpha * .05 * glow;
            ctx.stroke(path);
            ctx.lineWidth = w * 2.5;
            ctx.globalAlpha = alpha * .13 * glow;
            ctx.stroke(path);
        }
        ctx.strokeStyle = additive ? core(color) : color;
        ctx.lineWidth = w;
        ctx.globalAlpha = alpha;
        ctx.stroke(path);
    };
    const ADD = () => {
        ctx.globalCompositeOperation = additive ? 'lighter' : 'source-over';
    }, NRM = () => {
        ctx.globalCompositeOperation = 'source-over';
        ctx.globalAlpha = 1;
    };
    // поля
    if (LY.farm && S.farmPath) {
        ADD();
        ctx.lineJoin = 'miter';
        neon(S.farmPath, pal.farm, .7, .65, true);
        ctx.lineJoin = 'round';
        ctx.globalAlpha = .85;
        ctx.fillStyle = pal.farmDot;
        ctx.fill(S.farmDots);
        NRM();
    }
    // свалки (под тонировкой районов, чтобы выглядели «землёй»)
    if (LY.waste && S.waste.length) {
        const c = mixHex(pal.types.slums, '#2a1a0a', 0.45);
        ctx.globalAlpha = 0.42;
        ctx.fillStyle = c;
        for (const e of S.waste) {
            if (!e.path) e.path = blobEntityPath(e);
            ctx.fill(e.path);
        }
        ctx.globalAlpha = 0.65;
        ctx.strokeStyle = c;
        ctx.lineWidth = lw(0.6);
        for (const e of S.waste) ctx.stroke(e.path);
        ctx.globalAlpha = 1;
    }
    // тонировка районов
    for (const d of S.districts) {
        if (!d.fin) continue;
        ctx.globalAlpha = st.tint * (d.type === 'park' ? 2.2 : 1);
        ctx.fillStyle = dcol(S, d);
        ctx.fill(d.fin.tint);
    }
    ctx.globalAlpha = 1;
    // парки
    if (LY.parks) for (const d of S.districts) {
        if (!d.fin || !d.fin.park) continue;
        const c = pal.types.park;
        ctx.globalAlpha = .2;
        ctx.fillStyle = c;
        ctx.fill(d.fin.park);
        ADD();
        neon(d.fin.park, c, .8, .7, true);
        NRM();
    }
    // вода
    if (LY.water) {
        if (!S._wc && typeof document !== 'undefined') buildWaterBitmap(S);
        if (S._wc) {
            ctx.imageSmoothingEnabled = true;
            ctx.imageSmoothingQuality = 'high';
            ctx.globalAlpha = 1;
            ctx.drawImage(S._wc, 0, 0, S.gw * S.cell, S.gh * S.cell);
        }
        ADD();
        if (!fast) S.bathyPaths.forEach((p, i) => neon(p, pal.bathy, .6, .6 - i * .11, true));
        neon(S.coastPath, pal.coast, 1.6, 1);
        neon(S.pierPath, pal.types.harbor, 1.1, .9, true);
        NRM();
    }
    // горы
    if (LY.mountains && S.peaks) {
        ADD();
        neon(S.mountMinor, pal.mountain, .6, .5, true);
        neon(S.mountMajor, pal.mountain, 1.0, .85, false);
        if (S.peaks.length) {
            const P = new Path2D();
            for (const p of S.peaks) {
                P.moveTo(p[0] - 9, p[1] + 6);
                P.lineTo(p[0], p[1] - 9);
                P.lineTo(p[0] + 9, p[1] + 6);
            }
            neon(P, pal.mountain, 1.2, .9, true);
        }
        NRM();
    }
// реки
    if (LY.rivers) {
        for (const r of S.rivers) {
            if (!r.fill) continue;
            ctx.globalAlpha = .2;
            ctx.fillStyle = pal.river;
            ctx.fill(r.fill);
        }
        ADD();
        for (const r of S.rivers) neon(r.banks, pal.river, 1.3, .95);
        NRM();
    }
    // здания
    if (LY.buildings) {
        ADD();
        for (const d of S.districts) {
            if (!d.fin || !d.fin.buildPath) continue;
            const col = dcol(S, d);
            ctx.globalAlpha = 0.35;
            ctx.fillStyle = mixHex(pal.bg, col, 0.35);
            ctx.fill(d.fin.buildPath);
            ctx.globalAlpha = 0.65;
            ctx.strokeStyle = additive ? core(col) : col;
            ctx.lineWidth = lw(0.42);
            ctx.stroke(d.fin.buildPath);
        }
        NRM();
    }
    // зелёные зоны (парки, скверы, бульвары)
    if (LY.parks && S.green.length) {
        const c = pal.types.park;
        ADD();
        ctx.globalAlpha = 0.22;
        ctx.fillStyle = c;
        for (const e of S.green) {
            if (!e.path) e.path = blobEntityPath(e);
            ctx.fill(e.path);
        }
        for (const e of S.green) neon(e.path, c, 0.85, 0.75, true);
        NRM();
    }
    // улицы
    if (LY.streets) {
        ADD();
        const TA = [.42, .68, .95];
        for (const d of S.districts) {
            if (!d.fin) continue;
            const c = dcol(S, d), G = d.fin.groups;
            for (let t = 0; t < 3; t++) {
                if (G['a' + t]) neon(G['a' + t], c, 1.05, TA[t], t < 2);
                if (G['b' + t]) neon(G['b' + t], c, .85, TA[t] * .92, t < 2);
            }
            if (!fast && G.al) neon(G.al, c, .55, .4, true);
        }
        NRM();
    }
    // границы
    if (LY.boundaries) {
        ADD();
        for (const d of S.districts) if (d.fin && d.fin.bound) neon(d.fin.bound, mixHex(dcol(S, d), '#ffffff', .4), 1.3, .85);
        NRM();
    }
    // дороги
    if (LY.roads || LY.rails) {
        ADD();
        const order = ['street', 'avenue', 'highway'],
            cw = {street: [pal.street, 1.3], avenue: [pal.avenue, 1.9], highway: [pal.highway, 2.6]};
        if (LY.roads) for (const k of order) for (const r of S.roads) if (r.kind === k && r.path) neon(r.path, cw[k][0], cw[k][1], k === 'street' ? .85 : 1, k === 'street');
        if (LY.rails) for (const r of S.roads) if (r.kind === 'rail' && r.path) {
            ctx.strokeStyle = pal.rail;
            ctx.lineCap = 'butt';
            ctx.lineWidth = lw(3.4);
            ctx.setLineDash([lw(1.2), lw(3.6)]);
            ctx.globalAlpha = .75;
            ctx.stroke(r.path);
            ctx.setLineDash([]);
            ctx.lineCap = 'round';
            neon(r.path, pal.rail, 1, .85, true);
        }
        if (S.bridgePath) neon(S.bridgePath, pal.highway, 2.4, .8, true);
        NRM();
    }
    // значки
    if (LY.icons) {
        for (const ic of S.icons) {
            const col = ic.type === 'ship' ? pal.ship : ((SPECIAL_ICONS[ic.type] || ic.type === 'poi') ? pal.highway : pal.icon),
                sz = ic.size || ICON_SIZES[ic.type] || 30;
            ctx.save();
            ctx.translate(ic.x, ic.y);
            ctx.rotate(ic.ang || 0);
            ctx.scale(sz, sz);
            ADD();
            const w = lw(1.5) / sz;
            ctx.strokeStyle = col;
            if (glow > 0) {
                ctx.lineWidth = w * 3.5;
                ctx.globalAlpha = .12 * glow;
                ctx.stroke(iconPath(ic.type));
            }
            ctx.lineWidth = w;
            ctx.globalAlpha = .95;
            ctx.stroke(iconPath(ic.type));
            NRM();
            ctx.restore();
        }
    }
    // подписи
    NRM();
    const fam = st.labelFont || 'Exo 2', halo = pal.bg, lsz = st.labelScale;
    if (LY.districtNames) for (const d of S.districts) {
        if (d.showLabel === false || !d.lbl) continue;
        const size = d.lbl.size * lsz * (d.lblScale || 1);
        if (size * sCss < 7) continue;
        const c = d.lblPos || [d.lbl.x, d.lbl.y], a = d.lblAng !== undefined ? d.lblAng : d.lbl.ang,
            text = d.name.toUpperCase(), wd = textWidth(ctx, text, size, fam, .22, 700);
        const hl = wd * .6 + 20,
            path = [[c[0] - Math.cos(a) * hl, c[1] - Math.sin(a) * hl], [c[0] + Math.cos(a) * hl, c[1] + Math.sin(a) * hl]];
        if (!fast && glow > 0) {
            ctx.shadowColor = pal.label;
            ctx.shadowBlur = size * sCss * v.pxk * .35 * glow;
        }
        textOnPath(ctx, text, path, size, {color: pal.label, halo, family: fam, spacing: .22, weight: 700});
        ctx.shadowBlur = 0;
        ctx.shadowColor = 'transparent';
    }
    if (LY.streetNames) for (const l of S.labels) {
        if (l.kind === 'street') {
            const size = l.size * lsz;
            if (size * sCss < 5) continue;
            textOnPath(ctx, l.text, l.path, size, {
                color: pal.labelStreet,
                halo,
                family: fam,
                spacing: .06,
                weight: 600
            });
        } else if (l.kind === 'point') {
            const size = l.size * lsz;
            if (size * sCss < 5) continue;
            const hl = l.text.length * size * .5 + 10, a = l.ang || 0;
            textOnPath(ctx, l.text, [[l.x - Math.cos(a) * hl, l.y - Math.sin(a) * hl], [l.x + Math.cos(a) * hl, l.y + Math.sin(a) * hl]], size, {
                color: pal.label,
                halo,
                family: fam,
                spacing: .08,
                weight: 600
            });
        }
    }
    if (LY.roadNames) for (const r of S.roads) {
        if (!r.name || !r.flat || r.flat.length < 4) continue;
        const size = (r.kind === 'highway' ? 12 : 9.5) * lsz;
        if (size * sCss < 5) continue;
        const tw = textWidth(ctx, r.name, size, fam, .08, 600) + 6, L = flatLen(r.flat);
        if (L < tw * 1.2) continue;
        const path = subPath(r.flat, (r.lblT || .5) * L - tw * .6, (r.lblT || .5) * L + tw * .6);
        if (path.length < 2) continue;
        if (path[path.length - 1][0] < path[0][0]) path.reverse();
        textOnPath(ctx, r.name, path, size, {
            color: r.kind === 'rail' ? pal.rail : pal.labelStreet,
            halo,
            family: fam,
            spacing: .08,
            weight: 600
        });
    }
    // подписи объектов: парки, свалки, особые здания
    if (LY.objectNames) {
        const size = 9 * lsz;
        if (size * sCss > 4) {
            // Парки и свалки
            for (const list of [S.green, S.waste]) for (const e of list) {
                if (!e.name || e.showLabel === false) continue;
                textOnPath(ctx, e.name, [[e.x, e.y - e.r * 0.1], [e.x + e.name.length * size * .5, e.y - e.r * 0.1]], size, {
                    color: list === S.green ? pal.types.park : pal.highway,
                    halo,
                    family: fam,
                    spacing: .06,
                    weight: 600
                });
            }
            // Особые здания
            for (const ic of S.icons) {
                if (!SPECIAL_ICONS[ic.type] || !ic.name || ic.showLabel === false) continue;
                const hl = ic.name.length * size * .5 + 8, yOff = -(ic.size || 40) * .62;
                textOnPath(ctx, ic.name, [[ic.x - hl, ic.y + yOff], [ic.x + hl, ic.y + yOff]], size, {
                    color: pal.highway,
                    halo,
                    family: fam,
                    spacing: .06,
                    weight: 600
                });
            }
        }
    }
    ctx.restore();
    // рамка карты
    ctx.globalAlpha = .4;
    ctx.strokeStyle = pal.coast;
    ctx.lineWidth = lw(1.2);
    ctx.strokeRect(0, 0, W, H);
    ctx.globalAlpha = 1;
    // пост-эффекты
    ctx.setTransform(1, 0, 0, 1, 0, 0);
    if (!fast && !o.noPost && !o.transparent) {
        if (st.vignette > 0) {
            const cx = v.gw / 2 - v.gx, cy = v.gh / 2 - v.gy, r = Math.hypot(v.gw, v.gh) / 2,
                g = ctx.createRadialGradient(cx, cy, r * .35, cx, cy, r);
            g.addColorStop(0, 'rgba(0,0,0,0)');
            g.addColorStop(1, 'rgba(0,0,0,' + (.75 * st.vignette) + ')');
            ctx.fillStyle = g;
            ctx.fillRect(0, 0, v.w, v.h);
        }
        if (st.scan > 0) {
            ctx.fillStyle = 'rgba(0,0,0,' + (.22 * st.scan) + ')';
            const per = Math.max(3, Math.round(3 * v.pxk)), th = Math.max(1, Math.round(per / 3));
            for (let y = (per - (v.gy % per)) % per; y < v.h; y += per) ctx.fillRect(0, y, v.w, th);
        }
        if (st.grain > 0 && typeof document !== 'undefined') {
            const k = Math.max(1, v.pxk * .9), pat = ctx.createPattern(grainTile(), 'repeat');
            ctx.setTransform(k, 0, 0, k, -v.gx, -v.gy);
            ctx.globalCompositeOperation = additive ? 'lighter' : 'source-over';
            ctx.globalAlpha = .06 * st.grain;
            ctx.fillStyle = pat;
            ctx.fillRect(v.gx / k, v.gy / k, v.w / k + 2, v.h / k + 2);
            ctx.globalAlpha = 1;
            ctx.globalCompositeOperation = 'source-over';
            ctx.setTransform(1, 0, 0, 1, 0, 0);
        }
    }
    if (o.plate) drawPlate(ctx, S, v);
}

function drawPlate(ctx, S, v) {
    const pal = S.pal, u = Math.min(v.gw, v.gh) * .028, pad = u * .9, x = u * 1.4, y = u * 1.4,
        fam = S.style.labelFont || 'Exo 2';
    ctx.setTransform(1, 0, 0, 1, -v.gx, -v.gy);
    ctx.textBaseline = 'alphabetic';
    const title = (S.name || 'Название города').toUpperCase(), sub = PRESETS[S.preset].name;
    const tw = textWidth(ctx, title, u * 1.7, fam, .18, 800), sw = textWidth(ctx, sub, u * .7, fam, .12, 600),
        w = Math.max(tw, sw) + pad * 2, h = u * 4.1;
    ctx.fillStyle = hexA(pal.bg, .78);
    ctx.fillRect(x, y, w, h);
    ctx.strokeStyle = pal.highway;
    ctx.globalAlpha = .8;
    ctx.lineWidth = Math.max(1, u * .06);
    ctx.strokeRect(x, y, w, h);
    ctx.globalAlpha = 1;
    ctx.fillStyle = pal.label;
    let cx = x + pad;
    ctx.font = '800 ' + (u * 1.7) + 'px "' + fam + '", sans-serif';
    for (const ch of Array.from(title)) {
        ctx.fillText(ch, cx, y + pad + u * 1.45);
        cx += ctx.measureText(ch).width + u * 1.7 * .18;
    }
    ctx.font = '600 ' + (u * .7) + 'px "' + fam + '", sans-serif';
    ctx.fillStyle = pal.coast;
    cx = x + pad;
    for (const ch of Array.from(sub)) {
        ctx.fillText(ch, cx, y + h - pad * .9);
        cx += ctx.measureText(ch).width + u * .7 * .12;
    }
    ctx.setTransform(1, 0, 0, 1, 0, 0);
}

function hexA(h, a) {
    const [r, g, b] = hex2rgb(h);
    return 'rgba(' + r + ',' + g + ',' + b + ',' + a + ')';
}

/* =====================================================================
    ИНТЕРФЕЙС
    ===================================================================== */
(function () {
    const $ = id => document.getElementById(id);
    const cv = $('cv'), ctx = cv.getContext('2d');
    let cw = 300, chh = 300, dpr = 1;
    const PAPER = {A4: [210, 297], A3: [297, 420], A2: [420, 594], A1: [594, 841], A0: [841, 1189]};
    const app = {
        S: null,
        view: {s: .3, tx: 0, ty: 0},
        toolId: 'nav',
        tool: 'nav',
        brushMode: 'sea',
        sel: null,
        draft: null,
        tab: 'gen',
        interacting: false,
        frame: null,
        cursor: null,
        cursorW: null,
        gen: {
            preset: 'metropolis',
            terrain: 'coast',
            seaSide: 'right',
            cityShape: 'round',
            mountains: 1,
            rivers: 1,
            sep: 17,
            nd: 9,
            farm: 36,
            seed: 12345,
            targetPop: 500000
        },
        brush: {r: 70, k: .7},
        opts: {
            roadKind: 'avenue',
            iconType: 'anchor',
            distType: 'residential',
            riverW: 12,
            autoCount: 24,
            specialType: 'monument'
        },
        exp: {paper: 'A3', dpi: 200, margin: 10, plate: true, pngSize: 4000, transparent: false},
        undo: [],
        redo: []
    };
    window.__app = app;

    /* ---------- утилиты DOM ---------- */
    function h(tag, attrs) {
        const e = document.createElement(tag);
        if (attrs) for (const k in attrs) {
            const v = attrs[k];
            if (v === false || v == null) continue;
            if (k === 'class') e.className = v; else if (k === 'style') e.style.cssText = v; else if (k.startsWith('on')) e.addEventListener(k.slice(2), v); else if (v === true) e.setAttribute(k, ''); else e.setAttribute(k, v);
        }
        for (let i = 2; i < arguments.length; i++) {
            const c = arguments[i];
            if (c == null || c === false) continue;
            if (Array.isArray(c)) c.forEach(x => x != null && x !== false && e.append(x)); else e.append(c);
        }
        return e;
    }

    function svgIcon(inner) {
        return '<svg viewBox="0 0 24 24" width="22" height="22" fill="none" stroke="currentColor" stroke-width="1.8" stroke-linecap="round" stroke-linejoin="round" aria-hidden="true">' + inner + '</svg>';
    }

    let toastT = 0;

    function toast(msg) {
        const t = $('toast');
        t.textContent = msg;
        t.classList.add('on');
        clearTimeout(toastT);
        toastT = setTimeout(() => t.classList.remove('on'), 2600);
    }

    function setBusy(msg) {
        const b = $('busy');
        if (msg) {
            $('busyMsg').textContent = msg;
            b.hidden = false;
        } else b.hidden = true;
    }

    const tick = () => new Promise(r => setTimeout(r, 16));

    /* ---------- отмена/повтор ---------- */
    let lastCp = {key: '', t: 0};

    function pushUndo() {
        app.undo.push(snapshot(app.S));
        if (app.undo.length > 20) app.undo.shift();
        app.redo.length = 0;
        syncUndo();
    }

    function cp(key) {
        const now = performance.now();
        if (key && key === lastCp.key && now - lastCp.t < 1500) {
            lastCp.t = now;
            return;
        }
        lastCp = {key, t: now};
        pushUndo();
    }

    function undo() {
        if (!app.undo.length) return;
        app.redo.push(snapshot(app.S));
        restore(app.S, app.undo.pop());
        app.sel = null;
        afterRestore();
    }

    function redo() {
        if (!app.redo.length) return;
        app.undo.push(snapshot(app.S));
        restore(app.S, app.redo.pop());
        app.sel = null;
        afterRestore();
    }

    function afterRestore() {
        $('cityName').value = app.S.name;
        syncUndo();
        buildPanel();
        render();
        scheduleSave();
    }

    function syncUndo() {
        $('bUndo').disabled = !app.undo.length;
        $('bRedo').disabled = !app.redo.length;
    }

    /* ---------- сохранение ---------- */
    let saveT = 0;

    function scheduleSave() {
        clearTimeout(saveT);
        saveT = setTimeout(() => {
            try {
                localStorage.setItem('neon-city-autosave', JSON.stringify(toProject(app.S)));
            } catch (e) {
            }
        }, 1800);
    }

    function changed() {
        scheduleSave();
    }

    /* ---------- вид ---------- */
    function resize() {
        const r = $('stage').getBoundingClientRect();
        cw = Math.max(50, r.width);
        chh = Math.max(50, r.height);
        dpr = Math.min(2, window.devicePixelRatio || 1);
        cv.width = Math.round(cw * dpr);
        cv.height = Math.round(chh * dpr);
        cv.style.width = cw + 'px';
        cv.style.height = chh + 'px';
        render();
    }

    function fit() {
        const S = app.S, v = app.view;
        v.s = Math.min(cw / S.W, chh / S.H) * .96;
        v.tx = (cw - S.W * v.s) / 2;
        v.ty = (chh - S.H * v.s) / 2;
    }

    const toWorld = (px, py) => [(px - app.view.tx) / app.view.s, (py - app.view.ty) / app.view.s];
    const toScreen = (x, y) => [x * app.view.s + app.view.tx, y * app.view.s + app.view.ty];

    function zoomAt(px, py, f) {
        const v = app.view, ns = clamp(v.s * f, .05, 60), k = ns / v.s;
        v.tx = px - (px - v.tx) * k;
        v.ty = py - (py - v.ty) * k;
        v.s = ns;
    }

    let raf = 0, idleT = 0;

    function render() {
        if (raf) return;
        raf = requestAnimationFrame(() => {
            raf = 0;
            draw();
        });
    }

    function interact() {
        app.interacting = true;
        clearTimeout(idleT);
        idleT = setTimeout(() => {
            app.interacting = false;
            render();
        }, 160);
        render();
    }

    function draw() {
        if (!app.S) return;
        const v = {
            w: cv.width,
            h: cv.height,
            s: app.view.s * dpr,
            tx: app.view.tx * dpr,
            ty: app.view.ty * dpr,
            pxk: dpr,
            gx: 0,
            gy: 0,
            gw: cv.width,
            gh: cv.height
        };
        renderScene(ctx, app.S, v, {fast: app.interacting});
        drawOverlay();
        const z = $('hud'), pop = (app.S.totalPop || 0).toLocaleString('ru-RU');
        z.textContent = Math.round(app.view.s * 100) + '%  ·  ' + pop + ' чел.' + (app.cursorW ? '  ·  ' + Math.round(app.cursorW[0]) + ', ' + Math.round(app.cursorW[1]) : '');
    }

    /* ---------- выбор и попадание ---------- */
    function getSel() {
        const s = app.sel, S = app.S;
        if (!s) return null;
        const L = {
            district: S.districts,
            road: S.roads,
            river: S.rivers,
            label: S.labels,
            icon: S.icons,
            green: S.green,
            waste: S.waste
        }[s.kind];
        return L ? L.find(o => o.id === s.id) || null : null;
    }

    function select(hit) {
        app.sel = hit ? {kind: hit.kind, id: hit.id} : null;
        buildCard();
        render();
    }

    function polyDist(pts, x, y) {
        let m = 1e9;
        for (let i = 0; i < pts.length - 1; i++) {
            const d = distSeg(x, y, pts[i][0], pts[i][1], pts[i + 1][0], pts[i + 1][1]);
            if (d < m) m = d;
        }
        return m;
    }

    function hitTest(w) {
        const S = app.S, tol = 9 / app.view.s, [x, y] = w;
        for (let i = S.icons.length - 1; i >= 0; i--) {
            const ic = S.icons[i];
            if (Math.hypot(ic.x - x, ic.y - y) < Math.max(tol, (ic.size || 30) * .5)) return {kind: 'icon', id: ic.id};
        }
        for (let i = S.waste.length - 1; i >= 0; i--) {
            const e = S.waste[i];
            if (Math.hypot(e.x - x, e.y - y) < e.r) return {kind: 'waste', id: e.id};
        }
        for (let i = S.green.length - 1; i >= 0; i--) {
            const e = S.green[i];
            if (Math.hypot(e.x - x, e.y - y) < e.r) return {kind: 'green', id: e.id};
        }
        for (let i = S.labels.length - 1; i >= 0; i--) {
            const l = S.labels[i];
            if (l.kind === 'street') {
                if (polyDist(l.path, x, y) < Math.max(tol, l.size * .8)) return {kind: 'label', id: l.id};
            } else {
                const a = l.ang || 0, dx = x - l.x, dy = y - l.y, lx = dx * Math.cos(-a) - dy * Math.sin(-a),
                    ly = dx * Math.sin(-a) + dy * Math.cos(-a);
                if (Math.abs(lx) < l.text.length * l.size * .32 + 4 && Math.abs(ly) < l.size * .7) return {
                    kind: 'label',
                    id: l.id
                };
            }
        }
        for (let i = S.districts.length - 1; i >= 0; i--) {
            const d = S.districts[i];
            if (!d.lbl || d.showLabel === false) continue;
            const size = d.lbl.size * S.style.labelScale * (d.lblScale || 1), c = d.lblPos || [d.lbl.x, d.lbl.y],
                a = d.lblAng !== undefined ? d.lblAng : d.lbl.ang;
            const dx = x - c[0], dy = y - c[1], lx = dx * Math.cos(-a) - dy * Math.sin(-a),
                ly = dx * Math.sin(-a) + dy * Math.cos(-a);
            if (Math.abs(lx) < d.name.length * size * .5 && Math.abs(ly) < size * .7 && size * app.view.s > 7) return {
                kind: 'district',
                id: d.id,
                onLabel: true
            };
        }
        for (let i = S.roads.length - 1; i >= 0; i--) {
            const r = S.roads[i];
            if (r.dense && polyDist(r.dense, x, y) < tol) return {kind: 'road', id: r.id};
        }
        for (let i = S.rivers.length - 1; i >= 0; i--) {
            const r = S.rivers[i];
            if (r.samp && r.samp.length > 1 && polyDist(r.samp, x, y) < Math.max(tol, r.width * .6)) return {
                kind: 'river',
                id: r.id
            };
        }
        for (let i = S.districts.length - 1; i >= 0; i--) {
            const d = S.districts[i];
            if (pip(x, y, d.poly)) return {kind: 'district', id: d.id};
        }
        return null;
    }

    function selPoints(o) {
        if (!o) return null;
        const k = app.sel.kind;
        return k === 'district' ? o.poly : (k === 'road' || k === 'river') ? o.pts : null;
    }

    function hitHandle(p) {
        const o = getSel(), pts = selPoints(o);
        if (!pts) return null;
        for (let i = 0; i < pts.length; i++) {
            const q = toScreen(pts[i][0], pts[i][1]);
            if (Math.hypot(q[0] - p.x, q[1] - p.y) < 11) return {pts, i};
        }
        return null;
    }

    function segHit(o, w) {
        const pts = selPoints(o);
        if (!pts) return null;
        const closed = app.sel.kind === 'district', n = pts.length, tol = 12 / app.view.s;
        for (let i = 0; i < (closed ? n : n - 1); i++) {
            const a = pts[i], b = pts[(i + 1) % n];
            if (distSeg(w[0], w[1], a[0], a[1], b[0], b[1]) < tol) return i;
        }
        return -1;
    }

    /* ---------- объектная кисть ---------- */
    function addBlobLive(x, y, kind) {
        const S = app.S;
        const list = kind === 'waste' ? S.waste : S.green;
        const baseR = kind === 'waste' ? 32 : 34;
        const last = list[list.length - 1];
        if (last && Math.hypot(last.x - x, last.y - y) < baseR * 0.42) return;
        if (S.waterAt(x, y) > 0.5 || S.heightAt(x, y) > 0.7) return;
        const rng = mulberry32((Date.now() ^ (S.nextId * 2654435761)) >>> 0);
        const r = baseR * (0.7 + 0.7 * rng());
        list.push({id: S.nextId++, x, y, r, seed: Math.floor(rng() * 1e9)});
        render();
    }

    /* ---------- кисть ---------- */
    let finT = 0;

    function paintBrush(a, b) {
        const S = app.S, r = app.brush.r, k = app.brush.k, cell = S.cell, mode = app.brushMode,
            dist = Math.hypot(b[0] - a[0], b[1] - a[1]), n = Math.max(1, Math.ceil(dist / (r * .3)));
        for (let s = 0; s <= n; s++) {
            const x = a[0] + (b[0] - a[0]) * s / n, y = a[1] + (b[1] - a[1]) * s / n;
            const i0 = Math.max(0, Math.floor((x - r) / cell)), i1 = Math.min(S.gw - 1, Math.ceil((x + r) / cell)),
                j0 = Math.max(0, Math.floor((y - r) / cell)), j1 = Math.min(S.gh - 1, Math.ceil((y + r) / cell));
            for (let j = j0; j <= j1; j++) for (let i = i0; i <= i1; i++) {
                const d = Math.hypot((i + .5) * cell - x, (j + .5) * cell - y) / r;
                if (d >= 1) continue;
                const f = smoothstep(1, .3, d), idx = j * S.gw + i;
                if (mode === 'sea') S.water[idx] = clamp(S.water[idx] + f * k * .6, 0, 1);
                else if (mode === 'land') S.water[idx] = clamp(S.water[idx] - f * k * .6, 0, 1);
                else if (mode === 'mount') S.height[idx] = clamp(S.height[idx] + f * k * .05, 0, 1);
                else if (mode === 'valley') S.height[idx] = clamp(S.height[idx] - f * k * .07, 0, 1);
                else if (mode === 'smooth') {
                    for (const F of [S.water, S.height]) {
                        let sum = 0, c = 0;
                        for (let dj = -1; dj <= 1; dj++) for (let di = -1; di <= 1; di++) {
                            const ii = clamp(i + di, 0, S.gw - 1), jj = clamp(j + dj, 0, S.gh - 1);
                            sum += F[jj * S.gw + ii];
                            c++;
                        }
                        F[idx] += (sum / c - F[idx]) * clamp(f * k * .7, 0, 1);
                    }
                }
            }
        }
        S._wc = null;
        interact();
        if (!finT) finT = setTimeout(() => {
            finT = 0;
            finTerrain(app.S);
            render();
        }, 110);
    }

    function endBrush() {
        clearTimeout(finT);
        finT = 0;
        const S = app.S;
        for (let i = 0; i < S.height.length; i++) if (S.water[i] > .5) S.height[i] = 0;
        finalizeAll(S);
        changed();
        render();
    }

    /* ---------- черновик рисования ---------- */
    function updateDrawbar() {
        const d = app.draft, bar = $('drawbar');
        if (!d) {
            bar.hidden = true;
            return;
        }
        const need = d.tool === 'district' ? 3 : 2;
        bar.hidden = false;
        $('dbInfo').textContent = ({
            river: 'Река',
            district: 'Район',
            road: 'Дорога',
            rail: 'Ж/д'
        }[d.tool]) + ': точек ' + d.pts.length + (d.pts.length < need ? ' (нужно ≥ ' + need + ')' : '');
        $('dbDone').disabled = d.pts.length < need;
    }

    function dedupe(pts) {
        const out = [];
        for (const p of pts) {
            const q = out[out.length - 1];
            if (!q || Math.hypot(q[0] - p[0], q[1] - p[1]) > 3) out.push(p);
        }
        return out;
    }

    function finishDraft() {
        const d = app.draft;
        if (!d) return;
        const S = app.S;
        d.pts = dedupe(d.pts);
        const need = d.tool === 'district' ? 3 : 2;
        if (d.pts.length < need) {
            toast('Слишком мало точек');
            return;
        }
        pushUndo();
        const rng = mulberry32((Date.now() ^ S.nextId * 977) >>> 0);
        if (d.tool === 'river') {
            const r = {id: S.nextId++, name: riverName(S, rng), pts: d.pts, width: app.opts.riverW};
            S.rivers.push(r);
            finalizeAll(S);
            app.sel = {kind: 'river', id: r.id};
        } else if (d.tool === 'district') {
            const type = app.opts.distType,
                dist = makeDistrict(S, type, ensureCCW(d.pts.map(p => p.slice())), rng, districtName(S, rng, type, new Set(S.districts.map(x => x.name))));
            S.baseSep = S.baseSep || app.gen.sep;
            dist.sep = Math.round(S.baseSep * TYPES[type].sepK * 10) / 10;
            S.districts.push(dist);
            dist.raw = genDistrictRaw(dist, S);
            computeLabel(dist);
            finalizeAll(S);
            app.sel = {kind: 'district', id: dist.id};
        } else {
            const kind = d.tool === 'rail' ? 'rail' : app.opts.roadKind,
                r = {id: S.nextId++, kind, pts: d.pts, name: kind === 'rail' ? 'Линия' : streetName(S, rng), lblT: .5};
            S.roads.push(r);
            finRoads(S);
            app.sel = {kind: 'road', id: r.id};
        }
        app.draft = null;
        updateDrawbar();
        buildCard();
        changed();
        render();
    }

    function cancelDraft() {
        app.draft = null;
        updateDrawbar();
        render();
    }

    function draftPoint(w) {
        const t = app.tool;
        if (!app.draft || app.draft.tool !== t) app.draft = {tool: t, pts: []};
        app.draft.pts.push(w);
        updateDrawbar();
        render();
    }

    /* ---------- ввод ---------- */
    const pointers = new Map();
    let drag = null, pinch = null, spaceDown = false;

    function pos(e) {
        const r = cv.getBoundingClientRect();
        return {x: e.clientX - r.left, y: e.clientY - r.top};
    }

    cv.addEventListener('contextmenu', e => e.preventDefault());
    cv.addEventListener('pointerdown', e => {
        cv.setPointerCapture(e.pointerId);
        const p = pos(e);
        pointers.set(e.pointerId, p);
        if (pointers.size === 2) {
            const [a, b] = [...pointers.values()];
            pinch = {d: Math.hypot(a.x - b.x, a.y - b.y), cx: (a.x + b.x) / 2, cy: (a.y + b.y) / 2, v: {...app.view}};
            if (drag && drag.type === 'brush') endBrush();
            drag = null;
            return;
        }
        const w = toWorld(p.x, p.y), t = app.tool;
        if (e.button === 1 || e.button === 2 || spaceDown) {
            drag = {type: 'pan', x: p.x, y: p.y, tx: app.view.tx, ty: app.view.ty};
            return;
        }
        if (t === 'nav') {
            const hh = hitHandle(p);
            if (hh) {
                pushUndo();
                drag = {type: 'handle', hh};
                return;
            }
            const hit = hitTest(w);
            if (hit) {
                select(hit);
                if (hit.kind === 'label' || hit.kind === 'icon' || hit.kind === 'green' || hit.kind === 'waste' || hit.onLabel) {
                    pushUndo();
                    drag = {type: 'obj', hit, last: w, moved: false};
                    return;
                }
            } else if (app.sel) select(null);
            drag = {type: 'pan', x: p.x, y: p.y, tx: app.view.tx, ty: app.view.ty};
            return;
        }
        if (t === 'brush') {
            pushUndo();
            drag = {type: 'brush', last: w};
            paintBrush(w, w);
            return;
        }
        if (t === 'parkBrush' || t === 'wasteBrush') {
            pushUndo();
            const kind = t === 'wasteBrush' ? 'waste' : 'green';
            drag = {type: 'objbrush', kind};
            addBlobLive(w[0], w[1], kind);
            return;
        }
        if (t === 'frame') {
            drag = {type: 'frame', a: w};
            app.frame = {x0: w[0], y0: w[1], x1: w[0], y1: w[1]};
            return;
        }
        drag = {type: 'tap', x: p.x, y: p.y, tx: app.view.tx, ty: app.view.ty, moved: false};
    });
    cv.addEventListener('pointermove', e => {
        const p = pos(e);
        app.cursor = p;
        app.cursorW = toWorld(p.x, p.y);
        if (pointers.has(e.pointerId)) pointers.set(e.pointerId, p);
        if (pointers.size === 2 && pinch) {
            const [a, b] = [...pointers.values()], d = Math.hypot(a.x - b.x, a.y - b.y), cx = (a.x + b.x) / 2,
                cy = (a.y + b.y) / 2, ns = clamp(pinch.v.s * d / pinch.d, .05, 60), k = ns / pinch.v.s;
            app.view.s = ns;
            app.view.tx = cx - (pinch.cx - pinch.v.tx) * k;
            app.view.ty = cy - (pinch.cy - pinch.v.ty) * k;
            interact();
            return;
        }
        if (!drag) {
            render();
            return;
        }
        const w = app.cursorW;
        if (drag.type === 'pan') {
            app.view.tx = drag.tx + p.x - drag.x;
            app.view.ty = drag.ty + p.y - drag.y;
            interact();
        } else if (drag.type === 'tap') {
            if (!drag.moved && Math.hypot(p.x - drag.x, p.y - drag.y) > 7) drag.moved = true;
            if (drag.moved) {
                app.view.tx = drag.tx + p.x - drag.x;
                app.view.ty = drag.ty + p.y - drag.y;
                interact();
            }
        } else if (drag.type === 'brush') {
            paintBrush(drag.last, w);
            drag.last = w;
        } else if (drag.type === 'objbrush') {
            addBlobLive(w[0], w[1], drag.kind);
        } else if (drag.type === 'frame') {
            app.frame.x1 = w[0];
            app.frame.y1 = w[1];
            render();
        } else if (drag.type === 'handle') {
            const {pts, i} = drag.hh;
            pts[i][0] = w[0];
            pts[i][1] = w[1];
            const S = app.S, o = getSel();
            if (app.sel.kind === 'road') finRoads(S); else if (app.sel.kind === 'river') {
                S.rb = new Map();
                S.rivers.forEach(r => buildRiver(S, r));
            }
            drag.moved = true;
            interact();
        } else if (drag.type === 'obj') {
            const dx = w[0] - drag.last[0], dy = w[1] - drag.last[1];
            drag.last = w;
            drag.moved = true;
            const o = getSel(), S = app.S;
            if (drag.hit.kind === 'district') {
                const d = o;
                const c = d.lblPos || [d.lbl.x, d.lbl.y];
                d.lblPos = [c[0] + dx, c[1] + dy];
            } else if (drag.hit.kind === 'icon') {
                o.x += dx;
                o.y += dy;
            } else if (drag.hit.kind === 'green' || drag.hit.kind === 'waste') {
                o.x += dx;
                o.y += dy;
            } else if (o.kind === 'street') o.path.forEach(q => {
                q[0] += dx;
                q[1] += dy;
            }); else {
                o.x += dx;
                o.y += dy;
            }
            render();
        }
    });

    function endPointer(e) {
        const p = pos(e);
        pointers.delete(e.pointerId);
        if (pointers.size < 2) pinch = null;
        if (!drag) return;
        const d = drag;
        drag = null;
        if (d.type === 'brush') endBrush();
        else if (d.type === 'objbrush') {
            changed();
            render();
        } else if (d.type === 'tap') {
            if (!d.moved) onTap(toWorld(p.x, p.y));
        } else if (d.type === 'handle') {
            if (d.moved) commitShape();
        } else if (d.type === 'obj') {
            if (d.moved) changed(); else app.undo.pop(), syncUndo();
        } else if (d.type === 'frame') {
            const f = app.frame;
            if (Math.abs(f.x1 - f.x0) < 8 || Math.abs(f.y1 - f.y0) < 8) app.frame = null; else {
                toast('Рамка задана — экспорт во вкладке «Экспорт»');
            }
            buildPanel();
            render();
        } else if (d.type === 'pan') {
            render();
        }
    }

    cv.addEventListener('pointerup', endPointer);
    cv.addEventListener('pointercancel', endPointer);
    cv.addEventListener('pointerleave', () => {
        app.cursor = null;
        app.cursorW = null;
        render();
    });
    cv.addEventListener('wheel', e => {
        e.preventDefault();
        const p = pos(e);
        zoomAt(p.x, p.y, Math.exp(-e.deltaY * (e.ctrlKey ? .01 : .0016)));
        interact();
    }, {passive: false});

    function commitShape() {
        const S = app.S, k = app.sel && app.sel.kind, o = getSel();
        if (!o) return;
        if (k === 'district') {
            retraceDistrict(S, o);
            finalizeAll(S);
        } else if (k === 'river') finalizeAll(S); else if (k === 'road') finRoads(S);
        changed();
        render();
    }

    cv.addEventListener('dblclick', e => {
        const p = pos(e), w = toWorld(p.x, p.y);
        if (app.draft) {
            finishDraft();
            return;
        }
        if (app.tool !== 'nav') return;
        const o = getSel(), pts = selPoints(o);
        if (!o || !pts) return;
        const hh = hitHandle(p);
        const minPts = app.sel.kind === 'district' ? 3 : 2;
        pushUndo();
        if (hh) {
            if (pts.length > minPts) {
                pts.splice(hh.i, 1);
                commitShape();
            } else {
                app.undo.pop();
                syncUndo();
                toast('Нельзя удалить: слишком мало точек');
            }
            return;
        }
        const si = segHit(o, w);
        if (si >= 0) {
            pts.splice(si + 1, 0, [w[0], w[1]]);
            commitShape();
        } else {
            app.undo.pop();
            syncUndo();
        }
    });

    function onTap(w) {
        const S = app.S, t = app.tool, rng = mulberry32((Date.now() ^ S.nextId * 31) >>> 0);
        if (t === 'river' || t === 'district' || t === 'road' || t === 'rail') {
            draftPoint(w);
            return;
        }
        if (t === 'labelStreet') {
            const hit = nearestStreet(S, w[0], w[1], 16 / app.view.s);
            if (!hit) {
                toast('Кликните ближе к улице');
                return;
            }
            pushUndo();
            const text = streetName(S, rng), size = clamp(hit.tag && hit.tag.sep ? hit.tag.sep * .55 : 10, 7, 14),
                lb = makeStreetLabel(S, hit, text, size);
            if (!lb) {
                app.undo.pop();
                syncUndo();
                return;
            }
            S.labels.push(lb);
            app.sel = {kind: 'label', id: lb.id};
            buildCard();
            changed();
            render();
            return;
        }
        if (t === 'labelPoint') {
            pushUndo();
            const lb = {id: S.nextId++, kind: 'point', text: 'Название', x: w[0], y: w[1], ang: 0, size: 18};
            S.labels.push(lb);
            app.sel = {kind: 'label', id: lb.id};
            buildCard();
            changed();
            render();
            return;
        }
        if (t === 'icon') {
            pushUndo();
            const ty = app.opts.iconType,
                ic = {id: S.nextId++, type: ty, x: w[0], y: w[1], ang: 0, size: ICON_SIZES[ty]};
            S.icons.push(ic);
            app.sel = {kind: 'icon', id: ic.id};
            buildCard();
            changed();
            render();
            return;
        }
        if (t === 'special') {
            const ty = app.opts.specialType || 'monument';
            let host = null;
            for (const d of S.districts) if (pip(w[0], w[1], d.poly)) {
                host = d;
                break;
            }
            const pool = SPECIAL_FOR_TYPE[host ? host.type : 'center'] || [];
            const ok = pool.includes(ty);
            if (!ok && host) toast('Обычно «' + ICON_NAMES[ty] + '» ставится не в «' + TYPES[host.type].n + '» — но можно и сюда');
            pushUndo();
            const ic = {id: S.nextId++, type: ty, x: w[0], y: w[1], ang: 0, size: ICON_SIZES[ty] || 40};
            S.icons.push(ic);
            app.sel = {kind: 'icon', id: ic.id};
            buildCard();
            changed();
            render();
            return;
        }
    }

    window.addEventListener('keydown', e => {
        const tag = (e.target.tagName || '').toLowerCase();
        if (tag === 'input' || tag === 'textarea' || tag === 'select') {
            if (e.key === 'Escape') e.target.blur();
            return;
        }
        if (e.code === 'Space') {
            spaceDown = true;
            e.preventDefault();
        }
        if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'z') {
            e.preventDefault();
            e.shiftKey ? redo() : undo();
        } else if ((e.ctrlKey || e.metaKey) && e.key.toLowerCase() === 'y') {
            e.preventDefault();
            redo();
        } else if (e.key === 'Escape') {
            if (app.draft) cancelDraft(); else if (app.tool !== 'nav') setTool('nav'); else select(null);
        } else if (e.key === 'Enter') {
            if (app.draft) finishDraft();
        } else if (e.key === 'Backspace' && app.draft) {
            app.draft.pts.pop();
            updateDrawbar();
            render();
            e.preventDefault();
        } else if ((e.key === 'Delete' || e.key === 'Backspace') && app.sel) {
            deleteSel();
        }
    });
    window.addEventListener('keyup', e => {
        if (e.code === 'Space') spaceDown = false;
    });

    /* ---------- инструменты ---------- */
    const TOOLS = [
        {
            id: 'nav',
            label: 'Курсор',
            hint: 'Выбор и правка: перетаскивайте точки, двойной клик — добавить/убрать точку',
            ic: '<path d="M5 3l14 7-6 2-2 6z"/>'
        },
        {
            id: 'sea',
            tool: 'brush',
            mode: 'sea',
            label: 'Море',
            hint: 'Кисть: добавить воду (море, озеро, бухта)',
            ic: '<path d="M3 9q3-3 6 0t6 0t6 0M3 15q3-3 6 0t6 0t6 0"/>'
        },
        {
            id: 'land',
            tool: 'brush',
            mode: 'land',
            label: 'Суша',
            hint: 'Кисть: убрать воду — намыть сушу, побережье',
            ic: '<path d="M3 17c4-4 6-4 9-1s6 1 9-3v7H3z"/>'
        },
        {
            id: 'mount',
            tool: 'brush',
            mode: 'mount',
            label: 'Горы',
            hint: 'Кисть: поднять рельеф',
            ic: '<path d="M2 19l7-12 4 6 3-4 6 10z"/>'
        },
        {
            id: 'valley',
            tool: 'brush',
            mode: 'valley',
            label: 'Равнина',
            hint: 'Кисть: сгладить горы до равнины',
            ic: '<path d="M12 4v12M6 12l6 6 6-6"/>'
        },
        {
            id: 'smooth',
            tool: 'brush',
            mode: 'smooth',
            label: 'Сгладить',
            hint: 'Кисть: сгладить береговую линию и склоны',
            ic: '<path d="M3 12c3-6 6-6 9 0s6 6 9 0"/>'
        },
        {
            id: 'river',
            label: 'Река',
            hint: 'Клики — точки реки, двойной клик — готово',
            ic: '<path d="M4 4c8 2-2 6 4 9s-2 6 5 7"/>'
        },
        {
            id: 'district',
            label: 'Район',
            hint: 'Клики — вершины района, двойной клик — готово',
            ic: '<path d="M4 7l8-4 8 5-2 11-10 2z"/>'
        },
        {
            id: 'road',
            label: 'Дорога',
            hint: 'Клики — точки дороги (тип — во вкладке «Город»)',
            ic: '<path d="M4 20L10 4M20 20L14 4M12 6v3M12 12v3"/>'
        },
        {
            id: 'rail',
            label: 'Рельсы',
            hint: 'Клики — точки железной дороги',
            ic: '<path d="M8 3l-3 18M16 3l3 18M6.5 8h11M5.5 14h13"/>'
        },
        {
            id: 'labelStreet',
            label: 'Улица',
            hint: 'Клик по улице — поставить название вдоль неё',
            ic: '<path d="M5 19l7-14 7 14M8 14h8"/>'
        },
        {id: 'labelPoint', label: 'Текст', hint: 'Клик — свободная надпись', ic: '<path d="M5 6h14M12 6v13"/>'},
        {
            id: 'icon',
            label: 'Значок',
            hint: 'Клик — поставить значок (тип — во вкладке «Город»)',
            ic: '<path d="M12 8a2 2 0 100-4 2 2 0 000 4zM12 8v13M6 13H4a8 8 0 0016 0h-2M8 12h8"/>'
        },
        {
            id: 'park',
            tool: 'parkBrush',
            label: 'Парк',
            hint: 'Кисть: рисовать зелёные зоны — парки, скверы, бульвары, зоны отдыха',
            ic: '<path d="M12 4c-3 0-5 2-5 5 0 2 1 3 2 4-2 1-3 2-3 4h12c0-2-1-3-3-4 1-1 2-2 2-4 0-3-2-5-5-5zM12 17v3"/>'
        },
        {
            id: 'waste',
            tool: 'wasteBrush',
            label: 'Свалка',
            hint: 'Кисть: рисовать свалку, пустырь, полигон',
            ic: '<path d="M4 18l4-8 3 5 2-3 3 6M6 20h14M9 8l2 3M15 10l2 2"/>'
        },
        {
            id: 'special',
            label: 'Объект',
            hint: 'Клик — поставить особое здание (тип — во вкладке «Город»)',
            ic: '<path d="M12 3l7 5v10l-7 4-7-4V8zM12 3v18M5 8l14 10M19 8L5 18"/>'
        },
        {
            id: 'frame',
            label: 'Рамка',
            hint: 'Обведите область для PNG-экспорта',
            ic: '<path d="M4 8V4h4M16 4h4v4M20 16v4h-4M8 20H4v-4"/>'
        }
    ];

    function buildTools() {
        const nav = $('tools');
        nav.innerHTML = '';
        TOOLS.forEach(t => nav.append(h('button', {
            class: 'tool' + (app.toolId === t.id ? ' on' : ''),
            title: t.hint,
            'aria-label': t.label,
            'data-tool': t.id,
            onclick: () => setTool(t.id)
        }, Object.assign(h('span', {class: 'ti'}), {innerHTML: svgIcon(t.ic)}), h('span', {class: 'tl'}, t.label))));
    }

    function setTool(id) {
        const t = TOOLS.find(x => x.id === id);
        if (app.draft) cancelDraft();
        app.toolId = id;
        app.tool = t.tool || t.id;
        if (t.mode) app.brushMode = t.mode;
        buildTools();
        cv.style.cursor = app.tool === 'nav' ? 'default' : 'crosshair';
        toast(t.hint);
        render();
        if (['sea', 'land', 'mount', 'valley', 'smooth'].includes(id)) setTab('land'); else if (['road', 'rail', 'district', 'icon', 'park', 'waste', 'special'].includes(id)) setTab('city'); else if (id === 'frame') setTab('exp'); else if (id === 'labelStreet' || id === 'labelPoint') setTab('lab');
    }

    /* ---------- оверлей редактора ---------- */
    function drawOverlay() {
        ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
        ctx.globalCompositeOperation = 'source-over';
        ctx.globalAlpha = 1;
        ctx.setLineDash([]);
        ctx.lineJoin = 'round';
        ctx.lineCap = 'round';
        const ACC = '#ff3d8b', CY = '#35e8d8', o = getSel(), S = app.S;
        const handles = pts => {
            for (const p of pts) {
                const q = toScreen(p[0], p[1]);
                ctx.fillStyle = '#fff';
                ctx.strokeStyle = ACC;
                ctx.lineWidth = 2;
                ctx.beginPath();
                ctx.rect(q[0] - 4.5, q[1] - 4.5, 9, 9);
                ctx.fill();
                ctx.stroke();
            }
        };
        const line = (pts, closed) => {
            ctx.beginPath();
            pts.forEach((p, i) => {
                const q = toScreen(p[0], p[1]);
                i ? ctx.lineTo(q[0], q[1]) : ctx.moveTo(q[0], q[1]);
            });
            if (closed) ctx.closePath();
            ctx.stroke();
        };
        if (o && app.sel) {
            const k = app.sel.kind;
            ctx.strokeStyle = '#ffffff';
            ctx.lineWidth = 1.6;
            ctx.setLineDash([7, 5]);
            if (k === 'district') {
                line(o.poly, true);
                ctx.setLineDash([]);
                handles(o.poly);
                if (o.lbl && o.showLabel !== false) {
                    const c = o.lblPos || [o.lbl.x, o.lbl.y], q = toScreen(c[0], c[1]);
                    ctx.strokeStyle = CY;
                    ctx.beginPath();
                    ctx.arc(q[0], q[1], 5, 0, TAU);
                    ctx.stroke();
                }
            } else if (k === 'road' || k === 'river') {
                line(o.pts, false);
                ctx.setLineDash([]);
                handles(o.pts);
            } else if (k === 'label') {
                ctx.setLineDash([]);
                ctx.strokeStyle = CY;
                ctx.globalAlpha = .55;
                ctx.lineWidth = Math.max(6, o.size * app.view.s * 1.3);
                if (o.kind === 'street') line(o.path, false); else {
                    const q = toScreen(o.x, o.y);
                    ctx.beginPath();
                    ctx.arc(q[0], q[1], Math.max(8, o.text.length * o.size * app.view.s * .3), 0, TAU);
                    ctx.stroke();
                }
                ctx.globalAlpha = 1;
            } else if (k === 'icon') {
                const q = toScreen(o.x, o.y);
                ctx.setLineDash([]);
                ctx.strokeStyle = CY;
                ctx.beginPath();
                ctx.arc(q[0], q[1], Math.max(10, (o.size || 30) * app.view.s * .6), 0, TAU);
                ctx.stroke();
            } else if (k === 'green' || k === 'waste') {
                const q = toScreen(o.x, o.y);
                ctx.setLineDash([]);
                ctx.strokeStyle = CY;
                ctx.beginPath();
                ctx.arc(q[0], q[1], Math.max(8, o.r * app.view.s), 0, TAU);
                ctx.stroke();
            }
            ctx.setLineDash([]);
        }
        if (app.draft) {
            const pts = app.draft.pts;
            ctx.strokeStyle = CY;
            ctx.lineWidth = 2.2;
            ctx.setLineDash([]);
            const all = pts.slice();
            if (app.cursorW) all.push(app.cursorW);
            if (all.length > 1) line(all, false);
            if (app.draft.tool === 'district' && pts.length > 2) {
                ctx.globalAlpha = .4;
                ctx.setLineDash([4, 5]);
                line([pts[pts.length - 1], pts[0]], false);
                ctx.setLineDash([]);
                ctx.globalAlpha = 1;
            }
            for (const p of pts) {
                const q = toScreen(p[0], p[1]);
                ctx.fillStyle = ACC;
                ctx.beginPath();
                ctx.arc(q[0], q[1], 4.5, 0, TAU);
                ctx.fill();
            }
        }
        if (app.tool === 'brush' && app.cursor) {
            const R = app.brush.r * app.view.s;
            ctx.strokeStyle = {
                sea: '#35e8d8',
                land: '#ffb02e',
                mount: '#b8a4ff',
                valley: '#ffb02e',
                smooth: '#ffffff'
            }[app.brushMode];
            ctx.lineWidth = 2;
            ctx.beginPath();
            ctx.arc(app.cursor.x, app.cursor.y, R, 0, TAU);
            ctx.stroke();
            ctx.globalAlpha = .4;
            ctx.beginPath();
            ctx.arc(app.cursor.x, app.cursor.y, R * .3, 0, TAU);
            ctx.stroke();
            ctx.globalAlpha = 1;
        }
        if ((app.tool === 'parkBrush' || app.tool === 'wasteBrush') && app.cursor) {
            const R = 34 * app.view.s;
            ctx.strokeStyle = app.tool === 'wasteBrush' ? '#a08968' : '#37e6a4';
            ctx.lineWidth = 2;
            ctx.beginPath();
            ctx.arc(app.cursor.x, app.cursor.y, R, 0, TAU);
            ctx.stroke();
            ctx.globalAlpha = .4;
            ctx.beginPath();
            ctx.arc(app.cursor.x, app.cursor.y, R * .3, 0, TAU);
            ctx.stroke();
            ctx.globalAlpha = 1;
        }
        if (app.frame) {
            const f = app.frame, a = toScreen(Math.min(f.x0, f.x1), Math.min(f.y0, f.y1)),
                b = toScreen(Math.max(f.x0, f.x1), Math.max(f.y0, f.y1));
            ctx.fillStyle = 'rgba(0,0,0,.35)';
            ctx.beginPath();
            ctx.rect(0, 0, cw, chh);
            ctx.rect(a[0], a[1], b[0] - a[0], b[1] - a[1]);
            ctx.fill('evenodd');
            ctx.strokeStyle = '#ffb02e';
            ctx.lineWidth = 2;
            ctx.setLineDash([8, 5]);
            ctx.strokeRect(a[0], a[1], b[0] - a[0], b[1] - a[1]);
            ctx.setLineDash([]);
            ctx.fillStyle = '#ffb02e';
            ctx.font = '600 12px "Exo 2", sans-serif';
            ctx.fillText(Math.round(Math.abs(f.x1 - f.x0)) + ' × ' + Math.round(Math.abs(f.y1 - f.y0)), a[0] + 6, a[1] + 16);
        }
    }

    /* ---------- виджеты панели ---------- */
    const sec = (title, ...kids) => h('section', {class: 'sec'}, title ? h('h3', null, title) : null, ...kids);

    function slider(label, min, max, step, val, onInput, opt) {
        opt = opt || {};
        const fmt = opt.fmt || (v => v), out = h('output', null, fmt(val)),
            inp = h('input', {type: 'range', min, max, step, value: val, 'aria-label': label});
        inp.addEventListener('input', () => {
            const v = +inp.value;
            out.textContent = fmt(v);
            onInput(v);
        });
        if (opt.commit) inp.addEventListener('change', () => opt.commit(+inp.value));
        return h('label', {class: 'fld'}, h('span', {class: 'fl'}, label, out), inp);
    }

    function check(label, val, on) {
        const i = h('input', {type: 'checkbox'});
        i.checked = !!val;
        i.addEventListener('change', () => on(i.checked));
        return h('label', {class: 'chk'}, i, h('span', null, label));
    }

    function selectEl(label, opts, val, on) {
        const s = h('select', {'aria-label': label});
        opts.forEach(([v, t]) => {
            const o = h('option', {value: v}, t);
            if (v === val) o.selected = true;
            s.append(o);
        });
        s.addEventListener('change', () => on(s.value));
        return h('label', {class: 'fld'}, h('span', {class: 'fl'}, label), s);
    }

    function textEl(label, val, on) {
        const i = h('input', {type: 'text', value: val, 'aria-label': label});
        i.addEventListener('input', () => on(i.value));
        return h('label', {class: 'fld'}, h('span', {class: 'fl'}, label), i);
    }

    function colorEl(label, val, on, extra) {
        const i = h('input', {type: 'color', value: val, 'aria-label': label});
        i.addEventListener('input', () => on(i.value));
        return h('label', {class: 'clr'}, i, h('span', null, label), extra || null);
    }

    const btn = (label, on, cls) => h('button', {class: 'btn ' + (cls || ''), onclick: on}, label);

    /* ---------- вкладки ---------- */
    const TABS = [['gen', 'Генерация'], ['land', 'Ландшафт'], ['city', 'Город'], ['names', 'Названия'], ['col', 'Цвета'], ['lab', 'Подписи'], ['exp', 'Экспорт']];

    function setTab(t) {
        app.tab = t;
        buildPanel();
    }

    function buildPanel() {
        const tabs = $('tabs');
        tabs.innerHTML = '';
        TABS.forEach(([id, t]) => tabs.append(h('button', {
            class: 'tab' + (app.tab === id ? ' on' : ''),
            role: 'tab',
            'aria-selected': app.tab === id,
            onclick: () => setTab(id)
        }, t)));
        const b = $('pbody');
        b.innerHTML = '';
        ({
            gen: tabGen,
            land: tabLand,
            city: tabCity,
            names: tabNames,
            col: tabCol,
            lab: tabLab,
            exp: tabExp
        })[app.tab](b);
        buildCard();
        // Прокрутить к активной вкладке, если она ушла за край
        const active = tabs.querySelector('.tab.on');
        if (active) {
            const tL = tabs.scrollLeft, tR = tL + tabs.clientWidth;
            const aL = active.offsetLeft, aR = aL + active.offsetWidth;
            if (aL < tL + 12) tabs.scrollLeft = Math.max(0, aL - 12);
            else if (aR > tR - 12) tabs.scrollLeft = aR - tabs.clientWidth + 12;
        }
        updateTabsScroll();
    }

    function updateTabsScroll() {
        const tabs = $('tabs'), wrap = $('tabsWrap');
        if (!tabs || !wrap) return;
        const canL = tabs.scrollLeft > 2;
        const canR = tabs.scrollLeft + tabs.clientWidth < tabs.scrollWidth - 2;
        wrap.classList.toggle('canLeft', canL);
        wrap.classList.toggle('canRight', canR);
    }

    function buildCard() {
        const c = $('card');
        c.innerHTML = '';
        const o = getSel();
        if (!o) {
            c.hidden = true;
            return;
        }
        c.hidden = false;
        const S = app.S, k = app.sel.kind;
        const head = (t) => h('div', {class: 'chead'}, h('strong', null, t), btn('Снять выделение', () => select(null), 'ghost sm'));
        const del = btn('Удалить', deleteSel, 'danger');
        if (k === 'district') {
            const d = o, ref = () => refreshDistrict(d), T = d.type;
            c.append(head('Район'), textEl('Название', d.name, v => {
                    d.name = v;
                    render();
                    changed();
                }),
                selectEl('Тип района', Object.keys(TYPES).map(t => [t, TYPES[t].n]), d.type, v => {
                    cp('dtype' + d.id);
                    d.type = v;
                    const Tt = TYPES[v];
                    d.style = Tt.style;
                    d.curv = Tt.curv;
                    d.sep = Math.round(S.baseSep * Tt.sepK * 10) / 10;
                    d.alleys = Tt.alleys;
                    d.parks = Tt.parks;
                    d.ragged = Tt.ragged;
                    ref();
                    buildCard();
                }),
                colorEl('Цвет района', dcol(S, d), v => {
                    cp('dcol' + d.id);
                    d.color = v;
                    render();
                    changed();
                }, d.color ? btn('Сброс', () => {
                    cp('dcol' + d.id);
                    d.color = null;
                    render();
                    buildCard();
                    changed();
                }, 'ghost sm') : null),
                selectEl('Планировка', [['grid', 'Сетка'], ['organic', 'Извилистая'], ['radial', 'Радиальная']], d.style, v => {
                    cp('dsty' + d.id);
                    d.style = v;
                    ref();
                }),
                slider('Плотность застройки', 0, 1, .02, d.density || 0, v => {
                    d.density = v;
                    d.pop = Math.round(Math.abs(polyArea(d.poly)) * v * (TYPES[d.type].popDensity || 0));
                    app.S.totalPop = app.S.districts.reduce((s, x) => s + (x.pop || 0), 0);
                    render();
                }, {
                    commit: () => {
                        rebuildBuildings(app.S, d);
                        changed();
                        render();
                    }, fmt: v => Math.round(v * 100) + '%'
                }),
                h('div', {
                    class: 'fl',
                    style: 'margin:-6px 0 12px'
                }, h('span', null, 'Население района'), h('output', null, (d.pop || 0).toLocaleString('ru-RU') + ' чел.')),
                slider('Размер квартала', 8, 60, .5, d.sep, v => {
                    cp('dsep' + d.id);
                    d.sep = v;
                }, {commit: ref}),
                slider('Вытянутость кварталов', 1, 2.4, .05, d.ratio, v => {
                    cp('drat' + d.id);
                    d.ratio = v;
                }, {commit: ref}),
                slider('Угол сетки', 0, 180, 1, Math.round(d.angle * 180 / Math.PI) % 180, v => {
                    cp('dang' + d.id);
                    d.angle = v * Math.PI / 180;
                }, {commit: ref, fmt: v => v + '°'}),
                slider('Извилистость', 0, 1.6, .05, d.curv, v => {
                    cp('dcur' + d.id);
                    d.curv = v;
                }, {commit: ref}),
                slider('Переулки', 0, 1, .05, d.alleys, v => {
                    cp('dall' + d.id);
                    d.alleys = v;
                }, {commit: ref}),
                slider('Парки и скверы', 0, 1, .05, d.parks, v => {
                    cp('dpar' + d.id);
                    d.parks = v;
                }, {commit: ref}),
                slider('Рваный край', 0, 1, .05, d.ragged, v => {
                    cp('drag' + d.id);
                    d.ragged = v;
                }, {commit: ref}),
                slider('Размер названия', .4, 2.5, .05, d.lblScale || 1, v => {
                    d.lblScale = v;
                    render();
                }, {commit: changed}),
                check('Показывать название на карте', d.showLabel !== false, v => {
                    cp('dsl' + d.id);
                    d.showLabel = v;
                    render();
                    changed();
                }),
                h('div', {class: 'row'}, btn('Новая раскладка', () => {
                    cp();
                    d.seed = Math.floor(Math.random() * 1e9);
                    d.angle = Math.random() * Math.PI;
                    ref();
                    buildCard();
                }), btn('Новое имя', () => {
                    cp();
                    d.name = districtName(S, Math.random, d.type, new Set(S.districts.map(x => x.name)));
                    computeLabel(d);
                    render();
                    buildCard();
                    changed();
                })),
                h('div', {class: 'row'}, btn('Сбросить метку', () => {
                    cp();
                    delete d.lblPos;
                    delete d.lblAng;
                    render();
                    changed();
                }), btn('PNG района', () => exportDistrictPNG(d)), del),
                h('p', {class: 'hint'}, 'Тяните квадратики, чтобы менять границы. Двойной клик по границе — добавить точку, по точке — удалить. Название можно перетащить.'));
        } else if (k === 'road') {
            c.append(head(o.kind === 'rail' ? 'Железная дорога' : 'Дорога'), textEl('Название', o.name || '', v => {
                    o.name = v;
                    render();
                    changed();
                }),
                selectEl('Тип', [['highway', 'Магистраль'], ['avenue', 'Проспект'], ['street', 'Улица'], ['rail', 'Железная дорога']], o.kind, v => {
                    cp('rk' + o.id);
                    o.kind = v;
                    render();
                    buildCard();
                    changed();
                }),
                slider('Положение названия', .05, .95, .01, o.lblT || .5, v => {
                    o.lblT = v;
                    render();
                }, {commit: changed}), h('div', {class: 'row'}, del),
                h('p', {class: 'hint'}, 'Тяните точки, чтобы менять путь. Двойной клик по линии — добавить точку.'));
        } else if (k === 'river') {
            c.append(head('Река'), textEl('Название', o.name || '', v => {
                o.name = v;
                changed();
            }), slider('Ширина', 3, 40, .5, o.width, v => {
                cp('rw' + o.id);
                o.width = v;
                S.rb = new Map();
                S.rivers.forEach(r => buildRiver(S, r));
                interact();
            }, {
                commit: () => {
                    finalizeAll(S);
                    changed();
                    render();
                }
            }), h('div', {class: 'row'}, del));
        } else if (k === 'label') {
            c.append(head(o.kind === 'street' ? 'Название улицы' : 'Надпись'), textEl('Текст', o.text, v => {
                    o.text = v;
                    render();
                    changed();
                }),
                slider('Размер', 4, 60, .5, o.size, v => {
                    cp('ls' + o.id);
                    o.size = v;
                    render();
                }, {commit: changed}),
                o.kind === 'point' ? slider('Поворот', -90, 90, 1, Math.round((o.ang || 0) * 180 / Math.PI), v => {
                    cp('la' + o.id);
                    o.ang = v * Math.PI / 180;
                    render();
                }, {commit: changed, fmt: v => v + '°'}) : null,
                h('div', {class: 'row'}, btn('Другое имя', () => {
                    cp();
                    o.text = streetName(S, Math.random);
                    render();
                    buildCard();
                    changed();
                }), o.kind === 'street' ? btn('PNG улицы', () => exportLabelPNG(o)) : null, del));
        } else if (k === 'icon') {
            c.append(head(ICON_NAMES[o.type] || 'Значок'),
                selectEl('Тип', Object.keys(ICON_NAMES).map(t => [t, ICON_NAMES[t]]), o.type, v => {
                    cp('it' + o.id);
                    o.type = v;
                    render();
                    changed();
                }),
                SPECIAL_ICONS[o.type] ? textEl('Название', o.name || '', v => {
                    o.name = v;
                    render();
                    changed();
                }) : null,
                SPECIAL_ICONS[o.type] ? check('Показывать подпись', o.showLabel !== false, v => {
                    o.showLabel = v;
                    render();
                    changed();
                }) : null,
                slider('Размер', 10, 120, 1, o.size || 30, v => {
                    cp('is' + o.id);
                    o.size = v;
                    render();
                }, {commit: changed}),
                slider('Поворот', -180, 180, 1, Math.round((o.ang || 0) * 180 / Math.PI), v => {
                    cp('ia' + o.id);
                    o.ang = v * Math.PI / 180;
                    render();
                }, {commit: changed, fmt: v => v + '°'}),
                SPECIAL_ICONS[o.type] ? h('div', {class: 'row'}, btn('Новое имя', () => {
                    cp();
                    o.name = objectName(S, Math.random, 'special', o.type);
                    render();
                    buildCard();
                    changed();
                })) : null,
                h('div', {class: 'row'}, del));
        } else if (k === 'green' || k === 'waste') {
            const isPark = k === 'green';
            c.append(head(isPark ? 'Зелёная зона' : 'Свалка'),
                textEl('Название', o.name || '', v => {
                    o.name = v;
                    render();
                    changed();
                }),
                check('Показывать подпись', o.showLabel !== false, v => {
                    o.showLabel = v;
                    render();
                    changed();
                }),
                slider('Размер', 10, 120, 1, Math.round(o.r), v => {
                    cp('br' + o.id);
                    o.r = v;
                    render();
                }, {commit: changed}),
                h('div', {class: 'row'},
                    btn('Новое имя', () => {
                        cp();
                        o.name = objectName(S, Math.random, isPark ? 'park' : 'waste');
                        render();
                        buildCard();
                        changed();
                    }),
                    del));
        }
    }

    function refreshDistrict(d) {
        const S = app.S;
        d.raw = genDistrictRaw(d, S);
        computeLabel(d);
        finalizeAll(S);
        changed();
        render();
    }

    function deleteSel() {
        const s = app.sel, S = app.S;
        if (!s) return;
        pushUndo();
        const rm = (arr) => {
            const i = arr.findIndex(o => o.id === s.id);
            if (i >= 0) arr.splice(i, 1);
        };
        if (s.kind === 'district') {
            rm(S.districts);
            finalizeAll(S);
        } else if (s.kind === 'river') {
            rm(S.rivers);
            finalizeAll(S);
        } else if (s.kind === 'road') {
            rm(S.roads);
            finRoads(S);
        } else if (s.kind === 'label') rm(S.labels); else if (s.kind === 'icon') rm(S.icons); else if (s.kind === 'green') rm(S.green); else if (s.kind === 'waste') rm(S.waste);
        app.sel = null;
        buildCard();
        changed();
        render();
    }

    /* ---------- вкладка: генерация ---------- */
    async function doGenerate() {
        setBusy('Генерация города…');
        await tick();
        await tick();
        const old = app.S;
        if (old) pushUndo();
        let S;
        try {
            S = generateWorld(app.gen);
        } catch (e) {
            console.error(e);
            setBusy(null);
            toast('Не удалось сгенерировать: ' + e.message);
            return;
        }
        if (old) {
            S.pal = old.pal;
            S.style = old.style;
            S.layers = old.layers;
            S.name = old.name || '';
        }
        app.S = S;
        autoStreetLabels(S, mulberry32(S.seed + 7), {metropolis: 26, city: 18, village: 7}[S.preset]);
        app.sel = null;
        app.draft = null;
        updateDrawbar();
        $('cityName').value = S.name;
        fit();
        buildPanel();
        setBusy(null);
        render();
        changed();
    }

    function tabGen(b) {
        const g = app.gen;
        const seg = h('div', {class: 'seg', role: 'group', 'aria-label': 'Тип поселения'});
        Object.keys(PRESETS).forEach(k => seg.append(h('button', {
            class: 'segb' + (g.preset === k ? ' on' : ''),
            onclick: () => {
                g.preset = k;
                g.sep = PRESETS[k].sep;
                g.nd = PRESETS[k].nd;
                g.farm = PRESETS[k].farm;
                g.targetPop = PRESETS[k].pop;
                buildPanel();
            }
        }, PRESETS[k].name)));
        const seed = h('input', {type: 'number', value: g.seed, 'aria-label': 'Зерно генерации'});
        seed.addEventListener('input', () => {
            g.seed = Math.abs(parseInt(seed.value) || 0);
        });
        const popFmt = v => v.toLocaleString('ru-RU') + ' чел.';
        b.append(sec('Тип поселения', seg,
                selectEl('Местность', [['coast', 'Побережье'], ['bay', 'Бухта'], ['river', 'Река через город'], ['lake', 'Озеро'], ['inland', 'Равнина без воды']], g.terrain, v => {
                    g.terrain = v;
                    buildPanel();
                }),
                selectEl('Форма города', Object.entries(CITY_SHAPES).map(([k, v]) => [k, v.n]), g.cityShape, v => {
                    g.cityShape = v;
                }),
                (g.terrain === 'coast' || g.terrain === 'bay') ? selectEl('Где море', [['random', 'Случайно'], ['right', 'Справа'], ['left', 'Слева'], ['top', 'Сверху'], ['bottom', 'Снизу']], g.seaSide, v => {
                    g.seaSide = v;
                }) : null,
                slider('Горные хребты', 0, 3, 1, g.mountains, v => {
                    g.mountains = v;
                }), slider('Реки', 0, 3, 1, g.rivers, v => {
                    g.rivers = v;
                }),
                slider('Размер квартала', 10, 40, 1, g.sep, v => {
                    g.sep = v;
                }), slider('Число районов', 1, 14, 1, g.nd, v => {
                    g.nd = v;
                }), slider('Поля вокруг', 0, 60, 1, g.farm, v => {
                    g.farm = v;
                }),
                slider('Целевое население', 500, 3000000, 500, g.targetPop, v => {
                    g.targetPop = v;
                }, {fmt: popFmt}),
                h('label', {class: 'fld'}, h('span', {class: 'fl'}, 'Зерно (одно и то же зерно — тот же город)'), h('div', {class: 'row tight'}, seed, btn('Случайное', () => {
                    g.seed = Math.floor(Math.random() * 1e9);
                    buildPanel();
                }))),
                btn('Сгенерировать', doGenerate, 'primary wide')),
            sec('Население',
                h('p', {class: 'hint'}, 'Целевое — желаемое. Фактическое зависит от площади районов и их типов: если площади не хватает, город получится меньше.'),
                h('p', {class: 'hint'}, 'На карте: ' + (app.S ? (app.S.totalPop || 0).toLocaleString('ru-RU') : 0) + ' чел. (цель ' + (app.S ? (app.S.targetPop || 0) : 0).toLocaleString('ru-RU') + ')'),
                app.S ? btn('Применить к текущему городу', () => {
                    pushUndo();
                    allocatePopulation(app.S, g.targetPop);
                    finalizeAll(app.S);
                    changed();
                    render();
                    buildPanel();
                }, 'wide') : null),
            sec('Быстрые действия',
                h('div', {class: 'row'}, btn('Пересобрать улицы', async () => {
                    setBusy('Пересборка улиц…');
                    await tick();
                    pushUndo();
                    regenStreets(app.S, true);
                    setBusy(null);
                    changed();
                    render();
                }), btn('Новые названия районов', () => {
                    pushUndo();
                    const used = new Set();
                    app.S.districts.forEach(d => {
                        d.name = districtName(app.S, Math.random, d.type, used);
                        computeLabel(d);
                    });
                    changed();
                    render();
                })),
                h('p', {class: 'hint'}, 'Генерация заменяет всю карту, но цвета и стиль сохраняются. Любое действие можно отменить (Ctrl+Z).')));
    }

    /* ---------- вкладка: ландшафт ---------- */
    function tabLand(b) {
        const S = app.S, LY = S.layers, br = app.brush;
        b.append(sec('Кисть ландшафта',
                h('p', {class: 'hint'}, 'Выберите слева «Море», «Суша», «Горы», «Равнина» или «Сгладить» и рисуйте по карте. Так создаются моря, заливы, побережья и хребты.'),
                slider('Радиус кисти', 10, 300, 1, br.r, v => {
                    br.r = v;
                    render();
                }), slider('Сила', .1, 1, .05, br.k, v => {
                    br.k = v;
                }),
                h('div', {class: 'row'}, btn('Убрать всю воду', () => {
                    pushUndo();
                    S.water.fill(0);
                    finalizeAll(S);
                    changed();
                    render();
                }), btn('Убрать горы', () => {
                    pushUndo();
                    S.height.fill(0);
                    finalizeAll(S);
                    changed();
                    render();
                }))),
            sec('Реки', slider('Ширина новой реки', 3, 40, .5, app.opts.riverW, v => {
                app.opts.riverW = v;
            }), btn('Нарисовать реку', () => setTool('river'), 'wide')),
            sec('Слои', ...[['water', 'Море и побережье'], ['mountains', 'Горы'], ['rivers', 'Реки'], ['farm', 'Поля'], ['parks', 'Парки'], ['waste', 'Свалки'], ['buildings', 'Здания'], ['objectNames', 'Подписи объектов']].map(([k, t]) => check(t, LY[k], v => {
                LY[k] = v;
                render();
                changed();
            }))));
    }

    /* ---------- вкладка: город ---------- */
    function tabCity(b) {
        const S = app.S, o = app.opts, LY = S.layers;
        const list = (arr, kind, name) => h('div', {class: 'list'}, arr.map(x => h('button', {
                class: 'li' + (app.sel && app.sel.kind === kind && app.sel.id === x.id ? ' on' : ''),
                onclick: () => {
                    select({kind, id: x.id});
                    buildPanel();
                    const p = kind === 'district' ? polyCentroid(x.poly) : null;
                }
            },
            kind === 'district' ? h('i', {class: 'chip', style: 'background:' + dcol(S, x)}) : null, name(x))));
        b.append(sec('Новый район', selectEl('Тип', Object.keys(TYPES).map(t => [t, TYPES[t].n]), o.distType, v => {
                    o.distType = v;
                }), btn('Нарисовать район', () => setTool('district'), 'wide'),
                h('p', {class: 'hint'}, 'Новый район перекрывает старые: улицы под ним пересоздаются заново.')),
            sec('Районы (' + S.districts.length + ')', list(S.districts, 'district', d => d.name + ' · ' + TYPES[d.type].n)),
            sec('Дороги и рельсы', selectEl('Тип новой дороги', [['highway', 'Магистраль'], ['avenue', 'Проспект'], ['street', 'Улица']], o.roadKind, v => {
                    o.roadKind = v;
                }),
                h('div', {class: 'row'}, btn('Нарисовать дорогу', () => setTool('road')), btn('Нарисовать рельсы', () => setTool('rail'))),
                list(S.roads, 'road', r => (r.kind === 'rail' ? 'Ж/д · ' : r.kind === 'highway' ? 'Магистраль · ' : r.kind === 'avenue' ? 'Проспект · ' : 'Улица · ') + (r.name || 'без названия'))),
            sec('Особые здания',
                selectEl('Тип объекта', ['monument', 'capitol', 'gov', 'temple', 'stadium', 'landmark'].map(t => [t, ICON_NAMES[t]]), o.specialType, v => {
                    o.specialType = v;
                }),
                btn('Поставить объект', () => setTool('special'), 'wide'),
                h('p', {class: 'hint'}, 'Монумент — в центр/парк. Капитолий — в центр. Правительство — в центр/деловой/технопарк. Храм — в жилой/пригород/центр. Стадион — в жилой/пригород/технопарк. Достопримечательность — почти везде.')),
            sec('Значки', selectEl('Тип значка', ['anchor', 'ship', 'poi', 'tower', 'station'].map(t => [t, ICON_NAMES[t]]), o.iconType, v => {
                o.iconType = v;
            }), btn('Поставить значок', () => setTool('icon'), 'wide')),
            sec('Кисти объектов',
                h('p', {class: 'hint'}, 'Парк — рисовать зелёные зоны в любом месте. Свалка — рисовать пустыри и полигоны.'),
                h('div', {class: 'row'}, btn('Кисть «Парк»', () => setTool('park')), btn('Кисть «Свалка»', () => setTool('waste'))),
                h('div', {class: 'row'},
                    btn('Убрать все парки', () => {
                        if (!app.S.green.length) return;
                        pushUndo();
                        app.S.green = [];
                        changed();
                        render();
                        toast('Парки удалены');
                    }),
                    btn('Убрать все свалки', () => {
                        if (!app.S.waste.length) return;
                        pushUndo();
                        app.S.waste = [];
                        changed();
                        render();
                        toast('Свалки удалены');
                    }))),
            sec('Видимость слоёв',
                ...[['streets', 'Улицы'], ['boundaries', 'Границы районов'], ['roads', 'Дороги'], ['rails', 'Рельсы'], ['icons', 'Значки'], ['parks', 'Парки и зелень'], ['waste', 'Свалки']].map(([k, t]) => check('Показывать: ' + t, LY[k], v => {
                    LY[k] = v;
                    render();
                    changed();
                }))));
    }

    /* ---------- регенерация всех имён ---------- */
    function regenAllNames(S, rngSeed) {
        const rng = mulberry32((rngSeed || ((Date.now() ^ S.seed) >>> 0)) >>> 0);
        const used = new Set();
        for (const d of S.districts) {
            d.name = districtName(S, rng, d.type, used);
            computeLabel(d);
        }
        for (const r of S.rivers) r.name = riverName(S, rng);
        for (const r of S.roads) {
            if (r.kind === 'rail') r.name = 'Линия ' + rint(rng, 1, 99);
            else if (r.kind === 'highway') r.name = pick(rng, ['Магистраль', 'Трасса', 'Шоссе']) + ' ' + rint(rng, 1, 99);
            else if (r.kind === 'avenue') r.name = streetName(S, rng);
        }
        for (const l of S.labels) if (l.kind === 'street' && l.auto) l.text = streetName(S, rng);
        // 5. Объекты
        for (const e of S.green) e.name = objectName(S, rng, 'park') || 'Парк';
        for (const e of S.waste) e.name = objectName(S, rng, 'waste') || 'Свалка';
        for (const ic of S.icons) if (SPECIAL_ICONS[ic.type]) ic.name = objectName(S, rng, 'special', ic.type);
    }

    /* ---------- вкладка: названия ---------- */
    function tabNames(b) {
        const S = app.S;
        const lib = S.nameLib || NEON_LIB;
        const presetButtons = h('div', {class: 'pgrid'});
        Object.keys(NAME_LIBS).forEach(k => {
            const L = NAME_LIBS[k];
            presetButtons.append(h('button', {
                class: 'pbtn', title: L.name,
                onclick: () => {
                    pushUndo();
                    S.nameLib = clone(L);
                    regenAllNames(S);
                    changed();
                    buildPanel();
                    render();
                    toast('Библиотека «' + L.name + '» применена');
                }
            }, h('span', {class: 'chip', style: 'background:var(--acc2)'}), h('span', null, L.name)));
        });

        const saveBtn = btn('Сохранить библиотеку', () => {
            const blob = new Blob([JSON.stringify(S.nameLib, null, 2)], {type: 'application/json'});
            saveBlob((S.nameLib.id || 'lib') + '.json', blob);
        });
        const loadBtn = btn('Загрузить свою библиотеку', () => {
            const inp = document.createElement('input');
            inp.type = 'file';
            inp.accept = '.json,application/json';
            inp.addEventListener('change', e => {
                const f = e.target.files[0];
                if (!f) return;
                const r = new FileReader();
                r.onload = () => {
                    try {
                        const obj = JSON.parse(r.result);
                        const v = validateLib(obj);
                        if (!v.ok) {
                            toast('Библиотека не подходит: ' + v.err);
                            return;
                        }
                        pushUndo();
                        S.nameLib = obj;
                        regenAllNames(S);
                        changed();
                        buildPanel();
                        render();
                        toast('Библиотека «' + (obj.name || obj.id) + '» применена');
                    } catch (err) {
                        toast('Не удалось прочитать JSON');
                    }
                };
                r.readAsText(f);
            });
            inp.click();
        });

        const counts = Object.keys(lib.district && lib.district.types || {}).map(t => {
            const spec = lib.district.types[t];
            const total = (spec.patterns || []).length;
            return t + ': ' + total + ' патт.';
        }).join(' · ');
        const hasObj = ['park', 'waste', 'special'].map(k => lib[k] ? k + ' ✓' : k + ' —').join(' · ');

        b.append(sec('Активная библиотека',
                h('p', {class: 'hint'}, 'Источник названий для районов, улиц, рек и городов.'),
                h('p', {class: 'hint'}, 'Сейчас: «' + (lib.name || lib.id || 'без имени') + '»' + (lib.lang ? ' (' + lib.lang + ')' : '')),
                h('div', {class: 'row'}, btn('Перегенерировать все имена', () => {
                    pushUndo();
                    regenAllNames(S);
                    changed();
                    render();
                    toast('Все имена перегенерированы');
                }, 'primary'), btn('Регенерировать с новым зерном', () => {
                    pushUndo();
                    regenAllNames(S, Date.now());
                    changed();
                    render();
                }))),
            sec('Встроенные библиотеки', presetButtons),
            sec('Своя библиотека',
                h('div', {class: 'row'}, saveBtn, loadBtn),
                h('p', {class: 'hint'}, 'Своя библиотека — JSON-файл со словарями и паттернами. Формат: district, street, river, city. Подробнее — в документации.')),
            sec('Покрытие типов районов', h('p', {class: 'hint'}, counts || 'нет')),
            sec('Объекты', h('p', {class: 'hint'}, hasObj)),
            sec('Отдельные имена',
                btn('Случайное имя района', () => {
                    const t = pick(Math.random, Object.keys(TYPES));
                    toast(districtName(S, Math.random, t, new Set()));
                }),
                btn('Случайное имя улицы', () => {
                    toast(streetName(S, Math.random));
                }),
                btn('Случайное имя реки', () => {
                    toast(riverName(S, Math.random));
                })));
    }

    function validateLib(o) {
        if (!o || typeof o !== 'object') return {ok: false, err: 'не объект'};
        if (!o.district && !o.street && !o.river) return {ok: false, err: 'нет ни district, ни street, ни river'};
        const check = (spec, path) => {
            if (!spec.patterns) return {ok: false, err: 'нет ' + path + '.patterns'};
            for (const p of spec.patterns) {
                const str = Array.isArray(p) ? p[0] : p;
                const tokens = (str.match(/\{(\w+)\}/g) || []).map(t => t.slice(1, -1));
                for (const t of tokens) {
                    if (t === 'num') continue;
                    if (!Array.isArray(spec[t]) || !spec[t].length) return {
                        ok: false,
                        err: path + ': токен {' + t + '} не определён'
                    };
                }
            }
            return {ok: true};
        };
        if (o.street) {
            const r = check(o.street, 'street');
            if (!r.ok) return r;
        }
        if (o.river) {
            const r = check(o.river, 'river');
            if (!r.ok) return r;
        }
        if (o.city) {
            const r = check(o.city, 'city');
            if (!r.ok) return r;
        }
        if (o.park) {
            const r = check(o.park, 'park');
            if (!r.ok) return r;
        }
        if (o.waste) {
            const r = check(o.waste, 'waste');
            if (!r.ok) return r;
        }
        if (o.special) for (const k in o.special) {
            const r = check(o.special[k], 'special.' + k);
            if (!r.ok) return r;
        }
        if (o.district && o.district.types) {
            for (const t in o.district.types) {
                const r = check(o.district.types[t], 'district.types.' + t);
                if (!r.ok) return r;
            }
        }
        if (o.district && o.district.generic) {
            const r = check(o.district.generic, 'district.generic');
            if (!r.ok) return r;
        }
        return {ok: true};
    }

    /* ---------- вкладка: цвета ---------- */
    function tabCol(b) {
        const S = app.S, pal = S.pal, st = S.style;
        const presets = h('div', {class: 'pgrid'});
        Object.keys(PALETTES).forEach(k => {
            const P = PALETTES[k], sw = h('button', {
                class: 'pbtn', title: P.name, onclick: () => {
                    pushUndo();
                    S.pal = clone(P);
                    S._wc = null;
                    buildPanel();
                    render();
                    changed();
                }
            }, h('span', {
                class: 'sws',
                style: 'background:' + P.bg
            }, ...Object.values(P.types).slice(0, 6).map(c => h('i', {style: 'background:' + c}))), h('span', null, P.name));
            presets.append(sw);
        });
        const el = (k) => colorEl(COLOR_LABELS[k], pal[k], v => {
            cp('c' + k);
            pal[k] = v;
            if (k === 'water') S._wc = null;
            render();
            changed();
        });
        b.append(sec('Готовые палитры', presets),
            sec('Цвета элементов', h('div', {class: 'cgrid'}, Object.keys(COLOR_LABELS).map(el))),
            sec('Цвета типов районов', h('div', {class: 'cgrid'}, Object.keys(TYPES).map(t => colorEl(TYPES[t].n, pal.types[t], v => {
                cp('ct' + t);
                pal.types[t] = v;
                render();
                changed();
            })))),
            h('p', {class: 'hint'}, 'Цвет отдельного района меняется в его карточке — выберите район на карте.'),
            sec('Свечение и эффекты', slider('Неоновое свечение', 0, 2, .05, st.glow, v => {
                    st.glow = v;
                    render();
                }, {commit: changed}), slider('Толщина линий', .5, 2.5, .05, st.line, v => {
                    st.line = v;
                    render();
                }, {commit: changed}),
                slider('Подкраска районов', 0, .3, .01, st.tint, v => {
                    st.tint = v;
                    render();
                }, {commit: changed}), slider('Скан-линии', 0, 1, .05, st.scan, v => {
                    st.scan = v;
                    render();
                }, {commit: changed}),
                slider('Зерно плёнки', 0, 1, .05, st.grain, v => {
                    st.grain = v;
                    render();
                }, {commit: changed}), slider('Виньетка', 0, 1, .05, st.vignette, v => {
                    st.vignette = v;
                    render();
                }, {commit: changed})));
    }

    /* ---------- вкладка: подписи ---------- */
    function tabLab(b) {
        const S = app.S, LY = S.layers, st = S.style, o = app.opts;
        const ls = S.labels.filter(l => l.kind === 'street' || l.kind === 'point');
        b.append(sec('Показ', ...[['districtNames', 'Названия районов'], ['streetNames', 'Названия улиц и надписи'], ['roadNames', 'Названия магистралей и путей']].map(([k, t]) => check(t, LY[k], v => {
                    LY[k] = v;
                    render();
                    changed();
                })),
                selectEl('Шрифт', [['Exo 2', 'Exo 2 — техно'], ['Russo One', 'Russo One — плакатный'], ['Share Tech Mono', 'Share Tech Mono — моно']], st.labelFont, v => {
                    st.labelFont = v;
                    document.fonts.load('600 16px "' + v + '"').then(() => render());
                    changed();
                }),
                slider('Масштаб подписей', .5, 2.5, .05, st.labelScale, v => {
                    st.labelScale = v;
                    render();
                }, {commit: changed})),
            sec('Названия улиц', h('p', {class: 'hint'}, 'Инструмент «Улица» слева: кликните по любой улице — название ляжет вдоль неё и повторит изгиб. Подписи видны при достаточном приближении.'),
                slider('Сколько расставить', 5, 80, 1, o.autoCount, v => {
                    o.autoCount = v;
                }),
                h('div', {class: 'row'}, btn('Расставить названия', () => {
                    pushUndo();
                    const n = autoStreetLabels(S, mulberry32((Date.now() ^ 5) >>> 0), o.autoCount);
                    toast('Добавлено названий: ' + n);
                    buildPanel();
                    changed();
                    render();
                }), btn('Убрать все', () => {
                    pushUndo();
                    S.labels = [];
                    app.sel = null;
                    buildPanel();
                    changed();
                    render();
                })),
                h('div', {class: 'row'}, btn('Инструмент «Улица»', () => setTool('labelStreet')), btn('Свободный текст', () => setTool('labelPoint')))),
            sec('Список (' + ls.length + ')', h('div', {class: 'list'}, ls.slice(0, 200).map(l => h('button', {
                class: 'li' + (app.sel && app.sel.id === l.id ? ' on' : ''),
                onclick: () => {
                    select({kind: 'label', id: l.id});
                    const pt = l.kind === 'street' ? l.path[Math.floor(l.path.length / 2)] : [l.x, l.y];
                    const v = app.view;
                    v.tx = cw / 2 - pt[0] * v.s;
                    v.ty = chh / 2 - pt[1] * v.s;
                    buildPanel();
                    render();
                }
            }, l.text)))));
    }

    /* ---------- вкладка: экспорт ---------- */
    function pdfPlan() {
        const S = app.S, e = app.exp, P = PAPER[e.paper];
        let pw = P[0], ph = P[1];
        if (S.W > S.H) {
            const t = pw;
            pw = ph;
            ph = t;
        }
        const sc = Math.min((pw - 2 * e.margin) / S.W, (ph - 2 * e.margin) / S.H), dw = S.W * sc, dh = S.H * sc;
        let Wpx = Math.round(dw / 25.4 * e.dpi);
        if (Wpx > 15000) Wpx = 15000;
        const s = Wpx / S.W;
        return {pw, ph, dw, dh, Wpx, Hpx: Math.round(S.H * s), s};
    }

    function tabExp(b) {
        const S = app.S, e = app.exp, pl = pdfPlan(), sel = getSel(), isD = app.sel && app.sel.kind === 'district';
        const info = h('p', {class: 'hint'}, 'Страница ' + pl.pw + '×' + pl.ph + ' мм, карта ' + Math.round(pl.dw) + '×' + Math.round(pl.dh) + ' мм, растр ' + pl.Wpx + '×' + pl.Hpx + ' px (' + Math.round(pl.Wpx * pl.Hpx / 1e6) + ' Мп).');
        const upd = () => {
            buildPanel();
        };
        b.append(sec('PDF высокого разрешения',
                selectEl('Формат листа', Object.keys(PAPER).map(k => [k, k]), e.paper, v => {
                    e.paper = v;
                    upd();
                }),
                selectEl('Разрешение', [[100, '100 dpi — черновик'], [150, '150 dpi'], [200, '200 dpi'], [300, '300 dpi — печать']], e.dpi, v => {
                    e.dpi = +v;
                    upd();
                }),
                slider('Поля, мм', 0, 30, 1, e.margin, v => {
                    e.margin = v;
                }, {commit: upd}), check('Плашка с названием города', e.plate, v => {
                    e.plate = v;
                }), info,
                btn('Скачать PDF', exportPDF, 'primary wide')),
            sec('PNG',
                selectEl('Длинная сторона', [[2000, '2000 px'], [4000, '4000 px'], [6000, '6000 px'], [8000, '8000 px']], e.pngSize, v => {
                    e.pngSize = +v;
                }),
                check('Прозрачный фон (без эффектов плёнки)', e.transparent, v => {
                    e.transparent = v;
                }),
                btn('PNG текущего вида', exportView, 'wide'),
                btn('PNG всей карты', () => exportRect({
                    x0: 0,
                    y0: 0,
                    x1: S.W,
                    y1: S.H
                }, e.pngSize, fname('карта') + '.png'), 'wide'),
                btn('PNG рамки', exportFrame, 'wide' + (app.frame ? '' : ' off')), isD ? btn('PNG выбранного района', () => exportDistrictPNG(sel), 'wide') : null,
                h('div', {class: 'row'}, btn('Рамка для экспорта', () => setTool('frame')), app.frame ? btn('Сбросить рамку', () => {
                    app.frame = null;
                    buildPanel();
                    render();
                }) : null),
                h('p', {class: 'hint'}, 'Приблизьтесь к нужной улице или району и нажмите «PNG текущего вида» — линии и подписи будут так же чёткими, как на экране, в выбранном разрешении.')),
            sec('Проект',
                h('div', {class: 'row'}, btn('Сохранить проект', saveProject), btn('Загрузить проект', () => $('fileIn').click())),
                h('p', {class: 'hint'}, 'Проект хранит ландшафт, районы, дороги, подписи и цвета. Карта также автоматически сохраняется в браузере.')));
    }

    const fname = suf => (app.S.name || 'город').replace(/[^\p{L}\p{N}_-]+/gu, '_') + (suf ? '_' + suf : '');

    async function saveBlob(name, blob) {
        try {
            if (window.claude && window.claude.use) {
                const dl = await window.claude.use('downloads');
                if (dl) {
                    await dl.save({filename: name, data: blob});
                    toast('Готово: ' + name);
                    return;
                }
            }
        } catch (e) {
            if (e && e.code === 'declined') return;
            console.warn(e);
        }
        const a = document.createElement('a');
        a.href = URL.createObjectURL(blob);
        a.download = name;
        document.body.appendChild(a);
        a.click();
        a.remove();
        setTimeout(() => URL.revokeObjectURL(a.href), 4000);
        toast('Готово: ' + name);
    }

    async function exportRect(rect, long, name, sCssOverride) {
        const S = app.S;
        setBusy('Рендер PNG…');
        await tick();
        try {
            await document.fonts.ready;
        } catch (e) {
        }
        const w = rect.x1 - rect.x0, hh = rect.y1 - rect.y0;
        let outW, outH;
        if (w >= hh) {
            outW = long;
            outH = Math.round(long * hh / w);
        } else {
            outH = long;
            outW = Math.round(long * w / hh);
        }
        if (outW * outH > 60e6) {
            const k = Math.sqrt(60e6 / (outW * outH));
            outW = Math.floor(outW * k);
            outH = Math.floor(outH * k);
        }
        const s = outW / w, sCss = sCssOverride || 1000 / w, pxk = s / sCss, c = document.createElement('canvas');
        c.width = outW;
        c.height = outH;
        try {
            renderScene(c.getContext('2d'), S, {
                w: outW,
                h: outH,
                s,
                tx: -rect.x0 * s,
                ty: -rect.y0 * s,
                pxk,
                gx: 0,
                gy: 0,
                gw: outW,
                gh: outH
            }, {transparent: app.exp.transparent});
            const blob = await new Promise(r => c.toBlob(r, 'image/png'));
            setBusy(null);
            if (!blob) {
                toast('Не удалось создать PNG — уменьшите размер');
                return;
            }
            await saveBlob(name, blob);
        } catch (e) {
            setBusy(null);
            toast('Ошибка экспорта: ' + e.message);
        }
    }

    function exportView() {
        const v = app.view, x0 = -v.tx / v.s, y0 = -v.ty / v.s;
        exportRect({x0, y0, x1: x0 + cw / v.s, y1: y0 + chh / v.s}, app.exp.pngSize, fname('вид') + '.png', v.s);
    }

    function exportFrame() {
        const f = app.frame;
        if (!f) {
            toast('Сначала обведите рамку инструментом «Рамка»');
            return;
        }
        exportRect({
            x0: Math.min(f.x0, f.x1),
            y0: Math.min(f.y0, f.y1),
            x1: Math.max(f.x0, f.x1),
            y1: Math.max(f.y0, f.y1)
        }, app.exp.pngSize, fname('область') + '.png');
    }

    function exportDistrictPNG(d) {
        const bb = bboxOf(d.poly), m = Math.max(bb[2] - bb[0], bb[3] - bb[1]) * .06 + 10;
        exportRect({
            x0: bb[0] - m,
            y0: bb[1] - m,
            x1: bb[2] + m,
            y1: bb[3] + m
        }, app.exp.pngSize, fname(d.name.replace(/\s+/g, '_')) + '.png');
    }

    function exportLabelPNG(l) {
        const bb = bboxOf(l.path), pad = Math.max(l.size * 9, 90);
        let x0 = bb[0] - pad, x1 = bb[2] + pad, y0 = bb[1] - pad, y1 = bb[3] + pad;
        const w = x1 - x0, hh = y1 - y0, cx = (x0 + x1) / 2, cy = (y0 + y1) / 2;
        const W2 = Math.max(w, hh * 1.3), H2 = Math.max(hh, w / 1.3);
        exportRect({
            x0: cx - W2 / 2,
            y0: cy - H2 / 2,
            x1: cx + W2 / 2,
            y1: cy + H2 / 2
        }, app.exp.pngSize, fname(l.text.replace(/\s+/g, '_')) + '.png');
    }

    /* ---------- PDF ---------- */
    function buildPDF(page, bg, strips) {
        const enc = new TextEncoder(), chunks = [], offsets = [];
        let off = 0;
        const push = d => {
            const u = typeof d === 'string' ? enc.encode(d) : d;
            chunks.push(u);
            off += u.length;
        };
        const nImg = strips.length, total = 4 + nImg;
        push('%PDF-1.4\n%\xE2\xE3\xCF\xD3\n');
        offsets[1] = off;
        push('1 0 obj\n<< /Type /Catalog /Pages 2 0 R >>\nendobj\n');
        offsets[2] = off;
        push('2 0 obj\n<< /Type /Pages /Kids [3 0 R] /Count 1 >>\nendobj\n');
        const xo = strips.map((s, i) => '/Im' + i + ' ' + (5 + i) + ' 0 R').join(' ');
        offsets[3] = off;
        push('3 0 obj\n<< /Type /Page /Parent 2 0 R /MediaBox [0 0 ' + page.w.toFixed(2) + ' ' + page.h.toFixed(2) + '] /Resources << /XObject << ' + xo + ' >> >> /Contents 4 0 R >>\nendobj\n');
        let cs = 'q ' + bg.map(v => (v / 255).toFixed(4)).join(' ') + ' rg 0 0 ' + page.w.toFixed(2) + ' ' + page.h.toFixed(2) + ' re f Q\n';
        strips.forEach((s, i) => {
            cs += 'q ' + s.dw.toFixed(3) + ' 0 0 ' + s.dh.toFixed(3) + ' ' + s.x.toFixed(3) + ' ' + s.y.toFixed(3) + ' cm /Im' + i + ' Do Q\n';
        });
        offsets[4] = off;
        push('4 0 obj\n<< /Length ' + enc.encode(cs).length + ' >>\nstream\n' + cs + 'endstream\nendobj\n');
        strips.forEach((s, i) => {
            offsets[5 + i] = off;
            push((5 + i) + ' 0 obj\n<< /Type /XObject /Subtype /Image /Width ' + s.w + ' /Height ' + s.h + ' /ColorSpace /DeviceRGB /BitsPerComponent 8 /Filter /DCTDecode /Length ' + s.jpeg.length + ' >>\nstream\n');
            push(s.jpeg);
            push('\nendstream\nendobj\n');
        });
        const xr = off;
        let x = 'xref\n0 ' + (total + 1) + '\n0000000000 65535 f \n';
        for (let i = 1; i <= total; i++) x += String(offsets[i]).padStart(10, '0') + ' 00000 n \n';
        push(x + 'trailer\n<< /Size ' + (total + 1) + ' /Root 1 0 R >>\nstartxref\n' + xr + '\n%%EOF');
        return new Blob(chunks, {type: 'application/pdf'});
    }

    async function exportPDF() {
        const S = app.S, e = app.exp, pl = pdfPlan(), mmPt = 72 / 25.4;
        try {
            try {
                await document.fonts.ready;
            } catch (er) {
            }
            const c = document.createElement('canvas'), x = c.getContext('2d'),
                stripH = Math.max(64, Math.floor(14e6 / pl.Wpx / 8) * 8), n = Math.ceil(pl.Hpx / stripH), strips = [];
            const pxk = pl.Wpx / 1000, ptPx = pl.dw * mmPt / pl.Wpx, topPt = pl.ph * mmPt - e.margin * mmPt,
                leftPt = (pl.pw * mmPt - pl.dw * mmPt) / 2;
            for (let i = 0; i < n; i++) {
                setBusy('Рендер PDF: полоса ' + (i + 1) + ' из ' + n + '…');
                await tick();
                const y0 = i * stripH, hh = Math.min(stripH + (i < n - 1 ? 2 : 0), pl.Hpx - y0);
                c.width = pl.Wpx;
                c.height = hh;
                renderScene(x, S, {
                    w: pl.Wpx,
                    h: hh,
                    s: pl.s,
                    tx: 0,
                    ty: -y0,
                    pxk,
                    gx: 0,
                    gy: y0,
                    gw: pl.Wpx,
                    gh: pl.Hpx
                }, {plate: e.plate});
                const blob = await new Promise(r => c.toBlob(r, 'image/jpeg', .93));
                if (!blob) throw new Error('не хватило памяти — понизьте разрешение или формат');
                const jpeg = new Uint8Array(await blob.arrayBuffer());
                strips.push({
                    jpeg,
                    w: pl.Wpx,
                    h: hh,
                    dw: pl.Wpx * ptPx,
                    dh: hh * ptPx,
                    x: leftPt,
                    y: topPt - (y0 + hh) * ptPx
                });
            }
            setBusy('Сборка PDF…');
            await tick();
            const pdf = buildPDF({w: pl.pw * mmPt, h: pl.ph * mmPt}, hex2rgb(S.pal.bg), strips);
            setBusy(null);
            await saveBlob(fname() + '.pdf', pdf);
        } catch (er) {
            setBusy(null);
            console.error(er);
            toast('Ошибка PDF: ' + er.message);
        }
    }

    /* ---------- проект ---------- */
    async function saveProject() {
        const blob = new Blob([JSON.stringify(toProject(app.S))], {type: 'application/json'});
        await saveBlob(fname() + '.json', blob);
    }

    function loadProjectText(txt) {
        try {
            const S = fromProject(JSON.parse(txt));
            pushUndoRaw();
            app.S = S;
            if (S.gen) Object.assign(app.gen, S.gen);
            app.sel = null;
            app.draft = null;
            updateDrawbar();
            $('cityName').value = S.name;
            fit();
            buildPanel();
            render();
            changed();
            toast('Проект загружен');
        } catch (e) {
            console.error(e);
            toast('Не удалось прочитать проект');
        }
    }

    function pushUndoRaw() {
        if (app.S) {
            app.undo.push(snapshot(app.S));
            app.redo.length = 0;
            syncUndo();
        }
    }

    /* ---------- запуск ---------- */
    async function init() {
        buildTools();
        $('bUndo').onclick = undo;
        $('bRedo').onclick = redo;
        $('bFit').onclick = () => {
            fit();
            render();
        };

        // Горизонтальная прокрутка вкладок колесом мыши и трекпадом
        const tabsEl = $('tabs');
        tabsEl.addEventListener('wheel', e => {
            const dx = e.deltaX || 0, dy = e.deltaY || 0;
            const use = Math.abs(dx) > Math.abs(dy) ? dx : dy;
            if (!use) return;
            const canL = tabsEl.scrollLeft > 0;
            const canR = tabsEl.scrollLeft + tabsEl.clientWidth < tabsEl.scrollWidth - 1;
            if ((use < 0 && !canL) || (use > 0 && !canR)) return; // некуда скроллить — не мешаем дефолту
            e.preventDefault();
            tabsEl.scrollLeft += use;
            updateTabsScroll();
        }, {passive: false});
        tabsEl.addEventListener('scroll', updateTabsScroll, {passive: true});
        window.addEventListener('resize', () => {
            updateTabsScroll();
            const a = tabsEl.querySelector('.tab.on');
            if (a) {
                const tL = tabsEl.scrollLeft, tR = tL + tabsEl.clientWidth;
                if (a.offsetLeft < tL || a.offsetLeft + a.offsetWidth > tR) a.scrollIntoView({
                    inline: 'nearest',
                    block: 'nearest'
                });
            }
        });
        $('bGen').onclick = () => {
            app.gen.seed = Math.floor(Math.random() * 1e9);
            doGenerate();
        };
        $('dbDone').onclick = finishDraft;
        $('dbUndo').onclick = () => {
            if (app.draft) {
                app.draft.pts.pop();
                updateDrawbar();
                render();
            }
        };
        $('dbCancel').onclick = cancelDraft;
        $('cityName').addEventListener('input', e => {
            if (app.S) {
                app.S.name = e.target.value;
                changed();
            }
        });
        $('fileIn').addEventListener('change', e => {
            const f = e.target.files[0];
            if (!f) return;
            const r = new FileReader();
            r.onload = () => loadProjectText(r.result);
            r.readAsText(f);
            e.target.value = '';
        });
        new ResizeObserver(resize).observe($('stage'));
        resize();
        try {
            await Promise.race([Promise.all(['600 16px "Exo 2"', '700 16px "Exo 2"', '800 16px "Exo 2"', '16px "Russo One"', '16px "Share Tech Mono"'].map(f => document.fonts.load(f))), new Promise(r => setTimeout(r, 2500))]);
        } catch (e) {
        }
        let ok = false;
        try {
            const raw = localStorage.getItem('neon-city-autosave');
            if (raw) {
                app.S = fromProject(JSON.parse(raw));
                if (app.S.gen) Object.assign(app.gen, app.S.gen);
                if (!app.gen.cityShape) app.gen.cityShape = 'round';
                $('cityName').value = app.S.name;
                fit();
                buildPanel();
                ok = true;
            }
        } catch (e) {
            app.S = null;
        }
        if (!ok) {
            app.S = null;
            await doGenerate();
        }
        document.fonts.ready.then(() => render());
        syncUndo();
        render();
    }

    init();
})();