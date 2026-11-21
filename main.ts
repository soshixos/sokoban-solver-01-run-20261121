// Sokoban solver: push-optimal, room by room.
//
// A level is a hallway with rooms off it; a box pushed out of a room can
// never come back, so each room is solved on its own and the optima add up.
// Each room is solved by breadth-first search over pushes (fewest pushes
// first, so the first solution found is push-optimal), with two safe
// prunings: a box may only sit on a square from which some sequence of
// pushes reaches a goal, and no frozen 2x2 block of walls and boxes may
// form with a box off its goal.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

const IN = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const OUT = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const DX = [0, 0, -1, 1];
const DY = [-1, 1, 0, 0];
const STEP = ['u', 'd', 'l', 'r'];
const PUSH = ['U', 'D', 'L', 'R'];
const MAX = 300000;

type Board = {
  w: number;
  h: number;
  wall: Uint8Array;
  goals: number[];
  boxes: number[];
  player: number;
};

function parse(text: string): Board {
  const rows = text.split('\n').filter((r) => r.length > 0);
  const h = rows.length;
  const w = Math.max(...rows.map((r) => r.length));
  const wall = new Uint8Array(w * h).fill(1);
  const goals: number[] = [];
  const boxes: number[] = [];
  let player = -1;
  rows.forEach((row, y) => {
    for (let x = 0; x < row.length; x++) {
      const i = y * w + x;
      const ch = row[x]!;
      if (ch === '#') continue;
      wall[i] = 0;
      if (ch === '.' || ch === '*' || ch === '+') goals.push(i);
      if (ch === '$' || ch === '*') boxes.push(i);
      if (ch === '@' || ch === '+') player = i;
    }
  });
  for (let y = 0; y < h; y++)
    for (let x = 0; x < w; x++)
      if (x === 0 || y === 0 || x === w - 1 || y === h - 1) wall[y * w + x] = 1;
  return { w, h, wall, goals, boxes: boxes.sort((a, b) => a - b), player };
}

// Squares a lone box can be pushed from onto some goal, found by pulling
// boxes back from the goals: a box on y can be pushed to x when the player
// can stand on the far side of y.
function liveCells(b: Board, wall: Uint8Array, goals: number[]): Uint8Array {
  const live = new Uint8Array(b.w * b.h);
  const q = [...goals];
  for (const g of goals) live[g] = 1;
  for (let qi = 0; qi < q.length; qi++) {
    const x = q[qi]!;
    for (let k = 0; k < 4; k++) {
      const d = DY[k]! * b.w + DX[k]!;
      const y = x - d;
      if (!wall[y] && !wall[y - d] && !live[y]) {
        live[y] = 1;
        q.push(y);
      }
    }
  }
  return live;
}

// Flood the player's region from `from` over open floor (walls and boxes
// block), stamping it in `seen`; returns the region's lowest square.
function reach(
  b: Board,
  wall: Uint8Array,
  occ: Uint8Array,
  from: number,
  seen: Int32Array,
  stamp: number,
  stack: Int32Array,
): number {
  let low = from;
  let n = 0;
  stack[n++] = from;
  seen[from] = stamp;
  while (n > 0) {
    const p = stack[--n]!;
    if (p < low) low = p;
    for (let k = 0; k < 4; k++) {
      const q = p + DY[k]! * b.w + DX[k]!;
      if (!wall[q] && !occ[q] && seen[q] !== stamp) {
        seen[q] = stamp;
        stack[n++] = q;
      }
    }
  }
  return low;
}

// Whether the box just pushed to `t` is stuck in a frozen 2x2 block of
// walls and boxes holding a box off its goal.
function frozen(
  b: Board,
  wall: Uint8Array,
  occ: Uint8Array,
  goal: Uint8Array,
  t: number,
): boolean {
  const w = b.w;
  for (const a of [t, t - 1, t - w, t - w - 1]) {
    const c = a + w;
    const d = c + 1;
    const e = a + 1;
    if (!(wall[a] || occ[a]) || !(wall[e] || occ[e]) || !(wall[c] || occ[c]) || !(wall[d] || occ[d])) continue;
    if ((occ[a] && !goal[a]) || (occ[e] && !goal[e]) || (occ[c] && !goal[c]) || (occ[d] && !goal[d])) return true;
  }
  return false;
}

// Shortest walk from `from` to `to` around walls and boxes, lower letters.
function walkTo(
  b: Board,
  wall: Uint8Array,
  occ: Uint8Array,
  from: number,
  to: number,
): string | null {
  if (from === to) return '';
  const prev = new Int32Array(b.w * b.h).fill(-1);
  const how = new Array<string>(b.w * b.h);
  const q = [from];
  prev[from] = from;
  for (let qi = 0; qi < q.length; qi++) {
    const p = q[qi]!;
    if (p === to) break;
    for (let k = 0; k < 4; k++) {
      const nq = p + DY[k]! * b.w + DX[k]!;
      if (wall[nq] || occ[nq] || prev[nq] !== -1) continue;
      prev[nq] = p;
      how[nq] = STEP[k]!;
      q.push(nq);
    }
  }
  if (prev[to] === -1) return null;
  let s = '';
  for (let p = to; p !== from; p = prev[p]!) s = how[p]! + s;
  return s;
}

const keyOf = (bs: number[], low: number): string => `${low}:${bs.join(',')}`;

// Push-optimal solution for the movable `boxes0` (other boxes already
// folded into `wall`): {pushes, moves} or null when the search gives up.
// `forbid` marks squares a box may never be pushed onto (the hallway).
function pushSolve(
  b: Board,
  wall: Uint8Array,
  goals: number[],
  boxes0: number[],
  player0: number,
  forbid: Uint8Array,
): { pushes: number; moves: string } | null {
  const size = b.w * b.h;
  const goal = new Uint8Array(size);
  for (const g of goals) goal[g] = 1;
  const live = liveCells(b, wall, goals);
  const occ = new Uint8Array(size);
  const seen = new Int32Array(size);
  const mark = new Int32Array(size);
  const stack = new Int32Array(size);
  let stamp = 0;
  const solved = (bs: number[]): boolean => bs.every((x) => goal[x]);
  if (boxes0.some((x) => !live[x])) return null;
  const sBoxes: number[][] = [boxes0.slice()];
  const sPlayer: number[] = [player0];
  const parent: number[] = [-1];
  const pushFrom: number[] = [-1];
  const pushDir: number[] = [-1];
  const index = new Map<string, number>();
  for (const x of boxes0) occ[x] = 1;
  index.set(keyOf(boxes0, reach(b, wall, occ, player0, seen, ++stamp, stack)), 0);
  for (const x of boxes0) occ[x] = 0;
  let found = solved(boxes0) ? 0 : -1;
  for (let head = 0; found < 0 && head < sBoxes.length; head++) {
    const boxes = sBoxes[head]!;
    for (const x of boxes) occ[x] = 1;
    reach(b, wall, occ, sPlayer[head]!, seen, ++stamp, stack);
    const here = stamp;
    for (let bi = 0; bi < boxes.length && found < 0; bi++) {
      const box = boxes[bi]!;
      for (let k = 0; k < 4; k++) {
        const d = DY[k]! * b.w + DX[k]!;
        const t = box + d;
        if (seen[box - d] !== here || wall[t] || occ[t] || !live[t] || forbid[t]) continue;
        occ[box] = 0;
        occ[t] = 1;
        const frz = frozen(b, wall, occ, goal, t);
        let nk: string | null = null;
        let nb: number[] | null = null;
        if (!frz) {
          nb = boxes.slice();
          nb[bi] = t;
          nb.sort((x, y) => x - y);
          nk = keyOf(nb, reach(b, wall, occ, box, mark, ++stamp, stack));
        }
        occ[t] = 0;
        occ[box] = 1;
        if (frz || nk === null || index.has(nk)) continue;
        if (sBoxes.length >= MAX) {
          for (const x of boxes) occ[x] = 0;
          return null;
        }
        index.set(nk, sBoxes.length);
        sBoxes.push(nb!);
        sPlayer.push(box);
        parent.push(head);
        pushFrom.push(box);
        pushDir.push(k);
        if (solved(nb!)) {
          found = sBoxes.length - 1;
          break;
        }
      }
    }
    for (const x of boxes) occ[x] = 0;
  }
  if (found < 0) return null;
  const chain: number[] = [];
  for (let s = found; s > 0; s = parent[s]!) chain.push(s);
  chain.reverse();
  let moves = '';
  let player = player0;
  let boxes = boxes0.slice();
  for (const s of chain) {
    const nb = sBoxes[s]!;
    const from = pushFrom[s]!;
    const k = pushDir[s]!;
    const d = DY[k]! * b.w + DX[k]!;
    for (const x of boxes) occ[x] = 1;
    const w = walkTo(b, wall, occ, player, from - d);
    for (const x of boxes) occ[x] = 0;
    if (w === null) return null;
    moves += w + PUSH[k]!;
    player = from;
    boxes = nb;
  }
  return { pushes: chain.length, moves };
}

// The hallway row's dead squares, cut out of the floor; each remaining
// floor part holding boxes is a room.
function roomsOf(
  b: Board,
  live: Uint8Array,
): { boxes: number[]; goals: number[] }[] | null {
  const row = Math.floor(b.player / b.w);
  const cut = new Uint8Array(b.w * b.h);
  for (let x = 0; x < b.w; x++) {
    const i = row * b.w + x;
    if (!b.wall[i] && !live[i]) cut[i] = 1;
  }
  if (b.boxes.some((x) => cut[x])) return null;
  const comp = new Int32Array(b.w * b.h).fill(-1);
  const rooms: { boxes: number[]; goals: number[] }[] = [];
  for (let s = 0; s < b.w * b.h; s++) {
    if (b.wall[s] || cut[s] || comp[s] >= 0) continue;
    const cells = [s];
    comp[s] = rooms.length;
    for (let k = 0; k < cells.length; k++) {
      const p = cells[k]!;
      for (let d = 0; d < 4; d++) {
        const q = p + DY[d]! * b.w + DX[d]!;
        if (!b.wall[q] && !cut[q] && comp[q] < 0) {
          comp[q] = rooms.length;
          cells.push(q);
        }
      }
    }
    rooms.push({ boxes: [], goals: [] });
  }
  for (const x of b.boxes) rooms[comp[x]!]!.boxes.push(x);
  for (const g of b.goals) {
    if (comp[g] < 0) return null;
    rooms[comp[g]!]!.goals.push(g);
  }
  if (rooms.some((r) => r.boxes.length !== r.goals.length)) return null;
  return rooms.filter((r) => r.boxes.length > 0);
}

function endOf(w: number, from: number, moves: string): number {
  let p = from;
  for (const ch of moves.toLowerCase()) p += ch === 'u' ? -w : ch === 'd' ? w : ch === 'l' ? -1 : 1;
  return p;
}

function solveLevel(text: string): string {
  const b = parse(text);
  const live = liveCells(b, b.wall, b.goals);
  const empty = new Uint8Array(b.w * b.h);
  const rooms = roomsOf(b, live);
  if (rooms === null) {
    const r = pushSolve(b, b.wall, b.goals, b.boxes, b.player, empty);
    return r ? r.moves : '';
  }
  const row = Math.floor(b.player / b.w);
  const cut = new Uint8Array(b.w * b.h);
  for (let x = 0; x < b.w; x++) {
    const i = row * b.w + x;
    if (!b.wall[i] && !live[i]) cut[i] = 1;
  }
  let player = b.player;
  let moves = '';
  const cur: number[][] = rooms.map((r) => r.boxes.slice());
  for (let ri = 0; ri < rooms.length; ri++) {
    const room = rooms[ri]!;
    const wall2 = b.wall.slice();
    for (let oj = 0; oj < rooms.length; oj++) {
      if (oj === ri) continue;
      for (const x of cur[oj]!) wall2[x] = 1;
    }
    const r = pushSolve(b, wall2, room.goals, cur[ri]!, player, cut);
    if (r === null) {
      const whole = pushSolve(b, b.wall, b.goals, b.boxes, b.player, empty);
      return whole ? whole.moves : '';
    }
    moves += r.moves;
    player = endOf(b.w, player, r.moves);
    cur[ri] = room.goals.slice();
  }
  return moves;
}

for (const id of readdirSync(IN).sort()) {
  const moves = solveLevel(readFileSync(join(IN, id, 'level.txt'), 'utf8'));
  mkdirSync(join(OUT, id), { recursive: true });
  writeFileSync(join(OUT, id, 'solution.txt'), `${moves}\n`);
}
