// Tiny stack VM: a faithful interpreter of make.fun's tiny stack ISA v1
// (kit: program/generator/subject/ISA.md, reference vm.mjs). Rules in the
// reference's order: step limit, pc bounds, unknown opcode, cut-off
// immediate, stack under/overflow, then the instruction's own traps.
// Values wrap 32-bit; MUL is Math.imul; DIVU/MODU/LTU are unsigned;
// shifts mask to 5 bits; traps keep output written before them.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';

// [opcode, immediate bytes, pops, pushes] for every opcode in the ISA.
const OPS: [number, number, number, number][] = [
  [0x00, 0, 0, 0], [0x01, 1, 0, 1], [0x02, 4, 0, 1], [0x03, 0, 1, 0],
  [0x04, 0, 1, 2], [0x05, 0, 2, 2], [0x06, 0, 2, 3], [0x07, 0, 3, 3],
  [0x10, 0, 2, 1], [0x11, 0, 2, 1], [0x12, 0, 2, 1], [0x13, 0, 2, 1],
  [0x14, 0, 2, 1], [0x15, 0, 2, 1], [0x16, 0, 2, 1], [0x17, 0, 1, 1],
  [0x18, 0, 2, 1], [0x19, 0, 2, 1], [0x1a, 0, 2, 1], [0x1b, 0, 1, 1],
  [0x1c, 0, 2, 1], [0x1d, 0, 2, 1], [0x1e, 0, 2, 1], [0x20, 0, 2, 1],
  [0x21, 0, 2, 1], [0x22, 0, 2, 1], [0x30, 2, 0, 0], [0x31, 2, 1, 0],
  [0x32, 2, 1, 0], [0x33, 2, 0, 0], [0x34, 0, 0, 0], [0x40, 0, 1, 1],
  [0x41, 0, 2, 0], [0x50, 0, 1, 0], [0x51, 0, 1, 0], [0x52, 0, 0, 1],
  [0x53, 0, 1, 0],
];
const IMM = new Int8Array(256).fill(-1);
const POP = new Int8Array(256);
const PSH = new Int8Array(256);
for (const [o, i, p, q] of OPS) { IMM[o] = i; POP[o] = p; PSH[o] = q; }

function run(p: Uint8Array, inp: Uint8Array): { out: Uint8Array; code: number } {
  const n = p.length;
  const D = new Int32Array(256);
  const C = new Int32Array(64);
  const M = new Int32Array(256);
  const out = new Uint8Array(65536);
  let sp = 0, csp = 0, ip = 0, pc = 0, steps = 0, olen = 0;
  const done = (code: number): { out: Uint8Array; code: number } => ({ out: out.subarray(0, olen), code });
  for (;;) {
    if (steps === 1000000) return done(10);
    if (pc < 0 || pc >= n) return done(9);
    const op = p[pc]!;
    const im = IMM[op]!;
    if (im < 0) return done(5);
    if (pc + im >= n) return done(9);
    steps++;
    const nx = pc + 1 + im;
    if (sp < POP[op]!) return done(2);
    if (sp - POP[op]! + PSH[op]! > 256) return done(3);
    pc = nx;
    switch (op) {
      case 0x00: return done(0);
      case 0x01: D[sp++] = (p[nx - 1]! << 24) >> 24; break;
      case 0x02: D[sp++] = p[nx - 4]! | (p[nx - 3]! << 8) | (p[nx - 2]! << 16) | (p[nx - 1]! << 24); break;
      case 0x03: sp--; break;
      case 0x04: D[sp] = D[sp - 1]!; sp++; break;
      case 0x05: { const t = D[sp - 1]!; D[sp - 1] = D[sp - 2]!; D[sp - 2] = t; break; }
      case 0x06: D[sp] = D[sp - 2]!; sp++; break;
      case 0x07: { const a = D[sp - 3]!; D[sp - 3] = D[sp - 2]!; D[sp - 2] = D[sp - 1]!; D[sp - 1] = a; break; }
      case 0x10: D[sp - 2] = (D[sp - 2]! + D[sp - 1]!) | 0; sp--; break;
      case 0x11: D[sp - 2] = (D[sp - 2]! - D[sp - 1]!) | 0; sp--; break;
      case 0x12: D[sp - 2] = Math.imul(D[sp - 2]!, D[sp - 1]!); sp--; break;
      case 0x13: {
        const b = D[sp - 1]!, a = D[sp - 2]!;
        if (b === 0) return done(4);
        D[sp - 2] = a === -2147483648 && b === -1 ? a : (a / b) | 0; sp--; break;
      }
      case 0x14: {
        const b = D[sp - 1]!, a = D[sp - 2]!;
        if (b === 0) return done(4);
        D[sp - 2] = b === -1 ? 0 : (a % b) | 0; sp--; break;
      }
      case 0x15: {
        const b = D[sp - 1]!, a = D[sp - 2]!;
        if (b === 0) return done(4);
        D[sp - 2] = Math.floor((a >>> 0) / (b >>> 0)) | 0; sp--; break;
      }
      case 0x16: {
        const b = D[sp - 1]!, a = D[sp - 2]!;
        if (b === 0) return done(4);
        D[sp - 2] = ((a >>> 0) % (b >>> 0)) | 0; sp--; break;
      }
      case 0x17: D[sp - 1] = (-D[sp - 1]!) | 0; break;
      case 0x18: D[sp - 2] = D[sp - 2]! & D[sp - 1]!; sp--; break;
      case 0x19: D[sp - 2] = D[sp - 2]! | D[sp - 1]!; sp--; break;
      case 0x1a: D[sp - 2] = D[sp - 2]! ^ D[sp - 1]!; sp--; break;
      case 0x1b: D[sp - 1] = ~D[sp - 1]!; break;
      case 0x1c: D[sp - 2] = D[sp - 2]! << (D[sp - 1]! & 31); sp--; break;
      case 0x1d: D[sp - 2] = D[sp - 2]! >> (D[sp - 1]! & 31); sp--; break;
      case 0x1e: D[sp - 2] = (D[sp - 2]! >>> (D[sp - 1]! & 31)) | 0; sp--; break;
      case 0x20: D[sp - 2] = D[sp - 2]! === D[sp - 1]! ? 1 : 0; sp--; break;
      case 0x21: D[sp - 2] = D[sp - 2]! < D[sp - 1]! ? 1 : 0; sp--; break;
      case 0x22: D[sp - 2] = (D[sp - 2]! >>> 0) < (D[sp - 1]! >>> 0) ? 1 : 0; sp--; break;
      case 0x30: case 0x31: case 0x32: {
        const rel = ((p[nx - 2]! | (p[nx - 1]! << 8)) << 16) >> 16;
        const take = op === 0x30 || (op === 0x31) === (D[--sp] === 0);
        if (take) pc = nx + rel;
        break;
      }
      case 0x33:
        if (csp === 64) return done(7);
        C[csp++] = nx;
        pc = p[nx - 2]! | (p[nx - 1]! << 8);
        break;
      case 0x34:
        if (csp === 0) return done(8);
        pc = C[--csp]!;
        break;
      case 0x40: {
        const addr = D[sp - 1]!;
        if (addr < 0 || addr >= 256) return done(6);
        D[sp - 1] = M[addr]!;
        break;
      }
      case 0x41: {
        const addr = D[sp - 1]!, v = D[sp - 2]!;
        if (addr < 0 || addr >= 256) return done(6);
        sp -= 2;
        M[addr] = v;
        break;
      }
      case 0x50: {
        const s = String(D[sp - 1]!);
        if (olen + s.length > 65536) return done(11);
        sp--;
        for (let i = 0; i < s.length; i++) out[olen++] = s.charCodeAt(i);
        break;
      }
      case 0x51:
        if (olen + 1 > 65536) return done(11);
        out[olen++] = D[--sp]! & 255;
        break;
      case 0x52: D[sp++] = ip < inp.length ? inp[ip++]! : -1; break;
      case 0x53: return done(D[--sp]! & 255);
    }
  }
}

const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.out);
  writeFileSync(join(O, id, 'exit.txt'), `${r.code}\n`);
}
