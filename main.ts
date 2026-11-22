// Tiny stack VM: faithful port of the ISA reference (generator/subject/vm.mjs).
// Runs every /input/<id>/{program,input}.bin, writes /output/<id>/{stdout.bin,exit.txt}.
import { mkdirSync, readdirSync, readFileSync, writeFileSync } from 'node:fs';
import { join } from 'node:path';
const I = process.env.MAKEFUN_INPUT_DIR ?? '/input';
const O = process.env.MAKEFUN_OUTPUT_DIR ?? '/output';
const E = new TextEncoder();
function run(p: Uint8Array, q: Uint8Array) {
  const D = new Int32Array(256), C = new Int32Array(64), M = new Int32Array(256), o = new Uint8Array(65536);
  let s = 0, c = 0, pc = 0, t = 0, ip = 0, n = 0;
  const end = (x: number) => ({ o: o.slice(0, n), x });
  for (;;) {
    if (t === 1e6) return end(10); // step limit
    if (pc < 0 || pc >= p.length) return end(9); // pc outside program
    const b = p[pc];
    let m = 0, u = 0, v = 0, k = 1; // immediate bytes, pops, pushes, known?
    if (b === 0) /* HALT */;
    else if (b === 1) { m = 1; v = 1; } // PUSH8
    else if (b === 2) { m = 4; v = 1; } // PUSH32
    else if (b === 3) u = 1; // POP
    else if (b === 4) { u = 1; v = 2; } // DUP
    else if (b === 5) { u = 2; v = 2; } // SWAP
    else if (b === 6) { u = 2; v = 3; } // OVER
    else if (b === 7) { u = 3; v = 3; } // ROT
    else if (b === 23 || b === 27) { u = 1; v = 1; } // NEG, NOT
    else if (b >= 16 && b <= 34 && b !== 31) { u = 2; v = 1; } // binary ops
    else if (b >= 48 && b <= 50) { m = 2; if (b > 48) u = 1; } // JMP, JZ, JNZ
    else if (b === 51) m = 2; // CALL
    else if (b === 52) /* RET */;
    else if (b === 64) { u = 1; v = 1; } // LOAD
    else if (b === 65) u = 2; // STORE
    else if (b === 80 || b === 81 || b === 83) u = 1; // PRINT, PUTC, EXIT
    else if (b === 82) v = 1; // IN
    else k = 0;
    if (!k) return end(5); // unknown opcode
    if (pc + m >= p.length) return end(9); // immediate cut off
    t++;
    const nx = pc + 1 + m;
    if (s < u) return end(2); // stack underflow
    if (s - u + v > 256) return end(3); // stack overflow
    pc = nx;
    if (b === 0) return end(0); // HALT
    if (b === 1) D[s++] = (p[nx - 1] << 24) >> 24;
    else if (b === 2) D[s++] = p[nx - 4] | (p[nx - 3] << 8) | (p[nx - 2] << 16) | (p[nx - 1] << 24);
    else if (b === 3) s--; // POP
    else if (b === 4) { D[s] = D[s - 1]; s++; } // DUP
    else if (b === 5) { const w = D[s - 1]; D[s - 1] = D[s - 2]; D[s - 2] = w; } // SWAP
    else if (b === 6) { D[s] = D[s - 2]; s++; } // OVER
    else if (b === 7) { const a = D[s - 3]; D[s - 3] = D[s - 2]; D[s - 2] = D[s - 1]; D[s - 1] = a; } // ROT
    else if (b === 23) D[s - 1] = -D[s - 1] | 0; // NEG
    else if (b === 27) D[s - 1] = ~D[s - 1]; // NOT
    else if (b >= 16 && b <= 34 && b !== 31) { // binary ops
      const y = D[s - 1], a = D[s - 2];
      let r = 0;
      if (b === 16) r = (a + y) | 0;
      else if (b === 17) r = (a - y) | 0;
      else if (b === 18) r = Math.imul(a, y);
      else if (b === 19) { if (!y) return end(4); r = a === -2147483648 && y === -1 ? a : (a / y) | 0; }
      else if (b === 20) { if (!y) return end(4); r = y === -1 ? 0 : (a % y) | 0; }
      else if (b === 21) { if (!y) return end(4); r = Math.floor((a >>> 0) / (y >>> 0)) | 0; }
      else if (b === 22) { if (!y) return end(4); r = ((a >>> 0) % (y >>> 0)) | 0; }
      else if (b === 24) r = a & y;
      else if (b === 25) r = a | y;
      else if (b === 26) r = a ^ y;
      else if (b === 28) r = a << (y & 31);
      else if (b === 29) r = a >> (y & 31);
      else if (b === 30) r = (a >>> (y & 31)) | 0;
      else if (b === 32) r = a === y ? 1 : 0;
      else if (b === 33) r = a < y ? 1 : 0;
      else if (b === 34) r = (a >>> 0) < (y >>> 0) ? 1 : 0;
      s -= 2; D[s++] = r;
    } else if (b >= 48 && b <= 50) { // JMP, JZ, JNZ
      const rel = ((p[nx - 2] | (p[nx - 1] << 8)) << 16) >> 16;
      let tk = 1;
      if (b !== 48) { const w = D[--s]; tk = b === 49 ? w === 0 : w !== 0; }
      if (tk) pc = nx + rel;
    } else if (b === 51) { // CALL
      if (c === 64) return end(7);
      C[c++] = nx; pc = p[nx - 2] | (p[nx - 1] << 8);
    } else if (b === 52) { // RET
      if (!c) return end(8);
      pc = C[--c];
    } else if (b === 64) { // LOAD
      const a = D[s - 1];
      if (a < 0 || a > 255) return end(6);
      D[s - 1] = M[a];
    } else if (b === 65) { // STORE
      const a = D[s - 1], w = D[s - 2];
      if (a < 0 || a > 255) return end(6);
      s -= 2; M[a] = w;
    } else if (b === 80) { // PRINT
      const d = E.encode(String(D[s - 1]));
      if (n + d.length > 65536) return end(11);
      s--; o.set(d, n); n += d.length;
    } else if (b === 81) { // PUTC
      if (n + 1 > 65536) return end(11);
      o[n++] = D[--s] & 255;
    } else if (b === 82) D[s++] = ip < q.length ? q[ip++] : -1; // IN
    else if (b === 83) return end(D[--s] & 255); // EXIT
  }
}
for (const id of readdirSync(I).sort()) {
  const r = run(new Uint8Array(readFileSync(join(I, id, 'program.bin'))), new Uint8Array(readFileSync(join(I, id, 'input.bin'))));
  mkdirSync(join(O, id), { recursive: true });
  writeFileSync(join(O, id, 'stdout.bin'), r.o);
  writeFileSync(join(O, id, 'exit.txt'), r.x + '\n');
}
