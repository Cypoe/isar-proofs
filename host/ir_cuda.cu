/*
 * ir_cuda — CUDA parallel evaluator for packed-IR batches.
 *
 * Same stdin/stdout contract as the emitted win64 IR kernel
 * (routines_x86_64_win64 X86_64_WIN64_IR): stdin carries a stream of
 * packed-IR blobs [ADR-0005] — <IIII header {magic "PIR\0", ver,
 * n_nodes, n_roots}, then n_roots u32 root indices, then n_roots *
 * 9-byte node records <BII {tag,l,r}> in postorder — repeated until
 * EOF (a short/failed header read is clean end-of-stream).  One NF
 * postfix line per root on stdout; aggregate `steps=… alloc=…` on
 * stderr at exit.  Exit codes mirror the kernel: 0 clean, 2 fuel,
 * 3 malformed input.
 *
 * The reduction semantics mirror the emitted kernel exactly
 * (IStepBasis order at node t=(f x)): normβ I x→x, konstβ K a b→a,
 * dupβ W f x→f x x, compβ B f g x→f(g x), swapβ C f g x→f x g,
 * sβ S f g x→(f x)(g x) under -DFUSE_S, else congruence left-then-
 * right with fresh app cells up the zipper — allocation-per-rebuild,
 * so `alloc` counts every mkapp like the native kernel.
 *
 * Parallel shape: the audit data showed ~77 congruence descents per
 * rule firing — intra-root parallelism is thin, so one thread per
 * ROOT (the same unit the CPU fork-pool chunks).  Cells are
 * u32-indexed {tag,l,r} in a shared device arena; the input graph
 * depacks at cells[0..n_nodes), rule/congruence allocations bump a
 * global atomic.  Cells are immutable — sharing is sound.
 *
 * Build: nvcc -O2 -o ir_cuda.exe host/ir_cuda.cu
 *        [-DFUSE_S] [-DVERBOSE]
 * Env:   IR_CUDA_HEAP_MB   device arena size      (default 3072)
 *        IR_CUDA_FUEL      per-root step budget   (default 0 = none)
 *        IR_CUDA_NFCAP     per-root NF out bytes   (default 1<<20)
 *        IR_CUDA_FRAMES    per-root zipper depth   (default 65536)
 */

#include <cuda_runtime.h>
#include <cstdio>
#include <cstdlib>
#include <cstring>
#include <stdint.h>
#ifdef _WIN32
#include <io.h>
#include <fcntl.h>
#endif

#define IR_MAGIC   0x30524950u   /* "PIR\0" */
#define IR_VERSION 1u
#define IR_VAR     0xFEu

#define TAG_APP  0u
#define TAG_I    1u
#define TAG_K    2u
#define TAG_S    3u
#define TAG_B    4u
#define TAG_D    5u   /* dup leaf  = token 'W' */
#define TAG_C    6u   /* swap leaf = token 'C' */

#define ST_OK    0u
#define ST_FUEL  2u
#define ST_BAD   3u
#define ST_OOM   4u
#define ST_DEEP  5u
#define ST_NFOVF 6u

struct Cell { uint32_t tag, l, r; };
struct Frame { uint32_t node, side; };   /* side: 0 left, 1 right */
struct Res {
    uint32_t nf, nf_bytes, status, pad;
    uint64_t steps, alloc;
};

__device__ Cell*   g_cells;
__device__ uint32_t g_top;
__device__ uint32_t g_cap;

/* mkapp, counted: every allocated cell bumps the caller's alloc —
 * the same unit the kernel's `alloc=` stat reports.  bump==NULL uses
 * the shared stream bump counter (atomicAdd); non-NULL is the
 * per-root retake model — the thread owns a private bump cursor and
 * claims SLAB_CELLS-sized slabs from a shared pool on demand, so a
 * root's cells stay contiguous and heavy roots simply claim more
 * slabs; only the stream total is capped (g_slabtop vs g_cap), not
 * any per-root share — the GPU analog of the native kernel's
 * reserve-big / commit-on-touch / per-root DECOMMIT arena. */
#define SLAB_CELLS (1u << 20)
__device__ uint32_t g_slabtop;          /* slab pool high-water */

__device__ uint32_t mkapp(uint32_t f, uint32_t x, uint32_t* bump,
                          uint32_t* bend, uint64_t* alloc) {
    uint32_t i;
    *alloc += 1;
    if (bump) {
        if (*bump == *bend) {                    /* slab exhausted */
            uint32_t base = atomicAdd(&g_slabtop, SLAB_CELLS);
            *bump = base;
            *bend = base + SLAB_CELLS;
            if (*bend > g_cap) *bend = g_cap;
            if (*bump >= *bend) return 0xFFFFFFFFu;
        }
        i = (*bump)++;
        if (i >= *bend) return 0xFFFFFFFFu;
    } else {
        i = atomicAdd(&g_top, 1u);
        if (i >= g_cap) return 0xFFFFFFFFu;
    }
    g_cells[i].tag = TAG_APP;
    g_cells[i].l = f;
    g_cells[i].r = x;
    return i;
}

/* One LO step on the term at t: returns new root index, or 0xFFFFFFFF
 * if t is already in normal form.  Mirrors the kernel's step(): root
 * redex check, else left congruence, else right — with the zipper
 * rebuilt through fresh mkapp cells on the way up.  bump/bend select
 * the allocator: NULL,NULL = shared stream arena; per-root = the
 * thread's private slab cursor (see ir_reduce_kernel). */
__device__ uint32_t step_one(uint32_t t, Frame* st, uint32_t fcap,
                             uint32_t* deep, uint64_t* alloc,
                             uint32_t* bump, uint32_t* bend) {
    uint32_t top = 0, cur = t;
    for (;;) {
        Cell c = g_cells[cur];
        uint32_t v = 0xFFFFFFFFu;
        if (c.tag == TAG_APP) {
            Cell f = g_cells[c.l];
            if (f.tag == TAG_I) {
                v = c.r;                                     /* I x -> x */
            } else if (f.tag == TAG_APP) {
                Cell fl = g_cells[f.l];
                if (fl.tag == TAG_K) {
                    v = f.r;                                 /* K a b -> a */
                } else if (fl.tag == TAG_D) {          /* W f x -> f x x */
                    uint32_t fx = mkapp(f.r, c.r, bump, bend, alloc);
                    if (fx != 0xFFFFFFFFu) v = mkapp(fx, c.r, bump, bend, alloc);
                } else if (fl.tag == TAG_APP) {
                    Cell fll = g_cells[fl.l];
                    if (fll.tag == TAG_B) {            /* B f g x -> f(g x) */
                        uint32_t gx = mkapp(f.r, c.r, bump, bend, alloc);
                        if (gx != 0xFFFFFFFFu) v = mkapp(fl.r, gx, bump, bend, alloc);
                    } else if (fll.tag == TAG_C) {   /* C f g x -> f x g */
                        uint32_t fx = mkapp(fl.r, c.r, bump, bend, alloc);
                        if (fx != 0xFFFFFFFFu) v = mkapp(fx, f.r, bump, bend, alloc);
#ifdef FUSE_S
                    } else if (fll.tag == TAG_S) { /* S f g x -> (fx)(gx) */
                        uint32_t fx = mkapp(fl.r, c.r, bump, bend, alloc);
                        uint32_t gx = mkapp(f.r, c.r, bump, bend, alloc);
                        if (fx != 0xFFFFFFFFu && gx != 0xFFFFFFFFu)
                            v = mkapp(fx, gx, bump, bend, alloc);
#endif
                    }
                }
            }
        }
        if (v != 0xFFFFFFFFu) {
            /* contract: unwind the zipper, rebuilding parents with
             * fresh app cells (side LEFT -> (v p.r), RIGHT -> (p.l v)) */
            while (top) {
                Frame fr = st[--top];
                Cell p = g_cells[fr.node];
                v = fr.side == 0 ? mkapp(v, p.r, bump, bend, alloc)
                                 : mkapp(p.l, v, bump, bend, alloc);
                if (v == 0xFFFFFFFFu) return 0xFFFFFFFEu;   /* OOM mid-step */
            }
            return v;
        }
        if (c.tag == TAG_APP) {
            if (top >= fcap) { *deep = 1; return 0xFFFFFFFEu; }
            st[top].node = cur; st[top].side = 0; top++;
            cur = c.l;
            continue;
        }
        for (;;) {                                  /* leaf: backtrack */
            if (!top) return 0xFFFFFFFFu;           /* normal form */
            Frame fr = st[--top];
            if (fr.side == 0) {
                st[top].node = fr.node; st[top].side = 1; top++;
                cur = g_cells[fr.node].r;
                break;
            }
        }
    }
}

/* Postfix-decompile the NF at root into out (cap bytes): leaf chars
 * I K S B W C and '@' for app, each followed by ' ' — the exact
 * emit_nf alphabet of the emitted kernel.  Returns bytes written or
 * cap+1 on overflow.  Iterative; reuses the zipper stack. */
__device__ uint32_t emit_nf(uint32_t root, char* out, uint32_t cap,
                            Frame* st, uint32_t fcap) {
    static const char TAGC[7] = {'@', 'I', 'K', 'S', 'B', 'W', 'C'};
    uint32_t top = 0, cur = root, pos = 0;
    for (;;) {
        Cell c = g_cells[cur];
        if (c.tag == TAG_APP) {
            if (top >= fcap) return cap + 1;
            st[top].node = cur; st[top].side = 0; top++;
            cur = c.l;
            continue;
        }
        char ch = (c.tag < 7) ? TAGC[c.tag] : '?';
        if (pos + 2 > cap) return cap + 1;
        out[pos++] = ch; out[pos++] = ' ';
        for (;;) {
            if (!top) return pos;
            Frame fr = st[--top];
            Cell p = g_cells[fr.node];
            if (fr.side == 0) {                     /* left done: right */
                st[top].node = fr.node; st[top].side = 1; top++;
                cur = p.r;
                break;
            }
            /* both children done: '@' at the app node, keep unwinding */
            if (pos + 2 > cap) return cap + 1;
            out[pos++] = '@'; out[pos++] = ' ';
            cur = fr.node;
        }
    }
}

__global__ void ir_reduce_kernel(uint32_t n_roots, const uint32_t* roots,
                                 uint64_t fuel, Res* res,
                                 Frame* frames, uint32_t fcap,
                                 char* nfbuf, uint32_t nfcap,
                                 uint32_t per_root) {
    uint32_t tid = blockIdx.x * blockDim.x + threadIdx.x;
    if (tid >= n_roots) return;
    Frame* st = frames + (size_t)tid * fcap;
    Res r = {roots[tid], 0, ST_OK, 0, 0, 0};
    uint32_t deep = 0;
    /* allocator selection: shared = the stream's single bump counter;
     * per_root = a private [base, base+slice) region per root — the
     * same boundedness model as the native kernel's per-root
     * DECOMMIT reset (g_top is top0 here: input cells + ds template
     * are shared read-only below the slab pool, reduction cells are
     * per-root slabs). */
    uint32_t mytop = 0, myend = 0;   /* empty range -> claim on 1st mkapp */
    uint32_t* bump = NULL;
    uint32_t* bend = NULL;
    if (per_root) { bump = &mytop; bend = &myend; }
    while (fuel == 0 || r.steps < fuel) {
        uint32_t v = step_one(r.nf, st, fcap, &deep, &r.alloc,
                              bump, bend);
        if (v == 0xFFFFFFFFu) break;                    /* normal form */
        if (v == 0xFFFFFFFEu) { r.status = deep ? ST_DEEP : ST_OOM; break; }
        r.nf = v;
        r.steps++;
    }
    /* kernel semantics: the fuel check sits at the loop head, so
     * hitting the budget is exit2 even if the last step reached NF */
    if (r.status == ST_OK && fuel && r.steps >= fuel)
        r.status = ST_FUEL;
    res[tid] = r;
}

__global__ void ir_emit_kernel(uint32_t n_roots, Res* res,
                               Frame* frames, uint32_t fcap,
                               char* nfbuf, uint32_t nfcap) {
    uint32_t tid = blockIdx.x * blockDim.x + threadIdx.x;
    if (tid >= n_roots || res[tid].status != ST_OK) return;
    uint32_t n = emit_nf(res[tid].nf, nfbuf + (size_t)tid * nfcap,
                         nfcap, frames + (size_t)tid * fcap, fcap);
    if (n > nfcap) { res[tid].status = ST_NFOVF; return; }
    res[tid].nf_bytes = n;
}

__global__ void ir_probe_kernel(uint32_t n_cells, const uint32_t* roots,
                                uint32_t n_roots, uint64_t fuel,
                                uint32_t fcap) {
    printf("dev: n_roots=%u fuel=%llu fcap=%u g_top=%u g_cap=%u\n",
           n_roots, (unsigned long long)fuel, fcap, g_top, g_cap);
    for (uint32_t i = 0; i < n_cells && i < 32; i++)
        printf("  cell%u tag=%u l=%u r=%u\n", i, g_cells[i].tag,
               g_cells[i].l, g_cells[i].r);
    for (uint32_t i = 0; i < n_roots; i++)
        printf("  root%u = %u\n", i, roots[i]);
}

/* ------------------------------- host ------------------------------ */

static int read_exact(FILE* f, void* buf, size_t n) {
    size_t got = fread(buf, 1, n, f);
    if (got == n) return 1;
    if (got == 0 && feof(f)) return 0;          /* clean EOF */
    return -1;                                   /* truncated */
}

static void* xmalloc(size_t n) {
    void* p = malloc(n);
    if (!p) { fprintf(stderr, "ir_cuda: host oom\n"); exit(4); }
    return p;
}

int main(void) {
#ifdef _WIN32
    /* the wire is binary — text mode would corrupt 0x1A/\r bytes
     * (the kernel uses raw ReadFile/WriteFile for the same reason) */
    _setmode(_fileno(stdin), O_BINARY);
    _setmode(_fileno(stdout), O_BINARY);
#endif
    setvbuf(stdout, NULL, _IOFBF, 1 << 20);

    uint64_t heap_mb = 3072, fuel = 0;
    uint32_t nfcap = 1u << 20, fcap = 65536;
    if (const char* s = getenv("IR_CUDA_HEAP_MB")) heap_mb = strtoull(s, 0, 0);
    if (const char* s = getenv("IR_CUDA_FUEL"))    fuel    = strtoull(s, 0, 0);
    if (const char* s = getenv("IR_CUDA_NFCAP"))   nfcap   = strtoul(s, 0, 0);
    if (const char* s = getenv("IR_CUDA_FRAMES"))  fcap    = strtoul(s, 0, 0);
    uint32_t per_root = getenv("IR_CUDA_PER_ROOT") ? 1u : 0u;
    int managed = getenv("IR_CUDA_MANAGED") ? 1 : 0;

    size_t cap = ((size_t)heap_mb << 20) / sizeof(Cell);
    Cell* h_cells = (Cell*)xmalloc(cap * sizeof(Cell));

    Cell* d_cells;
    /* managed = demand-paged UVM: the GPU analog of the native
     * kernel's reserve-huge/commit-on-touch arena — heap_mb may
     * exceed VRAM (pages fault between device and host on access);
     * plain cudaMalloc is eager. */
    cudaError_t e0 = managed
        ? cudaMallocManaged(&d_cells, cap * sizeof(Cell))
        : cudaMalloc(&d_cells, cap * sizeof(Cell));
    if (e0 != cudaSuccess) {
        fprintf(stderr, "ir_cuda: device arena %lluMB alloc failed\n",
                (unsigned long long)heap_mb);
        return 4;
    }
    cudaMemcpyToSymbol(g_cells, &d_cells, sizeof(d_cells));
    cudaMemcpyToSymbol(g_cap, &cap, sizeof(uint32_t));

    uint64_t tot_steps = 0, tot_alloc = 0;
#ifndef FUSE_S
    tot_alloc = 19;      /* build_ds runs once per process: 11 mkleaf
                          * + 8 mkapp -> 19 cells in the kernel's nalloc */
#endif
    int rc = 0;

    for (;;) {                                   /* stream of blobs */
        uint32_t hdr[4];
        int rd = read_exact(stdin, hdr, 16);
        if (rd == 0) break;                              /* clean EOF */
        if (rd < 0 || hdr[0] != IR_MAGIC || hdr[1] != IR_VERSION) {
            rc = 3; break;
        }
        uint32_t n_nodes = hdr[2], n_roots = hdr[3];
        if (!n_roots || (uint64_t)n_nodes >= cap) { rc = 3; break; }

        uint32_t* roots = (uint32_t*)xmalloc(4 * n_roots);
        if (read_exact(stdin, roots, 4 * n_roots) != 1) { rc = 3; break; }
        for (uint32_t i = 0; i < n_roots; i++)
            if (roots[i] >= n_nodes) { rc = 3; break; }
        if (rc) break;

        /* depack: 9-byte records -> cells[0..n_nodes).  Mirrors the
         * kernel: tags >= 7 (incl. 0xFE VAR probes) reject; in the
         * default (non-FUSE_S) view a tag-3 cell depacks to a copy of
         * the derived-S root {APP, ds.l, ds.r} against the template
         * appended at cells[n_nodes..n_nodes+12] — the same expansion
         * build_ds emits once per process.  Depacked cells count as
         * allocations like the kernel's nalloc. */
        for (uint32_t i = 0; i < n_nodes; i++) {
            uint8_t tag; uint32_t l, r;
            uint8_t nb[9];
            if (read_exact(stdin, nb, 9) != 1) { rc = 3; break; }
            tag = nb[0];
            memcpy(&l, nb + 1, 4); memcpy(&r, nb + 5, 4);
            if (tag >= 7) { rc = 3; break; }
            if (tag == TAG_APP && (l >= i || r >= i)) { rc = 3; break; }
            h_cells[i].tag = tag;
            h_cells[i].l = l; h_cells[i].r = r;
        }
        if (rc) break;

        uint32_t top0 = n_nodes;
#ifndef FUSE_S
        /* ds template (13 cells), postorder, indices template-relative:
         *   leaves B D C I, then (B D), (B (B D)) [=left],
         *   (B B)x2, ((B B) C), X=(B B)((B B)C), (C X), ((C X) I)
         *   [=right], root=(left right).  Tag-3 input cells copy the
         *   root's children {APP, left, right} — same aliasing the
         *   kernel uses against its permanent template. */
        {
            static const Cell DS[13] = {
                {TAG_B,0,0}, {TAG_D,0,0}, {TAG_C,0,0}, {TAG_I,0,0},
                {0,0,1}, {0,0,4}, {0,0,0}, {0,0,0}, {0,7,2},
                {0,6,8}, {0,2,9}, {0,10,3}, {0,5,11},
            };
            uint32_t dsb = n_nodes;
            for (int j = 0; j < 13; j++) {
                h_cells[dsb + j] = DS[j];
                if (DS[j].tag == TAG_APP) {
                    h_cells[dsb + j].l += dsb;
                    h_cells[dsb + j].r += dsb;
                }
            }
            for (uint32_t i = 0; i < n_nodes; i++)
                if (h_cells[i].tag == TAG_S) {
                    h_cells[i].tag = TAG_APP;
                    h_cells[i].l = dsb + 5;
                    h_cells[i].r = dsb + 11;
                }
            top0 += 13;
        }
#endif
        tot_alloc += n_nodes;        /* depacked cells ~ kernel nalloc */

        uint32_t* d_roots; Res* d_res; Frame* d_frames; char* d_nf;
        cudaMalloc(&d_roots, 4 * n_roots);
        cudaMalloc(&d_res, n_roots * sizeof(Res));
        cudaMalloc(&d_frames, (size_t)n_roots * fcap * sizeof(Frame));
        cudaMalloc(&d_nf, (size_t)n_roots * nfcap);
        /* copy the input cells AND the appended ds template —
         * tag-3 rewrites already point at cells[n_nodes..top0) */
        cudaMemcpy(d_cells, h_cells, top0 * sizeof(Cell),
                   cudaMemcpyHostToDevice);
        cudaMemcpy(d_roots, roots, 4 * n_roots, cudaMemcpyHostToDevice);
        cudaMemcpyToSymbol(g_top, &top0, sizeof(uint32_t));
        cudaMemcpyToSymbol(g_slabtop, &top0, sizeof(uint32_t));

        uint32_t tpb = 128, nblk = (n_roots + tpb - 1) / tpb;
        if (getenv("IR_CUDA_DEBUG")) {
            ir_probe_kernel<<<1, 1>>>(top0, d_roots, n_roots, fuel, fcap);
            cudaDeviceSynchronize();
        }
        ir_reduce_kernel<<<nblk, tpb>>>(n_roots, d_roots, fuel, d_res,
                                        d_frames, fcap, d_nf, nfcap,
                                        per_root);
        cudaError_t e = cudaDeviceSynchronize();
        if (e != cudaSuccess) {
            fprintf(stderr, "ir_cuda: reduce: %s\n",
                    cudaGetErrorString(e));
            rc = 4; break;
        }
        ir_emit_kernel<<<nblk, tpb>>>(n_roots, d_res, d_frames, fcap,
                                      d_nf, nfcap);
        e = cudaDeviceSynchronize();
        if (e != cudaSuccess) {
            fprintf(stderr, "ir_cuda: emit: %s\n", cudaGetErrorString(e));
            rc = 4; break;
        }

        Res* h_res = (Res*)xmalloc(n_roots * sizeof(Res));
        cudaMemcpy(h_res, d_res, n_roots * sizeof(Res),
                   cudaMemcpyDeviceToHost);
        char* h_nf = (char*)xmalloc((size_t)n_roots * nfcap);
        cudaMemcpy(h_nf, d_nf, (size_t)n_roots * nfcap,
                   cudaMemcpyDeviceToHost);

        for (uint32_t i = 0; i < n_roots; i++) {
            tot_steps += h_res[i].steps;
            tot_alloc += h_res[i].alloc;
            if (getenv("IR_CUDA_DEBUG"))
                fprintf(stderr, "  root%u: nf=%u bytes=%u status=%u "
                        "steps=%llu alloc=%llu\n", i, h_res[i].nf,
                        h_res[i].nf_bytes, h_res[i].status,
                        (unsigned long long)h_res[i].steps,
                        (unsigned long long)h_res[i].alloc);
            if (h_res[i].status == ST_OK) {
                fwrite(h_nf + (size_t)i * nfcap, 1, h_res[i].nf_bytes,
                       stdout);
                fputc('\n', stdout);
            } else if (h_res[i].status == ST_FUEL) {
                rc = 2;
            } else {
                rc = 3;
            }
        }
        fflush(stdout);
        free(h_res); free(h_nf); free(roots);
        cudaFree(d_roots); cudaFree(d_res); cudaFree(d_frames);
        cudaFree(d_nf);
        if (rc) break;
    }

    fprintf(stderr, "steps=%llu alloc=%llu\n",
            (unsigned long long)tot_steps, (unsigned long long)tot_alloc);
    return rc;
}
