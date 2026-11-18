import ISAR.KoruEmit

/-!
# KoruProgEmit — KProg → C99 program emission (the H1 leg)

`emitC99` emits the *source* of a closed int expression. This module
emits the source of a whole Koru **program**: each callable becomes a
C function over a boxed `Val`, each arm an `aw_N` walk, each dispatch
list an unrolled `ds_N`, each pure expression an `ev_N`, each literal
a `vl_N` builder. The emitted artifact is compiled code, not an
interpreter — the runtime prelude (declared data below) provides only
the value representation, the `(cell (name val) …)` stdin wire, the
binop/unop/builtin tables, and the `Res` outcome type.

Semantics mirrored from `runK` (FlowDialect): bare dispatch tries
arms in order, `when` false skips, bind-on-payloadless and guard
eval errors refuse; tag dispatch tries only `branch == b` arms;
a catchall/`""` arm refuses *at its position* under bare dispatch;
invoke nodes feed conts by result branch; `done` unwraps to the
empty result; `jump` re-enters the head only through `preLabel`;
a nested invoke yielding anything but `.result` refuses.

Declared deltas (the realization row names them):
  * `.thunk` callables → codegen error `oracle/thunk` (the asserted-
    call oracle is claim data, not program structure).
  * Int arithmetic is int64-bounded with refuse-on-overflow — Lean
    `Int` is unbounded, so the realized observation is narrower.
  * Fuel is spent per call/dispatch/arm frame, approximating
    `runK`'s per-step count; exhaustion still refuses.
  * Strings are the wire's no-escape strings; entry args arrive at
    runtime as one `(cell (name val)…)` sexpr on stdin.

Anything outside the emitted subset fails codegen with a named
axis rather than emitting something approximate.
-/

namespace ISAR

/-- Codegen state: a fresh counter plus accumulated declarations.
`EStateM String` — the error is the refusal axis's name. -/
structure CES where
  n : Nat := 0
  out : String := ""

abbrev EM := EStateM String CES

def EM.fresh (pre : String) : EM String := do
  let i ← modifyGet fun s => (s.n, { s with n := s.n + 1 })
  return s!"{pre}{i}"

def EM.put (s : String) : EM Unit :=
  modify fun st => { st with out := st.out ++ s }

/-- Koru identifiers may carry `-`/`'`/etc; C identifiers may not. -/
def mangle (s : String) : String :=
  String.ofList (s.toList.map fun c =>
    if c.isAlphanum || c == '_' then c else '_')

/-- Escape a string into a C literal body (no surrounding quotes).
Byte-level: the runtime's `char*` strings are UTF-8, so non-ASCII
chars are escaped as their UTF-8 *bytes*, not their code point —
`—` → `\342\200\224`.  Three-digit octal is exact for bytes. -/
def cstrBody (s : String) : String :=
  String.ofList (s.toUTF8.toList.flatMap fun b =>
    let n := b.toNat
    if n == 34 then ['\\', '"']
    else if n == 92 then ['\\', '\\']
    else if n == 10 then ['\\', 'n']
    else if n == 9 then ['\\', 't']
    else if n == 13 then ['\\', 'r']
    else if n < 32 || n ≥ 127 then
      ['\\', Char.ofNat (48 + n / 64), Char.ofNat (48 + (n / 8) % 8),
       Char.ofNat (48 + n % 8)]
    else [Char.ofNat n])

def cstr (s : String) : String := "\"" ++ cstrBody s ++ "\""

/-! ## The declared runtime prelude

Everything the emitted program needs that is not program logic:
`Val`/`Res`/`E` representations, constructors, structural equality,
field/index access, the `evalKBin`/`evalKUn`/`evalKBuiltin` tables in
C, the `(cell …)` sexpr reader, fuel, and `main` — which reads the
entry's named args as `(cell (name val)…)` on stdin, invokes the
entry, and prints a str payload raw (matching `krun --emit` output)
or the result sexpr. Refuse → kstderr + exit 4. The forward-decl block
for every `k_<def>` is prepended by `emitProgC` so call order in the
graph never matters. -/

def prelude : String :=
"#define _CRT_SECURE_NO_WARNINGS\n" ++
"/* freestanding: <stddef.h> is the only header (CompCert ships it);\n" ++
"   the libc surface used is declared as extern prototypes so the\n" ++
"   source parses without ANY hosted headers — ccomp reads it raw. */\n" ++
"#include <stddef.h>\n" ++
"typedef void FILE;\n" ++
"typedef long long k_i64;\n" ++
"#define KIMIN (-9223372036854775807LL-1)\n" ++
"#define KIMAX 9223372036854775807LL\n" ++
"#define EOF (-1)\n" ++
"extern void *malloc(size_t);\n" ++
"extern void *realloc(void*,size_t);\n" ++
"extern void *memcpy(void*,const void*,size_t);\n" ++
"extern void *memset(void*,int,size_t);\n" ++
"extern size_t strlen(const char*);\n" ++
"extern int strcmp(const char*,const char*);\n" ++
"extern char *strcpy(char*,const char*);\n" ++
"extern char *strcat(char*,const char*);\n" ++
"extern long long strtoll(const char*,char**,int);\n" ++
"extern long long atoll(const char*);\n" ++
"extern int snprintf(char*,size_t,const char*,...);\n" ++
"extern int getchar(void);\n" ++
"extern int fputs(const char*,FILE*);\n" ++
"extern int fputc(int,FILE*);\n" ++
"extern int fprintf(FILE*,const char*,...);\n" ++
"#ifdef _WIN32\n" ++
"extern FILE*__acrt_iob_func(unsigned);\n" ++
"#define kstdout (__acrt_iob_func(1))\n" ++
"#define kstderr (__acrt_iob_func(2))\n" ++
"#else\n" ++
"extern FILE *stdout,*stderr;\n" ++
"#define kstdout stdout\n" ++
"#define kstderr stderr\n" ++
"#endif\n" ++
"extern void exit(int);\n" ++
"/* generated by ISAR.KoruProgEmit — generated program below runtime */\n" ++
"static void *xm(size_t n){void*p=malloc(n?n:1);if(!p){fputs(\"oom\\n\",kstderr);exit(2);}return p;}\n" ++
"static void *xrealloc(void*p,size_t n){void*q=realloc(p,n?n:1);if(!q){fputs(\"oom\\n\",kstderr);exit(2);}return q;}\n" ++
"static char *xsd(const char*s){size_t n=strlen(s)+1;char*p=xm(n);memcpy(p,s,n);return p;}\n" ++
"/* str is a rope: concat conses (O(1)), s_flat materializes once\n" ++
"   and memoizes the node to a leaf. Semantics unchanged — the repr\n" ++
"   is the emitter's choice, not the program's. */\n" ++
"typedef struct S S;\n" ++
"struct S{size_t n;char*p;S*l,*r;};\n" ++
"static S*s_leaf(char*p){S*s=xm(sizeof(S));s->n=strlen(p);s->p=p;s->l=s->r=0;return s;}\n" ++
"static S*s_cat(S*a,S*b){S*s=xm(sizeof(S));s->n=a->n+b->n;s->p=0;s->l=a;s->r=b;return s;}\n" ++
"static char*s_flat(S*s){\n" ++
" if(!s->l)return s->p;\n" ++
" {char*p=xm(s->n+1),*q=p;size_t cap=64,sp=0;S**st=xm(cap*sizeof(S*));S*c=s;\n" ++
"  for(;;){while(c->l){if(sp==cap){cap*=2;st=xrealloc(st,cap*sizeof(S*));}st[sp++]=c->r;c=c->l;}\n" ++
"   memcpy(q,c->p,c->n);q+=c->n;if(!sp){*q=0;s->p=p;s->l=s->r=0;return p;}c=st[--sp];}}}\n" ++
"typedef struct Val Val;\n" ++
"struct Val{int tag;k_i64 i,d;int b;S*s;Val**xs;int nx;char**ns;Val**vs;int nf;};\n" ++
"/* tags: 0 int 1 float(n/d) 2 bool 3 str 4 arr 5 cell */\n" ++
"static Val*vn(int t){Val*v=xm(sizeof(Val));memset(v,0,sizeof(Val));v->tag=t;return v;}\n" ++
"static Val _VI[9216];static int _vok;\n" ++
"static Val*v_int(k_i64 i){\n" ++
" if(i>=-1024&&i<8192){\n" ++
"  if(!_vok){int j;for(j=0;j<9216;j++){_VI[j].tag=0;_VI[j].i=j-1024;}_vok=1;}\n" ++
"  return&_VI[(int)(i+1024)];}\n" ++
" {Val*v=vn(0);v->i=i;return v;}}\n" ++
"static Val*v_flt(k_i64 n,k_i64 d){Val*v=vn(1);v->i=n;v->d=d;return v;}\n" ++
"static Val _VB[2]={{2,0,0,0,0,0,0,0,0,0},{2,0,0,1,0,0,0,0,0,0}};\n" ++
"static Val*v_bool(int b){return&_VB[b?1:0];}\n" ++
"static Val*v_str(const char*s){Val*v=vn(3);v->s=s_leaf(xsd(s));return v;}\n" ++
"static Val*v_sref(char*s){Val*v=vn(3);v->s=s_leaf(s);return v;}\n" ++
"static Val*v_arr(Val**xs,int n){Val*v=vn(4);v->xs=xs;v->nx=n;return v;}\n" ++
"static Val*v_cell(char**ns,Val**vs,int n){Val*v=vn(5);v->ns=ns;v->vs=vs;v->nf=n;return v;}\n" ++
"static int veq(Val*a,Val*b){int i;\n" ++
" if(!a||!b||a->tag!=b->tag)return 0;\n" ++
" switch(a->tag){case 0:return a->i==b->i;case 1:return a->i==b->i&&a->d==b->d;\n" ++
"  case 2:return a->b==b->b;case 3:return!strcmp(s_flat(a->s),s_flat(b->s));\n" ++
"  case 4:if(a->nx!=b->nx)return 0;for(i=0;i<a->nx;i++)if(!veq(a->xs[i],b->xs[i]))return 0;return 1;\n" ++
"  case 5:if(a->nf!=b->nf)return 0;for(i=0;i<a->nf;i++)if(strcmp(a->ns[i],b->ns[i])||!veq(a->vs[i],b->vs[i]))return 0;return 1;}\n" ++
" return 0;}\n" ++
"typedef struct E E;\n" ++
"struct E{int cnt;const char**ns;Val**vs;const char*n;Val*v;E*x;};\n" ++
"/* env: single-slot frames (cnt<0) for arm binds; multi-slot frames\n" ++
"   for invoke/jump args — one alloc per call, names are literals. */\n" ++
"static E*ecn(const char*n,Val*v,E*x){E*e=xm(sizeof(E));e->cnt=-1;e->n=n;e->v=v;e->x=x;return e;}\n" ++
"static E*efr(const char**ns,Val**vs,int n,E*x){E*e=xm(sizeof(E)+n*sizeof(Val*));\n" ++
" e->cnt=n;e->ns=ns;e->vs=(Val**)(e+1);memcpy(e->vs,vs,n*sizeof(Val*));e->x=x;return e;}\n" ++
"static Val*elk(E*e,const char*n){int i;char c0=n[0];\n" ++
" for(;e;e=e->x){\n" ++
"  if(e->cnt<0){if(e->n[0]==c0&&!strcmp(e->n,n))return e->v;}\n" ++
"  else{for(i=e->cnt-1;i>=0;i--)if(e->ns[i][0]==c0&&!strcmp(e->ns[i],n))return e->vs[i];}}\n" ++
" return 0;}\n" ++
"typedef struct Res{int k;const char*br;Val*v;const char*jl;E*ja;}Res;\n" ++
"/* k: 1 result-bare 2 result-tag 3 done 4 jump ; 9 = internal skip */\n" ++
"static Res*rpool;\n" ++
"static Res*rn(int k){Res*r=rpool;if(r)rpool=(Res*)r->v;else r=xm(sizeof(Res));\n" ++
" memset(r,0,sizeof(Res));r->k=k;return r;}\n" ++
"static void rfree(Res*r){r->v=(Val*)rpool;rpool=r;}\n" ++
"static Res*r_bare(Val*v){Res*r=rn(1);r->v=v;return r;}\n" ++
"static Res*r_tag(const char*b,Val*v){Res*r=rn(2);r->br=b;r->v=v;return r;}\n" ++
"static Res*r_done(void){return rn(3);}\n" ++
"static Res*r_jump(const char*l,E*a){Res*r=rn(4);r->jl=l;r->ja=a;return r;}\n" ++
"static Res _sk;static Res*KSKIP(void){_sk.k=9;return&_sk;}\n" ++
"static k_i64 kfuel;\n" ++
"#define KSTEP() do{if(--kfuel<0)return 0;}while(0)\n" ++
"/* ---- int64 guarded arithmetic: overflow / d0 / KIMIN edge refuse ---- */\n" ++
"static int ovf_mul(k_i64 a,k_i64 b,k_i64*o){k_i64 x;\n" ++
" if(a==0||b==0){*o=0;return 0;}\n" ++
" if(a==KIMIN||b==KIMIN)return 1;\n" ++
" x=a*b;if(x/b!=a)return 1;*o=x;return 0;}\n" ++
"static int ovf_add(k_i64 a,k_i64 b,k_i64*o){\n" ++
" if((b>0&&a>KIMAX-b)||(b<0&&a<KIMIN-b))return 1;*o=a+b;return 0;}\n" ++
"static int ovf_sub(k_i64 a,k_i64 b,k_i64*o){\n" ++
" if((b<0&&a>KIMAX+b)||(b>0&&a<KIMIN+b))return 1;*o=a-b;return 0;}\n" ++
"static k_i64 ktdiv(k_i64 a,k_i64 b,int*ok){\n" ++
" if(b==0||(a==KIMIN&&b==-1)){*ok=0;return 0;}*ok=1;return a/b;}\n" ++
"static k_i64 ktmod(k_i64 a,k_i64 b,int*ok){\n" ++
" if(b==0||(a==KIMIN&&b==-1)){*ok=0;return 0;}*ok=1;return a%b;}\n" ++
"static k_i64 kfmod(k_i64 a,k_i64 b,int*ok){k_i64 r,o;\n" ++
" if(b==0||(a==KIMIN&&b==-1)){*ok=0;return 0;}\n" ++
" r=a%b;if(r!=0&&((r<0)!=(b<0))){if(ovf_add(r,b,&o)){*ok=0;return 0;}r=o;}\n" ++
" *ok=1;return r;}\n" ++
"/* ---- kfloatBin: exact rational ops, overflow refuses ---- */\n" ++
"static int asrat(Val*v,k_i64*n,k_i64*d){\n" ++
" if(!v)return 0;\n" ++
" if(v->tag==0){*n=v->i;*d=1;return 1;}\n" ++
" if(v->tag!=1||v->d==0)return 0;\n" ++
" if(v->d<0){if(v->i==KIMIN||v->d==KIMIN)return 0;*n=-v->i;*d=-v->d;}\n" ++
" else{*n=v->i;*d=v->d;}return 1;}\n" ++
"static Val*fb(int op,k_i64 n1,k_i64 d1,k_i64 n2,k_i64 d2){k_i64 t1,t2,t3;\n" ++
" switch(op){\n" ++
"  case 0:if(ovf_mul(n1,d2,&t1)||ovf_mul(n2,d1,&t2)||ovf_add(t1,t2,&t3)||ovf_mul(d1,d2,&t1))return 0;return v_flt(t3,t1);\n" ++
"  case 1:if(ovf_mul(n1,d2,&t1)||ovf_mul(n2,d1,&t2)||ovf_sub(t1,t2,&t3)||ovf_mul(d1,d2,&t1))return 0;return v_flt(t3,t1);\n" ++
"  case 2:if(ovf_mul(n1,n2,&t1)||ovf_mul(d1,d2,&t2))return 0;return v_flt(t1,t2);\n" ++
"  case 3:if(ovf_mul(d1,n2,&t2)||t2==0||ovf_mul(n1,d2,&t1))return 0;return v_flt(t1,t2);\n" ++
"  case 4:return 0;\n" ++
"  case 5:if(ovf_mul(n1,d2,&t1)||ovf_mul(n2,d1,&t2))return 0;return v_bool(t1==t2);\n" ++
"  case 6:if(ovf_mul(n1,d2,&t1)||ovf_mul(n2,d1,&t2))return 0;return v_bool(t1!=t2);\n" ++
"  case 7:if(ovf_mul(n1,d2,&t1)||ovf_mul(n2,d1,&t2))return 0;return v_bool(t1<t2);\n" ++
"  case 8:if(ovf_mul(n1,d2,&t1)||ovf_mul(n2,d1,&t2))return 0;return v_bool(t1<=t2);\n" ++
"  case 9:if(ovf_mul(n1,d2,&t1)||ovf_mul(n2,d1,&t2))return 0;return v_bool(t1>t2);\n" ++
"  case 10:if(ovf_mul(n1,d2,&t1)||ovf_mul(n2,d1,&t2))return 0;return v_bool(t1>=t2);}\n" ++
" return 0;}\n" ++
"/* ---- evalKBin ---- */\n" ++
"static Val*kbin(int op,Val*a,Val*b){k_i64 n1,d1,n2,d2,o;int ok;\n" ++
" if(a->tag==1||b->tag==1){\n" ++
"  if(!asrat(a,&n1,&d1)||!asrat(b,&n2,&d2))return 0;\n" ++
"  if(op>=11)return 0;return fb(op,n1,d1,n2,d2);}\n" ++
" if(a->tag==0&&b->tag==0)switch(op){\n" ++
"  case 0:if(ovf_add(a->i,b->i,&o))return 0;return v_int(o);\n" ++
"  case 1:if(ovf_sub(a->i,b->i,&o))return 0;return v_int(o);\n" ++
"  case 2:if(ovf_mul(a->i,b->i,&o))return 0;return v_int(o);\n" ++
"  case 3:o=ktdiv(a->i,b->i,&ok);return ok?v_int(o):0;\n" ++
"  case 4:o=ktmod(a->i,b->i,&ok);return ok?v_int(o):0;\n" ++
"  case 5:return v_bool(a->i==b->i);case 6:return v_bool(a->i!=b->i);\n" ++
"  case 7:return v_bool(a->i<b->i);case 8:return v_bool(a->i<=b->i);\n" ++
"  case 9:return v_bool(a->i>b->i);case 10:return v_bool(a->i>=b->i);}\n" ++
" if(a->tag==2&&b->tag==2)switch(op){\n" ++
"  case 5:return v_bool(a->b==b->b);case 6:return v_bool(a->b!=b->b);}\n" ++
" if(a->tag==3&&b->tag==3)switch(op){\n" ++
"  case 5:return v_bool(!strcmp(s_flat(a->s),s_flat(b->s)));case 6:return v_bool(strcmp(s_flat(a->s),s_flat(b->s))!=0);\n" ++
"  case 13:{Val*r=vn(3);r->s=s_cat(a->s,b->s);return r;}}\n" ++
" return 0;}\n" ++
"static Val*kun(int op,Val*a){\n" ++
" if(op==1&&a->tag==2)return v_bool(!a->b);\n" ++
" if(op==0&&a->tag==0){if(a->i==KIMIN)return 0;return v_int(-a->i);}\n" ++
" if(op==0&&a->tag==1){if(a->i==KIMIN)return 0;return v_flt(-a->i,a->d);}\n" ++
" return 0;}\n" ++
"/* ---- evalKBuiltin table ---- */\n" ++
"static Val*kbi(const char*n,Val**av,int na){k_i64 o;int ok;\n" ++
" if(!strcmp(n,\"as\")&&na==2)return av[1];\n" ++
" if((!strcmp(n,\"intCast\")||!strcmp(n,\"truncate\"))&&na==1)\n" ++
"  return(av[0]->tag==0)?av[0]:0;\n" ++
" if(!strcmp(n,\"divTrunc\")&&na==2){\n" ++
"  if(av[0]->tag!=0||av[1]->tag!=0)return 0;\n" ++
"  o=ktdiv(av[0]->i,av[1]->i,&ok);return ok?v_int(o):0;}\n" ++
" if(!strcmp(n,\"rem\")&&na==2){\n" ++
"  if(av[0]->tag!=0||av[1]->tag!=0)return 0;\n" ++
"  o=ktmod(av[0]->i,av[1]->i,&ok);return ok?v_int(o):0;}\n" ++
" if(!strcmp(n,\"mod\")&&na==2){\n" ++
"  if(av[0]->tag!=0||av[1]->tag!=0)return 0;\n" ++
"  o=kfmod(av[0]->i,av[1]->i,&ok);return ok?v_int(o):0;}\n" ++
" if(!strcmp(n,\"len\")&&na==1)return(av[0]->tag==4)?v_int(av[0]->nx):0;\n" ++
" if(!strcmp(n,\"intToString\")&&na==1){char b[32];\n" ++
"  if(av[0]->tag!=0)return 0;snprintf(b,32,\"%lld\",(long long)av[0]->i);return v_str(b);}\n" ++
" if(!strcmp(n,\"chars\")&&na==1){char*f;int i,nn;Val**xs;\n" ++
"  if(av[0]->tag!=3)return 0;f=s_flat(av[0]->s);nn=strlen(f);\n" ++
"  xs=xm((nn?nn:1)*sizeof(Val*));for(i=0;i<nn;i++)xs[i]=v_int((unsigned char)f[i]);\n" ++
"  return v_arr(xs,nn);}\n" ++
" if(!strcmp(n,\"charsToString\")&&na==1){char*p;int i;\n" ++
"  if(av[0]->tag!=4)return 0;p=xm(av[0]->nx+1);\n" ++
"  for(i=0;i<av[0]->nx;i++){\n" ++
"   if(av[0]->xs[i]->tag!=0||av[0]->xs[i]->i<0||av[0]->xs[i]->i>255)return 0;\n" ++
"   p[i]=(char)av[0]->xs[i]->i;}\n" ++
"  p[av[0]->nx]=0;return v_str(p);}\n" ++
" if(!strcmp(n,\"charToString\")&&na==1){char*p;\n" ++
"  if(av[0]->tag!=0||av[0]->i<0||av[0]->i>127)return 0;\n" ++
"  p=xm(2);p[0]=(char)av[0]->i;p[1]=0;return v_str(p);}\n" ++
" return 0;}\n" ++
"static Val*k_field(Val*o,const char*n){int i;\n" ++
" if(!o||o->tag!=5)return 0;for(i=o->nf-1;i>=0;i--)if(!strcmp(o->ns[i],n))return o->vs[i];return 0;}\n" ++
"static Val*k_index(Val*o,Val*i){\n" ++
" if(!o||!i||o->tag!=4||i->tag!=0||i->i<0||i->i>=o->nx)return 0;return o->xs[i->i];}\n" ++
"/* ---- sexpr value reader: (int N)(float n d)(bool t)(str \"..\")(arr v*)(cell (f v)*) ---- */\n" ++
"static const char*xp;\n" ++
"static void xws(void){while(*xp==' '||*xp=='\\t'||*xp=='\\n'||*xp=='\\r')xp++;}\n" ++
"static int xatom(char**o){const char*s;size_t n;char*p;\n" ++
" xws();s=xp;\n" ++
" if(*s=='\"'){s++;while(*s&&*s!='\"'){if(*s=='\\\\'&&s[1]){s+=2;continue;}s++;}if(*s!='\"')return 0;s++;}\n" ++
" else{while(*s&&*s!=' '&&*s!='\\t'&&*s!='\\n'&&*s!='\\r'&&*s!='('&&*s!=')')s++;}\n" ++
" if(s==xp)return 0;n=s-xp;p=xm(n+1);memcpy(p,xp,n);p[n]=0;xp=s;*o=p;return 1;}\n" ++
"static int xopen(void){xws();if(*xp=='('){xp++;return 1;}return 0;}\n" ++
"static int xclose(void){xws();if(*xp==')'){xp++;return 1;}return 0;}\n" ++
"static char*xunesc(char*a){char*w=a,*r=a;\n" ++
" for(;*r;r++){if(*r=='\\\\'&&r[1]){char d=r[1];\n" ++
"  if(d=='\"'||d=='\\\\'){*w++=d;r++;continue;}\n" ++
"  if(d=='n'){*w++='\\n';r++;continue;}\n" ++
"  if(d=='t'){*w++='\\t';r++;continue;}\n" ++
"  if(d=='r'){*w++='\\r';r++;continue;}}\n" ++
" *w++=*r;}*w=0;return a;}\n" ++
"static Val*xval(void){char*h;\n" ++
" if(!xopen()||!xatom(&h))return 0;\n" ++
" if(!strcmp(h,\"int\")){char*a;if(!xatom(&a))return 0;{k_i64 i=strtoll(a,0,10);if(!xclose())return 0;return v_int(i);}}\n" ++
" if(!strcmp(h,\"float\")){char*a,*b;if(!xatom(&a)||!xatom(&b))return 0;{k_i64 n=strtoll(a,0,10),d=strtoll(b,0,10);if(!xclose())return 0;return v_flt(n,d);}}\n" ++
" if(!strcmp(h,\"bool\")){char*a;if(!xatom(&a)||!xclose())return 0;\n" ++
"  if(!strcmp(a,\"true\"))return v_bool(1);if(!strcmp(a,\"false\"))return v_bool(0);return 0;}\n" ++
" if(!strcmp(h,\"str\")){char*a;if(!xatom(&a))return 0;{size_t n=strlen(a);if(n<2||a[0]!='\"'||a[n-1]!='\"')return 0;a[n-1]=0;if(!xclose())return 0;return v_str(xunesc(a+1));}}\n" ++
" if(!strcmp(h,\"arr\")){Val**xs=0;int n=0,c=0;\n" ++
"  for(;;){xws();if(*xp==')'){xp++;break;}{Val*v=xval();if(!v)return 0;\n" ++
"   if(n==c){c=c?c*2:8;xs=xrealloc(xs,c*sizeof(Val*));}xs[n++]=v;}}return v_arr(xs,n);}\n" ++
" if(!strcmp(h,\"cell\")){char**ns=0;Val**vs=0;int n=0,c=0;\n" ++
"  for(;;){xws();if(*xp==')'){xp++;break;}if(!xopen())return 0;\n" ++
"   {char*f;if(!xatom(&f))return 0;{Val*v=xval();if(!v)return 0;if(!xclose())return 0;\n" ++
"    if(n==c){c=c?c*2:8;ns=xrealloc(ns,c*sizeof(char*));vs=xrealloc(vs,c*sizeof(Val*));}\n" ++
"    ns[n]=xsd(f);vs[n]=v;n++;}}}return v_cell(ns,vs,n);}\n" ++
" return 0;}\n" ++
"static char*xrd(void){size_t c=8192,n=0;char*b=xm(c);int ch;\n" ++
" while((ch=getchar())!=EOF){if(n+1>=c){c*=2;b=xrealloc(b,c);}b[n++]=(char)ch;}b[n]=0;return b;}\n" ++
"static void pval(Val*v,FILE*f){int i;\n" ++
" if(!v){fputs(\"refuse\",f);return;}\n" ++
" switch(v->tag){case 0:fprintf(f,\"(int %lld)\",(long long)v->i);break;\n" ++
"  case 1:fprintf(f,\"(float %lld %lld)\",(long long)v->i,(long long)v->d);break;\n" ++
"  case 2:fprintf(f,\"(bool %s)\",v->b?\"true\":\"false\");break;\n" ++
"  case 3:fprintf(f,\"(str \\\"%s\\\")\",s_flat(v->s));break;\n" ++
"  case 4:fputs(\"(arr\",f);for(i=0;i<v->nx;i++){fputc(' ',f);pval(v->xs[i],f);}fputc(')',f);break;\n" ++
"  case 5:fputs(\"(cell\",f);for(i=0;i<v->nf;i++){fprintf(f,\" (%s \",v->ns[i]);pval(v->vs[i],f);fputc(')',f);}fputc(')',f);break;}}\n" ++
"static void pres(Res*r,FILE*f){\n" ++
" if(!r->br&&!r->v){fputs(\"(void)\",f);return;}\n" ++
" if(!r->br){fputs(\"(bare \",f);pval(r->v,f);fputc(')',f);return;}\n" ++
" fprintf(f,\"(tag %s\",r->br);if(r->v){fputc(' ',f);pval(r->v,f);}fputc(')',f);}\n"

/-- The driver: stdin `(cell (name val)…)` → entry env → print. -/
def driver (entry fuel : String) : String :=
"static Res *k_" ++ mangle entry ++ "(E *e);\n" ++
"int main(int argc,char**argv){Val*a;E*e;Res*r;int i;\n" ++
" (void)veq;(void)r_tag;(void)r_done;(void)r_jump;(void)kun;(void)fb;\n" ++
" (void)asrat;(void)kfmod;(void)ktdiv;(void)ktmod;(void)v_flt;(void)pval;\n" ++
" (void)v_arr;(void)v_cell;(void)ovf_mul;(void)ovf_add;(void)ovf_sub;\n" ++
" (void)k_field;(void)k_index;(void)ecn;(void)efr;(void)rfree;(void)v_sref;\n" ++
" kfuel=" ++ fuel ++ ";if(argc>1)kfuel=atoll(argv[1]);\n" ++
" xp=xrd();a=xval();\n" ++
" if(!a||a->tag!=5){fputs(\"refuse: args not a cell\\n\",kstderr);return 2;}\n" ++
" e=0;for(i=a->nf-1;i>=0;i--)e=ecn(a->ns[i],a->vs[i],e);\n" ++
" r=k_" ++ mangle entry ++ "(e);\n" ++
" if(!r||(r->k!=1&&r->k!=2)){fputs(\"refuse\\n\",kstderr);return 4;}\n" ++
" if(r->k==1&&!r->br&&r->v&&r->v->tag==3){fputs(s_flat(r->v->s),kstdout);fputc('\\n',kstdout);return 0;}\n" ++
" pres(r,kstdout);fputc('\\n',kstdout);return 0;}\n"

/-! ## Expression emission — one `ev_N(E *e)` per node

`and`/`or`/`cond` keep their short-circuit shape in generated code;
every other form is strict children-then-primitive, matching
`evalKE`. `builtin` args evaluate in order except `as`'s ignored
type position (its first arg is never evaluated, like the walker). -/

def binOpC : KBinOp → Int
  | .add => 0 | .sub => 1 | .mul => 2 | .div => 3 | .mod => 4
  | .eq => 5 | .ne => 6 | .lt => 7 | .le => 8 | .gt => 9 | .ge => 10
  | .and => 11 | .or => 12 | .concat => 13

def unOpC : KUnOp → Int
  | .neg => 0 | .not => 1

partial def genLitVal : KVal → EM String
  | .int i => do
      let f ← EM.fresh "vl"
      EM.put s!"static Val *{f}(void)\{\n return v_int({i});}\n"
      return f
  | .float n d => do
      let f ← EM.fresh "vl"
      EM.put s!"static Val *{f}(void)\{\n return v_flt({n},{d});}\n"
      return f
  | .bool b => do
      let f ← EM.fresh "vl"
      EM.put s!"static Val *{f}(void)\{\n return v_bool({if b then 1 else 0});}\n"
      return f
  | .str s => do
      let f ← EM.fresh "vl"
      EM.put s!"static Val *{f}(void)\{\n return v_sref((char*){cstr s});}\n"
      return f
  | .arr xs => do
      let gs ← xs.mapM genLitVal
      let f ← EM.fresh "vl"
      let sets := String.intercalate ""
        (gs.mapIdx fun i g => s!" xs[{i}]={g}();\n")
      EM.put s!"static Val *{f}(void)\{\n Val**xs=xm({xs.length}*sizeof(Val*));\n{sets} return v_arr(xs,{xs.length});}\n"
      return f
  | .cell fs => do
      let gs ← fs.mapM fun (n, v) => do
        let g ← genLitVal v
        return (n, g)
      let f ← EM.fresh "vl"
      let sets := String.intercalate ""
        (gs.mapIdx fun i p =>
          s!" ns[{i}]=(char*){cstr p.1};vs[{i}]={p.2}();\n")
      EM.put s!"static Val *{f}(void)\{\n char**ns=xm({fs.length}*sizeof(char*));\n Val**vs=xm({fs.length}*sizeof(Val*));\n{sets} return v_cell(ns,vs,{fs.length});}\n"
      return f

partial def genExpr : KExpr → EM String
  | .lit v => do
      let g ← genLitVal v
      let f ← EM.fresh "ev"
      EM.put s!"static Val *{f}(E *e)\{\n (void)e;return {g}();}\n"
      return f
  | .var s => do
      let f ← EM.fresh "ev"
      EM.put s!"static Val *{f}(E *e)\{\n return elk(e,{cstr s});}\n"
      return f
  | .bin .and l r => do
      let lf ← genExpr l; let rf ← genExpr r
      let f ← EM.fresh "ev"
      EM.put s!"static Val *{f}(E *e)\{\n Val*a={lf}(e);\n if(!a||a->tag!=2)return 0;\n if(!a->b)return v_bool(0);\n a={rf}(e);if(!a||a->tag!=2)return 0;return a;}\n"
      return f
  | .bin .or l r => do
      let lf ← genExpr l; let rf ← genExpr r
      let f ← EM.fresh "ev"
      EM.put s!"static Val *{f}(E *e)\{\n Val*a={lf}(e);\n if(!a||a->tag!=2)return 0;\n if(a->b)return v_bool(1);\n a={rf}(e);if(!a||a->tag!=2)return 0;return a;}\n"
      return f
  | .bin op l r => do
      let lf ← genExpr l; let rf ← genExpr r
      let f ← EM.fresh "ev"
      EM.put s!"static Val *{f}(E *e)\{\n Val*a={lf}(e);if(!a)return 0;\n Val*b={rf}(e);if(!b)return 0;\n return kbin({binOpC op},a,b);}\n"
      return f
  | .un op x => do
      let xf ← genExpr x
      let f ← EM.fresh "ev"
      EM.put s!"static Val *{f}(E *e)\{\n Val*a={xf}(e);if(!a)return 0;\n return kun({unOpC op},a);}\n"
      return f
  | .cond c t el => do
      let cf ← genExpr c; let tf ← genExpr t; let ef ← genExpr el
      let f ← EM.fresh "ev"
      EM.put s!"static Val *{f}(E *e)\{\n Val*a={cf}(e);\n if(!a||a->tag!=2)return 0;\n return a->b?{tf}(e):{ef}(e);}\n"
      return f
  | .field o n => do
      let of ← genExpr o
      let f ← EM.fresh "ev"
      EM.put s!"static Val *{f}(E *e)\{\n Val*a={of}(e);if(!a)return 0;\n return k_field(a,{cstr n});}\n"
      return f
  | .index o i => do
      let of ← genExpr o; let ifn ← genExpr i
      let f ← EM.fresh "ev"
      EM.put s!"static Val *{f}(E *e)\{\n Val*a={of}(e);if(!a)return 0;\n Val*b={ifn}(e);if(!b)return 0;\n return k_index(a,b);}\n"
      return f
  | .builtin name args => do
      -- `as` evaluates only its value position (the walker's laziness)
      let evs ←
        if name == "as" && args.length == 2 then
          match args[1]? with
          | some v => do
              let g ← genExpr v
              pure [(1, g)]
          | none => pure []
        else
          (args.mapIdx fun i a => (i, a)).mapM fun p => do
            let g ← genExpr p.2
            pure (p.1, g)
      let f ← EM.fresh "ev"
      let slots := String.intercalate ""
        (evs.map fun p => s!" av[{p.1}]={p.2}(e);if(!av[{p.1}])return 0;\n")
      EM.put s!"static Val *{f}(E *e)\{\n Val*av[{args.length}];\n{slots} return kbi({cstr name},av,{args.length});}\n"
      return f

/-! ## Arm / dispatch / callable emission

`aw_N(E *e, Res *r)` is armTry+armWalk: bind payload, eval guard,
walk the node. `ds_N(E *e, Res *r)` is one dispatch list (flow arms
or a conts chain): the tag/bare split is decided on the incoming
result, exactly like `.loop` and armWalk's inner dispatch. -/

mutual

partial def genArm (a : KArm) : EM String := do
  let f ← EM.fresh "aw"
  let bindStmt := match a.bind with
    | none => ""
    | some b => s!" if(!r->v)return 0;\n ee=ecn({cstr b},r->v,ee);\n"
  let condStmt ← match a.cond with
    | none => pure ""
    | some c => do
        let g ← genExpr c
        pure s!" \{Val *g={g}(ee);\n if(!g||g->tag!=2)return 0;\n if(!g->b)return KSKIP();}\n"
  let nodeStmt ← match a.node with
    | none => pure " return r_done();\n"
    | some .terminal => pure " return r_done();\n"
    | some (.produce e) => do
        let g ← genExpr e
        pure s!" \{Val *v={g}(ee);return v?r_bare(v):0;}\n"
    | some (.retCtor b e) => do
        let g ← genExpr e
        pure s!" \{Val *v={g}(ee);return v?r_tag({cstr b},v):0;}\n"
    | some (.jump t args) => do
        let argCode ← genNamedArgs "ee" args "ja"
        pure s!" \{E*ja=0;\n{argCode} return r_jump({cstr t},ja);}\n"
    | some (.invoke t args) => do
        let argCode ← genNamedArgs "ee" args "ae"
        let contStmt ←
          if a.conts.isEmpty then pure " return ir;\n"
          else do
            let d ← genDispatch a.conts
            pure s!" \{Res*ct={d}(ee,ir);rfree(ir);return ct;}\n"
        pure s!" \{E*ae=0;\n{argCode} Res*ir=k_{mangle t}(ae);\n if(!ir)return 0;\n if(ir->k!=1&&ir->k!=2)return 0;\n{contStmt}}\n"
  EM.put s!"static Res *{f}(E *e, Res *r)\{\n KSTEP();\n E*ee=e;(void)r;(void)ee;\n{bindStmt}{condStmt}{nodeStmt}}\n"
  return f

/-- Named-arg evaluation in source order — mirrors `evalKArgs`.
Each arg evaluates in the *caller* env, then all names bind as one
frame: `an_N` is a static literal table, `efr` copies the values —
one alloc per call where `ecn` spent one per arg plus a name dup. -/
partial def genNamedArgs (env : String)
    (args : List (String × KExpr)) (dst : String) : EM String := do
  if args.isEmpty then return ""
  let an ← EM.fresh "an"
  let tbl := String.intercalate "," (args.map fun p => cstr p.1)
  EM.put s!"static const char*{an}[]=\{{tbl}};\n"
  let parts ← (args.mapIdx fun i p => (i, p)).mapM fun q => do
    let g ← genExpr q.2.2
    pure s!" \{Val *v={g}({env});if(!v)return 0;av[{q.1}]=v;}\n"
  return s!" \{Val*av[{args.length}];\n{String.intercalate "" parts} {dst}=efr({an},av,{args.length},{dst});}\n"

/-- One dispatch list → `ds_N`. Tag dispatch tries only matching
branches (skipped arms cost nothing); bare dispatch tries every
arm in order and refuses *at* a catchall/empty-branch arm's
position — the `runK` refusal order, unrolled. -/
partial def genDispatch (arms : List KArm) : EM String := do
  let fns ← arms.mapM genArm
  let f ← EM.fresh "ds"
  let tagTries := String.intercalate ""
    ((arms.zip fns).map fun p =>
      s!" if(!strcmp(r->br,{cstr p.1.branch}))\{Res*t={p.2}(e,r);if(!t)return 0;if(t!=KSKIP())return t;}\n")
  let bareTries := String.intercalate ""
    ((arms.zip fns).map fun p =>
      if p.1.catchall || p.1.branch == "" then
        " return 0; /* catchall/empty arm refuses under bare dispatch */\n"
      else
        s!" \{Res*t={p.2}(e,r);if(!t)return 0;if(t!=KSKIP())return t;}\n")
  EM.put s!"static Res *{f}(E *e, Res *r)\{\n KSTEP();\n if(r->br)\{\n{tagTries} return 0;}\n if(!r->v)return 0;\n{bareTries} return 0;}\n"
  return f

partial def genCallable (name : String) (c : KCallable) : EM Unit := do
  let kn := "k_" ++ mangle name
  match c with
  | .thunk =>
      throw s!"axis: oracle/thunk ({name} is an asserted leaf — claim data, not program structure)"
  | .bare e => do
      let g ← genExpr e
      EM.put s!"static Res *{kn}(E *e)\{\n KSTEP();\n Val*v={g}(e);\n return v?r_bare(v):0;}\n"
  | .subflow fl => do
      let headArgs ← genNamedArgs "ce" fl.head.2 "he"
      let jumpStmt :=
        match fl.preLabel with
        | some pre =>
            s!"   if(t->k==4)\{if(!strcmp(t->jl,{cstr pre}))\{he=t->ja;rfree(h);rfree(t);continue;}return 0;}\n"
        | none => "   if(t->k==4)return 0;\n"
      let body ←
        if fl.arms.isEmpty then pure "   return h;\n"
        else do
          let d ← genDispatch fl.arms
          pure s!"   \{Res*t={d}(ce,h);\n   if(!t)return 0;\n   if(t->k==3)\{rfree(h);rfree(t);return r_bare(0);}\n{jumpStmt}   rfree(h);\n   return t;}\n"
      -- arm-less + arg-less flows (kChain's unrealized-leg stubs)
      -- never touch `ce` — silence -Wunused-parameter honestly.
      let unusedCe :=
        if fl.arms.isEmpty && fl.head.2.isEmpty then " (void)ce;\n"
        else ""
      EM.put s!"static Res *{kn}(E *ce)\{\n KSTEP();\n{unusedCe} E*he=0;\n{headArgs} for(;;)\{\n  KSTEP();\n  Res*h=k_{mangle fl.head.1}(he);\n  if(!h||(h->k!=1&&h->k!=2))return 0;\n{body} }\n}\n"

end

/-- Callee names inside one arm — `.invoke` targets only
(`.jump` is `#label`-local). Nested `conts` arms recurse. -/
partial def armRefs (a : KArm) : List String :=
  (match a.node with
   | some (.invoke t _) => [t]
   | _ => []) ++ a.conts.flatMap armRefs

/-- Graph edges out of one callable: the subflow head plus every
`.invoke` target reachable through its arms. -/
def callableRefs : KCallable → List String
  | .bare _ | .thunk => []
  | .subflow fl => fl.head.1 :: fl.arms.flatMap armRefs

/-- Names reachable from `entry` in `g.length` closure steps — enough:
each pass either reaches a fixpoint or adds at least one name.  The
generated program is the reachable subgraph; declared-but-unwired
legs (kChain's stub boundaries) stay in the declaration but don't
materialize as dead C functions (`-Wunused-function`). -/
def reachables (g : List (String × KCallable)) (entry : String) : List String :=
  (List.range g.length).foldl
    (fun seen _ =>
      g.foldl (fun s q =>
        if s.contains q.1 then
          (callableRefs q.2).foldl
            (fun s' n => if s'.contains n then s' else s' ++ [n]) s
        else s)
        seen)
    [entry]

/-- Emit `p` as a self-contained C99 program: runtime prelude,
forward decls, generated callables, driver `main`. Refuses with a
named axis when the program leaves the realized subset. -/
def emitProgC (p : KProg) (fuel : Nat) : Except String String :=
  if p.graph.isEmpty then .error "axis: empty graph"
  else if !p.graph.any (·.1 == p.entry) then .error "axis: entry missing"
  else
    let live := reachables p.graph p.entry
    let g := p.graph.filter (live.contains ·.1)
    let fwd := String.intercalate ""
      (g.map fun q => s!"static Res *k_{mangle q.1}(E *e);\n")
    match (g.mapM fun q => genCallable q.1 q.2).run {} with
    | .error e _ => .error e
    | .ok _ st => .ok (prelude ++ fwd ++ st.out ++ driver p.entry (toString fuel))

/-! ## kEmitProg — emitProgC spelled as a KProg

The whole-program emitter realized in the flow dialect: the same
`prelude ++ fwd ++ decls ++ driver` product, produced by a program
that walks the `quoteProg` quotation (tag-30 program → tag-29/27/28
callables → tag-25 flows → tag-22 arms → tag-16…20 nodes →
tag-8…15 exprs → tag-1…6 vals) instead of the `KProg` inductive.

Two dialect adaptations from the host algorithm, each declared:

  * **Fresh names by structural count, not threaded state.**  The
    dialect returns exactly one `KVal` per call — `EM`'s
    `{counter, buffer}` pair cannot ride back.  `n` therefore goes
    *down* as a parameter (each `dc*` fold computes exactly the
    `EM.fresh` count a subtree allocates: `aw`/`an` allocate first
    in their frame, `ev`/`vl`/`ds` last) and the decl text comes
    back as the single result.  Byte-identical output, no packing.
  * **`mangle`/`cstrBody` as byte loops.**  Strings are atomic in
    the dialect; `chars`/`charsToString`/`charToString` (the
    emission leg's additive builtins) give the byte view.  The
    authority's `Char.isAlphanum`/`toNat` are code-point-level —
    identical on ASCII, which is the declared wire surface.

Refusals are structural like `kEmit`'s: a shape no arm matches
produces no result — `axis:` names stay host-side.

The emit entry is `{src: program, fuel: i64}` — `fuel` is the
target claim's own fuel, becoming the emitted driver's `kfuel`
default, the same position `emitProgC`'s parameter holds. -/

private def qs (s : String) : KExpr := .lit (.str s)
private def qv (n : String) : KExpr := .var n
private def qcnd (c t e : KExpr) : KExpr := .cond c t e
private def qgt (a b : KExpr) : KExpr := .bin .gt a b
private def qdv (a b : KExpr) : KExpr := .bin .div a b
private def qmd (a b : KExpr) : KExpr := .bin .mod a b
private def qix (e i : KExpr) : KExpr := .index e i
private def qcs (e : KExpr) : KExpr := .builtin "chars" [e]
private def qc1s (e : KExpr) : KExpr := .builtin "charToString" [e]

/-- Concat of a list of exprs (right-nested). -/
private def qcc : List KExpr → KExpr
  | [] => qs ""
  | [x] => x
  | x :: xs => qcat x (qcc xs)

/-- `xs[i]` in surface terms. -/
private def qat (e : KExpr) (i : KExpr) : KExpr := .index e i
/-- `e.kids` field. -/
private def qks (e : KExpr) : KExpr := qf e "kids"
/-- `e.kids[i]`. -/
private def qk (e : KExpr) (i : Int) : KExpr := qat (qks e) (qint i)
/-- `e.tag`. -/
private def qtg (e : KExpr) : KExpr := qf e "tag"

/-- ASCII C-identifier char: alnum or `_` (byte-level twin of
`mangle`'s keep-set — `Char.isAlphanum` agrees on ASCII). -/
private def qIdentC (c : KExpr) : KExpr :=
  qor (qor (qand (qge c (qint 48)) (qle c (qint 57)))
           (qand (qge c (qint 65)) (qle c (qint 90))))
      (qor (qand (qge c (qint 97)) (qle c (qint 122)))
            (qeq c (qint 95)))

/-- `| br b [when c] |> t(args)` continuing into `ct`. -/
private def qiv (br : String) (b : Option String) (c : Option KExpr)
    (t : String) (args : List (String × KExpr)) (ct : List KArm := [])
    : KArm :=
  .mk br false b c (some (.invoke t args)) ct

/-- Chain of invokes followed by a produce: steps
`[(m,"A",args),(r,"B",args')]` then `z` binds the last result
and `fin` produces from the env —
`|> A : m |> B : r |> (z) -> fin`. -/
private def qchain (steps : List (String × String ×
    List (String × KExpr))) (bind : String) (fin : KExpr)
    : List KArm :=
  match steps with
  | [] => [.mk "_chain" false (some bind) none
      (some (.produce fin)) []]
  | (b, t, a) :: xs =>
      [.mk "_chain" false (some b) none (some (.invoke t a))
        (qchain xs bind fin)]

/-- `| br b [when c] -> e`. -/
private def qp (br : String) (b : Option String) (c : Option KExpr)
    (e : KExpr) : KArm :=
  .mk br false b c (some (.produce e)) []

/-- `| _ b -> e` — an unconditional produce arm. -/
private def qp1 (b : Option String) (e : KExpr) : KArm :=
  qp "_" b none e

/-- `| _ b |> t(args)` — unconditional invoke arm, no conts. -/
private def qiv1s (b : Option String) (t : String)
    (args : List (String × KExpr)) : KArm :=
  qiv "_" b none t args []

/-- Set an arm's guard: `a` with `cond := some g`. -/
private def qArmG (g : KExpr) (a : KArm) : KArm :=
  match a with
  | .mk br ca b _ n cs => .mk br ca b (some g) n cs

/-- `| _ b |> t(args) : chain… -> fin` — invoke then nested
`_chain` binds ending in a produce. -/
private def qivc (b : Option String) (t : String)
    (args : List (String × KExpr))
    (steps : List (String × String × List (String × KExpr)))
    (fin : String) (e : KExpr) : KArm :=
  qiv "_" b none t args (qchain steps fin e)

-- ---------- shared small callables ----------

/-- `ep-id {x}` — echo: the generic head callable. -/
private def kEpId : String × KCallable :=
  ("ep-id", .bare (qv "x"))

/-- `ep-peek {cs,i,n}` — `cs[i]` or `-1` (int-array loop head). -/
private def kEpPeek : String × KCallable :=
  ("ep-peek", .bare
    (qcnd (qlt (qv "i") (qv "n")) (qix (qv "cs") (qv "i"))
      (qint (-1))))

/-- `ep-step {i,n}` — `i` or `-1` (loop head where the element is
not the dispatchable value). -/
private def kEpStep : String × KCallable :=
  ("ep-step", .bare
    (qcnd (qlt (qv "i") (qv "n")) (qv "i") (qint (-1))))

/-- `ep-tg {x}` — `x.tag` (tag-dispatch head). -/
private def kEpTg : String × KCallable :=
  ("ep-tg", .bare (qtg (qv "x")))

/-- Guarded `_chain`-style arm carrying a `when`. -/
private def qcg (b : Option String) (c : KExpr) (node : KArmNode)
    : KArm :=
  .mk "_chain" false b (some c) (some node) []

/-- Standard step-loop arms: `stop` at `c<0` produces `fin`;
the caller supplies the `go` arm(s). -/
private def qstop (fin : KExpr) : KArm :=
  qp "stop" (some "c") (some (qlt (qv "c") (qint 0))) fin

-- ---------- char/string helpers ----------

/-- `ep-ml {cs,i,n,out}` — `mangle` byte loop. -/
private def kEpMl : String × KCallable :=
  ("ep-ml", .subflow {
    preLabel := none
    head := ("ep-peek", [("cs", qv "cs"), ("i", qv "i"),
                          ("n", qv "n")])
    arms := [
      qstop (qv "out")
    , qiv "go" (some "c") none "ep-ml"
        [("cs", qv "cs"), ("i", qadd (qv "i") (qint 1)),
         ("n", qv "n"),
         ("out", qcat (qv "out")
           (qcnd (qIdentC (qv "c")) (qc1s (qv "c")) (qs "_")))]
    ] })

/-- `ep-m {s}` — `mangle`. -/
private def kEpM : String × KCallable :=
  ("ep-m", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "s")])
    arms := [qiv1s (some "v") "ep-ml"
      [("cs", qcs (qv "v")), ("i", qint 0),
       ("n", qlen (qcs (qv "v"))), ("out", qs "")]] })

/-- `ep-ec {c}` — `cstrBody` per byte: `\"` `\\` `\n` `\t` `\r`,
printable ASCII passthrough, else `\ooo` octal (≤255). -/
private def kEpEc : String × KCallable :=
  ("ep-ec", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "c")])
    arms := [
      qp "dq" (some "k") (some (qeq (qv "k") (qint 34)))
        (qs "\\\"")
    , qp "bs" (some "k") (some (qeq (qv "k") (qint 92)))
        (qs "\\\\")
    , qp "nl" (some "k") (some (qeq (qv "k") (qint 10)))
        (qs "\\n")
    , qp "tb" (some "k") (some (qeq (qv "k") (qint 9)))
        (qs "\\t")
    , qp "cr" (some "k") (some (qeq (qv "k") (qint 13)))
        (qs "\\r")
    , qp "asc" (some "k")
        (some (qand (qge (qv "k") (qint 32))
                    (qle (qv "k") (qint 126))))
        (qc1s (qv "k"))
    , qp "oct" (some "k") (some (qle (qv "k") (qint 255)))
        (qcc [qs "\\",
              qc1s (qadd (qint 48) (qdv (qv "k") (qint 64))),
              qc1s (qadd (qint 48)
                (qmd (qdv (qv "k") (qint 8)) (qint 8))),
              qc1s (qadd (qint 48) (qmd (qv "k") (qint 8)))])
    ] })

/-- `ep-el {cs,i,n,out}` — `cstrBody` loop. -/
private def kEpEl : String × KCallable :=
  ("ep-el", .subflow {
    preLabel := none
    head := ("ep-peek", [("cs", qv "cs"), ("i", qv "i"),
                          ("n", qv "n")])
    arms := [
      qstop (qv "out")
    , qivc (some "c") "ep-ec" [("c", qv "c")]
        [("p", "ep-el",
            [("cs", qv "cs"), ("i", qadd (qv "i") (qint 1)),
             ("n", qv "n"),
             ("out", qcat (qv "out") (qv "p"))])]
        "s" (qv "s")
    ] })

/-- `ep-e {s}` — `cstrBody`. -/
private def kEpE : String × KCallable :=
  ("ep-e", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "s")])
    arms := [qiv1s (some "v") "ep-el"
      [("cs", qcs (qv "v")), ("i", qint 0),
       ("n", qlen (qcs (qv "v"))), ("out", qs "")]] })

/-- `ep-cq {s}` — `cstr`: `"` + body + `"`. -/
private def kEpCq : String × KCallable :=
  ("ep-cq", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "s")])
    arms := [qivc (some "v") "ep-e" [("s", qv "v")] []
        "b" (qcc [qs "\"", qv "b", qs "\""])] })

/-- `ep-mi {cs,ss,i,j,sn}` — inner compare for `ep-mems`:
`cs[j] == ss[i+j]` for all `j < sn` → 1 else 0. -/
private def kEpMi : String × KCallable :=
  ("ep-mi", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "j")])
    arms := [
      qp "done" (some "j") (some (qge (qv "j") (qv "sn")))
        (qint 1)
    , qiv "eq" (some "j")
        (some (qeq (qix (qv "ss") (qadd (qv "i") (qv "j")))
                   (qix (qv "cs") (qv "j"))))
        "ep-mi"
        [("cs", qv "cs"), ("ss", qv "ss"), ("i", qv "i"),
         ("j", qadd (qv "j") (qint 1)), ("sn", qv "sn")]
    , qp1 (some "j") (qint 0)
    ] })

/-- `ep-mo {cs,ss,i,sn}` — outer scan for `ep-mems`: try `|s|` at
each position `i` of `ss`. -/
private def kEpMo : String × KCallable :=
  ("ep-mo", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "i")])
    arms := [
      qp "stop" (some "i")
        (some (qgt (qv "i")
          (qsub (qlen (qv "ss")) (qv "sn"))))
        (qint 0)
    , .mk "go" false (some "i") none
        (some (.invoke "ep-mi"
          [("cs", qv "cs"), ("ss", qv "ss"), ("i", qv "i"),
           ("j", qint 0), ("sn", qv "sn")]))
        [ qcg (some "m") (qeq (qv "m") (qint 1))
            (.produce (qint 1))
        , qiv "_chain" (some "m") none "ep-mo"
            [("cs", qv "cs"), ("ss", qv "ss"),
             ("i", qadd (qv "i") (qint 1)), ("sn", qv "sn")]
        ]
    ] })

/-- `ep-mems {st,s}` — 1 iff `st` (a `|a|b|` set-string) contains
`s`; the `|`-sentinel defeats prefix collisions. -/
private def kEpMems : String × KCallable :=
  ("ep-mems", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "s")])
    arms := [qiv1s (some "v") "ep-mo"
      [("cs", qcs (qcc [qs "|", qv "v", qs "|"])),
       ("ss", qcs (qv "st")), ("i", qint 0),
       ("sn", qlen (qcs (qcc [qs "|", qv "v", qs "|"])))] ] })

-- ---------- dc family: structural EM.fresh counts ----------
-- Each `dc*` computes exactly the fresh names `gen*` allocates
-- in its subtree: `aw`/`an` allocate first in their frame,
-- `ev`/`vl`/`ds` last.  The caller can then name each child's
-- thunk `ev_(n + dc(child) - 1)` without threading state.

/-- `ep-dv {v}` — `dcV`. -/
private def kEpDv : String × KCallable :=
  ("ep-dv", .subflow {
    preLabel := none
    head := ("ep-tg", [("x", qv "v")])
    arms := [
      qp "leaf" (some "t") (some (qle (qv "t") (qint 4)))
        (qint 1)
    , qivc (some "t") "ep-dvl"
        [("xs", qk (qv "v") 0), ("i", qint 0),
         ("n", qlen (qk (qv "v") 0))]
        [] "m" (qadd (qv "m") (qint 1))
        |> qArmG (qeq (qv "t") (qint 5))
    , qivc (some "t") "ep-dpl"
        [("xs", qk (qv "v") 0), ("i", qint 0),
         ("n", qlen (qk (qv "v") 0))]
        [] "m" (qadd (qv "m") (qint 1))
        |> qArmG (qeq (qv "t") (qint 6))
    ] })

/-- `ep-dvl {xs,i,n}` — `dcV` summed over a quoted arr's elems. -/
private def kEpDvl : String × KCallable :=
  ("ep-dvl", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qint 0)
    , qivc (some "c") "ep-dv" [("v", qix (qv "xs") (qv "c"))]
        [("m", "ep-dvl", [("xs", qv "xs"),
            ("i", qadd (qv "c") (qint 1)), ("n", qv "n")])]
        "r" (qadd (qv "m") (qv "r"))
    ] })

/-- `ep-dpl {xs,i,n}` — `dcV` summed over pair values. -/
private def kEpDpl : String × KCallable :=
  ("ep-dpl", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qint 0)
    , qivc (some "c") "ep-dv"
        [("v", qf (qix (qv "xs") (qv "c")) "v")]
        [("m", "ep-dpl", [("xs", qv "xs"),
            ("i", qadd (qv "c") (qint 1)), ("n", qv "n")])]
        "r" (qadd (qv "m") (qv "r"))
    ] })

/-- `ep-dbc {e,i,n,nm}` — one builtin arg's `dcE`; the `as`-2
env arg contributes 0 (it is not emitted as an `ev`). -/
private def kEpDbc : String × KCallable :=
  ("ep-dbc", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "e")])
    arms := [
      qp "skip" (some "x")
        (some (qand (qeq (qv "nm") (qs "as"))
              (qand (qeq (qv "n") (qint 2))
                    (qeq (qv "i") (qint 0)))))
        (qint 0)
    , qiv1s (some "x") "ep-de" [("e", qv "x")]
    ] })

/-- `ep-dbb {nm,xs,i,n}` — builtin args `dcE` sum. -/
private def kEpDbb : String × KCallable :=
  ("ep-dbb", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qint 0)
    , qivc (some "c") "ep-dbc"
        [("e", qix (qv "xs") (qv "c")), ("i", qv "c"),
         ("n", qv "n"), ("nm", qv "nm")]
        [("m", "ep-dbb", [("nm", qv "nm"), ("xs", qv "xs"),
            ("i", qadd (qv "c") (qint 1)), ("n", qv "n")])]
        "r" (qadd (qv "m") (qv "r"))
    ] })

/-- `ep-de {e}` — `dcE`. -/
private def kEpDe : String × KCallable :=
  ("ep-de", .subflow {
    preLabel := none
    head := ("ep-tg", [("x", qv "e")])
    arms := [
      qivc (some "t") "ep-dv" [("v", qk (qv "e") 0)]
        [] "m" (qadd (qv "m") (qint 1))
        |> qArmG (qeq (qv "t") (qint 8))
    , qp "var" (some "t") (some (qeq (qv "t") (qint 9))) (qint 1)
    , qivc (some "t") "ep-de" [("e", qk (qv "e") 1)]
        [("a", "ep-de", [("e", qk (qv "e") 2)])]
        "b" (qadd (qint 1) (qadd (qv "a") (qv "b")))
        |> qArmG (qeq (qv "t") (qint 10))
    , qivc (some "t") "ep-de" [("e", qk (qv "e") 1)]
        [] "a" (qadd (qv "a") (qint 1))
        |> qArmG (qeq (qv "t") (qint 11))
    , qivc (some "t") "ep-de" [("e", qk (qv "e") 0)]
        [("a", "ep-de", [("e", qk (qv "e") 1)]),
         ("b", "ep-de", [("e", qk (qv "e") 2)])]
        "c" (qadd (qint 1)
          (qadd (qv "a") (qadd (qv "b") (qv "c"))))
        |> qArmG (qeq (qv "t") (qint 12))
    , qivc (some "t") "ep-de" [("e", qk (qv "e") 0)]
        [] "a" (qadd (qv "a") (qint 1))
        |> qArmG (qeq (qv "t") (qint 13))
    , qivc (some "t") "ep-de" [("e", qk (qv "e") 0)]
        [("a", "ep-de", [("e", qk (qv "e") 1)])]
        "b" (qadd (qint 1) (qadd (qv "a") (qv "b")))
        |> qArmG (qeq (qv "t") (qint 14))
    , qivc (some "t") "ep-dbb"
        [("nm", qk (qv "e") 0), ("xs", qk (qv "e") 1),
         ("i", qint 0), ("n", qlen (qk (qv "e") 1))]
        [] "m" (qadd (qv "m") (qint 1))
        |> qArmG (qeq (qv "t") (qint 15))
    ] })

/-- `ep-doc {o}` — opt-expr `dcE`: none→0, some→`dcE`. -/
private def kEpDoc : String × KCallable :=
  ("ep-doc", .subflow {
    preLabel := none
    head := ("ep-tg", [("x", qv "o")])
    arms := [
      qp "none" (some "t") (some (qeq (qv "t") (qint 23)))
        (qint 0)
    , qiv "some" (some "t") (some (qeq (qv "t") (qint 24)))
        "ep-de" [("e", qk (qv "o") 0)]
    ] })

/-- `ep-dc0 {cs}` — conts `dcD` when nonempty, else 0. -/
private def kEpDc0 : String × KCallable :=
  ("ep-dc0", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "cs")])
    arms := [
      qp "empty" (some "x")
        (some (qeq (qlen (qv "x")) (qint 0))) (qint 0)
    , qiv1s (some "x") "ep-dd" [("xs", qv "x")]
    ] })

/-- `ep-dn {nd,cs}` — node `dc` (conts threaded for invoke). -/
private def kEpDn : String × KCallable :=
  ("ep-dn", .subflow {
    preLabel := none
    head := ("ep-tg", [("x", qv "nd")])
    arms := [
      qp "term" (some "t") (some (qeq (qv "t") (qint 16)))
        (qint 0)
    , qiv "jmp" (some "t") (some (qeq (qv "t") (qint 17)))
        "ep-dg" [("xs", qk (qv "nd") 1)]
    , qivc (some "t") "ep-dg" [("xs", qk (qv "nd") 1)]
        [("a", "ep-dc0", [("cs", qv "cs")])]
        "b" (qadd (qv "a") (qv "b"))
        |> qArmG (qeq (qv "t") (qint 18))
    , qiv "prod" (some "t") (some (qeq (qv "t") (qint 19)))
        "ep-de" [("e", qk (qv "nd") 0)]
    , qiv "ctor" (some "t") (some (qeq (qv "t") (qint 20)))
        "ep-de" [("e", qk (qv "nd") 1)]
    ] })

/-- `ep-don {o,cs}` — node-opt `dc`: none→0, some→`ep-dn`. -/
private def kEpDon : String × KCallable :=
  ("ep-don", .subflow {
    preLabel := none
    head := ("ep-tg", [("x", qv "o")])
    arms := [
      qp "none" (some "t") (some (qeq (qv "t") (qint 23)))
        (qint 0)
    , qiv "nd" (some "t") (some (qeq (qv "t") (qint 24)))
        "ep-dn" [("nd", qk (qv "o") 0), ("cs", qv "cs")]
    ] })

/-- `ep-dal {xs,i,n}` — `dcA` summed over an arm list. -/
private def kEpDal : String × KCallable :=
  ("ep-dal", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qint 0)
    , qivc (some "c") "ep-da" [("a", qix (qv "xs") (qv "c"))]
        [("m", "ep-dal", [("xs", qv "xs"),
            ("i", qadd (qv "c") (qint 1)), ("n", qv "n")])]
        "r" (qadd (qv "m") (qv "r"))
    ] })

/-- `ep-dd {xs}` — `dcD` = the `ds` fn + `dcA` of each arm. -/
private def kEpDd : String × KCallable :=
  ("ep-dd", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "xs")])
    arms := [qivc (some "x") "ep-dal"
      [("xs", qv "x"), ("i", qint 0), ("n", qlen (qv "x"))]
      [] "m" (qadd (qv "m") (qint 1))] })

/-- `ep-da {a}` — `dcA` = `aw` + cond `dcE` + node part. -/
private def kEpDa : String × KCallable :=
  ("ep-da", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "a")])
    arms := [qivc (some "x") "ep-doc" [("o", qk (qv "x") 3)]
      [("c", "ep-don", [("o", qk (qv "x") 4),
          ("cs", qk (qv "x") 5)])]
      "d" (qadd (qint 1) (qadd (qv "c") (qv "d")))] })

/-- `ep-dgl {xs,i,n}` — `dcE` summed over named-expr values. -/
private def kEpDgl : String × KCallable :=
  ("ep-dgl", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qint 0)
    , qivc (some "c") "ep-de"
        [("e", qf (qix (qv "xs") (qv "c")) "v")]
        [("m", "ep-dgl", [("xs", qv "xs"),
            ("i", qadd (qv "c") (qint 1)), ("n", qv "n")])]
        "r" (qadd (qv "m") (qv "r"))
    ] })

/-- `ep-dg {xs}` — `dc` of `genNamedArgs`: 0 when empty, else
`an` + arg expr counts. -/
private def kEpDg : String × KCallable :=
  ("ep-dg", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "xs")])
    arms := [
      qp "empty" (some "x")
        (some (qeq (qlen (qv "x")) (qint 0))) (qint 0)
    , qivc (some "x") "ep-dgl"
        [("xs", qv "x"), ("i", qint 0), ("n", qlen (qv "x"))]
        [] "m" (qadd (qv "m") (qint 1))
    ] })

/-- `ep-df2 {xs}` — arms `dcD` or 0 when empty. -/
private def kEpDf2 : String × KCallable :=
  ("ep-df2", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "xs")])
    arms := [
      qp "empty" (some "x")
        (some (qeq (qlen (qv "x")) (qint 0))) (qint 0)
    , qiv1s (some "x") "ep-dd" [("xs", qv "x")]
    ] })

/-- `ep-df {fl}` — `dc` of a flow: head args `dc` + arms `dc`. -/
private def kEpDf : String × KCallable :=
  ("ep-df", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "fl")])
    arms := [qivc (some "x") "ep-dg"
      [("xs", qk (qk (qv "x") 1) 1)]
      [("a", "ep-df2", [("xs", qk (qv "x") 2)])]
      "b" (qadd (qv "a") (qv "b"))] })

/-- `ep-dc {c}` — `dcC` = the body's `dc`. The `k_<mangle>`
decl is named, not numbered — no `EM.fresh` is consumed for it.
Thunks match no arm → refuse. -/
private def kEpDc : String × KCallable :=
  ("ep-dc", .subflow {
    preLabel := none
    head := ("ep-tg", [("x", qv "c")])
    arms := [
      qivc (some "t") "ep-de" [("e", qk (qv "c") 0)]
        [] "a" (qv "a")
        |> qArmG (qeq (qv "t") (qint 27))
    , qivc (some "t") "ep-df" [("fl", qk (qv "c") 0)]
        [] "a" (qv "a")
        |> qArmG (qeq (qv "t") (qint 29))
    ] })

-- ---------- g family: declaration text ----------

/-- `ep-gvl {xs,i,n,m,out}` — decls for a quoted arr's element
values; `m` is the running counter. -/
private def kEpGvl : String × KCallable :=
  ("ep-gvl", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qv "out")
    , qivc (some "c") "ep-gv"
        [("v", qix (qv "xs") (qv "c")), ("n", qv "m")]
        [("d", "ep-dv", [("v", qix (qv "xs") (qv "c"))]),
         ("dm", "ep-gvl", [("xs", qv "xs"),
            ("i", qadd (qv "c") (qint 1)), ("n", qv "n"),
            ("m", qadd (qv "m") (qv "dm")),
            ("out", qcat (qv "out") (qv "d"))])]
        "r" (qv "r")
    ] })

/-- `ep-gvs {xs,i,n,m,out}` — `xs[i]=vl_…();` set lines. -/
private def kEpGvs : String × KCallable :=
  ("ep-gvs", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qv "out")
    , qivc (some "c") "ep-dv" [("v", qix (qv "xs") (qv "c"))]
        [("dm", "ep-gvs", [("xs", qv "xs"),
            ("i", qadd (qv "c") (qint 1)), ("n", qv "n"),
            ("m", qadd (qv "m") (qv "dm")),
            ("out", qcc [qv "out", qs " xs[", qitoa (qv "c"),
              qs "]=vl",
              qitoa (qadd (qv "m") (qsub (qv "dm") (qint 1))),
              qs "();\n"])])]
        "r" (qv "r")
    ] })

/-- `ep-gpl {xs,i,n,m,out}` — decls for a quoted cell's pair
values. -/
private def kEpGpl : String × KCallable :=
  ("ep-gpl", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qv "out")
    , qivc (some "c") "ep-gv"
        [("v", qf (qix (qv "xs") (qv "c")) "v"), ("n", qv "m")]
        [("d", "ep-dv",
            [("v", qf (qix (qv "xs") (qv "c")) "v")]),
         ("dm", "ep-gpl", [("xs", qv "xs"),
            ("i", qadd (qv "c") (qint 1)), ("n", qv "n"),
            ("m", qadd (qv "m") (qv "dm")),
            ("out", qcat (qv "out") (qv "d"))])]
        "r" (qv "r")
    ] })

/-- `ep-gps {xs,i,n,m,out}` — `ns[i]=(char*)"…";vs[i]=vl_…();`
set lines. -/
private def kEpGps : String × KCallable :=
  ("ep-gps", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qv "out")
    , qivc (some "c") "ep-cq"
        [("s", qf (qix (qv "xs") (qv "c")) "name")]
        [("q", "ep-dv",
            [("v", qf (qix (qv "xs") (qv "c")) "v")]),
         ("dm", "ep-gps", [("xs", qv "xs"),
            ("i", qadd (qv "c") (qint 1)), ("n", qv "n"),
            ("m", qadd (qv "m") (qv "dm")),
            ("out", qcc [qv "out", qs " ns[", qitoa (qv "c"),
              qs "]=(char*)", qv "q", qs ";vs[",
              qitoa (qv "c"), qs "]=vl",
              qitoa (qadd (qv "m") (qsub (qv "dm") (qint 1))),
              qs "();\n"])])]
        "r" (qv "r")
    ] })

/-- `ep-gv {v,n}` — `genLitVal`: element decls then the `vl` fn
(last fresh in the subtree). -/
private def kEpGv : String × KCallable :=
  ("ep-gv", .subflow {
    preLabel := none
    head := ("ep-tg", [("x", qv "v")])
    arms := [
      qp "int" (some "t") (some (qeq (qv "t") (qint 1)))
        (qcc [qs "static Val *vl", qitoa (qv "n"),
              qs "(void){\n return v_int(",
              qitoa (qk (qv "v") 0), qs ");}\n"])
    , qp "flt" (some "t") (some (qeq (qv "t") (qint 2)))
        (qcc [qs "static Val *vl", qitoa (qv "n"),
              qs "(void){\n return v_flt(",
              qitoa (qk (qv "v") 0), qs ",",
              qitoa (qk (qv "v") 1), qs ");}\n"])
    , qp "boo" (some "t") (some (qeq (qv "t") (qint 3)))
        (qcc [qs "static Val *vl", qitoa (qv "n"),
              qs "(void){\n return v_bool(",
              qitoa (qk (qv "v") 0), qs ");}\n"])
    , qivc (some "t") "ep-cq" [("s", qk (qv "v") 0)]
        [] "q" (qcc [qs "static Val *vl", qitoa (qv "n"),
              qs "(void){\n return v_sref((char*)", qv "q",
              qs ");}\n"])
        |> qArmG (qeq (qv "t") (qint 4))
    , qivc (some "t") "ep-gvl"
        [("xs", qk (qv "v") 0), ("i", qint 0),
         ("n", qlen (qk (qv "v") 0)), ("m", qv "n"),
         ("out", qs "")]
        [("d", "ep-gvs",
            [("xs", qk (qv "v") 0), ("i", qint 0),
             ("n", qlen (qk (qv "v") 0)), ("m", qv "n"),
             ("out", qs "")]),
         ("st", "ep-dvl",
            [("xs", qk (qv "v") 0), ("i", qint 0),
             ("n", qlen (qk (qv "v") 0))])]
        "dm" (qcc [qv "d", qs "static Val *vl",
              qitoa (qadd (qv "n") (qv "dm")),
              qs "(void){\n Val**xs=xm(",
              qitoa (qlen (qk (qv "v") 0)),
              qs "*sizeof(Val*));\n", qv "st",
              qs " return v_arr(xs,",
              qitoa (qlen (qk (qv "v") 0)), qs ");}\n"])
        |> qArmG (qeq (qv "t") (qint 5))
    , qivc (some "t") "ep-gpl"
        [("xs", qk (qv "v") 0), ("i", qint 0),
         ("n", qlen (qk (qv "v") 0)), ("m", qv "n"),
         ("out", qs "")]
        [("d", "ep-gps",
            [("xs", qk (qv "v") 0), ("i", qint 0),
             ("n", qlen (qk (qv "v") 0)), ("m", qv "n"),
             ("out", qs "")]),
         ("st", "ep-dpl",
            [("xs", qk (qv "v") 0), ("i", qint 0),
             ("n", qlen (qk (qv "v") 0))])]
        "dm" (qcc [qv "d", qs "static Val *vl",
              qitoa (qadd (qv "n") (qv "dm")),
              qs "(void){\n char**ns=xm(",
              qitoa (qlen (qk (qv "v") 0)),
              qs "*sizeof(char*));\n Val**vs=xm(",
              qitoa (qlen (qk (qv "v") 0)),
              qs "*sizeof(Val*));\n", qv "st",
              qs " return v_cell(ns,vs,",
              qitoa (qlen (qk (qv "v") 0)), qs ");}\n"])
        |> qArmG (qeq (qv "t") (qint 6))
    ] })

/-- `ep-gebd {nm,xs,i,n,m,out}` — builtin-arg `ev` decls, honoring
the `as`-2 skip; `m` running counter. -/
private def kEpGeb2 : String × KCallable :=
  ("ep-geb2", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "dm")])
    arms := [
      qiv "skip" (some "k") (some (qeq (qv "k") (qint 0)))
        "ep-gebd"
        [("nm", qv "nm"), ("xs", qv "xs"), ("i", qv "i"),
         ("n", qv "n"), ("m", qv "m"), ("out", qv "out")]
    , qivc (some "k") "ep-ge"
        [("e", qv "x2"), ("n", qv "m")]
        [("d", "ep-gebd",
            [("nm", qv "nm"), ("xs", qv "xs"), ("i", qv "i"),
             ("n", qv "n"), ("m", qadd (qv "m") (qv "dm")),
             ("out", qcat (qv "out") (qv "d"))])]
        "r" (qv "r")
    ] })

/-- `ep-gebd` — the loop itself. -/
private def kEpGebd : String × KCallable :=
  ("ep-gebd", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qv "out")
    , qivc (some "c") "ep-dbc"
        [("e", qix (qv "xs") (qv "c")), ("i", qv "c"),
         ("n", qv "n"), ("nm", qv "nm")]
        [("m0", "ep-geb2",
            [("dm", qv "m0"), ("x2", qix (qv "xs") (qv "c")),
             ("nm", qv "nm"), ("xs", qv "xs"),
             ("i", qadd (qv "c") (qint 1)), ("n", qv "n"),
             ("m", qv "m"), ("out", qv "out")])]
        "r" (qv "r")
    ] })

/-- `ep-ges2 {x,i,dm,nm,xs,n,m,out}` — builtin slot step. -/
private def kEpGes2 : String × KCallable :=
  ("ep-ges2", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "dm")])
    arms := [
      qiv "skip" (some "k") (some (qeq (qv "k") (qint 0)))
        "ep-gebs"
        [("nm", qv "nm"), ("xs", qv "xs"), ("i", qv "i"),
         ("n", qv "n"), ("m", qv "m"), ("out", qv "out")]
    , qiv1s (some "k") "ep-gebs"
        [("nm", qv "nm"), ("xs", qv "xs"), ("i", qv "i"),
         ("n", qv "n"), ("m", qadd (qv "m") (qv "dm")),
         ("out", qcc [qv "out", qs " av[", qitoa (qv "ii"),
           qs "]=ev",
           qitoa (qadd (qv "m") (qsub (qv "dm") (qint 1))),
           qs "(e);if(!av[", qitoa (qv "ii"), qs "])return 0;\n"])]
    ] })

/-- `ep-gebs {nm,xs,i,n,m,out}` — builtin `av[i]=ev_…(e)` slots. -/
private def kEpGebs : String × KCallable :=
  ("ep-gebs", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qv "out")
    , qivc (some "c") "ep-dbc"
        [("e", qix (qv "xs") (qv "c")), ("i", qv "c"),
         ("n", qv "n"), ("nm", qv "nm")]
        [("m0", "ep-ges2",
            [("dm", qv "m0"), ("x", qix (qv "xs") (qv "c")),
             ("ii", qv "c"), ("nm", qv "nm"), ("xs", qv "xs"),
             ("i", qadd (qv "c") (qint 1)), ("n", qv "n"),
             ("m", qv "m"), ("out", qv "out")])]
        "r" (qv "r")
    ] })

/-- `ep-ge {e,n}` — `genExpr`: children `ev` decls first, then the
node's own `ev` (last fresh = `n + dcE - 1`). -/
private def kEpGe : String × KCallable :=
  ("ep-ge", .subflow {
    preLabel := none
    head := ("ep-tg", [("x", qv "e")])
    arms := [
      qivc (some "t") "ep-gv" [("v", qk (qv "e") 0), ("n", qv "n")]
        [("d", "ep-dv", [("v", qk (qv "e") 0)])]
        "m" (qcc [qv "d", qs "static Val *ev",
              qitoa (qadd (qv "n") (qv "m")),
              qs "(E *e){\n (void)e;return vl",
              qitoa (qadd (qv "n") (qsub (qv "m") (qint 1))),
              qs "();}\n"])
        |> qArmG (qeq (qv "t") (qint 8))
    , qivc (some "t") "ep-cq" [("s", qk (qv "e") 0)]
        [] "q" (qcc [qs "static Val *ev", qitoa (qv "n"),
              qs "(E *e){\n return elk(e,", qv "q", qs ");}\n"])
        |> qArmG (qeq (qv "t") (qint 9))
    , qivc (some "t") "ep-ge2"
        [("e", qv "e"), ("n", qv "n")] [] "r" (qv "r")
        |> qArmG (qeq (qv "t") (qint 10))
    , qivc (some "t") "ep-ge" [("e", qk (qv "e") 1), ("n", qv "n")]
        [("d", "ep-de", [("e", qk (qv "e") 1)])]
        "mx" (qcc [qv "d", qs "static Val *ev",
              qitoa (qadd (qv "n") (qv "mx")),
              qs "(E *e){\n Val*a=ev",
              qitoa (qadd (qv "n") (qsub (qv "mx") (qint 1))),
              qs "(e);if(!a)return 0;\n return kun(",
              qitoa (qk (qv "e") 0), qs ",a);}\n"])
        |> qArmG (qeq (qv "t") (qint 11))
    , qivc (some "t") "ep-ge" [("e", qk (qv "e") 0), ("n", qv "n")]
        [("dc", "ep-de", [("e", qk (qv "e") 0)]),
         ("mc", "ep-ge",
            [("e", qk (qv "e") 1),
             ("n", qadd (qv "n") (qv "mc"))]),
         ("dt", "ep-de", [("e", qk (qv "e") 1)]),
         ("mt", "ep-ge",
            [("e", qk (qv "e") 2),
             ("n", qadd (qv "n")
                (qadd (qv "mc") (qv "mt")))]),
         ("de2", "ep-de", [("e", qk (qv "e") 2)])]
        "me" (qcc [qv "dc", qv "dt", qv "de2",
              qs "static Val *ev",
              qitoa (qadd (qv "n")
                (qadd (qv "mc") (qadd (qv "mt") (qv "me")))),
              qs "(E *e){\n Val*a=ev",
              qitoa (qadd (qv "n") (qsub (qv "mc") (qint 1))),
              qs "(e);\n if(!a||a->tag!=2)return 0;\n return a->b?ev",
              qitoa (qadd (qv "n")
                (qadd (qv "mc") (qsub (qv "mt") (qint 1)))),
              qs "(e):ev",
              qitoa (qadd (qv "n")
                (qadd (qv "mc")
                  (qadd (qv "mt") (qsub (qv "me") (qint 1))))),
              qs "(e);}\n"])
        |> qArmG (qeq (qv "t") (qint 12))
    , qivc (some "t") "ep-ge" [("e", qk (qv "e") 0), ("n", qv "n")]
        [("d", "ep-de", [("e", qk (qv "e") 0)]),
         ("m", "ep-cq", [("s", qk (qv "e") 1)])]
        "q" (qcc [qv "d", qs "static Val *ev",
              qitoa (qadd (qv "n") (qv "m")),
              qs "(E *e){\n Val*a=ev",
              qitoa (qadd (qv "n") (qsub (qv "m") (qint 1))),
              qs "(e);if(!a)return 0;\n return k_field(a,",
              qv "q", qs ");}\n"])
        |> qArmG (qeq (qv "t") (qint 13))
    , qivc (some "t") "ep-ge" [("e", qk (qv "e") 0), ("n", qv "n")]
        [("d", "ep-de", [("e", qk (qv "e") 0)]),
         ("m1", "ep-ge",
            [("e", qk (qv "e") 1),
             ("n", qadd (qv "n") (qv "m1"))]),
         ("d2", "ep-de", [("e", qk (qv "e") 1)])]
        "m2" (qcc [qv "d", qv "d2", qs "static Val *ev",
              qitoa (qadd (qv "n") (qadd (qv "m1") (qv "m2"))),
              qs "(E *e){\n Val*a=ev",
              qitoa (qadd (qv "n") (qsub (qv "m1") (qint 1))),
              qs "(e);if(!a)return 0;\n Val*b=ev",
              qitoa (qadd (qv "n")
                (qadd (qv "m1") (qsub (qv "m2") (qint 1)))),
              qs "(e);if(!b)return 0;\n return k_index(a,b);}\n"])
        |> qArmG (qeq (qv "t") (qint 14))
    , qivc (some "t") "ep-gebd"
        [("nm", qk (qv "e") 0), ("xs", qk (qv "e") 1),
         ("i", qint 0), ("n", qlen (qk (qv "e") 1)),
         ("m", qv "n"), ("out", qs "")]
        [("d", "ep-gebs",
            [("nm", qk (qv "e") 0), ("xs", qk (qv "e") 1),
             ("i", qint 0), ("n", qlen (qk (qv "e") 1)),
             ("m", qv "n"), ("out", qs "")]),
         ("sl", "ep-cq", [("s", qk (qv "e") 0)]),
         ("q", "ep-dbb",
            [("nm", qk (qv "e") 0), ("xs", qk (qv "e") 1),
             ("i", qint 0), ("n", qlen (qk (qv "e") 1))])]
        "mt" (qcc [qv "d", qs "static Val *ev",
              qitoa (qadd (qv "n") (qv "mt")),
              qs "(E *e){\n Val*av[",
              qitoa (qlen (qk (qv "e") 1)), qs "];\n",
              qv "sl", qs " return kbi(", qv "q", qs ",av,",
              qitoa (qlen (qk (qv "e") 1)), qs ");}\n"])
        |> qArmG (qeq (qv "t") (qint 15))
    ] })

/-- `ep-ge2 {e,n}` — the `.bin` inner dispatch: `and`, `or`, or a
`kbin` op. `l`'s decls first, `r` at `n+dcE(l)`, self last. -/
private def kEpGe2 : String × KCallable :=
  ("ep-ge2", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qk (qv "e") 0)])
    arms := [
      qivc (some "op") "ep-ge"
        [("e", qk (qv "e") 1), ("n", qv "n")]
        [("dl", "ep-de", [("e", qk (qv "e") 1)]),
         ("ml", "ep-ge",
            [("e", qk (qv "e") 2),
             ("n", qadd (qv "n") (qv "ml"))]),
         ("dr", "ep-de", [("e", qk (qv "e") 2)])]
        "mr" (qcc [qv "dl", qv "dr", qs "static Val *ev",
              qitoa (qadd (qv "n") (qadd (qv "ml") (qv "mr"))),
              qs "(E *e){\n Val*a=ev",
              qitoa (qadd (qv "n") (qsub (qv "ml") (qint 1))),
              qs "(e);\n if(!a||a->tag!=2)return 0;\n if(!a->b)return v_bool(0);\n a=ev",
              qitoa (qadd (qv "n")
                (qadd (qv "ml") (qsub (qv "mr") (qint 1)))),
              qs "(e);if(!a||a->tag!=2)return 0;return a;}\n"])
        |> qArmG (qeq (qv "op") (qint 11))
    , qivc (some "op") "ep-ge"
        [("e", qk (qv "e") 1), ("n", qv "n")]
        [("dl", "ep-de", [("e", qk (qv "e") 1)]),
         ("ml", "ep-ge",
            [("e", qk (qv "e") 2),
             ("n", qadd (qv "n") (qv "ml"))]),
         ("dr", "ep-de", [("e", qk (qv "e") 2)])]
        "mr" (qcc [qv "dl", qv "dr", qs "static Val *ev",
              qitoa (qadd (qv "n") (qadd (qv "ml") (qv "mr"))),
              qs "(E *e){\n Val*a=ev",
              qitoa (qadd (qv "n") (qsub (qv "ml") (qint 1))),
              qs "(e);\n if(!a||a->tag!=2)return 0;\n if(a->b)return v_bool(1);\n a=ev",
              qitoa (qadd (qv "n")
                (qadd (qv "ml") (qsub (qv "mr") (qint 1)))),
              qs "(e);if(!a||a->tag!=2)return 0;return a;}\n"])
        |> qArmG (qeq (qv "op") (qint 12))
    , qivc (some "op") "ep-ge"
        [("e", qk (qv "e") 1), ("n", qv "n")]
        [("dl", "ep-de", [("e", qk (qv "e") 1)]),
         ("ml", "ep-ge",
            [("e", qk (qv "e") 2),
             ("n", qadd (qv "n") (qv "ml"))]),
         ("dr", "ep-de", [("e", qk (qv "e") 2)])]
        "mr" (qcc [qv "dl", qv "dr", qs "static Val *ev",
              qitoa (qadd (qv "n") (qadd (qv "ml") (qv "mr"))),
              qs "(E *e){\n Val*a=ev",
              qitoa (qadd (qv "n") (qsub (qv "ml") (qint 1))),
              qs "(e);if(!a)return 0;\n Val*b=ev",
              qitoa (qadd (qv "n")
                (qadd (qv "ml") (qsub (qv "mr") (qint 1)))),
              qs "(e);if(!b)return 0;\n return kbin(",
              qitoa (qv "op"), qs ",a,b);}\n"])
    ] })


-- ---------- named args ----------

/-- `ep-gan {xs,i,n,out}` — the `an` table's `cstr` CSV. -/
private def kEpGan : String × KCallable :=
  ("ep-gan", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qv "out")
    , qivc (some "c") "ep-cq"
        [("s", qf (qix (qv "xs") (qv "c")) "name")]
        [("q", "ep-gan", [("xs", qv "xs"),
            ("i", qadd (qv "c") (qint 1)), ("n", qv "n"),
            ("out", qcc [qv "out",
              qcnd (qgt (qv "c") (qint 0)) (qs ",") (qs ""),
              qv "q"])])]
        "r" (qv "r")
    ] })

/-- `ep-gaed {xs,i,n,m,out}` — arg-expr `ev` decls; `m` runs
(`n+1` at entry — the `an` table takes the first fresh). -/
private def kEpGaed : String × KCallable :=
  ("ep-gaed", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qv "out")
    , qivc (some "c") "ep-ge"
        [("e", qf (qix (qv "xs") (qv "c")) "v"), ("n", qv "m")]
        [("d", "ep-de",
            [("e", qf (qix (qv "xs") (qv "c")) "v")]),
         ("dm", "ep-gaed", [("xs", qv "xs"),
            ("i", qadd (qv "c") (qint 1)), ("n", qv "n"),
            ("m", qadd (qv "m") (qv "dm")),
            ("out", qcat (qv "out") (qv "d"))])]
        "r" (qv "r")
    ] })

/-- `ep-gasl {xs,i,n,m,e,out}` — `av[i]=ev_…(e)` slot lines. -/
private def kEpGasl : String × KCallable :=
  ("ep-gasl", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qv "out")
    , qivc (some "c") "ep-de"
        [("e", qf (qix (qv "xs") (qv "c")) "v")]
        [("dm", "ep-gasl", [("xs", qv "xs"),
            ("i", qadd (qv "c") (qint 1)), ("n", qv "n"),
            ("m", qadd (qv "m") (qv "dm")), ("e", qv "e"),
            ("out", qcc [qv "out", qs " {Val *v=ev",
              qitoa (qadd (qv "m") (qsub (qv "dm") (qint 1))),
              qs "(", qv "e", qs ");if(!v)return 0;av[",
              qitoa (qv "c"), qs "]=v;}\n"])])]
        "r" (qv "r")
    ] })

/-- `ep-gad {xs,n}` — `genNamedArgs` decls: `an` table + arg `ev`s
(empty args → ""). -/
private def kEpGad : String × KCallable :=
  ("ep-gad", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "xs")])
    arms := [
      qp "empty" (some "x")
        (some (qeq (qlen (qv "x")) (qint 0))) (qs "")
    , qivc (some "x") "ep-gan"
        [("xs", qv "x"), ("i", qint 0), ("n", qlen (qv "x")),
         ("out", qs "")]
        [("csv", "ep-gaed",
            [("xs", qv "x"), ("i", qint 0), ("n", qlen (qv "x")),
             ("m", qadd (qv "n") (qint 1)), ("out", qs "")])]
        "d" (qcc [qs "static const char*an", qitoa (qv "n"),
              qs "[]={", qv "csv", qs "};\n", qv "d"])
    ] })

/-- `ep-gas {xs,e,d,n}` — `genNamedArgs` snippet: the caller-side
`av` array + `efr` call into `d` (`ja`/`ae`/`he`). -/
private def kEpGas : String × KCallable :=
  ("ep-gas", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "xs")])
    arms := [
      qp "empty" (some "x")
        (some (qeq (qlen (qv "x")) (qint 0))) (qs "")
    , qivc (some "x") "ep-gasl"
        [("xs", qv "x"), ("i", qint 0), ("n", qlen (qv "x")),
         ("m", qadd (qv "n") (qint 1)), ("e", qv "e"),
         ("out", qs "")]
        [] "p" (qcc [qs " {Val*av[",
              qitoa (qlen (qv "x")), qs "];\n", qv "p", qs " ",
              qv "d", qs "=efr(an", qitoa (qv "n"), qs ",av,",
              qitoa (qlen (qv "x")), qs ",", qv "d", qs ");}\n"])
    ] })

-- ---------- nodes / arms / dispatch ----------

/-- `ep-gcd {cs,n}` — conts dispatch decls or "". -/
private def kEpGcd : String × KCallable :=
  ("ep-gcd", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "cs")])
    arms := [
      qp "empty" (some "x")
        (some (qeq (qlen (qv "x")) (qint 0))) (qs "")
    , qiv1s (some "x") "ep-gd" [("xs", qv "x"), ("n", qv "n")]
    ] })

/-- `ep-gnd {nd,cs,n}` — node decls. -/
private def kEpGnd : String × KCallable :=
  ("ep-gnd", .subflow {
    preLabel := none
    head := ("ep-tg", [("x", qv "nd")])
    arms := [
      qp "term" (some "t") (some (qeq (qv "t") (qint 16)))
        (qs "")
    , qiv "jmp" (some "t") (some (qeq (qv "t") (qint 17)))
        "ep-gad" [("xs", qk (qv "nd") 1), ("n", qv "n")]
    , qivc (some "t") "ep-gad"
        [("xs", qk (qv "nd") 1), ("n", qv "n")]
        [("d", "ep-dg", [("xs", qk (qv "nd") 1)]),
         ("dg", "ep-gcd", [("cs", qv "cs"),
            ("n", qadd (qv "n") (qv "dg"))])]
        "cd" (qcat (qv "d") (qv "cd"))
        |> qArmG (qeq (qv "t") (qint 18))
    , qiv "prod" (some "t") (some (qeq (qv "t") (qint 19)))
        "ep-ge" [("e", qk (qv "nd") 0), ("n", qv "n")]
    , qiv "ctor" (some "t") (some (qeq (qv "t") (qint 20)))
        "ep-ge" [("e", qk (qv "nd") 1), ("n", qv "n")]
    ] })

/-- `ep-gcs {cs,n}` — invoke conts stmt: `return ir` or a `ds`
call. -/
private def kEpGcs : String × KCallable :=
  ("ep-gcs", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "cs")])
    arms := [
      qp "empty" (some "x")
        (some (qeq (qlen (qv "x")) (qint 0)))
        (qs " return ir;\n")
    , qivc (some "x") "ep-dd" [("xs", qv "x")]
        [] "dd" (qcc [qs " {Res*ct=ds",
              qitoa (qadd (qv "n") (qsub (qv "dd") (qint 1))),
              qs "(ee,ir);rfree(ir);return ct;}\n"])
    ] })

/-- `ep-gns {nd,cs,n}` — node stmt (`ee` env). -/
private def kEpGns : String × KCallable :=
  ("ep-gns", .subflow {
    preLabel := none
    head := ("ep-tg", [("x", qv "nd")])
    arms := [
      qp "term" (some "t") (some (qeq (qv "t") (qint 16)))
        (qs " return r_done();\n")
    , qivc (some "t") "ep-gas"
        [("xs", qk (qv "nd") 1), ("e", qs "ee"),
         ("d", qs "ja"), ("n", qv "n")]
        [("ac", "ep-cq", [("s", qk (qv "nd") 0)])]
        "q" (qcc [qs " {E*ja=0;\n", qv "ac",
              qs " return r_jump(", qv "q", qs ",ja);}\n"])
        |> qArmG (qeq (qv "t") (qint 17))
    , qivc (some "t") "ep-gas"
        [("xs", qk (qv "nd") 1), ("e", qs "ee"),
         ("d", qs "ae"), ("n", qv "n")]
        [("ac", "ep-m", [("s", qk (qv "nd") 0)]),
         ("km", "ep-dg", [("xs", qk (qv "nd") 1)]),
         ("dg", "ep-gcs", [("cs", qv "cs"),
            ("n", qadd (qv "n") (qv "dg"))])]
        "ct" (qcc [qs " {E*ae=0;\n", qv "ac",
              qs " Res*ir=k_", qv "km",
              qs "(ae);\n if(!ir)return 0;\n if(ir->k!=1&&ir->k!=2)return 0;\n",
              qv "ct", qs "}\n"])
        |> qArmG (qeq (qv "t") (qint 18))
    , qivc (some "t") "ep-de" [("e", qk (qv "nd") 0)]
        [] "m" (qcc [qs " {Val *v=ev",
              qitoa (qadd (qv "n") (qsub (qv "m") (qint 1))),
              qs "(ee);return v?r_bare(v):0;}\n"])
        |> qArmG (qeq (qv "t") (qint 19))
    , qivc (some "t") "ep-de" [("e", qk (qv "nd") 1)]
        [("m", "ep-cq", [("s", qk (qv "nd") 0)])]
        "q" (qcc [qs " {Val *v=ev",
              qitoa (qadd (qv "n") (qsub (qv "m") (qint 1))),
              qs "(ee);return v?r_tag(", qv "q", qs ",v):0;}\n"])
        |> qArmG (qeq (qv "t") (qint 20))
    ] })

/-- `ep-anb {o}` — bind stmt from the bind-opt. -/
private def kEpAnb : String × KCallable :=
  ("ep-anb", .subflow {
    preLabel := none
    head := ("ep-tg", [("x", qv "o")])
    arms := [
      qp "none" (some "t") (some (qeq (qv "t") (qint 23)))
        (qs "")
    , qivc (some "t") "ep-cq" [("s", qk (qv "o") 0)]
        [] "q" (qcc [qs " if(!r->v)return 0;\n ee=ecn(",
              qv "q", qs ",r->v,ee);\n"])
        |> qArmG (qeq (qv "t") (qint 24))
    ] })

/-- `ep-acd {o,n}` — cond decls from the cond-opt. -/
private def kEpAcd : String × KCallable :=
  ("ep-acd", .subflow {
    preLabel := none
    head := ("ep-tg", [("x", qv "o")])
    arms := [
      qp "none" (some "t") (some (qeq (qv "t") (qint 23)))
        (qs "")
    , qiv "some" (some "t") (some (qeq (qv "t") (qint 24)))
        "ep-ge" [("e", qk (qv "o") 0), ("n", qv "n")]
    ] })

/-- `ep-acs {o,n}` — cond stmt from the cond-opt. -/
private def kEpAcs : String × KCallable :=
  ("ep-acs", .subflow {
    preLabel := none
    head := ("ep-tg", [("x", qv "o")])
    arms := [
      qp "none" (some "t") (some (qeq (qv "t") (qint 23)))
        (qs "")
    , qivc (some "t") "ep-de" [("e", qk (qv "o") 0)]
        [] "m" (qcc [qs " {Val *g=ev",
              qitoa (qadd (qv "n") (qsub (qv "m") (qint 1))),
              qs "(ee);\n if(!g||g->tag!=2)return 0;\n if(!g->b)return KSKIP();}\n"])
        |> qArmG (qeq (qv "t") (qint 24))
    ] })

/-- `ep-ano {o,cs,n}` — node decls from the node-opt. -/
private def kEpAno : String × KCallable :=
  ("ep-ano", .subflow {
    preLabel := none
    head := ("ep-tg", [("x", qv "o")])
    arms := [
      qp "none" (some "t") (some (qeq (qv "t") (qint 23)))
        (qs "")
    , qiv "nd" (some "t") (some (qeq (qv "t") (qint 24)))
        "ep-gnd" [("nd", qk (qv "o") 0), ("cs", qv "cs"),
                  ("n", qv "n")]
    ] })

/-- `ep-ann {o,cs,n}` — node stmt from the node-opt. -/
private def kEpAnn : String × KCallable :=
  ("ep-ann", .subflow {
    preLabel := none
    head := ("ep-tg", [("x", qv "o")])
    arms := [
      qp "none" (some "t") (some (qeq (qv "t") (qint 23)))
        (qs " return r_done();\n")
    , qiv "nd" (some "t") (some (qeq (qv "t") (qint 24)))
        "ep-gns" [("nd", qk (qv "o") 0), ("cs", qv "cs"),
                  ("n", qv "n")]
    ] })

/-- `ep-ga {a,n}` — `genArm`: `aw_n` first; cond subtree at
`n+1`, node subtree at `n+1+dcE(cond)`. -/
private def kEpGa : String × KCallable :=
  ("ep-ga", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "a")])
    arms := [qivc (some "x") "ep-acd"
      [("o", qk (qv "x") 3), ("n", qadd (qv "n") (qint 1))]
      [("cd", "ep-doc", [("o", qk (qv "x") 3)]),
       ("cm", "ep-ano", [("o", qk (qv "x") 4),
          ("cs", qk (qv "x") 5),
          ("n", qadd (qv "n")
            (qadd (qint 1) (qv "cm")))]),
       ("nd", "ep-anb", [("o", qk (qv "x") 2)]),
       ("bs", "ep-acs", [("o", qk (qv "x") 3),
          ("n", qadd (qv "n") (qint 1))]),
       ("cs", "ep-ann", [("o", qk (qv "x") 4),
          ("cs", qk (qv "x") 5),
          ("n", qadd (qv "n")
            (qadd (qint 1) (qv "cm")))])]
      "ns" (qcc [qv "cd", qv "nd",
            qs "static Res *aw", qitoa (qv "n"),
            qs "(E *e, Res *r){\n KSTEP();\n E*ee=e;(void)r;(void)ee;\n",
            qv "bs", qv "cs", qv "ns", qs "}\n"])] })

/-- `ep-gal2 {xs,i,n,m,out}` — arm decls loop; `m` runs. -/
private def kEpGal2 : String × KCallable :=
  ("ep-gal2", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qv "out")
    , qivc (some "c") "ep-ga"
        [("a", qix (qv "xs") (qv "c")), ("n", qv "m")]
        [("d", "ep-da", [("a", qix (qv "xs") (qv "c"))]),
         ("dm", "ep-gal2", [("xs", qv "xs"),
            ("i", qadd (qv "c") (qint 1)), ("n", qv "n"),
            ("m", qadd (qv "m") (qv "dm")),
            ("out", qcat (qv "out") (qv "d"))])]
        "r" (qv "r")
    ] })

/-- `ep-gtt {a,n}` — one tag-dispatch try line. -/
private def kEpGtt : String × KCallable :=
  ("ep-gtt", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "a")])
    arms := [qivc (some "x") "ep-cq" [("s", qk (qv "x") 0)]
      [] "q" (qcc [qs " if(!strcmp(r->br,", qv "q",
            qs ")){Res*t=aw", qitoa (qv "n"),
            qs "(e,r);if(!t)return 0;if(t!=KSKIP())return t;}\n"])] })

/-- `ep-gdt {xs,i,n,m,out}` — tag-dispatch tries loop. -/
private def kEpGdt : String × KCallable :=
  ("ep-gdt", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qv "out")
    , qivc (some "c") "ep-gtt"
        [("a", qix (qv "xs") (qv "c")), ("n", qv "m")]
        [("t", "ep-da", [("a", qix (qv "xs") (qv "c"))]),
         ("dm", "ep-gdt", [("xs", qv "xs"),
            ("i", qadd (qv "c") (qint 1)), ("n", qv "n"),
            ("m", qadd (qv "m") (qv "dm")),
            ("out", qcat (qv "out") (qv "t"))])]
        "r" (qv "r")
    ] })

/-- `ep-gbt {a,n}` — one bare-dispatch try line (or the refusal
comment at a catchall/empty-branch arm's position). -/
private def kEpGbt : String × KCallable :=
  ("ep-gbt", .bare
    (qcnd (qor (qeq (qk (qv "a") 1) (qint 1))
               (qeq (qk (qv "a") 0) (qs "")))
      (qs " return 0; /* catchall/empty arm refuses under bare dispatch */\n")
      (qcc [qs " {Res*t=aw", qitoa (qv "n"),
            qs "(e,r);if(!t)return 0;if(t!=KSKIP())return t;}\n"])))

/-- `ep-gdb {xs,i,n,m,out}` — bare-dispatch tries loop. -/
private def kEpGdb : String × KCallable :=
  ("ep-gdb", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qv "out")
    , qivc (some "c") "ep-gbt"
        [("a", qix (qv "xs") (qv "c")), ("n", qv "m")]
        [("t", "ep-da", [("a", qix (qv "xs") (qv "c"))]),
         ("dm", "ep-gdb", [("xs", qv "xs"),
            ("i", qadd (qv "c") (qint 1)), ("n", qv "n"),
            ("m", qadd (qv "m") (qv "dm")),
            ("out", qcat (qv "out") (qv "t"))])]
        "r" (qv "r")
    ] })

/-- `ep-gd {xs,n}` — `genDispatch`: arm fns first, `ds` last
(`ds` number = `n + Σ dcA`). -/
private def kEpGd : String × KCallable :=
  ("ep-gd", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "xs")])
    arms := [qivc (some "x") "ep-gal2"
      [("xs", qv "x"), ("i", qint 0), ("n", qlen (qv "x")),
       ("m", qv "n"), ("out", qs "")]
      [("d", "ep-gdt", [("xs", qv "x"), ("i", qint 0),
          ("n", qlen (qv "x")), ("m", qv "n"), ("out", qs "")]),
       ("tt", "ep-gdb", [("xs", qv "x"), ("i", qint 0),
          ("n", qlen (qv "x")), ("m", qv "n"), ("out", qs "")]),
       ("bt", "ep-dal", [("xs", qv "x"), ("i", qint 0),
          ("n", qlen (qv "x"))])]
      "dm" (qcc [qv "d", qs "static Res *ds",
            qitoa (qadd (qv "n") (qv "dm")),
            qs "(E *e, Res *r){\n KSTEP();\n if(r->br){\n",
            qv "tt", qs " return 0;}\n if(!r->v)return 0;\n",
            qv "bt", qs " return 0;}\n"])] })


-- ---------- flow / callable ----------

/-- `ep-gfd {xs,n}` — flow arms decls: `ds` subtree or "". -/
private def kEpGfd : String × KCallable :=
  ("ep-gfd", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "xs")])
    arms := [
      qp "empty" (some "x")
        (some (qeq (qlen (qv "x")) (qint 0))) (qs "")
    , qiv1s (some "x") "ep-gd" [("xs", qv "x"), ("n", qv "n")]
    ] })

/-- `ep-gfj {pl}` — the preLabel jump clause or the plain refuse. -/
private def kEpGfj : String × KCallable :=
  ("ep-gfj", .subflow {
    preLabel := none
    head := ("ep-tg", [("x", qv "pl")])
    arms := [
      qp "none" (some "t") (some (qeq (qv "t") (qint 23)))
        (qs "   if(t->k==4)return 0;\n")
    , qivc (some "t") "ep-cq" [("s", qk (qv "pl") 0)]
        [] "q" (qcc [qs "   if(t->k==4){if(!strcmp(t->jl,",
              qv "q",
              qs ")){he=t->ja;rfree(h);rfree(t);continue;}return 0;}\n"])
        |> qArmG (qeq (qv "t") (qint 24))
    ] })

/-- `ep-gfx {pl,xs,n}` — the for-body: `return h` or the dispatch
block (`ds` number = `n + dcD - 1`). -/
private def kEpGfx : String × KCallable :=
  ("ep-gfx", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "xs")])
    arms := [
      qp "empty" (some "x")
        (some (qeq (qlen (qv "x")) (qint 0)))
        (qs "   return h;\n")
    , qivc (some "x") "ep-dd" [("xs", qv "x")]
        [("dd", "ep-gfj", [("pl", qv "pl")])]
        "js" (qcc [qs "   {Res*t=ds",
              qitoa (qadd (qv "n") (qsub (qv "dd") (qint 1))),
              qs "(ce,h);\n   if(!t)return 0;\n   if(t->k==3){rfree(h);rfree(t);return r_bare(0);}\n",
              qv "js", qs "   rfree(h);\n   return t;}\n"])
    ] })

/-- `ep-gf {fl,kn,n}` — `genCallable`'s subflow case. -/
private def kEpGf : String × KCallable :=
  ("ep-gf", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "fl")])
    arms := [qivc (some "x") "ep-gad"
      [("xs", qk (qk (qv "x") 1) 1), ("n", qv "n")]
      [("hd", "ep-gas", [("xs", qk (qk (qv "x") 1) 1),
          ("e", qs "ce"), ("d", qs "he"), ("n", qv "n")]),
       ("has", "ep-dg", [("xs", qk (qk (qv "x") 1) 1)]),
       ("dg", "ep-gfd", [("xs", qk (qv "x") 2),
          ("n", qadd (qv "n") (qv "dg"))]),
       ("ad", "ep-gfx", [("pl", qk (qv "x") 0),
          ("xs", qk (qv "x") 2),
          ("n", qadd (qv "n") (qv "dg"))]),
       ("bd", "ep-m", [("s", qk (qk (qv "x") 1) 0)])]
      "hm" (qcc [qv "hd", qv "ad", qs "static Res *",
            qv "kn", qs "(E *ce){\n KSTEP();\n",
            qcnd (qand (qeq (qlen (qk (qv "x") 2)) (qint 0))
                       (qeq (qlen (qk (qk (qv "x") 1) 1))
                            (qint 0)))
                 (qs " (void)ce;\n") (qs ""),
            qs " E*he=0;\n", qv "has",
            qs " for(;;){\n  KSTEP();\n  Res*h=k_", qv "hm",
            qs "(he);\n  if(!h||(h->k!=1&&h->k!=2))return 0;\n",
            qv "bd", qs " }\n}\n"])] })

/-- `ep-gc {nm,c,n}` — `genCallable` on a quoted callable. -/
private def kEpGc : String × KCallable :=
  ("ep-gc", .subflow {
    preLabel := none
    head := ("ep-tg", [("x", qv "c")])
    arms := [
      qivc (some "t") "ep-m" [("s", qv "nm")]
        [("mm", "ep-ge", [("e", qk (qv "c") 0), ("n", qv "n")]),
         ("d", "ep-de", [("e", qk (qv "c") 0)])]
        "m" (qcc [qv "d", qs "static Res *k_", qv "mm",
              qs "(E *e){\n KSTEP();\n Val*v=ev",
              qitoa (qadd (qv "n") (qsub (qv "m") (qint 1))),
              qs "(e);\n return v?r_bare(v):0;}\n"])
        |> qArmG (qeq (qv "t") (qint 27))
    , qivc (some "t") "ep-m" [("s", qv "nm")]
        [("mm", "ep-gf",
            [("fl", qk (qv "c") 0),
             ("kn", qcc [qs "k_", qv "mm"]), ("n", qv "n")])]
        "d" (qv "d")
        |> qArmG (qeq (qv "t") (qint 29))
    ] })

-- ---------- reachables ----------

/-- `ep-arf {st,fr,s}` — frontier append: `|s|` onto `fr` only
when `s` is in neither set-string.  The `st` check is what makes
the closure terminate: without it already-found names re-enter
the frontier and `ep-grr` never converges. -/
private def kEpArf : String × KCallable :=
  ("ep-arf", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "s")])
    arms := [qivc (some "s") "ep-mems"
      [("st", qv "st"), ("s", qv "s")]
      [("k", "ep-mems", [("st", qv "fr"), ("s", qv "s")])]
      "k2" (qcnd (qor (qeq (qv "k") (qint 1)) (qeq (qv "k2") (qint 1)))
             (qv "fr")
             (qcc [qv "fr", qs "|", qv "s", qs "|"]))] })

/-- `ep-anod {a,st,fr}` — one arm's invoke-target ref (tag-24 opt
wrapping a tag-18 invoke), or `fr`. -/
private def kEpAnod : String × KCallable :=
  ("ep-anod", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "a")])
    arms := [
      qiv "inv" (some "a")
        (some (qand (qeq (qtg (qk (qv "a") 4)) (qint 24))
                    (qeq (qtg (qk (qk (qv "a") 4) 0)) (qint 18))))
        "ep-arf" [("st", qv "st"), ("fr", qv "fr"),
                  ("s", qk (qk (qk (qv "a") 4) 0) 0)]
    , qp1 (some "a") (qv "fr")
    ] })

/-- `ep-anl {xs,i,n,st,fr}` — `armRefs` over an arm list into `fr`,
dedup'd against `st`. -/
private def kEpAnl : String × KCallable :=
  ("ep-anl", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qv "fr")
    , qivc (some "c") "ep-aref"
        [("a", qix (qv "xs") (qv "c")), ("st", qv "st"),
         ("fr", qv "fr")]
        [("fr2", "ep-anl", [("xs", qv "xs"),
            ("i", qadd (qv "c") (qint 1)), ("n", qv "n"),
            ("st", qv "st"), ("fr", qv "fr2")])]
        "r" (qv "r")
    ] })

/-- `ep-aref {a,st,fr}` — `armRefs` of one arm into `fr`:
the node's invoke target plus conts' refs. -/
private def kEpAref : String × KCallable :=
  ("ep-aref", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "a")])
    arms := [qivc (some "a") "ep-anod"
      [("a", qv "a"), ("st", qv "st"), ("fr", qv "fr")]
      [("fr2", "ep-anl", [("xs", qk (qv "a") 5), ("i", qint 0),
          ("n", qlen (qk (qv "a") 5)), ("st", qv "st"),
          ("fr", qv "fr2")])]
      "r" (qv "r")] })

/-- `ep-cref {c,st,fr}` — `callableRefs` of one callable into
`fr` (dedup vs `st`): subflow → head name + arm refs;
bare/thunk → `fr` unchanged. -/
private def kEpCref : String × KCallable :=
  ("ep-cref", .subflow {
    preLabel := none
    head := ("ep-tg", [("x", qv "c")])
    arms := [
      qivc (some "t") "ep-arf"
        [("st", qv "st"), ("fr", qv "fr"),
         ("s", qk (qk (qk (qv "c") 0) 1) 0)]
        [("fr2", "ep-anl", [("xs", qk (qk (qv "c") 0) 2),
            ("i", qint 0),
            ("n", qlen (qk (qk (qv "c") 0) 2)),
            ("st", qv "st"), ("fr", qv "fr2")])]
        "r" (qv "r")
        |> qArmG (qeq (qv "t") (qint 29))
    , qp1 (some "t") (qv "fr")
    ] })

/-- `ep-grq2 {x,k,g,st,fr,fr2,i,n}` — one frontier-pass step:
`k` is the membership verdict for `x.name` **in `fr`**. -/
private def kEpGrq2 : String × KCallable :=
  ("ep-grq2", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "k")])
    arms := [
      qiv "miss" (some "k") (some (qeq (qv "k") (qint 0)))
        "ep-grq" [("g", qv "g"), ("st", qv "st"), ("fr", qv "fr"),
                  ("fr2", qv "fr2"),
                  ("i", qadd (qv "i") (qint 1)), ("n", qv "n")]
    , qivc (some "k") "ep-cref"
        [("c", qf (qv "x2") "v"), ("st", qv "st"),
         ("fr", qv "fr2")]
        [("fr3", "ep-grq", [("g", qv "g"), ("st", qv "st"),
            ("fr", qv "fr"), ("fr2", qv "fr3"),
            ("i", qadd (qv "i") (qint 1)), ("n", qv "n")])]
        "r" (qv "r")
    ] })

/-- `ep-grq {g,st,fr,fr2,i,n}` — one frontier pass: scan the
graph for members of `fr` (this pass's delta) and collect their
not-yet-known refs into `fr2`.  Each callable is processed at
most once across the whole closure — the old version scanned
all `|st|` members every pass, O(passes·G²·L); this is
O(G²·L) total. -/
private def kEpGrq : String × KCallable :=
  ("ep-grq", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qv "fr2")
    , qivc (some "c") "ep-mems"
        [("st", qv "fr"),
         ("s", qf (qix (qv "g") (qv "c")) "name")]
        [("k0", "ep-grq2",
            [("k", qv "k0"), ("x2", qix (qv "g") (qv "c")),
             ("g", qv "g"), ("st", qv "st"), ("fr", qv "fr"),
             ("fr2", qv "fr2"),
             ("i", qv "c"), ("n", qv "n")])]
        "r" (qv "r")
    ] })

/-- `ep-grd {g,st,fr2,k,n}` — pass verdict: empty frontier means
fixpoint, otherwise merge `fr2` into `st` and continue. -/
private def kEpGrd : String × KCallable :=
  ("ep-grd", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "fr2")])
    arms := [
      qp "fix" (some "f") (some (qeq (qv "f") (qs ""))) (qv "st")
    , qiv "more" (some "f") none "ep-grr"
        [("g", qv "g"), ("st", qcc [qv "st", qv "f"]),
         ("fr", qv "f"), ("k", qv "k"), ("n", qv "n")]
    ] })

/-- `ep-grr {g,st,fr,k,n}` — frontier closure: `fr` is the
last pass's additions; a pass yields `fr2` = refs of
`fr`-members not already in `st`.  `k` stays as the honest
cap (graph-size bound). -/
private def kEpGrr : String × KCallable :=
  ("ep-grr", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "k")])
    arms := [
      qp "done" (some "k") (some (qle (qv "k") (qint 0)))
        (qv "st")
    , qivc (some "k") "ep-grq"
        [("g", qv "g"), ("st", qv "st"), ("fr", qv "fr"),
         ("fr2", qs ""), ("i", qint 0), ("n", qv "n")]
        [("fr2", "ep-grd",
            [("g", qv "g"), ("st", qv "st"), ("fr2", qv "fr2"),
             ("k", qsub (qv "k") (qint 1)), ("n", qv "n")])]
        "r" (qv "r")
    ] })

/-- `ep-gr {g,e}` — `reachables` as a `|a|b|` set-string. -/
private def kEpGr : String × KCallable :=
  ("ep-gr", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "e")])
    arms := [qiv1s (some "e") "ep-grr"
      [("g", qv "g"),
       ("st", qcc [qs "|", qv "e", qs "|"]),
       ("fr", qcc [qs "|", qv "e", qs "|"]),
       ("k", qlen (qv "g")), ("n", qlen (qv "g"))]] })

/-- `ep-hase {g,e,i,n}` — 1 iff `e` names a graph entry. -/
private def kEpHase : String × KCallable :=
  ("ep-hase", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qint 0)
    , qp "hit" (some "c")
        (some (qeq (qf (qix (qv "g") (qv "c")) "name")
                   (qv "e")))
        (qint 1)
    , qiv "go" (some "c") none "ep-hase"
        [("g", qv "g"), ("e", qv "e"),
         ("i", qadd (qv "c") (qint 1)), ("n", qv "n")]
    ] })

-- ---------- program walk ----------

/-- `ep-gfwd {x,k,out}` — one fwd-decls step: `k` membership
verdict; produce the extended (or unchanged) `out`. -/
private def kEpGfwd : String × KCallable :=
  ("ep-gfwd", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "k")])
    arms := [
      qivc (some "k") "ep-m"
        [("s", qf (qv "x2") "name")] []
        "mm" (qcc [qv "out", qs "static Res *k_", qv "mm",
              qs "(E *e);\n"])
        |> qArmG (qeq (qv "k") (qint 1))
    , qp "no" (some "k") (some (qeq (qv "k") (qint 0)))
        (qv "out")
    ] })

/-- `ep-gfw {g,live,i,n,out}` — forward decls over the live
subgraph (in graph order). -/
private def kEpGfw : String × KCallable :=
  ("ep-gfw", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qv "out")
    , qivc (some "c") "ep-mems"
        [("st", qv "live"),
         ("s", qf (qix (qv "g") (qv "c")) "name")]
        [("k0", "ep-gfwd",
            [("k", qv "k0"), ("x2", qix (qv "g") (qv "c")),
             ("out", qv "out")]),
         ("o2", "ep-gfw", [("g", qv "g"), ("live", qv "live"),
            ("i", qadd (qv "c") (qint 1)), ("n", qv "n"),
            ("out", qv "o2")])]
        "r" (qv "r")
    ] })

/-- `ep-gbo3 {x,k,g,live,i,n,m,out}` — one body step. -/
private def kEpGbo3 : String × KCallable :=
  ("ep-gbo3", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "k")])
    arms := [
      qiv "no" (some "k") (some (qeq (qv "k") (qint 0)))
        "ep-gbo" [("g", qv "g"), ("live", qv "live"),
                  ("i", qv "i"), ("n", qv "n"), ("m", qv "m"),
                  ("out", qv "out")]
    , qivc (some "k") "ep-gc"
        [("nm", qf (qv "x2") "name"), ("c", qf (qv "x2") "v"),
         ("n", qv "m")]
        [("d", "ep-dc", [("c", qf (qv "x2") "v")]),
         ("dm", "ep-gbo", [("g", qv "g"), ("live", qv "live"),
            ("i", qv "i"), ("n", qv "n"),
            ("m", qadd (qv "m") (qv "dm")),
            ("out", qcat (qv "out") (qv "d"))])]
        "r" (qv "r")
    ] })

/-- `ep-gbo2 {x,g,live,i,n,m,out}` — membership check step. -/
private def kEpGbo2 : String × KCallable :=
  ("ep-gbo2", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "x")])
    arms := [qivc (some "x") "ep-mems"
      [("st", qv "live"), ("s", qf (qv "x") "name")]
      [("k0", "ep-gbo3",
          [("k", qv "k0"), ("x2", qv "x"), ("g", qv "g"),
           ("live", qv "live"), ("i", qv "i"), ("n", qv "n"),
           ("m", qv "m"), ("out", qv "out")])]
      "r" (qv "r")] })

/-- `ep-gbo {g,live,i,n,m,out}` — callable decls over the live
subgraph; `m` is the running fresh counter. -/
private def kEpGbo : String × KCallable :=
  ("ep-gbo", .subflow {
    preLabel := none
    head := ("ep-step", [("i", qv "i"), ("n", qv "n")])
    arms := [
      qstop (qv "out")
    , qivc (some "c") "ep-gbo2"
        [("x", qix (qv "g") (qv "c")), ("g", qv "g"),
         ("live", qv "live"), ("i", qadd (qv "c") (qint 1)),
         ("n", qv "n"), ("m", qv "m"), ("out", qv "out")]
        [] "r" (qv "r")
    ] })

/-- `ep-gw {fb,e,f}` — assemble `prelude ++ fwd+body ++ driver`. -/
private def kEpGw : String × KCallable :=
  ("ep-gw", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "e")])
    arms := [qivc (some "e") "ep-m" [("s", qv "e")] []
      "mm" (qcc [
        qs prelude, qv "fb",
        qs "static Res *k_", qv "mm", qs "(E *e);\n",
        qs "int main(int argc,char**argv){Val*a;E*e;Res*r;int i;\n",
        qs " (void)veq;(void)r_tag;(void)r_done;(void)r_jump;(void)kun;(void)fb;\n",
        qs " (void)asrat;(void)kfmod;(void)ktdiv;(void)ktmod;(void)v_flt;(void)pval;\n",
        qs " (void)v_arr;(void)v_cell;(void)ovf_mul;(void)ovf_add;(void)ovf_sub;\n",
        qs " (void)k_field;(void)k_index;(void)ecn;(void)efr;(void)rfree;(void)v_sref;\n",
        qs " kfuel=", qitoa (qv "f"),
        qs ";if(argc>1)kfuel=atoll(argv[1]);\n",
        qs " xp=xrd();a=xval();\n",
        qs " if(!a||a->tag!=5){fputs(\"refuse: args not a cell\\n\",kstderr);return 2;}\n",
        qs " e=0;for(i=a->nf-1;i>=0;i--)e=ecn(a->ns[i],a->vs[i],e);\n",
        qs " r=k_", qv "mm", qs "(e);\n",
        qs " if(!r||(r->k!=1&&r->k!=2)){fputs(\"refuse\\n\",kstderr);return 4;}\n",
        qs " if(r->k==1&&!r->br&&r->v&&r->v->tag==3){fputs(s_flat(r->v->s),kstdout);fputc('\\n',kstdout);return 0;}\n",
        qs " pres(r,kstdout);fputc('\\n',kstdout);return 0;}\n"])] })

/-- `emit {src,fuel}` — the gate: tag-30 program with nonempty
graph and declared entry; reachables → fwd + body → wrap. -/
private def kEpEmit : String × KCallable :=
  ("emit", .subflow {
    preLabel := none
    head := ("ep-id", [("x", qv "src")])
    arms := [.mk "go" false (some "s")
      (some (qand (qeq (qtg (qv "s")) (qint 30))
            (qand (qeq (qlen (qks (qv "s"))) (qint 3))
                  (qgt (qlen (qk (qv "s") 0)) (qint 0)))))
      (some (.invoke "ep-hase"
        [("g", qk (qv "s") 0), ("e", qk (qv "s") 1),
         ("i", qint 0), ("n", qlen (qk (qv "s") 0))]))
      [ .mk "_chain" false (some "he")
          (some (qeq (qv "he") (qint 1)))
          (some (.invoke "ep-gr"
            [("g", qk (qv "s") 0), ("e", qk (qv "s") 1)]))
          [ .mk "_chain" false (some "live") none
            (some (.invoke "ep-gfw"
              [("g", qk (qv "s") 0), ("live", qv "live"),
               ("i", qint 0), ("n", qlen (qk (qv "s") 0)),
               ("out", qs "")]))
            [ .mk "_chain" false (some "fw") none
              (some (.invoke "ep-gbo"
                [("g", qk (qv "s") 0), ("live", qv "live"),
                 ("i", qint 0), ("n", qlen (qk (qv "s") 0)),
                 ("m", qint 0), ("out", qs "")]))
              [ .mk "_chain" false (some "bd") none
                (some (.invoke "ep-gw"
                  [("fb", qcat (qv "fw") (qv "bd")),
                   ("e", qk (qv "s") 1), ("f", qv "fuel")]))
                [ .mk "_chain" false (some "out") none
                  (some (.produce (qv "out"))) []] ] ] ] ] ] })

/-- `kEmitProg` — the whole-program C99 emitter as a KProg. -/
def kEmitProg : KProg := {
  entry := "emit"
  args := [("src", .cell []), ("fuel", .int 0)]
  graph := [
    kEpId, kEpPeek, kEpStep, kEpTg,
    kEpMl, kEpM, kEpEc, kEpEl, kEpE, kEpCq,
    kEpMi, kEpMo, kEpMems,
    kEpDv, kEpDvl, kEpDpl, kEpDbc, kEpDbb, kEpDe,
    kEpDoc, kEpDc0, kEpDn, kEpDon, kEpDal, kEpDd, kEpDa,
    kEpDgl, kEpDg, kEpDf2, kEpDf, kEpDc,
    kEpGvl, kEpGvs, kEpGpl, kEpGps, kEpGv,
    kEpGeb2, kEpGebd, kEpGes2, kEpGebs, kEpGe, kEpGe2,
    kEpGan, kEpGaed, kEpGasl, kEpGad, kEpGas,
    kEpGcd, kEpGnd, kEpGcs, kEpGns,
    kEpAnb, kEpAcd, kEpAcs, kEpAno, kEpAnn,
    kEpGa, kEpGal2, kEpGtt, kEpGdt, kEpGbt, kEpGdb, kEpGd,
    kEpGfd, kEpGfj, kEpGfx, kEpGf, kEpGc,
    kEpArf, kEpAnod, kEpAnl, kEpAref, kEpCref,
    kEpGrq2, kEpGrq, kEpGrd, kEpGrr, kEpGr, kEpHase,
    kEpGfwd, kEpGfw, kEpGbo3, kEpGbo2, kEpGbo,
    kEpGw, kEpEmit
  ] }

end ISAR
