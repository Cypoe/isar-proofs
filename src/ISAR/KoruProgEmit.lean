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

/-- Escape a string into a C literal body (no surrounding quotes). -/
def cstrBody (s : String) : String :=
  String.ofList (s.toList.flatMap fun c =>
    match c with
    | '"' => ['\\', '"']
    | '\\' => ['\\', '\\']
    | '\n' => ['\\', 'n']
    | '\t' => ['\\', 't']
    | '\r' => ['\\', 'r']
    | c =>
        if c.toNat < 32 || c.toNat ≥ 127 then
          let n := c.toNat
          ['\\', Char.ofNat (48 + n / 64), Char.ofNat (48 + (n / 8) % 8),
           Char.ofNat (48 + n % 8)]
        else [c])

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
"static Val*v_int(k_i64 i){Val*v=vn(0);v->i=i;return v;}\n" ++
"static Val*v_flt(k_i64 n,k_i64 d){Val*v=vn(1);v->i=n;v->d=d;return v;}\n" ++
"static Val*v_bool(int b){Val*v=vn(2);v->b=b?1:0;return v;}\n" ++
"static Val*v_str(const char*s){Val*v=vn(3);v->s=s_leaf(xsd(s));return v;}\n" ++
"static Val*v_arr(Val**xs,int n){Val*v=vn(4);v->xs=xs;v->nx=n;return v;}\n" ++
"static Val*v_cell(char**ns,Val**vs,int n){Val*v=vn(5);v->ns=ns;v->vs=vs;v->nf=n;return v;}\n" ++
"static int veq(Val*a,Val*b){int i;\n" ++
" if(!a||!b||a->tag!=b->tag)return 0;\n" ++
" switch(a->tag){case 0:return a->i==b->i;case 1:return a->i==b->i&&a->d==b->d;\n" ++
"  case 2:return a->b==b->b;case 3:return!strcmp(s_flat(a->s),s_flat(b->s));\n" ++
"  case 4:if(a->nx!=b->nx)return 0;for(i=0;i<a->nx;i++)if(!veq(a->xs[i],b->xs[i]))return 0;return 1;\n" ++
"  case 5:if(a->nf!=b->nf)return 0;for(i=0;i<a->nf;i++)if(strcmp(a->ns[i],b->ns[i])||!veq(a->vs[i],b->vs[i]))return 0;return 1;}\n" ++
" return 0;}\n" ++
"typedef struct E{char*n;Val*v;struct E*x;}E;\n" ++
"static E*ecn(const char*n,Val*v,E*x){E*e=xm(sizeof(E));e->n=xsd(n);e->v=v;e->x=x;return e;}\n" ++
"static Val*elk(E*e,const char*n){for(;e;e=e->x)if(!strcmp(e->n,n))return e->v;return 0;}\n" ++
"typedef struct Res{int k;char*br;Val*v;char*jl;E*ja;}Res;\n" ++
"/* k: 1 result-bare 2 result-tag 3 done 4 jump ; 9 = internal skip */\n" ++
"static Res*rn(int k){Res*r=xm(sizeof(Res));memset(r,0,sizeof(Res));r->k=k;return r;}\n" ++
"static Res*r_bare(Val*v){Res*r=rn(1);r->v=v;return r;}\n" ++
"static Res*r_tag(const char*b,Val*v){Res*r=rn(2);r->br=xsd(b);r->v=v;return r;}\n" ++
"static Res*r_done(void){return rn(3);}\n" ++
"static Res*r_jump(const char*l,E*a){Res*r=rn(4);r->jl=xsd(l);r->ja=a;return r;}\n" ++
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
" (void)k_field;(void)k_index;\n" ++
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
      EM.put s!"static Val *{f}(void)\{\n return v_str({cstr s});}\n"
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
          s!" ns[{i}]=xsd({cstr p.1});vs[{i}]={p.2}();\n")
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
            pure s!" return {d}(ee,ir);\n"
        pure s!" \{E*ae=0;\n{argCode} Res*ir=k_{mangle t}(ae);\n if(!ir)return 0;\n if(ir->k!=1&&ir->k!=2)return 0;\n{contStmt}}\n"
  EM.put s!"static Res *{f}(E *e, Res *r)\{\n KSTEP();\n E*ee=e;(void)r;(void)ee;\n{bindStmt}{condStmt}{nodeStmt}}\n"
  return f

/-- Named-arg evaluation in source order — mirrors `evalKArgs`. -/
partial def genNamedArgs (env : String)
    (args : List (String × KExpr)) (dst : String) : EM String := do
  let parts ← args.mapM fun p => do
    let g ← genExpr p.2
    pure s!" \{Val *v={g}({env});if(!v)return 0;{dst}=ecn({cstr p.1},v,{dst});}\n"
  return String.intercalate "" parts

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
            s!"   if(t->k==4)\{if(!strcmp(t->jl,{cstr pre}))\{he=t->ja;continue;}return 0;}\n"
        | none => "   if(t->k==4)return 0;\n"
      let body ←
        if fl.arms.isEmpty then pure "   return h;\n"
        else do
          let d ← genDispatch fl.arms
          pure s!"   \{Res*t={d}(ce,h);\n   if(!t)return 0;\n   if(t->k==3)return r_bare(0);\n{jumpStmt}   return t;}\n"
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

end ISAR
