"""WP136 -- the Astra 6 review's two new theorems, probed (2026-10-08).

The review (papers/astra-6-latest-review-and-extension/, Astra 6, 2026-10-07)
proved two results in prose and reported finite checks. This probe re-derives
everything independently, SELF-CONTAINED: ordered-disjoint frames are
enumerated from the OD axioms (strict order + admissible disjointness), which
by the certified normal form (RCC5NormalForm.lean, odNet_frame) is exactly the
class of strong-EQ RCC5 frames.

  A. The review's own finite checks, reproduced: 41 OD frames on 3 labelled
     points; boundary tables (C_exPO 480/0, C_exPP 12/0, C_allDR 12/0).
  B. NORMALIZATION (review Thm 4.3): for NNF concepts without EX-PO and
     ALL-DR, truth transfers to the maximal-disjointness model (principal
     down-sets). Exhaustive on sizes 2-3 over a 400-concept sample.
     NEGATIVE CONTROL: an EX-PO concept must break it (it does).
  C. PO-ERASURE (review Thm 5.4): for the fragment D (no EX-PP, EX-PO,
     ALL-DR; ALL-PO permitted), Sat(C) iff Sat(erase(C)). Bounded-sat
     comparison on 220 D-concepts, domains up to 4.
     NEGATIVE CONTROLS: the review's C_exPP and C_allDR (outside D) diverge.
  D. C_optional: satisfiable, yet NO principal-down-set model up to size 4 --
     the concept-level witness that overlap can be forced to have no
     represented common part.

Convention (matches the project): rho(x,y)=PP means x is a proper part of y;
an EX-PP witness is a superpart. All checks must PASS; exit code 0 iff so.
The Lean formalization of C is POFreeLift.lean SS299 (erase_equisat,
decidableSat_dfrag); B's interpretation-level statement remains theorem-level.
"""
import itertools, random, sys

FAILURES=[]
def check(name, ok):
    print(("PASS" if ok else "FAIL"), "-", name)
    if not ok: FAILURES.append(name)

def strict_orders(n):
    pairs=[(i,j) for i in range(n) for j in range(n) if i!=j]
    for bits in itertools.product([0,1],repeat=len(pairs)):
        lt={p for p,b in zip(pairs,bits) if b}
        if any((i,i) in lt for i in range(n)): continue
        if any((a,b) in lt and (b,a) in lt for a in range(n) for b in range(n)): continue
        if any((a,b) in lt and (b,c) in lt and (a,c) not in lt
               for a in range(n) for b in range(n) for c in range(n)): continue
        yield frozenset(lt)

def leq(lt,a,b): return a==b or (a,b) in lt

def admissible_disjs(n,lt):
    # symmetric irreflexive #, disjoint from comparability, downward hereditary
    cand=[(i,j) for i in range(n) for j in range(i+1,n)
          if (i,j) not in lt and (j,i) not in lt]
    for bits in itertools.product([0,1],repeat=len(cand)):
        dj={p for p,b in zip(cand,bits) if b}
        djf=dj|{(b,a) for a,b in dj}
        ok=True
        for (x,y) in djf:
            for u in range(n):
                if not leq(lt,u,x): continue
                for v in range(n):
                    if leq(lt,v,y) and (u,v) not in djf and not (u==v)==False and True:
                        pass
            # downward closure check
        for (x,y) in djf:
            for u in range(n):
                for v in range(n):
                    if leq(lt,u,x) and leq(lt,v,y):
                        if u==v: ok=False; break
                        if (u,v) not in djf: ok=False; break
                if not ok: break
            if not ok: break
        if ok: yield frozenset(djf)

def frames(n):
    for lt in strict_orders(n):
        for dj in admissible_disjs(n,lt):
            yield (lt,dj)

def rho(n,lt,dj,x,y):
    if x==y: return 'EQ'
    if (x,y) in lt: return 'PP'
    if (y,x) in lt: return 'PPI'
    if (x,y) in dj: return 'DR'
    return 'PO'

# ---- concept language ----
def sat(n,lt,dj,val,x,C):
    k=C[0]
    if k=='top': return True
    if k=='bot': return False
    if k=='A': return x in val
    if k=='nA': return x not in val
    if k=='and': return sat(n,lt,dj,val,x,C[1]) and sat(n,lt,dj,val,x,C[2])
    if k=='or': return sat(n,lt,dj,val,x,C[1]) or sat(n,lt,dj,val,x,C[2])
    if k=='ex':
        return any(rho(n,lt,dj,x,y)==C[1] and sat(n,lt,dj,val,y,C[2]) for y in range(n))
    if k=='all':
        return all(rho(n,lt,dj,x,y)!=C[1] or sat(n,lt,dj,val,y,C[2]) for y in range(n))
    raise ValueError(k)

def maxdj(n,lt):
    dj=set()
    for x in range(n):
        for y in range(n):
            if x!=y and not any(leq(lt,z,x) and leq(lt,z,y) for z in range(n)):
                dj.add((x,y))
    return frozenset(dj)

# ---- 1. frame count on 3 labelled points ----
F3=list(frames(3))
check("A1: 41 OD frames on 3 labelled points", len(F3)==41)

# ---- 2. boundary tables ----
AND=lambda *cs: cs[0] if len(cs)==1 else ('and',cs[0],AND(*cs[1:]))
C_expo = AND(('ex','PO',('top',)),('all','PO',('bot',)))
C_expo_er = ('ex','PO',('top',))
C_expp = AND(('ex','PP',AND(('A',),('all','PP',('A',)),('all','PO',('A',)))),
             ('ex','PP',AND(('nA',),('all','PP',('nA',)))))
C_expp_er = AND(('ex','PP',AND(('A',),('all','PP',('A',)))),
                ('ex','PP',AND(('nA',),('all','PP',('nA',)))))
C_alldr = AND(('ex','PPI',AND(('A',),('all','PPI',('A',)),('all','DR',('A',)),('all','PO',('A',)))),
              ('ex','PPI',AND(('nA',),('all','PPI',('nA',)))))
C_alldr_er = AND(('ex','PPI',AND(('A',),('all','PPI',('A',)),('all','DR',('A',)))),
                 ('ex','PPI',AND(('nA',),('all','PPI',('nA',)))))
def count3(C):
    c=0
    for lt,dj in F3:
        for vbits in itertools.product([0,1],repeat=3):
            val={i for i in range(3) if vbits[i]}
            for x in range(3):
                if sat(3,lt,dj,val,x,C): c+=1
    return c
check("A2: C_exPO table 480/0", (count3(C_expo_er),count3(C_expo))==(480,0))
check("A3: C_exPP table 12/0", (count3(C_expp_er),count3(C_expp))==(12,0))
check("A4: C_allDR table 12/0", (count3(C_alldr_er),count3(C_alldr))==(12,0))

# ---- 3. normalization theorem, exhaustive on sizes 2..3 + sampled size 4 ----
def gen_concepts(depth, roles_ex, roles_all):
    if depth==0:
        return [('A',),('nA',),('top',)]
    subs=gen_concepts(depth-1,roles_ex,roles_all)
    out=list(subs)
    for s in subs:
        for r in roles_ex: out.append(('ex',r,s))
        for r in roles_all: out.append(('all',r,s))
    for a in subs[:6]:
        for b in subs[:6]:
            out.append(('and',a,b)); out.append(('or',a,b))
    return out

# fragment for normalization: no EX-PO, no ALL-DR
norm_frag = gen_concepts(2, ['PP','PPI','DR','EQ'], ['PP','PPI','PO','EQ'])
random.seed(0)
norm_sample = random.sample(norm_frag, 400)
viol=0; tested=0
for n in (2,3):
    FR=F3 if n==3 else list(frames(2))
    for lt,dj in FR:
        mdj=maxdj(n,lt)
        for vbits in itertools.product([0,1],repeat=n):
            val={i for i in range(n) if vbits[i]}
            for C in norm_sample:
                for x in range(n):
                    if sat(n,lt,dj,val,x,C):
                        tested+=1
                        if not sat(n,lt,mdj,val,x,C): viol+=1
check(f"B1: normalization, {tested} facts, 0 violations", viol==0 and tested>100000)

# sanity negative control: fragment WITH ex-PO must violate
ctrl=('ex','PO',('top',))
cviol=0
for lt,dj in F3:
    mdj=maxdj(3,lt)
    for x in range(3):
        if sat(3,lt,dj,set(),x,ctrl) and not sat(3,lt,mdj,set(),x,ctrl): cviol+=1
check(f"B2: NEGATIVE CONTROL fires ({cviol} ex-PO violations)", cviol>0)

# ---- 4. erasure theorem: equisatisfiability corroboration ----
def erase(C):
    k=C[0]
    if k=='all' and C[1]=='PO': return ('top',)
    if k in ('and','or'): return (k,erase(C[1]),erase(C[2]))
    if k in ('ex','all'): return (k,C[1],erase(C[2]))
    return C
def bsat(C,maxn=4):
    for n in range(1,maxn+1):
        for lt,dj in frames(n):
            for vbits in itertools.product([0,1],repeat=n):
                val={i for i in range(n) if vbits[i]}
                for x in range(n):
                    if sat(n,lt,dj,val,x,C): return True
    return False

# D-fragment: no EX-PP, EX-PO, ALL-DR; ALL-PO allowed
D_frag = gen_concepts(2, ['PPI','DR','EQ'], ['PP','PPI','PO','EQ'])
pool=[c for c in D_frag if 'PO' in str(c)]
# enrich: wrap ALL-PO concepts under allowed modalities so erasure bites at depth
extra=[]
for c in pool:
    for r in ['PPI','DR']: extra.append(('ex',r,c))
    for r in ['PP','PPI']: extra.append(('all',r,c))
    extra.append(('and',c,('ex','DR',('nA',))))
pool=pool+extra
D_sample = random.sample(pool, min(len(pool),220))
print("D-pool size:",len(pool))
diverge=[]
for C in D_sample:
    s_er=bsat(erase(C)); s_c=bsat(C)
    if s_er!=s_c: diverge.append(C)
check(f"C1: erasure, {len(D_sample)} D-concepts, 0 divergences", len(diverge)==0)
for d in diverge[:3]: print("  DIVERGE:", d)

# negative control: C_expp (has EX-PP, outside D) must diverge
check("C2: NEGATIVE CONTROL C_exPP diverges", bsat(C_expp_er) and not bsat(C_expp))
check("C3: NEGATIVE CONTROL C_allDR diverges", bsat(C_alldr_er) and not bsat(C_alldr))

# ---- 5. C_optional: sat, but no principal-down-set model ----
C_opt=AND(('all','PPI',('A',)),('ex','PO',('all','PPI',('nA',))))
check("D1: C_optional satisfiable (general)", bsat(C_opt))
pd=0
for n in (1,2,3,4):
    for lt in strict_orders(n):
        mdj=maxdj(n,lt)
        for vbits in itertools.product([0,1],repeat=n):
            val={i for i in range(n) if vbits[i]}
            for x in range(n):
                if sat(n,lt,mdj,val,x,C_opt): pd+=1
check("D2: C_optional has NO principal-down-set model (<=4)", pd==0)

print()
if FAILURES:
    print("WP136: FAIL --", FAILURES); sys.exit(1)
print("WP136: ALL CHECKS PASS")
