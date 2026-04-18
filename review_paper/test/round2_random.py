#!/usr/bin/env python3
"""Medium-depth random attacks, saves output line-by-line."""
import sys, time, random, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), '..', '..', 'src'))
import cover_tree_tableau as ct
import alcircc5_reasoner as qm
from alcircc5_reasoner import (
    DR, PO, PP, PPI,
    AtomicConcept, NegAtomicConcept,
    And, Or, Exists, ForAll,
)

def qm_sat(C): return qm.check_satisfiability(C, cycle_close=True)[0]
def ct_sat(C): return ct.check_satisfiability(C)[0]

def rand_concept(depth, atoms=['A','B','C'], roles=[DR, PO, PP, PPI], p_atom=0.4):
    if depth == 0 or random.random() < p_atom:
        a = random.choice(atoms)
        return AtomicConcept(a) if random.random() < 0.5 else NegAtomicConcept(a)
    k = random.random()
    if k < 0.2: return And(rand_concept(depth-1, atoms, roles), rand_concept(depth-1, atoms, roles))
    elif k < 0.4: return Or(rand_concept(depth-1, atoms, roles), rand_concept(depth-1, atoms, roles))
    elif k < 0.7: return Exists(random.choice(roles), rand_concept(depth-1, atoms, roles))
    else: return ForAll(random.choice(roles), rand_concept(depth-1, atoms, roles))

seed = int(sys.argv[1]) if len(sys.argv) > 1 else 1
ntests = int(sys.argv[2]) if len(sys.argv) > 2 else 100
max_per_test = float(sys.argv[3]) if len(sys.argv) > 3 else 30.0

random.seed(seed)
mismatches = 0
total_done = 0
skipped = 0
t_all = time.time()
print(f'Seed={seed} n={ntests} max_per_test={max_per_test}s', flush=True)
for i in range(ntests):
    depth = random.choice([3, 4])
    n_atoms = random.choice([2, 3])
    atoms = ['A', 'B', 'C'][:n_atoms]
    C = rand_concept(depth, atoms=atoms)
    t0 = time.time()
    try:
        # Measure ct time first to decide to skip qm if ct is slow
        ctr = ct_sat(C)
        ct_t = time.time() - t0
        if ct_t > max_per_test:
            skipped += 1
            print(f'  [{i:3d}] SKIP (ct too slow {ct_t:.1f}s)', flush=True)
            continue
        t1 = time.time()
        qmr = qm_sat(C)
        qm_t = time.time() - t1
        if qm_t > max_per_test:
            skipped += 1
            print(f'  [{i:3d}] SKIP (qm too slow {qm_t:.1f}s)', flush=True)
            continue
        total_done += 1
        if ctr != qmr:
            mismatches += 1
            print(f'  [{i:3d}] MISMATCH CT={ctr} QMc={qmr}  C={C}', flush=True)
    except Exception as e:
        print(f'  [{i:3d}] EXC: {type(e).__name__}', flush=True)
    if i % 20 == 19:
        print(f'  ...{i+1}/{ntests}, done={total_done}, mismatches={mismatches}, skipped={skipped}, elapsed={time.time()-t_all:.1f}s', flush=True)

print(f'\nSeed={seed} tests={ntests} done={total_done} skipped={skipped} mismatches={mismatches}')
