#!/usr/bin/env python3
"""
Random concept generator + tableau oscillation detector for ALCI_RCC5.

Generates random ALCI_RCC5 concepts and runs the Tri-neighborhood
tableau, looking for blocking/unblocking oscillation.

Strategy: generate concepts that are likely to produce infinite models
with many witnesses (lots of ∃ demands + ∀ propagation), since these
create the most Tri-changing opportunities.
"""

import random
import sys
import time
from tableau_oscillation_search import (
    TableauState, concept_str, RELS,
    DR, PO, PP, PPI
)


def random_concept(depth, max_depth=3, atoms=('A', 'B', 'C'),
                   roles=(PP, PO, DR)):
    """Generate a random ALCI_RCC5 concept."""
    if depth >= max_depth:
        # Base case: atom or negated atom
        a = random.choice(atoms)
        if random.random() < 0.3:
            return ('neg', a)
        return ('atom', a)

    choice = random.random()

    if choice < 0.25:
        # Conjunction
        return ('and', random_concept(depth+1, max_depth, atoms, roles),
                random_concept(depth+1, max_depth, atoms, roles))
    elif choice < 0.35:
        # Disjunction
        return ('or', random_concept(depth+1, max_depth, atoms, roles),
                random_concept(depth+1, max_depth, atoms, roles))
    elif choice < 0.65:
        # Exists
        r = random.choice(roles)
        return ('exists', r, random_concept(depth+1, max_depth, atoms, roles))
    elif choice < 0.85:
        # Forall
        r = random.choice(roles)
        return ('forall', r, random_concept(depth+1, max_depth, atoms, roles))
    elif choice < 0.90:
        # Forall with universal role
        return ('forall', '*', random_concept(depth+1, max_depth, atoms, roles))
    else:
        # Atom
        a = random.choice(atoms)
        return ('atom', a)


def generate_chain_concept(chain_role=PP, witness_roles=None,
                           num_witness_types=2, use_forall_star=True):
    """Generate concepts that force infinite chains with witnesses.
    These are the most promising for oscillation."""
    if witness_roles is None:
        witness_roles = [DR, PO]

    atoms = [('atom', chr(65+i)) for i in range(num_witness_types + 1)]
    chain_type = atoms[0]

    # Build witness demands
    witness_demands = []
    for i, wr in enumerate(witness_roles):
        witness_demands.append(('exists', wr, atoms[min(i+1, len(atoms)-1)]))

    # Combine witness demands
    if len(witness_demands) == 1:
        demand = witness_demands[0]
    else:
        demand = witness_demands[0]
        for wd in witness_demands[1:]:
            demand = ('and', demand, wd)

    # Chain continuation
    chain_demand = ('exists', chain_role, chain_type)

    # Body: chain + witnesses
    body = ('and', chain_demand, demand)

    # Root: typed + body
    root = ('and', chain_type, body)

    # Global propagation
    if use_forall_star:
        prop = ('forall', '*', body)
    else:
        prop = ('forall', chain_role, body)

    return ('and', root, prop)


def generate_cross_witness_concept():
    """Generate concepts where witnesses of one node create demands
    that interact with witnesses of another node."""
    A, B, C = ('atom', 'A'), ('atom', 'B'), ('atom', 'C')

    # A-nodes on PP-chain, each has DR-witness (B) and PO-witness (C)
    # B-witnesses need PO to an A
    # C-witnesses need DR to a B
    # This creates cross-references that may cause Tri instability

    variants = []

    # Variant 1: B needs PO-to-A, creating triangles with the chain
    v1 = ('and',
        ('and', A,
            ('and', ('exists', 'PP', A),
                ('and', ('exists', 'DR', ('and', B, ('exists', 'PO', A))),
                        ('exists', 'PO', ('and', C, ('exists', 'DR', B)))))),
        ('forall', 'PP', ('and',
            ('exists', 'PP', A),
            ('and', ('exists', 'DR', ('and', B, ('exists', 'PO', A))),
                    ('exists', 'PO', ('and', C, ('exists', 'DR', B)))))))
    variants.append(('cross-v1', v1))

    # Variant 2: deeper nesting
    v2 = ('and',
        ('and', A,
            ('and', ('exists', 'PP', A),
                ('exists', 'DR', ('and', B,
                    ('exists', 'PO', ('and', A,
                        ('exists', 'DR', B))))))),
        ('forall', '*', ('and',
            ('exists', 'PP', ('top',)),
            ('exists', 'DR', ('top',)))))
    variants.append(('cross-v2', v2))

    # Variant 3: all three witness roles with back-references
    v3 = ('and',
        ('and', A, ('exists', 'PP', A)),
        ('forall', '*', ('and',
            ('exists', 'PP', ('top',)),
            ('and',
                ('exists', 'DR', ('forall', 'DR', ('exists', 'PO', ('top',)))),
                ('exists', 'PO', ('forall', 'PO', ('exists', 'DR', ('top',))))
            ))))
    variants.append(('cross-v3', v3))

    return variants


def run_random_search(num_trials=500, max_nodes=60, max_steps=1500,
                      seed=42):
    random.seed(seed)
    print(f"Random tableau oscillation search")
    print(f"Trials: {num_trials}, max nodes: {max_nodes}, max steps: {max_steps}")
    print(f"{'='*72}")

    best_osc = 0
    best_concept = None
    best_report = None
    total_with_events = 0

    start_time = time.time()

    # Phase 1: Hand-crafted chain concepts
    print(f"\n--- Phase 1: Structured chain concepts ---")
    structured = []
    for chain_r in [PP]:
        for witness_rs in [[DR], [PO], [DR, PO], [DR, PO, PP]]:
            for nwt in [1, 2, 3]:
                for fstar in [True, False]:
                    c = generate_chain_concept(chain_r, witness_rs, nwt, fstar)
                    name = (f"chain({chain_r})+{'_'.join(witness_rs)}"
                            f"_{nwt}types_{'fstar' if fstar else 'fchain'}")
                    structured.append((name, c))

    for name, c in generate_cross_witness_concept():
        structured.append((name, c))

    for name, c in structured:
        tab = TableauState(c, max_nodes=max_nodes, max_steps=max_steps)
        report = tab.run()
        osc = report['max_oscillation']
        events = report['total_block_events']
        if events > 0:
            total_with_events += 1
        if osc > best_osc:
            best_osc = osc
            best_concept = (name, c)
            best_report = report
        flag = " <<<" if osc > 0 else ""
        if events > 0 or osc > 0:
            print(f"  {name:50s} osc={osc} events={events} "
                  f"nodes={report['total_created']}{flag}")

    # Phase 2: Random concepts
    print(f"\n--- Phase 2: Random concepts ({num_trials} trials) ---")
    hits = 0
    for trial in range(num_trials):
        depth = random.choice([2, 3, 4])
        atoms = random.choice([
            ('A', 'B'),
            ('A', 'B', 'C'),
            ('A', 'B', 'C', 'D'),
        ])
        c = random_concept(0, max_depth=depth, atoms=atoms)

        tab = TableauState(c, max_nodes=max_nodes, max_steps=max_steps)
        report = tab.run()
        osc = report['max_oscillation']
        events = report['total_block_events']
        if events > 0:
            total_with_events += 1
        if osc > best_osc:
            best_osc = osc
            best_concept = (f"random_{trial}", c)
            best_report = report
            print(f"  *** Trial {trial}: osc={osc} events={events} "
                  f"nodes={report['total_created']}")
            print(f"      {concept_str(c)}")
        elif osc > 0:
            hits += 1
            if hits <= 20:
                print(f"  Trial {trial}: osc={osc} events={events} "
                      f"nodes={report['total_created']}")
                print(f"      {concept_str(c)}")

    # Phase 3: Mutation of best
    if best_concept and best_osc > 0:
        print(f"\n--- Phase 3: Mutating best concept ({best_concept[0]}) ---")
        base = best_concept[1]
        for m in range(100):
            c = mutate(base)
            tab = TableauState(c, max_nodes=max_nodes, max_steps=max_steps)
            report = tab.run()
            osc = report['max_oscillation']
            if osc > best_osc:
                best_osc = osc
                best_concept = (f"mutant_{m}", c)
                best_report = report
                print(f"  *** Mutant {m}: osc={osc} events={report['total_block_events']} "
                      f"nodes={report['total_created']}")
                print(f"      {concept_str(c)}")

    elapsed = time.time() - start_time
    print(f"\n{'='*72}")
    print(f"Search complete in {elapsed:.1f}s")
    print(f"Total concepts with blocking events: {total_with_events}")
    print(f"Maximum oscillation (unblocks per node): {best_osc}")
    if best_concept:
        print(f"Best concept: {best_concept[0]}")
        print(f"  {concept_str(best_concept[1])}")
        if best_report:
            print(f"  Nodes: {best_report['total_created']}, "
                  f"Events: {best_report['total_block_events']}, "
                  f"Steps: {best_report['total_steps']}")
            if best_report['node_unblock_counts']:
                print(f"  Unblock counts: {best_report['node_unblock_counts']}")

    if best_osc > 0:
        print(f"\n*** Re-running best with verbose output ***")
        tab = TableauState(best_concept[1], max_nodes=max_nodes,
                           max_steps=max_steps, verbose=True)
        tab.run()

    return best_osc


def mutate(concept):
    """Randomly mutate a concept."""
    if concept[0] in ('atom', 'neg', 'top', 'bot'):
        r = random.random()
        if r < 0.2:
            return ('exists', random.choice(RELS), concept)
        elif r < 0.4:
            return ('forall', random.choice(RELS), concept)
        return concept

    if concept[0] in ('and', 'or'):
        branch = random.choice([1, 2])
        if branch == 1:
            return (concept[0], mutate(concept[1]), concept[2])
        else:
            return (concept[0], concept[1], mutate(concept[2]))

    if concept[0] in ('exists', 'forall'):
        r = random.random()
        if r < 0.3:
            # Change role
            new_role = random.choice(RELS)
            return (concept[0], new_role, concept[2])
        elif r < 0.6:
            # Mutate filler
            return (concept[0], concept[1], mutate(concept[2]))
        else:
            # Wrap in another quantifier
            return ('and', concept,
                    ('exists', random.choice(RELS), ('top',)))

    return concept


if __name__ == '__main__':
    num_trials = int(sys.argv[1]) if len(sys.argv) > 1 else 500
    max_nodes = int(sys.argv[2]) if len(sys.argv) > 2 else 60
    seed = int(sys.argv[3]) if len(sys.argv) > 3 else 42
    run_random_search(num_trials=num_trials, max_nodes=max_nodes, seed=seed)
