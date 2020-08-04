import argparse
from itertools import chain
from typing import Dict, List, Set, Tuple

NUM_CLAUSES_TO_SKIP=1
NUM_CLAUSES_TO_SEARCH_FOR=1


Lit = int
Smt2 = str

def lit_to_smt2(i: Lit) -> str:
    assert i != 0
    # IMPORTANT special invariant of IC3Ref
    # what it calls 0 (we will call 1 because we add 1 so it doesn't
    # clash with zero termination)
    # is just false or true when it's negated
    if i == 1:
        return "false"
    if i == -1:
        return "true"

    if i > 0:
        return f"l{i}"
    else:
        return f"(not l{-i})"

def var_to_smt2(i: Lit) -> str:
    assert i > 1, "Expecting a variable"
    return lit_to_smt2(i)

def negate(s: Smt2) -> Smt2:
    return f"(not {s})"

def param_list(vs: List[Smt2]) -> Smt2:
    return " ".join(f"({v} Bool)" for v in vs)

def space_sep_list(vs: List[Lit]) -> Smt2:
    return " ".join(map(var_to_smt2, vs))

def cnf_to_smt2(cnf: List[List[Smt2]]) -> Smt2:
    if len(cnf) == 0:
        return "true"

    if len(cnf) > 1:
        str_cnf = "(and\n"
    for clause in cnf:
        assert clause
        if "true" in clause:
            continue
        if len(clause) == 1:
            str_clause = clause[0]
        else:
            str_clause = "  (or"
            for l in clause:
                assert l != 0
                str_clause += " "
                str_clause += l
            str_clause += ")"
        str_cnf += str_clause + "\n"
    if len(cnf) > 1:
        str_cnf += ")"
    return str_cnf

if __name__ == "__main__":
    parser = argparse.ArgumentParser(description="Generate smt2 encoding of invariant search from IC3ref output")
    parser.add_argument("--base", type=str, help="Base name of dumped files")
    parser.add_argument("--trans", type=str, help="CNF for the transition relation")
    parser.add_argument("--init", type=str, help="CNF for the initial states")
    parser.add_argument("--inv", type=str, help="CNF for the invariant found by IC3ref")
    parser.add_argument("--mapping", type=str, help="Space-delimited mapping from current to next state vars")

    args = parser.parse_args()

    file_trans = args.trans
    file_init = args.init
    file_inv = args.inv
    file_mapping = args.mapping
    base = args.base
    if base:
        file_trans   = base + "-trans.cnf"
        file_init    = base + "-init.cnf"
        file_inv     = base + "-inv.cnf"
        file_mapping = base + "-mapping.txt"
    elif (not file_trans or
          not file_init or
          not file_inv or
          not file_mapping):
        raise ValueError("If base not provided, then all four other options must be given")


    transl = open(file_trans).read().splitlines()
    invl   = open(file_inv).read().splitlines()
    initl  = open(file_init).read().splitlines()
    pml    = open(file_mapping).read().splitlines()

    _prime: Dict[int, int] = {}
    for l in pml:
        k, v = map(int, l.split())
        _prime[k] = v
    assert 1 not in _prime
    assert 1 not in _prime.values()
    _unprime = {v:k for k, v in _prime.items()}

    def prime(l: Lit) -> Lit:
        if abs(l) == 1:
            return l
        elif l < 0:
            return -_prime[-l]
        else:
            return _prime[l]

    def unprime(l: Lit) -> Lit:
        if abs(l) == 1:
            return l
        elif l < 0:
            return -_unprime[-l]
        else:
            return _unprime[l]

    trans: List[List[int]] = []
    for l in transl:
        trans.append([int(c) for c in l.split()[:-1]])

    inv: List[List[int]] = []
    for l in invl:
        if l.strip()[0] == 'c':
            # this line is a comment
            continue
        inv.append([int(c) for c in l.split()[:-1]])

    # the property is the first element of the invariant
    prop = inv[0]
    assert len(prop) == 1, 'expecting a single literal'
    prop = prop[0]

    # IC3ref filters the property out of init
    # add it back in for now
    init: List[List[int]] = [[prop]]
    for l in initl:
        init.append([int(c) for c in l.split()[:-1]])

    # drop some clauses -- try to get CVC4 to find them
    if NUM_CLAUSES_TO_SKIP > 0:
        inv = inv[:-NUM_CLAUSES_TO_SKIP]

    # IMPORTANT: Special invariant of IC3Ref
    # what it calls 0 (we add 1 to all vars so it's 1)
    # just exists to refer to false (1) and true (-1)
    vs: List[Lit] = [v for v in
                     sorted(set(abs(v) for c in chain(init, trans, inv, [_unprime.keys(), _unprime.values()]) for v in c))
                     if v != 1]
    current_vs: List[Lit] = sorted(_prime.keys())
    next_vs: List[Lit] = [prime(v) for v in current_vs]

    current_lits = [l for v in current_vs for l in [v, -v]]

    assert len(current_vs) <= len(vs)/2, f"Expecting less than half to be current vars but got {current_vs} and {vs}"

    indicator_literals: Dict[Tuple[int, Lit], Smt2] = {}
    for i in range(NUM_CLAUSES_TO_SEARCH_FOR):
        for v in current_vs:
            name = f"x_{i}_{lit_to_smt2(v)}"
            indicator_literals[i, v] = name
            indicator_literals[i, -v] = name + "_not"

    cnf: List[List[Smt2]] = []

    # Tseitin variables
    cti: Smt2 = "cti"
    inv_post_vs: List[Smt2] = [f"inv_post_{i}" for i in range(len(inv))]
    q_post_vs = [f"q_post_{i}" for i in range(NUM_CLAUSES_TO_SEARCH_FOR)]


    q_pre: Dict[Tuple[int, Lit], Smt2] = {}
    for (i, lit), x in indicator_literals.items():
        q_pre[i, lit] = f"q_pre_{i}_{x}"
        cnf.append([negate(q_pre[i, lit]), x])
        cnf.append([negate(q_pre[i, lit]), lit_to_smt2(lit)])

    cnf.append([negate(x) for x in inv_post_vs + q_post_vs])

    cnf.extend(
        [inv_post_vs[i], lit_to_smt2(prime(-v))]
        for i, clause in enumerate(inv)
        for v in clause
    )

    cnf.extend(
        [q_post_vs[i], negate(x), lit_to_smt2(prime(-lit))]
        for (i, lit), x in indicator_literals.items()
    )

    # Inv Pre
    # If it's a CTI then invariant holds in pre-state
    cnf.extend(
        [negate(cti)] + [lit_to_smt2(lit) for lit in clause]
        for clause in inv
    )

    # Also for the unknown part of the invariant
    cnf.extend(
        [negate(cti)] + [q_pre[i, lit] for lit in current_lits]
        for i in range(NUM_CLAUSES_TO_SEARCH_FOR)
    )

    cnf.extend(
        [cti] + [lit_to_smt2(prime(l)) for l in clause]
        for clause in init
    )

    cnf.extend(
        [negate(cti)] + [lit_to_smt2(l) for l in clause]
        for clause in trans
    )


    # print("(set-logic UF)\n(set-option :produce-models true)\n")
    print("(assert")
    print(f"(forall ({param_list(indicator_literals.values())})")
    print(f"(exists ({param_list(chain([cti], [lit_to_smt2(v) for v in vs], inv_post_vs, q_post_vs, q_pre.values()))})")
    print(cnf_to_smt2(cnf))
    print(")))")
    print("(check-sat)")
