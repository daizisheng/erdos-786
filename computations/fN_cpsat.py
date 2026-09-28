#!/usr/bin/env python3
"""Erdős #786, step 1, implementation A (solver glue: OR-tools CP-SAT; no Rust route for CP-SAT).

f(N)  = max |A|, A ⊆ [1,N], no DISTINCT-element product identity with r != s.
        Violation <=> nonzero c ∈ {-1,0,1}^A, sum c_a v(a) = 0, sum c_a != 0.
g(N)  = same with repetitions allowed <=> exists completely additive F (rational) with F(a)=1 on A.
        Violation <=> integer c with sum c_a v(a) = 0, sum c_a != 0 <=> 1_A not in column space
        (linear algebra over Q).

Counterexample-guided: master CP-SAT maximises |A| under cuts "not all of S", where each S is
the support of a verified violating relation.  Subproblem finds violations for the proposed A.
Every cut is re-verified by exact integer arithmetic before use, so the upper bound certificate is
(list of cuts, master optimality).  Output: one JSON line per N.
"""
import json, sys, time
from fractions import Fraction
from math import prod
from ortools.sat.python import cp_model

def primes_upto(n):
    s = [True] * (n + 1); s[0:2] = [False, False][: n + 1]
    for i in range(2, int(n ** .5) + 1):
        if s[i]:
            s[i * i :: i] = [False] * len(s[i * i :: i])
    return [i for i in range(n + 1) if s[i]]

def vec(n, P):
    out = []
    for p in P:
        e = 0
        while n % p == 0:
            n //= p; e += 1
        out.append(e)
    return out

def check_distinct_relation(c):  # c: dict a -> ±1
    L = [a for a, s in c.items() if s == 1]; R = [a for a, s in c.items() if s == -1]
    return len(set(L) & set(R)) == 0 and prod(L) == prod(R) and len(L) != len(R)

def sub_distinct(A, P, V, maxcuts, timelimit=60.0):
    """Return up to maxcuts violating supports (minimum size first) for set A."""
    cuts = []
    m = cp_model.CpModel()
    pos = {a: m.NewBoolVar(f"p{a}") for a in A}
    neg = {a: m.NewBoolVar(f"n{a}") for a in A}
    for a in A:
        m.Add(pos[a] + neg[a] <= 1)
    for j, p in enumerate(P):
        terms = [(pos[a] - neg[a]) * V[a][j] for a in A if V[a][j]]
        if terms:
            m.Add(sum(terms) == 0)
    m.Add(sum(pos[a] - neg[a] for a in A) >= 1)  # wlog (c -> -c)
    m.Minimize(sum(pos[a] + neg[a] for a in A))
    while len(cuts) < maxcuts:
        s = cp_model.CpSolver(); s.parameters.max_time_in_seconds = timelimit
        s.parameters.num_workers = 8
        st = s.Solve(m)
        if st not in (cp_model.OPTIMAL, cp_model.FEASIBLE):
            if st == cp_model.UNKNOWN:
                raise RuntimeError("subproblem timeout")
            break
        c = {a: (1 if s.Value(pos[a]) else -1) for a in A if s.Value(pos[a]) or s.Value(neg[a])}
        assert check_distinct_relation(c), c
        supp = sorted(c)
        cuts.append(supp)
        # forbid this support (and supersets) to diversify
        z = [m.NewBoolVar("") for _ in supp]
        for zi, a in zip(z, supp):
            m.Add(pos[a] + neg[a] == 0).OnlyEnforceIf(zi)
            m.Add(pos[a] + neg[a] == 1).OnlyEnforceIf(zi.Not())
        m.AddBoolOr(z)
    return cuts

def rank_solve(A, P, V):
    """Is 1 in span of columns? i.e. exists F with V_A F = 1. Exact Gaussian elimination."""
    rows = [[Fraction(x) for x in V[a]] + [Fraction(1)] for a in A]
    ncol = len(P)
    r = 0
    for col in range(ncol):
        piv = next((i for i in range(r, len(rows)) if rows[i][col] != 0), None)
        if piv is None:
            continue
        rows[r], rows[piv] = rows[piv], rows[r]
        pv = rows[r][col]
        rows[r] = [x / pv for x in rows[r]]
        for i in range(len(rows)):
            if i != r and rows[i][col] != 0:
                f = rows[i][col]
                rows[i] = [x - f * y for x, y in zip(rows[i], rows[r])]
        r += 1
    return all(row[-1] == 0 for row in rows[r:])

def sub_rep(A, P, V):
    if rank_solve(A, P, V):
        return []
    S = list(A)  # deletion filter -> minimal infeasible subset
    i = 0
    while i < len(S):
        T = S[:i] + S[i + 1 :]
        if not rank_solve(T, P, V):
            S = T
        else:
            i += 1
    return [sorted(S)]

def solve(N, mode, warm=None, maxcuts=30):
    P = [p for p in primes_upto(N)]
    V = {a: vec(a, P) for a in range(1, N + 1)}
    cuts = [list(x) for x in (warm or [])]
    cuts.append([1])
    it = 0
    while True:
        it += 1
        m = cp_model.CpModel()
        x = {a: m.NewBoolVar(f"x{a}") for a in range(1, N + 1)}
        for S in cuts:
            m.Add(sum(x[a] for a in S) <= len(S) - 1)
        m.Maximize(sum(x.values()))
        s = cp_model.CpSolver(); s.parameters.num_workers = 8
        s.parameters.max_time_in_seconds = 3000
        st = s.Solve(m)
        assert st == cp_model.OPTIMAL, st
        A = [a for a in x if s.Value(x[a])]
        new = sub_distinct(A, P, V, maxcuts) if mode == "distinct" else sub_rep(A, P, V)
        if not new:
            return len(A), A, cuts, it
        cuts.extend(new)

if __name__ == "__main__":
    mode = sys.argv[1]; N0, N1 = int(sys.argv[2]), int(sys.argv[3])
    cuts = []
    for N in range(N0, N1 + 1):
        t = time.time()
        f, A, cuts, it = solve(N, mode, warm=[c for c in cuts if max(c) <= N])
        print(json.dumps({"mode": mode, "N": N, "f": f, "D": N - f, "A": A,
                          "missing": [a for a in range(1, N + 1) if a not in A],
                          "ncuts": len(cuts), "iters": it, "sec": round(time.time() - t, 2)}), flush=True)
