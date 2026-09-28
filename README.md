# Erdős Problem #786 (distinct-factor version): both questions answered negatively

- `paper/` — the paper (in preparation).
- `lean/` — Lean 4 formalization (in progress). Build: `cd lean && lake build`.

Results (for products of *distinct* elements):
1. If A ⊆ {1,…,N} has the property, then Σ_{a∈A} 1/a ≤ ½ log N + (log log N + 2)². Hence the upper logarithmic density of an infinite such set is at most 1/2 (question (i): no).
2. There is an absolute η > 0 such that every such A ⊆ {1,…,N} has |A| < (1−η)N for all large N (question (ii): no).
