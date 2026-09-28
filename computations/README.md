# Exact values of f(N) for N ≤ 60

f(N) = largest admissible subset of {1,…,N} (products of distinct elements). Two independent programs:

- `fN_cpsat.py` — counterexample-guided search with OR-tools CP-SAT (`python3 fN_cpsat.py distinct 2 60`, or `rep` for the repetition-allowed version). Every cut is a violating relation re-verified by exact integer multiplication.
- `fn_rs/` — exhaustive Rust search using f(N) ∈ {f(N−1), f(N−1)+1} and an exact dynamic programme for violations (`cargo run --release -- 60`).

Both give the values in `results.csv` for 2 ≤ N ≤ 60.
