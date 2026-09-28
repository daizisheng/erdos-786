# Erdős Problem #786 (distinct-factor version): both questions answered negatively

A set A of positive integers is *admissible* if a₁⋯aᵣ = b₁⋯bₛ with distinct aᵢ ∈ A and distinct bⱼ ∈ A forces r = s.

1. Every admissible A ⊆ {1,…,N} has Σ_{a∈A} 1/a ≤ ½ log N + (log log N + 2)²; so admissible sets have upper logarithmic density ≤ 1/2 (question (i): **no**).
2. There is an absolute η > 0 such that every admissible A ⊆ {1,…,N} has |A| < (1−η)N for all large N (question (ii): **no**).

- `paper/erdos786.tex` — the paper.
- `computations/` — exact values of the maximum for N ≤ 60 (two independent programs).
- `lean/` — Lean 4 formalization of (2), and of both questions exactly as stated in
  [google-deepmind/formal-conjectures](https://github.com/google-deepmind/formal-conjectures/blob/main/FormalConjectures/ErdosProblems/786.lean)
  (`erdos_786.parts.i`, `erdos_786.parts.ii`, answer resolved to `False`).

## Checking the Lean proof

```
cd lean
lake exe cache get      # Mathlib build cache
lake build
lake env lean Check.lean
```
`Check.lean` prints
```
'Erdos786.erdos_786.parts.i' depends on axioms: [propext, Classical.choice, Quot.sound]
'Erdos786.erdos_786.parts.ii' depends on axioms: [propext, Classical.choice, Quot.sound]
```
No `sorry`, no project axioms. Toolchain `leanprover/lean4:v4.33.1`, Mathlib `0df444a`.
The statements and the definitions they use are copied verbatim from formal-conjectures into
`Erdos786/Statement.lean`. `Erdos786/Vendor/` contains explicit Mertens estimates vendored (Apache-2.0)
from [PrimeNumberTheoremAnd](https://github.com/AlexKontorovich/PrimeNumberTheoremAnd).

| file | content |
|---|---|
| `Statement.lean` | formal-conjectures definitions and statements (verbatim) |
| `Defs.lean` | violations, q-matchings, rich ratios, Q-parts |
| `Lifting.lean` | lifting lemma; many pairs ⇒ large matching |
| `Heavy.lean` | Step 1: heavily deleted primes (Turán–Kubilius) |
| `Smooth.lean` | Step 2: positive proportion of smooth numbers in [X/2, X] |
| `QPart.lean` | Step 3: the Q-part of a random integer is usually small |
| `Coupling.lean` | Step 5: replacing the largest Q-part (core) |
| `Words.lean` | Step 6: short words of rich ratios |
| `Assembly.lean` | Step 7 and constants |
| `Main.lean`, `Reduction.lean`, `Final.lean` | main theorem; reduction to the formal-conjectures statements |
