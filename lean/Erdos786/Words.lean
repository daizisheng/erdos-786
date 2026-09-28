import Erdos786.Lifting

/-! # Step 6: every good prime is a short product of rich ratios (induction on primes) -/

open Finset Real

namespace Erdos786

/-- Paper Lemma 6.7, abstract form. `good` is the set of admissible primes (nonheavy, `≤ P`).
Small primes (`≤ p₀`) are rich; every good prime `p > p₀` has a replacement `p = (pk/m)·m·k⁻¹`
with `pk/m` rich, `k, m` composed of good primes `q` with `q^16 ≤ p`, `k ≤ p^(5/2)`, `m ≤ pk`.
Then every good prime is a product of at most `16 (log p)^2` rich ratios (or their inverses). -/
theorem short_word (A : Set ℕ) (M p₀ : ℕ) (good : ℕ → Prop)
    (hsmall : ∀ p, p.Prime → p ≤ p₀ → Rich A p M)
    (hstep : ∀ p, p.Prime → good p → p₀ < p → ∃ k m : ℕ, 1 ≤ k ∧ 1 ≤ m ∧
      (∀ q ∈ k.primeFactors, good q ∧ q ^ 16 ≤ p) ∧ (∀ q ∈ m.primeFactors, good q ∧ q ^ 16 ≤ p) ∧
      (k : ℝ) ^ 2 ≤ (p : ℝ) ^ 5 ∧ m ≤ p * k ∧ Rich A ((p * k : ℕ) / (m : ℚ)) M) :
    ∀ p, p.Prime → (good p ∨ p ≤ p₀) →
      ∃ w : List ℚ, w.prod = p ∧ (∀ q ∈ w, Rich A q M) ∧ (w.length : ℝ) ≤ 16 * (Real.log p) ^ 2 := by
  sorry

end Erdos786
