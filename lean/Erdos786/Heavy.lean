import Erdos786.Defs

/-! # Step 1: heavily deleted primes have small reciprocal sum (Turán–Kubilius) -/

open Finset

namespace Erdos786

/-- Paper Lemma 6.2. `E ⊆ [1,N]`, `|E| ≤ N/32`; every `p ∈ H` is a prime `≤ N` with
`|E ∩ pℕ| ≥ N/(16p)`. Then `∑_{p ∈ H} 1/p ≤ 3072 |E| / N`. -/
theorem heavy_recip_sum_le (N : ℕ) (hN : 0 < N) (E : Finset ℕ) (hE : E ⊆ Icc 1 N)
    (hD : 32 * E.card ≤ N) (H : Finset ℕ)
    (hH : ∀ p ∈ H, p.Prime ∧ p ≤ N ∧ (N : ℝ) ≤ 16 * p * (E.filter (fun n => p ∣ n)).card) :
    ∑ p ∈ H, (1 : ℝ) / p ≤ 3072 * E.card / N := by
  sorry

end Erdos786
