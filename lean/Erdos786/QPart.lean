import Erdos786.Defs

/-! # Step 3: the `Q`-part of a random integer is usually small (Chebyshev + Markov) -/

open Finset Real
open scoped Classical

namespace Erdos786

/-- Paper Lemma 6.4. -/
theorem qPart_tail : ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime ∧ (q : ℝ) ≤ y) →
    ∀ T : ℕ, (((Icc 1 T).filter (fun z => y ^ 40 < (qPart Q z : ℝ))).card : ℝ) ≤ T / 10 := by
  sorry

end Erdos786
