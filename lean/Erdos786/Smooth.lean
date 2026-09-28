import Erdos786.Defs
import PrimeNumberTheoremAnd.IEANTN.Mertens

/-! # Step 2: an explicit positive proportion of smooth numbers in `[X/2, X]`

Uses Mertens' second theorem with explicit error (`Mertens.E₂p.abs_le` from PrimeNumberTheoremAnd)
in place of Rosser–Schoenfeld; the constant `c₀` is therefore not `e^{-1400}` but some positive
constant, which is all the main theorem needs. -/

open Finset Real
open scoped Classical

namespace Erdos786

/-- Paper Lemma 6.3 (with an unspecified constant). -/
theorem smooth_count : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ X : ℝ, y ^ 16 ≤ X → X ≤ y ^ 56 →
    c₀ * X ≤ (((Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card : ℝ) := by
  sorry

end Erdos786
