import Erdos786.Defs

/-! # The lifting lemma (paper Lemma 3.1) and matchings from many pairs (Lemma 3.2) -/

open Finset

namespace Erdos786

theorem Rich.mono {A : Set ℕ} {q : ℚ} {M M' : ℕ} (h : Rich A q M) (hM : M' ≤ M) : Rich A q M' := by
  obtain ⟨S, hS, hc⟩ := h
  exact ⟨S, hS, hM.trans hc⟩

/-- Richness is invariant under inversion of the ratio. -/
theorem Rich.inv {A : Set ℕ} {q : ℚ} {M : ℕ} (hq : q ≠ 0) (h : Rich A q M) : Rich A q⁻¹ M := by
  sorry

/-- **Lifting lemma.** If `a ∈ A` is a product of rationals `q₁ ⋯ qₜ`, each of which has a matching
of size `2t` in `A`, then `A` contains a violation (`a·x₁⋯xₜ = y₁⋯yₜ`, all distinct). -/
theorem violation_of_word (A : Set ℕ) (h0 : 0 ∉ A) (a : ℕ) (ha : a ∈ A) (qs : List ℚ)
    (hprod : (a : ℚ) = qs.prod) (hrich : ∀ q ∈ qs, Rich A q (2 * qs.length)) : Violation A := by
  sorry

/-- **Many pairs give a matching.** For a fixed ratio `q > 1`, a set `L` of lower endpoints of
`q`-pairs in `A` yields a matching of size at least `|L| / 3` (each pair meets at most two others). -/
theorem rich_of_pairs (A : Set ℕ) (h0 : 0 ∉ A) (q : ℚ) (hq : 1 < q) (L : Finset ℕ)
    (hL : ∀ x ∈ L, x ∈ A ∧ ∃ y ∈ A, (y : ℚ) = q * x) : Rich A q (L.card / 3) := by
  sorry

end Erdos786
