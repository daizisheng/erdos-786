import Erdos786.Statement

/-!
# Erdős #786 — basic definitions

Working definitions: violations, `q`-matchings, richness, `Q`-parts.
-/

open Finset

namespace Erdos786

/-- A violation of the property. -/
def Violation (A : Set ℕ) : Prop :=
  ∃ s t : Finset ℕ, ↑s ⊆ A ∧ ↑t ⊆ A ∧ s.prod id = t.prod id ∧ s.card ≠ t.card

lemma isMulCardSet_iff_not_violation (A : _root_.Set ℕ) : Set.IsMulCardSet A ↔ ¬ Violation A := by
  unfold Set.IsMulCardSet Violation
  constructor
  · rintro h ⟨s, t, hs, ht, hp, hc⟩
    exact hc (h s t hs ht hp)
  · intro h s t hs ht hp
    by_contra hc
    exact h ⟨s, t, hs, ht, hp, hc⟩

/-- `S` is a matching of `q`-pairs `(x, q x)` inside `A`: every pair lies in `A`, has ratio `q`,
and all `2 |S|` endpoints are distinct. -/
structure IsQMatching (A : Set ℕ) (q : ℚ) (S : Finset (ℕ × ℕ)) : Prop where
  mem : ∀ e ∈ S, e.1 ∈ A ∧ e.2 ∈ A
  ratio : ∀ e ∈ S, (e.2 : ℚ) = q * e.1
  disj : (S.image Prod.fst ∪ S.image Prod.snd).card = 2 * S.card

/-- `q` is `M`-rich for `A`: the `q`-pairs in `A` contain a matching of size at least `M`. -/
def Rich (A : Set ℕ) (q : ℚ) (M : ℕ) : Prop :=
  ∃ S : Finset (ℕ × ℕ), IsQMatching A q S ∧ M ≤ S.card

/-- The largest divisor of `z` composed of primes in `Q`. -/
noncomputable def qPart (Q : Finset ℕ) (z : ℕ) : ℕ :=
  ∏ q ∈ Q, q ^ z.factorization q

end Erdos786
