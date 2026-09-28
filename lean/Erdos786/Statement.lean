import Mathlib

/-!
# Erdős #786 — the statements

The definitions `Set.partialDensity`, `Set.HasDensity` (from `FormalConjecturesForMathlib/Data/Set/Density.lean`)
and `Set.IsMulCardSet`, and the two statements `erdos_786.parts.i` / `erdos_786.parts.ii`, are copied verbatim
from `google-deepmind/formal-conjectures` (`FormalConjectures/ErdosProblems/786.lean`), with `answer(sorry)`
resolved to `False` (both questions have a negative answer). Only the statements are recorded here; the proofs
are in `Erdos786/Final.lean`.
-/

open Filter
open scoped Topology

namespace Set

/-- (formal-conjectures) partial density. -/
@[inline]
noncomputable abbrev partialDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (A : Set β := Set.univ) (b : β) : ℝ :=
  ((S ∩ A) ∩ Iio b).ncard / (A ∩ Iio b).ncard

/-- (formal-conjectures) `S` has density `α` relative to `A`. -/
def HasDensity {β : Type*} [Preorder β] [LocallyFiniteOrderBot β]
    (S : Set β) (α : ℝ) (A : Set β := Set.univ) : Prop :=
  Tendsto (fun (b : β) => S.partialDensity A b) atTop (𝓝 α)

end Set

open Real

namespace Erdos786

open Erdos786

/--
`Nat.IsMulCardSet A` means that `A` is a set of natural numbers that
satisfies the property that $a_1\cdots a_r = b_1\cdots b_s$ with $a_i, b_j\in A$
can only hold when $r = s$.
-/
def Set.IsMulCardSet {α : Type*} [CommMonoid α] (A : Set α) :=
  ∀ (a b : Finset α) (_ :↑a ⊆ A) (_ : ↑b ⊆ A) (_ : a.prod id = b.prod id),
    a.card = b.card

/-- The right-hand side of `erdos_786.parts.i` (formal-conjectures, verbatim). -/
def PartIStatement : Prop :=
  ∀ ε > 0, ε ≤ 1 →
    ∃ (A : Set ℕ) (δ : ℝ), 0 ∉ A ∧ 1 - ε < δ ∧ A.HasDensity δ ∧ A.IsMulCardSet

/-- The right-hand side of `erdos_786.parts.ii` (formal-conjectures, verbatim). -/
def PartIIStatement : Prop :=
  ∃ (A : ℕ → Set ℕ) (f : ℕ → ℝ) (_ : f =o[atTop] (1 : ℕ → ℝ)),
    ∀ N, A N ⊆ Set.Icc 1 (N + 1) ∧ (1 - f N) * N ≤ (A N).ncard ∧ (A N).IsMulCardSet

end Erdos786
