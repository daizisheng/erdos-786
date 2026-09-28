import Erdos786.Defs

/-! # The lifting lemma (paper Lemma 3.1) and matchings from many pairs (Lemma 3.2) -/

open Finset

namespace Erdos786

theorem Rich.mono {A : Set ℕ} {q : ℚ} {M M' : ℕ} (h : Rich A q M) (hM : M' ≤ M) : Rich A q M' := by
  obtain ⟨S, hS, hc⟩ := h
  exact ⟨S, hS, hM.trans hc⟩

/-- The endpoint-distinctness condition of a matching, unpacked: lower endpoints are distinct,
upper endpoints are distinct, and no lower endpoint equals an upper endpoint. -/
lemma disj_iff (S : Finset (ℕ × ℕ)) :
    (S.image Prod.fst ∪ S.image Prod.snd).card = 2 * S.card ↔
      ((∀ e ∈ S, ∀ e' ∈ S, e.1 = e'.1 → e = e') ∧ (∀ e ∈ S, ∀ e' ∈ S, e.2 = e'.2 → e = e') ∧
        (∀ e ∈ S, ∀ e' ∈ S, e.1 ≠ e'.2)) := by
  constructor
  · intro h
    have h1 := card_union_add_card_inter (S.image Prod.fst) (S.image Prod.snd)
    have h2 := card_image_le (s := S) (f := Prod.fst)
    have h3 := card_image_le (s := S) (f := Prod.snd)
    have hf : (S.image Prod.fst).card = S.card := by omega
    have hs : (S.image Prod.snd).card = S.card := by omega
    have hi : (S.image Prod.fst ∩ S.image Prod.snd).card = 0 := by omega
    rw [card_image_iff] at hf hs
    rw [card_eq_zero] at hi
    refine ⟨fun e he e' he' h => hf he he' h, fun e he e' he' h => hs he he' h, ?_⟩
    intro e he e' he' h
    have : e.1 ∈ S.image Prod.fst ∩ S.image Prod.snd :=
      mem_inter.2 ⟨mem_image_of_mem _ he, h ▸ mem_image_of_mem _ he'⟩
    rw [hi] at this
    simp at this
  · rintro ⟨hf, hs, hd⟩
    rw [card_union_of_disjoint, card_image_of_injOn, card_image_of_injOn]
    · ring
    · intro e he e' he' h; exact hs e he e' he' h
    · intro e he e' he' h; exact hf e he e' he' h
    · rw [disjoint_left]
      intro z hz hz'
      obtain ⟨e, he, rfl⟩ := mem_image.1 hz
      obtain ⟨e', he', h⟩ := mem_image.1 hz'
      exact hd e he e' he' h.symm

/-- Richness is invariant under inversion of the ratio. -/
theorem Rich.inv {A : Set ℕ} {q : ℚ} {M : ℕ} (hq : q ≠ 0) (h : Rich A q M) : Rich A q⁻¹ M := by
  obtain ⟨S, hS, hc⟩ := h
  refine ⟨S.image Prod.swap, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro e he'
    obtain ⟨e, he, rfl⟩ := mem_image.1 he'
    exact ⟨(hS.mem e he).2, (hS.mem e he).1⟩
  · intro e he'
    obtain ⟨e, he, rfl⟩ := mem_image.1 he'
    simp only [Prod.fst_swap, Prod.snd_swap]
    rw [hS.ratio e he, ← mul_assoc, inv_mul_cancel₀ hq, one_mul]
  · obtain ⟨hf, hs, hd⟩ := (disj_iff S).1 hS.disj
    rw [disj_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro e0 he0 e0' he0' h
      obtain ⟨e, he, rfl⟩ := mem_image.1 he0
      obtain ⟨e', he', rfl⟩ := mem_image.1 he0'
      rw [hs e he e' he' h]
    · intro e0 he0 e0' he0' h
      obtain ⟨e, he, rfl⟩ := mem_image.1 he0
      obtain ⟨e', he', rfl⟩ := mem_image.1 he0'
      rw [hf e he e' he' h]
    · intro e0 he0 e0' he0' h
      obtain ⟨e, he, rfl⟩ := mem_image.1 he0
      obtain ⟨e', he', rfl⟩ := mem_image.1 he0'
      exact hd e' he' e he h.symm
  · rw [card_image_of_injective _ Prod.swap_injective]; exact hc

/-- In a matching of size exceeding `|F|`, some pair avoids the finite set `F`. -/
lemma exists_pair_avoiding {A : Set ℕ} {q : ℚ} {S : Finset (ℕ × ℕ)} (hS : IsQMatching A q S)
    (F : Finset ℕ) (hF : F.card < S.card) : ∃ e ∈ S, e.1 ∉ F ∧ e.2 ∉ F := by
  obtain ⟨hf, hs, hd⟩ := (disj_iff S).1 hS.disj
  classical
  by_contra hcon
  push Not at hcon
  have : S.card ≤ F.card := by
    refine card_le_card_of_injOn (fun e => if e.1 ∈ F then e.1 else e.2) ?_ ?_
    · intro e he
      by_cases h1 : e.1 ∈ F
      · simp [h1]
      · simp [h1, hcon e he h1]
    · intro e he e' he' h
      simp only at h
      have he := mem_coe.1 he
      have he' := mem_coe.1 he'
      split_ifs at h with h1 h2 h2
      · exact hf e he e' he' h
      · exact absurd h (hd e he e' he')
      · exact absurd h.symm (hd e' he' e he)
      · exact hs e he e' he' h
  omega

/-- Generalised lifting: choose, for each ratio in `qs`, a pair avoiding `F` and all previously
chosen endpoints. -/
lemma lift_aux (A : Set ℕ) (N : ℕ) : ∀ (qs : List ℚ) (F : Finset ℕ),
    (∀ q ∈ qs, Rich A q N) → F.card + 2 * qs.length ≤ N + 1 →
    ∃ X Y : Finset ℕ, (↑X : Set ℕ) ⊆ A ∧ (↑Y : Set ℕ) ⊆ A ∧ Disjoint X Y ∧ Disjoint F X ∧
      Disjoint F Y ∧ X.card = qs.length ∧ Y.card = qs.length ∧
      (∏ y ∈ Y, (y : ℚ)) = qs.prod * ∏ x ∈ X, (x : ℚ) := by
  intro qs
  induction qs with
  | nil =>
    intro F _ _
    exact ⟨∅, ∅, by simp, by simp, by simp, by simp, by simp, by simp, by simp, by simp⟩
  | cons q rest ih =>
    intro F hrich hcard
    obtain ⟨S, hS, hSc⟩ := hrich q (List.mem_cons_self ..)
    simp only [List.length_cons] at hcard
    obtain ⟨e, he, h1, h2⟩ := exists_pair_avoiding hS F (by omega)
    obtain ⟨hf, hs, hd⟩ := (disj_iff S).1 hS.disj
    have hxy : e.1 ≠ e.2 := hd e he e he
    obtain ⟨X, Y, hXA, hYA, hXY, hFX, hFY, hXc, hYc, hprod⟩ :=
      ih (insert e.1 (insert e.2 F)) (fun q' hq' => hrich q' (List.mem_cons_of_mem _ hq'))
        (by
          have := card_insert_le e.1 (insert e.2 F)
          have := card_insert_le e.2 F
          omega)
    simp only [disjoint_insert_left] at hFX hFY
    have hxX : e.1 ∉ X := hFX.1
    have hyY : e.2 ∉ Y := hFY.2.1
    have hxY : e.1 ∉ Y := hFY.1
    have hyX : e.2 ∉ X := hFX.2.1
    refine ⟨insert e.1 X, insert e.2 Y, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [coe_insert]; exact Set.insert_subset (hS.mem e he).1 hXA
    · rw [coe_insert]; exact Set.insert_subset (hS.mem e he).2 hYA
    · rw [disjoint_insert_left, disjoint_insert_right]
      exact ⟨by simp [hxy, hxY], hyX, hXY⟩
    · rw [disjoint_insert_right]
      exact ⟨h1, hFX.2.2⟩
    · rw [disjoint_insert_right]
      exact ⟨h2, hFY.2.2⟩
    · rw [card_insert_of_notMem hxX, hXc]; simp
    · rw [card_insert_of_notMem hyY, hYc]; simp
    · rw [prod_insert hxX, prod_insert hyY, hprod, hS.ratio e he, List.prod_cons]
      ring

/-- **Lifting lemma.** If `a ∈ A` is a product of rationals `q₁ ⋯ qₜ`, each of which has a matching
of size `2t` in `A`, then `A` contains a violation (`a·x₁⋯xₜ = y₁⋯yₜ`, all distinct). -/
theorem violation_of_word (A : Set ℕ) (h0 : 0 ∉ A) (a : ℕ) (ha : a ∈ A) (qs : List ℚ)
    (hprod : (a : ℚ) = qs.prod) (hrich : ∀ q ∈ qs, Rich A q (2 * qs.length)) : Violation A := by
  obtain ⟨X, Y, hXA, hYA, _, hFX, _, hXc, hYc, hp⟩ :=
    lift_aux A (2 * qs.length) qs {a} hrich (by simp only [card_singleton]; omega)
  have haX : a ∉ X := by
    rw [disjoint_singleton_left] at hFX; exact hFX
  refine ⟨insert a X, Y, ?_, hYA, ?_, ?_⟩
  · rw [coe_insert]; exact Set.insert_subset ha hXA
  · rw [prod_insert haX]
    have : ((a * X.prod id : ℕ) : ℚ) = ((Y.prod id : ℕ) : ℚ) := by
      push_cast
      simp only [id]
      rw [hp, hprod]
    exact_mod_cast this
  · rw [card_insert_of_notMem haX, hXc, hYc]; omega

/-- Generalised version of `rich_of_pairs`, also recording that lower endpoints lie in `L`. -/
lemma rich_of_pairs_aux (A : Set ℕ) (h0 : 0 ∉ A) (q : ℚ) (hq : 1 < q) : ∀ (n : ℕ) (L : Finset ℕ),
    L.card = n → (∀ x ∈ L, x ∈ A ∧ ∃ y ∈ A, (y : ℚ) = q * x) →
    ∃ S : Finset (ℕ × ℕ), IsQMatching A q S ∧ L.card / 3 ≤ S.card ∧ ∀ e ∈ S, e.1 ∈ L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro L hLn hL
  rcases L.eq_empty_or_nonempty with hE | hne
  · subst hE
    refine ⟨∅, ⟨by simp, by simp, by simp⟩, by simp, by simp⟩
  classical
  set x := L.min' hne with hxdef
  have hxL : x ∈ L := min'_mem L hne
  obtain ⟨hxA, y, hyA, hy⟩ := hL x hxL
  set L' := (L.erase x).erase y with hL'
  have hL'sub : L' ⊆ L := (erase_subset _ _).trans (erase_subset _ _)
  have hL'c : L.card ≤ L'.card + 2 := by
    have h1 : (L.erase x).card - 1 ≤ L'.card := pred_card_le_card_erase
    have h2 : (L.erase x).card = L.card - 1 := card_erase_of_mem hxL
    have h3 : 0 < L.card := card_pos.2 hne
    omega
  have hL'lt : L'.card < n := by
    have : L'.card < L.card :=
      lt_of_le_of_lt (card_le_card (erase_subset _ _)) (card_erase_lt_of_mem hxL)
    omega
  obtain ⟨S', hS', hS'c, hS'L⟩ := ih _ hL'lt L' rfl (fun z hz => hL z (hL'sub hz))
  have hxpos : (0 : ℚ) < x := by
    have : x ≠ 0 := fun h => h0 (h ▸ hxA)
    exact_mod_cast Nat.pos_of_ne_zero this
  -- every lower endpoint in `L'` exceeds `x`
  have hgt : ∀ z ∈ L', x < z := by
    intro z hz
    have hz1 : z ≠ x := by
      intro h; rw [hL', mem_erase, mem_erase] at hz; exact hz.2.1 h
    exact lt_of_le_of_ne (min'_le L z (hL'sub hz)) (Ne.symm hz1)
  have hxy_lt : (x : ℚ) < y := by rw [hy]; nlinarith
  have hxy : x ≠ y := by intro h; rw [h] at hxy_lt; exact lt_irrefl _ hxy_lt
  obtain ⟨hf, hs, hd⟩ := (disj_iff S').1 hS'.disj
  have hnot : (x, y) ∉ S' := by
    intro h
    have := hS'L _ h
    exact lt_irrefl _ (hgt x this)
  refine ⟨insert (x, y) S', ⟨?_, ?_, ?_⟩, ?_, ?_⟩
  · intro e he
    rcases mem_insert.1 he with rfl | he
    · exact ⟨hxA, hyA⟩
    · exact hS'.mem e he
  · intro e he
    rcases mem_insert.1 he with rfl | he
    · exact hy
    · exact hS'.ratio e he
  · -- facts about pairs of `S'`
    have hlow : ∀ e ∈ S', x < e.1 ∧ e.1 ≠ y := by
      intro e he
      have h1 := hS'L e he
      refine ⟨hgt _ h1, ?_⟩
      intro h
      rw [hL', mem_erase] at h1
      exact h1.1 h
    have hup : ∀ e ∈ S', x < e.2 ∧ e.2 ≠ y := by
      intro e he
      have hl := hlow e he
      have hr := hS'.ratio e he
      have hx1 : (x : ℚ) < e.1 := by exact_mod_cast hl.1
      refine ⟨?_, ?_⟩
      · have : (x : ℚ) < e.2 := by rw [hr]; nlinarith
        exact_mod_cast this
      · intro h
        have h2 : (e.2 : ℚ) = y := by rw [h]
        rw [hr, hy] at h2
        have h3 : (e.1 : ℚ) = x := mul_left_cancel₀ (by linarith : q ≠ 0) h2
        have h4 : e.1 = x := by exact_mod_cast h3
        rw [h4] at hl
        exact lt_irrefl _ hl.1
    rw [disj_iff]
    refine ⟨?_, ?_, ?_⟩
    · intro e he e' he' h
      rcases mem_insert.1 he with rfl | he <;> rcases mem_insert.1 he' with rfl | he'
      · rfl
      · exact absurd h (ne_of_lt (hlow e' he').1)
      · exact absurd h.symm (ne_of_lt (hlow e he).1)
      · exact hf e he e' he' h
    · intro e he e' he' h
      rcases mem_insert.1 he with rfl | he <;> rcases mem_insert.1 he' with rfl | he'
      · rfl
      · exact absurd h.symm (hup e' he').2
      · exact absurd h (hup e he).2
      · exact hs e he e' he' h
    · intro e he e' he'
      rcases mem_insert.1 he with rfl | he <;> rcases mem_insert.1 he' with rfl | he'
      · exact hxy
      · exact ne_of_lt (hup e' he').1
      · exact (hlow e he).2
      · exact hd e he e' he'
  · rw [card_insert_of_notMem hnot]; omega
  · intro e he
    rcases mem_insert.1 he with rfl | he
    · exact hxL
    · exact hL'sub (hS'L e he)

/-- **Many pairs give a matching.** For a fixed ratio `q > 1`, a set `L` of lower endpoints of
`q`-pairs in `A` yields a matching of size at least `|L| / 3` (each pair meets at most two others). -/
theorem rich_of_pairs (A : Set ℕ) (h0 : 0 ∉ A) (q : ℚ) (hq : 1 < q) (L : Finset ℕ)
    (hL : ∀ x ∈ L, x ∈ A ∧ ∃ y ∈ A, (y : ℚ) = q * x) : Rich A q (L.card / 3) := by
  obtain ⟨S, hS, hc, -⟩ := rich_of_pairs_aux A h0 q hq _ L rfl hL
  exact ⟨S, hS, hc⟩

end Erdos786
