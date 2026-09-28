import Erdos786.Defs

/-! # From the main counting theorem to the formal-conjectures statements -/

open Finset Filter Topology

namespace Erdos786

/-- The shape of the main theorem (`Erdos786.main`). -/
def MainStatement : Prop :=
  ∃ η : ℝ, 0 < η ∧ ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Icc 1 N →
    (1 - η) * N ≤ A.card → Violation (A : _root_.Set ℕ)

lemma violation_mono {A B : _root_.Set ℕ} (h : A ⊆ B) (hA : Violation A) : Violation B := by
  obtain ⟨s, t, hs, ht, hp, hc⟩ := hA
  exact ⟨s, t, hs.trans h, ht.trans h, hp, hc⟩

theorem not_partII_of_main (hmain : MainStatement) : ¬ PartIIStatement := by
  obtain ⟨η, hη, hev⟩ := hmain
  rintro ⟨A, f, hf, hA⟩
  have hf0 : Tendsto f atTop (𝓝 0) := by
    have := hf.tendsto_div_nhds_zero
    simpa using this
  have hsmall : ∀ᶠ N : ℕ in atTop, f N ≤ η / 2 :=
    (hf0.eventually (gt_mem_nhds (by linarith : (0:ℝ) < η / 2))).mono fun _ h => h.le
  have hbig : ∀ᶠ N : ℕ in atTop, 2 / η ≤ (N : ℝ) :=
    tendsto_natCast_atTop_atTop.eventually_ge_atTop _
  have hev' := (tendsto_add_atTop_nat 1).eventually hev
  obtain ⟨N, hN1, hN2, hN3⟩ := (hev'.and (hsmall.and hbig)).exists
  obtain ⟨hsub, hcard, hP⟩ := hA N
  have hfin : (A N).Finite := (Set.finite_Icc 1 (N + 1)).subset hsub
  set F := hfin.toFinset with hF
  have hFsub : F ⊆ Icc 1 (N + 1) := by
    intro x hx
    have : x ∈ A N := hfin.mem_toFinset.mp hx
    simpa using hsub this
  have hFcard : (F.card : ℝ) = (A N).ncard := by
    rw [Set.ncard_eq_toFinset_card _ hfin]
  have hNpos : (0 : ℝ) < N := by
    have : (0:ℝ) < 2 / η := by positivity
    linarith
  have hkey : (1 - η) * ((N + 1 : ℕ) : ℝ) ≤ F.card := by
    rw [hFcard]
    have h1 : (1 - f N) * N ≤ (A N).ncard := hcard
    have h2 : (1 - η / 2) * (N : ℝ) ≤ (1 - f N) * N := by
      apply mul_le_mul_of_nonneg_right _ hNpos.le; linarith
    have h3 : (1 - η) * ((N + 1 : ℕ) : ℝ) ≤ (1 - η / 2) * N := by
      push_cast
      have : 2 ≤ η * N := by
        have := (div_le_iff₀ hη).mp hN3; linarith
      nlinarith
    linarith
  have hviol := hN1 F hFsub hkey
  have hcoe : ((F : Set ℕ)) = A N := by simp [hF]
  rw [hcoe] at hviol
  exact (isMulCardSet_iff_not_violation _).mp hP hviol

theorem not_partI_of_main (hmain : MainStatement) : ¬ PartIStatement := by
  classical
  obtain ⟨η, hη, hev⟩ := hmain
  intro h
  set ε : ℝ := min η 1 / 2 with hε
  have hε0 : 0 < ε := by positivity
  have hε1 : ε ≤ 1 := by
    have : min η 1 ≤ 1 := min_le_right _ _
    linarith
  have hεη : ε ≤ η / 2 := by
    have : min η 1 ≤ η := min_le_left _ _
    linarith
  obtain ⟨A, δ, h0, hδ, hd, hP⟩ := h ε hε0 hε1
  have hlt : ∀ᶠ b : ℕ in atTop, 1 - ε < A.partialDensity Set.univ b :=
    hd.eventually (lt_mem_nhds hδ)
  have hlt' := (tendsto_add_atTop_nat 1).eventually hlt
  obtain ⟨N, hN1, hN2⟩ := (hev.and hlt').exists
  set F : Finset ℕ := (Finset.range (N + 1)).filter (· ∈ A) with hF
  have hFA : ((F : Set ℕ)) ⊆ A := by
    intro x hx
    simp only [hF, Finset.coe_filter, Set.mem_ofPred_eq] at hx
    exact hx.2
  have hFsub : F ⊆ Icc 1 N := by
    intro x hx
    simp only [hF, Finset.mem_filter, Finset.mem_range] at hx
    have hx0 : x ≠ 0 := by rintro rfl; exact h0 hx.2
    simp only [Finset.mem_Icc]; omega
  have hcardF : ((A ∩ Set.univ) ∩ Set.Iio (N + 1)).ncard = F.card := by
    rw [← Set.ncard_coe_finset]
    congr 1
    ext x
    simp [hF, and_comm]
  have hden : (Set.univ ∩ Set.Iio (N + 1)).ncard = N + 1 := by
    simp [Set.ncard_eq_toFinset_card']
  have hkey : (1 - η) * (N : ℝ) ≤ F.card := by
    have h2 := hN2
    simp only [Set.partialDensity, hcardF, hden] at h2
    have hpos : (0 : ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    rw [lt_div_iff₀ hpos] at h2
    push_cast at h2
    have : (1 - η) * (N : ℝ) ≤ (1 - ε) * (N + 1) := by nlinarith
    linarith
  have hviol := violation_mono hFA (hN1 F hFsub hkey)
  exact (isMulCardSet_iff_not_violation _).mp hP hviol

end Erdos786
