import Erdos786.Reduction

/-! # Step 7: assembling the steps into the main theorem

Each step enters as a hypothesis whose type is exactly the statement proved in its own file;
`Erdos786.Main` instantiates them. -/

open Finset Real Filter

namespace Erdos786

def LiftStmt : Prop := ∀ (A : _root_.Set ℕ), 0 ∉ A → ∀ (a : ℕ), a ∈ A → ∀ (qs : List ℚ),
  (a : ℚ) = qs.prod → (∀ q ∈ qs, Rich A q (2 * qs.length)) → Violation A

def PairsStmt : Prop := ∀ (A : _root_.Set ℕ), 0 ∉ A → ∀ (q : ℚ), 1 < q → ∀ (L : Finset ℕ),
  (∀ x ∈ L, x ∈ A ∧ ∃ y ∈ A, (y : ℚ) = q * x) → Rich A q (L.card / 3)

def HeavyStmt : Prop := ∀ (N : ℕ), 0 < N → ∀ (E : Finset ℕ), E ⊆ Icc 1 N → 32 * E.card ≤ N →
  ∀ (H : Finset ℕ), (∀ p ∈ H, p.Prime ∧ p ≤ N ∧ (N : ℝ) ≤ 16 * p * (E.filter (fun n => p ∣ n)).card) →
    ∑ p ∈ H, (1 : ℝ) / p ≤ 3072 * E.card / N

def SmoothStmt : Prop := ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ X : ℝ, y ^ 16 ≤ X → X ≤ y ^ 56 →
  c₀ * X ≤ (((Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card : ℝ)

def QPartStmt : Prop := ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime ∧ (q : ℝ) ≤ y) →
  ∀ T : ℕ, (((Icc 1 T).filter (fun z => y ^ 40 < (qPart Q z : ℝ))).card : ℝ) ≤ T / 10

def CoreStmt : Prop := ∀ (N p K : ℕ) (γ : ℝ), 0 < γ → ∀ (A : Finset ℕ), A ⊆ Icc 1 N →
  ∀ (Q : Finset ℕ), (∀ q ∈ Q, q.Prime) → p.Prime → p ∉ Q → 2 * p ≤ N → 1 ≤ K →
  (((Icc 1 (N / p)).filter (fun z => K < qPart Q z)).card : ℝ) ≤ (N / p : ℕ) / 10 →
  16 * p * ((Icc 1 N \ A).filter (fun n => p ∣ n)).card < N →
  (∀ k ∈ Nat.factoredNumbers Q, 1 ≤ k → k ≤ K →
    γ * p * k ≤ (((Icc 1 (p * k)).filter (fun m => m ∈ Nat.factoredNumbers Q ∧ p * k ≤ 2 * m)).card : ℝ)) →
  32 * ((Icc 1 N \ A).card : ℝ) ≤ γ * N →
  ∃ k m : ℕ, k ∈ Nat.factoredNumbers Q ∧ m ∈ Nat.factoredNumbers Q ∧ 1 ≤ k ∧ k ≤ K ∧
    p * k ≤ 2 * m ∧ m < p * k ∧
    ∃ U : Finset ℕ, ((N / p : ℕ) : ℝ) / (2 * K) ≤ U.card ∧ ∀ u ∈ U, m * u ∈ A ∧ p * k * u ∈ A

def WordsStmt : Prop := ∀ (A : _root_.Set ℕ) (M p₀ : ℕ) (good : ℕ → Prop),
  (∀ p, p.Prime → p ≤ p₀ → Rich A p M) →
  (∀ p, p.Prime → good p → p₀ < p → ∃ k m : ℕ, 1 ≤ k ∧ 1 ≤ m ∧
      (∀ q ∈ k.primeFactors, good q ∧ q ^ 16 ≤ p) ∧ (∀ q ∈ m.primeFactors, good q ∧ q ^ 16 ≤ p) ∧
      (k : ℝ) ^ 2 ≤ (p : ℝ) ^ 5 ∧ m ≤ p * k ∧ Rich A ((p * k : ℕ) / (m : ℚ)) M) →
  ∀ p, p.Prime → (good p ∨ p ≤ p₀) →
    ∃ w : List ℚ, w.prod = p ∧ (∀ q ∈ w, Rich A q M) ∧ (w.length : ℝ) ≤ 16 * (Real.log p) ^ 2


/-! ## Helper lemmas for `main_of` -/

lemma rich_mono {A : _root_.Set ℕ} {q : ℚ} {M M' : ℕ} (h : Rich A q M) (hM : M' ≤ M) :
    Rich A q M' := by
  obtain ⟨S, hS, hc⟩ := h
  exact ⟨S, hS, hM.trans hc⟩

/-- `p` is heavy for the exceptional set `E ⊆ [1, N]`. -/
def Heavy (N : ℕ) (E : Finset ℕ) (p : ℕ) : Prop :=
  (N : ℝ) ≤ 16 * p * (E.filter (fun n => p ∣ n)).card

lemma heavy_le {N : ℕ} {E : Finset ℕ} (hN : 0 < N) (hE : E ⊆ Icc 1 N) {p : ℕ}
    (h : Heavy N E p) : p ≤ N := by
  by_contra hp
  push Not at hp
  have h0 : E.filter (fun n => p ∣ n) = ∅ := by
    apply Finset.filter_false_of_mem
    intro n hn hd
    have := hE hn
    simp only [Finset.mem_Icc] at this
    have := Nat.le_of_dvd (by omega) hd
    omega
  unfold Heavy at h
  rw [h0] at h
  simp only [Finset.card_empty, Nat.cast_zero, mul_zero] at h
  have : (0:ℝ) < N := by exact_mod_cast hN
  linarith

open scoped Classical in
lemma heavy_sum (hHeavy : HeavyStmt) {N : ℕ} {E : Finset ℕ} (hN : 0 < N) (hE : E ⊆ Icc 1 N)
    (h32 : 32 * E.card ≤ N) (H : Finset ℕ) (hH : ∀ p ∈ H, p.Prime ∧ Heavy N E p) :
    ∑ p ∈ H, (1 : ℝ) / p ≤ 3072 * E.card / N :=
  hHeavy N hN E hE h32 H (fun p hp => ⟨(hH p hp).1, heavy_le hN hE (hH p hp).2, (hH p hp).2⟩)

lemma card_multiples_le (B q : ℕ) :
    (((Icc 1 B).filter (fun n => q ∣ n)).card : ℝ) ≤ (B : ℝ) / q := by
  have h : (Icc 1 B) = Ioc 0 B := by ext x; simp only [Finset.mem_Icc, Finset.mem_Ioc]; omega
  rw [h, Nat.Ioc_filter_dvd_card_eq_div]
  exact Nat.cast_div_le

open scoped Classical in
lemma heavy_count (hHeavy : HeavyStmt) {N : ℕ} {E : Finset ℕ} (hN : 0 < N) (hE : E ⊆ Icc 1 N)
    (h32 : 32 * E.card ≤ N) (B : ℕ) :
    (((Icc 1 B).filter (fun n => ∃ q ∈ n.primeFactors, Heavy N E q)).card : ℝ)
      ≤ B * (3072 * E.card / N) := by
  set H := (range (B+1)).filter (fun q => q.Prime ∧ Heavy N E q) with hHdef
  have hsub : (Icc 1 B).filter (fun n => ∃ q ∈ n.primeFactors, Heavy N E q) ⊆
      H.biUnion (fun q => (Icc 1 B).filter (fun n => q ∣ n)) := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨h1, h2⟩, q, hq, hqh⟩ := hn
    rw [Nat.mem_primeFactors] at hq
    simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc, hHdef, Finset.mem_range]
    exact ⟨q, ⟨by have := Nat.le_of_dvd (by omega) hq.2.1; omega, hq.1, hqh⟩, ⟨h1, h2⟩, hq.2.1⟩
  calc _ ≤ (((H.biUnion (fun q => (Icc 1 B).filter (fun n => q ∣ n)))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ ∑ q ∈ H, (((Icc 1 B).filter (fun n => q ∣ n)).card : ℝ) := by
        exact_mod_cast Finset.card_biUnion_le
    _ ≤ ∑ q ∈ H, (B : ℝ) * (1 / q) := by
        apply Finset.sum_le_sum; intro q _; rw [mul_one_div]; exact card_multiples_le B q
    _ = B * ∑ q ∈ H, (1:ℝ) / q := by rw [Finset.mul_sum]
    _ ≤ B * (3072 * E.card / N) := by
        apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg _)
        apply heavy_sum hHeavy hN hE h32
        intro p hp; simp only [hHdef, Finset.mem_filter] at hp; exact hp.2

open scoped Classical in
lemma smooth_good (hHeavy : HeavyStmt) {c₀ y₀ : ℝ}
    (hsm : ∀ y : ℝ, y₀ ≤ y → ∀ X : ℝ, y ^ 16 ≤ X → X ≤ y ^ 56 →
      c₀ * X ≤ (((Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter
        (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card : ℝ))
    {N : ℕ} {E : Finset ℕ} (hN : 0 < N) (hE : E ⊆ Icc 1 N) (h32 : 32 * E.card ≤ N)
    (hS : 3072 * (E.card : ℝ) / N ≤ c₀ / 2)
    (y : ℝ) (hy : y₀ ≤ y) (X : ℝ) (hX0 : 0 < X) (hX1 : y ^ 16 ≤ X) (hX2 : X ≤ y ^ 56) :
    c₀ / 2 * X ≤ (((Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter
      (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y ∧ ¬ Heavy N E p)).card : ℝ) := by
  have h1 := hsm y hy X hX1 hX2
  set S := (Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)
  set G := (Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter
    (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y ∧ ¬ Heavy N E p)
  set Bd := (Icc 1 ⌊X⌋₊).filter (fun n => ∃ q ∈ n.primeFactors, Heavy N E q)
  have hsub : S ⊆ G ∪ Bd := by
    intro n hn
    simp only [S, Finset.mem_filter, Finset.mem_Icc] at hn
    by_cases hh : ∃ q ∈ n.primeFactors, Heavy N E q
    · apply Finset.mem_union_right
      simp only [Bd, Finset.mem_filter, Finset.mem_Icc]
      refine ⟨⟨?_, hn.1.2⟩, hh⟩
      have : 0 < ⌈X / 2⌉₊ := Nat.ceil_pos.mpr (by positivity)
      omega
    · push Not at hh
      apply Finset.mem_union_left
      simp only [G, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨hn.1, fun p hp => ⟨hn.2 p hp, hh p hp⟩⟩
  have hc := Finset.card_le_card hsub
  have hu := Finset.card_union_le G Bd
  have hb := heavy_count hHeavy hN hE h32 ⌊X⌋₊
  have hfl : (⌊X⌋₊ : ℝ) ≤ X := Nat.floor_le hX0.le
  have hSn : 0 ≤ 3072 * (E.card : ℝ) / N := by positivity
  have : (⌊X⌋₊ : ℝ) * (3072 * E.card / N) ≤ X * (c₀ / 2) :=
    mul_le_mul hfl hS hSn hX0.le
  have hc' : (S.card : ℝ) ≤ G.card + Bd.card := by exact_mod_cast hc.trans hu
  nlinarith


lemma card_E_le {N : ℕ} {A : Finset ℕ} {η : ℝ} (hA : A ⊆ Icc 1 N)
    (hcard : (1 - η) * N ≤ A.card) : ((Icc 1 N \ A).card : ℝ) ≤ η * N := by
  have h1 : (Icc 1 N \ A).card = N - A.card := by
    rw [Finset.card_sdiff_of_subset hA, Nat.card_Icc]; omega
  have h2 : A.card ≤ N := by
    have := Finset.card_le_card hA
    rw [Nat.card_Icc] at this; omega
  rw [h1, Nat.cast_sub h2]
  linarith

lemma small_prime_count {N : ℕ} {A : Finset ℕ} (p : ℕ) (hp : 0 < p) :
    N / p ≤ ((Icc 1 (N / p)).filter (fun x => x ∈ A ∧ p * x ∈ A)).card
      + 2 * (Icc 1 N \ A).card := by
  set E := Icc 1 N \ A with hEdef
  set I := Icc 1 (N / p) with hI
  have hmul : ∀ x ∈ I, 1 ≤ x ∧ x ≤ N ∧ p * x ≤ N := by
    intro x hx
    simp only [hI, Finset.mem_Icc] at hx
    have h1 : x * p ≤ N := (Nat.le_div_iff_mul_le hp).mp hx.2
    refine ⟨hx.1, ?_, by linarith⟩
    nlinarith
  have hsub : I ⊆ I.filter (fun x => x ∈ A ∧ p * x ∈ A) ∪ (E ∪ I.filter (fun x => p * x ∉ A)) := by
    intro x hx
    obtain ⟨h1, h2, h3⟩ := hmul x hx
    simp only [Finset.mem_union, Finset.mem_filter, hEdef, Finset.mem_sdiff, Finset.mem_Icc]
    by_cases hxA : x ∈ A
    · by_cases hpx : p * x ∈ A
      · exact Or.inl ⟨hx, hxA, hpx⟩
      · exact Or.inr (Or.inr ⟨hx, hpx⟩)
    · exact Or.inr (Or.inl ⟨⟨h1, h2⟩, hxA⟩)
  have h2 : (I.filter (fun x => p * x ∉ A)).card ≤ E.card := by
    rw [← Finset.card_image_of_injective _ (fun a b h => Nat.eq_of_mul_eq_mul_left hp h)]
    apply Finset.card_le_card
    intro n hn
    simp only [Finset.mem_image, Finset.mem_filter] at hn
    obtain ⟨x, ⟨hx, hxA⟩, rfl⟩ := hn
    obtain ⟨h1, _, h3⟩ := hmul x hx
    simp only [hEdef, Finset.mem_sdiff, Finset.mem_Icc]
    exact ⟨⟨by nlinarith, h3⟩, hxA⟩
  have hc := Finset.card_le_card hsub
  have hu1 := Finset.card_union_le (I.filter (fun x => x ∈ A ∧ p * x ∈ A))
    (E ∪ I.filter (fun x => p * x ∉ A))
  have hu2 := Finset.card_union_le E (I.filter (fun x => p * x ∉ A))
  have hIc : I.card = N / p := by simp [hI]
  rw [hIc] at hc
  omega

lemma small_prime_rich (hPairs : PairsStmt) {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 N)
    (p p₀ M : ℕ) (hp : p.Prime) (hpp₀ : p ≤ p₀)
    (hbig : 3 * (M : ℝ) + 2 * (Icc 1 N \ A).card + 1 ≤ (N : ℝ) / p₀) :
    Rich (A : _root_.Set ℕ) (p : ℚ) M := by
  have h0 : (0 : ℕ) ∉ (A : _root_.Set ℕ) := by
    intro h; have := hA (Finset.mem_coe.mp h); simp at this
  have hp0 : 0 < p := hp.pos
  have hR := hPairs (A : _root_.Set ℕ) h0 (p : ℚ) (by exact_mod_cast hp.one_lt)
    ((Icc 1 (N / p)).filter (fun x => x ∈ A ∧ p * x ∈ A)) (by
      intro x hx
      simp only [Finset.mem_filter] at hx
      exact ⟨Finset.mem_coe.mpr hx.2.1, p * x, Finset.mem_coe.mpr hx.2.2, by push_cast; ring⟩)
  apply rich_mono hR
  have hc := small_prime_count (N := N) (A := A) p hp0
  have hdiv : N / p₀ ≤ N / p := Nat.div_le_div_left hpp₀ hp0
  have hlt := Nat.lt_mul_div_succ N (lt_of_lt_of_le hp0 hpp₀)
  have hp₀r : (0 : ℝ) < p₀ := by exact_mod_cast lt_of_lt_of_le hp0 hpp₀
  have hlt' : (N : ℝ) / p₀ < (N / p₀ : ℕ) + 1 := by
    rw [div_lt_iff₀ hp₀r]
    have : (N : ℝ) < (p₀ : ℝ) * ((N / p₀ : ℕ) + 1) := by exact_mod_cast hlt
    linarith
  have hreal : 3 * (M : ℝ) ≤ (((Icc 1 (N / p)).filter (fun x => x ∈ A ∧ p * x ∈ A)).card : ℝ) := by
    have h1 : ((N / p : ℕ) : ℝ) ≤ (((Icc 1 (N / p)).filter (fun x => x ∈ A ∧ p * x ∈ A)).card : ℝ)
      + 2 * (Icc 1 N \ A).card := by exact_mod_cast hc
    have h2 : ((N / p₀ : ℕ) : ℝ) ≤ ((N / p : ℕ) : ℝ) := by exact_mod_cast hdiv
    linarith
  have : 3 * M ≤ ((Icc 1 (N / p)).filter (fun x => x ∈ A ∧ p * x ∈ A)).card := by
    exact_mod_cast hreal
  omega


open scoped Classical in
lemma replacement (hPairs : PairsStmt) (hHeavy : HeavyStmt) (hCore : CoreStmt) {c₀ y₀ y₂ : ℝ}
    (hc₀ : 0 < c₀)
    (hsm : ∀ y : ℝ, y₀ ≤ y → ∀ X : ℝ, y ^ 16 ≤ X → X ≤ y ^ 56 →
      c₀ * X ≤ (((Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter
        (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card : ℝ))
    (hqp : ∀ y : ℝ, y₂ ≤ y → ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime ∧ (q : ℝ) ≤ y) →
      ∀ T : ℕ, (((Icc 1 T).filter (fun z => y ^ 40 < (qPart Q z : ℝ))).card : ℝ) ≤ T / 10)
    {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 N) (hN : 0 < N)
    (h32 : 32 * (Icc 1 N \ A).card ≤ N)
    (hS : 3072 * ((Icc 1 N \ A).card : ℝ) / N ≤ c₀ / 2)
    (hdef : 32 * ((Icc 1 N \ A).card : ℝ) ≤ c₀ / 2 * N)
    (p : ℕ) (hp : p.Prime) (hnh : ¬ Heavy N (Icc 1 N \ A) p) (h2p : 2 * p ≤ N)
    (y : ℝ) (hyp : y ^ 16 = p) (hy0 : y₀ ≤ y) (hy2 : y₂ ≤ y) (hy1 : 2 ≤ y) :
    ∃ k m : ℕ, 1 ≤ k ∧ 1 ≤ m ∧
      (∀ q ∈ k.primeFactors, q.Prime ∧ ¬ Heavy N (Icc 1 N \ A) q ∧ (q : ℝ) ≤ y) ∧
      (∀ q ∈ m.primeFactors, q.Prime ∧ ¬ Heavy N (Icc 1 N \ A) q ∧ (q : ℝ) ≤ y) ∧
      (k : ℝ) ^ 2 ≤ (p : ℝ) ^ 5 ∧ m ≤ p * k ∧
      ∃ c : ℕ, ((N / p : ℕ) : ℝ) / (2 * y ^ 40) ≤ c ∧
        Rich (A : _root_.Set ℕ) (((p * k : ℕ) : ℚ) / (m : ℚ)) (c / 3) := by
  have hE : Icc 1 N \ A ⊆ Icc 1 N := Finset.sdiff_subset
  have hyn : 0 ≤ y := by linarith
  set K := ⌊y ^ 40⌋₊ with hK
  set Q := (range (⌊y⌋₊ + 1)).filter (fun q => q.Prime ∧ ¬ Heavy N (Icc 1 N \ A) q) with hQ
  have hQmem : ∀ q ∈ Q, q.Prime ∧ ¬ Heavy N (Icc 1 N \ A) q ∧ (q:ℝ) ≤ y := by
    intro q hq
    simp only [hQ, Finset.mem_filter, Finset.mem_range] at hq
    refine ⟨hq.2.1, hq.2.2, ?_⟩
    have : q ≤ ⌊y⌋₊ := by omega
    exact (Nat.le_floor_iff hyn).mp this
  have hpy : (p:ℝ) = y ^ 16 := hyp.symm
  have hy40 : (1:ℝ) ≤ y ^ 40 := one_le_pow₀ (by linarith)
  have hK1 : 1 ≤ K := Nat.le_floor (by simpa using hy40)
  have hKle : (K:ℝ) ≤ y ^ 40 := Nat.floor_le (by positivity)
  have hpQ : p ∉ Q := by
    intro h
    have h1 := (hQmem p h).2.2
    rw [hpy] at h1
    have : y < y ^ 16 := lt_self_pow₀ (by linarith) (by norm_num)
    linarith
  have htail : (((Icc 1 (N / p)).filter (fun z => K < qPart Q z)).card : ℝ)
      ≤ (N / p : ℕ) / 10 := by
    have h := hqp y hy2 Q (fun q hq => ⟨(hQmem q hq).1, (hQmem q hq).2.2⟩) (N / p)
    refine le_trans ?_ h
    have hsub : (Icc 1 (N / p)).filter (fun z => K < qPart Q z) ⊆
        (Icc 1 (N / p)).filter (fun z => y ^ 40 < (qPart Q z : ℝ)) := by
      intro z hz
      simp only [Finset.mem_filter] at hz ⊢
      refine ⟨hz.1, ?_⟩
      have h1 : ((K + 1 : ℕ) : ℝ) ≤ (qPart Q z : ℝ) := by exact_mod_cast hz.2
      have h2 : y ^ 40 < (K : ℝ) + 1 := Nat.lt_floor_add_one _
      push_cast at h1
      linarith
    exact_mod_cast Finset.card_le_card hsub
  have hnh' : 16 * p * ((Icc 1 N \ A).filter (fun n => p ∣ n)).card < N := by
    unfold Heavy at hnh
    push Not at hnh
    exact_mod_cast hnh
  have hres : ∀ k ∈ Nat.factoredNumbers Q, 1 ≤ k → k ≤ K →
      c₀ / 2 * p * k ≤ (((Icc 1 (p * k)).filter
        (fun m => m ∈ Nat.factoredNumbers Q ∧ p * k ≤ 2 * m)).card : ℝ) := by
    intro k _ hk1 hkK
    have hkr : (k:ℝ) ≤ y ^ 40 := le_trans (by exact_mod_cast hkK) hKle
    have hk1r : (1:ℝ) ≤ k := by exact_mod_cast hk1
    set X : ℝ := ((p * k : ℕ) : ℝ) with hX
    have hXe : X = y ^ 16 * k := by rw [hX]; push_cast; rw [hpy]
    have hy16 : 0 < y ^ 16 := by positivity
    have h := smooth_good hHeavy hsm hN hE h32 hS y hy0 X (by rw [hXe]; positivity)
      (by rw [hXe]; nlinarith)
      (by rw [hXe]; calc y ^ 16 * k ≤ y ^ 16 * y ^ 40 := by gcongr
                  _ = y ^ 56 := by ring)
    have hfl : ⌊X⌋₊ = p * k := by rw [hX]; exact Nat.floor_natCast _
    rw [hfl] at h
    have hX0 : 0 < X := by rw [hXe]; positivity
    calc c₀ / 2 * p * k = c₀ / 2 * X := by rw [hX]; push_cast; ring
      _ ≤ _ := h
      _ ≤ _ := by
        apply Nat.cast_le.mpr
        apply Finset.card_le_card
        intro n hn
        simp only [Finset.mem_filter, Finset.mem_Icc] at hn ⊢
        obtain ⟨⟨hn1, hn2⟩, hn3⟩ := hn
        have hc1 : 0 < ⌈X / 2⌉₊ := Nat.ceil_pos.mpr (by positivity)
        have hn0 : n ≠ 0 := by omega
        refine ⟨⟨by omega, hn2⟩, ?_, ?_⟩
        · rw [Nat.mem_factoredNumbers']
          intro q hq hqn
          have hqf : q ∈ n.primeFactors := Nat.mem_primeFactors.mpr ⟨hq, hqn, hn0⟩
          obtain ⟨hqy, hqh⟩ := hn3 q hqf
          simp only [hQ, Finset.mem_filter, Finset.mem_range]
          exact ⟨by have := Nat.le_floor hqy; omega, hq, hqh⟩
        · have h1 : X / 2 ≤ (n : ℝ) := Nat.ceil_le.mp hn1
          have h2 : ((p * k : ℕ) : ℝ) ≤ ((2 * n : ℕ) : ℝ) := by
            push_cast; rw [hX] at h1; push_cast at h1; linarith
          exact_mod_cast h2
  obtain ⟨k, m, hkQ, hmQ, hk1, hkK, _, hmpk, U, hU, hUA⟩ :=
    hCore N p K (c₀ / 2) (by positivity) A hA Q (fun q hq => (hQmem q hq).1) hp hpQ h2p hK1
      htail hnh' hres hdef
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr (Nat.mem_factoredNumbers.mp hmQ).1
  have hfac : ∀ j ∈ Nat.factoredNumbers Q, ∀ q ∈ j.primeFactors,
      q.Prime ∧ ¬ Heavy N (Icc 1 N \ A) q ∧ (q : ℝ) ≤ y := by
    intro j hj q hq
    exact hQmem q (Nat.mem_factoredNumbers'.mp hj q (Nat.prime_of_mem_primeFactors hq)
      (Nat.dvd_of_mem_primeFactors hq))
  have hkr : (k:ℝ) ≤ y ^ 40 := le_trans (by exact_mod_cast hkK) hKle
  have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg _
  refine ⟨k, m, hk1, hm1, hfac k hkQ, hfac m hmQ, ?_, hmpk.le, U.card, ?_, ?_⟩
  · rw [hpy]
    calc (k:ℝ) ^ 2 ≤ (y ^ 40) ^ 2 := by gcongr
      _ = (y ^ 16) ^ 5 := by ring
  · have hK0 : (0:ℝ) < K := by exact_mod_cast hK1
    refine le_trans ?_ hU
    apply div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity)
    linarith
  · have h0 : (0 : ℕ) ∉ (A : _root_.Set ℕ) := by
      intro h; have := hA (Finset.mem_coe.mp h); simp at this
    have hinj : Function.Injective (fun u => m * u) :=
      fun a b h => Nat.eq_of_mul_eq_mul_left (by omega) h
    rw [← Finset.card_image_of_injective U hinj]
    apply hPairs (A : _root_.Set ℕ) h0
    · rw [one_lt_div (by exact_mod_cast hm1)]
      exact_mod_cast hmpk
    · intro x hx
      simp only [Finset.mem_image] at hx
      obtain ⟨u, hu, rfl⟩ := hx
      refine ⟨Finset.mem_coe.mpr (hUA u hu).1, p * k * u, Finset.mem_coe.mpr (hUA u hu).2, ?_⟩
      have hm0 : (m : ℚ) ≠ 0 := by exact_mod_cast (show m ≠ 0 by omega)
      push_cast
      field_simp


open scoped Classical in
lemma exists_good (hHeavy : HeavyStmt) {c₀ y₀ : ℝ}
    (hsm : ∀ y : ℝ, y₀ ≤ y → ∀ X : ℝ, y ^ 16 ≤ X → X ≤ y ^ 56 →
      c₀ * X ≤ (((Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter
        (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card : ℝ))
    {N : ℕ} {A : Finset ℕ} (hN : 0 < N)
    (h32 : 32 * (Icc 1 N \ A).card ≤ N)
    (hS : 3072 * ((Icc 1 N \ A).card : ℝ) / N ≤ c₀ / 2)
    (hsmall : ((Icc 1 N \ A).card : ℝ) < c₀ / 2 * N)
    (P : ℝ) (hP : y₀ ≤ P) (hP1 : P ^ 16 ≤ N) (hP2 : (N : ℝ) ≤ P ^ 56) :
    ∃ a ∈ A, ∀ q ∈ a.primeFactors, (q : ℝ) ≤ P ∧ ¬ Heavy N (Icc 1 N \ A) q := by
  have hE : Icc 1 N \ A ⊆ Icc 1 N := Finset.sdiff_subset
  have hN0 : (0:ℝ) < N := by exact_mod_cast hN
  have h := smooth_good hHeavy hsm hN hE h32 hS P hP (N : ℝ) hN0 hP1 hP2
  rw [Nat.floor_natCast] at h
  set G := (Icc ⌈(N : ℝ) / 2⌉₊ N).filter
    (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ P ∧ ¬ Heavy N (Icc 1 N \ A) p) with hG
  by_contra hcon
  push Not at hcon
  have hsub : G ⊆ Icc 1 N \ A := by
    intro n hn
    have hn' := hn
    simp only [hG, Finset.mem_filter, Finset.mem_Icc] at hn'
    have hc1 : 0 < ⌈(N : ℝ) / 2⌉₊ := Nat.ceil_pos.mpr (by positivity)
    rw [Finset.mem_sdiff, Finset.mem_Icc]
    refine ⟨⟨by omega, hn'.1.2⟩, fun hnA => ?_⟩
    obtain ⟨q, hq, hq'⟩ := hcon n hnA
    exact (hn'.2 q hq).2 (hq' (hn'.2 q hq).1)
  have := Finset.card_le_card hsub
  have : (G.card : ℝ) ≤ (Icc 1 N \ A).card := by exact_mod_cast this
  linarith

lemma word_concat (l : List ℕ) (W : ℕ → List ℚ) (c : ℝ)
    (h : ∀ q ∈ l, 1 ≤ q ∧ (W q).prod = q ∧ ((W q).length : ℝ) ≤ 16 * Real.log q ^ 2 ∧
      Real.log q ≤ c) :
    (l.flatMap W).prod = ((l.prod : ℕ) : ℚ) ∧
      ((l.flatMap W).length : ℝ) ≤ 16 * c * Real.log (l.prod : ℕ) := by
  induction l with
  | nil => simp
  | cons q l ih =>
    have hq := h q (by simp)
    obtain ⟨ih1, ih2⟩ := ih (fun r hr => h r (by simp [hr]))
    have hl0 : l.prod ≠ 0 := by
      rw [Ne, List.prod_eq_zero_iff]
      intro h0
      have := (h 0 (by simp [h0])).1
      omega
    have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast (show q ≠ 0 by omega)
    have hl0' : ((l.prod : ℕ) : ℝ) ≠ 0 := by exact_mod_cast hl0
    have hlogq : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hq.1)
    refine ⟨?_, ?_⟩
    · rw [List.flatMap_cons, List.prod_append, hq.2.1, ih1, List.prod_cons]
      push_cast; ring
    · rw [List.flatMap_cons, List.length_append, List.prod_cons, Nat.cast_mul,
        Real.log_mul hq0 hl0']
      push_cast
      have h3 := hq.2.2.1
      have h4 : 16 * Real.log q ^ 2 ≤ 16 * c * Real.log q := by
        have := mul_le_mul_of_nonneg_left hq.2.2.2 hlogq
        nlinarith
      push_cast at ih2
      linarith

lemma eventually_B (C : ℝ) : ∀ᶠ N : ℕ in atTop,
    ∃ B : ℝ, 0 ≤ B ∧ B ^ 64 = (N : ℝ) ∧ C ≤ B ∧ Real.log N ^ 2 ≤ B := by
  have h1 : Tendsto (fun x : ℝ => x ^ ((64:ℕ):ℝ)⁻¹) atTop atTop :=
    tendsto_rpow_atTop (by positivity)
  have h2 := (isLittleO_log_rpow_rpow_atTop (2:ℝ) (s := ((64:ℕ):ℝ)⁻¹) (by positivity)).bound
    one_pos
  have h3 := (h1.eventually_ge_atTop C).and (h2.and (eventually_ge_atTop 0))
  filter_upwards [tendsto_natCast_atTop_atTop.eventually h3] with N hN
  obtain ⟨hC, hlo, h0⟩ := hN
  refine ⟨_, Real.rpow_nonneg h0 _, Real.rpow_inv_natCast_pow h0 (by norm_num), hC, ?_⟩
  rw [Real.norm_eq_abs, Real.norm_eq_abs, one_mul, Real.rpow_two,
    abs_of_nonneg (Real.rpow_nonneg h0 _)] at hlo
  exact (le_abs_self _).trans hlo

lemma poly_big {B M u v : ℝ} (hB : 2 ≤ B) (hM : M ≤ B + 1) (hu0 : 0 ≤ u)
    (hu : u ≤ B ^ 7) (hv : v ≤ B ^ 2) : 6 * M * u + v ≤ B ^ 64 := by
  have hB1 : 1 ≤ B := by linarith
  have h7 : 0 ≤ B ^ 7 := by positivity
  have h1 : 6 * M * u ≤ 6 * (B + 1) * B ^ 7 := by
    have := mul_le_mul hM hu hu0 (by linarith)
    nlinarith
  have h2 : B ^ 2 ≤ B ^ 8 := pow_le_pow_right₀ hB1 (by norm_num)
  have h3 : 16 ≤ B ^ 4 := by
    have : (2:ℝ) ^ 4 ≤ B ^ 4 := by gcongr
    norm_num at this; linarith
  have h4 : B ^ 12 ≤ B ^ 64 := pow_le_pow_right₀ hB1 (by norm_num)
  have h5 : B ^ 12 = B ^ 4 * B ^ 8 := by ring
  have h6 : B * B ^ 7 = B ^ 8 := by ring
  have h8 : 0 ≤ B ^ 8 := by positivity
  nlinarith

lemma main_small (hPairs : PairsStmt) {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 N)
    {p₀ M : ℕ} {η B : ℝ} (hp₀pos : (0:ℝ) < p₀) (hB0 : 0 ≤ B) (hB1 : 1 ≤ B)
    (hBp₀ : 14 * (p₀:ℝ) ≤ B) (hNr : (N:ℝ) = B ^ 64)
    (hEc : ((Icc 1 N \ A).card : ℝ) ≤ η * N) (hη3 : η ≤ 1 / (4 * p₀))
    (hM2 : (M:ℝ) ≤ B + 1) :
    ∀ p, p.Prime → p ≤ p₀ → Rich (A : _root_.Set ℕ) p M := by
  intro p hp hpp
  have hNr0 : (0:ℝ) ≤ N := Nat.cast_nonneg _
  apply small_prime_rich hPairs hA p p₀ M hp hpp
  rw [le_div_iff₀ hp₀pos]
  have h1 : 2 * ((Icc 1 N \ A).card:ℝ) * p₀ ≤ N / 2 := by
    have h4 : η * (4 * p₀) ≤ 1 := by rwa [le_div_iff₀ (by positivity)] at hη3
    have h5 : ((Icc 1 N \ A).card:ℝ) * p₀ ≤ η * N * p₀ :=
      mul_le_mul_of_nonneg_right hEc hp₀pos.le
    have h6 : η * (4 * p₀) * N ≤ 1 * N := mul_le_mul_of_nonneg_right h4 hNr0
    nlinarith
  have h2 : (3 * M + 1) * (p₀:ℝ) ≤ N / 2 := by
    have h3 : (3 * M + 1) * (p₀:ℝ) ≤ (3 * B + 4) * p₀ :=
      mul_le_mul_of_nonneg_right (by linarith) hp₀pos.le
    have h4 : (3 * B + 4) * (p₀:ℝ) ≤ B * B / 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hBp₀) hB0]
    have h5 : B ^ 2 ≤ B ^ 64 := pow_le_pow_right₀ hB1 (by norm_num)
    rw [hNr]; nlinarith
  nlinarith

lemma main_repl (hPairs : PairsStmt) (hHeavy : HeavyStmt) (hCore : CoreStmt) {c₀ y₀ y₂ : ℝ}
    (hc₀ : 0 < c₀)
    (hsm : ∀ y : ℝ, y₀ ≤ y → ∀ X : ℝ, y ^ 16 ≤ X → X ≤ y ^ 56 →
      c₀ * X ≤ (((Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter
        (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card : ℝ))
    (hqp : ∀ y : ℝ, y₂ ≤ y → ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime ∧ (q : ℝ) ≤ y) →
      ∀ T : ℕ, (((Icc 1 T).filter (fun z => y ^ 40 < (qPart Q z : ℝ))).card : ℝ) ≤ T / 10)
    {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 N) (hN : 0 < N)
    (h32 : 32 * (Icc 1 N \ A).card ≤ N)
    (hS : 3072 * ((Icc 1 N \ A).card : ℝ) / N ≤ c₀ / 2)
    (hdef : 32 * ((Icc 1 N \ A).card : ℝ) ≤ c₀ / 2 * N)
    {ys B : ℝ} {p₀ M : ℕ} (hys1 : y₀ ≤ ys) (hys2 : y₂ ≤ ys) (hys3 : 2 ≤ ys)
    (hp₀ : ys ^ 16 ≤ p₀) (hB0 : 0 ≤ B) (hB2 : 2 ≤ B) (hNr : (N:ℝ) = B ^ 64)
    (hM2 : (M:ℝ) ≤ B + 1) :
    ∀ p, p.Prime → (p.Prime ∧ ¬ Heavy N (Icc 1 N \ A) p ∧ (p:ℝ) ≤ B ^ 2) → p₀ < p →
      ∃ k m : ℕ, 1 ≤ k ∧ 1 ≤ m ∧
      (∀ q ∈ k.primeFactors,
        (q.Prime ∧ ¬ Heavy N (Icc 1 N \ A) q ∧ (q:ℝ) ≤ B ^ 2) ∧ q ^ 16 ≤ p) ∧
      (∀ q ∈ m.primeFactors,
        (q.Prime ∧ ¬ Heavy N (Icc 1 N \ A) q ∧ (q:ℝ) ≤ B ^ 2) ∧ q ^ 16 ≤ p) ∧
      (k : ℝ) ^ 2 ≤ (p : ℝ) ^ 5 ∧ m ≤ p * k ∧
      Rich (A : _root_.Set ℕ) ((p * k : ℕ) / (m : ℚ)) M := by
  intro p hp hgp hpp₀
  obtain ⟨_, hnh, hpB⟩ := hgp
  have hB1 : 1 ≤ B := by linarith
  have hp0 : (0:ℝ) ≤ p := Nat.cast_nonneg _
  obtain ⟨y, hy0, hyp⟩ : ∃ y : ℝ, 0 ≤ y ∧ y ^ 16 = p :=
    ⟨(p:ℝ) ^ ((16:ℕ):ℝ)⁻¹, Real.rpow_nonneg hp0 _, Real.rpow_inv_natCast_pow hp0 (by norm_num)⟩
  have hysy : ys ≤ y := by
    have h1 : ys ^ 16 ≤ p := by
      have : (p₀ : ℝ) < p := by exact_mod_cast hpp₀
      linarith
    rw [← hyp] at h1
    exact (pow_le_pow_iff_left₀ (by linarith) hy0 (by norm_num)).mp h1
  have h2p : 2 * p ≤ N := by
    have : 2 * (p:ℝ) ≤ N := by
      rw [hNr]
      have h5 : B ^ 3 ≤ B ^ 64 := pow_le_pow_right₀ hB1 (by norm_num)
      have h6 : 2 * B ^ 2 ≤ B ^ 3 := by
        have : B ^ 3 = B * B ^ 2 := by ring
        rw [this]; exact mul_le_mul_of_nonneg_right hB2 (sq_nonneg B)
      linarith
    exact_mod_cast this
  obtain ⟨k, m, hk1, hm1, hkf, hmf, hk2, hmk, c, hc, hR⟩ :=
    replacement hPairs hHeavy hCore hc₀ hsm hqp hA hN h32 hS hdef p hp hnh h2p y hyp
      (hys1.trans hysy) (hys2.trans hysy) (hys3.trans hysy)
  have hy1 : 1 ≤ y := by linarith
  have hyp' : y ≤ (p:ℝ) := by rw [← hyp]; exact le_self_pow₀ hy1 (by norm_num)
  have hfac : ∀ j : ℕ,
      (∀ q ∈ j.primeFactors, q.Prime ∧ ¬ Heavy N (Icc 1 N \ A) q ∧ (q : ℝ) ≤ y) →
      ∀ q ∈ j.primeFactors,
        (q.Prime ∧ ¬ Heavy N (Icc 1 N \ A) q ∧ (q:ℝ) ≤ B ^ 2) ∧ q ^ 16 ≤ p := by
    intro j hj q hq
    obtain ⟨h1, h2, h3⟩ := hj q hq
    refine ⟨⟨h1, h2, by linarith⟩, ?_⟩
    have : (q:ℝ) ^ 16 ≤ p := by
      rw [← hyp]; exact pow_le_pow_left₀ (Nat.cast_nonneg _) h3 16
    exact_mod_cast this
  refine ⟨k, m, hk1, hm1, hfac k hkf, hfac m hmf, hk2, hmk, rich_mono hR ?_⟩
  have hstep : 3 * (M:ℝ) ≤ c := by
    have hq' := Nat.lt_mul_div_succ N hp.pos
    have hq'r : (N:ℝ) < p * ((N / p : ℕ) + 1) := by exact_mod_cast hq'
    have hy8 : y ^ 8 ≤ B := by
      have : (y ^ 8) ^ 2 ≤ B ^ 2 := by
        rw [← pow_mul, hyp]; exact hpB
      exact (pow_le_pow_iff_left₀ (by positivity) hB0 (by norm_num)).mp this
    have hu : y ^ 56 ≤ B ^ 7 := by
      calc y ^ 56 = (y ^ 8) ^ 7 := by ring
        _ ≤ B ^ 7 := pow_le_pow_left₀ (by positivity) hy8 7
    have hM0 : (0:ℝ) ≤ M := Nat.cast_nonneg _
    have hpoly := poly_big hB2 hM2 (by positivity : (0:ℝ) ≤ y ^ 56) hu hpB
    have hp0' : (0:ℝ) < p := by exact_mod_cast hp.pos
    have hy40 : 0 < y ^ 40 := by positivity
    have hkey : 3 * (M:ℝ) * (2 * y ^ 40) ≤ ((N / p : ℕ) : ℝ) := by
      have h6 : (p:ℝ) * (3 * M * (2 * y ^ 40)) = 6 * M * y ^ 56 := by
        rw [← hyp]; ring
      have : (p:ℝ) * (3 * M * (2 * y ^ 40)) < p * ((N / p : ℕ) : ℝ) := by
        rw [h6]; linarith
      exact le_of_lt (lt_of_mul_lt_mul_left this hp0'.le)
    calc 3 * (M:ℝ) ≤ ((N / p : ℕ) : ℝ) / (2 * y ^ 40) := by
          rw [le_div_iff₀ (by positivity)]; exact hkey
      _ ≤ c := hc
  have : 3 * M ≤ c := by exact_mod_cast hstep
  omega

lemma main_final (hLift : LiftStmt) (hHeavy : HeavyStmt) {c₀ y₀ : ℝ}
    (hsm : ∀ y : ℝ, y₀ ≤ y → ∀ X : ℝ, y ^ 16 ≤ X → X ≤ y ^ 56 →
      c₀ * X ≤ (((Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter
        (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card : ℝ))
    {N : ℕ} {A : Finset ℕ} (hA : A ⊆ Icc 1 N) (hN : 0 < N)
    (h32 : 32 * (Icc 1 N \ A).card ≤ N)
    (hS : 3072 * ((Icc 1 N \ A).card : ℝ) / N ≤ c₀ / 2)
    (hEsmall : ((Icc 1 N \ A).card : ℝ) < c₀ / 2 * N)
    {B : ℝ} {p₀ M : ℕ} (hB1 : 1 ≤ B) (hy₀B : y₀ ≤ B ^ 2) (hNr : (N:ℝ) = B ^ 64)
    (hM1 : Real.log N ^ 2 ≤ M)
    (hW : ∀ p, p.Prime → ((p.Prime ∧ ¬ Heavy N (Icc 1 N \ A) p ∧ (p:ℝ) ≤ B ^ 2) ∨ p ≤ p₀) →
      ∃ w : List ℚ, w.prod = p ∧ (∀ q ∈ w, Rich (A : _root_.Set ℕ) q M) ∧
        (w.length : ℝ) ≤ 16 * (Real.log p) ^ 2) :
    Violation (A : _root_.Set ℕ) := by
  have h0 : (0 : ℕ) ∉ (A : _root_.Set ℕ) := by
    intro h; have := hA (Finset.mem_coe.mp h); simp at this
  obtain ⟨a, haA, ha⟩ := exists_good hHeavy hsm hN h32 hS hEsmall (B ^ 2) hy₀B
    (by rw [hNr, ← pow_mul]; exact pow_le_pow_right₀ hB1 (by norm_num))
    (by rw [hNr, ← pow_mul]; exact pow_le_pow_right₀ hB1 (by norm_num))
  have ha0 : a ≠ 0 := by have := hA haA; simp at this; omega
  have hWq : ∀ q, ∃ w : List ℚ, q ∈ a.primeFactorsList → (w.prod = q ∧
      (∀ r ∈ w, Rich (A : _root_.Set ℕ) r M) ∧ (w.length : ℝ) ≤ 16 * Real.log q ^ 2) := by
    intro q
    by_cases hq : q ∈ a.primeFactorsList
    · have hqp := Nat.prime_of_mem_primeFactorsList hq
      have hqf : q ∈ a.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hqp, Nat.dvd_of_mem_primeFactorsList hq, ha0⟩
      obtain ⟨h1, h2⟩ := ha q hqf
      obtain ⟨w, hw1, hw2, hw3⟩ := hW q hqp (Or.inl ⟨hqp, h2, h1⟩)
      exact ⟨w, fun _ => ⟨hw1, hw2, hw3⟩⟩
    · exact ⟨[], fun h => absurd h hq⟩
  choose W hW' using hWq
  have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB1
  have hcw := word_concat a.primeFactorsList W (Real.log (B ^ 2)) (fun q hq => by
      obtain ⟨h1, _, h3⟩ := hW' q hq
      have hqp := Nat.prime_of_mem_primeFactorsList hq
      have hqf : q ∈ a.primeFactors :=
        Nat.mem_primeFactors.mpr ⟨hqp, Nat.dvd_of_mem_primeFactorsList hq, ha0⟩
      refine ⟨hqp.one_lt.le, h1, h3, ?_⟩
      exact Real.log_le_log (by exact_mod_cast hqp.pos) (ha q hqf).1)
  rw [Nat.prod_primeFactorsList ha0] at hcw
  obtain ⟨hprod, hlen⟩ := hcw
  have haN : a ≤ N := (Finset.mem_Icc.mp (hA haA)).2
  have ha1 : (1:ℝ) ≤ a := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr ha0
  have hloga : Real.log a ≤ Real.log N :=
    Real.log_le_log (by linarith) (by exact_mod_cast haN)
  have hlogN : Real.log N = 64 * Real.log B := by rw [hNr, Real.log_pow]; norm_num
  have hlogB2 : Real.log (B ^ 2) = 2 * Real.log B := by rw [Real.log_pow]; norm_num
  have h2t : 2 * ((a.primeFactorsList.flatMap W).length : ℝ) ≤ M := by
    rw [hlogB2] at hlen
    have : 16 * (2 * Real.log B) * Real.log a ≤ 16 * (2 * Real.log B) * Real.log N :=
      mul_le_mul_of_nonneg_left hloga (by positivity)
    rw [hlogN] at this hM1
    nlinarith
  have h2t' : 2 * (a.primeFactorsList.flatMap W).length ≤ M := by exact_mod_cast h2t
  apply hLift (A : _root_.Set ℕ) h0 a (Finset.mem_coe.mpr haA) _ hprod.symm
  intro r hr
  obtain ⟨q, hq, hrq⟩ := List.mem_flatMap.mp hr
  exact rich_mono ((hW' q hq).2.1 r hrq) h2t'

theorem main_of (hLift : LiftStmt) (hPairs : PairsStmt) (hHeavy : HeavyStmt) (hSmooth : SmoothStmt)
    (hQPart : QPartStmt) (hCore : CoreStmt) (hWords : WordsStmt) : MainStatement := by
  obtain ⟨c₀, hc₀, y₁, hsm⟩ := hSmooth
  obtain ⟨y₂, hqp⟩ := hQPart
  obtain ⟨ys, hys1, hys2, hys3⟩ : ∃ ys : ℝ, y₁ ≤ ys ∧ y₂ ≤ ys ∧ 2 ≤ ys :=
    ⟨max y₁ (max y₂ 2), le_max_left _ _, (le_max_left _ _).trans (le_max_right _ _),
      (le_max_right _ _).trans (le_max_right _ _)⟩
  obtain ⟨p₀, hp₀pos, hp₀⟩ : ∃ p₀ : ℕ, (0:ℝ) < p₀ ∧ ys ^ 16 ≤ p₀ :=
    ⟨⌈ys ^ 16⌉₊ + 1, by positivity, by push_cast; linarith [Nat.le_ceil (ys ^ 16)]⟩
  obtain ⟨η, hη0, hη1, hη2, hη3⟩ : ∃ η : ℝ, 0 < η ∧ η ≤ c₀ / 6144 ∧ η ≤ 1 / 32 ∧
      η ≤ 1 / (4 * p₀) :=
    ⟨min (min (c₀ / 6144) (1/32)) (1 / (4 * p₀)),
      lt_min (lt_min (by positivity) (by norm_num)) (by positivity),
      (min_le_left _ _).trans (min_le_left _ _), (min_le_left _ _).trans (min_le_right _ _),
      min_le_right _ _⟩
  refine ⟨η, hη0, ?_⟩
  filter_upwards [eventually_B (|y₁| + 14 * p₀ + 2)] with N hB
  obtain ⟨B, hB0, hBN, hBC, hlog⟩ := hB
  intro A hA hcard
  have hy₁B : y₁ ≤ B := by have := le_abs_self y₁; linarith
  have hB2 : 2 ≤ B := by have := abs_nonneg y₁; linarith
  have hBp₀ : 14 * (p₀:ℝ) ≤ B := by have := abs_nonneg y₁; linarith
  have hB1 : 1 ≤ B := by linarith
  have hNr : (N:ℝ) = B ^ 64 := hBN.symm
  have hNr0 : (0:ℝ) < N := by rw [hNr]; positivity
  have hN : 0 < N := by exact_mod_cast hNr0
  have hEc : ((Icc 1 N \ A).card : ℝ) ≤ η * N := card_E_le hA hcard
  have hE0 : (0:ℝ) ≤ (Icc 1 N \ A).card := Nat.cast_nonneg _
  have hηN1 : η * N ≤ c₀ / 6144 * N := mul_le_mul_of_nonneg_right hη1 hNr0.le
  have hηN2 : η * N ≤ 1 / 32 * N := mul_le_mul_of_nonneg_right hη2 hNr0.le
  have hc₀N : 0 < c₀ * N := mul_pos hc₀ hNr0
  have h32r : 32 * ((Icc 1 N \ A).card : ℝ) ≤ N := by linarith
  have h32 : 32 * (Icc 1 N \ A).card ≤ N := by exact_mod_cast h32r
  have hS : 3072 * ((Icc 1 N \ A).card : ℝ) / N ≤ c₀ / 2 := by
    rw [div_le_iff₀ hNr0]; linarith
  have hdef : 32 * ((Icc 1 N \ A).card : ℝ) ≤ c₀ / 2 * N := by linarith
  have hEsmall : ((Icc 1 N \ A).card : ℝ) < c₀ / 2 * N := by linarith
  have hM1 : Real.log N ^ 2 ≤ (⌈Real.log N ^ 2⌉₊ : ℕ) := Nat.le_ceil _
  have hM2 : ((⌈Real.log N ^ 2⌉₊ : ℕ) : ℝ) ≤ B + 1 := by
    have := Nat.ceil_lt_add_one (sq_nonneg (Real.log N)); linarith
  have hsmall := main_small hPairs hA hp₀pos hB0 hB1 hBp₀ hNr hEc hη3 hM2
  have hrepl := main_repl hPairs hHeavy hCore hc₀ hsm hqp hA hN h32 hS hdef hys1 hys2 hys3 hp₀
    hB0 hB2 hNr hM2
  have hW := hWords (A : _root_.Set ℕ) ⌈Real.log N ^ 2⌉₊ p₀
    (fun q => q.Prime ∧ ¬ Heavy N (Icc 1 N \ A) q ∧ (q:ℝ) ≤ B ^ 2) hsmall hrepl
  exact main_final hLift hHeavy hsm hA hN h32 hS hEsmall hB1 (by nlinarith) hNr hM1 hW

end Erdos786
