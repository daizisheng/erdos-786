import Erdos786.Defs
import Erdos786.Vendor.Mertens

/-! # Step 2: an explicit positive proportion of smooth numbers in `[X/2, X]`

Uses Mertens' second theorem with explicit error (`Mertens.E₂p.abs_le` from PrimeNumberTheoremAnd)
in place of Rosser–Schoenfeld; the constant `c₀` is therefore not `e^{-1400}` but some positive
constant, which is all the main theorem needs. -/

open Finset Real
open scoped Classical

namespace Erdos786

/-- The constant in the explicit Mertens error bound. -/
noncomputable def mC : ℝ := log 4 + 6 + Mertens.E₁

lemma mC_nonneg : 0 ≤ mC := by
  unfold mC
  have := Mertens.E₁.nonneg
  have : 0 < log (4:ℝ) := log_pos (by norm_num)
  linarith

/-- Threshold on `log y`. -/
noncomputable def mK : ℝ := max 100 (3552 * mC)

lemma sum_filter_prime_split (A B : ℝ) (hAB : A ≤ B) :
    ∑ p ∈ Ioc 0 ⌊B⌋₊ with p.Prime, (1:ℝ) / p =
      (∑ p ∈ Ioc 0 ⌊A⌋₊ with p.Prime, (1:ℝ) / p) +
        ∑ p ∈ Ioc ⌊A⌋₊ ⌊B⌋₊ with p.Prime, (1:ℝ) / p := by
  simp only [Finset.sum_filter]
  rw [Finset.sum_Ioc_consecutive _ (Nat.zero_le _) (Nat.floor_mono hAB)]

/-- Mertens on a short multiplicative interval. -/
lemma mertens_interval (l L : ℝ) (hl : mK ≤ l) (h16 : 16 * l ≤ L) (h56 : L ≤ 56 * l) :
    (1:ℝ) / 222 ≤ ∑ p ∈ Ioc ⌊exp ((L - l) / 112)⌋₊ ⌊exp ((L - l / 2) / 112)⌋₊ with p.Prime,
      (1:ℝ) / p := by
  set A := exp ((L - l) / 112) with hA
  set B := exp ((L - l / 2) / 112) with hB
  have hl100 : 100 ≤ l := le_trans (le_max_left _ _) hl
  have hlC : 3552 * mC ≤ l := le_trans (le_max_right _ _) hl
  have hlogA : log A = (L - l) / 112 := log_exp _
  have hlogB : log B = (L - l / 2) / 112 := log_exp _
  have hlA8 : l / 8 ≤ log A := by rw [hlogA]; linarith
  have hlAB : log A ≤ log B := by rw [hlogA, hlogB]; linarith
  have hAB : A ≤ B := exp_le_exp.mpr (by linarith)
  have hA2 : 2 ≤ A := by
    have := add_one_le_exp ((L - l) / 112)
    rw [← hA] at this; linarith
  have hB2 : 2 ≤ B := le_trans hA2 hAB
  have hsplit := sum_filter_prime_split A B hAB
  rw [Mertens.sum_prime_div_eq B, Mertens.sum_prime_div_eq A] at hsplit
  have hEA := Mertens.E₂p.abs_le hA2
  have hEB := Mertens.E₂p.abs_le hB2
  have hposA : 0 < log A := by linarith
  have hposB : 0 < log B := by linarith
  have hEA' : |Mertens.E₂p A| ≤ 8 * mC / l := by
    refine le_trans hEA ?_
    rw [div_le_div_iff₀ hposA (by linarith)]
    have := mC_nonneg
    unfold mC at this ⊢
    nlinarith
  have hEB' : |Mertens.E₂p B| ≤ 8 * mC / l := by
    refine le_trans hEB ?_
    rw [div_le_div_iff₀ hposB (by linarith)]
    have := mC_nonneg
    unfold mC at this ⊢
    nlinarith
  have hsmall : 16 * mC / l ≤ 1 / 222 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]; linarith
  have hlog : (1:ℝ) / 111 ≤ log (log B) - log (log A) := by
    rw [← log_div hposB.ne' hposA.ne']
    refine le_trans ?_ (one_sub_inv_le_log_of_pos (div_pos hposB hposA))
    rw [inv_div, le_sub_comm, div_le_iff₀ hposB, hlogA, hlogB]
    linarith
  have h1 := (abs_le.mp hEA').1
  have h2 := (abs_le.mp hEB').1
  have h3 := (abs_le.mp hEA').2
  have : 16 * mC / l = 8 * mC / l + 8 * mC / l := by ring
  linarith


lemma card_Icc_half_ge (t : ℝ) (ht : 6 ≤ t) :
    t / 3 ≤ ((Icc ⌈t / 2⌉₊ ⌊t⌋₊).card : ℝ) := by
  rw [Nat.card_Icc]
  have h1 : (⌈t / 2⌉₊ : ℝ) < t / 2 + 1 := Nat.ceil_lt_add_one (by linarith)
  have h2 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
  have hle : ⌈t / 2⌉₊ ≤ ⌊t⌋₊ + 1 := by
    have : (⌈t / 2⌉₊ : ℝ) ≤ (⌊t⌋₊ : ℝ) + 1 := by linarith
    exact_mod_cast this
  rw [Nat.cast_sub hle]
  push_cast
  linarith

lemma card_big_primeFactors (n : ℕ) (hn : n ≠ 0) (A X : ℝ) (hA : 1 < A) (hnX : (n : ℝ) ≤ X)
    (hXA : X ≤ A ^ 448) : (n.primeFactors.filter (fun p : ℕ => A < (p : ℝ))).card ≤ 448 := by
  set F := n.primeFactors.filter (fun p : ℕ => A < (p : ℝ))
  have hdvd : ∏ p ∈ F, p ∣ n :=
    (Finset.prod_dvd_prod_of_subset F n.primeFactors id (Finset.filter_subset _ _)).trans
      (Nat.prod_primeFactors_dvd n)
  have hle : ∏ p ∈ F, p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) hdvd
  have hpow : A ^ F.card ≤ ((∏ p ∈ F, p : ℕ) : ℝ) := by
    rw [← Finset.prod_const, Nat.cast_prod]
    refine Finset.prod_le_prod (fun _ _ => by linarith) (fun p hp => ?_)
    exact le_of_lt (Finset.mem_filter.mp hp).2
  have : A ^ F.card ≤ A ^ 448 := by
    refine le_trans hpow (le_trans ?_ (le_trans hnX hXA))
    exact_mod_cast hle
  exact (pow_le_pow_iff_right₀ hA).mp this

/-- The core counting estimate, in logarithmic coordinates. -/
lemma main_count (y X : ℝ) (hy : 0 < y) (hX : 0 < X) (hl : mK ≤ log y)
    (h16 : 16 * log y ≤ log X) (h56 : log X ≤ 56 * log y) :
    X / 3 * ((1:ℝ) / 222) ^ 112 ≤ (448 ^ 112 : ℝ) *
      (((Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card : ℝ) := by
  set l := log y with hl_def
  set L := log X with hL_def
  set A := exp ((L - l) / 112) with hA
  set B := exp ((L - l / 2) / 112) with hB
  set S := (Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)
  set I := (Ioc ⌊A⌋₊ ⌊B⌋₊).filter Nat.Prime with hI
  have hmert : (1:ℝ) / 222 ≤ ∑ p ∈ I, (1:ℝ) / p := mertens_interval l L hl h16 h56
  have hl100 : 100 ≤ l := le_trans (le_max_left _ _) hl
  have hyexp : exp l = y := exp_log hy
  have hXexp : exp L = X := exp_log hX
  have hA112 : A ^ 112 = X / y := by
    rw [hA, ← exp_nat_mul, ← hyexp, ← hXexp, ← exp_sub]; congr 1; push_cast; ring
  have hB112 : B ^ 112 = X / exp (l / 2) := by
    rw [hB, ← exp_nat_mul, ← hXexp, ← exp_sub]; congr 1; push_cast; ring
  have hA448 : X ≤ A ^ 448 := by
    rw [hA, ← exp_nat_mul, ← hXexp]; apply exp_le_exp.mpr; push_cast; linarith
  have hBy : B ≤ y := by rw [← hyexp, hB]; apply exp_le_exp.mpr; linarith
  have hA1 : 1 < A := by rw [hA]; linarith [add_one_le_exp ((L - l) / 112)]
  have hsq6 : 6 ≤ exp (l / 2) := by have := add_one_le_exp (l / 2); linarith
  have hsqpos : 0 < exp (l / 2) := exp_pos _
  -- tuples
  set T := Fintype.piFinset (fun _ : Fin 112 => I) with hT
  let Qn : (Fin 112 → ℕ) → ℕ := fun q => ∏ i, q i
  have hQcast : ∀ q, (Qn q : ℝ) = ∏ i, (q i : ℝ) := fun q => Nat.cast_prod _ _
  have hmemI : ∀ q ∈ T, ∀ i, q i ∈ I := fun q hq i => Fintype.mem_piFinset.mp hq i
  have hqA : ∀ q ∈ T, ∀ i, A < (q i : ℝ) := fun q hq i => by
    have := (Finset.mem_filter.mp (hmemI q hq i)).1
    exact Nat.lt_of_floor_lt (Finset.mem_Ioc.mp this).1
  have hqB : ∀ q ∈ T, ∀ i, (q i : ℝ) ≤ B := fun q hq i => by
    have := (Finset.mem_filter.mp (hmemI q hq i)).1
    exact (Nat.le_floor_iff (by positivity)).mp (Finset.mem_Ioc.mp this).2
  have hqprime : ∀ q ∈ T, ∀ i, (q i).Prime := fun q hq i => (Finset.mem_filter.mp (hmemI q hq i)).2
  have hQlow : ∀ q ∈ T, X / y < (Qn q : ℝ) := fun q hq => by
    rw [← hA112, hQcast]
    have := Finset.prod_lt_prod_of_nonempty (s := (Finset.univ : Finset (Fin 112)))
      (f := fun _ => A) (g := fun i => (q i : ℝ)) (fun _ _ => by linarith)
      (fun i _ => hqA q hq i) Finset.univ_nonempty
    rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  have hQup : ∀ q ∈ T, (Qn q : ℝ) ≤ X / exp (l / 2) := fun q hq => by
    rw [← hB112, hQcast]
    have := Finset.prod_le_prod (s := (Finset.univ : Finset (Fin 112)))
      (f := fun i => (q i : ℝ)) (g := fun _ => B) (fun _ _ => by positivity)
      (fun i _ => hqB q hq i)
    rwa [Finset.prod_const, Finset.card_univ, Fintype.card_fin] at this
  have hQpos : ∀ q ∈ T, 0 < (Qn q : ℝ) := fun q hq => lt_trans (by positivity) (hQlow q hq)
  have htlow : ∀ q ∈ T, exp (l / 2) ≤ X / (Qn q : ℝ) := fun q hq => by
    rw [le_div_iff₀ (hQpos q hq)]
    have := hQup q hq
    rw [le_div_iff₀ hsqpos] at this; linarith
  have htup : ∀ q ∈ T, X / (Qn q : ℝ) < y := fun q hq => by
    rw [div_lt_iff₀ (hQpos q hq)]
    have := hQlow q hq
    rw [div_lt_iff₀ hy] at this; linarith
  -- pairs
  let R : (Fin 112 → ℕ) → Finset ℕ := fun q => Icc ⌈X / (Qn q : ℝ) / 2⌉₊ ⌊X / (Qn q : ℝ)⌋₊
  set P := T.sigma R with hP
  let f : (Σ _ : Fin 112 → ℕ, ℕ) → ℕ := fun x => x.2 * Qn x.1
  have hmaps : ∀ x ∈ P, f x ∈ S := by
    rintro ⟨q, r⟩ hx
    rw [Finset.mem_sigma] at hx
    obtain ⟨hq, hr⟩ := hx
    have hr' := Finset.mem_Icc.mp hr
    have hQ := hQpos q hq
    have ht6 : 6 ≤ X / (Qn q : ℝ) := le_trans hsq6 (htlow q hq)
    have hrlow : X / (Qn q : ℝ) / 2 ≤ r := Nat.ceil_le.mp hr'.1
    have hrup : (r : ℝ) ≤ X / (Qn q : ℝ) := (Nat.le_floor_iff (by linarith)).mp hr'.2
    have hrpos : 0 < r := by
      have : (0:ℝ) < r := by linarith
      exact_mod_cast this
    show r * Qn q ∈ S
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · apply Nat.ceil_le.mpr
      push_cast
      rw [div_div, div_le_iff₀ (by linarith)] at hrlow
      linarith
    · apply Nat.le_floor
      push_cast
      rw [le_div_iff₀ hQ] at hrup
      linarith
    · intro p hp
      have hpp := Nat.prime_of_mem_primeFactors hp
      have hpd := Nat.dvd_of_mem_primeFactors hp
      rcases (Nat.Prime.dvd_mul hpp).mp hpd with h | h
      · have : p ≤ r := Nat.le_of_dvd hrpos h
        have : (p : ℝ) ≤ r := by exact_mod_cast this
        linarith [htup q hq]
      · obtain ⟨i, -, hi⟩ := (Prime.dvd_finsetProd_iff hpp.prime _).mp h
        have : p ≤ q i := Nat.le_of_dvd (hqprime q hq i).pos hi
        have : (p : ℝ) ≤ q i := by exact_mod_cast this
        linarith [hqB q hq i]
  have hfib : ∀ n ∈ S, (P.filter (fun x => f x = n)).card ≤ 448 ^ 112 := by
    intro n hn
    have hn' := Finset.mem_Icc.mp (Finset.mem_filter.mp hn).1
    have hnX : (n : ℝ) ≤ X := (Nat.le_floor_iff hX.le).mp hn'.2
    have hn0 : n ≠ 0 := by
      intro h0
      have : ⌈X / 2⌉₊ = 0 := by omega
      rw [Nat.ceil_eq_zero] at this; linarith
    set F := n.primeFactors.filter (fun p : ℕ => A < (p : ℝ))
    have hF := card_big_primeFactors n hn0 A X hA1 hnX hA448
    calc (P.filter (fun x => f x = n)).card
        ≤ (Fintype.piFinset (fun _ : Fin 112 => F)).card := by
          refine Finset.card_le_card_of_injOn (fun x => x.1) ?_ ?_
          · rintro ⟨q, r⟩ hx
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_sigma] at hx
            obtain ⟨⟨hq, hr⟩, hfx⟩ := hx
            rw [Finset.mem_coe, Fintype.mem_piFinset]
            intro i
            rw [Finset.mem_filter, Nat.mem_primeFactors]
            refine ⟨⟨hqprime q hq i, ?_, hn0⟩, hqA q hq i⟩
            rw [← hfx]
            exact Dvd.dvd.mul_left (Finset.dvd_prod_of_mem _ (Finset.mem_univ i)) _
          · rintro ⟨q, r⟩ hx ⟨q', r'⟩ hx' (hqq : q = q')
            subst hqq
            rw [Finset.mem_coe, Finset.mem_filter, Finset.mem_sigma] at hx hx'
            have hQ := hQpos q hx.1.1
            have hQn : 0 < Qn q := by exact_mod_cast hQ
            have : r * Qn q = r' * Qn q := by
              have h1 := hx.2; have h2 := hx'.2
              simp only [f] at h1 h2; rw [h1, h2]
            have := Nat.eq_of_mul_eq_mul_right hQn this
            subst this; rfl
      _ = F.card ^ 112 := Fintype.card_piFinset_const F 112
      _ ≤ 448 ^ 112 := Nat.pow_le_pow_left hF 112
  have hkey : P.card ≤ 448 ^ 112 * S.card :=
    Finset.card_le_mul_card_image_of_maps_to hmaps _ hfib
  have hlower : X / 3 * ((1:ℝ) / 222) ^ 112 ≤ (P.card : ℝ) := by
    rw [hP, Finset.card_sigma, Nat.cast_sum]
    calc X / 3 * ((1:ℝ) / 222) ^ 112
        ≤ X / 3 * (∑ p ∈ I, (1:ℝ) / p) ^ 112 := by
          gcongr
      _ = X / 3 * ∏ _i : Fin 112, ∑ p ∈ I, (1:ℝ) / p := by
          rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = ∑ q ∈ T, X / 3 * ∏ i, (1:ℝ) / (q i) := by
          rw [Finset.prod_univ_sum, Finset.mul_sum]
      _ = ∑ q ∈ T, X / (Qn q : ℝ) / 3 := by
          refine Finset.sum_congr rfl (fun q hq => ?_)
          rw [hQcast, Finset.prod_div_distrib, Finset.prod_const_one]
          ring
      _ ≤ ∑ q ∈ T, ((R q).card : ℝ) := by
          refine Finset.sum_le_sum (fun q hq => ?_)
          exact card_Icc_half_ge _ (le_trans hsq6 (htlow q hq))
  have : (P.card : ℝ) ≤ 448 ^ 112 * (S.card : ℝ) := by exact_mod_cast hkey
  linarith

/-- Paper Lemma 6.3 (with an unspecified constant). -/
theorem smooth_count : ∃ c₀ : ℝ, 0 < c₀ ∧ ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ X : ℝ, y ^ 16 ≤ X → X ≤ y ^ 56 →
    c₀ * X ≤ (((Icc ⌈X / 2⌉₊ ⌊X⌋₊).filter (fun n => ∀ p ∈ n.primeFactors, ((p : ℕ) : ℝ) ≤ y)).card : ℝ) := by
  refine ⟨((1:ℝ) / 222) ^ 112 / 3 / 448 ^ 112, by positivity, exp mK, ?_⟩
  intro y hy X hX1 hX2
  have hypos : 0 < y := lt_of_lt_of_le (exp_pos _) hy
  have hl : mK ≤ log y := by rw [← log_exp mK]; exact log_le_log (exp_pos _) hy
  have hXpos : 0 < X := lt_of_lt_of_le (by positivity) hX1
  have h16 : 16 * log y ≤ log X := by
    have := log_le_log (by positivity) hX1
    rwa [log_pow] at this
  have h56 : log X ≤ 56 * log y := by
    have := log_le_log hXpos hX2
    rwa [log_pow] at this
  have key := main_count y X hypos hXpos hl (by exact_mod_cast h16) (by exact_mod_cast h56)
  have h448 : (0:ℝ) < 448 ^ 112 := by positivity
  calc ((1:ℝ) / 222) ^ 112 / 3 / 448 ^ 112 * X = X / 3 * ((1:ℝ) / 222) ^ 112 / 448 ^ 112 := by
        ring
    _ ≤ _ := by rw [div_le_iff₀ h448]; linarith

end Erdos786
