import Erdos786.Defs

/-! # Step 1: heavily deleted primes have small reciprocal sum (Turán–Kubilius) -/

open Finset

namespace Erdos786

lemma card_Icc_filter_dvd (N d : ℕ) : ((Icc 1 N).filter (fun n => d ∣ n)).card = N / d := by
  have : Icc 1 N = Ioc 0 N := by ext x; simp; omega
  rw [this, Nat.Ioc_filter_dvd_card_eq_div]

lemma card_Icc_filter_dvd_le (N d : ℕ) :
    ((((Icc 1 N).filter (fun n => d ∣ n)).card : ℕ) : ℝ) ≤ (N : ℝ) / d := by
  rw [card_Icc_filter_dvd]; exact Nat.cast_div_le

lemma card_Icc_filter_dvd_ge (N d : ℕ) (hd : 0 < d) :
    (N : ℝ) / d - 1 ≤ ((((Icc 1 N).filter (fun n => d ∣ n)).card : ℕ) : ℝ) := by
  rw [card_Icc_filter_dvd]
  have h := Nat.lt_div_mul_add (a := N) hd
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  have h' : (N : ℝ) < ((N / d : ℕ) : ℝ) * d + d := by exact_mod_cast h
  rw [div_sub_one hd'.ne', div_le_iff₀ hd']
  linarith

/-- Number of elements of `H` dividing `n`, as a real number. -/
noncomputable def omegaH (H : Finset ℕ) (n : ℕ) : ℝ := ∑ p ∈ H, if p ∣ n then (1 : ℝ) else 0

lemma sum_omegaH (H : Finset ℕ) (s : Finset ℕ) :
    ∑ n ∈ s, omegaH H n = ∑ p ∈ H, (((s.filter (fun n => p ∣ n)).card : ℕ) : ℝ) := by
  unfold omegaH
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_boole]

lemma sum_omegaH_sq_le (N : ℕ) (H : Finset ℕ) (hH : ∀ p ∈ H, p.Prime) :
    ∑ n ∈ Icc 1 N, omegaH H n ^ 2 ≤
      N * (∑ p ∈ H, (1 : ℝ) / p) + N * (∑ p ∈ H, (1 : ℝ) / p) ^ 2 := by
  have expand : ∀ n, omegaH H n ^ 2 =
      ∑ p ∈ H, ∑ q ∈ H, (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0) := by
    intro n
    unfold omegaH
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    by_cases hp : p ∣ n <;> by_cases hq : q ∣ n <;> simp [hp, hq]
  simp_rw [expand]
  rw [Finset.sum_comm]
  have pair : ∀ p ∈ H, ∀ q ∈ H,
      ∑ n ∈ Icc 1 N, (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0) ≤
        (N : ℝ) / (p * q) + (if p = q then (N : ℝ) / p else 0) := by
    intro p hp q hq
    rw [Finset.sum_boole]
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hH p hp).pos
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (hH q hq).pos
    by_cases hpq : p = q
    · subst hpq
      simp only [and_self, if_true]
      have := card_Icc_filter_dvd_le N p
      have : (0 : ℝ) ≤ (N : ℝ) / (p * p) := by positivity
      linarith
    · rw [if_neg hpq]
      have hcop : Nat.Coprime p q := (Nat.coprime_primes (hH p hp) (hH q hq)).2 hpq
      have : (Icc 1 N).filter (fun n => p ∣ n ∧ q ∣ n) =
          (Icc 1 N).filter (fun n => p * q ∣ n) := by
        ext n
        simp only [Finset.mem_filter]
        constructor
        · rintro ⟨h1, h2, h3⟩; exact ⟨h1, hcop.mul_dvd_of_dvd_of_dvd h2 h3⟩
        · rintro ⟨h1, h2⟩
          exact ⟨h1, (Nat.dvd_mul_right p q).trans h2, (Nat.dvd_mul_left q p).trans h2⟩
      rw [this]
      have := card_Icc_filter_dvd_le N (p * q)
      push_cast at this
      linarith
  calc ∑ p ∈ H, ∑ n ∈ Icc 1 N, ∑ q ∈ H, (if p ∣ n ∧ q ∣ n then (1 : ℝ) else 0)
      ≤ ∑ p ∈ H, ∑ q ∈ H, ((N : ℝ) / (p * q) + (if p = q then (N : ℝ) / p else 0)) := by
        refine Finset.sum_le_sum fun p hp => ?_
        rw [Finset.sum_comm]
        exact Finset.sum_le_sum fun q hq => pair p hp q hq
    _ = N * (∑ p ∈ H, (1 : ℝ) / p) + N * (∑ p ∈ H, (1 : ℝ) / p) ^ 2 := by
        simp_rw [Finset.sum_add_distrib, Finset.sum_ite_eq, sq, Finset.sum_mul_sum,
          Finset.mul_sum]
        rw [add_comm]
        congr 1
        · refine Finset.sum_congr rfl fun p hp => ?_
          rw [if_pos hp]; ring
        · refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
          field_simp

/-- Paper Lemma 6.2. `E ⊆ [1,N]`, `|E| ≤ N/32`; every `p ∈ H` is a prime `≤ N` with
`|E ∩ pℕ| ≥ N/(16p)`. Then `∑_{p ∈ H} 1/p ≤ 3072 |E| / N`. -/
theorem heavy_recip_sum_le (N : ℕ) (hN : 0 < N) (E : Finset ℕ) (hE : E ⊆ Icc 1 N)
    (hD : 32 * E.card ≤ N) (H : Finset ℕ)
    (hH : ∀ p ∈ H, p.Prime ∧ p ≤ N ∧ (N : ℝ) ≤ 16 * p * (E.filter (fun n => p ∣ n)).card) :
    ∑ p ∈ H, (1 : ℝ) / p ≤ 3072 * E.card / N := by
  set S : ℝ := ∑ p ∈ H, (1 : ℝ) / p with hSdef
  have hHp : ∀ p ∈ H, p.Prime := fun p hp => (hH p hp).1
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun p _ => by positivity
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  -- |H| ≤ N
  have hm : (H.card : ℝ) ≤ N := by
    have hsub : H ⊆ Icc 1 N := fun p hp => by
      simp only [Finset.mem_Icc]; exact ⟨(hH p hp).1.one_le, (hH p hp).2.1⟩
    have := Finset.card_le_card hsub
    simp only [Nat.card_Icc, add_tsub_cancel_right] at this
    exact_mod_cast this
  -- first moment
  have hB : (N : ℝ) * S - H.card ≤ ∑ n ∈ Icc 1 N, omegaH H n := by
    rw [sum_omegaH, hSdef, Finset.mul_sum, Finset.card_eq_sum_ones, Nat.cast_sum,
      ← Finset.sum_sub_distrib]
    refine Finset.sum_le_sum fun p hp => ?_
    have := card_Icc_filter_dvd_ge N p (hHp p hp).pos
    push_cast
    rw [mul_one_div]
    exact this
  -- second moment
  have hA := sum_omegaH_sq_le N H hHp
  rw [← hSdef] at hA
  -- variance over [1,N]
  have hV : ∑ n ∈ Icc 1 N, (omegaH H n - S) ^ 2 ≤ 3 * N * S := by
    have e : ∀ n, (omegaH H n - S) ^ 2 = omegaH H n ^ 2 - 2 * S * omegaH H n + S ^ 2 := by
      intro n; ring
    simp_rw [e, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum,
      Finset.sum_const, Nat.card_Icc, add_tsub_cancel_right, nsmul_eq_mul]
    nlinarith [mul_le_mul_of_nonneg_left hB (by linarith : (0 : ℝ) ≤ 2 * S),
      mul_le_mul_of_nonneg_left hm hS0]
  -- restrict to E
  have hVE : ∑ n ∈ E, (omegaH H n - S) ^ 2 ≤ 3 * N * S :=
    le_trans (Finset.sum_le_sum_of_subset_of_nonneg hE fun n _ _ => sq_nonneg _) hV
  have hCS := sq_sum_le_card_mul_sum_sq (s := E) (f := fun n => omegaH H n - S)
  -- heaviness
  have hheavy : (N : ℝ) * S / 16 ≤ ∑ n ∈ E, omegaH H n := by
    rw [sum_omegaH, hSdef, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_le_sum fun p hp => ?_
    have h3 := (hH p hp).2.2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hHp p hp).pos
    rw [div_le_iff₀ (by norm_num : (0 : ℝ) < 16), mul_one_div, div_le_iff₀ hp0]
    linarith
  have hX : ∑ n ∈ E, (omegaH H n - S) = ∑ n ∈ E, omegaH H n - E.card * S := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, nsmul_eq_mul]
  have hDr : 32 * (E.card : ℝ) ≤ N := by exact_mod_cast hD
  have hD0 : (0 : ℝ) ≤ E.card := Nat.cast_nonneg _
  have hXlow : (N : ℝ) * S / 32 ≤ ∑ n ∈ E, (omegaH H n - S) := by
    rw [hX]; nlinarith
  have hsq : ((N : ℝ) * S / 32) ^ 2 ≤ E.card * (3 * N * S) := by
    have h1 : ((N : ℝ) * S / 32) ^ 2 ≤ (∑ n ∈ E, (omegaH H n - S)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hXlow 2
    have h2 := mul_le_mul_of_nonneg_left hVE hD0
    linarith
  rw [le_div_iff₀ hNr]
  rcases hS0.eq_or_lt with h0 | hpos
  · rw [← h0, zero_mul]; positivity
  · have : S * ((N : ℝ) * (S * N) / 1024) ≤ S * (3 * E.card * N) := by nlinarith
    have h4 := le_of_mul_le_mul_left this hpos
    have h5 : (S * N) * N ≤ (3072 * E.card) * N := by nlinarith
    exact le_of_mul_le_mul_right h5 hNr

end Erdos786
