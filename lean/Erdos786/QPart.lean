import Erdos786.Defs
import Erdos786.Vendor.Mertens

/-! # Step 3: the `Q`-part of a random integer is usually small (Chebyshev + Markov) -/

open Finset Real
open scoped Classical

namespace Erdos786

lemma sum_factorization_Icc_eq (q : ℕ) (T : ℕ) :
    ∑ z ∈ Icc 1 T, z.factorization q = (T.factorial).factorization q := by
  induction T with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_Icc_succ_top (by omega), ih, Nat.factorial_succ,
      Nat.factorization_mul (by omega) (Nat.factorial_ne_zero n)]
    simp [add_comm]

lemma sub_one_mul_sum_factorization_le {q : ℕ} (hq : q.Prime) (T : ℕ) :
    ((q : ℝ) - 1) * ∑ z ∈ Icc 1 T, (z.factorization q : ℝ) ≤ T := by
  have h1 : (q - 1) * (T.factorial).factorization q ≤ T := by
    have := Fact.mk hq
    rw [Nat.factorization_def _ hq, sub_one_mul_padicValNat_factorial]
    exact Nat.sub_le _ _
  have h2 : ((q - 1 : ℕ) : ℝ) = (q : ℝ) - 1 := by
    rw [Nat.cast_sub hq.one_le]; simp
  rw [← h2, ← Nat.cast_sum, sum_factorization_Icc_eq, ← Nat.cast_mul]
  exact_mod_cast h1

lemma log_qPart {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) (z : ℕ) :
    Real.log (qPart Q z) = ∑ q ∈ Q, (z.factorization q : ℝ) * Real.log q := by
  unfold qPart
  push_cast
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl fun q _ => ?_
    rw [Real.log_pow]
  · intro q hq
    exact pow_ne_zero _ (by exact_mod_cast (hQ q hq).ne_zero)

lemma one_le_qPart {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) (z : ℕ) : 1 ≤ qPart Q z := by
  unfold qPart
  rw [Nat.one_le_iff_ne_zero, Finset.prod_ne_zero_iff]
  intro q hq
  exact pow_ne_zero _ (hQ q hq).ne_zero

lemma sum_log_div_sub_one_le {y : ℝ} (hy1 : 1 ≤ y) (hy : 7 ≤ Real.log y) (Q : Finset ℕ)
    (hQ : ∀ q ∈ Q, q.Prime ∧ (q : ℝ) ≤ y) :
    ∑ q ∈ Q, Real.log q / ((q : ℝ) - 1) ≤ 4 * Real.log y := by
  calc ∑ q ∈ Q, Real.log q / ((q : ℝ) - 1)
      ≤ ∑ q ∈ Q, 2 * (Real.log q / q) := by
        refine Finset.sum_le_sum fun q hq => ?_
        have h2 : (2 : ℝ) ≤ q := by exact_mod_cast (hQ q hq).1.two_le
        have hl : 0 ≤ Real.log q := Real.log_natCast_nonneg q
        rw [div_le_iff₀ (by linarith), mul_comm, ← mul_assoc, mul_div_assoc']
        rw [le_div_iff₀ (by linarith)]
        nlinarith
    _ = 2 * ∑ q ∈ Q, Real.log q / q := by rw [Finset.mul_sum]
    _ ≤ 2 * ∑ p ∈ Ioc 0 ⌊y⌋₊ with p.Prime, Real.log p / p := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (by norm_num)
        · intro q hq
          simp only [Finset.mem_filter, Finset.mem_Ioc]
          exact ⟨⟨(hQ q hq).1.pos, Nat.le_floor (hQ q hq).2⟩, (hQ q hq).1⟩
        · intro p _ _
          exact div_nonneg (Real.log_natCast_nonneg p) (Nat.cast_nonneg p)
    _ = 2 * (Real.log y + Mertens.E₁p y) := by rw [Mertens.sum_log_prime_div_eq]
    _ ≤ 4 * Real.log y := by
        have hE := Mertens.E₁p.le hy1
        have h4 : Real.log 4 ≤ 4 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
        linarith

/-- Paper Lemma 6.4. -/
theorem qPart_tail : ∃ y₀ : ℝ, ∀ y : ℝ, y₀ ≤ y → ∀ Q : Finset ℕ, (∀ q ∈ Q, q.Prime ∧ (q : ℝ) ≤ y) →
    ∀ T : ℕ, (((Icc 1 T).filter (fun z => y ^ 40 < (qPart Q z : ℝ))).card : ℝ) ≤ T / 10 := by
  refine ⟨Real.exp 7, fun y hy Q hQ T => ?_⟩
  have hy0 : 0 < y := lt_of_lt_of_le (Real.exp_pos 7) hy
  have hlog : 7 ≤ Real.log y := by
    rw [← Real.log_exp 7]; exact Real.log_le_log (Real.exp_pos 7) hy
  have hQp : ∀ q ∈ Q, q.Prime := fun q hq => (hQ q hq).1
  set F := (Icc 1 T).filter (fun z => y ^ 40 < (qPart Q z : ℝ))
  have key2 : ∑ z ∈ Icc 1 T, Real.log (qPart Q z) ≤ T * (4 * Real.log y) := by
    simp_rw [log_qPart hQp]
    rw [Finset.sum_comm]
    calc ∑ q ∈ Q, ∑ z ∈ Icc 1 T, (z.factorization q : ℝ) * Real.log q
        = ∑ q ∈ Q, Real.log q / ((q : ℝ) - 1) *
            (((q : ℝ) - 1) * ∑ z ∈ Icc 1 T, (z.factorization q : ℝ)) := by
          refine Finset.sum_congr rfl fun q hq => ?_
          have h2 : (2 : ℝ) ≤ q := by exact_mod_cast (hQp q hq).two_le
          have hne : (q : ℝ) - 1 ≠ 0 := by linarith
          rw [← Finset.sum_mul]
          field_simp
      _ ≤ ∑ q ∈ Q, Real.log q / ((q : ℝ) - 1) * T := by
          refine Finset.sum_le_sum fun q hq => ?_
          have h2 : (2 : ℝ) ≤ q := by exact_mod_cast (hQp q hq).two_le
          exact mul_le_mul_of_nonneg_left (sub_one_mul_sum_factorization_le (hQp q hq) T)
            (div_nonneg (Real.log_natCast_nonneg q) (by linarith))
      _ = T * ∑ q ∈ Q, Real.log q / ((q : ℝ) - 1) := by
          rw [← Finset.sum_mul, mul_comm]
      _ ≤ T * (4 * Real.log y) :=
          mul_le_mul_of_nonneg_left (sum_log_div_sub_one_le (le_trans (Real.one_le_exp (by norm_num)) hy) hlog Q hQ) (Nat.cast_nonneg T)
  have key3 : (F.card : ℝ) * (40 * Real.log y) ≤ ∑ z ∈ Icc 1 T, Real.log (qPart Q z) := by
    calc (F.card : ℝ) * (40 * Real.log y) = ∑ z ∈ F, 40 * Real.log y := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ∑ z ∈ F, Real.log (qPart Q z) := by
          refine Finset.sum_le_sum fun z hz => ?_
          have hz' := (Finset.mem_filter.1 hz).2
          have : Real.log (y ^ 40) = 40 * Real.log y := by rw [Real.log_pow]; norm_num
          rw [← this]
          exact (Real.log_lt_log (by positivity) hz').le
      _ ≤ ∑ z ∈ Icc 1 T, Real.log (qPart Q z) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun z _ _ => Real.log_natCast_nonneg _)
  have hl0 : 0 < Real.log y := by linarith
  have : (F.card : ℝ) * (40 * Real.log y) ≤ (T / 10) * (40 * Real.log y) := by
    calc _ ≤ _ := key3
      _ ≤ _ := key2
      _ = _ := by ring
  exact le_of_mul_le_mul_right this (by positivity)

end Erdos786
