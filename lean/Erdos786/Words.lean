import Erdos786.Lifting

/-! # Step 6: every good prime is a short product of rich ratios (induction on primes) -/

open Finset Real

namespace Erdos786

/-- Product of the entrywise inverses of a list of rationals. -/
lemma prod_map_inv_rat (l : List ℚ) : (l.map (·⁻¹)).prod = l.prod⁻¹ := by
  induction l with
  | nil => simp
  | cons a l ih => simp [List.prod_cons, ih, mul_comm]

/-- Words for all prime factors of `v` (of length `≤ log q · L`) concatenate to a word for `v` of
length `≤ log v · L`. -/
lemma word_of_factors (R : ℚ → Prop) (Q : ℕ → Prop) (L : ℝ)
    (hQ : ∀ q, q.Prime → Q q → ∃ w : List ℚ, w.prod = q ∧ (∀ x ∈ w, R x) ∧
      (w.length : ℝ) ≤ Real.log q * L) :
    ∀ v : ℕ, v ≠ 0 → (∀ q ∈ v.primeFactors, Q q) →
      ∃ w : List ℚ, w.prod = v ∧ (∀ x ∈ w, R x) ∧ (w.length : ℝ) ≤ Real.log v * L := by
  intro v
  induction v using Nat.recOnMul with
  | zero => intro h; exact absurd rfl h
  | one => intro _ _; exact ⟨[], by simp, by simp, by simp⟩
  | prime p hp =>
    intro _ h
    exact hQ p hp (h p (Nat.mem_primeFactors.2 ⟨hp, dvd_rfl, hp.ne_zero⟩))
  | mul a b iha ihb =>
    intro hab h
    have ha : a ≠ 0 := left_ne_zero_of_mul hab
    have hb : b ≠ 0 := right_ne_zero_of_mul hab
    rw [Nat.primeFactors_mul ha hb] at h
    obtain ⟨wa, hwa, hRa, hla⟩ := iha ha (fun q hq => h q (Finset.mem_union_left _ hq))
    obtain ⟨wb, hwb, hRb, hlb⟩ := ihb hb (fun q hq => h q (Finset.mem_union_right _ hq))
    refine ⟨wa ++ wb, ?_, ?_, ?_⟩
    · rw [List.prod_append, hwa, hwb]; push_cast; ring
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · exact hRa x hx
      · exact hRb x hx
    · rw [List.length_append]
      push_cast
      rw [Real.log_mul (by exact_mod_cast ha) (by exact_mod_cast hb)]
      linarith

/-- Paper Lemma 6.7, abstract form. `good` is the set of admissible primes (nonheavy, `≤ P`).
Small primes (`≤ p₀`) are rich; every good prime `p > p₀` has a replacement `p = (pk/m)·m·k⁻¹`
with `pk/m` rich, `k, m` composed of good primes `q` with `q^16 ≤ p`, `k ≤ p^(5/2)`, `m ≤ pk`.
Then every good prime is a product of at most `16 (log p)^2` rich ratios (or their inverses). -/
theorem short_word (A : Set ℕ) (M p₀ : ℕ) (good : ℕ → Prop)
    (hsmall : ∀ p, p.Prime → p ≤ p₀ → Rich A p M)
    (hstep : ∀ p, p.Prime → good p → p₀ < p → ∃ k m : ℕ, 1 ≤ k ∧ 1 ≤ m ∧
      (∀ q ∈ k.primeFactors, good q ∧ q ^ 16 ≤ p) ∧ (∀ q ∈ m.primeFactors, good q ∧ q ^ 16 ≤ p) ∧
      (k : ℝ) ^ 2 ≤ (p : ℝ) ^ 5 ∧ m ≤ p * k ∧ Rich A ((p * k : ℕ) / (m : ℚ)) M) :
    ∀ p, p.Prime → (good p ∨ p ≤ p₀) →
      ∃ w : List ℚ, w.prod = p ∧ (∀ q ∈ w, Rich A q M) ∧ (w.length : ℝ) ≤ 16 * (Real.log p) ^ 2 := by
  -- strengthened statement: all entries are also nonzero
  have key : ∀ p, p.Prime → (good p ∨ p ≤ p₀) →
      ∃ w : List ℚ, w.prod = p ∧ (∀ q ∈ w, Rich A q M ∧ q ≠ 0) ∧
        (w.length : ℝ) ≤ 16 * (Real.log p) ^ 2 := by
    intro p
    induction p using Nat.strong_induction_on with
    | _ p ih =>
    intro hp hgp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hlogp : 0.6931471803 < Real.log p :=
      lt_of_lt_of_le Real.log_two_gt_d9 (Real.log_le_log (by norm_num) hp2)
    by_cases hsm : p ≤ p₀
    · refine ⟨[(p : ℚ)], by simp, ?_, ?_⟩
      · intro q hq
        rw [List.mem_singleton] at hq
        subst hq
        exact ⟨hsmall p hp hsm, by exact_mod_cast hp.ne_zero⟩
      · simp only [List.length_singleton, Nat.cast_one]
        nlinarith
    have hgood : good p := hgp.resolve_right hsm
    obtain ⟨k, m, hk1, hm1, hkf, hmf, hk2, hmk, hr⟩ := hstep p hp hgood (by omega)
    -- words for the small prime factors, with length `≤ log q · log p`
    have hQ : ∀ q, q.Prime → (good q ∧ q ^ 16 ≤ p) →
        ∃ w : List ℚ, w.prod = q ∧ (∀ x ∈ w, Rich A x M ∧ x ≠ 0) ∧
          (w.length : ℝ) ≤ Real.log q * Real.log p := by
      rintro q hq ⟨hgq, hq16⟩
      have hqlt : q < p := by
        have : q ^ 1 < q ^ 16 := Nat.pow_lt_pow_right hq.one_lt (by norm_num)
        rw [pow_one] at this
        omega
      obtain ⟨w, hw, hR, hl⟩ := ih q hqlt hq (Or.inl hgq)
      refine ⟨w, hw, hR, hl.trans ?_⟩
      have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.one_lt.le
      have hlq : 0 ≤ Real.log q := Real.log_nonneg hq1
      have h16 : 16 * Real.log q ≤ Real.log p := by
        have : ((q : ℝ) ^ 16) ≤ p := by exact_mod_cast hq16
        have := Real.log_le_log (by positivity) this
        rw [Real.log_pow] at this
        push_cast at this
        linarith
      nlinarith
    obtain ⟨wk, hwk, hRk, hlk⟩ := word_of_factors _ _ _ hQ k (by omega) hkf
    obtain ⟨wm, hwm, hRm, hlm⟩ := word_of_factors _ _ _ hQ m (by omega) hmf
    have hkpos : (0 : ℚ) < k := by exact_mod_cast hk1
    have hmpos : (0 : ℚ) < m := by exact_mod_cast hm1
    have hppos : (0 : ℚ) < p := by exact_mod_cast hp.pos
    refine ⟨[((p * k : ℕ) : ℚ) / (m : ℚ)] ++ wm ++ wk.map (·⁻¹), ?_, ?_, ?_⟩
    · rw [List.prod_append, List.prod_append, prod_map_inv_rat, hwm, hwk]
      simp only [List.prod_singleton]
      push_cast
      field_simp
    · intro x hx
      rcases List.mem_append.1 hx with hx | hx
      · rcases List.mem_append.1 hx with hx | hx
        · rw [List.mem_singleton] at hx
          subst hx
          refine ⟨hr, ?_⟩
          push_cast
          positivity
        · exact hRm x hx
      · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
        exact ⟨Rich.inv (hRk y hy).2 (hRk y hy).1, inv_ne_zero (hRk y hy).2⟩
    · simp only [List.length_append, List.length_singleton, List.length_map]
      push_cast
      have hk1r : (1 : ℝ) ≤ k := by exact_mod_cast hk1
      have hm1r : (1 : ℝ) ≤ m := by exact_mod_cast hm1
      have hlk0 : 0 ≤ Real.log k := Real.log_nonneg hk1r
      have hlogk : 2 * Real.log k ≤ 5 * Real.log p := by
        have := Real.log_le_log (by positivity) hk2
        rw [Real.log_pow, Real.log_pow] at this
        push_cast at this
        linarith
      have hlogm : Real.log m ≤ Real.log p + Real.log k := by
        have hmr : (m : ℝ) ≤ p * k := by exact_mod_cast hmk
        have := Real.log_le_log (by positivity) hmr
        rw [Real.log_mul (by positivity) (by positivity)] at this
        exact this
      have hsum : Real.log m + Real.log k ≤ 6 * Real.log p := by linarith
      have hlp0 : 0 ≤ Real.log p := by linarith
      nlinarith
  intro p hp hgp
  obtain ⟨w, hw, hR, hl⟩ := key p hp hgp
  exact ⟨w, hw, fun q hq => (hR q hq).1, hl⟩

end Erdos786
