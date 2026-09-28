import Erdos786.Lifting

/-! # Step 5 (core): replacing the maximal `Q`-part

Pure counting form of paper Lemma 6.6. Probabilities over `z ∈ [1,T]` are replaced by weighted counts. -/

open Finset

namespace Erdos786

lemma qPart_factorization {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) (z r : ℕ) :
    (qPart Q z).factorization r = if r ∈ Q then z.factorization r else 0 := by
  unfold qPart
  rw [Nat.factorization_prod (fun q hq => pow_ne_zero _ (hQ q hq).ne_zero)]
  rw [Finsupp.finsetSum_apply]
  rw [Finset.sum_congr rfl (fun q hq => by rw [(hQ q hq).factorization_pow])]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']

lemma qPart_ne_zero {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) (z : ℕ) : qPart Q z ≠ 0 := by
  unfold qPart
  rw [Finset.prod_ne_zero_iff]
  intro q hq
  exact pow_ne_zero _ (hQ q hq).ne_zero

lemma qPart_dvd {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) {z : ℕ} (hz : z ≠ 0) : qPart Q z ∣ z := by
  rw [← Nat.factorization_le_iff_dvd (qPart_ne_zero hQ z) hz]
  intro r
  rw [qPart_factorization hQ]
  split_ifs <;> simp

lemma qPart_mem {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) (z : ℕ) : qPart Q z ∈ Nat.factoredNumbers Q := by
  rw [Nat.mem_factoredNumbers']
  intro r hr hdvd
  have hpos := hr.factorization_pos_of_dvd (qPart_ne_zero hQ z) hdvd
  rw [qPart_factorization hQ] at hpos
  by_contra h
  simp [h] at hpos

lemma qPart_of_mem {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) {m : ℕ} (hm : m ∈ Nat.factoredNumbers Q) :
    qPart Q m = m := by
  apply Nat.eq_of_factorization_eq (qPart_ne_zero hQ m) (Nat.ne_zero_of_mem_factoredNumbers hm)
  intro r
  rw [qPart_factorization hQ]
  split_ifs with h
  · rfl
  · symm
    by_contra h0
    have hr : r.Prime := Nat.prime_of_mem_primeFactors (Nat.support_factorization m ▸ Finsupp.mem_support_iff.2 h0)
    have hd : r ∣ m := Nat.dvd_of_mem_primeFactors (Nat.support_factorization m ▸ Finsupp.mem_support_iff.2 h0)
    exact h (Nat.mem_factoredNumbers'.1 hm r hr hd)

lemma qPart_mul (Q : Finset ℕ) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    qPart Q (a * b) = qPart Q a * qPart Q b := by
  unfold qPart
  rw [← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [Nat.factorization_mul ha hb, Finsupp.add_apply, pow_add]

lemma qPart_div_qPart {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) {z : ℕ} (hz : z ≠ 0) :
    qPart Q (z / qPart Q z) = 1 := by
  have hd := qPart_dvd hQ hz
  show ∏ q ∈ Q, q ^ (z / qPart Q z).factorization q = 1
  refine Finset.prod_eq_one fun q hq => ?_
  have : (z / qPart Q z).factorization q = 0 := by
    rw [Nat.factorization_div hd, Finsupp.tsub_apply, qPart_factorization hQ, if_pos hq]
    simp
  rw [this, pow_zero]

lemma qPart_mul_div_eq {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) {z : ℕ} (hz : z ≠ 0) :
    qPart Q z * (z / qPart Q z) = z :=
  Nat.mul_div_cancel' (qPart_dvd hQ hz)

lemma div_qPart_ne_zero {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) {z : ℕ} (hz : z ≠ 0) :
    z / qPart Q z ≠ 0 := by
  intro h
  have := qPart_mul_div_eq hQ hz
  rw [h, mul_zero] at this
  exact hz this.symm

lemma qPart_smooth_mul {Q : Finset ℕ} (hQ : ∀ q ∈ Q, q.Prime) {m z : ℕ}
    (hm : m ∈ Nat.factoredNumbers Q) (hz : z ≠ 0) : qPart Q (m * (z / qPart Q z)) = m := by
  rw [qPart_mul Q (Nat.ne_zero_of_mem_factoredNumbers hm) (div_qPart_ne_zero hQ hz),
    qPart_div_qPart hQ hz, qPart_of_mem hQ hm, mul_one]


/-- Paper Lemma 6.6, counting form.
* `A ⊆ [1,N]`, `E = [1,N] \ A`, `p` prime, `p ∉ Q`, `Q` a finite set of primes, `2p ≤ N`, `T = N / p`;
* (tail) at most `T/10` of `z ∈ [1,T]` have `qPart Q z > K`;
* (nonheavy) `16 p |E ∩ pℕ| < N`;
* (reservoir) for every `Q`-smooth `1 ≤ k ≤ K`, the set `M_k` of `Q`-smooth `m` with `pk ≤ 2m ≤ 2pk`
  has at least `γ p k` elements;
* (small deficit) `32 |E| ≤ γ N`.
Then some `Q`-smooth `k ≤ K`, `m` with `pk ≤ 2m`, `m < pk` admit at least `T / (2K)` values `u` with
`m u ∈ A` and `p k u ∈ A`. -/
theorem core_pairs (N p K : ℕ) (γ : ℝ) (hγ : 0 < γ) (A : Finset ℕ) (hA : A ⊆ Icc 1 N)
    (Q : Finset ℕ) (hQ : ∀ q ∈ Q, q.Prime) (hp : p.Prime) (hpQ : p ∉ Q) (hpN : 2 * p ≤ N) (hK : 1 ≤ K)
    (htail : (((Icc 1 (N / p)).filter (fun z => K < qPart Q z)).card : ℝ) ≤ (N / p : ℕ) / 10)
    (hnonheavy : 16 * p * ((Icc 1 N \ A).filter (fun n => p ∣ n)).card < N)
    (hres : ∀ k ∈ Nat.factoredNumbers Q, 1 ≤ k → k ≤ K →
      γ * p * k ≤ (((Icc 1 (p * k)).filter (fun m => m ∈ Nat.factoredNumbers Q ∧ p * k ≤ 2 * m)).card : ℝ))
    (hdef : 32 * ((Icc 1 N \ A).card : ℝ) ≤ γ * N) :
    ∃ k m : ℕ, k ∈ Nat.factoredNumbers Q ∧ m ∈ Nat.factoredNumbers Q ∧ 1 ≤ k ∧ k ≤ K ∧
      p * k ≤ 2 * m ∧ m < p * k ∧
      ∃ U : Finset ℕ, ((N / p : ℕ) : ℝ) / (2 * K) ≤ U.card ∧ ∀ u ∈ U, m * u ∈ A ∧ p * k * u ∈ A := by
  obtain ⟨M, hM⟩ : ∃ M : ℕ → Finset ℕ, ∀ k, M k =
      (Icc 1 (p * k)).filter (fun m => m ∈ Nat.factoredNumbers Q ∧ p * k ≤ 2 * m) :=
    ⟨_, fun _ => rfl⟩
  have hres' : ∀ k ∈ Nat.factoredNumbers Q, 1 ≤ k → k ≤ K → γ * p * k ≤ ((M k).card : ℝ) := by
    intro k h1 h2 h3; rw [hM]; exact hres k h1 h2 h3
  set T := N / p with hT
  have hp0 : 0 < p := hp.pos
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp0
  have hT2 : 2 ≤ T := (Nat.le_div_iff_mul_le hp0).2 (by linarith)
  have hTN : p * T ≤ N := Nat.mul_div_le N p
  have hNT : N < p * (T + 1) := Nat.lt_mul_div_succ N hp0
  have hγp : 0 < γ * p := mul_pos hγ hpR
  set E := Icc 1 N \ A with hE
  set G := (Icc 1 T).filter (fun z => qPart Q z ≤ K) with hG
  have hGmem : ∀ z ∈ G, 1 ≤ z ∧ z ≤ T ∧ qPart Q z ≤ K := by
    intro z hz
    simp only [hG, Finset.mem_filter, Finset.mem_Icc] at hz
    exact ⟨hz.1.1, hz.1.2, hz.2⟩
  have hk1 : ∀ z, (1 : ℝ) ≤ qPart Q z := fun z => by
    exact_mod_cast Nat.one_le_iff_ne_zero.2 (qPart_ne_zero hQ z)
  have hcG : ∀ z ∈ G, γ * p * (qPart Q z) ≤ ((M (qPart Q z)).card : ℝ) := by
    intro z hz
    exact hres' _ (qPart_mem hQ z) (Nat.one_le_iff_ne_zero.2 (qPart_ne_zero hQ z)) (hGmem z hz).2.2
  have hcpos : ∀ z ∈ G, 0 < ((M (qPart Q z)).card : ℝ) := by
    intro z hz
    have := hcG z hz
    have : 0 < γ * p * (qPart Q z : ℝ) := mul_pos hγp (by linarith [hk1 z])
    linarith
  -- size of G
  have hGcard : (T : ℝ) - T / 10 ≤ G.card := by
    have h := Finset.card_filter_add_card_filter_not (s := Icc 1 T) (fun z => qPart Q z ≤ K)
    have h2 : ((Icc 1 T).filter (fun z => ¬ qPart Q z ≤ K)) =
        (Icc 1 T).filter (fun z => K < qPart Q z) := by
      apply Finset.filter_congr; intro z _; exact not_le
    rw [h2, Nat.card_Icc] at h
    have h3 : (G.card : ℝ) + (((Icc 1 T).filter (fun z => K < qPart Q z)).card : ℝ) = T := by
      norm_cast
    linarith
  -- failure (b)
  have hFb : 16 * ((G.filter (fun z => p * z ∉ A)).card) ≤ T := by
    have hinj : (G.filter (fun z => p * z ∉ A)).card ≤ (E.filter (fun n => p ∣ n)).card := by
      apply Finset.card_le_card_of_injOn (fun z => p * z)
      · intro z hz
        simp only [Finset.mem_coe, Finset.mem_filter] at hz ⊢
        obtain ⟨h1, h2, -⟩ := hGmem z hz.1
        simp only [hE, Finset.mem_sdiff, Finset.mem_Icc]
        refine ⟨⟨⟨?_, ?_⟩, hz.2⟩, dvd_mul_right p z⟩
        · nlinarith
        · calc p * z ≤ p * T := Nat.mul_le_mul_left p h2
            _ ≤ N := hTN
      · intro z _ z' _ h
        exact Nat.eq_of_mul_eq_mul_left hp0 h
    have h1 : p * (16 * (G.filter (fun z => p * z ∉ A)).card) < p * (T + 1) := by
      calc p * (16 * (G.filter (fun z => p * z ∉ A)).card)
          = 16 * p * (G.filter (fun z => p * z ∉ A)).card := by ring
        _ ≤ 16 * p * (E.filter (fun n => p ∣ n)).card := Nat.mul_le_mul_left _ hinj
        _ < N := hnonheavy
        _ < p * (T + 1) := hNT
    have := Nat.lt_of_mul_lt_mul_left h1
    omega
  -- failure (c), per point of E
  have hper : ∀ b ∈ E, ∑ z ∈ G, ∑ m ∈ M (qPart Q z),
      (if b = m * (z / qPart Q z) then 1 / ((M (qPart Q z)).card : ℝ) else 0) ≤ 3 / (γ * p) := by
    intro b _
    obtain ⟨m₀, hm₀⟩ : ∃ m₀, m₀ = qPart Q b := ⟨_, rfl⟩
    have hm₀0 : m₀ ≠ 0 := hm₀ ▸ qPart_ne_zero hQ b
    obtain ⟨x, hx⟩ : ∃ x : ℝ, x = (m₀ : ℝ) / p := ⟨_, rfl⟩
    have hx0 : 0 ≤ x := by rw [hx]; positivity
    obtain ⟨Z, hZ⟩ : ∃ Z : Finset ℕ,
        Z = G.filter (fun z => m₀ ∈ M (qPart Q z) ∧ b = m₀ * (z / qPart Q z)) := ⟨_, rfl⟩
    have step1 : ∑ z ∈ G, ∑ m ∈ M (qPart Q z),
        (if b = m * (z / qPart Q z) then 1 / ((M (qPart Q z)).card : ℝ) else 0)
        = ∑ z ∈ Z, 1 / ((M (qPart Q z)).card : ℝ) := by
      rw [hZ, Finset.sum_filter (s := G)]
      refine Finset.sum_congr rfl fun z hz => ?_
      have hz0 : z ≠ 0 := by have := (hGmem z hz).1; omega
      rw [ite_and, ← Finset.sum_ite_eq' (M (qPart Q z)) m₀
        (fun _ => if b = m₀ * (z / qPart Q z) then 1 / ((M (qPart Q z)).card : ℝ) else 0)]
      refine Finset.sum_congr rfl fun m hm => ?_
      have hmF : m ∈ Nat.factoredNumbers Q := by
        rw [hM] at hm; exact (Finset.mem_filter.1 hm).2.1
      by_cases hmm : m = m₀
      · rw [if_pos hmm, hmm]
      · rw [if_neg hmm, if_neg]
        intro hbm
        apply hmm
        rw [hm₀, hbm, qPart_smooth_mul hQ hmF hz0]
    have hmx : 0 < max 1 x := lt_of_lt_of_le one_pos (le_max_left _ _)
    have step2 : ∑ z ∈ Z, 1 / ((M (qPart Q z)).card : ℝ) ≤ Z.card * (1 / (γ * p * max 1 x)) := by
      rw [← nsmul_eq_mul, ← Finset.sum_const]
      refine Finset.sum_le_sum fun z hz => ?_
      rw [hZ, Finset.mem_filter] at hz
      obtain ⟨hzG, hmem, -⟩ := hz
      rw [hM, Finset.mem_filter, Finset.mem_Icc] at hmem
      have hkx : x ≤ qPart Q z := by
        rw [hx, div_le_iff₀ hpR]
        have : (m₀ : ℝ) ≤ p * qPart Q z := by exact_mod_cast hmem.1.2
        linarith
      apply one_div_le_one_div_of_le (mul_pos hγp hmx)
      calc γ * p * max 1 x ≤ γ * p * qPart Q z :=
            mul_le_mul_of_nonneg_left (max_le (hk1 z) hkx) hγp.le
        _ ≤ _ := hcG z hzG
    have step3 : (Z.card : ℝ) ≤ x + 2 := by
      have hcard : Z.card ≤ (Icc (m₀ / p) (2 * m₀ / p)).card := by
        apply Finset.card_le_card_of_injOn (fun z => qPart Q z)
        · intro z hz
          simp only [Finset.mem_coe, hZ, Finset.mem_filter] at hz
          obtain ⟨-, hmem, -⟩ := hz
          rw [hM, Finset.mem_filter, Finset.mem_Icc] at hmem
          simp only [Finset.mem_coe, Finset.mem_Icc]
          constructor
          · calc m₀ / p ≤ (p * qPart Q z) / p := Nat.div_le_div_right hmem.1.2
              _ = qPart Q z := Nat.mul_div_cancel_left _ hp0
          · exact (Nat.le_div_iff_mul_le hp0).2 (by rw [mul_comm]; exact hmem.2.2)
        · intro z hz z' hz' hzz
          simp only [Finset.mem_coe, hZ, Finset.mem_filter] at hz hz'
          have hz0 : z ≠ 0 := by have := (hGmem z hz.1).1; omega
          have hz0' : z' ≠ 0 := by have := (hGmem z' hz'.1).1; omega
          have hu : z / qPart Q z = z' / qPart Q z' :=
            Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm₀0) (hz.2.2.symm.trans hz'.2.2)
          simp only at hzz
          calc z = qPart Q z * (z / qPart Q z) := (qPart_mul_div_eq hQ hz0).symm
            _ = qPart Q z' * (z' / qPart Q z') := by rw [hu, hzz]
            _ = z' := qPart_mul_div_eq hQ hz0'
      rw [Nat.card_Icc] at hcard
      have ha : (m₀ : ℝ) / p - 1 ≤ ((m₀ / p : ℕ) : ℝ) := by
        have h := Nat.lt_mul_div_succ m₀ hp0
        have h' : (m₀ : ℝ) < p * (((m₀ / p : ℕ) : ℝ) + 1) := by exact_mod_cast h
        rw [div_sub_one hpR.ne', div_le_iff₀ hpR]
        linarith
      have hc : ((2 * m₀ / p : ℕ) : ℝ) ≤ 2 * ((m₀ : ℝ) / p) := by
        have := Nat.cast_div_le (m := 2 * m₀) (n := p) (α := ℝ)
        push_cast at this
        rw [mul_div_assoc] at this
        exact this
      rcases le_total (m₀ / p) (2 * m₀ / p + 1) with h | h
      · have h4 : ((Z.card : ℕ) : ℝ) ≤ ((2 * m₀ / p + 1 - m₀ / p : ℕ) : ℝ) := by exact_mod_cast hcard
        rw [Nat.cast_sub h] at h4
        push_cast at h4
        rw [hx]
        linarith
      · rw [Nat.sub_eq_zero_of_le h, Nat.le_zero] at hcard
        rw [hcard]
        simp only [Nat.cast_zero]
        linarith
    have hx3 : x + 2 ≤ 3 * max 1 x := by
      rcases le_total x 1 with h | h
      · rw [max_eq_left h]; linarith
      · rw [max_eq_right h]; linarith
    rw [step1]
    calc _ ≤ _ := step2
      _ ≤ (x + 2) * (1 / (γ * p * max 1 x)) :=
          mul_le_mul_of_nonneg_right step3 (one_div_pos.2 (mul_pos hγp hmx)).le
      _ ≤ 3 / (γ * p) := by
          rw [mul_one_div, div_le_div_iff₀ (mul_pos hγp hmx) hγp]
          have := mul_le_mul_of_nonneg_left hx3 hγp.le
          nlinarith
  -- failure (c), total
  have hFc : ∑ z ∈ G, (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∉ A)).card : ℝ)
      / (M (qPart Q z)).card ≤ E.card * (3 / (γ * p)) := by
    calc _ ≤ ∑ z ∈ G, ∑ m ∈ M (qPart Q z), ∑ b ∈ E,
          (if b = m * (z / qPart Q z) then 1 / ((M (qPart Q z)).card : ℝ) else 0) := by
          refine Finset.sum_le_sum fun z hz => ?_
          have hz0 : z ≠ 0 := by have := (hGmem z hz).1; omega
          have hzT := (hGmem z hz).2.1
          rw [← Finset.sum_boole, Finset.sum_div]
          refine Finset.sum_le_sum fun m hm => ?_
          rw [Finset.sum_ite_eq']
          have hmM := hm
          rw [hM, Finset.mem_filter, Finset.mem_Icc] at hmM
          by_cases hA' : m * (z / qPart Q z) ∈ A
          · rw [if_neg (not_not.2 hA'), zero_div]
            split_ifs <;> positivity
          · have hEm : m * (z / qPart Q z) ∈ E := by
              simp only [hE, Finset.mem_sdiff, Finset.mem_Icc]
              refine ⟨⟨?_, ?_⟩, hA'⟩
              · have := Nat.pos_of_ne_zero (div_qPart_ne_zero hQ hz0)
                nlinarith [hmM.1.1]
              · calc m * (z / qPart Q z) ≤ (p * qPart Q z) * (z / qPart Q z) :=
                      Nat.mul_le_mul_right _ hmM.1.2
                  _ = p * z := by rw [mul_assoc, qPart_mul_div_eq hQ hz0]
                  _ ≤ p * T := Nat.mul_le_mul_left p hzT
                  _ ≤ N := hTN
            rw [if_pos hA', if_pos hEm]
      _ = ∑ b ∈ E, ∑ z ∈ G, ∑ m ∈ M (qPart Q z),
          (if b = m * (z / qPart Q z) then 1 / ((M (qPart Q z)).card : ℝ) else 0) :=
          (Finset.sum_congr rfl fun z _ => Finset.sum_comm).trans Finset.sum_comm
      _ ≤ ∑ b ∈ E, 3 / (γ * p) := Finset.sum_le_sum hper
      _ = E.card * (3 / (γ * p)) := by rw [Finset.sum_const, nsmul_eq_mul]
  -- pointwise lower bound for the success weight
  have hlow : ∀ z ∈ G, 1 - (if p * z ∉ A then (1 : ℝ) else 0)
      - (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∉ A)).card : ℝ) / (M (qPart Q z)).card
      ≤ (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∈ A ∧ p * z ∈ A)).card : ℝ)
        / (M (qPart Q z)).card := by
    intro z hz
    have hc := hcpos z hz
    by_cases hpz : p * z ∈ A
    · have hsplit := Finset.card_filter_add_card_filter_not (s := M (qPart Q z))
        (fun m => m * (z / qPart Q z) ∈ A)
      have hf : (M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∈ A ∧ p * z ∈ A)
          = (M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∈ A) := by
        apply Finset.filter_congr; intro m _; simp [hpz]
      rw [hf, if_neg (not_not.2 hpz)]
      have h2 : (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∈ A)).card : ℝ)
          + (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∉ A)).card : ℝ)
          = (M (qPart Q z)).card := by exact_mod_cast hsplit
      have h3 : (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∈ A)).card : ℝ)
            / (M (qPart Q z)).card
          + (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∉ A)).card : ℝ)
            / (M (qPart Q z)).card = 1 := by
        rw [← add_div, h2, div_self hc.ne']
      linarith
    · rw [if_pos hpz]
      have : 0 ≤ (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∉ A)).card : ℝ)
          / (M (qPart Q z)).card := by positivity
      have : 0 ≤ (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∈ A ∧ p * z ∈ A)).card : ℝ)
          / (M (qPart Q z)).card := by positivity
      linarith
  have hSlow : (G.card : ℝ) - (G.filter (fun z => p * z ∉ A)).card
      - ∑ z ∈ G, (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∉ A)).card : ℝ)
          / (M (qPart Q z)).card
      ≤ ∑ z ∈ G, (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∈ A ∧ p * z ∈ A)).card : ℝ)
          / (M (qPart Q z)).card := by
    calc _ = ∑ z ∈ G, (1 - (if p * z ∉ A then (1 : ℝ) else 0)
          - (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∉ A)).card : ℝ)
            / (M (qPart Q z)).card) := by
          rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.sum_boole,
            nsmul_eq_mul, mul_one]
      _ ≤ _ := Finset.sum_le_sum hlow
  -- the conclusion, by contradiction
  by_contra hcon
  obtain ⟨Ks, hKs⟩ : ∃ Ks : Finset ℕ, Ks = (Icc 1 K).filter (fun k => k ∈ Nat.factoredNumbers Q) :=
    ⟨_, rfl⟩
  have hsmall : ∀ k ∈ Ks, ∀ m ∈ M k,
      ((G.filter (fun z => qPart Q z = k ∧ m * (z / k) ∈ A ∧ p * z ∈ A)).card : ℝ) < T / (2 * K) := by
    intro k hk m hm
    by_contra hge
    replace hge := not_lt.1 hge
    apply hcon
    rw [hKs, Finset.mem_filter, Finset.mem_Icc] at hk
    have hm' := hm
    rw [hM, Finset.mem_filter, Finset.mem_Icc] at hm'
    have hdz : ∀ z ∈ G.filter (fun z => qPart Q z = k ∧ m * (z / k) ∈ A ∧ p * z ∈ A), k ∣ z := by
      intro z hz
      rw [Finset.mem_filter] at hz
      have hz0 : z ≠ 0 := by have := (hGmem z hz.1).1; omega
      rw [← hz.2.1]; exact qPart_dvd hQ hz0
    refine ⟨k, m, hk.2, hm'.2.1, hk.1.1, hk.1.2, hm'.2.2, ?_,
      (G.filter (fun z => qPart Q z = k ∧ m * (z / k) ∈ A ∧ p * z ∈ A)).image (fun z => z / k), ?_, ?_⟩
    · refine lt_of_le_of_ne hm'.1.2 ?_
      intro hmk
      apply hpQ
      exact Nat.mem_factoredNumbers'.1 hm'.2.1 p hp (by rw [hmk]; exact dvd_mul_right p k)
    · rw [Finset.card_image_of_injOn]
      · exact hge
      · intro z hz z' hz' h
        have h1 := hdz z hz
        have h2 := hdz z' hz'
        simp only at h
        calc z = k * (z / k) := (Nat.mul_div_cancel' h1).symm
          _ = k * (z' / k) := by rw [h]
          _ = z' := Nat.mul_div_cancel' h2
    · intro u hu
      rw [Finset.mem_image] at hu
      obtain ⟨z, hz, rfl⟩ := hu
      have h1 := hdz z hz
      rw [Finset.mem_filter] at hz
      refine ⟨hz.2.2.1, ?_⟩
      rw [mul_assoc, Nat.mul_div_cancel' h1]
      exact hz.2.2.2
  have hKpos : ∀ k ∈ Ks, 0 < ((M k).card : ℝ) := by
    intro k hk
    rw [hKs, Finset.mem_filter, Finset.mem_Icc] at hk
    have := hres' k hk.2 hk.1.1 hk.1.2
    have h1 : (1 : ℝ) ≤ k := by exact_mod_cast hk.1.1
    have : 0 < γ * p * (k : ℝ) := mul_pos hγp (by linarith)
    linarith
  have hmaps : ∀ z ∈ G, qPart Q z ∈ Ks := by
    intro z hz
    rw [hKs, Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨Nat.one_le_iff_ne_zero.2 (qPart_ne_zero hQ z), (hGmem z hz).2.2⟩, qPart_mem hQ z⟩
  have hKsK : (Ks.card : ℝ) ≤ K := by
    have : Ks.card ≤ K := by
      rw [hKs]
      calc _ ≤ (Icc 1 K).card := Finset.card_filter_le _ _
        _ = K := by simp
    exact_mod_cast this
  have hSup : ∑ z ∈ G, (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∈ A ∧ p * z ∈ A)).card : ℝ)
      / (M (qPart Q z)).card ≤ T / 2 := by
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc _ = ∑ k ∈ Ks, (∑ m ∈ M k,
          ((G.filter (fun z => qPart Q z = k ∧ m * (z / k) ∈ A ∧ p * z ∈ A)).card : ℝ))
            / (M k).card := by
          refine Finset.sum_congr rfl fun k _ => ?_
          have e1 : ∑ z ∈ G.filter (fun z => qPart Q z = k),
              (((M (qPart Q z)).filter (fun m => m * (z / qPart Q z) ∈ A ∧ p * z ∈ A)).card : ℝ)
                / (M (qPart Q z)).card
              = ∑ z ∈ G.filter (fun z => qPart Q z = k),
                (((M k).filter (fun m => m * (z / k) ∈ A ∧ p * z ∈ A)).card : ℝ) / (M k).card :=
            Finset.sum_congr rfl fun z hz => by rw [(Finset.mem_filter.1 hz).2]
          have e2 : ∑ z ∈ G.filter (fun z => qPart Q z = k),
                ((M k).filter (fun m => m * (z / k) ∈ A ∧ p * z ∈ A)).card
              = ∑ m ∈ M k, (G.filter (fun z => qPart Q z = k ∧ m * (z / k) ∈ A ∧ p * z ∈ A)).card := by
            simp only [Finset.card_filter]
            rw [Finset.sum_comm]
            refine Finset.sum_congr rfl fun m _ => ?_
            rw [Finset.sum_filter]
            refine Finset.sum_congr rfl fun z _ => ?_
            by_cases h : qPart Q z = k <;> simp [h]
          rw [e1, ← Finset.sum_div]
          congr 1
          exact_mod_cast e2
      _ ≤ ∑ k ∈ Ks, (∑ m ∈ M k, ((T : ℝ) / (2 * K))) / (M k).card := by
          refine Finset.sum_le_sum fun k hk => ?_
          apply div_le_div_of_nonneg_right _ (hKpos k hk).le
          exact Finset.sum_le_sum fun m hm => (hsmall k hk m hm).le
      _ = ∑ k ∈ Ks, ((T : ℝ) / (2 * K)) := by
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [Finset.sum_const, nsmul_eq_mul, mul_div_right_comm, div_self (hKpos k hk).ne', one_mul]
      _ = Ks.card * ((T : ℝ) / (2 * K)) := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ K * ((T : ℝ) / (2 * K)) :=
          mul_le_mul_of_nonneg_right hKsK (by positivity)
      _ = T / 2 := by
          have : (K : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ K := by exact_mod_cast hK
                                   linarith
          field_simp
  -- numerics
  have hTR : (2 : ℝ) ≤ T := by exact_mod_cast hT2
  have hFbR : 16 * (((G.filter (fun z => p * z ∉ A)).card : ℕ) : ℝ) ≤ T := by exact_mod_cast hFb
  have hNTR : (N : ℝ) < p * (T + 1) := by exact_mod_cast hNT
  have hEc : E.card * (3 / (γ * p)) ≤ 3 * (T + 1) / 32 := by
    rw [mul_div_assoc', div_le_div_iff₀ hγp (by norm_num)]
    have : (E.card : ℝ) * 32 ≤ γ * N := by linarith
    nlinarith
  linarith

end Erdos786
