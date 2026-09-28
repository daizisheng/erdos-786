import Erdos786.Lifting

/-! # Step 5 (core): replacing the maximal `Q`-part

Pure counting form of paper Lemma 6.6. Probabilities over `z ∈ [1,T]` are replaced by weighted counts. -/

open Finset

namespace Erdos786

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
  sorry

end Erdos786
