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

theorem main_of (hLift : LiftStmt) (hPairs : PairsStmt) (hHeavy : HeavyStmt) (hSmooth : SmoothStmt)
    (hQPart : QPartStmt) (hCore : CoreStmt) (hWords : WordsStmt) : MainStatement := by
  sorry

end Erdos786
