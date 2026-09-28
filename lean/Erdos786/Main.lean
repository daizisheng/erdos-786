import Erdos786.Heavy
import Erdos786.Smooth
import Erdos786.QPart
import Erdos786.Coupling
import Erdos786.Words
import Erdos786.Assembly

/-! # The main theorem -/

open Finset Real Filter

namespace Erdos786

/-- **Main theorem (question (ii), distinct-factor version).** There is an absolute `η > 0` such that
for all large `N`, every `A ⊆ [1,N]` with `|A| ≥ (1-η)N` contains a violation. -/
theorem main : ∃ η : ℝ, 0 < η ∧ ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Icc 1 N →
    (1 - η) * N ≤ A.card → Violation (A : Set ℕ) :=
  main_of
    (fun A h0 a ha qs hp hr => violation_of_word A h0 a ha qs hp hr)
    (fun A h0 q hq L hL => rich_of_pairs A h0 q hq L hL)
    (fun N hN E hE hD H hH => heavy_recip_sum_le N hN E hE hD H hH)
    smooth_count qPart_tail
    (fun N p K γ hγ A hA Q hQ hp hpQ hpN hK ht hn hr hd =>
      core_pairs N p K γ hγ A hA Q hQ hp hpQ hpN hK ht hn hr hd)
    (fun A M p₀ good hs hst => short_word A M p₀ good hs hst)

end Erdos786
