import Erdos786.Main
import Erdos786.Reduction

/-! # The formal-conjectures statements, resolved

`erdos_786.parts.i` and `erdos_786.parts.ii` of google-deepmind/formal-conjectures, with
`answer(sorry)` resolved to `False`: both questions have a negative answer. -/

namespace Erdos786

theorem erdos_786.parts.ii : False ↔ PartIIStatement :=
  ⟨False.elim, fun h => not_partII_of_main main h⟩

theorem erdos_786.parts.i : False ↔ PartIStatement :=
  ⟨False.elim, fun h => not_partI_of_main main h⟩

end Erdos786
