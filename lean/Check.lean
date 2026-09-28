import Erdos786

/-! Run `lake env lean Check.lean` to see the axioms used by the two resolved statements. -/

#check @Erdos786.erdos_786.parts.i
#check @Erdos786.erdos_786.parts.ii
#print axioms Erdos786.erdos_786.parts.i
#print axioms Erdos786.erdos_786.parts.ii
