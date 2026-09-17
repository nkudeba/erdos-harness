import Formal.Library.BinomialCoefficients
#print axioms Formal.Library.BinomialCoefficients.erdos_699_sub1_1_ns.erdos_699_sub1_1
#print axioms Formal.Library.BinomialCoefficients.erdos_699_sub2_1_ns.erdos_699_sub2_1
#print axioms Formal.Library.BinomialCoefficients.erdos_699_sub3_1_ns.erdos_699_sub3_1
#print axioms Formal.Library.BinomialCoefficients.erdos_699_sub4_1_ns.erdos_699_sub4_1
#print axioms Formal.Library.BinomialCoefficients.erdos_699_sub5_1_ns.erdos_699_sub5_1
#print axioms Formal.Library.BinomialCoefficients.digit_carry
#print axioms Formal.Library.BinomialCoefficients.small_index_carry
#print axioms Formal.Library.BinomialCoefficients.block_prime
#print axioms Formal.Library.BinomialCoefficients.counterexample_forces_smooth_block
#print axioms Formal.Library.BinomialCoefficients.residue_route_fails
#print axioms Formal.Library.BinomialCoefficients.same_example_satisfies_target
example : 3 < 7 ∧ 2*7 ≤ 16 ∧ Nat.Prime 5 ∧ 3 ≤ 5 ∧ 5 ≤ 7 ∧ 16 % 5 < 3 % 5 ∧ 16 % 5 < 7 % 5 := by decide
