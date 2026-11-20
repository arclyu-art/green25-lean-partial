import Green25

/-!
# Trust-basis audit for the formalized Green 25 partial theorem

Compile this file separately to print the axioms used by the main verified declarations.
-/

#print axioms Green25.add_xor_eq_add_two_mul_ldiff
#print axioms Green25.card_compatibleBits
#print axioms Green25.card_allowedMasks_le_two_pow_sub_weight
#print axioms Green25.card_restrictedSameColorSums_le_weight_sum
#print axioms Green25.target_bound_of_weight_certificate
#print axioms Green25.exists_matrixScore_certificate
#print axioms Green25.card_codeQuotient
#print axioms Green25.exists_surjective_refinement
#print axioms Green25.exists_exactColor_of_average
#print axioms Green25.green25_partial

#print axioms Green25.Midpoint.exists_exact_of_parameters
#print axioms Green25.Midpoint.subpolynomial_bound
#print axioms Green25.Midpoint.exact_fixed_power
#print axioms Green25.Midpoint.exists_adaptive_partition
