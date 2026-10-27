-- AI wrote this Lean code. Binary Goldbach is open.
import LeanLab.Ternary78.CanonicalAt300000104
import LeanLab.Ternary78.CanonicalCount104
import LeanLab.Ternary78.CanonicalGamma104
import LeanLab.Ternary78.CanonicalZeros104
import LeanLab.Ternary78.Decomp104
import LeanLab.Ternary78.Decomp104b
import LeanLab.Ternary78.Limitations104
import LeanLab.Ternary78.Paper104
import LeanLab.Ternary78.PaperCorollary104

set_option format.width 1000

#print axioms LeanLab.Ternary78.Bennett.actual_zero_grid25_exists
#print axioms LeanLab.Ternary78.Bennett.gamma25_weight_le_three_tenths
#print axioms LeanLab.Ternary78.Bennett.actual_gamma25_lower
#print axioms LeanLab.Ternary78.Bennett.gamma25_certificate_has_closing_model
#print axioms LeanLab.Ternary78.Bennett.canonicalCount_eq_card
#print axioms LeanLab.Ternary78.Bennett.canonicalCount_mono
#print axioms LeanLab.Ternary78.Bennett.canonicalCount_eq_card_filter
#print axioms LeanLab.Ternary78.Bennett.canonicalCount_eq_sum_orders
#print axioms LeanLab.Ternary78.Bennett.actual_gamma_summable
#print axioms LeanLab.Ternary78.Bennett.actual_gamma_grid_lower
#print axioms LeanLab.Ternary78.Bennett.actual_model_gap
#print axioms LeanLab.Ternary78.Bennett.lfunction_strip_zeros_finite
#print axioms LeanLab.Ternary78.Bennett.zeroOccurrences_bounded_finite
#print axioms LeanLab.Ternary78.Bennett.lfunction_order_ne_top
#print axioms LeanLab.Ternary78.Bennett.primitive_ne_one
#print axioms LeanLab.Ternary78.Bennett.lfunction_order_pos_iff
#print axioms LeanLab.Ternary78.Bennett.primitive_mod_three_exists
#print axioms LeanLab.Ternary78.Paper104.analytic_table46
#print axioms LeanLab.Ternary78.Paper104.computed_prime_ladder
#print axioms LeanLab.Ternary78.Paper104.table46_below_join
#print axioms LeanLab.Ternary78.Paper104.table46_interval_inclusion
#print axioms LeanLab.Ternary78.Paper104.ladder_covers
#print axioms LeanLab.Ternary78.Paper104.primeInterval_decomposed
#print axioms LeanLab.Ternary78.Paper104.primeInterval_from_conservative_inputs
#print axioms LeanLab.Ternary78.Paper104.lemma7_denominator
#print axioms LeanLab.Ternary78.Paper104.lemma7_identity
#print axioms LeanLab.Ternary78.Paper104.lemma7_exp_term
#print axioms LeanLab.Ternary78.Paper104.lemma7_gap_term
#print axioms LeanLab.Ternary78.Paper104.lemma7_decomposed
#print axioms LeanLab.Ternary78.Paper104.coarse_interval_not_sufficient
#print axioms LeanLab.Ternary78.Paper104.oddPrimeRange_of_inputs
