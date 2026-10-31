-- AI wrote this Lean code. Binary Goldbach is open.
import LeanLab.Ternary78.BennettAsymptotic
import LeanLab.Ternary78.BennettAt300000
import LeanLab.Ternary78.BennettConsistency
import LeanLab.Ternary78.BennettCorollary
import LeanLab.Ternary78.BennettGrowth
import LeanLab.Ternary78.BennettLower
import LeanLab.Ternary78.BennettRounded
import LeanLab.Ternary78.BennettThreshold
import LeanLab.Ternary78.BennettZeroData
import LeanLab.Ternary78.CountSummability
import LeanLab.Ternary78.FiniteWeights
import LeanLab.Ternary78.GammaTail
import LeanLab.Ternary78.GammaWeights

#print axioms LeanLab.Ternary78.Bennett.printed_growth_slope_negative
#print axioms LeanLab.Ternary78.Bennett.growth_slope_positive
#print axioms LeanLab.Ternary78.Bennett.lowerEndpoint_affine
#print axioms LeanLab.Ternary78.Bennett.countGrowthAt_of_bennett
#print axioms LeanLab.Ternary78.Bennett.countGrowthAt_above_071431
#print axioms LeanLab.Ternary78.Bennett.grid25_log_bounds
#print axioms LeanLab.Ternary78.Bennett.grid25_lower_certificate
#print axioms LeanLab.Ternary78.Bennett.count_grid25_positive
#print axioms LeanLab.Ternary78.Bennett.gamma25_tsum_lower
#print axioms LeanLab.Ternary78.Bennett.gamma25_weight_pos
#print axioms LeanLab.Ternary78.Bennett.modelCount_satisfies_bennett
#print axioms LeanLab.Ternary78.Bennett.modelCountFull_satisfies_bennett
#print axioms LeanLab.Ternary78.Bennett.cor12_log_constants
#print axioms LeanLab.Ternary78.Bennett.cor12_error_envelope
#print axioms LeanLab.Ternary78.Bennett.cor12_log_height
#print axioms LeanLab.Ternary78.Bennett.cor12_large_of_bennett
#print axioms LeanLab.Ternary78.Bennett.mainTerm_ge_neg_two_div
#print axioms LeanLab.Ternary78.Bennett.small_mainTerm_abs_le_four
#print axioms LeanLab.Ternary78.Bennett.cor12_of_full_bennett
#print axioms LeanLab.Ternary78.Bennett.exp1567_le_six
#print axioms LeanLab.Ternary78.Bennett.large_ell_of_twenty
#print axioms LeanLab.Ternary78.Bennett.bennett_log_upper
#print axioms LeanLab.Ternary78.Bennett.count_le_quadratic_of_bennett
#print axioms LeanLab.Ternary78.Bennett.exists_quadratic_bound_of_bennett
#print axioms LeanLab.Ternary78.Bennett.lowerEndpoint_le_count
#print axioms LeanLab.Ternary78.Bennett.gridLower_le_gridCount
#print axioms LeanLab.Ternary78.Bennett.weightedCount_lower_of_bennett
#print axioms LeanLab.Ternary78.Bennett.roundedGrid_le_gridCount
#print axioms LeanLab.Ternary78.Bennett.weightedCount_le_rounded
#print axioms LeanLab.Ternary78.Bennett.rounded_weighted_lower_of_bennett
#print axioms LeanLab.Ternary78.Bennett.model_gap_of_bennett_certificate
#print axioms LeanLab.Ternary78.Bennett.model_gap_of_gamma_bennett
#print axioms LeanLab.Ternary78.Bennett.weak_certificate_has_closing_model
#print axioms LeanLab.Ternary78.Bennett.summable_gamma_of_bennett
#print axioms LeanLab.Ternary78.Bennett.gamma_real_tsum_lower_of_bennett
#print axioms LeanLab.Ternary78.Bennett.summable_of_quadratic_fibers
#print axioms LeanLab.Ternary78.Bennett.summable_gamma_of_quadratic_bins
#print axioms LeanLab.Ternary78.Bennett.weightedCount_card_le_sum
#print axioms LeanLab.Ternary78.Bennett.heightSet_mono
#print axioms LeanLab.Ternary78.Bennett.finite_weighted_lower_of_bennett
#print axioms LeanLab.Ternary78.Bennett.height_weighted_lower_of_bennett
#print axioms LeanLab.Ternary78.Bennett.gamma_norm_le_real
#print axioms LeanLab.Ternary78.Bennett.gamma_norm_mul_pow_le_real
#print axioms LeanLab.Ternary78.Bennett.gamma_norm_mul_one_add_abs_pow_le
#print axioms LeanLab.Ternary78.Bennett.gamma_factor_norm_mono
#print axioms LeanLab.Ternary78.Bennett.gammaSeq_norm_antitone
#print axioms LeanLab.Ternary78.Bennett.gamma_norm_antitone
#print axioms LeanLab.Ternary78.Bennett.gamma_norm_abs
#print axioms LeanLab.Ternary78.Bennett.gamma_weighted_lower_of_bennett
#print axioms LeanLab.Ternary78.Bennett.gamma_tsum_lower_of_bennett
#print axioms LeanLab.Ternary78.Bennett.gamma78_integer_grid_lower_of_bennett
