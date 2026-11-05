import LeanLab.LiuWang2002.GapEndpointCert352
import LeanLab.LiuWang2002.GapData352_0
import LeanLab.LiuWang2002.GapData352_1
import LeanLab.LiuWang2002.GapData352_2
import LeanLab.LiuWang2002.GapData352_3
import LeanLab.LiuWang2002.GapData352_4
import LeanLab.LiuWang2002.GapData352_5

/-!
Finite proper prime power lower bounds from Schoenfeld page 356.
Display 9.3 and its following interval are verified by integer products.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task352
open Real

/-- Derived rational enclosures for the first two middle cutoffs on
page 356, proof of display 5.1 star. -/
theorem gap_endpoint_bounds : (10 : ℝ) ^ 8 < exp 18.43 ∧
    exp (18.43 : ℝ) < 100936350 ∧ exp (18.45 : ℝ) < 102975400 := by
  have he : exp (1 : ℝ) ≤ 2.71828183 := Real.exp_one_lt_d9.le.trans (by norm_num)
  have upper43 : exp (18.43 : ℝ) < 100936350 := by
    have hh := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le he 1843
    have hp : exp (18.43 : ℝ) ^ 100 ≤ (2.71828183 : ℝ) ^ 1843 := by
      rw [← exp_nat_mul] at hh ⊢
      norm_num at hh ⊢
      exact hh
    have hn : (2.71828183 : ℝ) ^ 1843 < (100936350 : ℝ) ^ 100 := by
      have hc : (271828183 : ℝ) ^ 1843 < (100936350 : ℝ) ^ 100 * 100000000 ^ 1843 := by
        exact_mod_cast gap_endpoint_certificate.1
      rw [show (2.71828183 : ℝ) = 271828183 / 100000000 by norm_num, div_pow]
      exact (div_lt_iff₀ (by positivity)).mpr hc
    exact (pow_lt_pow_iff_left₀ (exp_pos _).le (by positivity)
      (by norm_num : (100 : ℕ) ≠ 0)).mp (hp.trans_lt hn)
  have upper45 : exp (18.45 : ℝ) < 102975400 := by
    have hh := pow_le_pow_left₀ (exp_pos (1 : ℝ)).le he 1845
    have hp : exp (18.45 : ℝ) ^ 100 ≤ (2.71828183 : ℝ) ^ 1845 := by
      rw [← exp_nat_mul] at hh ⊢
      norm_num at hh ⊢
      exact hh
    have hn : (2.71828183 : ℝ) ^ 1845 < (102975400 : ℝ) ^ 100 := by
      have hc : (271828183 : ℝ) ^ 1845 < (102975400 : ℝ) ^ 100 * 100000000 ^ 1845 := by
        exact_mod_cast gap_endpoint_certificate.2
      rw [show (2.71828183 : ℝ) = 271828183 / 100000000 by norm_num, div_pow]
      exact (div_lt_iff₀ (by positivity)).mpr hc
    exact (pow_lt_pow_iff_left₀ (exp_pos _).le (by positivity)
      (by norm_num : (100 : ℕ) ≠ 0)).mp (hp.trans_lt hn)
  refine ⟨?_, upper43, upper45⟩
  have hl := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2.7182818283)
    Real.exp_one_gt_d9.le 18
  have hs := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.43) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at hs
  have ht := mul_le_mul hl hs (by positivity) (by positivity : 0 ≤ exp 1 ^ 18)
  rw [show (18.43 : ℝ) = 18 + 0.43 by norm_num, exp_add,
    show exp (18 : ℝ) = exp 1 ^ 18 by simpa using exp_nat_mul (1 : ℝ) 18]
  norm_num at ht ⊢
  linarith

/-- Display 9.3 on its full interval. The five source subintervals use
six finite endpoints and the actual monotone proper prime power gap. -/
theorem gap_early (X : ℝ) (hSmall : 10 ^ 8 < X) (hEnd : X < exp 18.43) :
    0.000104517 * X < Chebyshev.psi X - Chebyshev.theta X := by
  have h0 := gap_of_certificate 100000000 10512 1 (by norm_num) (by norm_num) gap_certificate_0
  have h1 := gap_of_certificate 100140049 10521 1 (by norm_num) (by norm_num) gap_certificate_1
  have h2 := gap_of_certificate 100180081 10531 1 (by norm_num) (by norm_num) gap_certificate_2
  have h3 := gap_of_certificate 100741369 10540 1 (by norm_num) (by norm_num) gap_certificate_3
  have h4 := gap_of_certificate 100781521 84397 8 (by norm_num) (by norm_num) gap_certificate_4
  norm_num at h0 h1 h2 h3 h4 hSmall
  by_cases hA : X ≤ 100140049
  · have hm := gap_mono (show (100000000 : ℝ) ≤ X by linarith)
    norm_num at hm
    linarith
  by_cases hB : X ≤ 100180081
  · have hm := gap_mono (show (100140049 : ℝ) ≤ X by linarith)
    norm_num at hm
    linarith
  by_cases hC : X ≤ 100741369
  · have hm := gap_mono (show (100180081 : ℝ) ≤ X by linarith)
    norm_num at hm
    linarith
  by_cases hD : X ≤ 100781521
  · have hm := gap_mono (show (100741369 : ℝ) ≤ X by linarith)
    norm_num at hm
    linarith
  have hm := gap_mono (show (100781521 : ℝ) ≤ X by linarith)
  norm_num at hm
  have hu := hEnd.trans gap_endpoint_bounds.2.1
  linarith

/-- The displayed proper prime power lower bound after 9.3. The
finite certificates prove it without the cited 1962 theta estimate. -/
theorem gap_bridge (X : ℝ) (hStart : exp 18.43 ≤ X) (hEnd : X < exp 18.45) :
    0.000102563 * X < Chebyshev.psi X - Chebyshev.theta X := by
  have h0 := gap_of_certificate 100000000 10512 1 (by norm_num) (by norm_num) gap_certificate_0
  have h5 := gap_of_certificate 102400000 10562 1 (by norm_num) (by norm_num) gap_certificate_5
  norm_num at h0 h5
  by_cases hA : X ≤ 102400000
  · have hl := gap_endpoint_bounds.1.trans_le hStart
    norm_num at hl
    have hm := gap_mono hl.le
    norm_num at hm
    linarith
  · have hm := gap_mono (show (102400000 : ℝ) ≤ X by linarith)
    norm_num at hm
    have hu := hEnd.trans gap_endpoint_bounds.2.2
    linarith

end LeanLab.LiuWang2002.Task352
#print axioms LeanLab.LiuWang2002.Task352.gap_endpoint_bounds
#print axioms LeanLab.LiuWang2002.Task352.gap_early
#print axioms LeanLab.LiuWang2002.Task352.gap_bridge
