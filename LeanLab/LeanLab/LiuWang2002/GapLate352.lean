import LeanLab.LiuWang2002.GapSquare352
import LeanLab.LiuWang2002.LateData352_0
import LeanLab.LiuWang2002.LateData352_1
import LeanLab.LiuWang2002.LateData352_2
import LeanLab.LiuWang2002.LateData352_3
import LeanLab.LiuWang2002.LateData352_4
import LeanLab.LiuWang2002.LateData352_5
import LeanLab.LiuWang2002.LateData352_6
import LeanLab.LiuWang2002.LateData352_7
import LeanLab.LiuWang2002.LateData352_8
import LeanLab.LiuWang2002.LateData352_9
import LeanLab.LiuWang2002.LateData352_10
import LeanLab.LiuWang2002.LateData352_11
import LeanLab.LiuWang2002.LateData352_12

/-!
The square root lower correction in Schoenfeld page 356, after display 9.3.
The proof uses only finite integer certificates and monotonicity.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task352
open Real

/-- The last middle correction holds on the whole larger finite
interval from 100000000 through 133000000. This supplies the weaker
source bound with 616 in place of c plus log 467. Page 356, proof of 5.1 star. -/
theorem gap_late (X : ℝ) (hlo : 100000000 ≤ X) (hhi : X ≤ 133000000) :
    0.98 * sqrt X + 616 < Chebyshev.psi X - Chebyshev.theta X := by
  by_cases h0 : X ≤ 101949409
  · exact gap_square_interval_at X 100000000 10000 10097 10512 (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num; exact h0)
      late_certificate_0 (by norm_num)
  by_cases h1 : X ≤ 103999204
  · exact gap_square_interval_at X 101949409 10097 10198 10611 (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num; exact h1)
      late_certificate_1 (by norm_num)
  by_cases h2 : X ≤ 106502400
  · exact gap_square_interval_at X 103999204 10198 10320 10730 (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num; exact h2)
      late_certificate_2 (by norm_num)
  by_cases h3 : X ≤ 109139809
  · exact gap_square_interval_at X 106502400 10320 10447 10855 (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num; exact h3)
      late_certificate_3 (by norm_num)
  by_cases h4 : X ≤ 111513600
  · exact gap_square_interval_at X 109139809 10447 10560 10965 (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num; exact h4)
      late_certificate_4 (by norm_num)
  by_cases h5 : X ≤ 114062400
  · exact gap_square_interval_at X 111513600 10560 10680 11083 (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num; exact h5)
      late_certificate_5 (by norm_num)
  by_cases h6 : X ≤ 116812864
  · exact gap_square_interval_at X 114062400 10680 10808 11208 (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num; exact h6)
      late_certificate_6 (by norm_num)
  by_cases h7 : X ≤ 119705481
  · exact gap_square_interval_at X 116812864 10808 10941 11339 (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num; exact h7)
      late_certificate_7 (by norm_num)
  by_cases h8 : X ≤ 122766400
  · exact gap_square_interval_at X 119705481 10941 11080 11475 (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num; exact h8)
      late_certificate_8 (by norm_num)
  by_cases h9 : X ≤ 125529616
  · exact gap_square_interval_at X 122766400 11080 11204 11596 (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num; exact h9)
      late_certificate_9 (by norm_num)
  by_cases h10 : X ≤ 128663649
  · exact gap_square_interval_at X 125529616 11204 11343 11733 (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num; exact h10)
      late_certificate_10 (by norm_num)
  by_cases h11 : X ≤ 131859289
  · exact gap_square_interval_at X 128663649 11343 11483 11870 (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num; exact h11)
      late_certificate_11 (by norm_num)
  exact gap_square_interval_at X 131859289 11483 11533 11919 (by norm_num) (by norm_num) (by norm_num; linarith) (by norm_num; linarith)
      late_certificate_12 (by norm_num)

end LeanLab.LiuWang2002.Task352
#print axioms LeanLab.LiuWang2002.Task352.gap_late
