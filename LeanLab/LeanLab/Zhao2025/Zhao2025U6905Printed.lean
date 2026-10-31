import Mathlib
import LeanLab.Zhao2025.Zhao2025U6902R
import LeanLab.Zhao2025.Zhao2025U6903ST

/-!
# Zhao 2025, the printed Section 4 R values and T sums, certified

G. Zhao, arXiv 2511.05631v2, a preprint.  Unit U-6905, CLOUD MANUAL-M2, T2.  AI wrote the Lean code.
Binary Goldbach is open.  Parameters from gen/u6905_r.py.  Each theorem is PROVED by kernel computation
and bounds the printed display through `Rbound_of_342_343`, `Rbound_of_338` or `sT_of_315`,
CONDITIONAL ON (3.42) or (3.43), (3.38), (3.15) respectively.

* (4.13) max Rᵢ ≤ 0.157 with `λ₁ = λ₂ = λ* = 0.92`, `N* = 4`, `Λ = 1.467`; Σ Rᵢ ≤ 0.457 by (3.38).
* (4.16) R₁, R₂ ≤ 0.374, `λ₁ = 0.40`, `λ₂ = λ* = 0.92`, `N* = 4`.
* (4.18) R₁ ≤ 0.556, `λ₁ = λ₂ = 0.40`, `λ* = 0.92`, only with `N* = 3`; with the `N* = 4` the text
  names the (3.42) branch alone exceeds 0.5902, `br342_418_N4` of U-6837, a cosmetic QUESTION.
* (4.23) max Rᵢ ≤ 0.300, `N* = 3`, and Σ Rᵢ ≤ 0.581 by (3.38), `Λ = 1.348`, `λ₀ = 0.60`, `λ* = 0.91`.
* (4.8) Σ_{i≥2} Tᵢ ≤ 6.85 at `λ₀ = Λ = 1.29`; (4.12) Σ Tᵢ ≤ 6.33 at `λ₀ = 0.92`, `Λ = 1.467`;
  (4.21) Σ Tᵢ ≤ 7.63 at `λ₀ = 0.60`, `Λ = 1.348`, all by (3.15) with general `k`.
-/

namespace LeanLab.Zhao2025.U6900

set_option maxRecDepth 100000 in
theorem p413max_ok : chkR4 (1131/1000 : ℚ) (1467/1000 : ℚ) (23/25 : ℚ) (23/25 : ℚ) (23/25 : ℚ) 4 (157/1000 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p413sum_ok : chkR8 (101/125 : ℚ) (1467/1000 : ℚ) (23/25 : ℚ) (23/25 : ℚ) (23/25 : ℚ) (457/1000 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p416_ok : chkR4 (927/1000 : ℚ) (1467/1000 : ℚ) (2/5 : ℚ) (23/25 : ℚ) (23/25 : ℚ) 4 (187/500 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p418N3_ok : chkR4 (1229/1000 : ℚ) (1467/1000 : ℚ) (2/5 : ℚ) (2/5 : ℚ) (23/25 : ℚ) 3 (139/250 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p423max_ok : chkR4 (1309/1000 : ℚ) (337/250 : ℚ) (3/5 : ℚ) (3/5 : ℚ) (91/100 : ℚ) 3 (3/10 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p423sum_ok : chkR8 (37/50 : ℚ) (337/250 : ℚ) (3/5 : ℚ) (3/5 : ℚ) (91/100 : ℚ) (581/1000 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p48sum_ok : chkT (199/2000 : ℚ) (2501/10000 : ℚ) (1977/10000 : ℚ) (129/100 : ℚ) (129/100 : ℚ) (5808713/50000000 : ℚ) (137/20 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p412sum_ok : chkT (891/10000 : ℚ) (113/500 : ℚ) (1697/10000 : ℚ) (1467/1000 : ℚ) (23/25 : ℚ) (108543817/1000000000 : ℚ) (633/100 : ℚ) = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem p421sum_ok : chkT (951/10000 : ℚ) (1187/5000 : ℚ) (439/2500 : ℚ) (337/250 : ℚ) (3/5 : ℚ) (7787083/62500000 : ℚ) (763/100 : ℚ) = true := by decide +kernel

end LeanLab.Zhao2025.U6900
