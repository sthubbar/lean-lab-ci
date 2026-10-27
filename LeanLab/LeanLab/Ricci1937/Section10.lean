import Mathlib

/-!
# P0092 Ricci 1937, the numerical step of Section 10, page 90

Lab check, unit U-5615, CLOUD 20261019T1416Z-cloud26. AI wrote the Lean code. Read from the page
image of page 90 of papers/P0092.pdf. Binary Goldbach is OPEN.

Ricci writes "coi valori (2.2) e (2.5) calcolati al n.° 2, (1 + τ(2))² σ < 18,9227", with
(2.2) τ(2) < 2,9555 and (2.5) σ < 1,20948. These two printed bounds give only 18,9235, see
`printed_inputs_exceed`; the true values, τ(2) = 2,9554037 and σ = 1,200714 from
numerics/sec1.py and sec2.py, give 18,785, so the printed inequality is true but does not follow
from the printed inputs. The slip is cosmetic: `k_unchanged` shows k = ⌊1,6813 · 1,003 · X⌋ + 1 = 32
for every X ≤ 18,9235, so k = 32, w ≤ 6719 and S ≤ 67 stand.

* `printed_inputs_exceed`: (1 + 2,9555)² · 1,20948 > 18,9227, PROVED.
* `k_unchanged`: 31 ≤ 1,6813 · 1,003 · X < 32 for 18,78 ≤ X ≤ 18,9235, PROVED.
* `jk`: 210 · 32 - 1 = 6719 and 64 + 3 = 67, PROVED.
-/

namespace LeanLab.Ricci1937

theorem printed_inputs_exceed :
    (189227 / 10000 : ℚ) < (1 + 29555 / 10000) ^ 2 * (120948 / 100000) := by norm_num

theorem printed_inputs_value :
    (1 + 29555 / 10000 : ℚ) ^ 2 * (120948 / 100000) < 189236 / 10000 := by norm_num

theorem k_unchanged (X : ℚ) (h1 : 1878 / 100 ≤ X) (h2 : X ≤ 189236 / 10000) :
    31 ≤ 16813 / 10000 * (1003 / 1000) * X ∧ 16813 / 10000 * (1003 / 1000) * X < 32 := by
  constructor <;> nlinarith

theorem jk : 210 * 32 - 1 = 6719 ∧ 2 * 32 + 3 = 67 := by norm_num

end LeanLab.Ricci1937
