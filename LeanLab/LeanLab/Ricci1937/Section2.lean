import Mathlib

/-!
# P0092 Ricci 1937, Section 2 numerics, pages 80 and 81

Lab check, unit U-5612, CLOUD 20261019T1416Z-cloud26. AI wrote the Lean code. The polynomial
constants of (2.5) and (2.6), with the expansions E₃^(i) and Ē₃^(i) as printed on pages 80 and 81
of papers/P0092.pdf, read from the page images. The exponential constants e^{θ₁+θ₂+θ₃}, the
quotients with e^{3θ}, and τ(f, Θ) of (2.2), (2.4) were recomputed in numerics/sec2.py, all
MATCH, and are not in Lean. Binary Goldbach is OPEN.

* `E3_lt`: E(3, Θ) < 0.186722 at θ = (0.70, 0.58, 0.54), (2.5), PROVED; the value is 0.1867211.
* `Ebar3_gt`: Ē(3, Θ) > 0.0122847 at θ = (0.90, 0.56, 0.52), (2.6), PROVED; the value is
  0.01228473, margin 3·10⁻⁸.
-/

namespace LeanLab.Ricci1937

/-- `E(3, Θ) = Σ_{i ≤ 6} (-1)^i E₃^(i)`, page 80. -/
def E3 (t1 t2 t3 : ℚ) : ℚ :=
  let s := t1 + t2 + t3
  1 - s + s ^ 2 / 2 - (s ^ 3 - t1 ^ 3) / 6 + (s ^ 4 - t1 ^ 4 - 4 * t1 ^ 3 * (t2 + t3)) / 24
    - (s ^ 5 - t1 ^ 5 - 5 * t1 ^ 4 * (t2 + t3) - 10 * t1 ^ 3 * (t2 + t3) ^ 2
        - t2 ^ 3 * (t2 ^ 2 + 5 * t1 * t2 + 10 * t1 ^ 2)) / 120
    + t3 ^ 2 / 720 * (15 * t1 ^ 2 * (6 * t2 ^ 2 + 4 * t2 * t3 + t3 ^ 2)
        + 6 * t1 * (10 * t2 ^ 3 + 10 * t2 ^ 2 * t3 + 5 * t2 * t3 ^ 2 + t3 ^ 3)
        + (15 * t2 ^ 4 + 20 * t2 ^ 3 * t3 + 15 * t2 ^ 2 * t3 ^ 2 + 6 * t2 * t3 ^ 3 + t3 ^ 4))

/-- `Ē(3, Θ) = Σ_{i ≤ 5} (-1)^i Ē₃^(i)`, page 81. -/
def Ebar3 (t1 t2 t3 : ℚ) : ℚ :=
  let s := t1 + t2 + t3
  1 - s + (s ^ 2 - t1 ^ 2) / 2 - (s ^ 3 - t1 ^ 3 - 3 * t1 ^ 2 * (t2 + t3)) / 6
    + t3 / 24 * (4 * t1 * (3 * t2 ^ 2 + 3 * t2 * t3 + t3 ^ 2)
        + 2 * t2 * (2 * t2 ^ 2 + 3 * t2 * t3 + 2 * t3 ^ 2) + t3 ^ 3)
    - t3 ^ 2 / 120 * (5 * t1 * (6 * t2 ^ 2 + 4 * t2 * t3 + t3 ^ 2)
        + 5 * t2 * (2 * t2 ^ 2 + 2 * t2 * t3 + t3 ^ 2) + t3 ^ 3)

theorem E3_lt : E3 (70 / 100) (58 / 100) (54 / 100) < 186722 / 1000000 := by
  unfold E3; norm_num

theorem Ebar3_gt : 122847 / 10000000 < Ebar3 (90 / 100) (56 / 100) (52 / 100) := by
  unfold Ebar3; norm_num

/-- (2.5) from its printed inputs: `6,171859 (0,186722 + 0,228639 · 0,0404263) < 1,20948`. -/
theorem sigma_chain : (6171859 / 1000000 : ℚ) * (186722 / 1000000 + 228639 / 1000000 * (404263 / 10000000))
    < 120948 / 100000 := by norm_num

/-- (2.6) from its printed inputs: `7,24274 (0,0122847 - 0,5449213 · 0,0223742) > 0,00066`. -/
theorem sigmabar_chain : (66 : ℚ) / 100000 <
    724274 / 100000 * (122847 / 10000000 - 5449213 / 10000000 * (223742 / 10000000)) := by norm_num

end LeanLab.Ricci1937
