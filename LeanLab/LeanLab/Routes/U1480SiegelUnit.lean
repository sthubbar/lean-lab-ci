/-
AI-written Lean code, Claude, Lean Lab run 20261022T1302Z-31860, unit U-1480, track T3 CONNECTION SWEEP.
Candidate I-SWEEP1: a q-dependent exceptional zero bound for even real characters, for the
Siegel term nu of BJS 2022 (P0009) equation (91), which uses Bordignon 2020 (arXiv 1907.08327)
Theorem 1.3, beta0 <= 1 - 100/(sqrt q log^2 q), uniform in q.

Bordignon's 100 is 8 times 12.52, where 12.52 = (1/2) log(7.5e10) bounds log eta_d from below
in the range d u0^2 >= 7.5e10, eta_d = (v0 + u0 sqrt d)/2, v0^2 - d u0^2 = 4. The trivial bound
d u0^2 >= d gives log eta_d >= (1/2) log d, so L(1, chi) >= log q / (2 sqrt q) for every even
primitive real chi mod q above 7.5e10 with h >= 1, and with Bordignon's Theorem 1.1,
|L'(sigma, chi)| <= log^2 q / 8, the mean value step gives beta0 <= 1 - 4/(sqrt q log q).

Here only the elementary steps, PROVED with no hypothesis beyond the stated real inequalities:
* `log_unit_ge`: v^2 - d u^2 = 4, u >= 1, v > 0, d > 0 imply log d / 2 <= log ((v + u sqrt d)/2).
* `siegel_gap`: L1 >= log q/(2 sqrt q), 0 < M <= log^2 q / 8 and L1 <= delta M give
  delta >= 4/(sqrt q log q).  delta is 1 - beta0, M a bound for |L'| on (beta0, 1).
* `new_beats_old`: for log q >= 25 the new gap is at least Bordignon's 100/(sqrt q log^2 q).
The class number formula, h >= 1, the mean value theorem for L and Theorem 1.1 are NOT formalized;
they are the cited inputs of the composed statement. Nothing here is progress on binary Goldbach,
which is OPEN.
-/
import Mathlib

namespace LeanLab.Routes.U1480

open Real

/-- The norm `+1` unit `(v + u √d)/2` with `v² - d u² = 4` and `u ≥ 1` has `log ≥ (log d)/2`. -/
theorem log_unit_ge {d u v : ℝ} (hd : 0 < d) (hu : 1 ≤ u) (hv : 0 < v)
    (h : v ^ 2 - d * u ^ 2 = 4) :
    Real.log d / 2 ≤ Real.log ((v + u * Real.sqrt d) / 2) := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have hsq : Real.sqrt d ^ 2 = d := Real.sq_sqrt hd.le
  have h1 : u * Real.sqrt d < v := by
    by_contra hc
    push_neg at hc
    have hpos : 0 ≤ u * Real.sqrt d := by positivity
    have : v ^ 2 ≤ (u * Real.sqrt d) ^ 2 := by
      exact pow_le_pow_left₀ hv.le hc 2
    have : (u * Real.sqrt d) ^ 2 = d * u ^ 2 := by rw [mul_pow, hsq]; ring
    nlinarith
  have h2 : Real.sqrt d ≤ u * Real.sqrt d := by nlinarith
  have h3 : Real.sqrt d ≤ (v + u * Real.sqrt d) / 2 := by linarith
  rw [← Real.log_sqrt hd.le]
  exact Real.log_le_log hs h3

/-- The mean value step: `L(1) ≥ log q /(2 √q)`, `|L'| ≤ M ≤ log² q / 8`, `L(1) ≤ δ M`
give `δ ≥ 4 /(√q log q)`. -/
theorem siegel_gap {q L1 M δ : ℝ} (hq : 1 < q) (hM : 0 < M)
    (hMle : M ≤ Real.log q ^ 2 / 8) (hL1 : Real.log q / (2 * Real.sqrt q) ≤ L1)
    (hmv : L1 ≤ δ * M) : 4 / (Real.sqrt q * Real.log q) ≤ δ := by
  have hl : 0 < Real.log q := Real.log_pos hq
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 (by linarith)
  have hL1pos : 0 < L1 := lt_of_lt_of_le (by positivity) hL1
  have hδ : 0 < δ := by
    by_contra hc
    push_neg at hc
    nlinarith
  have hA : Real.log q / (2 * Real.sqrt q) ≤ δ * (Real.log q ^ 2 / 8) := by
    calc Real.log q / (2 * Real.sqrt q) ≤ L1 := hL1
      _ ≤ δ * M := hmv
      _ ≤ δ * (Real.log q ^ 2 / 8) := by gcongr
  rw [div_le_iff₀ (by positivity)] at hA
  rw [div_le_iff₀ (by positivity)]
  have key : Real.log q * 4 ≤ Real.log q * (δ * (Real.sqrt q * Real.log q)) := by nlinarith
  exact le_of_mul_le_mul_left key hl

/-- For `log q ≥ 25` the q-dependent gap `4/(√q log q)` is at least Bordignon's
`100/(√q log² q)`; at the BJS modulus range `log K ≈ 45` the ratio is about 1.8. -/
theorem new_beats_old {q : ℝ} (hq : 0 < q) (hL : 25 ≤ Real.log q) :
    100 / (Real.sqrt q * Real.log q ^ 2) ≤ 4 / (Real.sqrt q * Real.log q) := by
  have hl : 0 < Real.log q := by linarith
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 hq
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have : 0 < Real.sqrt q * Real.log q := by positivity
  nlinarith [mul_pos this hl]

/-- Non-vacuity of `log_unit_ge`: d = 5, u = 1, v = 3, 9 - 5 = 4. -/
example : Real.log 5 / 2 ≤ Real.log ((3 + 1 * Real.sqrt 5) / 2) :=
  log_unit_ge (by norm_num) le_rfl (by norm_num) (by norm_num)

end LeanLab.Routes.U1480

#print axioms LeanLab.Routes.U1480.log_unit_ge
#print axioms LeanLab.Routes.U1480.siegel_gap
#print axioms LeanLab.Routes.U1480.new_beats_old
