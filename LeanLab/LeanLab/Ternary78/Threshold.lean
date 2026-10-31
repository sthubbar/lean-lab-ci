/-
I-0086, T2 FRONTIER, unit U-1323, PC run 20261021T0203Z-29730.

The 7/8 hybrid as a CONDITIONAL theorem. Everything here is CONDITIONAL ON the 7/8 half-plane
`HalfPlane78`, OpenAI's unrefereed quasi-Riemann claim of 30 Sep 2026, and on two further named
inputs: the explicit formula error `ExplicitFormula78`, constant `A` a parameter with no published
explicit value, and the circle method transfer `MajorArcTransfer`, a MODEL of Helfgott's
Section 7.4 closing with the major arcs fed by the 7/8 explicit formula. Nothing here is about
binary Goldbach, which is OPEN.

* `HalfPlane78 Q`: no zero of any Dirichlet `L(s, χ)`, `χ` mod `q ≤ Q`, in `Re s > 7/8`,
  stated with Mathlib's `DirichletCharacter.LFunction`.
* `ExplicitPsi78 Q A x₀`: `‖ψ(x, χ) - δ_χ x‖ ≤ A x^{7/8} log² x` for `x ≥ x₀`, `q ≤ Q`.
* `closes_of_ge`: for `N ≥ N₀ = (S √Q / m)^8 / c` the closing inequality
  `S √Q ≤ m (c N)^{1/8}` holds, PROVED unconditional, real numbers.
* `ternary_of_78`: CONDITIONAL ON `HalfPlane78`, `ExplicitFormula78`, `MajorArcTransfer`, every
  odd `N ≥ N₀` is a sum of three primes.
* `gap_open`: for every `S ≥ 0.985` the closing inequality fails for every `N ≤ 8.875·10³⁰`
  at `Q = 300000`, PROVED unconditional; so the hybrid closes the Helfgott-Platt gap only if the
  zero sum is below `0.98449`, while the main term zero count mod `300000` gives about `4.0`.
* `gap_open_S4`: with `S ≥ 3.99` it fails for every `N ≤ 6·10³⁵`.
* `hl_barrier`: for `θ > 3/4` the pure explicit formula minor arc bound `C N^{θ+1/4} log N`
  never drops below `c N / log N` when `c ≤ C`, `N ≥ e`; Hardy-Littlewood needed `θ < 3/4`.

AI-written Lean code, Claude, unit U-1323.
-/
import Mathlib
import LeanLab.Common.Goldbach
import LeanLab.Ternary78.Hybrid

namespace LeanLab.Ternary78.Threshold
open Real
open scoped Classical

/-- **The 7/8 half-plane** for moduli `q ≤ Q`, CITED, OpenAI 30 Sep 2026, unrefereed. -/
def HalfPlane78 (Q : ℕ) : Prop :=
  ∀ (q : ℕ) [NeZero q], q ≤ Q → ∀ (χ : DirichletCharacter ℂ q) (s : ℂ),
    7 / 8 < s.re → (χ ≠ 1 ∨ s ≠ 1) → DirichletCharacter.LFunction χ s ≠ 0

/-- `ψ(x, χ) = ∑_{n ≤ x} χ(n) Λ(n)`. -/
noncomputable def psiChi {q : ℕ} (χ : DirichletCharacter ℂ q) (x : ℝ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, χ n * (ArithmeticFunction.vonMangoldt n : ℂ)

/-- The explicit formula error under the half-plane: constant `A`, from `x₀` on. -/
def ExplicitPsi78 (Q : ℕ) (A x₀ : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q], q ≤ Q → ∀ (χ : DirichletCharacter ℂ q) (x : ℝ), x₀ ≤ x →
    ‖psiChi χ x - (if χ = 1 then (x : ℂ) else 0)‖ ≤ A * x ^ (7 / 8 : ℝ) * Real.log x ^ 2

/-- **Cited input**, the truncated explicit formula with zeros in `Re s ≤ 7/8`. -/
def ExplicitFormula78 (Q : ℕ) (A x₀ : ℝ) : Prop := HalfPlane78 Q → ExplicitPsi78 Q A x₀

/-- **MODEL input**, the circle method transfer: with the explicit formula error, Helfgott's
minor arcs at `r₀ = Q/2` and his Section 7.4 margin `m`, an odd `N` with `x = c N ≥ x₀` is a sum of
three primes as soon as the relative major arc error `S √Q x^{-1/8}` is at most `m`. -/
def MajorArcTransfer (Q : ℕ) (A x₀ S m c : ℝ) : Prop :=
  ExplicitPsi78 Q A x₀ → ∀ N : ℕ, Odd N → x₀ ≤ c * N →
    S * sqrt Q ≤ m * (c * N) ^ (1 / 8 : ℝ) → IsTernarySum N

/-- **The threshold**: for `N ≥ (S √Q / m)^8 / c` the closing inequality holds. -/
theorem closes_of_ge {Q S m c N : ℝ} (hQ : 0 ≤ Q) (hS : 0 ≤ S) (hm : 0 < m) (hc : 0 < c)
    (hN : (S * sqrt Q / m) ^ 8 / c ≤ N) : S * sqrt Q ≤ m * (c * N) ^ (1 / 8 : ℝ) := by
  set B := S * sqrt Q / m with hB
  have hB0 : 0 ≤ B := div_nonneg (mul_nonneg hS (sqrt_nonneg _)) hm.le
  have hx : B ^ 8 ≤ c * N := by
    have := mul_le_mul_of_nonneg_left hN hc.le
    rwa [mul_div_cancel₀ _ hc.ne'] at this
  have h1 : B ≤ (c * N) ^ (1 / 8 : ℝ) := by
    have e : (B ^ 8) ^ (1 / 8 : ℝ) = B := by
      rw [← rpow_natCast, ← rpow_mul hB0]; norm_num
    calc B = (B ^ 8) ^ (1 / 8 : ℝ) := e.symm
      _ ≤ (c * N) ^ (1 / 8 : ℝ) := rpow_le_rpow (by positivity) hx (by norm_num)
  calc S * sqrt Q = m * B := by rw [hB]; field_simp
    _ ≤ m * (c * N) ^ (1 / 8 : ℝ) := mul_le_mul_of_nonneg_left h1 hm.le

/-- **CONDITIONAL ON `HalfPlane78`, `ExplicitFormula78`, `MajorArcTransfer`**: every odd
`N ≥ N₀ = (S √Q / m)^8 / c` with `x₀ ≤ c N` is a sum of three primes. -/
theorem ternary_of_78 {Q : ℕ} {A x₀ S m c : ℝ} (hS : 0 ≤ S) (hm : 0 < m) (hc : 0 < c)
    (hH : HalfPlane78 Q) (hE : ExplicitFormula78 Q A x₀) (hT : MajorArcTransfer Q A x₀ S m c)
    (N : ℕ) (hodd : Odd N) (hx₀ : x₀ ≤ c * N) (hN : (S * sqrt Q / m) ^ 8 / c ≤ N) :
    IsTernarySum N :=
  hT (hE hH) N hodd hx₀ (closes_of_ge (Nat.cast_nonneg Q) hS hm hc hN)

/-- Helfgott's margin and `x = c N`, `c = 0.495461...`: the instance used below. -/
noncomputable def m78 : ℝ := LeanLab.Ternary78.Hybrid.margin

/-- **The gap stays open for `S ≥ 0.985`**: at `Q = 300000`, every `N ≤ 8.875·10³⁰` with
`x = c N`, `0 < c ≤ 0.495462`, fails the closing inequality. -/
theorem gap_open {S c N : ℝ} (hS : 0.985 ≤ S) (hc : 0 < c) (hc2 : c ≤ 0.495462) (hN0 : 0 < N)
    (hN : N ≤ 8.875e30) : m78 * (c * N) ^ (1 / 8 : ℝ) < S * sqrt 300000 := by
  have hx : 0 < c * N := mul_pos hc hN0
  refine LeanLab.Ternary78.Hybrid.hybrid_fails (by norm_num) (by linarith)
    (by unfold m78 LeanLab.Ternary78.Hybrid.margin; norm_num) hx ?_
  have hm8 : m78 ^ 8 ≤ (0.079685 : ℝ) ^ 8 :=
    pow_le_pow_left₀ (by unfold LeanLab.Ternary78.Hybrid.margin; norm_num)
      LeanLab.Ternary78.Hybrid.margin_bounds.2.le 8
  have hxle : c * N ≤ 0.495462 * 8.875e30 := mul_le_mul hc2 hN hN0.le (by norm_num)
  have hS8 : (0.985 : ℝ) ^ 8 ≤ S ^ 8 := pow_le_pow_left₀ (by norm_num) hS 8
  calc m78 ^ 8 * (c * N) ≤ (0.079685 : ℝ) ^ 8 * (0.495462 * 8.875e30) :=
        mul_le_mul hm8 hxle hx.le (by positivity)
    _ < (0.985 : ℝ) ^ 8 * 300000 ^ 4 := by norm_num
    _ ≤ S ^ 8 * 300000 ^ 4 := mul_le_mul_of_nonneg_right hS8 (by norm_num)

/-- **With the zero count value `S ≈ 4.0`**: for `S ≥ 3.99` it fails for every `N ≤ 6·10³⁵`. -/
theorem gap_open_S4 {S c N : ℝ} (hS : 3.99 ≤ S) (hc : 0 < c) (hc2 : c ≤ 0.495462) (hN0 : 0 < N)
    (hN : N ≤ 6e35) : m78 * (c * N) ^ (1 / 8 : ℝ) < S * sqrt 300000 := by
  have hx : 0 < c * N := mul_pos hc hN0
  refine LeanLab.Ternary78.Hybrid.hybrid_fails (by norm_num) (by linarith)
    (by unfold m78 LeanLab.Ternary78.Hybrid.margin; norm_num) hx ?_
  have hm8 : m78 ^ 8 ≤ (0.079685 : ℝ) ^ 8 :=
    pow_le_pow_left₀ (by unfold LeanLab.Ternary78.Hybrid.margin; norm_num)
      LeanLab.Ternary78.Hybrid.margin_bounds.2.le 8
  have hxle : c * N ≤ 0.495462 * 6e35 := mul_le_mul hc2 hN hN0.le (by norm_num)
  have hS8 : (3.99 : ℝ) ^ 8 ≤ S ^ 8 := pow_le_pow_left₀ (by norm_num) hS 8
  calc m78 ^ 8 * (c * N) ≤ (0.079685 : ℝ) ^ 8 * (0.495462 * 6e35) :=
        mul_le_mul hm8 hxle hx.le (by positivity)
    _ < (3.99 : ℝ) ^ 8 * 300000 ^ 4 := by norm_num
    _ ≤ S ^ 8 * 300000 ^ 4 := mul_le_mul_of_nonneg_right hS8 (by norm_num)

/-- **Hardy-Littlewood barrier**: for `θ > 3/4`, `c ≤ C` and `log N ≥ 1`, the pure explicit
formula minor arc error `C N^{θ+1/4} log N` is never below the needed `c N / log N`. -/
theorem hl_barrier {θ C c N : ℝ} (hθ : 3 / 4 < θ) (hc : 0 ≤ c) (hcC : c ≤ C) (hN : 1 ≤ N)
    (hL : 1 ≤ Real.log N) : c * N / Real.log N ≤ C * N ^ (θ + 1 / 4) * Real.log N := by
  have hN0 : 0 < N := by linarith
  have h1 : N ≤ N ^ (θ + 1 / 4) := by
    calc N = N ^ (1 : ℝ) := (rpow_one N).symm
      _ ≤ N ^ (θ + 1 / 4) := rpow_le_rpow_of_exponent_le hN (by linarith)
  have h2 : N / Real.log N ≤ N := div_le_self hN0.le hL
  have h3 : N ^ (θ + 1 / 4) ≤ N ^ (θ + 1 / 4) * Real.log N := le_mul_of_one_le_right
    (by positivity) hL
  calc c * N / Real.log N = c * (N / Real.log N) := by ring
    _ ≤ C * (N ^ (θ + 1 / 4) * Real.log N) :=
        mul_le_mul hcC (h2.trans (h1.trans h3)) (by positivity) (hc.trans hcC)
    _ = C * N ^ (θ + 1 / 4) * Real.log N := by ring

/-- Vacuity, `closes_of_ge`: `S = 1`, `Q = 300000`, `m = 0.0797`, `c = 0.5`, `N = 10^32`. -/
example : (1 : ℝ) * sqrt 300000 ≤ 0.0797 * (0.5 * 1e32) ^ (1 / 8 : ℝ) := by
  apply closes_of_ge (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hs : sqrt (300000 : ℝ) ≤ 548 := by
    rw [sqrt_le_left (by norm_num)]; norm_num
  have : (1 * sqrt 300000 / 0.0797 : ℝ) ^ 8 ≤ (548 / 0.0797) ^ 8 :=
    pow_le_pow_left₀ (by positivity) (by gcongr; linarith) 8
  calc (1 * sqrt 300000 / 0.0797 : ℝ) ^ 8 / 0.5 ≤ (548 / 0.0797) ^ 8 / 0.5 := by gcongr
    _ ≤ 1e32 := by norm_num

/-- Vacuity, `gap_open`: `S = 1`, `c = 0.495461`, `N = 8.875·10³⁰`. -/
example : m78 * (0.495461 * 8.875e30 : ℝ) ^ (1 / 8 : ℝ) < 1 * sqrt 300000 :=
  gap_open (by norm_num) (by norm_num) (by norm_num) (by norm_num) le_rfl

/-- Vacuity, `hl_barrier`: `θ = 7/8`, `c = C = 1`, `N = e^2`. -/
example : 1 * exp 2 / Real.log (exp 2) ≤ 1 * exp 2 ^ (7 / 8 + 1 / 4 : ℝ) * Real.log (exp 2) :=
  hl_barrier (by norm_num) (by norm_num) le_rfl (by linarith [add_one_le_exp (2 : ℝ)])
    (by rw [Real.log_exp]; norm_num)

/-- Vacuity, `ternary_of_78`: the hypotheses typecheck at an instance; `HalfPlane78 0` and
`ExplicitPsi78 0 A x₀` hold vacuously, `HalfPlane78 Q` for every `Q` is VERIFIED EXTERNALLY in
OAIQuasiRiemann. -/
example : HalfPlane78 0 := fun q _ hq => by
  exact absurd (Nat.le_zero.mp hq) (NeZero.ne q)

end LeanLab.Ternary78.Threshold
