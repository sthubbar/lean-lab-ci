/-
U-1582, cloud run 20261028T0803Z-11675, track T2 FRONTIER, idea I-0138.
AI wrote this Lean code. Binary Goldbach is OPEN; nothing here is progress on it.

Continuation of I-0137 and U-1579. There `thm1_of_chen`, range h > 2/(7k), and
`thm2_of_chen`, range h > 1/(7k), were CONDITIONAL ON three inputs: `PerelliReduction`
or `PerelliReduction2`, `ChenDensity`, and `LogFreeNearOne (7/3) σ₀` for some σ₀ < 1.
The last one was not a published statement. This file replaces it by a published one.

Plain math. Huxley's large values estimate for Dirichlet polynomials gives, for σ in
[3/4, 1], the Halász-Montgomery-Huxley density bound
  Σ_{χ mod q} N(σ, T, χ) ≤ C (qT)^{3(1-σ)/(3σ-1)} (log qT)^B.
Chen, Gupta and Li, arXiv 2507.08296 v1, display (1.4), quote this exponent for σ > 3/4;
Huxley, Acta Arith. 26 (1975) 435-444, is the source Perelli cites for display (21).
The exponent function A(σ) = 3/(3σ-1) decreases in σ and equals 7/3 exactly at σ = 16/21,
so on σ ≥ 16/21 the bound is at most (qT)^{(7/3)(1-σ)} (log qT)^B: that is
`LogFreeNearOne (7/3) (16/21)`. So the U-1579 ranges need only PerelliReduction,
ChenDensity and Huxley's printed near one bound, `HuxleyNearOne (3/4)`.

BUILD NOTE. In the clone at a321cfd8, `LeanLab.Routes.U1579Perelli` does not build: it uses
`Perelli1996.deg`, `nRange`, `err`, `F2` from the PC encoding of Perelli1996/Statements.lean,
which the repo copy, encoding B, lacks. So this file does not import U1579. It restates
`ZeroDensityUnif` and `LogFreeNearOne` with the same bodies as U1579, and states the
composition over an abstract target `Target : ℝ → Prop` and a degree k through
`ReductionAt`, which is exactly what U1579's `PerelliReduction` gives at one polynomial F
with k = deg F and Target = Thm1Exact F. The one line bridge to U1579 is in
U1582Bridge.lean, NOT BUILT in the clone, to be built on the PC.

Status labels are on each statement. `HuxleyNearOne` is a CITED input, stated here, never
asserted. The exact log power and the single modulus form qT are the form Perelli uses in
display (21) p. 485 for the whole range; the σ dependent form near 1 is read from Chen,
Gupta, Li (1.4) and Huxley 1975, NOT CHECKED against Huxley's page, no copy in the lab.
-/
import Mathlib
import LeanLab.Routes.U1578Sweep
import LeanLab.PerelliPintz1992.Section6

namespace LeanLab.Routes.U1582
open LeanLab.PerelliPintz1992.Section6 (allCharacterCount zeroCount zeroRegion)

/-! ### Density inputs, same bodies as U1579 -/

/-- Same body as `U1579.ZeroDensityUnif`: for every ε > 0 there is C with
Σ_{χ mod q} N(σ,T,χ) ≤ C (qT)^{A(1-σ)+ε} for q ≥ 1, T ≥ 2, 1/2 ≤ σ ≤ 1. -/
def ZeroDensityUnif (A : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ q : ℕ+, ∀ T σ : ℝ, 2 ≤ T → 1 / 2 ≤ σ → σ ≤ 1 →
    allCharacterCount q σ T ≤ ENNReal.ofReal (C * ((q : ℝ) * T) ^ (A * (1 - σ) + ε))

/-- Same body as `U1579.LogFreeNearOne`: on σ₀ ≤ σ ≤ 1,
Σ_{χ mod q} N(σ,T,χ) ≤ C (qT)^{A(1-σ)} (log qT)^B. -/
def LogFreeNearOne (A σ₀ : ℝ) : Prop :=
  ∃ C : ℝ, ∃ B : ℕ, ∀ q : ℕ+, ∀ T σ : ℝ, 2 ≤ T → σ₀ ≤ σ → σ ≤ 1 →
    allCharacterCount q σ T ≤
      ENNReal.ofReal (C * ((q : ℝ) * T) ^ (A * (1 - σ)) * Real.log ((q : ℝ) * T) ^ B)

/-- CITED, Chen-Gupta-Li arXiv 2507.08296: the ε form at A = 7/3. Same as U1579. -/
def ChenDensity : Prop := ZeroDensityUnif (7 / 3)

/-- The shape of U1579's `PerelliReduction` at one polynomial of degree k, with
`Target h` standing for Perelli's Theorem 1 at H ≥ N^h and c(h) = 1 - kh/2: from an ε
density bound with exponent A, a log free bound with exponent A' on [σ₀, 1], σ₀ < 1, and
A c(h) < 2, A' c(h) < 2, the target holds. For Theorem 2 take c(h) = 1 - kh, display (32).
A named hypothesis, never asserted. -/
def ReductionAt (c : ℝ → ℝ) (Target : ℝ → Prop) : Prop :=
  ∀ A A' σ₀ : ℝ, 0 < A → σ₀ < 1 → ZeroDensityUnif A → LogFreeNearOne A' σ₀ →
    ∀ h : ℝ, A * c h < 2 → A' * c h < 2 → Target h

/-- Plain math: the Halász-Montgomery-Huxley density exponent A(σ) = 3/(3σ - 1). -/
noncomputable def huxA (σ : ℝ) : ℝ := 3 / (3 * σ - 1)

/-- CITED input, Huxley 1975 Acta Arith. 26, as quoted by Chen-Gupta-Li arXiv 2507.08296
display (1.4): there are C and B with, for all q ≥ 1, T ≥ 2 and σ₁ ≤ σ ≤ 1,
Σ_{χ mod q} N(σ,T,χ) ≤ C (qT)^{3(1-σ)/(3σ-1)} (log qT)^B. Expected with σ₁ = 3/4. -/
def HuxleyNearOne (σ₁ : ℝ) : Prop :=
  ∃ C : ℝ, ∃ B : ℕ, ∀ q : ℕ+, ∀ T σ : ℝ, 2 ≤ T → σ₁ ≤ σ → σ ≤ 1 →
    allCharacterCount q σ T ≤
      ENNReal.ofReal (C * ((q : ℝ) * T) ^ (huxA σ * (1 - σ)) * Real.log ((q : ℝ) * T) ^ B)

/-- Plain math: A(3/4) = 12/5, Huxley's printed exponent at the junction. PROVED. -/
theorem huxA_three_quarters : huxA (3 / 4) = 12 / 5 := by
  unfold huxA; norm_num

/-- Plain math: A(16/21) = 7/3, Chen's exponent. PROVED. -/
theorem huxA_sixteen : huxA (16 / 21) = 7 / 3 := by
  unfold huxA; norm_num

/-- Plain math: A(4/5) = 15/7. PROVED. -/
theorem huxA_four_fifths : huxA (4 / 5) = 15 / 7 := by
  unfold huxA; norm_num

/-- Plain math: A is decreasing on σ > 1/3: if 1/3 < σ₀ ≤ σ then 3/(3σ-1) ≤ 3/(3σ₀-1).
PROVED. -/
theorem huxA_anti {σ₀ σ : ℝ} (h0 : 1 / 3 < σ₀) (h : σ₀ ≤ σ) : huxA σ ≤ huxA σ₀ := by
  unfold huxA
  apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)

/-- Plain math, sharpness of 16/21: for 1/3 < σ₀ < 16/21, A(σ₀) > 7/3, so Huxley's
exponent at σ₀ does not give the log free input at exponent 7/3. PROVED. -/
theorem huxA_gt_of_lt {σ₀ : ℝ} (h0 : 1 / 3 < σ₀) (h1 : σ₀ < 16 / 21) : 7 / 3 < huxA σ₀ := by
  unfold huxA
  rw [lt_div_iff₀ (by linarith)]
  linarith

/-- Plain math: if Huxley's bound holds on [σ₁, 1], σ₁ ≤ σ₀, 1/3 < σ₀ and
3/(3σ₀ - 1) ≤ A', then Σ_{χ mod q} N(σ,T,χ) ≤ C' (qT)^{A'(1-σ)} (log qT)^B on [σ₀, 1],
that is `LogFreeNearOne A' σ₀`. PROVED. -/
theorem logFree_of_huxley {σ₁ σ₀ A' : ℝ} (hH : HuxleyNearOne σ₁) (h10 : σ₁ ≤ σ₀)
    (hpos : 1 / 3 < σ₀) (hA : huxA σ₀ ≤ A') : LogFreeNearOne A' σ₀ := by
  obtain ⟨C, B, hb⟩ := hH
  refine ⟨max C 0, B, fun q T σ hT hσ hσ1 => ?_⟩
  refine (hb q T σ hT (h10.trans hσ) hσ1).trans (ENNReal.ofReal_le_ofReal ?_)
  set x := (q : ℝ) * T
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast q.pos
  have hx : 1 ≤ x := by nlinarith
  have hl0 : 0 ≤ Real.log x ^ B := pow_nonneg (Real.log_nonneg hx) B
  have hexp : huxA σ * (1 - σ) ≤ A' * (1 - σ) :=
    mul_le_mul_of_nonneg_right ((huxA_anti hpos hσ).trans hA) (by linarith)
  have hp : x ^ (huxA σ * (1 - σ)) ≤ x ^ (A' * (1 - σ)) :=
    Real.rpow_le_rpow_of_exponent_le hx hexp
  have hp0 : 0 ≤ x ^ (huxA σ * (1 - σ)) := Real.rpow_nonneg (by linarith) _
  calc C * x ^ (huxA σ * (1 - σ)) * Real.log x ^ B
      ≤ max C 0 * x ^ (huxA σ * (1 - σ)) * Real.log x ^ B := by
        gcongr; exact le_max_left _ _
    _ ≤ max C 0 * x ^ (A' * (1 - σ)) * Real.log x ^ B := by
        gcongr

/-- Plain math: Huxley's near one bound from σ = 3/4 gives the log free bound with
exponent 7/3 on [16/21, 1]. CONDITIONAL ON `HuxleyNearOne (3/4)`. -/
theorem logFree73_of_huxley (hH : HuxleyNearOne (3 / 4)) : LogFreeNearOne (7 / 3) (16 / 21) :=
  logFree_of_huxley hH (by norm_num) (by norm_num) (le_of_eq huxA_sixteen)

/-- Plain math: the same with exponent 15/7 on [4/5, 1]. CONDITIONAL ON
`HuxleyNearOne (3/4)`. -/
theorem logFree157_of_huxley (hH : HuxleyNearOne (3 / 4)) : LogFreeNearOne (15 / 7) (4 / 5) :=
  logFree_of_huxley hH (by norm_num) (by norm_num) (le_of_eq huxA_four_fifths)

/-- Main result, CONDITIONAL ON a Perelli Theorem 1 reduction `ReductionAt`, `ChenDensity`
and Huxley's printed near one bound `HuxleyNearOne (3/4)`: the target holds for every
h > 2/(7k), against the printed 1/(3k). Plain math: Perelli 1996 Theorem 1 for every
H ≥ N^h, h > 2/(7k). The U-1579 input `LogFreeNearOne (7/3) σ₀` is no longer a hypothesis. -/
theorem thm1_of_chen_huxley {k : ℝ} {Target : ℝ → Prop}
    (hR : ReductionAt (fun h => 1 - k * h / 2) Target) (hZ : ChenDensity)
    (hH : HuxleyNearOne (3 / 4)) (hk : 0 < k) {h : ℝ} (hh : 2 / (7 * k) < h) : Target h := by
  have hc : (7 / 3 : ℝ) * (1 - k * h / 2) < 2 := by
    apply U1578.thm1_condition (by norm_num) hk
    rw [(U1578.chen_values k).1]; exact hh
  exact hR (7 / 3) (7 / 3) (16 / 21) (by norm_num) (by norm_num) hZ
    (logFree73_of_huxley hH) h hc hc

/-- Main result 2, CONDITIONAL ON a Theorem 2 reduction `ReductionAt` with c(h) = 1 - kh,
`ChenDensity` and `HuxleyNearOne (3/4)`: Perelli 1996 Theorem 2 for every H ≥ N^h,
h > 1/(7k), against the printed 1/(6k). -/
theorem thm2_of_chen_huxley {k : ℝ} {Target : ℝ → Prop}
    (hR : ReductionAt (fun h => 1 - k * h) Target) (hZ : ChenDensity)
    (hH : HuxleyNearOne (3 / 4)) (hk : 0 < k) {h : ℝ} (hh : 1 / (7 * k) < h) : Target h := by
  have hc : (7 / 3 : ℝ) * (1 - k * h) < 2 := by
    apply U1578.thm2_condition (by norm_num) hk
    rw [(U1578.chen_values k).2]; exact hh
  exact hR (7 / 3) (7 / 3) (16 / 21) (by norm_num) (by norm_num) hZ
    (logFree73_of_huxley hH) h hc hc

/-- Sanity check, CONDITIONAL ON the reduction and Huxley's (21) in the form
`LogFreeNearOne (12/5) (1/2)` together with its ε form: the printed range h > 1/(3k) of
Perelli's Theorem 1, p. 478, comes back. -/
theorem printed_of_huxley21 {k : ℝ} {Target : ℝ → Prop}
    (hR : ReductionAt (fun h => 1 - k * h / 2) Target) (hZ : ZeroDensityUnif (12 / 5))
    (h21 : LogFreeNearOne (12 / 5) (1 / 2)) (hk : 0 < k) {h : ℝ} (hh : 1 / (3 * k) < h) :
    Target h := by
  have hc : (12 / 5 : ℝ) * (1 - k * h / 2) < 2 := by
    apply U1578.thm1_condition (by norm_num) hk
    rw [(U1578.huxley_reproduces k).1]; exact hh
  exact hR (12 / 5) (12 / 5) (1 / 2) (by norm_num) (by norm_num) hZ h21 h hc hc

/-- Plain math, slack: for every kh > 2/15 the 15/7 condition A'(1 - kh/2) < 2 holds; in
particular for every h > 2/(7k) since then kh > 2/7. PROVED. -/
theorem nearOne_157 {k h : ℝ} (hk : 0 < k) (hh : 2 / (7 * k) < h) :
    (15 / 7 : ℝ) * (1 - k * h / 2) < 2 := by
  have : 2 / 7 < k * h := by
    rw [div_lt_iff₀ (by positivity)] at hh; nlinarith
  nlinarith

/-! ### Vacuity checks -/

/-- Vacuity of the shape of `HuxleyNearOne`: at σ₁ = 1 it holds, the region σ ≤ β < 1 at
σ = 1 being empty; so the hypothesis is satisfiable and the case σ₁ = 1 is excluded by
using σ₁ = 3/4 in the main theorems. PROVED. -/
theorem huxleyNearOne_one : HuxleyNearOne 1 := by
  refine ⟨0, 0, fun q T σ _ hσ hσ1 => ?_⟩
  have hσ' : σ = 1 := le_antisymm hσ1 hσ
  have hz : ∀ χ : DirichletCharacter ℂ (q : ℕ), zeroCount χ σ T = 0 := by
    intro χ
    unfold zeroCount
    have : ∀ ρ : ℂ, ρ ∉ zeroRegion σ T := by
      intro ρ hρ
      unfold zeroRegion at hρ
      obtain ⟨h1, _, h3, _⟩ := hρ
      rw [hσ'] at h1; linarith
    simp [this]
  unfold allCharacterCount
  simp [hz]

/-- Vacuity of the main theorems: at k = 1, h = 29/100 lies strictly between 2/7 and
the printed 1/3, and h = 15/100 strictly between 1/7 and the printed 1/6, so both
conclusions cover exponents the printed theorems do not. PROVED. -/
theorem main_vacuity :
    2 / (7 * (1 : ℝ)) < 29 / 100 ∧ (29 / 100 : ℝ) < 1 / (3 * 1) ∧
      1 / (7 * (1 : ℝ)) < 15 / 100 ∧ (15 / 100 : ℝ) < 1 / (6 * 1) := by
  norm_num

/-- Vacuity of `ReductionAt`: it is satisfiable, by the target that always holds, so the
main theorems are not about an empty hypothesis; and it is not trivially true, since with
the false target it would force the negation of one of its density inputs. PROVED. -/
theorem reductionAt_vacuity (c : ℝ → ℝ) :
    ReductionAt c (fun _ => True) ∧
      (ReductionAt c (fun _ => False) → ∀ A A' σ₀ h : ℝ, 0 < A → σ₀ < 1 → A * c h < 2 →
        A' * c h < 2 → ZeroDensityUnif A → ¬ LogFreeNearOne A' σ₀) := by
  refine ⟨fun _ _ _ _ _ _ _ _ _ _ => trivial, ?_⟩
  intro hR A A' σ₀ h hA hσ h1 h2 hZ hL
  exact hR A A' σ₀ hA hσ hZ hL h h1 h2

end LeanLab.Routes.U1582
#print axioms LeanLab.Routes.U1582.huxA_three_quarters
#print axioms LeanLab.Routes.U1582.huxA_sixteen
#print axioms LeanLab.Routes.U1582.huxA_four_fifths
#print axioms LeanLab.Routes.U1582.huxA_anti
#print axioms LeanLab.Routes.U1582.huxA_gt_of_lt
#print axioms LeanLab.Routes.U1582.logFree_of_huxley
#print axioms LeanLab.Routes.U1582.logFree73_of_huxley
#print axioms LeanLab.Routes.U1582.logFree157_of_huxley
#print axioms LeanLab.Routes.U1582.thm1_of_chen_huxley
#print axioms LeanLab.Routes.U1582.thm2_of_chen_huxley
#print axioms LeanLab.Routes.U1582.printed_of_huxley21
#print axioms LeanLab.Routes.U1582.reductionAt_vacuity
#print axioms LeanLab.Routes.U1582.nearOne_157
#print axioms LeanLab.Routes.U1582.huxleyNearOne_one
#print axioms LeanLab.Routes.U1582.main_vacuity
