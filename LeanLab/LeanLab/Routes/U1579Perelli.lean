/-
U-1579, PC run 20261027T1215Z-9234, track T2 FRONTIER, idea I-0137.
AI wrote this Lean code. Binary Goldbach is OPEN; nothing here is progress on it.

This file makes the U-1578 schema `perelli_thm1_chen` concrete.

* `ZeroDensityUnif A`: for every ε > 0 there is C with, for all moduli q ≥ 1, T ≥ 2 and
  1/2 ≤ σ ≤ 1, Σ_{χ mod q} N(σ,T,χ) ≤ C (qT)^{A(1-σ)+ε}. The count is the lab's
  `PerelliPintz1992.Section6.allCharacterCount`, zeros of the Mathlib `χ.LFunction` with
  multiplicity, σ ≤ β < 1, |γ| ≤ T, imported read only. Twin: Chen, Gupta, Li,
  arXiv 2507.08296, abstract and Theorem 1.2 of v2, Theorem 1.4 of v1 with (1.3), A = 7/3;
  Huxley 1975, Perelli 1996 display (21) p. 485, A = 12/5.
* `LogFreeNearOne A σ₀`: the same count is at most C (qT)^{A(1-σ)} (log qT)^B for
  σ₀ ≤ σ ≤ 1, no additive ε. Perelli's (21) is `LogFreeNearOne (12/5) (1/2)`.
* `Thm1Exact F h`, `Thm2Exact F h`: Perelli 1996 Theorem 1 p. 478 and Theorem 2 p. 479 with
  the lower range N^{1/(3k)+ε}, N^{1/(6k)+ε} replaced by N^h, built from the lab's
  `Perelli1996` definitions, imported read only.
* `PerelliReduction`, `PerelliReduction2`: the reading of Perelli's proof, displays (21),
  (22), (25), (32). These are named Props used as hypotheses, never asserted.

Why two density inputs. Chen's bound carries an additive ε, a factor (qT)^ε = N^{O(ε)}.
Perelli uses (21) twice. In (22) p. 485 at 1 - σ ≍ (B/ε) log L / L it counts bad characters
by L^{O(B/ε)}; there an additive N^{O(ε)} loss is fatal and the value 12/5 is irrelevant. In
(25) the sup over 1/2 ≤ σ ≤ 1 - 10(B/ε) log L / L only needs a saving N^{-(2-Ac)(1-σ)},
which beats N^{O(ε)} only for 1 - σ ≥ η fixed. So the ε form of Chen serves σ ≤ 1 - η and a
log free bound with exponent A' satisfying A' c < 2 is needed for σ ≥ 1 - η.
-/
import Mathlib
import LeanLab.Routes.U1578Sweep
import LeanLab.PerelliPintz1992.Section6
import LeanLab.Perelli1996.StatementsA

namespace LeanLab.Routes.U1579
open Polynomial
open LeanLab.PerelliPintz1992.Section6 (allCharacterCount zeroCount zeroRegion)
open LeanLab.Perelli1996.EncA (Admissible deg nRange err R Fn CF F2 Theorem1 Theorem2)

/-! ### Zero density inputs -/

/-- Chen-Gupta-Li type zero density, uniform in q: for every ε > 0 there is C with
Σ_{χ mod q} N(σ,T,χ) ≤ C (qT)^{A(1-σ)+ε} for q ≥ 1, T ≥ 2, 1/2 ≤ σ ≤ 1. -/
def ZeroDensityUnif (A : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ q : ℕ+, ∀ T σ : ℝ, 2 ≤ T → 1 / 2 ≤ σ → σ ≤ 1 →
    allCharacterCount q σ T ≤ ENNReal.ofReal (C * ((q : ℝ) * T) ^ (A * (1 - σ) + ε))

/-- Log free density on σ₀ ≤ σ ≤ 1: Σ_{χ mod q} N(σ,T,χ) ≤ C (qT)^{A(1-σ)} (log qT)^B.
With A = 12/5, σ₀ = 1/2 this is Perelli 1996 display (21), p. 485, Huxley 1975. -/
def LogFreeNearOne (A σ₀ : ℝ) : Prop :=
  ∃ C : ℝ, ∃ B : ℕ, ∀ q : ℕ+, ∀ T σ : ℝ, 2 ≤ T → σ₀ ≤ σ → σ ≤ 1 →
    allCharacterCount q σ T ≤
      ENNReal.ofReal (C * ((q : ℝ) * T) ^ (A * (1 - σ)) * Real.log ((q : ℝ) * T) ^ B)

/-- Perelli's display (21), p. 485, Huxley's density theorem with logarithms. -/
def HuxleyLog : Prop := LogFreeNearOne (12 / 5) (1 / 2)

/-- Chen-Gupta-Li, arXiv 2507.08296: the ε form at A = 7/3. -/
def ChenDensity : Prop := ZeroDensityUnif (7 / 3)

/-! ### Perelli's theorems with a variable exponent -/

/-- Perelli 1996 Theorem 1, p. 478, at H ≥ N^h: for every A > 0 there are C, N₀ with
Σ_{N^{1/k} ≤ n ≤ N^{1/k}+H} |R(F(n)) - F(n)𝔖(F(n))|² ≤ C H N² (log N)^{-A}
for N ≥ N₀ and N^h ≤ H ≤ N^{1/k}. -/
def Thm1Exact (F : ℤ[X]) (h : ℝ) : Prop :=
  Admissible F → ∀ A : ℝ, 0 < A → ∃ C N0 : ℝ, ∀ N H : ℝ, N0 ≤ N →
    N ^ h ≤ H → H ≤ N ^ (1 / deg F) →
    ∑ n ∈ nRange (N ^ (1 / deg F)) H, err F n ^ 2 ≤ C * H * N ^ 2 / Real.log N ^ A

/-- Perelli 1996 Theorem 2, p. 479, at H ≥ N^h: for A, ε > 0 there are C, N₀ with
|Σ_{N^{1/k} ≤ n ≤ N^{1/k}+H} R(F(n)) - C(F) H N| ≤ C H N (log N)^{-A}
for N ≥ N₀ and N^h ≤ H ≤ N^{1/k-ε}. -/
def Thm2Exact (F : ℤ[X]) (h : ℝ) : Prop :=
  Admissible F → ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C N0 : ℝ, ∀ N H : ℝ, N0 ≤ N →
    N ^ h ≤ H → H ≤ N ^ (1 / deg F - ε) →
    |∑ n ∈ nRange (N ^ (1 / deg F)) H, R (Fn F n) - CF F * H * N| ≤
      C * H * N / Real.log N ^ A

/-! ### The reductions, readings of Perelli's proof -/

/-- CITED reading of Perelli 1996 Section 2, pp. 480-486. The density enters only through
(21), used in (22) at σ near 1, where any log free bound works, and in the sup of (25) with
base N/Q, Q = H^{k/2}, so c = 1 - kh/2. With an ε form for σ ≤ 1 - η and a log free form for
σ ≥ σ₀, the sup saves a power of N on σ ≤ 1 - η when A c < 2 and a power of L on the rest
when A' c < 2; Siegel, the zero free region (19) and the minor arcs are unchanged. This is a
named hypothesis, not proved and not asserted in this file. -/
def PerelliReduction : Prop :=
  ∀ A A' σ₀ : ℝ, 0 < A → σ₀ < 1 → ZeroDensityUnif A → LogFreeNearOne A' σ₀ →
    ∀ F : ℤ[X], ∀ h : ℝ, A * (1 - deg F * h / 2) < 2 → A' * (1 - deg F * h / 2) < 2 →
      Thm1Exact F h

/-- CITED reading of Perelli 1996 Section 3, pp. 486-489, display (32): the same with base
N/Q, Q = H^k L^{-B}, so c = 1 - kh, and moduli q ≤ P = L^B. -/
def PerelliReduction2 : Prop :=
  ∀ A A' σ₀ : ℝ, 0 < A → σ₀ < 1 → ZeroDensityUnif A → LogFreeNearOne A' σ₀ →
    ∀ F : ℤ[X], ∀ h : ℝ, A * (1 - deg F * h) < 2 → A' * (1 - deg F * h) < 2 →
      Thm2Exact F h

/-! ### Proved links -/

theorem deg_pos {F : ℤ[X]} (hF : Admissible F) : 0 < deg F := by
  unfold deg; exact_mod_cast hF.1

/-- Plain math: (log x)^B ≤ δ^{-B} x^ε for x ≥ 1, δ = ε/(B+1). PROVED. -/
theorem log_pow_le {x ε : ℝ} (B : ℕ) (hx : 1 ≤ x) (hε : 0 < ε) :
    Real.log x ^ B ≤ x ^ ε / (ε / (B + 1)) ^ B := by
  set δ := ε / ((B : ℝ) + 1) with hδ
  have hδ0 : 0 < δ := by positivity
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have hl : Real.log x ≤ x ^ δ / δ := Real.log_le_rpow_div (by linarith) hδ0
  have h1 : Real.log x ^ B ≤ (x ^ δ / δ) ^ B := pow_le_pow_left₀ hl0 hl B
  have h2 : (x ^ δ / δ) ^ B = x ^ (δ * B) / δ ^ B := by
    rw [div_pow, ← Real.rpow_natCast (x ^ δ), ← Real.rpow_mul (by linarith)]
  have h3 : δ * B ≤ ε := by
    rw [hδ, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; nlinarith
  have h4 : x ^ (δ * B) ≤ x ^ ε := Real.rpow_le_rpow_of_exponent_le hx h3
  calc Real.log x ^ B ≤ x ^ (δ * B) / δ ^ B := h2 ▸ h1
    _ ≤ x ^ ε / δ ^ B := by gcongr

/-- A log free bound on 1/2 ≤ σ ≤ 1 gives the ε form with the same A. PROVED. -/
theorem zd_of_logfree {A : ℝ} (h : LogFreeNearOne A (1 / 2)) : ZeroDensityUnif A := by
  obtain ⟨C, B, hb⟩ := h
  intro ε hε
  refine ⟨max C 0 / (ε / (B + 1)) ^ B, fun q T σ hT hσ hσ1 => ?_⟩
  refine (hb q T σ hT hσ hσ1).trans (ENNReal.ofReal_le_ofReal ?_)
  set x := (q : ℝ) * T
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast q.pos
  have hx : 1 ≤ x := by nlinarith
  have hx0 : 0 < x := by linarith
  have hl := log_pow_le B hx hε
  have hl0 : 0 ≤ Real.log x ^ B := pow_nonneg (Real.log_nonneg hx) B
  have hp : 0 ≤ x ^ (A * (1 - σ)) := Real.rpow_nonneg hx0.le _
  rw [Real.rpow_add hx0]
  calc C * x ^ (A * (1 - σ)) * Real.log x ^ B
      ≤ max C 0 * x ^ (A * (1 - σ)) * Real.log x ^ B := by
        gcongr; exact le_max_left _ _
    _ ≤ max C 0 * x ^ (A * (1 - σ)) * (x ^ ε / (ε / (B + 1)) ^ B) := by
        gcongr
    _ = max C 0 / (ε / (B + 1)) ^ B * (x ^ (A * (1 - σ)) * x ^ ε) := by ring

/-- Monotonicity: `ZeroDensityUnif A` gives `ZeroDensityUnif A'` for A ≤ A'. So Chen's 7/3
implies the ε form of Huxley's 12/5. PROVED. -/
theorem zd_mono {A A' : ℝ} (h : ZeroDensityUnif A) (hA : A ≤ A') : ZeroDensityUnif A' := by
  intro ε hε
  obtain ⟨C, hC⟩ := h ε hε
  refine ⟨max C 0, fun q T σ hT hσ hσ1 => (hC q T σ hT hσ hσ1).trans
    (ENNReal.ofReal_le_ofReal ?_)⟩
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast q.pos
  have hx : 1 ≤ (q : ℝ) * T := by nlinarith
  have h1 : (0 : ℝ) ≤ ((q : ℝ) * T) ^ (A * (1 - σ) + ε) := Real.rpow_nonneg (by linarith) _
  calc C * ((q : ℝ) * T) ^ (A * (1 - σ) + ε) ≤ max C 0 * ((q : ℝ) * T) ^ (A * (1 - σ) + ε) := by
        gcongr; exact le_max_left _ _
    _ ≤ max C 0 * ((q : ℝ) * T) ^ (A' * (1 - σ) + ε) := by
        apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
        apply Real.rpow_le_rpow_of_exponent_le hx
        nlinarith

/-- Chen's density implies the ε form of Huxley's exponent. PROVED. -/
theorem chen_implies_huxley_eps (h : ChenDensity) : ZeroDensityUnif (12 / 5) :=
  zd_mono h (by norm_num)

/-- The printed Theorem 1 follows from the exact family at h = 1/(3k) + ε. PROVED. -/
theorem theorem1_of_exact {F : ℤ[X]}
    (h : ∀ ε : ℝ, 0 < ε → Thm1Exact F (1 / (3 * deg F) + ε)) : Theorem1 F := by
  intro hF A ε hA hε
  exact h ε hε hF A hA

/-- The printed Theorem 2 follows from the exact family at h = 1/(6k) + ε. PROVED. -/
theorem theorem2_of_exact {F : ℤ[X]}
    (h : ∀ ε : ℝ, 0 < ε → Thm2Exact F (1 / (6 * deg F) + ε)) : Theorem2 F := by
  intro hF A ε hA hε
  exact h ε hε hF A ε hA hε

/-- CONDITIONAL ON `PerelliReduction`, Chen's `ZeroDensityUnif (7/3)` and a log free bound
with exponent 7/3 near σ = 1: Perelli's Theorem 1 holds at every H = N^h, h > 2/(7k). -/
theorem thm1_of_chen (hR : PerelliReduction) (hZ : ChenDensity) {σ₀ : ℝ} (hσ₀ : σ₀ < 1)
    (hL : LogFreeNearOne (7 / 3) σ₀) {F : ℤ[X]} (hF : Admissible F) {h : ℝ}
    (hh : 2 / (7 * deg F) < h) : Thm1Exact F h := by
  have hk := deg_pos hF
  have hc : (7 / 3 : ℝ) * (1 - deg F * h / 2) < 2 := by
    apply U1578.thm1_condition (by norm_num) hk
    rw [(U1578.chen_values (deg F)).1]; exact hh
  exact hR (7 / 3) (7 / 3) σ₀ (by norm_num) hσ₀ hZ hL F h hc hc

/-- CONDITIONAL ON `PerelliReduction2`, Chen's density and a log free bound with exponent
7/3 near σ = 1: Perelli's Theorem 2 at every H = N^h, h > 1/(7k). -/
theorem thm2_of_chen (hR : PerelliReduction2) (hZ : ChenDensity) {σ₀ : ℝ} (hσ₀ : σ₀ < 1)
    (hL : LogFreeNearOne (7 / 3) σ₀) {F : ℤ[X]} (hF : Admissible F) {h : ℝ}
    (hh : 1 / (7 * deg F) < h) : Thm2Exact F h := by
  have hk := deg_pos hF
  have hc : (7 / 3 : ℝ) * (1 - deg F * h) < 2 := by
    apply U1578.thm2_condition (by norm_num) hk
    rw [(U1578.chen_values (deg F)).2]; exact hh
  exact hR (7 / 3) (7 / 3) σ₀ (by norm_num) hσ₀ hZ hL F h hc hc

/-- Sanity check, CONDITIONAL ON `PerelliReduction` and Perelli's (21): the reduction
recovers the printed Theorem 1, range N^{1/(3k)+ε}, p. 478, the lab's `Theorem1`. -/
theorem printed_of_huxley (hR : PerelliReduction) (hH : HuxleyLog) (F : ℤ[X]) :
    Theorem1 F := by
  apply theorem1_of_exact
  intro ε hε hF
  have hk := deg_pos hF
  have hc : (12 / 5 : ℝ) * (1 - deg F * (1 / (3 * deg F) + ε) / 2) < 2 := by
    apply U1578.thm1_condition (by norm_num) hk
    rw [(U1578.huxley_reproduces (deg F)).1]; linarith
  exact hR (12 / 5) (12 / 5) (1 / 2) (by norm_num) (by norm_num) (zd_of_logfree hH) hH F _
    hc hc hF

/-- Sanity check, CONDITIONAL ON `PerelliReduction2` and (21): the printed Theorem 2,
range N^{1/(6k)+ε}, p. 479. -/
theorem printed2_of_huxley (hR : PerelliReduction2) (hH : HuxleyLog) (F : ℤ[X]) :
    Theorem2 F := by
  apply theorem2_of_exact
  intro ε hε hF
  have hk := deg_pos hF
  have hc : (12 / 5 : ℝ) * (1 - deg F * (1 / (6 * deg F) + ε)) < 2 := by
    apply U1578.thm2_condition (by norm_num) hk
    rw [(U1578.huxley_reproduces (deg F)).2]; linarith
  exact hR (12 / 5) (12 / 5) (1 / 2) (by norm_num) (by norm_num) (zd_of_logfree hH) hH F _
    hc hc hF

/-! ### Vacuity checks -/

/-- Vacuity, why σ₀ < 1 is required: at σ₀ = 1 the zero region σ ≤ β < 1 is empty, so
`LogFreeNearOne A 1` holds for every A. PROVED. -/
theorem nearOne_at_one (A : ℝ) : LogFreeNearOne A 1 := by
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

/-- Vacuity of `thm1_of_chen`: F = 2x is admissible of degree 1, h = 29/100 > 2/7, and for
every N ≥ 1 the range N^h ≤ H ≤ N^{1/k} contains H = N, so the conclusion is not empty. -/
theorem thm1_vacuity :
    Admissible (F2 1) ∧ deg (F2 1) = 1 ∧ 2 / (7 * deg (F2 1)) < 29 / 100 ∧
      ∀ N : ℝ, 1 ≤ N → N ^ (29 / 100 : ℝ) ≤ N ∧ N ≤ N ^ (1 / deg (F2 1)) := by
  have hd : deg (F2 1) = 1 := by
    unfold deg; rw [LeanLab.Perelli1996.EncA.F2_natDegree]; norm_num
  refine ⟨LeanLab.Perelli1996.EncA.F2_admissible le_rfl, hd, by rw [hd]; norm_num, fun N hN => ?_⟩
  rw [hd]
  refine ⟨?_, by simp⟩
  calc N ^ (29 / 100 : ℝ) ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
    _ = N := Real.rpow_one N

/-- Vacuity of `thm2_of_chen`: F = 2x, h = 15/100 > 1/7, ε = 1/100, and H = N^{99/100}
lies in N^h ≤ H ≤ N^{1/k-ε} for N ≥ 1. -/
theorem thm2_vacuity :
    1 / (7 * deg (F2 1)) < 15 / 100 ∧
      ∀ N : ℝ, 1 ≤ N → N ^ (15 / 100 : ℝ) ≤ N ^ (99 / 100 : ℝ) ∧
        N ^ (99 / 100 : ℝ) ≤ N ^ (1 / deg (F2 1) - 1 / 100) := by
  have hd : deg (F2 1) = 1 := by
    unfold deg; rw [LeanLab.Perelli1996.EncA.F2_natDegree]; norm_num
  refine ⟨by rw [hd]; norm_num, fun N hN => ⟨?_, ?_⟩⟩
  · exact Real.rpow_le_rpow_of_exponent_le hN (by norm_num)
  · rw [hd]; norm_num

/-- Vacuity of the reduction's numeric hypotheses: at A = A' = 7/3, k = 1, h = 29/100 the
Theorem 1 condition holds, and at Huxley's 12/5 it fails, so the new range is not reached
by (21). PROVED. -/
theorem reduction_vacuity :
    (7 / 3 : ℝ) * (1 - 1 * (29 / 100) / 2) < 2 ∧ ¬ ((12 / 5 : ℝ) * (1 - 1 * (29 / 100) / 2) < 2) ∧
      (7 / 3 : ℝ) * (1 - 1 * (15 / 100)) < 2 ∧ ¬ ((12 / 5 : ℝ) * (1 - 1 * (15 / 100)) < 2) := by
  norm_num

end LeanLab.Routes.U1579
#print axioms LeanLab.Routes.U1579.deg_pos
#print axioms LeanLab.Routes.U1579.log_pow_le
#print axioms LeanLab.Routes.U1579.zd_of_logfree
#print axioms LeanLab.Routes.U1579.zd_mono
#print axioms LeanLab.Routes.U1579.chen_implies_huxley_eps
#print axioms LeanLab.Routes.U1579.theorem1_of_exact
#print axioms LeanLab.Routes.U1579.theorem2_of_exact
#print axioms LeanLab.Routes.U1579.thm1_of_chen
#print axioms LeanLab.Routes.U1579.thm2_of_chen
#print axioms LeanLab.Routes.U1579.printed_of_huxley
#print axioms LeanLab.Routes.U1579.printed2_of_huxley
#print axioms LeanLab.Routes.U1579.nearOne_at_one
#print axioms LeanLab.Routes.U1579.thm1_vacuity
#print axioms LeanLab.Routes.U1579.thm2_vacuity
#print axioms LeanLab.Routes.U1579.reduction_vacuity
