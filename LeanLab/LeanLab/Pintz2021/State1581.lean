/-
P0054 J. Pintz, "An approximate formula for Goldbach's problem with applications",
Riv. Mat. Univ. Parma 12 (2021), 181-199. Unit U-1581, architect run 20261028T0803Z-11675,
track T1 STATE.

This file states the two results of P0054 that were still NOT STATED in the lab:
* `Theorem1_220`: Theorem 1, display (2.20), page 8 of the author copy real.mtak.hu/124681,
  the approximate formula for the major arc integral `R₁(m)` through the generalized exceptional
  zeros `E(H, √X)` of (2.2), (2.19), with the generalized singular series (2.5) to (2.7) and the
  discrete kernel `I(ϱᵢ, ϱⱼ, m)` of (2.10).
* `Theorem2_312`: Theorem 2, display (3.12), page 11, the bound `< 1 - 2ε` for the sum of
  `X^{-δᵢ-δⱼ}` over pairs of generalized exceptional characters induced to one modulus
  `q ≤ X^{7/25}`, in the absence of a Siegel zero.
Both are CITED: P0054 states Theorem 1 without proof, from Pin1 = arXiv 1804.05561 Theorem 1,
and quotes Theorem 2 from Pin2 = arXiv 1804.09084. They are sealed `Prop`s, not theorems.
The formulas were read through the text layer of the author copy, cross checked against the
LaTeX of Pin1 on ar5iv; see STATEMENTS.md, section U-1581, for every reading choice.

Not stated here: (2.21) for `R₁'(m)` with `S'` and `I'`, and the truncated form (2.22) with
`U(χ₁, χ₂, m)`; their exact displays could not be read, see DECOMPOSE lines in PROGRESS.md.

AI-written Lean code, Claude, 2026-10-28. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Pintz2021.Statements
import LeanLab.Pintz2021.Reduction3
import LeanLab.Pintz2021.Lemma1U1369
import LeanLab.Pintz2021.WeightedKernelsTask08
import LeanLab.DERZ1997.Statements

namespace LeanLab.Pintz2021.State1581

open Complex Finset Filter Topology
open LeanLab.Pintz2021.MinorArcs LeanLab.Pintz2021.Reduction3

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Generalized exceptional singularities, (2.1), (2.2), (2.19) -/

/-- A pair `(ϱ, χ)` with `χ` a Dirichlet character of modulus `r ≥ 1`. -/
structure ExcPair where
  r : ℕ
  hr : NeZero r
  χ : DirichletCharacter ℂ r
  ρ : ℂ

/-- The pole `ϱ₀ = 1` with the character `χ₀` mod 1, (2.1). -/
def pole : ExcPair := ⟨1, ⟨one_ne_zero⟩, 1, 1⟩

/-- (2.2): `(ϱ, χ)` is a generalized exceptional zero for `H, U, P, X`: `χ` primitive of
conductor `r ≤ P`, `L(ϱ, χ) = 0`, `ϱ = 1 - δ + iγ`, `δ ≤ H/L`, `|γ| ≤ U`, `L = log X`. -/
def IsExcZero (H U P X : ℝ) (z : ExcPair) : Prop :=
  (z.r : ℝ) ≤ P ∧ z.χ.IsPrimitive ∧ @DirichletCharacter.LFunction z.r z.hr z.χ z.ρ = 0 ∧
    1 - z.ρ.re ≤ H / Real.log X ∧ |z.ρ.im| ≤ U

/-- (2.19): `E(H, U)`, the pole together with the generalized exceptional zeros, at level `P`. -/
def excSet (H U P X : ℝ) : Set ExcPair := insert pole {z | IsExcZero H U P X z}

/-- (2.1): `A(ϱ) = 1` if `ϱ = 1`, else `-1`. -/
def Asign (z : ExcPair) : ℝ := if z.ρ = 1 then 1 else -1

/-- Multiplicity: zeros are listed with their multiplicity, remark after Theorem 1; the pole
counts once. -/
def mult (z : ExcPair) : ℕ :=
  if z = pole then 1 else analyticOrderNatAt (@DirichletCharacter.LFunction z.r z.hr z.χ) z.ρ

/-- `δ = 1 - β` for `ϱ = β + iγ`. -/
def delta (z : ExcPair) : ℝ := 1 - z.ρ.re

/-! ### The generalized singular series, (2.5) to (2.7), Pin1 (2.1) to (2.3) -/

/-- `χ χ₀,q`: the character mod `q` induced by `χ` when `r ∣ q`, else the trivial one. -/
def lift (z : ExcPair) (q : ℕ) : DirichletCharacter ℂ q :=
  if h : z.r ∣ q then DirichletCharacter.changeLevel h z.χ else 1

/-- `c_ψ(m) = ∑_{h=1}^{q} ψ(h) e(hm/q)`, (2.7). -/
def cRam (q : ℕ) (ψ : DirichletCharacter ℂ q) (m : ℤ) : ℂ :=
  ∑ h ∈ Icc 1 q, ψ (h : ZMod q) * LeanLab.PNTPort.LargeSieve.e ((h : ℝ) * m / q)

/-- `τ(ψ) = c_ψ(1)`, (2.7). -/
def tau (q : ℕ) (ψ : DirichletCharacter ℂ q) : ℂ := cRam q ψ 1

/-- (2.6), Pin1 (2.2): `c(χ₁,χ₂,q,m) = φ(q)^{-2} c_{χ₁χ₂χ₀,q}(-m) τ(χ̄₁χ₀,q) τ(χ̄₂χ₀,q)`. -/
def cCoef (z w : ExcPair) (q : ℕ) (m : ℕ) : ℂ :=
  ((Nat.totient q : ℂ) ^ 2)⁻¹ * cRam q (lift z q * lift w q) (-(m : ℤ)) *
    tau q (lift z q)⁻¹ * tau q (lift w q)⁻¹

/-- The partial sums of (2.5): `∑_{q ≤ Q, [r₁, r₂] ∣ q} c(χ₁,χ₂,q,m)`. -/
def singPartial (z w : ExcPair) (m Q : ℕ) : ℂ :=
  ∑ q ∈ (Icc 1 Q).filter (fun q => Nat.lcm z.r w.r ∣ q), cCoef z w q m

/-! ### The major arc integral and the main term -/

/-- `X₁ = X^{1-ε}`, (1.1). -/
def X1 (ε X : ℝ) : ℝ := X ^ (1 - ε)

/-- `R₁(m) = ∫_𝔐 S(α)² e(-mα) dα`, (1.8), with `S` of (1.1) over `X₁ < p ≤ X`, the major arcs
(1.3) at level `P` and `Q = X/P`. -/
def R1maj (ε X P : ℝ) (m : ℕ) : ℂ :=
  R1 (S (X1 ε X) X) (Lemma1U1369.majorArcs P (X / P))ᶜ m

/-- The main term of (2.20), with the series values `Sg` and the discrete kernel of (2.10):
`∑_{i,j ∈ E} A(ϱᵢ)A(ϱⱼ) 𝔖(χᵢ,χⱼ,m) I(ϱᵢ,ϱⱼ,m)`, each zero repeated by its multiplicity. -/
def mainTerm (E : Set ExcPair) (Sg : ExcPair → ExcPair → ℕ → ℂ) (ε X : ℝ) (m : ℕ) : ℂ :=
  ∑ᶠ (z) (_ : z ∈ E), ∑ᶠ (w) (_ : w ∈ E),
    ((mult z * mult w : ℕ) : ℂ) * (Asign z : ℂ) * (Asign w : ℂ) * Sg z w m *
      WeightedKernelsTask08.weightedKernel (X1 ε X) X z.ρ w.ρ m false

/-! ### Theorem 1, display (2.20), page 8 -/

/-- The range of the parameters of Theorem 1: `H₀ ≤ H ≤ (log X)/2`, `X ≥ X₀`,
`1 ≤ P₀ ≤ X^{4/9-ε}`. The upper bound on `H` is a conservative restriction, see STATEMENTS.md. -/
def Thm1Hyp (ε H0 X0 H X P0 : ℝ) : Prop :=
  H0 ≤ H ∧ H ≤ Real.log X / 2 ∧ X0 ≤ X ∧ 1 ≤ P0 ∧ P0 ≤ X ^ (4 / 9 - ε)

/-- **Theorem 1**, (2.20), CITED from Pin1. For every sufficiently small `ε > 0` there are
`c_ε > 0` and constants such that for `P₀ ≤ X^{4/9-ε}` one can choose `P ∈ [P₀X^{-ε}, P₀]` with:
`E = E(H, √X)` at level `P` is finite, every generalized singular series of (2.5) converges, and
for all `m ≤ X`
`R₁(m) = ∑_{i,j ∈ E} A(ϱᵢ)A(ϱⱼ) 𝔖(χᵢ,χⱼ,m) I(ϱᵢ,ϱⱼ,m) + O_ε(𝔖(m) X e^{-c_ε H}) + O_ε(X^{1-ε})`. -/
def Theorem1_220 : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c H0 C X0 : ℝ, 0 < c ∧ ∀ H X P0 : ℝ, Thm1Hyp ε H0 X0 H X P0 →
      ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
        (excSet H (Real.sqrt X) P X).Finite ∧
        ∃ Sg : ExcPair → ExcPair → ℕ → ℂ,
          (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ,
            Tendsto (singPartial z w m) atTop (𝓝 (Sg z w m))) ∧
          ∀ m : ℕ, (m : ℝ) ≤ X →
            ‖R1maj ε X P m - mainTerm (excSet H (Real.sqrt X) P X) Sg ε X m‖ ≤
              C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε))

/-! ### Theorem 2, display (3.12), page 11 -/

/-- Absence of a Siegel zero at level `h`, as in Pin2 (2.16): no real primitive character `χ`
of conductor `≤ X^{4/9-ε}` has a real zero `β` with `1 - h/log X < β < 1`. -/
def NoSiegel (h ε X : ℝ) : Prop :=
  ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (β : ℝ), χ.IsPrimitive → χ ^ 2 = 1 →
    (r : ℝ) ≤ X ^ (4 / 9 - ε) → DirichletCharacter.LFunction χ β = 0 → β < 1 →
      β ≤ 1 - h / Real.log X

/-- The sum of (3.12) at modulus `q`: over pairs of generalized exceptional zeros whose
characters induce characters mod `q`, `ϱᵢ ≠ 1` or `ϱⱼ ≠ 1`, `cond χᵢχⱼ < Ccond`, of
`X^{-δᵢ-δⱼ}`, with multiplicity. -/
def sum312 (E : Set ExcPair) (Ccond X : ℝ) (q : ℕ) : ℝ :=
  ∑ᶠ (z) (_ : z ∈ E), ∑ᶠ (w) (_ : w ∈ E),
    if z.r ∣ q ∧ w.r ∣ q ∧ (z.ρ ≠ 1 ∨ w.ρ ≠ 1) ∧
        (((lift z q * lift w q).conductor : ℕ) : ℝ) < Ccond then
      ((mult z * mult w : ℕ) : ℝ) * X ^ (-(delta z + delta w))
    else 0

/-- **Theorem 2**, (3.12), CITED from Pin2, with the conductor bound `C(ε)` of (3.10), (3.11)
as the explicit function `Cc`: for small `ε` there are `h > 0`, `H > 0` and `X₀` such that for
`X > X₀`, in the absence of a Siegel zero, for every `q ≤ X^{7/25}`, with `E = E(H, √X)` at level
`P = X^{7/25}`, the sum (3.12) is below `1 - 2ε`. -/
def Theorem2_312 (Cc : ℝ → ℝ) : Prop :=
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ h H X0 : ℝ, 0 < h ∧ 0 < H ∧ ∀ X : ℝ, X0 < X → NoSiegel h ε X →
      (excSet H (Real.sqrt X) (X ^ (7 / 25 : ℝ)) X).Finite ∧
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ X ^ (7 / 25 : ℝ) →
        sum312 (excSet H (Real.sqrt X) (X ^ (7 / 25 : ℝ)) X) (Cc ε) X q < 1 - 2 * ε

/-! ### Vacuity instances, PROVED -/

/-- The pole lies in every `E(H, U)`, so the main term of (2.20) is never an empty sum. -/
theorem pole_mem_excSet (H U P X : ℝ) : pole ∈ excSet H U P X := Set.mem_insert _ _

theorem Asign_pole : Asign pole = 1 := by simp [Asign, pole]

theorem mult_pole : mult pole = 1 := by simp [mult]

/-- The hypotheses of Theorem 1 hold together: for every `ε ∈ (0, 4/9)` and all constants
`H₀, X₀` there are `H, X, P₀` with `Thm1Hyp`, and the interval `[P₀X^{-ε}, P₀]` is nonempty. -/
theorem thm1Hyp_inhabited {ε : ℝ} (hε : 0 < ε) (hε' : ε < 4 / 9) (H0 X0 : ℝ) :
    ∃ H X P0 : ℝ, Thm1Hyp ε H0 X0 H X P0 ∧ P0 * X ^ (-ε) ≤ P0 := by
  set H := max H0 0 with hH
  set X := max (max X0 1) (Real.exp (2 * H)) with hX
  have hX1 : 1 ≤ X := le_trans (le_max_right X0 1) (le_max_left _ _)
  have hlog : 2 * H ≤ Real.log X := by
    have h1 : Real.exp (2 * H) ≤ X := le_max_right _ _
    have := Real.log_le_log (Real.exp_pos _) h1
    rwa [Real.log_exp] at this
  refine ⟨H, X, 1, ⟨le_max_left _ _, by linarith, ?_, le_refl _, ?_⟩, ?_⟩
  · exact le_trans (le_max_left X0 1) (le_max_left _ _)
  · exact Real.one_le_rpow hX1 (by linarith)
  · have : X ^ (-ε) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hX1 (by linarith)
    linarith

/-- The parameter range of Theorem 2 is inhabited above every `X₀`: `q = 1` and `X > X₀`. -/
theorem thm2_range_inhabited (X0 : ℝ) :
    ∃ X : ℝ, X0 < X ∧ 1 < X ∧ ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ X ^ (7 / 25 : ℝ) := by
  refine ⟨max X0 1 + 1, by linarith [le_max_left X0 1], by linarith [le_max_right X0 1], 1,
    le_refl _, ?_⟩
  push_cast
  exact Real.one_le_rpow (by linarith [le_max_right X0 1]) (by norm_num)

/-- The no Siegel zero hypothesis of Theorem 2 is consistent with every `X > 1` and every
`0 < h ≤ (log X)/2`: it follows from GRH, `DERZ1997.GRH`, a statement not known to be false.
This is a consistency check relative to GRH, not an unconditional instance. -/
theorem noSiegel_of_GRH (hG : LeanLab.DERZ1997.GRH) {h ε X : ℝ} (hX : 1 < X) (hh : 0 < h)
    (hhX : h ≤ Real.log X / 2) : NoSiegel h ε X := by
  intro r _ χ β _ _ _ hz h1
  have hL : 0 < Real.log X := Real.log_pos hX
  have hq : h / Real.log X ≤ 1 / 2 := by
    rw [div_le_iff₀ hL]; linarith
  by_cases h0 : 0 < β
  · have := hG r χ β hz (by simpa using h0) (by simpa using h1)
    simp at this
    linarith
  · push Not at h0
    have : 0 < h / Real.log X := div_pos hh hL
    linarith

end

end LeanLab.Pintz2021.State1581

#print axioms LeanLab.Pintz2021.State1581.pole_mem_excSet
#print axioms LeanLab.Pintz2021.State1581.Asign_pole
#print axioms LeanLab.Pintz2021.State1581.mult_pole
#print axioms LeanLab.Pintz2021.State1581.thm1Hyp_inhabited
#print axioms LeanLab.Pintz2021.State1581.thm2_range_inhabited
#print axioms LeanLab.Pintz2021.State1581.noSiegel_of_GRH
