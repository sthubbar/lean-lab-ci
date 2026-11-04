/-
The three cited zero density estimates in P0089, pages 226 and 229.
Source https://www.rivmat.unipr.it/fulltext/2004-3s/pdf/13.pdf.
AI wrote the Lean code. Goldbach is open. No density estimate is asserted.
New paper Prop definitions require Claude source review before merge.
-/
import LeanLab.Languasco2004.StatementsA

namespace LeanLab.Languasco2004.Density279
open Real
open LeanLab.LanguascoPerelli1996
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Pages 226 and 227: N of sigma, T and chi counts zeros with
beta at least sigma and absolute height at most T, with multiplicity.
The principal character pole at 1 is excluded from the meromorphic zero count.
The extended nonnegative sum is infinity for an infinite positive count.
It never replaces an infinite zero set by an empty finite sum. -/
def zeroCount {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (σ T : ℝ) : ENNReal :=
  ∑' ρ : ℂ, if DirichletCharacter.LFunction χ ρ = 0 ∧ σ ≤ ρ.re ∧
    |ρ.im| ≤ T ∧ (χ ≠ 1 ∨ ρ ≠ 1) then (mult χ ρ : ENNReal) else 0

/-- Page 227: the starred character sum runs over primitive characters only.
The zero modulus is assigned zero and is excluded by the outer interval. -/
def primitiveCount (q : ℕ) (σ T : ℝ) : ENNReal :=
  if h : q = 0 then 0 else
    letI : NeZero q := ⟨h⟩
    ∑ χ : DirichletCharacter ℂ q, if χ.IsPrimitive then zeroCount χ σ T else 0

/-- Pages 226 and 229: sum the primitive zero counts over positive q at most P. -/
def totalCount (P σ T : ℝ) : ENNReal :=
  ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, primitiveCount q σ T

/-- Page 226 display 1, cited from Ramachandra 1973 reference 22.
The large parameter reading uses P and T at least 2. This is a cited statement,
not a theorem, and the finite upper bound also excludes an infinite zero count. -/
def RamachandraDensity : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ P T σ : ℝ, 2 ≤ P → 2 ≤ T → 1 / 2 ≤ σ → σ ≤ 1 →
    totalCount P σ T ≤ ENNReal.ofReal
      (C * (P ^ 2 * T) ^ ((12 / 5 : ℝ) * (1 - σ)) * Real.log (P * T) ^ (22 : ℕ))

/-- Page 226 display 2, cited from Peneva 2001 and the 2004 corrigendum,
references 16 and 17. The base is P to the fourth power times T. -/
def PenevaDensity : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∀ P T σ : ℝ, 2 ≤ P → 2 ≤ T → 27 / 28 ≤ σ → σ ≤ 1 →
    totalCount P σ T ≤ ENNReal.ofReal
      (C * (P ^ 4 * T) ^ ((3 / 2 : ℝ) * (1 - σ)))

/-- Page 229 display 3, cited from Jutila 1977 reference 9.
The constant is allowed to depend on the positive epsilon. -/
def JutilaDensity : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 < C ∧ ∀ P T σ : ℝ,
    2 ≤ P → 2 ≤ T → 4 / 5 ≤ σ → σ ≤ 1 →
    totalCount P σ T ≤ ENNReal.ofReal
      (C * (P ^ 2 * T) ^ ((2 + ε) * (1 - σ)))

/-- At sigma equal to 1, Mathlib nonvanishing excludes every proper zero.
This checks the upper endpoint without assuming any density estimate. -/
theorem zeroCount_at_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (T : ℝ) :
    zeroCount χ 1 T = 0 := by
  unfold zeroCount
  apply ENNReal.tsum_eq_zero.mpr
  intro ρ
  split_ifs with h
  · exfalso
    exact (χ.LFunction_ne_zero_of_one_le_re h.2.2.2 h.2.1) h.1
  · rfl

/-- The primitive sum also vanishes at the upper sigma endpoint. -/
theorem totalCount_at_one (P T : ℝ) : totalCount P 1 T = 0 := by
  simp [totalCount, primitiveCount, zeroCount_at_one]

/-- Concrete parameter domains for the three cited displays. -/
theorem density_parameter_instances :
    (2 : ℝ) ≤ 2 ∧ (1 / 2 : ℝ) ≤ 1 ∧ (27 / 28 : ℝ) ≤ 1 ∧
      (4 / 5 : ℝ) ≤ 1 ∧ (0 : ℝ) < 1 := by norm_num

#print axioms zeroCount
#print axioms primitiveCount
#print axioms totalCount
#print axioms RamachandraDensity
#print axioms PenevaDensity
#print axioms JutilaDensity
#print axioms zeroCount_at_one
#print axioms totalCount_at_one
#print axioms density_parameter_instances
end
end LeanLab.Languasco2004.Density279
