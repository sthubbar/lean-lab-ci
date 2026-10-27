import Mathlib
import LeanLab.Zhao2025.Zhao2025U6902Interval

/-!
# Zhao 2025, the R bounds (3.38), (3.42), (3.43) as real formulas, and their certified values

G. Zhao, arXiv 2511.05631v2, a preprint.  Unit U-6902, CLOUD MANUAL-M2, T2.  AI wrote the Lean code.
Binary Goldbach is open.

With `F_x(z) = G(z/x)`, `ψ = F_x(Λ-λ₀)/F_x(-λ₀)`, `ψ* = F_x(λ*-λ₀)/F_x(-λ₀)`,
`ψⱼ = F_x(λⱼ-λ₀)/F_x(-λ₀)`, `ξ = (ϕ/2) f_x(0)/F_x(-λ₀) = (8/45) x/F_x(-λ₀)`, `Δ = ψ - ξ`,
`λ₀ = λ₁`, the right sides of (3.38), (3.42), (3.43) are `R38`, `R42`, `R43` below, transcribed from
p. 12 and p. 13 of the arXiv PDF.  `chkR` builds the matching `Ex` terms and checks their intervals.

* `R43_le`, `R42_le`, `R38_le`, PROVED: a passing check bounds the formula by the target.
* `Rbound_of_342_343`, `Rbound_of_338`, CONDITIONAL ON Zhao's (3.42) or (3.43), resp. (3.38), as
  hypotheses: `R(Λ) ≤ target`.
-/

namespace LeanLab.Zhao2025.U6900

open LeanLab.Zhao2025.U6841

noncomputable def eW (t : ℝ) : ℝ := Real.exp (-(10 / 3 * t))

noncomputable def psiR (x L l0 : ℝ) : ℝ := Gz ((L - l0) / x) / Gz (-l0 / x)

noncomputable def xiR (x l0 : ℝ) : ℝ := 8 / 45 * x / Gz (-l0 / x)

noncomputable def firstR (L l1 l2 : ℝ) : ℝ := (eW l1 - eW L) + (eW l2 - eW L)

noncomputable def s12R (x L l1 l2 : ℝ) : ℝ :=
  (psiR x l1 l1 - psiR x L l1) + (psiR x l2 l1 - psiR x L l1)

noncomputable def coefR (x L l1 ls : ℝ) : ℝ := (eW ls - eW L) / (psiR x ls l1 - psiR x L l1)

/-- (3.43) with `N*`. -/
noncomputable def R43 (x L l1 l2 ls : ℝ) (Ns : ℕ) : ℝ :=
  firstR L l1 l2 + coefR x L l1 ls *
    ((1 - ((Ns : ℝ) + 1) * ((psiR x L l1 - xiR x l1) * (psiR x L l1 - xiR x l1))) /
        (2 * (psiR x L l1 - xiR x l1)) -
      s12R x L l1 l2)

/-- (3.42) with `N*`. -/
noncomputable def R42 (L l1 l2 ls : ℝ) (Ns : ℕ) : ℝ :=
  firstR L l1 l2 + ((Ns : ℝ) - 2) * (eW ls - eW L)

/-- (3.38). -/
noncomputable def R38 (x L l1 l2 ls : ℝ) : ℝ :=
  firstR L l1 l2 + coefR x L l1 ls *
    ((1 - xiR x l1) / (2 * (psiR x L l1 - xiR x l1)) - s12R x L l1 l2)

/-! ### The `Ex` terms -/

def eG1 (x l1 : ℚ) : Ex := .g (-l1 / x)
def ePsi (x L l1 : ℚ) : Ex := .dv (.g ((L - l1) / x)) (eG1 x l1)
def eXi (x l1 : ℚ) : Ex := .dv (.c (8 / 45 * x)) (eG1 x l1)
def eD (x L l1 : ℚ) : Ex := .sub (ePsi x L l1) (eXi x l1)
def eFirst (L l1 l2 : ℚ) : Ex := .add (.sub (.ex l1) (.ex L)) (.sub (.ex l2) (.ex L))
def eS12 (x L l1 l2 : ℚ) : Ex :=
  .add (.sub (ePsi x l1 l1) (ePsi x L l1)) (.sub (ePsi x l2 l1) (ePsi x L l1))
def eCoef (x L l1 ls : ℚ) : Ex := .dv (.sub (.ex ls) (.ex L)) (.sub (ePsi x ls l1) (ePsi x L l1))
def eR43 (x L l1 l2 ls : ℚ) (Ns : ℕ) : Ex :=
  .add (eFirst L l1 l2) (.mul (eCoef x L l1 ls) (.pos (.sub
    (.dv (.sub (.c 1) (.mul (.c ((Ns : ℚ) + 1)) (.mul (eD x L l1) (eD x L l1))))
      (.mul (.c 2) (eD x L l1))) (eS12 x L l1 l2))))
def eR42 (L l1 l2 ls : ℚ) (Ns : ℕ) : Ex :=
  .add (eFirst L l1 l2) (.mul (.c ((Ns : ℚ) - 2)) (.sub (.ex ls) (.ex L)))
def eR38 (x L l1 l2 ls : ℚ) : Ex :=
  .add (eFirst L l1 l2) (.mul (eCoef x L l1 ls) (.pos (.sub
    (.dv (.sub (.c 1) (eXi x l1)) (.mul (.c 2) (eD x L l1))) (eS12 x L l1 l2))))
/-- `Δ² - ξ`, for the validity condition of (3.38). -/
def eV (x L l1 : ℚ) : Ex := .sub (.mul (eD x L l1) (eD x L l1)) (eXi x l1)

/-- The check for (3.42) and (3.43): validity `x ≥ max(4λ₀/5, 3/5)`, and both bounds `≤ target`. -/
def chkR4 (x L l1 l2 ls : ℚ) (Ns : ℕ) (t : ℚ) : Bool :=
  decide (4 * l1 / 5 ≤ x) && decide (3 / 5 ≤ x) && decide (2 ≤ Ns) &&
  (eR43 x L l1 l2 ls Ns).ok && decide ((eR43 x L l1 l2 ls Ns).iv.2 ≤ t) &&
  (eR42 L l1 l2 ls Ns).ok && decide ((eR42 L l1 l2 ls Ns).iv.2 ≤ t)

/-- The check for (3.38): validity `x ≥ max(4λ₀/5, 3/5)`, `Δ > 0`, `Δ² > ξ`, and the bound `≤ target`. -/
def chkR8 (x L l1 l2 ls : ℚ) (t : ℚ) : Bool :=
  decide (4 * l1 / 5 ≤ x) && decide (3 / 5 ≤ x) &&
  (eD x L l1).ok && decide (0 < (eD x L l1).iv.1) &&
  (eV x L l1).ok && decide (0 < (eV x L l1).iv.1) &&
  (eR38 x L l1 l2 ls).ok && decide ((eR38 x L l1 l2 ls).iv.2 ≤ t)

theorem val_psi (x L l1 : ℚ) : (ePsi x L l1).val = psiR x L l1 := by
  simp only [ePsi, eG1, Ex.val, psiR]; push_cast; ring_nf

theorem val_xi (x l1 : ℚ) : (eXi x l1).val = xiR x l1 := by
  simp only [eXi, eG1, Ex.val, xiR]; push_cast; ring_nf

theorem val_D (x L l1 : ℚ) : (eD x L l1).val = psiR x L l1 - xiR x l1 := by
  simp only [eD, Ex.val, val_psi, val_xi]

theorem val_first (L l1 l2 : ℚ) : (eFirst L l1 l2).val = firstR L l1 l2 := by
  simp only [eFirst, Ex.val, firstR, eW]

theorem val_s12 (x L l1 l2 : ℚ) : (eS12 x L l1 l2).val = s12R x L l1 l2 := by
  simp only [eS12, Ex.val, val_psi, s12R]

theorem val_coef (x L l1 ls : ℚ) : (eCoef x L l1 ls).val = coefR x L l1 ls := by
  simp only [eCoef, Ex.val, val_psi, coefR, eW]

theorem pos_ok_mul {a b : ℝ} (ha : 0 ≤ a) : a * b ≤ a * max b 0 :=
  mul_le_mul_of_nonneg_left (le_max_left _ _) ha

theorem coef_nonneg_of_ok (x L l1 ls : ℚ) (b : Ex)
    (h : (Ex.mul (eCoef x L l1 ls) b).ok = true) : 0 ≤ coefR x L l1 ls := by
  simp only [Ex.ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hc, -⟩, hc0⟩, -⟩ := h
  have := (Ex.sound _ hc).1
  rw [val_coef] at this
  have hc0' : (0 : ℝ) ≤ ((eCoef x L l1 ls).iv.1 : ℝ) := by exact_mod_cast hc0
  linarith

/-- PROVED: a passing check gives `R43 ≤ t` and `R42 ≤ t`. -/
theorem R4_le (x L l1 l2 ls : ℚ) (Ns : ℕ) (t : ℚ) (h : chkR4 x L l1 l2 ls Ns t = true) :
    R43 x L l1 l2 ls Ns ≤ t ∧ R42 L l1 l2 ls Ns ≤ t := by
  simp only [chkR4, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, _⟩, h43⟩, h43t⟩, h42⟩, h42t⟩ := h
  have s43 := (Ex.sound _ h43).2
  have s42 := (Ex.sound _ h42).2
  have h43t' : (((eR43 x L l1 l2 ls Ns).iv.2 : ℚ) : ℝ) ≤ t := by exact_mod_cast h43t
  have h42t' : (((eR42 L l1 l2 ls Ns).iv.2 : ℚ) : ℝ) ≤ t := by exact_mod_cast h42t
  have hm : (Ex.mul (eCoef x L l1 ls) (.pos (.sub
      (.dv (.sub (.c 1) (.mul (.c ((Ns : ℚ) + 1)) (.mul (eD x L l1) (eD x L l1))))
        (.mul (.c 2) (eD x L l1))) (eS12 x L l1 l2)))).ok = true := by
    simp only [eR43, Ex.ok, Bool.and_eq_true] at h43 ⊢; exact h43.2
  have hcoef := coef_nonneg_of_ok _ _ _ _ _ hm
  constructor
  · have hv : (eR43 x L l1 l2 ls Ns).val = firstR L l1 l2 + coefR x L l1 ls *
        max ((1 - ((Ns : ℝ) + 1) * ((psiR x L l1 - xiR x l1) * (psiR x L l1 - xiR x l1))) /
          (2 * (psiR x L l1 - xiR x l1)) - s12R x L l1 l2) 0 := by
      simp only [eR43, Ex.val, val_first, val_coef, val_D, val_s12]; push_cast; ring_nf
    have := pos_ok_mul (b := (1 - ((Ns : ℝ) + 1) * ((psiR x L l1 - xiR x l1) *
      (psiR x L l1 - xiR x l1))) / (2 * (psiR x L l1 - xiR x l1)) - s12R x L l1 l2) hcoef
    unfold R43; rw [hv] at s43; linarith
  · have hv : (eR42 L l1 l2 ls Ns).val = R42 L l1 l2 ls Ns := by
      simp only [eR42, Ex.val, val_first, R42, eW]; push_cast; ring_nf
    rw [hv] at s42; linarith

/-- PROVED: a passing check gives `Δ > 0`, `Δ² > ξ` and `R38 ≤ t`. -/
theorem R8_le (x L l1 l2 ls : ℚ) (t : ℚ) (h : chkR8 x L l1 l2 ls t = true) :
    0 < psiR x L l1 - xiR x l1 ∧ xiR x l1 < (psiR x L l1 - xiR x l1) ^ 2 ∧
      R38 x L l1 l2 ls ≤ t := by
  simp only [chkR8, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨_, _⟩, hDok⟩, hD0⟩, hV⟩, hV0⟩, h38⟩, h38t⟩ := h
  have sD := (Ex.sound _ hDok).1
  rw [val_D] at sD
  have hD0' : (0 : ℝ) < ((eD x L l1).iv.1 : ℝ) := by exact_mod_cast hD0
  have sV := (Ex.sound _ hV).1
  have hV0' : (0 : ℝ) < ((eV x L l1).iv.1 : ℝ) := by exact_mod_cast hV0
  have hvV : (eV x L l1).val = (psiR x L l1 - xiR x l1) ^ 2 - xiR x l1 := by
    simp only [eV, Ex.val, val_D, val_xi]; ring
  have s38 := (Ex.sound _ h38).2
  have h38t' : (((eR38 x L l1 l2 ls).iv.2 : ℚ) : ℝ) ≤ t := by exact_mod_cast h38t
  have hm : (Ex.mul (eCoef x L l1 ls) (.pos (.sub
      (.dv (.sub (.c 1) (eXi x l1)) (.mul (.c 2) (eD x L l1))) (eS12 x L l1 l2)))).ok = true := by
    simp only [eR38, Ex.ok, Bool.and_eq_true] at h38 ⊢; exact h38.2
  have hcoef := coef_nonneg_of_ok _ _ _ _ _ hm
  refine ⟨by linarith, by linarith, ?_⟩
  have hv : (eR38 x L l1 l2 ls).val = firstR L l1 l2 + coefR x L l1 ls *
      max ((1 - xiR x l1) / (2 * (psiR x L l1 - xiR x l1)) - s12R x L l1 l2) 0 := by
    simp only [eR38, Ex.val, val_first, val_coef, val_D, val_s12, val_xi]; push_cast; ring_nf
  have := pos_ok_mul (b := (1 - xiR x l1) / (2 * (psiR x L l1 - xiR x l1)) - s12R x L l1 l2) hcoef
  unfold R38; rw [hv] at s38; linarith

/-- CONDITIONAL ON Zhao's dichotomy (3.42) or (3.43) at this `x` and `N*`, as the hypothesis
`hR`: `R(Λ) ≤ t`. -/
theorem Rbound_of_342_343 (x L l1 l2 ls : ℚ) (Ns : ℕ) (t : ℚ) (h : chkR4 x L l1 l2 ls Ns t = true)
    (R : ℝ) (hR : R ≤ R42 L l1 l2 ls Ns ∨ R ≤ R43 x L l1 l2 ls Ns) : R ≤ t := by
  obtain ⟨h43, h42⟩ := R4_le x L l1 l2 ls Ns t h
  rcases hR with hR | hR <;> linarith

/-- CONDITIONAL ON Zhao's (3.38) at this `x`, as the hypothesis `hR`, whose validity condition
`Δ > 0`, `Δ² > ξ`, that is `Δ > √ξ`, the check also proves: `R(Λ) ≤ t`. -/
theorem Rbound_of_338 (x L l1 l2 ls : ℚ) (t : ℚ) (h : chkR8 x L l1 l2 ls t = true)
    (R : ℝ) (hR : 0 < psiR x L l1 - xiR x l1 → xiR x l1 < (psiR x L l1 - xiR x l1) ^ 2 →
      R ≤ R38 x L l1 l2 ls) : R ≤ t := by
  obtain ⟨hD, hv, h38⟩ := R8_le x L l1 l2 ls t h
  linarith [hR hD hv]

end LeanLab.Zhao2025.U6900
