import LeanLab.ChenDoubleSieve.Burst9Psi2Scalar
import LeanLab.ChenDoubleSieve.Burst9I2

/-!
# Burst 9: the four Ψ₂ lower bounds of Table 1 from finer pieces

Source: Wu 2004, arXiv 0705.1652, Lemma 5.2, page 26, the definition of `Ψ₂`, and Table 1,
page 30, rows 1 to 4. `table1_Psi2_zero` is `Burst4Split.table1_Psi2` with the extra hypothesis
`ZeroBelowOne ω`, Wu's convention `ω(u) = 0` for `u < 1`; see the QUESTION in the note on why
the version without it cannot hold for every `ω` allowed by `IsBuchstab`. It is proved from the
PROVED scalar certificates `scalar_row0` to `scalar_row3` and the 52 `I₂` bounds of `Burst9I2`,
32 of them LEAF declarations. AI wrote the Lean code. Binary Goldbach is OPEN.
-/

noncomputable section
open Real Set Finset MeasureTheory
namespace LeanLab.ChenDoubleSieve.Burst9Psi2
open Wu04Functional

/-- Table 1 row 1: `0.015826357 ≤ Ψ₂`, Wu 2004 Lemma 5.2 and Table 1, page 30.
CONDITIONAL ON IsBuchstab, ZeroBelowOne and the LEAF `I₂` bounds of row 1. -/
theorem Psi2_row0 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    (0.015826357 : ℝ) ≤ Psi2 ω (tableParams 0) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := scalar_row0
  have hI := I2_sum_row0 hω hz
  unfold Psi2
  norm_num at h1 h2 h3 h4 h5 hI ⊢
  linarith

/-- Table 1 row 2: `0.015247971 ≤ Ψ₂`, Wu 2004 Lemma 5.2 and Table 1, page 30.
CONDITIONAL ON IsBuchstab, ZeroBelowOne and the LEAF `I₂` bounds of row 2. -/
theorem Psi2_row1 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    (0.015247971 : ℝ) ≤ Psi2 ω (tableParams 1) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := scalar_row1
  have hI := I2_sum_row1 hω hz
  unfold Psi2
  norm_num at h1 h2 h3 h4 h5 hI ⊢
  linarith

/-- Table 1 row 3: `0.013898757 ≤ Ψ₂`, Wu 2004 Lemma 5.2 and Table 1, page 30.
CONDITIONAL ON IsBuchstab, ZeroBelowOne and the LEAF `I₂` bounds of row 3. -/
theorem Psi2_row2 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    (0.013898757 : ℝ) ≤ Psi2 ω (tableParams 2) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := scalar_row2
  have hI := I2_sum_row2 hω hz
  unfold Psi2
  norm_num at h1 h2 h3 h4 h5 hI ⊢
  linarith

/-- Table 1 row 4: `0.011776059 ≤ Ψ₂`, Wu 2004 Lemma 5.2 and Table 1, page 30.
CONDITIONAL ON IsBuchstab, ZeroBelowOne and the LEAF `I₂` bounds of row 4. -/
theorem Psi2_row3 {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    (0.011776059 : ℝ) ≤ Psi2 ω (tableParams 3) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := scalar_row3
  have hI := I2_sum_row3 hω hz
  unfold Psi2
  norm_num at h1 h2 h3 h4 h5 hI ⊢
  linarith

/-- **The four Ψ₂ entries of Table 1**, Wu 2004 page 30, rows 1 to 4, in the form of
`Burst4Split.table1_Psi2` plus `ZeroBelowOne ω`. CONDITIONAL ON the 32 LEAF `I₂` bounds. -/
theorem table1_Psi2_zero {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω) :
    ∀ i : Fin 4, tablePsi ⟨i.val, by omega⟩ ≤ Psi2 ω (tableParams i) := by
  intro i
  fin_cases i
  · have := Psi2_row0 hω hz; norm_num [tablePsi] at this ⊢; exact this
  · have := Psi2_row1 hω hz; norm_num [tablePsi] at this ⊢; exact this
  · have := Psi2_row2 hω hz; norm_num [tablePsi] at this ⊢; exact this
  · have := Psi2_row3 hω hz; norm_num [tablePsi] at this ⊢; exact this

end LeanLab.ChenDoubleSieve.Burst9Psi2

#print axioms LeanLab.ChenDoubleSieve.Burst9Psi2.Psi2_row0
#print axioms LeanLab.ChenDoubleSieve.Burst9Psi2.Psi2_row1
#print axioms LeanLab.ChenDoubleSieve.Burst9Psi2.Psi2_row2
#print axioms LeanLab.ChenDoubleSieve.Burst9Psi2.Psi2_row3
#print axioms LeanLab.ChenDoubleSieve.Burst9Psi2.table1_Psi2_zero
