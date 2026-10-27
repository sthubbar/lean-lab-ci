/-
AI wrote the Lean code. CODEX task139, 2026-10-27.
Source: https://arxiv.org/pdf/2012.06322, Section 4, printed page 9.
The logarithmic saving leaf records the unresolved estimate in the printed deduction.
Binary Goldbach is open.
-/
import LeanLab.Song2020.Decomp139

namespace LeanLab.Song2020.Decomp139b

open LeanLab.Song2020 LeanLab.Song2020.State1562

noncomputable section

/-- LEAF. Page 9, cubic expansion. A pointwise perturbation bound. -/
theorem norm_cube_sub_le139 (z w : ℂ) :
    ‖z ^ 3 - w ^ 3‖ ≤ 2 * ‖z - w‖ * (‖z‖ ^ 2 + ‖w‖ ^ 2) := by
  have he : z ^ 3 - w ^ 3 = (z - w) * (z ^ 2 + z * w + w ^ 2) := by ring
  have hsum : ‖z ^ 2 + z * w + w ^ 2‖ ≤ ‖z‖ ^ 2 + ‖z‖ * ‖w‖ + ‖w‖ ^ 2 := by
    calc
      _ ≤ ‖z ^ 2 + z * w‖ + ‖w ^ 2‖ := norm_add_le _ _
      _ ≤ (‖z ^ 2‖ + ‖z * w‖) + ‖w ^ 2‖ := add_le_add (norm_add_le _ _) le_rfl
      _ = _ := by simp [norm_pow]
  have hpoly : ‖z ^ 2 + z * w + w ^ 2‖ ≤ 2 * (‖z‖ ^ 2 + ‖w‖ ^ 2) := by
    nlinarith [sq_nonneg (‖z‖ - ‖w‖)]
  rw [he, norm_mul]
  calc
    _ ≤ ‖z - w‖ * (2 * (‖z‖ ^ 2 + ‖w‖ ^ 2)) :=
      mul_le_mul_of_nonneg_left hpoly (norm_nonneg _)
    _ = _ := by ring

/-- LEAF. Page 9, Cauchy estimate. Uniform discrepancy times the two mean squares
bounds the difference of the cubic integrals. -/
theorem cube_transfer139 (f g : ℝ → ℂ) (hf : Continuous f) (hg : Continuous g)
    (n D : ℝ) (hD : ∀ α : ℝ, ‖f α - g α‖ ≤ D) :
    ‖(∫ α in (0 : ℝ)..1, f α ^ 3 * eC (-(n * α))) -
      (∫ α in (0 : ℝ)..1, g α ^ 3 * eC (-(n * α)))‖ ≤
      2 * D * ((∫ α in (0 : ℝ)..1, ‖f α‖ ^ 2) +
        (∫ α in (0 : ℝ)..1, ‖g α‖ ^ 2)) := by
  have hF : Continuous (fun α : ℝ => f α ^ 3 * eC (-(n * α))) := by unfold eC; fun_prop
  have hG : Continuous (fun α : ℝ => g α ^ 3 * eC (-(n * α))) := by unfold eC; fun_prop
  have heC (x : ℝ) : ‖eC x‖ = 1 := by
    simp [eC, Complex.norm_exp, Complex.mul_re, Complex.mul_im]
  rw [← intervalIntegral.integral_sub (hF.intervalIntegrable _ _) (hG.intervalIntegrable _ _)]
  calc
    _ ≤ ∫ α in (0 : ℝ)..1, ‖f α ^ 3 * eC (-(n * α)) - g α ^ 3 * eC (-(n * α))‖ :=
      intervalIntegral.norm_integral_le_integral_norm (by norm_num)
    _ ≤ ∫ α in (0 : ℝ)..1, 2 * D * (‖f α‖ ^ 2 + ‖g α‖ ^ 2) := by
      apply intervalIntegral.integral_mono_on (by norm_num)
        ((hF.sub hG).norm.intervalIntegrable _ _)
        ((by fun_prop : Continuous (fun α : ℝ => 2 * D * (‖f α‖ ^ 2 + ‖g α‖ ^ 2))).intervalIntegrable _ _)
      intro α _
      simp only [Pi.sub_apply]
      rw [show f α ^ 3 * eC (-(n * α)) - g α ^ 3 * eC (-(n * α)) =
        (f α ^ 3 - g α ^ 3) * eC (-(n * α)) by ring, norm_mul, heC, mul_one]
      calc
        _ ≤ 2 * ‖f α - g α‖ * (‖f α‖ ^ 2 + ‖g α‖ ^ 2) := norm_cube_sub_le139 _ _
        _ ≤ 2 * D * (‖f α‖ ^ 2 + ‖g α‖ ^ 2) := by
          gcongr
          exact hD α
    _ = _ := by
      rw [intervalIntegral.integral_const_mul]
      congr 1
      have hf2 : IntervalIntegrable (fun α : ℝ => ‖f α‖ ^ 2) MeasureTheory.volume 0 1 :=
        (by fun_prop : Continuous (fun α : ℝ => ‖f α‖ ^ 2)).intervalIntegrable _ _
      have hg2 : IntervalIntegrable (fun α : ℝ => ‖g α‖ ^ 2) MeasureTheory.volume 0 1 :=
        (by fun_prop : Continuous (fun α : ℝ => ‖g α‖ ^ 2)).intervalIntegrable _ _
      simpa only [Pi.add_apply] using intervalIntegral.integral_add hf2 hg2

/-- LEAF. Page 9. Specialize the cubic perturbation bound to the sealed f and g. -/
theorem song_cube_transfer139 (γ : ℝ) (n : ℕ) (y D : ℝ)
    (hD : ∀ α : ℝ, ‖fS γ n y α - gS n y α‖ ≤ D) :
    ‖RS γ n y - gCube n y‖ ≤
      2 * D * ((∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) +
        (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2)) := by
  have hf : Continuous (fS γ n y) := by unfold fS eC; fun_prop
  have hg : Continuous (gS n y) := by unfold gS eC; fun_prop
  exact cube_transfer139 (fS γ n y) (gS n y) hf hg n D hD

/-- LEAF. Page 9, final use of Lemmas 4 and 5. QUESTION Q139c.
This is the unresolved logarithmic saving needed by the printed deduction.
Audit139 records the positive epsilon loss in the displayed bounds. -/
theorem logarithmic_transfer139 (H4 : Lemma4) :
    ∀ γ : ℝ, 44 / 45 < γ → γ < 1 →
      ∃ C : ℝ, ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
        (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
        ∃ D : ℝ, 0 ≤ D ∧ (∀ α : ℝ, ‖fS γ n y α - gS n y α‖ ≤ D) ∧
          2 * D * ((∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) +
            (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2)) ≤
              C * (y ^ 2 / Real.log (n : ℝ) ^ 4) := by
  sorry

/-- Page 9. Assemble the exact sealed Asymptotic proposition from the named leaves
and the cited Pan and Pan input in Lemma 3. -/
theorem song_asymptotic_decomposed : Asymptotic := by
  intro γ hγ hγ1
  obtain ⟨C₀, N₀, hmain⟩ := song_lemma3
  obtain ⟨C₁, N₁, hlog⟩ := logarithmic_transfer139
    LeanLab.Song2020.Decomp139.song_lemma4_decomposed γ hγ hγ1
  refine ⟨C₀ + C₁, max 1 (max N₀ N₁), ?_⟩
  intro n ho hn y hy hyupper
  have hnR : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hsmall : (n : ℝ) ^ ((7 : ℝ) / 8) ≤ y :=
    (Real.rpow_le_rpow_of_exponent_le hnR (songExponent_mem hγ hγ1).1.le).trans hy.le
  have hmain' := hmain n ho (by omega) y hsmall hyupper
  obtain ⟨D, _, hD, hbudget⟩ := hlog n (by omega) y hy hyupper
  have herr := (song_cube_transfer139 γ n y D hD).trans hbudget
  calc
    ‖RS γ n y - (mainTerm n y : ℂ)‖ ≤
        ‖RS γ n y - gCube n y‖ + ‖gCube n y - (mainTerm n y : ℂ)‖ := by
      have he : RS γ n y - (mainTerm n y : ℂ) =
          (RS γ n y - gCube n y) + (gCube n y - (mainTerm n y : ℂ)) := by ring
      rw [he]
      exact norm_add_le _ _
    _ ≤ C₁ * (y ^ 2 / Real.log (n : ℝ) ^ 4) + C₀ * (y ^ 2 / Real.log (n : ℝ) ^ 4) :=
      add_le_add herr hmain'
    _ = _ := by ring

end

end LeanLab.Song2020.Decomp139b

#print axioms LeanLab.Song2020.Decomp139b.norm_cube_sub_le139
#print axioms LeanLab.Song2020.Decomp139b.cube_transfer139
#print axioms LeanLab.Song2020.Decomp139b.song_cube_transfer139
#print axioms LeanLab.Song2020.Decomp139b.logarithmic_transfer139
#print axioms LeanLab.Song2020.Decomp139b.song_asymptotic_decomposed

namespace LeanLab.Song2020.State1562

/-- OPEN: the asymptotic formula of Section 4. -/
theorem song_asymptotic : Asymptotic :=
  LeanLab.Song2020.Decomp139b.song_asymptotic_decomposed

end LeanLab.Song2020.State1562

#print axioms LeanLab.Song2020.State1562.song_asymptotic
