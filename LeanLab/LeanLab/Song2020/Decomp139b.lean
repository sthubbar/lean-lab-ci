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

/-- Page 9. Exact product of the Lemma 4 and Lemma 5 scales.
The window ratio records the saving before any logarithmic absorption. -/
theorem lemma4_product_identity2527 (γ ε n y : ℝ) (hn : 0 < n) (hy : 0 < y) :
    (n ^ (21 / 31 - 14 * γ / 31 + ε) * y ^ ((23 : ℝ) / 31)) *
        (n ^ (1 - γ) * y) =
      (y ^ 2 * n ^ ε) * (n ^ songExponent γ / y) ^ ((8 : ℝ) / 31) := by
  apply Real.log_injOn_pos
    (by simp only [Set.mem_Ioi]; positivity)
    (by simp only [Set.mem_Ioi]; positivity)
  simp (disch := positivity) only
    [Real.log_mul, Real.log_rpow, Real.log_pow, Real.log_div]
  unfold songExponent
  ring

/-- Page 9. CONDITIONAL ON Lemma4. At the exact window the displayed
mean square argument supplies a positive epsilon power, not a logarithmic saving. -/
theorem power_loss_transfer2527 (H4 : Lemma4) (γ : ℝ)
    (hγ : 44 / 45 < γ) (hγ1 : γ < 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → ∀ y : ℝ,
      (n : ℝ) ^ songExponent γ < y → y ≤ (n : ℝ) / 3 →
      ∃ D : ℝ, 0 ≤ D ∧ (∀ α : ℝ, ‖fS γ n y α - gS n y α‖ ≤ D) ∧
        2 * D * ((∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) +
          (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2)) ≤
            C * (y ^ 2 * (n : ℝ) ^ ε) := by
  obtain ⟨C₄, N₄, h₄⟩ := H4 γ hγ hγ1 ε hε
  obtain ⟨C₅, N₅, h₅⟩ := song_lemma5 γ hγ hγ1
  refine ⟨4 * |C₄| * |C₅|, by positivity, max 2 (max N₄ N₅), ?_⟩
  intro n hn y hy hyupper
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
  have hn0 : (0 : ℝ) < n := by linarith
  have hy0 : 0 < y := (Real.rpow_pos_of_pos hn0 _).trans hy
  let P := (n : ℝ) ^ (21 / 31 - 14 * γ / 31 + ε) * y ^ ((23 : ℝ) / 31)
  let Q := (n : ℝ) ^ (1 - γ) * y
  have hP : 0 ≤ P := by dsimp [P]; positivity
  have hQ : 0 ≤ Q := by dsimp [Q]; positivity
  have hnγ : 1 ≤ (n : ℝ) ^ (1 - γ) :=
    Real.one_le_rpow hn1 (by linarith)
  have hyQ : y ≤ Q := by dsimp [Q]; nlinarith
  obtain ⟨hf, hg⟩ := h₅ n (by omega) y hy hyupper
  have hf' : (∫ α in (0 : ℝ)..1, ‖fS γ n y α‖ ^ 2) ≤ |C₅| * Q :=
    hf.trans (mul_le_mul_of_nonneg_right (le_abs_self C₅) hQ)
  have hg' : (∫ α in (0 : ℝ)..1, ‖gS n y α‖ ^ 2) ≤ |C₅| * Q := by
    calc
      _ ≤ C₅ * y := hg
      _ ≤ |C₅| * y := mul_le_mul_of_nonneg_right (le_abs_self C₅) hy0.le
      _ ≤ |C₅| * Q := mul_le_mul_of_nonneg_left hyQ (abs_nonneg C₅)
  have hratio : ((n : ℝ) ^ songExponent γ / y) ^ ((8 : ℝ) / 31) ≤ 1 := by
    calc
      _ ≤ (1 : ℝ) ^ ((8 : ℝ) / 31) :=
        Real.rpow_le_rpow (by positivity) ((div_le_one hy0).mpr hy.le) (by norm_num)
      _ = 1 := Real.one_rpow _
  have hscalar : P * Q ≤ y ^ 2 * (n : ℝ) ^ ε := by
    dsimp [P, Q]
    rw [lemma4_product_identity2527 γ ε n y hn0 hy0]
    simpa only [mul_one] using
      mul_le_mul_of_nonneg_left hratio (by positivity : 0 ≤ y ^ 2 * (n : ℝ) ^ ε)
  refine ⟨|C₄| * P, mul_nonneg (abs_nonneg C₄) hP, ?_, ?_⟩
  · intro α
    exact (h₄ n (by omega) y hy hyupper α).trans
      (mul_le_mul_of_nonneg_right (le_abs_self C₄) hP)
  · calc
      _ ≤ 2 * (|C₄| * P) * (|C₅| * Q + |C₅| * Q) :=
        mul_le_mul_of_nonneg_left (add_le_add hf' hg') (by positivity)
      _ = 4 * |C₄| * |C₅| * (P * Q) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hscalar (by positivity)

/-- Page 9, QUESTION Q139c. The displayed scalar envelope exceeds every
inverse fourth logarithm budget even on strictly admissible windows.
This does not refute the estimate for the actual functions f and g. -/
theorem lemma4_envelope_not_log_saving2527 (γ : ℝ)
    (hγ : 44 / 45 < γ) (hγ1 : γ < 1) (ε : ℝ) (hε : 0 < ε) (C : ℝ) (N : ℕ) :
    ∃ n : ℕ, N ≤ n ∧ ∃ y : ℝ,
      (n : ℝ) ^ songExponent γ < y ∧ y ≤ (n : ℝ) / 3 ∧
        C * (y ^ 2 / Real.log (n : ℝ) ^ 4) <
          ((n : ℝ) ^ (21 / 31 - 14 * γ / 31 + ε) * y ^ ((23 : ℝ) / 31)) *
            ((n : ℝ) ^ (1 - γ) * y) := by
  let k : ℝ := ((1 : ℝ) / 2) ^ ((8 : ℝ) / 31)
  have hk : 0 < k := by dsimp [k]; positivity
  have hθ : 0 < 1 - songExponent γ := by
    have := (songExponent_mem hγ hγ1).2
    linarith
  have hlog : Filter.Tendsto (fun n : ℕ => Real.log (n : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hgood : ∀ᶠ n : ℕ in Filter.atTop,
      N ≤ n ∧ (1 : ℝ) ≤ n ∧ 1 ≤ Real.log (n : ℝ) ∧
        6 < (n : ℝ) ^ (1 - songExponent γ) ∧ max C 0 / k < (n : ℝ) ^ ε := by
    filter_upwards [Filter.eventually_ge_atTop N,
      tendsto_natCast_atTop_atTop.eventually_ge_atTop (1 : ℝ),
      hlog.eventually_ge_atTop 1,
      ((_root_.tendsto_rpow_atTop hθ).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop 6,
      ((_root_.tendsto_rpow_atTop hε).comp tendsto_natCast_atTop_atTop).eventually_gt_atTop
        (max C 0 / k)] with n hN hn hL hW hD
    exact ⟨hN, hn, hL, hW, hD⟩
  obtain ⟨n, hN, hn, hL, hW, hD⟩ := hgood.exists
  have hn0 : (0 : ℝ) < n := by linarith
  have hp : 0 < (n : ℝ) ^ songExponent γ := Real.rpow_pos_of_pos hn0 _
  let y : ℝ := 2 * (n : ℝ) ^ songExponent γ
  have hy0 : 0 < y := by dsimp [y]; positivity
  have hwin : (n : ℝ) ^ songExponent γ < y := by dsimp [y]; linarith
  have he : (n : ℝ) ^ songExponent γ * (n : ℝ) ^ (1 - songExponent γ) = n := by
    rw [← Real.rpow_add hn0,
      show songExponent γ + (1 - songExponent γ) = 1 by ring, Real.rpow_one]
  have hyupper : y ≤ (n : ℝ) / 3 := by
    have := mul_lt_mul_of_pos_left hW hp
    dsimp [y]
    nlinarith
  have hden : 1 ≤ Real.log (n : ℝ) ^ 4 := one_le_pow₀ hL
  have hdiv : C / Real.log (n : ℝ) ^ 4 ≤ max C 0 := by
    apply (div_le_iff₀ (by linarith : 0 < Real.log (n : ℝ) ^ 4)).mpr
    have hm := mul_le_mul_of_nonneg_left hden (le_max_right C 0)
    nlinarith [le_max_left C 0]
  have hbad : C / Real.log (n : ℝ) ^ 4 < k * (n : ℝ) ^ ε := by
    have := (div_lt_iff₀ hk).mp hD
    nlinarith
  have hquot : (n : ℝ) ^ songExponent γ / y = (1 : ℝ) / 2 := by
    dsimp [y]
    field_simp
  refine ⟨n, hN, y, hwin, hyupper, ?_⟩
  rw [lemma4_product_identity2527 γ ε n y hn0 hy0, hquot]
  change C * (y ^ 2 / Real.log (n : ℝ) ^ 4) < (y ^ 2 * (n : ℝ) ^ ε) * k
  calc
    _ = y ^ 2 * (C / Real.log (n : ℝ) ^ 4) := by ring
    _ < y ^ 2 * (k * (n : ℝ) ^ ε) :=
      mul_lt_mul_of_pos_left hbad (sq_pos_of_pos hy0)
    _ = _ := by ring

/-- LEAF. Page 9, final use of Lemmas 4 and 5. QUESTION Q139c.
This is the unresolved logarithmic saving needed by the printed deduction.
Audit139 records the positive epsilon loss in the displayed bounds.
Status audit CLAUDE S60 2026-11-22: BLOCKED. `Audit1122Absorption.printed_absorption_false` proves
that the displayed Lemma 4 and Lemma 5 bounds cannot give this at the exact window; the margin
version is `Repair591Margin.logarithmic_transfer_with_margin591`, and
`Palomar1122Song.songTheorem1_of_lemma3_logTransfer` takes this content as `Flag1734.LogTransferDQ`. -/
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
#print axioms LeanLab.Song2020.Decomp139b.lemma4_product_identity2527
#print axioms LeanLab.Song2020.Decomp139b.power_loss_transfer2527
#print axioms LeanLab.Song2020.Decomp139b.lemma4_envelope_not_log_saving2527
#print axioms LeanLab.Song2020.Decomp139b.logarithmic_transfer139
#print axioms LeanLab.Song2020.Decomp139b.song_asymptotic_decomposed

namespace LeanLab.Song2020.State1562

/-- OPEN: the asymptotic formula of Section 4. -/
theorem song_asymptotic : Asymptotic :=
  LeanLab.Song2020.Decomp139b.song_asymptotic_decomposed

end LeanLab.Song2020.State1562

#print axioms LeanLab.Song2020.State1562.song_asymptotic
