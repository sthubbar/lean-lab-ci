/-
P0069, Lemma 9, pages 22 and 23. CODEX task488.
The Perron assembly is CONDITIONAL on its named split leaves.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp488c

namespace LeanLab.BHP1997.DecompC165a
open Classical Complex MeanValue132
namespace Contour230
open MeasureTheory Filter Asymptotics Set Real
open scoped Topology

/-- Page 22, Perron formula and display 3.36 with the existing regular kernel.
The exact sealed conclusion follows from the three smaller split pieces
and the proved residue identity. CONDITIONAL on the remaining analytic leaves. -/
theorem regularized_perron_bound (h8 : MeanValue132.Lemma8) :
    ∃ C : ℝ, 0 < C ∧ ∀ x N T : ℝ, ∀ (q : ℕ) [NeZero q],
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      2 ≤ x → 2 ≤ N → N ≤ x → 2 ≤ T → T ≤ x → 1 ≤ q → (q : ℝ) ≤ x → |t| ≤ T →
        ‖partialSum N χ t‖ ≤ ‖lineIntegral N T χ t‖ +
          C * Real.log x * (Real.sqrt q / Real.sqrt T) +
          C * Real.log x * (Real.sqrt N / T) +
          C * (if χ = 1 then Real.sqrt N / (1 + |t|) else 0) := by
  exact regularized_perron_assembly h8

end Contour230

/-- Pages 22 and 23, display 3.36 and the weighted fourth moment.
The regular kernel, chosen height and complete Holder estimate are proved.
This exact sealed conclusion is CONDITIONAL on regularized_perron_bound.
The uniform pointwise contour error remains OPEN. -/
theorem contour_holder (h8 : MeanValue132.Lemma8) :
    ∃ C : ℝ, 0 < C ∧ ∀ x N T : ℝ, ∀ (q : ℕ) [NeZero q],
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      2 ≤ x → 2 ≤ N → N ≤ x → 2 ≤ T → T ≤ x → 1 ≤ q → (q : ℝ) ≤ x →
      Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
        ∃ J : ℝ × DirichletCharacter ℂ q → ℂ,
          (∑ p ∈ S, ‖J p‖ ^ 4) ≤ C * Real.log x ^ (3 : ℝ) * weightedMoment T S ∧
          ∀ p ∈ S, ‖partialSum N p.2 p.1‖ ≤ ‖J p‖ +
            C * Real.log x * (Real.sqrt q / Real.sqrt T) +
            C * Real.log x * (Real.sqrt N / T) +
            C * (if p.2 = 1 then Real.sqrt N / (1 + |p.1|) else 0) := by
  obtain ⟨Ce, hCe, hpoint⟩ := Contour230.regularized_perron_bound h8
  let C := max Ce ((332 : ℝ) ^ 3)
  have hC : 0 < C := lt_of_lt_of_le hCe (le_max_left _ _)
  refine ⟨C, hC, ?_⟩
  intro x N T q _ S hx hN hNx hT hTx hq hqx hspace htimes
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  refine ⟨fun p => Contour230.lineIntegral N T p.2 p.1, ?_, ?_⟩
  · have hm := Contour230.lineIntegral_sum S hx hN hNx hT hTx htimes
    have hw0 : 0 ≤ weightedMoment T S := by
      unfold weightedMoment
      apply Finset.sum_nonneg
      intro p hp
      apply intervalIntegral.integral_nonneg (by linarith)
      intro u hu
      positivity
    have hc := mul_le_mul_of_nonneg_right (le_max_right Ce ((332 : ℝ) ^ 3))
      (show 0 ≤ Real.log x ^ (3 : ℝ) * weightedMoment T S by positivity)
    exact hm.trans (by simpa only [mul_assoc] using hc)
  · intro p hp
    have h0 : Ce ≤ C := le_max_left _ _
    have h1 := mul_le_mul_of_nonneg_right h0
      (show 0 ≤ Real.log x * (Real.sqrt q / Real.sqrt T) by positivity)
    have h2 := mul_le_mul_of_nonneg_right h0
      (show 0 ≤ Real.log x * (Real.sqrt N / T) by positivity)
    have h3 := mul_le_mul_of_nonneg_right h0
      (show 0 ≤ (if p.2 = 1 then Real.sqrt N / (1 + |p.1|) else 0) by
        split_ifs <;> positivity)
    have hh := hpoint x N T q p.2 p.1 hx hN hNx hT hTx hq hqx (htimes p hp)
    simp only [mul_assoc] at hh ⊢
    exact hh.trans (add_le_add (add_le_add (add_le_add (le_refl _) h1) h2) h3)

/-- LEAF. Page 23, fourth and fifth displays. Rearrange by character,
bound the kernel with Spacing132.kernel_le_ten_log and apply Lemma 7
at 2T with ambient scale 2x. Absorb log 2x into a constant times log x.
CONDITIONAL on Lemma 7. The finite spacing and integration step is proved. -/
theorem spaced_weighted_moment (h7 : MeanValue132.Lemma7) :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 < C ∧ ∀ x T : ℝ, ∀ (q : ℕ) [NeZero q],
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      2 ≤ x → 2 ≤ T → T ≤ x → 1 ≤ q → (q : ℝ) ≤ x →
      Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
        weightedMoment T S ≤ C * ((q : ℝ) * T * Real.log x ^ B) := by
  obtain ⟨B, C, hB, hC, h7⟩ := h7
  refine ⟨B + 1, 20 * C * (2 : ℝ) ^ B, by linarith, by positivity, ?_⟩
  intro x T q _ S hx hT hTx hq hqx hspace htimes
  have hx0 : 0 < x := by linarith
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hcont (χ : DirichletCharacter ℂ q) :
      Continuous (fun u : ℝ => ‖χ.LFunction (Thm4.half u)‖ ^ 4) := by
    have hh : Continuous (fun u : ℝ => Thm4.half u) := by
      unfold Thm4.half
      fun_prop
    have hc : Continuous (fun u : ℝ => χ.LFunction (Thm4.half u)) := by
      apply continuous_iff_continuousAt.mpr
      intro u
      have hne : Thm4.half u ≠ 1 := by
        intro heq
        have hre := congrArg Complex.re heq
        norm_num [Thm4.half] at hre
      exact (χ.differentiableAt_LFunction _ (.inl hne)).continuousAt.comp hh.continuousAt
    exact hc.norm.pow 4
  have hk := KernelC165.weighted_kernel_integral S
    (fun χ u => ‖χ.LFunction (Thm4.half u)‖ ^ 4) hcont
    (fun χ u => pow_nonneg (norm_nonneg _) 4) hx (by linarith) hTx hspace htimes
  have hm := h7 (2 * x) (2 * T) q (by linarith) (by linarith)
    (by linarith) hq (by linarith)
  have hlog2 : Real.log (2 * x) ≤ 2 * Real.log x := by
    rw [Real.log_mul (by norm_num) (ne_of_gt hx0)]
    have := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hx
    linarith
  have hlog20 : 0 ≤ Real.log (2 * x) := Real.log_nonneg (by linarith)
  have hp : Real.log (2 * x) ^ B ≤ (2 : ℝ) ^ B * Real.log x ^ B := by
    calc
      Real.log (2 * x) ^ B ≤ (2 * Real.log x) ^ B := Real.rpow_le_rpow hlog20 hlog2 hB
      _ = _ := Real.mul_rpow (by norm_num) hlog.le
  have hexp : Real.log x ^ (B + 1) = Real.log x ^ B * Real.log x := by
    rw [Real.rpow_add hlog, Real.rpow_one]
  calc
    weightedMoment T S ≤ 10 * Real.log x *
        ∑ χ : DirichletCharacter ℂ q, ∫ u in (-2 * T)..(2 * T),
          ‖χ.LFunction (Thm4.half u)‖ ^ 4 := hk
    _ ≤ 10 * Real.log x * (C * (q : ℝ) * (2 * T) * Real.log (2 * x) ^ B) := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      simpa only [neg_mul] using hm
    _ ≤ 10 * Real.log x * (C * (q : ℝ) * (2 * T) *
        ((2 : ℝ) ^ B * Real.log x ^ B)) := by
      gcongr
    _ = 20 * C * (2 : ℝ) ^ B * ((q : ℝ) * T * Real.log x ^ (B + 1)) := by
      rw [hexp]
      ring


/-- Page 23, collecting constants proves the exact perron_input statement.
CONDITIONAL on the three OPEN leaves. No direct sorry. -/
theorem perron_input :
    ∃ B C : ℝ, 0 ≤ B ∧ 0 < C ∧ ∀ x N T : ℝ, ∀ q : ℕ,
      ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
      2 ≤ x → 2 ≤ N → N ≤ x → 2 ≤ T → T ≤ x → 1 ≤ q → (q : ℝ) ≤ x →
      Thm4.WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
        ∃ J : ℝ × DirichletCharacter ℂ q → ℂ,
          (∑ p ∈ S, ‖J p‖ ^ 4) ≤ C * ((q : ℝ) * T * Real.log x ^ B) ∧
          ∀ p ∈ S, ‖partialSum N p.2 p.1‖ ≤ ‖J p‖ +
            C * Real.log x * (Real.sqrt q / Real.sqrt T) +
            C * Real.log x * (Real.sqrt N / T) +
            C * (if p.2 = 1 then Real.sqrt N / (1 + |p.1|) else 0) := by
  obtain ⟨C0, hC0, hcontour⟩ := contour_holder rademacher_strip_bound
  obtain ⟨B, C1, hB, hC1, hmoment⟩ := spaced_weighted_moment all_character_fourth_moment
  let C := max C0 (C0 * C1)
  have hC : 0 < C := lt_of_lt_of_le hC0 (le_max_left _ _)
  refine ⟨B + 3, C, by linarith, hC, ?_⟩
  intro x N T q S hx hN hNx hT hTx hq hqx hspace htimes
  haveI : NeZero q := ⟨by omega⟩
  obtain ⟨J, hJ, hpoint⟩ := hcontour x N T q S hx hN hNx hT hTx hq hqx hspace htimes
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  refine ⟨J, ?_, ?_⟩
  · have hW := hmoment x T q S hx hT hTx hq hqx hspace htimes
    have hprod : Real.log x ^ (3 : ℝ) * Real.log x ^ B = Real.log x ^ (B + 3) := by
      rw [← Real.rpow_add hlog]
      congr 1
      ring
    calc
      (∑ p ∈ S, ‖J p‖ ^ 4) ≤ C0 * Real.log x ^ (3 : ℝ) * weightedMoment T S := hJ
      _ ≤ C0 * Real.log x ^ (3 : ℝ) * (C1 * ((q : ℝ) * T * Real.log x ^ B)) :=
        mul_le_mul_of_nonneg_left hW (by positivity)
      _ = (C0 * C1) * ((q : ℝ) * T * Real.log x ^ (B + 3)) := by
        calc
          _ = (C0 * C1) * ((q : ℝ) * T *
              (Real.log x ^ (3 : ℝ) * Real.log x ^ B)) := by ring
          _ = _ := by rw [hprod]
      _ ≤ C * ((q : ℝ) * T * Real.log x ^ (B + 3)) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · intro p hp
    have h0 : C0 ≤ C := le_max_left _ _
    have h1 := mul_le_mul_of_nonneg_right h0
      (show 0 ≤ Real.log x * (Real.sqrt q / Real.sqrt T) by positivity)
    have h2 := mul_le_mul_of_nonneg_right h0
      (show 0 ≤ Real.log x * (Real.sqrt N / T) by positivity)
    have h3 := mul_le_mul_of_nonneg_right h0
      (show 0 ≤ (if p.2 = 1 then Real.sqrt N / (1 + |p.1|) else 0) by
        split_ifs <;> positivity)
    have hpbound := hpoint p hp
    simp only [mul_assoc] at hpbound ⊢
    by_cases hχ : p.2 = 1
    · simp only [hχ, ite_true] at hpbound h3 ⊢
      exact hpbound.trans (add_le_add (add_le_add (add_le_add (le_refl _) h1) h2) h3)
    · simp only [hχ, ite_false] at hpbound h3 ⊢
      exact hpbound.trans (add_le_add (add_le_add (add_le_add (le_refl _) h1) h2) h3)

/-- Page 23, the existing finite fourth-power assembly with the new
Perron decomposition. CONDITIONAL on its named analytic leaves. -/
theorem lemma9 : MeanValue132.Lemma9 := by
  obtain ⟨B, C, hB, hC, hinput⟩ := perron_input
  refine ⟨B, 64 * max C (C ^ 4), hB, by positivity, ?_⟩
  intro x N T q S hx hN hNx hT hTx hq hqx hspace htimes
  obtain ⟨J, hJ, hpoint⟩ := hinput x N T q S hx hN hNx hT hTx hq hqx hspace htimes
  have hs := Decomp132b.fourth_moment_sum S (fun p => partialSum N p.2 p.1) J
    (fun _ => C * Real.log x * (Real.sqrt q / Real.sqrt T))
    (fun _ => C * Real.log x * (Real.sqrt N / T))
    (fun p => C * (if p.2 = 1 then Real.sqrt N / (1 + |p.1|) else 0)) hpoint
  rw [Decomp132b.error_sum x N T C (by linarith) (by linarith) S] at hs
  have hlog : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hmain : 0 ≤ (q : ℝ) * T * Real.log x ^ B := by positivity
  have hrem : 0 ≤ remainder x N T S := by
    unfold remainder
    apply add_nonneg
    · positivity
    · apply mul_nonneg (sq_nonneg _)
      apply Finset.sum_nonneg
      intro p hp
      split_ifs <;> positivity
  have h1 := mul_le_mul_of_nonneg_right (le_max_left C (C ^ 4)) hmain
  have h2 := mul_le_mul_of_nonneg_right (le_max_right C (C ^ 4)) hrem
  nlinarith

end LeanLab.BHP1997.DecompC165a
