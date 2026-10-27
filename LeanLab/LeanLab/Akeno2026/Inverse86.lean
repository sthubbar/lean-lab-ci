/-
P0087 Akeno 2026 page 4, Lemma 2.2 equation 4.
The positive lower bound r for every integer distance makes nonresonance explicit.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Akeno2026.Localization86
import LeanLab.Akeno2026.Kernel86
namespace LeanLab.Akeno2026.Inverse86
open Real Finset LeanLab.Akeno2026
open scoped ContDiff
/-- LEAF. Page 4 equation 4, with an explicit positive lower bound for distance to integers. -/
theorem inverse_distance_bound (w : ℝ → ℝ) (hw : ContDiff ℝ ∞ w)
    (hs : Function.support w ⊆ Set.Icc 0 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X α r : ℝ, 1 ≤ X → 0 < r →
      (∀ n : ℤ, r ≤ |(n : ℝ) - α|) →
      ‖∑ n ∈ Finset.Icc (0 : ℤ) ⌊X⌋,
        e (α * n) * (w ((n : ℝ) / X) : ℂ)‖ ≤ C / r := by
  obtain ⟨C, hC, hdec⟩ := Localization86.weightFourier_decay w hw hs 3
  obtain ⟨S, hS, hK⟩ := Kernel86.uniform_shifted_kernel
  refine ⟨C * S, by positivity, ?_⟩
  intro X α r hX hr hdist
  have hX0 : 0 < X := by linarith
  let K : ℤ → ℝ := fun n => 1 / (1 + |(n : ℝ) - α|) ^ 2
  let F : ℤ → ℂ := fun n => (X : ℂ) * Localization86.weightFourier w (X * ((n : ℝ) - α))
  let den : ℤ → ℝ := fun n => 1 + X * |(n : ℝ) - α|
  have hkSum : Summable K := (hK α).1
  have hkBound : (∑' n : ℤ, K n) ≤ S := (hK α).2
  have hmajor (n : ℤ) : ‖F n‖ ≤ (C / r) * K n := by
    have hd : 1 + |(n : ℝ) - α| ≤ den n := by
      have hh := mul_le_mul_of_nonneg_right hX (abs_nonneg ((n : ℝ) - α))
      dsimp [den]
      linarith
    have hdr : X * r ≤ den n := by
      have hh := mul_le_mul_of_nonneg_left (hdist n) hX0.le
      dsimp [den]
      linarith
    have hp : (X * r) * (1 + |(n : ℝ) - α|) ^ 2 ≤ den n ^ 3 := by
      have hh := mul_le_mul hdr (pow_le_pow_left₀ (by positivity) hd 2)
        (by positivity) (show 0 ≤ den n by dsimp [den]; positivity)
      convert hh using 1; ring
    have hdec' : den n ^ 3 *
        ‖Localization86.weightFourier w (X * ((n : ℝ) - α))‖ ≤ C := by
      simpa only [den, abs_mul, abs_of_pos hX0] using hdec (X * ((n : ℝ) - α))
    have hh := (mul_le_mul_of_nonneg_right hp
      (norm_nonneg (Localization86.weightFourier w (X * ((n : ℝ) - α))))).trans hdec'
    have hv : ‖Localization86.weightFourier w (X * ((n : ℝ) - α))‖ ≤
        C / ((X * r) * (1 + |(n : ℝ) - α|) ^ 2) := by
      apply (le_div_iff₀ (by positivity)).mpr
      simpa only [mul_comm] using hh
    have hn : ‖F n‖ = X *
        ‖Localization86.weightFourier w (X * ((n : ℝ) - α))‖ := by
      simp only [F, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hX0]
    rw [hn]
    apply (mul_le_mul_of_nonneg_left hv hX0.le).trans_eq
    dsimp [K]
    field_simp
  have hns : Summable (fun n : ℤ => ‖F n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _) hmajor (hkSum.mul_left (C / r))
  have hp := Localization86.poisson_scaled w hw hs X hX0 α
  rw [hp]
  change ‖∑' n : ℤ, F n‖ ≤ C * S / r
  calc
    _ ≤ ∑' n : ℤ, ‖F n‖ := norm_tsum_le_tsum_norm hns
    _ ≤ ∑' n : ℤ, (C / r) * K n :=
      Summable.tsum_le_tsum hmajor hns (hkSum.mul_left (C / r))
    _ = (C / r) * ∑' n : ℤ, K n := tsum_mul_left
    _ ≤ (C / r) * S := mul_le_mul_of_nonneg_left hkBound (by positivity)
    _ = _ := by ring

end LeanLab.Akeno2026.Inverse86
