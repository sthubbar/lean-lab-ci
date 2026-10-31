/-
P0028, https://arxiv.org/abs/1610.02017, section 4.3, page 9.
The mixed convolution error estimate from Fourier uniformity and restriction bounds.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSHolder
import LeanLab.Ternary.MMSFourierConvolution

namespace LeanLab.Ternary.MMS
open Finset

/-- The interpolation exponents give exactly the quadratic power of N. -/
theorem mms_error_scale {N : ℕ} {δ K q : ℝ}
    (hN : 0 < N) (hδ : 0 ≤ δ) (hK : 0 ≤ K) (hq : q ≠ 0) :
    (δ * N) ^ (3 - q) * (K * (N : ℝ) ^ (1 - 1 / q)) ^ q =
      δ ^ (3 - q) * K ^ q * (N : ℝ) ^ 2 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  rw [Real.mul_rpow hδ hNr.le,
    Real.mul_rpow hK (Real.rpow_nonneg hNr.le _), ← Real.rpow_mul hNr.le]
  have hex : (3 - q) + (1 - 1 / q) * q = 2 := by field_simp; ring
  calc δ ^ (3 - q) * (N : ℝ) ^ (3 - q) * (K ^ q * (N : ℝ) ^ ((1 - 1 / q) * q)) =
      δ ^ (3 - q) * K ^ q * ((N : ℝ) ^ (3 - q) * (N : ℝ) ^ ((1 - 1 / q) * q)) := by ring
    _ = _ := by rw [← Real.rpow_add hNr, hex, Real.rpow_two]

/-- A uniform Fourier factor and three restriction norms control a full integer convolution. -/
theorem abs_int_triple_le_restriction (f g h : ℤ →₀ ℝ) (m : ℤ)
    {q M : ℝ} (hq : 2 < q) (hq3 : q < 3)
    (hM : ∀ γ : ℝ, ‖intHat f γ‖ ≤ M) :
    |∑ a ∈ f.support, ∑ b ∈ g.support, f a * g b * h (m - a - b)| ≤
      M ^ (3 - q) * intLq f q ^ (q - 2) * intLq g q * intLq h q := by
  have hi : 0 ≤ ∫ γ in (0 : ℝ)..1, ‖intHat f γ‖ ^ q :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (fun γ => Real.rpow_nonneg (norm_nonneg _) _)
  have he : intLq f q ^ (q - 2) =
      (∫ γ in (0 : ℝ)..1, ‖intHat f γ‖ ^ q) ^ ((q - 2) / q) := by
    rw [intLq, ← Real.rpow_mul hi]
    congr 1
    ring
  have hb := integral_three_uniform_bound
    (fun γ => ‖intHat f γ‖) (fun γ => ‖intHat g γ‖) (fun γ => ‖intHat h γ‖)
    (continuous_intHat f).norm (continuous_intHat g).norm (continuous_intHat h).norm
    (fun _ => norm_nonneg _) (fun _ => norm_nonneg _) (fun _ => norm_nonneg _)
    hq hq3 hM
  rw [← he] at hb
  exact (abs_int_triple_le_integral f g h m).trans hb

/-- The page 9 mixed error is at most δ to the power 3-q times K to the power q times N². -/
theorem abs_int_triple_uniform_bound (f g h : ℤ →₀ ℝ) (m : ℤ)
    {N : ℕ} {δ K q : ℝ} (hN : 0 < N) (hδ : 0 ≤ δ) (hK : 0 ≤ K)
    (hq : 2 < q) (hq3 : q < 3)
    (hM : ∀ γ : ℝ, ‖intHat f γ‖ ≤ δ * N)
    (hf : intLq f q ≤ K * (N : ℝ) ^ (1 - 1 / q))
    (hg : intLq g q ≤ K * (N : ℝ) ^ (1 - 1 / q))
    (hh : intLq h q ≤ K * (N : ℝ) ^ (1 - 1 / q)) :
    |∑ a ∈ f.support, ∑ b ∈ g.support, f a * g b * h (m - a - b)| ≤
      δ ^ (3 - q) * K ^ q * (N : ℝ) ^ 2 := by
  let R := K * (N : ℝ) ^ (1 - 1 / q)
  have hR : 0 ≤ R := mul_nonneg hK (Real.rpow_nonneg (Nat.cast_nonneg _) _)
  have hnorm (u : ℤ →₀ ℝ) : 0 ≤ intLq u q := by
    unfold intLq
    apply Real.rpow_nonneg
    exact intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (fun γ => Real.rpow_nonneg (norm_nonneg _) _)
  have hlf := hnorm f
  have hlg := hnorm g
  have hlh := hnorm h
  have hbase := abs_int_triple_le_restriction f g h m hq hq3 hM
  have hprod : (δ * N) ^ (3 - q) * intLq f q ^ (q - 2) * intLq g q * intLq h q ≤
      (δ * N) ^ (3 - q) * R ^ (q - 2) * R * R := by
    gcongr
  have he : R ^ (q - 2) * R * R = R ^ q := by
    calc _ = R ^ (q - 2) * R ^ (2 : ℕ) := by ring
      _ = R ^ (q - 2) * R ^ (2 : ℝ) := by rw [Real.rpow_two]
      _ = R ^ q := by
        rw [← Real.rpow_add' hR (by linarith : (q - 2) + 2 ≠ 0)]
        congr 1
        ring
  calc _ ≤ (δ * N) ^ (3 - q) * R ^ (q - 2) * R * R := hbase.trans hprod
    _ = (δ * N) ^ (3 - q) * (R ^ (q - 2) * R * R) := by ring
    _ = (δ * N) ^ (3 - q) * R ^ q := by rw [he]
    _ = _ := mms_error_scale hN hδ hK (by linarith)

/-- The mixed error coefficient can be made smaller than any positive tolerance. -/
theorem exists_uniform_error_scale {K q κ : ℝ} (hK : 0 ≤ K) (hq : q < 3) (hκ : 0 < κ) :
    ∃ δ : ℝ, 0 < δ ∧ δ < 1 ∧ δ ^ (3 - q) * K ^ q ≤ κ := by
  have hpow : 0 ≤ K ^ q := Real.rpow_nonneg hK _
  have hden : 0 < K ^ q + 1 := by linarith
  let r := κ / (K ^ q + 1)
  have hr : 0 < r := div_pos hκ hden
  let δ := min (1 / 2) (r ^ (1 / (3 - q)))
  have hδ : 0 < δ := lt_min (by norm_num) (Real.rpow_pos_of_pos hr _)
  refine ⟨δ, hδ, (min_le_left _ _).trans_lt (by norm_num), ?_⟩
  have he : (r ^ (1 / (3 - q))) ^ (3 - q) = r := by
    rw [← Real.rpow_mul hr.le]
    have hq' : 3 - q ≠ 0 := by linarith
    rw [one_div_mul_cancel hq', Real.rpow_one]
  have hb : δ ^ (3 - q) ≤ r := by
    calc δ ^ (3 - q) ≤ (r ^ (1 / (3 - q))) ^ (3 - q) :=
        Real.rpow_le_rpow hδ.le (min_le_right _ _) (by linarith)
      _ = r := he
  calc δ ^ (3 - q) * K ^ q ≤ r * K ^ q := mul_le_mul_of_nonneg_right hb hpow
    _ ≤ r * (K ^ q + 1) := mul_le_mul_of_nonneg_left (by linarith) hr.le
    _ = κ := by dsimp [r]; field_simp

end LeanLab.Ternary.MMS
