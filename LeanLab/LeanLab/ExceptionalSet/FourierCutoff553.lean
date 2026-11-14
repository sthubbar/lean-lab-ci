import LeanLab.ExceptionalSet.ParityFourier553
import LeanLab.ExceptionalSet.FourierTransport553
import LeanLab.ExceptionalSet.FiniteGap553
import Mathlib.Algebra.BigOperators.Group.Finset.Interval

/-!
P0082 page370 after display41, quantitative Fourier cutoff removal.
Finite symmetric sums converge by Mathlib's signed integer summation theorem.
The inverse square estimate gives an explicit cutoff error.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.FourierCutoff553
open Finset Filter Topology

/-- P0082 page370 after display41, finite signed integer sum bookkeeping. -/
theorem symmetric_sum_formula {E : Type*} [AddCommGroup E] (f : ℤ → E) (N : ℕ) :
    (∑ h ∈ Finset.Icc (-(N : ℤ)) N, f h) =
      (∑ n ∈ Finset.range N, (f n + f (-(n + 1 : ℤ)))) + f N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Nat.cast_succ, Finset.sum_Icc_succ_eq_add_endpoints f, ih, Finset.sum_range_succ]
    push_cast
    abel

/-- P0082 page370 after display41, convergence of actual symmetric cutoffs. -/
theorem symmetric_sums_tendsto (f : ℤ → ℂ) (hf : Summable f) :
    Tendsto (fun N : ℕ => ∑ h ∈ Finset.Icc (-(N : ℤ)) N, f h)
      atTop (𝓝 (∑' h : ℤ, f h)) := by
  have hp := hf.hasSum.nat_add_neg_add_one.tendsto_sum_nat
  have hn : Summable (fun n : ℕ => f n) := hf.comp_injective Nat.cast_injective
  have hz := hn.tendsto_atTop_zero
  simpa only [← symmetric_sum_formula, add_zero] using hp.add hz

/-- P0082 page370 after display41, an outer cutoff minus an inner cutoff
is precisely the finite paired annulus. -/
theorem symmetric_annulus_formula {E : Type*} [AddCommGroup E] (f : ℤ → E)
    (H K : ℕ) (hHK : H ≤ K) :
    (∑ h ∈ Finset.Icc (-(K : ℤ)) K, f h) -
      (∑ h ∈ Finset.Icc (-(H : ℤ)) H, f h) =
        ∑ n ∈ Finset.Ioc H K, (f n + f (-(n : ℤ))) := by
  induction K, hHK using Nat.le_induction with
  | base => simp
  | succ K hK ih =>
    rw [Nat.cast_succ, Finset.sum_Icc_succ_eq_add_endpoints f,
      Finset.sum_Ioc_succ_top hK]
    rw [← ih]
    push_cast
    abel

/-- P0082 page370 after display41, an absolutely convergent coefficient
series with inverse square decay has an explicit symmetric cutoff error. -/
theorem symmetric_truncation_bound (f : ℤ → ℂ) (hf : Summable f) (H : ℕ)
    (C Δ : ℝ) (hC : 0 ≤ C) (hΔ : 0 < Δ)
    (hbound : ∀ h : ℤ, h ≠ 0 → ‖f h‖ ≤ C / (Δ * (h : ℝ) ^ 2)) :
    ‖(∑' h : ℤ, f h) - ∑ h ∈ Finset.Icc (-(H : ℤ)) H, f h‖ ≤
      4 * C / (Δ * (H + 1)) := by
  have hfinite (K : ℕ) (hHK : H ≤ K) :
      ‖(∑ h ∈ Finset.Icc (-(K : ℤ)) K, f h) -
        ∑ h ∈ Finset.Icc (-(H : ℤ)) H, f h‖ ≤ 4 * C / (Δ * (H + 1)) := by
    rw [symmetric_annulus_formula f H K hHK]
    have he : Finset.Ioc H K = Finset.Ioo H (K + 1) := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Ioo]
      omega
    rw [he]
    have hp (n : ℕ) (hn : n ∈ Finset.Ioo H (K + 1)) :
        ‖f n‖ ≤ C / (Δ * (n : ℝ) ^ 2) := by
      have hne : (n : ℤ) ≠ 0 := by have := (Finset.mem_Ioo.mp hn).1; omega
      simpa only [Int.cast_natCast] using hbound n hne
    have hm (n : ℕ) (hn : n ∈ Finset.Ioo H (K + 1)) :
        ‖f (-(n : ℤ))‖ ≤ C / (Δ * (n : ℝ) ^ 2) := by
      have hne : (n : ℤ) ≠ 0 := by have := (Finset.mem_Ioo.mp hn).1; omega
      simpa only [Int.cast_neg, Int.cast_natCast, neg_sq] using hbound (-(n : ℤ)) (neg_ne_zero.mpr hne)
    have ht := FourierTransport553.paired_fourier_tail f (fun _ => 1) H (K + 1)
      C Δ 1 hC hΔ (by norm_num) hp hm (by intro n hn; norm_num) (by intro n hn; norm_num)
    simpa only [mul_one] using ht
  have ht := ((symmetric_sums_tendsto f hf).sub
    (tendsto_const_nhds (x := ∑ h ∈ Finset.Icc (-(H : ℤ)) H, f h))).norm
  exact le_of_tendsto ht (Filter.eventually_atTop.mpr ⟨H, hfinite⟩)

open LeanLab.ExceptionalSet.U1539 (eC)
open LeanLab.ExceptionalSet.ParityFourier553

/-- P0082 page370 display41, absolute convergence of the actual shifted
block phase series, including both parity conventions. -/
theorem shifted_block_series_summable (s : Finset ℕ) (v : ℕ → ℝ) (t : ℝ)
    (j : ℤ) (Δ : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    Summable (fun h : ℤ => (coefficientKernel Δ h * eC (h * j / 2 - t * j)) *
      (∑ n ∈ s, eC ((t + h / 2) * v n))) := by
  apply Summable.of_norm_bounded ((coefficient_norm_summable Δ hΔ hΔ1).mul_right (s.card : ℝ))
  intro h
  rw [norm_mul, shifted_coefficient_norm]
  exact mul_le_mul_of_nonneg_left (Fejer467.phase_sum_norm_le_card s v (t + h / 2)) (norm_nonneg _)

/-- P0082 page370 after display41, the actual shifted block Fourier series
loses at most four times the block size over Delta times cutoff plus one. -/
theorem shifted_series_cutoff_error (s : Finset ℕ) (v : ℕ → ℝ) (t : ℝ)
    (j : ℤ) (Δ : ℝ) (H : ℕ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    ‖(∑' h : ℤ, (coefficientKernel Δ h * eC (h * j / 2 - t * j)) *
        (∑ n ∈ s, eC ((t + h / 2) * v n))) -
      ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
        (coefficientKernel Δ h * eC (h * j / 2 - t * j)) *
          (∑ n ∈ s, eC ((t + h / 2) * v n))‖ ≤
      4 * s.card / (Δ * (H + 1)) := by
  apply symmetric_truncation_bound _ (shifted_block_series_summable s v t j Δ hΔ hΔ1)
    H (s.card : ℝ) Δ (Nat.cast_nonneg _) hΔ
  intro h hh
  rw [norm_mul, shifted_coefficient_norm]
  have hc := coefficient_nonzero_bound Δ (h : ℝ) hΔ hΔ1 (by exact_mod_cast hh)
  have hp := Fejer467.phase_sum_norm_le_card s v (t + h / 2)
  calc
    _ ≤ (1 / (Δ * (h : ℝ) ^ 2)) * (s.card : ℝ) :=
      mul_le_mul hc hp (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- P0082 page370 display41 and its following truncation, actual finite
Fourier approximation for either shifted parity on any finite block. -/
theorem finite_shifted_fourier_error (s : Finset ℕ) (v : ℕ → ℝ) (t : ℝ)
    (j : ℤ) (Δ : ℝ) (H : ℕ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    ‖(∑ n ∈ s.filter (fun n => Even (⌊v n⌋ + j)), eC (t * (v n - j))) -
      ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
        (coefficientKernel Δ h * eC (h * j / 2 - t * j)) *
          (∑ n ∈ s, eC ((t + h / 2) * v n))‖ ≤
      ((s.filter (fun n => Int.fract (v n) < Δ / 2 ∨
        1 - Δ / 2 < Int.fract (v n))).card : ℝ) + 4 * s.card / (Δ * (H + 1)) := by
  let Z := ∑ n ∈ s.filter (fun n => Even (⌊v n⌋ + j)), eC (t * (v n - j))
  let T := ∑' h : ℤ, (coefficientKernel Δ h * eC (h * j / 2 - t * j)) *
    (∑ n ∈ s, eC ((t + h / 2) * v n))
  let A := ∑ h ∈ Finset.Icc (-(H : ℤ)) H,
    (coefficientKernel Δ h * eC (h * j / 2 - t * j)) *
      (∑ n ∈ s, eC ((t + h / 2) * v n))
  have h1 := shifted_parity_fourier_error s v t j Δ hΔ hΔ1
  have h2 := shifted_series_cutoff_error s v t j Δ H hΔ hΔ1
  change ‖Z - A‖ ≤ _
  calc
    _ = ‖(Z - T) + (T - A)‖ := by congr 1; ring
    _ ≤ ‖Z - T‖ + ‖T - A‖ := norm_add_le _ _
    _ ≤ _ := add_le_add h1 h2

/-- P0082 page370 display40, the actual twisted coefficients have a
finite norm sum at most five over Delta, uniformly in the parity shift. -/
theorem shifted_cutoff_mass (H : ℕ) (Δ t : ℝ) (j : ℤ)
    (hΔ : 0 < Δ) (hΔ1 : Δ < 1) :
    (∑ h ∈ Finset.Icc (-(H : ℤ)) H,
      ‖coefficientKernel Δ h * eC (h * j / 2 - t * j)‖) ≤ 5 / Δ := by
  simp only [shifted_coefficient_norm]
  let c : ℤ → ℂ := fun h => coefficientKernel Δ h
  change (∑ h ∈ Finset.Icc (-(H : ℤ)) H, ‖c h‖) ≤ 5 / Δ
  have he := symmetric_annulus_formula (fun h : ℤ => ‖c h‖) 0 H (Nat.zero_le H)
  simp only [Nat.cast_zero, neg_zero, Finset.Icc_self, Finset.sum_singleton] at he
  have hset : Finset.Ioc 0 H = Finset.Ioo 0 (H + 1) := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_Ioo]
    omega
  rw [hset] at he
  have h0 : ‖c 0‖ ≤ (1 : ℝ) := by
    simpa only [c, Int.cast_zero] using (coefficient_uniform Δ 0 hΔ hΔ1).trans
      (show (1 / 2 : ℝ) ≤ (1 : ℝ) by norm_num)
  have hp (n : ℕ) (hn : n ∈ Finset.Ioo 0 (H + 1)) :
      ‖c n‖ ≤ 1 / (Δ * (n : ℝ) ^ 2) := by
    have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Finset.mem_Ioo.mp hn).1)
    simpa only [c, Int.cast_natCast] using coefficient_nonzero_bound Δ (n : ℝ) hΔ hΔ1 hne
  have hm (n : ℕ) (hn : n ∈ Finset.Ioo 0 (H + 1)) :
      ‖c (-(n : ℤ))‖ ≤ 1 / (Δ * (n : ℝ) ^ 2) := by
    have hne : (n : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt (Finset.mem_Ioo.mp hn).1)
    simpa only [c, Int.cast_neg, Int.cast_natCast, neg_sq] using
      coefficient_nonzero_bound Δ (-(n : ℝ)) hΔ hΔ1 (neg_ne_zero.mpr hne)
  have hb := FourierTransport553.symmetric_coefficient_mass c
    (H + 1) 1 Δ (by norm_num) hΔ hΔ1.le h0 hp hm
  simp only [mul_one] at hb
  linarith

/-- P0082 page370 after display41, finite large value localization with
the actual parity coefficients, boundary error and explicit cutoff error. -/
theorem shifted_block_gap (s : Finset ℕ) (v : ℕ → ℝ) (t : ℝ) (j : ℤ)
    (Δ : ℝ) (H : ℕ) (r U : ℝ) (hΔ : 0 < Δ) (hΔ1 : Δ < 1) (hU : 0 ≤ U)
    (hsmall : ∀ h ∈ Finset.Icc (-(H : ℤ)) H,
      r < |t + h / 2| → ‖∑ n ∈ s, eC ((t + h / 2) * v n)‖ ≤ U)
    (hlarge :
      (((s.filter (fun n => Int.fract (v n) < Δ / 2 ∨
        1 - Δ / 2 < Int.fract (v n))).card : ℝ) + 4 * s.card / (Δ * (H + 1))) +
        (5 / Δ) * U < ‖∑ n ∈ s.filter (fun n => Even (⌊v n⌋ + j)), eC (t * (v n - j))‖) :
    ∃ h : ℤ, (|h| : ℝ) ≤ H ∧ |t - h / 2| ≤ r := by
  exact FiniteGap553.finite_fourier_gap H
    (fun h : ℤ => coefficientKernel Δ h * eC (h * j / 2 - t * j))
    (fun a => ∑ n ∈ s, eC (a * v n))
    (∑ n ∈ s.filter (fun n => Even (⌊v n⌋ + j)), eC (t * (v n - j)))
    t r
    (((s.filter (fun n => Int.fract (v n) < Δ / 2 ∨
      1 - Δ / 2 < Int.fract (v n))).card : ℝ) + 4 * s.card / (Δ * (H + 1)))
    (5 / Δ) U hU (finite_shifted_fourier_error s v t j Δ H hΔ hΔ1)
    (shifted_cutoff_mass H Δ t j hΔ hΔ1) hsmall hlarge

end LeanLab.ExceptionalSet.FourierCutoff553
