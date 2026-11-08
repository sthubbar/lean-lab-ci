/-
AI wrote this Lean code for CODEX task459.
Source: PrimeNumberTheoremAnd commit c39a751132c88b6e8080b74c74023fd95b3d8be0,
MellinCalculus.lean, blueprint comment at lines 486 to 492.
A smooth bump has rapid Mellin decay on each fixed vertical line.
-/
import LeanLab.PNTPort.StrongPNT.MellinCalculus
import Mathlib.Analysis.MellinInversion
import Mathlib.Analysis.Distribution.SchwartzSpace.Fourier

open Real Complex Set MeasureTheory
open scoped FourierTransform ContDiff

namespace LeanLab.PNTPort

/-- Rapid vertical Mellin decay for a smooth bump supported away from zero. -/
theorem mellin_bump_rapid_vertical {ν : ℝ → ℝ} (hν : ContDiff ℝ ∞ ν)
    (hs : Function.support ν ⊆ Icc (1 / 2) 2) (σ : ℝ) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ,
      |t| ^ k * ‖mellin (fun x ↦ (ν x : ℂ)) (σ + t * I)‖ ≤ C := by
  let g : ℝ → ℂ := fun u ↦ Real.exp (-σ * u) • (ν (Real.exp (-u)) : ℂ)
  have hg : ContDiff ℝ ∞ g := by
    exact (show ContDiff ℝ ∞ (fun u : ℝ ↦ Real.exp (-σ * u)) from by fun_prop).smul
      (Complex.ofRealCLM.contDiff.comp (hν.comp (by fun_prop)))
  have hgs : Function.support g ⊆ Icc (-Real.log 2) (Real.log 2) := by
    intro u hu
    have hnu : ν (Real.exp (-u)) ≠ 0 := by
      intro hz
      simp [g, hz] at hu
    have hx := hs hnu
    have hlow : Real.log (1 / 2 : ℝ) ≤ -u := by
      simpa using Real.log_le_log (by norm_num) hx.1
    have hhigh : -u ≤ Real.log 2 := by
      simpa using Real.log_le_log (Real.exp_pos _) hx.2
    rw [one_div, Real.log_inv] at hlow
    constructor <;> linarith
  have hgc : HasCompactSupport g :=
    HasCompactSupport.of_support_subset_isCompact isCompact_Icc hgs
  let G := hgc.toSchwartzMap hg
  obtain ⟨C, hC, hbound⟩ := (𝓕 G).decay k 0
  refine ⟨C * (2 * Real.pi) ^ k, by positivity, fun t ↦ ?_⟩
  have h := hbound (t / (2 * Real.pi))
  simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  have hm : mellin (fun x ↦ (ν x : ℂ)) (σ + t * I) =
      𝓕 (g : ℝ → ℂ) (t / (2 * Real.pi)) := by
    rw [mellin_eq_fourier]
    simp [g]
  rw [SchwartzMap.fourier_coe] at h
  change |t / (2 * Real.pi)| ^ k *
    ‖𝓕 (g : ℝ → ℂ) (t / (2 * Real.pi))‖ ≤ C at h
  rw [← hm] at h
  rw [abs_div, abs_of_pos (by positivity : 0 < 2 * Real.pi), div_pow,
    div_mul_eq_mul_div, div_le_iff₀ (by positivity)] at h
  exact h

/-- Rapid Mellin decay with a constant uniform on the positive strip of width two. -/
theorem mellin_bump_rapid_strip {ν : ℝ → ℝ} (hν : ContDiff ℝ ∞ ν)
    (hs : Function.support ν ⊆ Icc (1 / 2) 2) (k : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ s : ℂ, 0 < s.re → s.re ≤ 2 →
      ‖s‖ ^ (k + 1) * ‖mellin (fun x ↦ (ν x : ℂ)) s‖ ≤ C := by
  induction k generalizing ν with
  | zero =>
    obtain ⟨C, hC, hbound⟩ := MellinOfPsi (hν.of_le (by simp)) hs
    refine ⟨C, hC, fun s hpos htwo ↦ ?_⟩
    have hs0 : s ≠ 0 := by intro hz; simp [hz] at hpos
    have hb := mul_le_mul_of_nonneg_left (hbound s.re hpos s le_rfl htwo) (norm_nonneg s)
    simpa [mul_left_comm, norm_ne_zero_iff.mpr hs0] using hb
  | succ k ih =>
    have hd : ContDiff ℝ ∞ (fun x ↦ x * deriv ν x) :=
      contDiff_id.mul (contDiff_infty_iff_deriv.mp hν).2
    have hds : Function.support (fun x ↦ x * deriv ν x) ⊆ Icc (1 / 2) 2 := by
      intro x hx
      have hd0 : deriv ν x ≠ 0 := by
        intro hz
        simp [Function.mem_support, hz] at hx
      exact (closure_minimal hs isClosed_Icc) (support_deriv_subset hd0)
    obtain ⟨C, hC, hbound⟩ := ih hd hds
    refine ⟨C, hC, fun s hpos htwo ↦ ?_⟩
    have hs0 : s ≠ 0 := by intro hz; simp [hz] at hpos
    have hrec : mellin (fun x ↦ (ν x : ℂ)) s =
        -(1 / s) * mellin (fun x ↦ ((x * deriv ν x : ℝ) : ℂ)) s := by
      rw [mellin]
      simp only [smul_eq_mul]
      rw [show (fun x : ℝ ↦ (x : ℂ) ^ (s - 1) * ↑(ν x)) =
          (fun x : ℝ ↦ ↑(ν x) * (x : ℂ) ^ (s - 1)) by funext; ring]
      rw [MellinOfPsi_aux (hν.of_le (by simp)) hs hs0]
      congr 1
      apply setIntegral_congr_fun measurableSet_Ioi
      intro x hx
      have hx0 : (x : ℂ) ≠ 0 := by exact_mod_cast (ne_of_gt hx)
      simp only [smul_eq_mul, Complex.ofReal_mul]
      have hp := Complex.cpow_add (s - 1) 1 hx0
      simp only [sub_add_cancel, Complex.cpow_one] at hp
      rw [hp]
      ring
    have hb := hbound s hpos htwo
    rw [hrec, norm_mul, norm_neg, norm_div, norm_one]
    calc
      _ = ‖s‖ ^ (k + 1) *
          ‖mellin (fun x ↦ ((x * deriv ν x : ℝ) : ℂ)) s‖ := by
        rw [pow_succ]
        field_simp [norm_ne_zero_iff.mpr hs0]
      _ ≤ C := hb

/-- The Mellin transform of a smooth bump supported away from zero is entire. -/
theorem mellin_bump_entire {ν : ℝ → ℝ} (hν : ContDiff ℝ ∞ ν)
    (hs : Function.support ν ⊆ Icc (1 / 2) 2) :
    Differentiable ℂ (mellin (fun x ↦ (ν x : ℂ))) := by
  intro s
  refine mellin_differentiableAt_of_isBigO_rpow (a := s.re + 1) (b := s.re - 1)
    ?_ ?_ (by linarith) ?_ (by linarith)
  · exact (continuous_ofReal.comp hν.continuous).continuousOn.locallyIntegrableOn
      measurableSet_Ioi
  · apply Asymptotics.IsBigO.trans_le (g' := fun _ ↦ (0 : ℝ)) ?_ (by simp)
    apply Filter.BigO_zero_atTop_of_support_in_Icc (a := 1 / 2) (b := 2)
    rwa [Function.support_ofReal]
  · apply Asymptotics.IsBigO.trans_le (g' := fun _ ↦ (0 : ℝ)) ?_ (by simp)
    apply Filter.BigO_zero_atZero_of_support_in_Icc (a := 1 / 2) (b := 2) (ha := by norm_num)
    rwa [Function.support_ofReal]

end LeanLab.PNTPort
