/-
P0028, https://arxiv.org/abs/1610.02017, Lemma 4.3 proof, page 9.
Continuity and moment estimates for the standard large spectrum covering argument.
The explicit Lipschitz constant follows from the sparse majorant mass bound.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSBohrPhases
namespace LeanLab.Ternary.MMS
open Finset

theorem norm_e_sub_e_le (x y : ℝ) : ‖e x - e y‖ ≤ 2 * Real.pi * |x - y| := by
  have he : e x - e y = e y * (e (x - y) - 1) := by
    rw [mul_sub, mul_one, ← e_add]
    rw [show y + (x - y) = x by ring]
  rw [he, norm_mul, norm_e, one_mul]
  exact norm_e_sub_one_le _

theorem prop31Hyp_fhat_lipschitz {N : ℕ} {η ε K q : ℝ} {f : ℕ → ℝ}
    (hf : Prop31Hyp N η ε K q f) (hη : η ≤ 1) (γ β : ℝ) :
    ‖fhat N f γ - fhat N f β‖ ≤ 4 * Real.pi * (N : ℝ) ^ 2 * |γ - β| := by
  have hhat (t : ℝ) : fhat N f t = ∑ n ∈ Icc 1 N, (f n : ℂ) * e (-(n : ℝ) * t) := by
    unfold fhat
    apply sum_congr rfl
    intro n hn
    unfold e
    congr 2
    push_cast
    ring
  have he : fhat N f γ - fhat N f β =
      ∑ n ∈ Icc 1 N, (f n : ℂ) * (e (-(n : ℝ) * γ) - e (-(n : ℝ) * β)) := by
    rw [hhat γ, hhat β, ← sum_sub_distrib]
    apply sum_congr rfl
    intro n hn
    ring
  have hpoint (n : ℕ) (hn : n ∈ Icc 1 N) :
      ‖(f n : ℂ) * (e (-(n : ℝ) * γ) - e (-(n : ℝ) * β))‖ ≤
        f n * (2 * Real.pi * N * |γ - β|) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hf.1 n hn)]
    apply mul_le_mul_of_nonneg_left _ (hf.1 n hn)
    have hφ := norm_e_sub_e_le (-(n : ℝ) * γ) (-(n : ℝ) * β)
    have habs : |-(n : ℝ) * γ - (-(n : ℝ) * β)| = (n : ℝ) * |γ - β| := by
      rw [show -(n : ℝ) * γ - (-(n : ℝ) * β) = -(n : ℝ) * (γ - β) by ring,
        abs_mul, abs_neg, abs_of_nonneg (Nat.cast_nonneg n)]
    rw [habs] at hφ
    have hnN : (n : ℝ) ≤ N := by exact_mod_cast (mem_Icc.mp hn).2
    calc _ ≤ 2 * Real.pi * ((n : ℝ) * |γ - β|) := hφ
      _ = 2 * Real.pi * (n : ℝ) * |γ - β| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hnN (by positivity)) (abs_nonneg _)
  have hmass : (∑ n ∈ Icc 1 N, f n) ≤ 2 * N := by
    have hm := prop31Hyp_mass_le hf
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith
  calc ‖fhat N f γ - fhat N f β‖ ≤
        ∑ n ∈ Icc 1 N, ‖(f n : ℂ) * (e (-(n : ℝ) * γ) - e (-(n : ℝ) * β))‖ := by
          rw [he]
          exact norm_sum_le _ _
    _ ≤ ∑ n ∈ Icc 1 N, f n * (2 * Real.pi * N * |γ - β|) := sum_le_sum hpoint
    _ = (∑ n ∈ Icc 1 N, f n) * (2 * Real.pi * N * |γ - β|) := (sum_mul _ _ _).symm
    _ ≤ (2 * N) * (2 * Real.pi * N * |γ - β|) :=
      mul_le_mul_of_nonneg_right hmass (by positivity)
    _ = _ := by ring

theorem prop31Hyp_near_large_frequency {N : ℕ} {η ε K q δ : ℝ} {f : ℕ → ℝ}
    (hf : Prop31Hyp N η ε K q f) (hη : η ≤ 1) (hN : 0 < N) (_hδ : 0 ≤ δ)
    (γ β : ℝ) (hlarge : δ * N ≤ ‖fhat N f γ‖)
    (hclose : |γ - β| ≤ δ / (8 * Real.pi * N)) :
    δ * N / 2 ≤ ‖fhat N f β‖ := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hlip := prop31Hyp_fhat_lipschitz hf hη γ β
  have hbound : ‖fhat N f γ - fhat N f β‖ ≤ δ * N / 2 := by
    calc _ ≤ 4 * Real.pi * (N : ℝ) ^ 2 * |γ - β| := hlip
      _ ≤ 4 * Real.pi * (N : ℝ) ^ 2 * (δ / (8 * Real.pi * N)) := by gcongr
      _ = _ := by field_simp; ring
  have htri := norm_sub_norm_le (fhat N f γ) (fhat N f β)
  linarith

theorem prop31Hyp_large_peak_integral {N : ℕ} {η ε K q δ r : ℝ} {f : ℕ → ℝ}
    (hf : Prop31Hyp N η ε K q f) (hη : η ≤ 1) (hN : 0 < N) (hδ : 0 ≤ δ)
    (hq : 0 ≤ q) (hr : 0 ≤ r) (hradius : r ≤ δ / (8 * Real.pi * N))
    (γ : ℝ) (hlarge : δ * N ≤ ‖fhat N f γ‖) :
    (δ * N / 2) ^ q * (2 * r) ≤
      ∫ β in (γ - r)..(γ + r), ‖fhat N f β‖ ^ q := by
  have hc : Continuous (fun β : ℝ => ‖fhat N f β‖ ^ q) :=
    (continuous_fhat N f).norm.rpow_const (fun _ => Or.inr hq)
  have hp (β : ℝ) (hβ : β ∈ Set.Icc (γ - r) (γ + r)) :
      (δ * N / 2) ^ q ≤ ‖fhat N f β‖ ^ q := by
    have hclose : |γ - β| ≤ δ / (8 * Real.pi * N) := by
      apply le_trans _ hradius
      rw [abs_le]
      constructor <;> linarith [hβ.1, hβ.2]
    exact Real.rpow_le_rpow (by positivity)
      (prop31Hyp_near_large_frequency hf hη hN hδ γ β hlarge hclose) hq
  calc (δ * N / 2) ^ q * (2 * r) =
      ∫ β in (γ - r)..(γ + r), (δ * N / 2) ^ q := by
        simp only [intervalIntegral.integral_const, smul_eq_mul]
        ring
    _ ≤ _ := intervalIntegral.integral_mono_on (by linarith)
      (intervalIntegrable_const) (hc.intervalIntegrable _ _) hp


theorem prop31Hyp_moment_le {N : ℕ} {η ε K q : ℝ} {f : ℕ → ℝ}
    (hf : Prop31Hyp N η ε K q f) (hN : 0 < N) (hK : 0 ≤ K) (hq : 0 < q) :
    (∫ γ in (0 : ℝ)..1, ‖fhat N f γ‖ ^ q) ≤ K ^ q * (N : ℝ) ^ (q - 1) := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hi : 0 ≤ ∫ γ in (0 : ℝ)..1, ‖fhat N f γ‖ ^ q :=
    intervalIntegral.integral_nonneg_of_forall (by norm_num)
      (fun _ => Real.rpow_nonneg (norm_nonneg _) _)
  have hm := Real.rpow_le_rpow (Real.rpow_nonneg hi _) hf.2.2.2 hq.le
  rw [← Real.rpow_mul hi, one_div_mul_cancel hq.ne', Real.rpow_one,
    Real.mul_rpow hK (Real.rpow_nonneg hNr.le _), ← Real.rpow_mul hNr.le] at hm
  have he : (1 - 1 / q) * q = q - 1 := by field_simp
  rwa [he] at hm

theorem fhat_periodic (N : ℕ) (f : ℕ → ℝ) : Function.Periodic (fhat N f) 1 := by
  let u := intervalLift N f
  have hp : Function.Periodic (intHat u) 1 := by
    intro γ
    simp only [intHat, Finsupp.linearCombination_apply, Finsupp.sum, Algebra.smul_def]
    apply sum_congr rfl
    intro n hn
    have he : -(n : ℝ) * (γ + 1) = -(n : ℝ) * γ + ((-n : ℤ) : ℝ) := by
      push_cast
      ring
    rw [he, e_add, e_int, mul_one]
  intro γ
  simpa only [u, intHat_intervalLift] using hp γ

end LeanLab.Ternary.MMS
