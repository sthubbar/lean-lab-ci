import LeanLab.ExceptionalSet.Decomp1539a

/-!
Elementary preparation for P0082 page359 Lemma4 from page354 Theorem2.
Source: https://doi.org/10.5802/aif.1621
The rounded upper half index preserves the printed choice c equal to one half.
The discrepancy argument omitted on page359 stays open.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp547a

open Real Finset Filter
open scoped Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (Theorem2 eC expSumF norm_eC)

/-- P0082 pages354 and359, auxiliary exact endpoint correction.
The upper rounded half interval differs by at most one term of norm one. -/
theorem upper_half_sum_norm_le (γ α : ℝ) (N : ℕ) :
    ‖∑ n ∈ Ioc (N / 2) N, eC (α * F γ n)‖ ≤
      ‖expSumF γ α ((N + 1) / 2)‖ + 1 := by
  classical
  let s := Ioc (N / 2) N
  let t := Icc ((N + 1) / 2) (2 * ((N + 1) / 2))
  let f : ℕ → ℂ := fun n => eC (α * F γ n)
  have hst : s ⊆ t := by
    intro n hn
    simp only [s, t, mem_Ioc, mem_Icc] at hn ⊢
    omega
  have hcard : (t \ s).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    simp only [Finset.mem_sdiff, s, t, Finset.mem_Icc, Finset.mem_Ioc, not_and_or, not_lt, not_le] at ha hb
    omega
  have heq : (∑ n ∈ s, f n) = (∑ n ∈ t, f n) - ∑ n ∈ t \ s, f n := by
    have hh := Finset.sum_sdiff hst (f := f)
    linear_combination hh
  have hnorm : ‖∑ n ∈ t \ s, f n‖ ≤ 1 := by
    calc
      _ ≤ ∑ n ∈ t \ s, ‖f n‖ := norm_sum_le _ _
      _ = ((t \ s).card : ℝ) := by simp [f, norm_eC]
      _ ≤ 1 := by exact_mod_cast hcard
  change ‖∑ n ∈ s, f n‖ ≤ ‖∑ n ∈ t, f n‖ + 1
  rw [heq]
  exact (norm_sub_le _ _).trans (by linarith)

/-- P0082 pages354 and359, auxiliary logarithmic comparison.
For N at least sixteen, log N is at most twice the logarithm
of the rounded upper half index. -/
theorem upper_half_log (N : ℕ) (hN : 16 ≤ N) :
    0 < Real.log ((N + 1) / 2 : ℕ) ∧
      Real.log (N : ℝ) ≤ 2 * Real.log ((N + 1) / 2 : ℕ) := by
  have hm : 8 ≤ (N + 1) / 2 := by omega
  have hmr : (8 : ℝ) ≤ ((N + 1) / 2 : ℕ) := by exact_mod_cast hm
  have hNr : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hdouble : (N : ℝ) ≤ 2 * ((N + 1) / 2 : ℕ) := by
    exact_mod_cast (show N ≤ 2 * ((N + 1) / 2) by omega)
  have hsquare : (N : ℝ) ≤ (((N + 1) / 2 : ℕ) : ℝ) ^ 2 := by nlinarith
  refine ⟨Real.log_pos (by linarith), ?_⟩
  calc
    _ ≤ Real.log ((((N + 1) / 2 : ℕ) : ℝ) ^ 2) := Real.log_le_log hNr hsquare
    _ = _ := by rw [Real.log_pow]; norm_num

/-- P0082 page359, the c equal to one half specialization of Theorem2.
The small positive upper exponent has a factor four margin.
No cancellation estimate is assumed in this scalar range lemma. -/
theorem upper_half_frequency_range (γ α : ℝ) (hγ1 : 1 < γ) (hγ2 : γ < 3 / 2)
    (N h : ℕ) (hN : 16 ≤ N) (hh : 1 ≤ h)
    (hαlow : F γ N ^ (-(1 / 2 : ℝ)) < |α|) (hαhigh : |α| ≤ 1)
    (hhhigh : (h : ℝ) ≤ F γ N ^ ((γ - 1) / 8)) :
    F γ (2 * ((N + 1) / 2 : ℕ)) ^ (-(1 / 2 : ℝ)) ≤ |(h : ℝ) * α| ∧
      |(h : ℝ) * α| ≤ F γ ((N + 1) / 2 : ℕ) ^ ((γ - 1) / 2) := by
  have hγ : 0 ≤ γ := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  obtain ⟨hmL, hlog⟩ := upper_half_log N hN
  have hpow : Real.log (N : ℝ) ^ γ ≤ 4 * Real.log ((N + 1) / 2 : ℕ) ^ γ := by
    calc
      _ ≤ (2 * Real.log ((N + 1) / 2 : ℕ)) ^ γ := Real.rpow_le_rpow hL hlog hγ
      _ = (2 : ℝ) ^ γ * Real.log ((N + 1) / 2 : ℕ) ^ γ :=
        Real.mul_rpow (by norm_num) hmL.le
      _ ≤ 4 * Real.log ((N + 1) / 2 : ℕ) ^ γ := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hmL.le _)
        calc
          (2 : ℝ) ^ γ ≤ (2 : ℝ) ^ (2 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
          _ = 4 := by norm_num
  have hupper : F γ N ^ ((γ - 1) / 8) ≤
      F γ ((N + 1) / 2 : ℕ) ^ ((γ - 1) / 2) := by
    simp only [F, ← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    nlinarith
  have hdouble : (N : ℝ) ≤ 2 * ((N + 1) / 2 : ℕ) := by
    exact_mod_cast (show N ≤ 2 * ((N + 1) / 2) by omega)
  have hpow2 : Real.log (N : ℝ) ^ γ ≤
      Real.log (2 * ((N + 1) / 2 : ℕ)) ^ γ := by
    apply Real.rpow_le_rpow hL _ hγ
    exact Real.log_le_log hNpos hdouble
  have hlower : F γ (2 * ((N + 1) / 2 : ℕ)) ^ (-(1 / 2 : ℝ)) ≤
      F γ N ^ (-(1 / 2 : ℝ)) := by
    simp only [F, ← Real.exp_mul]
    exact Real.exp_le_exp.mpr (by linarith)
  have hhr : (1 : ℝ) ≤ h := by exact_mod_cast hh
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg h)]
  constructor
  · exact hlower.trans (hαlow.le.trans (by nlinarith [abs_nonneg α]))
  · exact (mul_le_of_le_one_right (Nat.cast_nonneg h) hαhigh).trans (hhhigh.trans hupper)

/-- P0082 pages354 and359, auxiliary asymptotic scale comparison.
Every positive logarithm power at the rounded upper half index
is eventually at least any fixed fraction below one of its value at N.
The squeeze proof adapts the lower half comparison in Decomp450e. -/
theorem upper_half_power_lower (γ ε : ℝ) (_hγ : 0 < γ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (1 - ε) * Real.log (N : ℝ) ^ γ ≤ Real.log ((N + 1) / 2 : ℕ) ^ γ := by
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hlow : Tendsto (fun N : ℕ => 1 - Real.log 2 / Real.log (N : ℝ)) atTop (𝓝 1) := by
    simpa only [sub_zero] using tendsto_const_nhds.sub (hl.const_div_atTop (Real.log 2))
  have hr : Tendsto (fun N : ℕ => Real.log ((N + 1) / 2 : ℕ) / Real.log (N : ℝ))
      atTop (𝓝 1) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    · filter_upwards [eventually_ge_atTop (16 : ℕ)] with N hN
      have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
      have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
      have hm : (N : ℝ) / 2 ≤ ((N + 1) / 2 : ℕ) := by
        have hh : N ≤ 2 * ((N + 1) / 2) := by omega
        have hh' : (N : ℝ) ≤ 2 * ((N + 1) / 2 : ℕ) := by exact_mod_cast hh
        linarith
      have hc := Real.log_le_log (by positivity : (0 : ℝ) < (N : ℝ) / 2) hm
      rw [Real.log_div hNpos.ne' (by norm_num : (2 : ℝ) ≠ 0)] at hc
      have he : 1 - Real.log 2 / Real.log (N : ℝ) =
          (Real.log (N : ℝ) - Real.log 2) / Real.log (N : ℝ) := by field_simp
      rw [he]
      exact div_le_div_of_nonneg_right hc hL.le
    · filter_upwards [eventually_ge_atTop (16 : ℕ)] with N hN
      have hm : (0 : ℝ) < ((N + 1) / 2 : ℕ) := by exact_mod_cast (by omega : 0 < (N + 1) / 2)
      have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
      apply (div_le_one hL).mpr
      apply Real.log_le_log hm
      exact_mod_cast (show (N + 1) / 2 ≤ N by omega)
  have ht : Tendsto (fun N : ℕ =>
      (Real.log ((N + 1) / 2 : ℕ) / Real.log (N : ℝ)) ^ γ) atTop (𝓝 1) := by
    simpa only [Real.one_rpow] using hr.rpow_const (Or.inl (by norm_num : (1 : ℝ) ≠ 0))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp ((tendsto_order.mp ht).1 (1 - ε) (by linarith))
  refine ⟨max 16 N₀, fun N hN => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  obtain ⟨hmL, -⟩ := upper_half_log N hN16
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hh := (hN₀ N ((le_max_right _ _).trans hN)).le
  rw [Real.div_rpow hmL.le hL.le] at hh
  exact (le_div_iff₀ (Real.rpow_pos_of_pos hL γ)).mp hh

/-- P0082 page359, the full upper exponent specialization of Theorem2.
The intermediate exponent is strictly between C and gamma minus one.
The lower frequency bound uses the printed c equal to one half. -/
theorem upper_half_frequency_range_full (γ C : ℝ) (_hγ1 : 1 < γ) (hγ2 : γ < 3 / 2)
    (hC : 0 < C) (hCγ : C < γ - 1) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ α : ℝ,
      F γ N ^ (-(1 / 2 : ℝ)) < |α| → |α| ≤ 1 → ∀ h : ℕ, 1 ≤ h →
      (h : ℝ) ≤ F γ N ^ C →
      F γ (2 * ((N + 1) / 2 : ℕ)) ^ (-(1 / 2 : ℝ)) ≤ |(h : ℝ) * α| ∧
        |(h : ℝ) * α| ≤ F γ ((N + 1) / 2 : ℕ) ^ ((C + γ - 1) / 2) := by
  let D := (C + γ - 1) / 2
  have hD : 0 < D := by dsimp [D]; linarith
  have hCD : C < D := by dsimp [D]; linarith
  let ε := 1 - C / D
  have hε : 0 < ε := by dsimp [ε]; exact sub_pos.mpr ((div_lt_one hD).mpr hCD)
  obtain ⟨N₀, hN₀⟩ := upper_half_power_lower γ ε (by linarith) hε
  refine ⟨max 16 N₀, fun N hN α hαlow hαhigh h hh hhhigh => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
  have hp := hN₀ N ((le_max_right _ _).trans hN)
  have hcoef : D * (1 - ε) = C := by dsimp [ε]; field_simp; ring
  have hupper : F γ N ^ C ≤ F γ ((N + 1) / 2 : ℕ) ^ D := by
    simp only [F, ← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    have hm := mul_le_mul_of_nonneg_left hp hD.le
    rw [← mul_assoc, hcoef] at hm
    nlinarith
  have hdouble : (N : ℝ) ≤ 2 * ((N + 1) / 2 : ℕ) := by
    exact_mod_cast (show N ≤ 2 * ((N + 1) / 2) by omega)
  have hpow : Real.log (N : ℝ) ^ γ ≤ Real.log (2 * ((N + 1) / 2 : ℕ)) ^ γ :=
    Real.rpow_le_rpow hL (Real.log_le_log hNpos hdouble) (by linarith)
  have hlower : F γ (2 * ((N + 1) / 2 : ℕ)) ^ (-(1 / 2 : ℝ)) ≤ F γ N ^ (-(1 / 2 : ℝ)) := by
    simp only [F, ← Real.exp_mul]
    exact Real.exp_le_exp.mpr (by linarith)
  have hhr : (1 : ℝ) ≤ h := by exact_mod_cast hh
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg h)]
  constructor
  · exact hlower.trans (hαlow.le.trans (by nlinarith [abs_nonneg α]))
  · exact (mul_le_of_le_one_right (Nat.cast_nonneg h) hαhigh).trans (hhhigh.trans hupper)

/-- P0082 pages354 and359, the full integer frequency input for Lemma4.
This is CONDITIONAL ON the explicit Theorem2 hypothesis for every allowed C.
No discrepancy theorem or Karacuba result occurs in the proof. -/
theorem integer_multiple_decay_full (hT : Theorem2) (γ : ℝ)
    (hγ1 : 1 < γ) (hγ2 : γ < 3 / 2) (C : ℝ) (hC : 0 < C) (hCγ : C < γ - 1) :
    ∃ κ B : ℝ, 0 < κ ∧ 0 < B ∧ ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ,
      F γ N ^ (-(1 / 2 : ℝ)) < |α| → |α| ≤ 1 → ∀ h : ℕ, 1 ≤ h →
      (h : ℝ) ≤ F γ N ^ C →
      ‖∑ n ∈ Ioc (N / 2) N, eC ((h : ℝ) * α * F γ n)‖ ≤
        B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  obtain ⟨η, A, hη, hsum⟩ := hT γ hγ1 hγ2 (1 / 2) ((C + γ - 1) / 2)
    (by norm_num) (by norm_num) (by linarith) (by linarith)
  have hp0 : 0 < 3 - 2 * γ := by linarith
  have hp1 : 3 - 2 * γ < 1 := by linarith
  have ht : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (1 - (3 - 2 * γ))) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < 1 - (3 - 2 * γ))).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (η / 2))
  obtain ⟨Nr, hr⟩ := upper_half_frequency_range_full γ C hγ1 hγ2 hC hCγ
  let M := max 16 (max N₀ Nr)
  let B := max (|A| + 2) (Real.exp (η / 2 * Real.log (M : ℝ) ^ (3 - 2 * γ)))
  have hB : 0 < B := (by positivity : 0 < |A| + 2).trans_le (le_max_left _ _)
  refine ⟨η / 2, B, by positivity, hB, ?_⟩
  intro N hN α hαlow hαhigh h hh hhhigh
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hL : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hu : 0 ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) := Real.rpow_nonneg hL _
  by_cases hNM : M ≤ N
  · have hN16 : 16 ≤ N := (le_max_left _ _).trans hNM
    have hNN₀ : N₀ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hNM)
    have hNr : Nr ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hNM)
    obtain ⟨hmL, hlog⟩ := upper_half_log N hN16
    have hpow : Real.log (N : ℝ) ^ (3 - 2 * γ) ≤
        2 * Real.log ((N + 1) / 2 : ℕ) ^ (3 - 2 * γ) := by
      calc
        _ ≤ (2 * Real.log ((N + 1) / 2 : ℕ)) ^ (3 - 2 * γ) :=
          Real.rpow_le_rpow hL hlog hp0.le
        _ = (2 : ℝ) ^ (3 - 2 * γ) * Real.log ((N + 1) / 2 : ℕ) ^ (3 - 2 * γ) :=
          Real.mul_rpow (by norm_num) hmL.le
        _ ≤ 2 * Real.log ((N + 1) / 2 : ℕ) ^ (3 - 2 * γ) := by
          apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hmL.le _)
          simpa only [Real.rpow_one] using
            Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hp1.le
    have hdecay : Real.exp (-η * Real.log ((N + 1) / 2 : ℕ) ^ (3 - 2 * γ)) ≤
        Real.exp (-(η / 2) * Real.log (N : ℝ) ^ (3 - 2 * γ)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hlogpos : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
    have hscale : η / 2 * Real.log (N : ℝ) ^ (3 - 2 * γ) ≤ Real.log (N : ℝ) := by
      have hh := mul_le_mul_of_nonneg_left (hN₀ N hNN₀) hu
      rw [← Real.rpow_add hlogpos] at hh
      have he : (3 - 2 * γ) + (1 - (3 - 2 * γ)) = 1 := by ring
      rw [he, Real.rpow_one] at hh
      nlinarith
    have hunit : 1 ≤ (N : ℝ) * Real.exp (-(η / 2) * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by
      have he := Real.exp_le_exp.mpr hscale
      rw [Real.exp_log hNpos] at he
      have hh := mul_le_mul_of_nonneg_right he
        (Real.exp_pos (-(η / 2) * Real.log (N : ℝ) ^ (3 - 2 * γ))).le
      rw [← Real.exp_add] at hh
      simpa using hh
    obtain ⟨hl, hr⟩ := hr N hNr α hαlow hαhigh h hh hhhigh
    have hraw := hsum ((N + 1) / 2) (by omega) ((h : ℝ) * α) hl hr
    have hraw' : ‖expSumF γ ((h : ℝ) * α) ((N + 1) / 2)‖ ≤
        (|A| + 1) * N * Real.exp (-(η / 2) * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by
      refine hraw.trans ?_
      calc
        _ ≤ (|A| + 1) * ((N + 1) / 2 : ℕ) *
            Real.exp (-η * Real.log ((N + 1) / 2 : ℕ) ^ (3 - 2 * γ)) := by
          gcongr
          exact (le_abs_self A).trans (by linarith)
        _ ≤ _ := by
          gcongr
          · exact_mod_cast (show (N + 1) / 2 ≤ N by omega)
    have hend := upper_half_sum_norm_le γ ((h : ℝ) * α) N
    have hcoef : |A| + 2 ≤ B := le_max_left _ _
    have hcoeff := mul_le_mul_of_nonneg_right hcoef
      (by positivity : 0 ≤ (N : ℝ) * Real.exp (-(η / 2) * Real.log (N : ℝ) ^ (3 - 2 * γ)))
    nlinarith
  · have hNM' : N ≤ M := by omega
    have hMpos : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by dsimp [M]; omega)
    have hpow : Real.log (N : ℝ) ^ (3 - 2 * γ) ≤ Real.log (M : ℝ) ^ (3 - 2 * γ) :=
      Real.rpow_le_rpow hL (Real.log_le_log hNpos (by exact_mod_cast hNM')) hp0.le
    have he : 1 ≤ Real.exp (η / 2 * Real.log (M : ℝ) ^ (3 - 2 * γ)) *
        Real.exp (-(η / 2) * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp
      nlinarith
    have hcoef : Real.exp (η / 2 * Real.log (M : ℝ) ^ (3 - 2 * γ)) ≤ B := le_max_right _ _
    have hbound : ‖∑ n ∈ Ioc (N / 2) N, eC ((h : ℝ) * α * F γ n)‖ ≤ (N : ℝ) := by
      calc
        _ ≤ ∑ n ∈ Ioc (N / 2) N, ‖eC ((h : ℝ) * α * F γ n)‖ := norm_sum_le _ _
        _ = ((N - N / 2 : ℕ) : ℝ) := by simp [norm_eC, Nat.card_Ioc]
        _ ≤ _ := by exact_mod_cast (show N - N / 2 ≤ N by omega)
    have he' := mul_le_mul_of_nonneg_right hcoef
      (Real.exp_pos (-(η / 2) * Real.log (N : ℝ) ^ (3 - 2 * γ))).le
    have hunit : 1 ≤ B * Real.exp (-(η / 2) * Real.log (N : ℝ) ^ (3 - 2 * γ)) := he.trans he'
    nlinarith

/-- P0082 pages354 and359, the integer multiple exponential sums.
This is CONDITIONAL ON the explicit Theorem2 hypothesis.
It uses c equal to one half and leaves the discrepancy theorem open. -/
theorem integer_multiple_decay (hT : Theorem2) (γ : ℝ)
    (hγ1 : 1 < γ) (hγ2 : γ < 3 / 2) :
    ∃ κ B : ℝ, 0 < κ ∧ 0 < B ∧ ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ,
      F γ N ^ (-(1 / 2 : ℝ)) < |α| → |α| ≤ 1 → ∀ h : ℕ, 1 ≤ h →
      (h : ℝ) ≤ F γ N ^ ((γ - 1) / 8) →
      ‖∑ n ∈ Ioc (N / 2) N, eC ((h : ℝ) * α * F γ n)‖ ≤
        B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  exact integer_multiple_decay_full hT γ hγ1 hγ2 ((γ - 1) / 8) (by linarith) (by linarith)

end LeanLab.ExceptionalSet.Decomp547a
