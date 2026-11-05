import LeanLab.ChenDoubleSieve.Decomp363a
import LeanLab.ChenDoubleSieve.Decomp348p

/-!
The elementary logarithmic integral replacement in Wu 2004 equation 10.2.
The integral error bound is reused from Mathlib's Chebyshev module.
Source: https://arxiv.org/pdf/0705.1652, pages 6 and 38.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set MeasureTheory intervalIntegral
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task363
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-- Powers of reciprocal logarithms are integrable on closed intervals above two. -/
theorem inv_log_pow_integrable {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) (k : ℕ) :
    IntervalIntegrable (fun t : ℝ => 1 / log t ^ k) volume a b := by
  apply ContinuousOn.intervalIntegrable_of_Icc hab
  apply ContinuousOn.div continuousOn_const
  · apply ContinuousOn.pow
    apply ContinuousOn.log continuousOn_id
    intro t ht
    change t ≠ 0
    linarith [ht.1]
  · intro t ht
    exact pow_ne_zero _ (log_pos (by linarith [ht.1])).ne'

/-- Exact elementary integration by parts for the paper's logarithmic integral. -/
theorem li_integral_remainder {x : ℝ} (hx : 2 ≤ x) :
    Wu04.li x = x / log x - 2 / log 2 + ∫ t in (2 : ℝ)..x, 1 / log t ^ 2 := by
  have hd : ∀ t ∈ uIcc (2 : ℝ) x,
      HasDerivAt (fun t : ℝ => t / log t)
        (1 / log t - 1 / log t ^ 2) t := by
    intro t ht
    rw [uIcc_of_le hx] at ht
    have htpos : 0 < t := by linarith [ht.1]
    have hlog : log t ≠ 0 := (log_pos (by linarith [ht.1])).ne'
    convert (hasDerivAt_id t).div (hasDerivAt_log htpos.ne') hlog using 1
    · rfl
    · dsimp only [id_eq]
      field_simp [htpos.ne', hlog]
  have hi := (inv_log_pow_integrable (le_refl (2 : ℝ)) hx 1).sub
    (inv_log_pow_integrable (le_refl (2 : ℝ)) hx 2)
  simp only [pow_one] at hi
  have he := integral_eq_sub_of_hasDerivAt hd hi
  rw [integral_sub (by simpa using inv_log_pow_integrable (le_refl (2 : ℝ)) hx 1)
    (inv_log_pow_integrable (le_refl (2 : ℝ)) hx 2)] at he
  unfold Wu04.li
  simp only [one_div] at he ⊢
  linarith

/-- The logarithmic integral replacement error is smaller than x over log x. -/
theorem li_relative_error :
    (fun x : ℝ => Wu04.li x - x / log x) =o[atTop] (fun x => x / log x) := by
  have hsmall : (fun x : ℝ => x / log x ^ 2) =o[atTop] (fun x => x / log x) := by
    simpa only [div_eq_mul_inv, inv_pow, pow_two, mul_assoc, mul_one, mul_inv_rev] using
      (Asymptotics.isBigO_refl (fun x : ℝ => x / log x) atTop).mul_isLittleO
        Real.inv_log_isLittleO_one
  have hc : (fun _ : ℝ => 2 / log 2) =o[atTop] (fun x => x / log x) := by
    have hn : ∀ᶠ x : ℝ in atTop, log x ≠ 0 := by
      filter_upwards [eventually_gt_atTop (1 : ℝ)] with x hx
      exact (log_pos hx).ne'
    have hh : (fun x : ℝ => (2 / log 2 : ℝ) * log x) =o[atTop] (fun x : ℝ => x) :=
      Real.isLittleO_log_id_atTop.const_mul_left (2 / log 2 : ℝ)
    exact (Asymptotics.isLittleO_mul_iff_isLittleO_div (𝕜 := ℝ) hn).mp
      (by simpa only [mul_comm] using hh)
  have he := (Chebyshev.integral_one_div_log_sq_isBigO.trans_isLittleO hsmall).sub hc
  apply he.congr' _ (Eventually.of_forall fun _ => rfl)
  filter_upwards [eventually_ge_atTop (2 : ℝ)] with x hx
  rw [li_integral_remainder hx]
  ring

/-- The paper's logarithmic integral divided by x over log x tends to one. -/
theorem li_ratio_tendsto :
    Tendsto (fun x : ℝ => Wu04.li x / (x / log x)) atTop (𝓝 1) := by
  have ht := li_relative_error.tendsto_div_nhds_zero.add_const 1
  simp only [zero_add] at ht
  apply ht.congr'
  filter_upwards [eventually_gt_atTop (2 : ℝ)] with x hx
  have hlog : log x ≠ 0 := (log_pos (by linarith)).ne'
  have hpos : x ≠ 0 := by linarith
  field_simp
  ring



/-- The li form of the finite main term in Lemma 2.2. -/
def liMain0 (f : ℝ → ℝ) (B : ℝ) (N : ℕ) : ℝ :=
  Wu04.li N * lowerDensity N * f (lowerLevel B N 1)

/-- Exact ratio of the two finite main terms above one. -/
theorem liMain0_ratio (f : ℝ → ℝ) (B : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    liMain0 f B N / Θ N =
      (Wu04.li N / ((N : ℝ) / log N)) * (main0 f B N / Θ N) := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : log (N : ℝ) ≠ 0 :=
    (log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  unfold liMain0 main0
  field_simp [hpos.ne', hlog]

/-- The local li density scale has the same exact coefficient limit. -/
theorem li_density_scale_tendsto :
    Tendsto (fun N : ℕ => Wu04.li N * lowerDensity N / Θ N) evenAtTop
      (𝓝 (2 / (kappa1 * exp eulerMascheroniConstant))) := by
  have hl : Tendsto (fun N : ℕ => Wu04.li N / ((N : ℝ) / log N))
      evenAtTop (𝓝 1) :=
    tendsto_inf_left (li_ratio_tendsto.comp tendsto_natCast_atTop_atTop)
  have ht := hl.mul scaledDensity_supplied
  simp only [one_mul] at ht
  apply ht.congr'
  filter_upwards [(eventually_ge_atTop (2 : ℕ)).filter_mono inf_le_left] with N hN
  rw [← density_scale_ratio hN]
  have he := liMain0_ratio (fun _ => 1) 1 hN
  simpa only [liMain0, main0, mul_one] using he.symm

/-- The li density scale is bounded by a fixed positive multiple of Theta. -/
theorem li_density_scale_bounded : ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      Wu04.li N * lowerDensity N ≤ K * Θ N := by
  let c : ℝ := 2 / (kappa1 * exp eulerMascheroniConstant)
  have hc : 0 < c := by dsimp [c, kappa1]; positivity
  have he : ∀ᶠ N : ℕ in evenAtTop, Wu04.li N * lowerDensity N / Θ N < c + 1 :=
    li_density_scale_tendsto.eventually (eventually_lt_nhds (by dsimp [c]; linarith))
  obtain ⟨M, hM⟩ := eventually_atTop.1 (eventually_inf_principal.1 he)
  refine ⟨c + 1, by linarith, max 2 M, ?_⟩
  intro N hEven hN
  exact (div_le_iff₀ (Θ_pos (by omega : 2 ≤ N))).1 (hM N (by omega) hEven).le

/-- Replacing li by N over log N changes the finite main term negligibly.
CONDITIONAL ON IsLinearSieve only. No OPEN leaf is used. -/
theorem liMain0_error_tendsto (F f : ℝ → ℝ) (h : IsLinearSieve F f) (B : ℝ) :
    Tendsto (fun N : ℕ => (main0 f B N - liMain0 f B N) / Θ N)
      evenAtTop (𝓝 0) := by
  have hli : Tendsto (fun N : ℕ => Wu04.li N / ((N : ℝ) / log N))
      evenAtTop (𝓝 1) :=
    tendsto_inf_left (li_ratio_tendsto.comp tendsto_natCast_atTop_atTop)
  have hl : Tendsto (fun N : ℕ => 1 - Wu04.li N / ((N : ℝ) / log N))
      evenAtTop (𝓝 0) := by
    simpa only [sub_self] using hli.const_sub 1
  have ht := hl.mul (Task348.Supplied.main0_tendsto F f (fun _ => 0) h B)
  simp only [zero_mul] at ht
  apply ht.congr'
  filter_upwards [(eventually_ge_atTop (2 : ℕ)).filter_mono inf_le_left] with N hN
  rw [sub_div, liMain0_ratio f B hN]
  ring

/-- The absolute li replacement error is absorbed by any positive Theta budget.
CONDITIONAL ON IsLinearSieve only. -/
theorem liMain0_error_absorbed (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B η : ℝ) (hη : 0 < η) : ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        |main0 f B N - liMain0 f B N| ≤ η * Θ N := by
  have he : ∀ᶠ N in evenAtTop,
      |(main0 f B N - liMain0 f B N) / Θ N| < η :=
    (liMain0_error_tendsto F f h B).abs.eventually
      (by simpa using eventually_lt_nhds hη)
  obtain ⟨M, hM⟩ := eventually_atTop.1 (eventually_inf_principal.1 he)
  refine ⟨max 2 M, ?_⟩
  intro N hEven hN
  have ht : 0 < Θ N := Θ_pos (by omega)
  have hb := (hM N (by omega) hEven).le
  rw [abs_div, abs_of_pos ht] at hb
  exact (div_le_iff₀ ht).1 hb

end LeanLab.ChenDoubleSieve.Task363
