/-
Elementary assembly for the shared P0079 arc leaves.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp293a

open Real Finset MeasureTheory Filter

noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 4, display 15. This identity needs integrability, not analytic estimates. -/
theorem arc_split293 (f : ℝ → ℂ) (hf : Integrable f) (X L : ℝ) :
    (∫ α : ℝ, f α) = (∫ α in major293 X, f α) +
      (∫ α in minor293 X L, f α) + (∫ α in trivial293 X L, f α) := by
  have hM : MeasurableSet (major293 X) := by
    unfold major293
    exact measurableSet_le measurable_abs measurable_const
  have hm : MeasurableSet (minor293 X L) := by
    unfold minor293
    exact (measurableSet_lt measurable_const measurable_abs).inter
      (measurableSet_le measurable_abs measurable_const)
  have hd : Disjoint (major293 X) (minor293 X L) := by
    rw [Set.disjoint_left]
    intro α hα hα'
    exact (not_lt_of_ge hα) hα'.1
  have hu := integral_add_compl (hM.union hm) hf
  rw [setIntegral_union hd hm hf.integrableOn hf.integrableOn] at hu
  exact hu.symm

/-- P0079 pages 4 to 5, displays 15 to 19. Bounds for three arc pieces give
an explicit lower bound. No positivity of the coefficient is assumed or asserted. -/
theorem arc_lower293 (f : ℝ → ℂ) (hf : Integrable f) (X L A B D W : ℝ)
    (hM : A * W ≤ (∫ α in major293 X, f α).re)
    (hm : ‖∫ α in minor293 X L, f α‖ ≤ B * W)
    (ht : ‖∫ α in trivial293 X L, f α‖ ≤ D * W) :
    (A - B - D) * W ≤ (∫ α : ℝ, f α).re := by
  rw [arc_split293 f hf X L, Complex.add_re, Complex.add_re]
  have hmr := (abs_le.mp (Complex.abs_re_le_norm (∫ α in minor293 X L, f α))).1
  have htr := (abs_le.mp (Complex.abs_re_le_norm (∫ α in trivial293 X L, f α))).1
  nlinarith

/-- P0079 page 4, the cutoff is nonnegative once the box is large enough. -/
theorem cutoff_nonneg293 (s : ℕ) (μ : ℕ → ℝ) (ε X : ℝ)
    (hM : 0 < ∑ i : Fin s, |μ i|)
    (hX : 2 * ∑ i : Fin s, |μ i| ≤ ε * X) :
    0 ≤ cutoff293 s μ ε X := by
  unfold cutoff293
  apply Real.logb_nonneg (by norm_num : (1 : ℝ) < 2)
  exact (one_le_div (by positivity)).mpr hX

/-- P0079 page 4, the additive character has unit norm. -/
theorem character_norm293 (u : ℝ) : ‖character293 u‖ = 1 := by
  exact Complex.norm_exp_ofReal_mul_I _

/-- P0079 page 4, display 12. The continuous kernel is nonnegative. -/
theorem kernel_nonneg293 (η α : ℝ) : 0 ≤ kernel293 η α := by
  exact sq_nonneg _

/-- P0079 page 4, display 12. The continuous kernel is at most eta squared. -/
theorem kernel_le293 (η α : ℝ) : kernel293 η α ≤ η ^ 2 := by
  have h := mul_self_le_mul_self (abs_nonneg (Real.sinc (Real.pi * η * α)))
    (Real.abs_sinc_le_one (Real.pi * η * α))
  simp only [← pow_two, sq_abs, one_pow] at h
  simpa only [kernel293, mul_pow, mul_one] using mul_le_mul_of_nonneg_left h (sq_nonneg η)

/-- P0079 page 4, the logarithmic cutoff is eventually at least a positive
constant times log X. The constant is independent of the coefficient mass. -/
theorem cutoff_log_lower293 (s : ℕ) (μ : ℕ → ℝ) (ε : ℝ)
    (hM : 0 < ∑ i : Fin s, |μ i|) (hε : 0 < ε) :
    ∀ᶠ X : ℝ in atTop,
      (1 / (2 * log 2)) * log X ≤ cutoff293 s μ ε X := by
  have hratio : 0 < ε / (2 * ∑ i : Fin s, |μ i|) := by positivity
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have H := tendsto_log_atTop.eventually
    (eventually_ge_atTop (-2 * log (ε / (2 * ∑ i : Fin s, |μ i|))))
  filter_upwards [H, eventually_gt_atTop (0 : ℝ)] with X hlogX hX
  unfold cutoff293 Real.logb
  rw [show ε * X / (2 * ∑ i : Fin s, |μ i|) =
      (ε / (2 * ∑ i : Fin s, |μ i|)) * X by ring,
    log_mul hratio.ne' hX.ne']
  apply (le_div_iff₀ hlog2).mpr
  have heq : (1 / (2 * log 2)) * log X * log 2 = log X / 2 := by
    field_simp
  rw [heq]
  linarith

/-- P0079 page 4, display 13 and its counting consequence. This elementary
conversion keeps the quantitative constant explicit. -/
theorem count_to_density293 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε c : ℝ)
    (hs : 2 ≤ s) (hM : 0 < ∑ i : Fin s, |μ i|) (hη : 0 < η) (hε : 0 < ε)
    (hc : 0 < c)
    (hcount : ∀ᶠ X : ℝ in atTop, c * X * (cutoff293 s μ ε X) ^ s ≤
      η * (log X) ^ 2 * NX l1 l2 (fun i : Fin s => μ i) γ η ε X) :
    ∃ c' X0 : ℝ, 0 < c' ∧ ∀ X, X0 ≤ X →
      c' * X * (log X) ^ (s - 2) ≤ NX l1 l2 (fun i : Fin s => μ i) γ η ε X := by
  let a : ℝ := 1 / (2 * log 2)
  have ha : 0 < a := by dsimp [a]; positivity
  refine ⟨c * a ^ s / η, ?_⟩
  have H : ∀ᶠ X : ℝ in atTop,
      (c * a ^ s / η) * X * (log X) ^ (s - 2) ≤
        NX l1 l2 (fun i : Fin s => μ i) γ η ε X := by
    filter_upwards [hcount, cutoff_log_lower293 s μ ε hM hε,
      eventually_ge_atTop (2 : ℝ)] with X hb hL hX
    have hlog : 0 < log X := log_pos (by linarith)
    have hXL : 0 ≤ a * log X := mul_nonneg ha.le hlog.le
    have hpow := pow_le_pow_left₀ hXL hL s
    have hprod := mul_le_mul_of_nonneg_left hpow (show 0 ≤ c * X by positivity)
    have heq : ((c * a ^ s / η) * X * (log X) ^ (s - 2)) *
        (η * (log X) ^ 2) = c * X * (a * log X) ^ s := by
      have hp : (log X) ^ (s - 2) * (log X) ^ 2 = (log X) ^ s := by
        rw [← pow_add, Nat.sub_add_cancel hs]
      rw [mul_pow]
      calc
        _ = c * X * a ^ s * ((log X) ^ (s - 2) * (log X) ^ 2) := by
          field_simp
        _ = _ := by rw [hp]; ring
    apply (mul_le_mul_iff_left₀ (show 0 < η * (log X) ^ 2 by positivity)).mp
    rw [heq]
    nlinarith only [hprod, hb]
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp H
  exact ⟨X0, by positivity, hX0⟩

/-- P0079 page 12, Section 8 and display 19. At exact equality in the
limiting coefficient, every positive epsilon makes the displayed margin negative.
This checks the existing QUESTION. It is not an OPEN assumption. -/
theorem endpoint_margin_negative293 (l1 l2 η ε B : ℝ)
    (h1 : 0 < l1) (hp : 0 < |l1 * l2|) (hη : 0 < η) (hε : 0 < ε)
    (hB : B = η / (2 * |l1 * l2|)) :
    (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η - B < 0 := by
  have heq : (1 - 4 * l1 * ε) / (2 * |l1 * l2|) * η - B =
      -(4 * l1 * ε * η) / (2 * |l1 * l2|) := by
    rw [hB]
    ring
  rw [heq]
  exact div_neg_of_neg_of_pos (neg_lt_zero.mpr (by positivity)) (by positivity)

end LeanLab.LZPowersOfTwo
