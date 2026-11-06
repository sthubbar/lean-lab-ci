import LeanLab.AlmostPrimeSums.Prime243

/-!
AI wrote this Lean code for CODEX task243. Binary Goldbach is open.
Coarse unconditional Abel errors for BJS pp. 57 to 58 equations 186 to 189.
These adapt the existing derivative calculations in ChenExplicit.Decomp1552a.
The proved Mertens interval bound replaces that file's open Dusart interval input.
https://arxiv.org/abs/2207.09452
-/

namespace LeanLab.AlmostPrimeSums.Abel243
open Finset Real Filter Topology MeasureTheory
open LeanLab.ChenExplicit.D1552 LeanLab.AlmostPrimeSums.Prime243

/-- The decreasing smooth Abel comparison with the proved six over log a
interval error. Derived weaker input for BJS p. 58 equation 189. -/
theorem prime_abel_antitone_bound (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b)
    (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) < b)
    (f f' : ℝ → ℝ) (hf : ∀ t ∈ Set.Icc a b, HasDerivAt f (f' t) t)
    (hfc : ContinuousOn f' (Set.Icc a b))
    (hfb : 0 ≤ f b) (hf' : ∀ t ∈ Set.Icc a b, f' t ≤ 0) :
    ∑ p ∈ s, f p / p ≤ (∫ t in a..b, f t / (t * log t)) + 6 / log a * f a := by
  apply prime_abel_antitone a b (6 / log a) (by linarith) hab s hs f f' hf hfc hfb hf'
  intro x y hax hxy _hyb
  have hx2 : 2 ≤ x := ha.trans hax
  have h := (le_abs_self _).trans (prime_interval_error x y hx2 hxy)
  have hlog : 0 < log a := log_pos (by linarith)
  have hle : 6 / log x ≤ 6 / log a := by
    apply div_le_div_of_nonneg_left (by norm_num) hlog
    exact log_le_log (by linarith) hax
  linarith

/-- The inner Chen logarithmic weight has a fully proved coarse Abel error.
BJS p. 58 equation 188, using the proved Mertens interval estimate. -/
theorem hP_prime_sum_coarse (N p : ℕ) (hN : (0 : ℝ) < N) (hp : (0 : ℝ) < p)
    (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b)
    (hb : 0 < log (N / (p * b))) (s : Finset ℕ)
    (hs : ∀ q ∈ s, q.Prime ∧ a ≤ (q : ℝ) ∧ (q : ℝ) < b) :
    ∑ q ∈ s, 1 / ((q : ℝ) * log (N / (p * q))) ≤
      (∫ t in a..b, 1 / (t * log t * log (N / (p * t)))) +
        6 / log a * hP N p b := by
  have ha0 : 0 < a := by linarith
  have ha1 : 1 < a := by linarith
  have htpos : ∀ t ∈ Set.Icc a b, 0 < t := fun t ht => ha0.trans_le ht.1
  have hlpos : ∀ t ∈ Set.Icc a b, 0 < log (N / (p * t)) := by
    intro t ht
    apply hb.trans_le
    apply log_le_log (div_pos hN (mul_pos hp (ha0.trans_le hab)))
    apply div_le_div_of_nonneg_left hN.le (mul_pos hp (htpos t ht))
    exact mul_le_mul_of_nonneg_left ht.2 hp.le
  let f' : ℝ → ℝ := fun t => 1 / (t * log (N / (p * t)) ^ 2)
  have hf : ∀ t ∈ Set.Icc a b, HasDerivAt (hP N p) (f' t) t := by
    intro t ht
    have ht0 := htpos t ht
    have harg := div_pos hN (mul_pos hp ht0)
    have hd := (((hasDerivAt_const t (N : ℝ)).div
      ((hasDerivAt_id t).const_mul (p : ℝ)) (mul_pos hp ht0).ne').log harg.ne').inv
      (hlpos t ht).ne'
    convert hd using 1
    · funext u
      simp [hP, one_div]
    · dsimp [f']
      field_simp
      <;> ring
  have hfc : ContinuousOn f' (Set.Icc a b) := by
    intro t ht
    have ht0 := htpos t ht
    have hl0 := hlpos t ht
    have hp0 := hp.ne'
    have hpt : (p : ℝ) * t ≠ 0 := (mul_pos hp ht0).ne'
    have harg := (div_pos hN (mul_pos hp ht0)).ne'
    have hd : t * log (N / (p * t)) ^ 2 ≠ 0 := mul_ne_zero ht0.ne' (pow_ne_zero 2 hl0.ne')
    apply ContinuousAt.continuousWithinAt
    dsimp [f']
    fun_prop (disch := assumption)
  have hh := prime_abel_monotone_bound a b ha hab s hs
    (hP N p) f' hf hfc (by dsimp [hP]; exact (one_div_pos.mpr (hlpos a ⟨le_rfl, hab⟩)).le)
    (fun t ht => by have ht0 := htpos t ht; dsimp [f']; positivity)
  convert hh using 1
  · apply sum_congr rfl
    intro q hq
    dsimp [hP]
    ring
  · congr 1
    · apply intervalIntegral.integral_congr
      intro t ht
      dsimp [hP]
      ring

/-- The outer Chen logarithmic weight has a fully proved coarse Abel error.
BJS p. 58 equation 189. No cited reciprocal prime error is assumed. -/
theorem chen_weight_sum_coarse (L a b : ℝ) (hL : 0 < L) (ha : 2 ≤ a)
    (hab : a ≤ b) (hb : log b ≤ L / 3) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime ∧ a ≤ (p : ℝ) ∧ (p : ℝ) < b)
    (f : ℝ → ℝ)
    (hformula : ∀ t ∈ Set.Icc a b,
      f t = log (2 - 3 * (log t / L)) / ((1 - log t / L) * L)) :
    ∑ p ∈ s, f p / p ≤ (∫ t in a..b, f t / (t * log t)) + 6 / log a * f a := by
  have ha0 : 0 < a := by linarith
  have ha1 : 1 < a := by linarith
  have hfacts : ∀ t ∈ Set.Icc a b,
      0 < t ∧ log t / L ∈ Set.Icc (0 : ℝ) (1 / 3) := by
    intro t ht
    have ht0 := ha0.trans_le ht.1
    have htl : 0 < log t := log_pos (ha1.trans_le ht.1)
    have hhi := (log_le_log ht0 ht.2).trans hb
    exact ⟨ht0, (div_pos htl hL).le, (div_le_iff₀ hL).2 (by linarith)⟩
  let F : ℝ → ℝ := fun α => log (2 - 3 * α) / (1 - α)
  let F' : ℝ → ℝ := fun α =>
    ((-3 / (2 - 3 * α)) * (1 - α) + log (2 - 3 * α)) / (1 - α) ^ 2
  have hderiv : ∀ α ∈ Set.Icc (0 : ℝ) (1 / 3), HasDerivAt F (F' α) α := by
    intro α hα
    have hp : 0 < 2 - 3 * α := by have := hα.2; linarith
    have hd : 0 < 1 - α := by have := hα.2; linarith
    have d1 := (((hasDerivAt_id α).const_mul 3).const_sub 2).log hp.ne'
    have d2 := (hasDerivAt_id α).const_sub 1
    convert d1.div d2 hd.ne' using 1
    · rfl
    · dsimp [F']; ring
  have hnonpos : ∀ α ∈ Set.Icc (0 : ℝ) (1 / 3), F' α ≤ 0 := by
    intro α hα
    have hp : 0 < 2 - 3 * α := by have := hα.2; linarith
    have hl := log_le_sub_one_of_pos hp
    have hlg : log (2 - 3 * α) ≤ 1 := by have := hα.1; linarith
    have hr : (-3 / (2 - 3 * α)) * (1 - α) ≤ -1 := by
      rw [div_mul_eq_mul_div]
      apply (div_le_iff₀ hp).2
      linarith
    exact div_nonpos_of_nonpos_of_nonneg (by linarith) (sq_nonneg _)
  let G : ℝ → ℝ := fun t => F (log t / L) / L
  let G' : ℝ → ℝ := fun t => (F' (log t / L) * (t⁻¹ / L)) / L
  have hG : ∀ t ∈ Set.Icc a b, HasDerivAt G (G' t) t := by
    intro t ht
    exact ((hderiv (log t / L) (hfacts t ht).2).comp t
      ((hasDerivAt_log (hfacts t ht).1.ne').div_const L)).div_const L
  have hGc : ContinuousOn G' (Set.Icc a b) := by
    intro t ht
    obtain ⟨ht0, hαlo, hαhi⟩ := hfacts t ht
    have hp : 2 - 3 * (log t / L) ≠ 0 := by linarith
    have hd : 1 - log t / L ≠ 0 := by linarith
    have hd2 : (1 - log t / L) ^ 2 ≠ 0 := pow_ne_zero 2 hd
    have htne := ht0.ne'
    have hF : ContinuousAt F' ((fun u : ℝ => log u / L) t) := by
      dsimp [F']
      fun_prop (disch := assumption)
    have hti : ContinuousAt (fun t : ℝ => t⁻¹) t := by fun_prop (disch := assumption)
    exact (((hF.comp (f := fun u : ℝ => log u / L) ((continuousAt_log htne).div_const L)).mul
      (hti.div_const L)).div_const L).continuousWithinAt
  have heq : ∀ t ∈ Set.Icc a b, G t = f t := by
    intro t ht
    rw [hformula t ht]
    dsimp [G, F]
    rw [div_div]
  have hGb : 0 ≤ G b := by
    obtain ⟨hαlo, hαhi⟩ := (hfacts b ⟨hab, le_rfl⟩).2
    dsimp [G, F]
    apply div_nonneg _ hL.le
    apply div_nonneg _ (by linarith)
    exact log_nonneg (by linarith)
  have hh := prime_abel_antitone_bound a b ha hab s hs G G'
    hG hGc hGb (fun t ht => div_nonpos_of_nonpos_of_nonneg
      (mul_nonpos_of_nonpos_of_nonneg (hnonpos _ (hfacts t ht).2)
        (div_nonneg (inv_nonneg.mpr (hfacts t ht).1.le) hL.le)) hL.le)
  convert hh using 1
  · apply sum_congr rfl
    intro p hp
    rw [heq p ⟨(hs p hp).2.1, (hs p hp).2.2.le⟩]
  · congr 1
    · apply intervalIntegral.integral_congr
      intro t ht
      rw [Set.uIcc_of_le hab] at ht
      dsimp only
      rw [heq t ht]
    · rw [heq a ⟨le_rfl, hab⟩]

end LeanLab.AlmostPrimeSums.Abel243
