/-- Minimal test file to verify buchstab_pos_above_one logic. -/
import LeanLab.ChenDoubleSieve.FunctionalStatements
import LeanLab.ChenDoubleSieve.BuchstabBounds

namespace LeanLab.ChenDoubleSieve.Wu04Buchstab

theorem buchstab_pos_above_one_test {ω : ℝ → ℝ} (hω : IsBuchstab ω) {u : ℝ} (hu : 1 < u) :
    0 < ω u := by
  have hnonneg : ∀ v : ℝ, 1 ≤ v → 0 ≤ ω v := by
    intro v hv
    exact buchstab_nonneg hω hv
  have hpos_interval : ∀ v : ℝ, 1 ≤ v → v ≤ 2 → 0 < ω v := by
    intro v hv1 hv2
    have hωv : ω v = 1 / v := hω.2.1 v hv1 (by linarith)
    rw [hωv]
    have hv0 : 0 < v := by linarith [hv1]
    positivity
  by_cases hle2 : u ≤ 2
  · have hωu : ω u = 1 / u := hω.2.1 u (by linarith [hu, hle2]) (by linarith)
    rw [hωu]
    have hu0 : 0 < u := by linarith [hu]
    positivity
  · have hu2 : 2 < u := by linarith [hle2]
    have hcont : ContinuousOn (fun t : ℝ => t * ω t) (Icc 2 u) :=
      continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
    have hder : ∀ t ∈ Ioo (2 : ℝ) u,
        HasDerivAt (fun v => v * ω v) (ω (t - 1)) t := by
      intro t ht
      have h₁ := hω.2.1 (t - 1) (by linarith [ht.1]) (by linarith [ht.2, hu2])
      simpa only [h₁, one_div] using hω.2.2 t ht.1
    have hci : ContinuousOn (fun t : ℝ => ω (t - 1)) (uIcc 2 u) := by
      rw [uIcc_of_le hu2]
      apply hω.1.comp (by fun_prop)
      intro t ht
      change 1 ≤ t - 1
      linarith [ht.1]
    have hFTC := integral_eq_sub_of_hasDerivAt_of_le (by norm_num) hcont hder hci.intervalIntegrable
    have hI : (∫ t in (2 : ℝ)..u, ω (t - 1)) ≥ 0 := by
      apply intervalIntegral.integral_nonneg (by norm_num)
      intro t ht
      have ht' : 2 ≤ t := by linarith [ht.1]
      have ht'' : t ≤ u := by linarith [ht.2]
      have ht''' : 1 ≤ t - 1 := by linarith
      exact hnonneg (t - 1) ht'''
    have h2w2 : 0 < 2 * ω 2 := by
      have hω2 : ω 2 = 1 / 2 := hω.2.1 2 (by norm_num) (by norm_num)
      rw [hω2]
      norm_num
    have hwu : u * ω u = 2 * ω 2 + ∫ t in (2 : ℝ)..u, ω (t - 1) := by
      have h₁ := hFTC
      have h₂ : (∫ t in (2 : ℝ)..u, ω (t - 1)) = (u * ω u - 2 * ω 2) := by
        linarith
      linarith
    have hwu_pos : 0 < u * ω u := by
      have h₁ : 0 ≤ ∫ t in (2 : ℝ)..u, ω (t - 1) := hI
      have h₂ : 0 < 2 * ω 2 := h2w2
      rw [hwu]
      linarith
    have hu0 : 0 < u := by linarith [hu]
    have hωu_pos : 0 < ω u := by
      by_contra h
      have hωu_nonpos : ω u ≤ 0 := by linarith
      have h₁ : u * ω u ≤ 0 := by
        nlinarith
      linarith
    exact hωu_pos
