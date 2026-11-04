/-
Uniform partial sums for the actual smoothed minor arc family.
Source: P0029 page 27, the smoothed Vinogradov Vaughan step in the proof of 7.8.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.Smoothing261

namespace LeanLab.BhowmikGrimmelt2026

open ArithmeticFunction MeasureTheory
open scoped NNReal

/-- A minor arc at length X controls every shorter unsmoothed partial sum. -/
theorem minor_partial_sum261 {X : ℕ} {R α : ℝ} (hX : 2 ≤ X) (hR : 1 ≤ R)
    (hRX : R ≤ X) (hminor : ¬ MajorArc X R α) {m : ℕ} (hm : m ≤ X) :
    ‖Ssum m α‖ ≤ 48600 * ((X : ℝ) / Real.sqrt R +
      (X : ℝ) ^ (4 / 5 : ℝ)) * Real.log X ^ 4 := by
  have hX0 : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hR0 : 0 < R := by linarith
  have hlogX : 0 ≤ Real.log (X : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ X))
  by_cases hm2 : 2 ≤ m
  · have hm0 : (0 : ℝ) < m := by exact_mod_cast (by omega : 0 < m)
    have hmX : (m : ℝ) ≤ X := by exact_mod_cast hm
    obtain ⟨a, q, hq, hcop, hRq, hqR, happ⟩ := minor_dirichlet84 hX0 hR0 hRX hminor
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
    have hsR : 0 < Real.sqrt R := Real.sqrt_pos.mpr hR0
    have hsR2 : Real.sqrt R ^ 2 = R := Real.sq_sqrt hR0.le
    have hfirst : (m : ℝ) / Real.sqrt q ≤ (X : ℝ) / Real.sqrt R :=
      (div_le_div_of_nonneg_right hmX (Real.sqrt_nonneg _)).trans
        (div_le_div_of_nonneg_left hX0.le hsR (Real.sqrt_le_sqrt hRq.le))
    have hlast : Real.sqrt ((m : ℝ) * q) ≤ (X : ℝ) / Real.sqrt R := by
      have hprod : (m : ℝ) * q ≤ ((X : ℝ) / Real.sqrt R) ^ 2 := by
        have hqr : (q : ℝ) * R ≤ X := (le_div_iff₀ hR0).mp hqR
        rw [div_pow, hsR2, le_div_iff₀ hR0]
        nlinarith [mul_le_mul_of_nonneg_left hqr hX0.le,
          mul_le_mul_of_nonneg_right hmX (mul_nonneg hq0.le hR0.le)]
      exact (Real.sqrt_le_sqrt hprod).trans_eq (Real.sqrt_sq (by positivity))
    have hexplicit : ‖Ssum m α‖ ≤ 24300 * ((m : ℝ) / Real.sqrt q +
        (m : ℝ) ^ (4 / 5 : ℝ) + Real.sqrt ((m : ℝ) * q)) * Real.log m ^ 4 := by
      rcases le_total q m with hqm | hmq
      · exact vaughan_small_denominator84 hm2 hq hcop happ hqm
      · exact vaughan_large_denominator84 hm2 hmq α
    have hpow : (m : ℝ) ^ (4 / 5 : ℝ) ≤ (X : ℝ) ^ (4 / 5 : ℝ) :=
      Real.rpow_le_rpow hm0.le hmX (by norm_num)
    have hlog : Real.log (m : ℝ) ^ 4 ≤ Real.log X ^ 4 :=
      pow_le_pow_left₀ (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ m)))
        (Real.log_le_log hm0 hmX) 4
    calc
      _ ≤ 24300 * ((m : ℝ) / Real.sqrt q + (m : ℝ) ^ (4 / 5 : ℝ) +
          Real.sqrt ((m : ℝ) * q)) * Real.log m ^ 4 := hexplicit
      _ ≤ 24300 * (2 * ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ))) *
          Real.log X ^ 4 := by
        apply mul_le_mul _ hlog (by positivity) (by positivity)
        have hXp : 0 ≤ (X : ℝ) ^ (4 / 5 : ℝ) := by positivity
        nlinarith
      _ = _ := by ring
  · have hm01 : m = 0 ∨ m = 1 := by omega
    rcases hm01 with rfl | rfl <;> norm_num [Ssum] <;> positivity

/-- The unsmoothed sum includes its zero coefficient without changing its value. -/
theorem Ssum_range261 (N : ℕ) (α : ℝ) :
    (∑ n ∈ Finset.range (N + 1), (vonMangoldt n : ℂ) * ee (α * n)) = Ssum N α := by
  rw [Nat.range_succ_eq_Icc_zero]
  symm
  apply Finset.sum_subset (Finset.Icc_subset_Icc (by omega) le_rfl)
  intro n hn hn'
  have hz : n = 0 := by simp only [Finset.mem_Icc] at hn hn'; omega
  simp [hz]

/-- Summation by parts transfers uniform partial sum control to the actual cutoff sum. -/
theorem Sphi_of_partial_bound261 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ)
    {L : ℝ≥0} (hL : LipschitzWith L ϕ) {N : ℕ} {α B : ℝ}
    (hB : 0 ≤ B) (hpartial : ∀ m ≤ N, ‖Ssum m α‖ ≤ B) :
    ‖Sphi ϕ N α‖ ≤ (L : ℝ) * B := by
  by_cases hN : N = 0
  · subst N
    simp [Sphi]
    positivity
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (Nat.pos_of_ne_zero hN)
  have hphi1 : ϕ ((N : ℝ) / N) = 0 := by
    rw [div_self hNpos.ne']
    exact phi_zero_ge_one261 hϕ le_rfl
  have hparts := Finset.sum_range_by_parts (fun n : ℕ => ϕ ((n : ℝ) / N))
    (fun n : ℕ => (vonMangoldt n : ℂ) * ee (α * n)) (N + 1)
  have hrepr : Sphi ϕ N α =
      -(∑ n ∈ Finset.range N, (ϕ (((n + 1 : ℕ) : ℝ) / N) - ϕ ((n : ℝ) / N)) •
        Ssum n α) := by
    have hleft : (∑ n ∈ Finset.range (N + 1), ϕ ((n : ℝ) / N) •
        ((vonMangoldt n : ℂ) * ee (α * n))) = Sphi ϕ N α := by
      unfold Sphi
      apply Finset.sum_congr rfl
      intro n hn
      change (ϕ ((n : ℝ) / N) : ℂ) * ((vonMangoldt n : ℂ) * ee (α * n)) = _
      push_cast
      ring
    rw [hleft] at hparts
    simpa only [Nat.add_sub_cancel, hphi1, zero_smul, zero_sub, Ssum_range261] using hparts
  have hstep (n : ℕ) :
      |ϕ (((n + 1 : ℕ) : ℝ) / N) - ϕ ((n : ℝ) / N)| ≤ (L : ℝ) / N := by
    have h := hL.norm_sub_le (((n + 1 : ℕ) : ℝ) / N) ((n : ℝ) / N)
    simp only [Real.norm_eq_abs] at h
    have heq : ((n + 1 : ℕ) : ℝ) / N - (n : ℝ) / N = 1 / N := by push_cast; ring
    rw [heq, abs_of_pos (one_div_pos.mpr hNpos)] at h
    simpa only [div_eq_mul_inv, one_mul] using h
  rw [hrepr, norm_neg]
  calc
    _ ≤ ∑ n ∈ Finset.range N,
        ‖(ϕ (((n + 1 : ℕ) : ℝ) / N) - ϕ ((n : ℝ) / N)) • Ssum n α‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range N, ((L : ℝ) / N) * B := by
      apply Finset.sum_le_sum
      intro n hn
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hstep n) (hpartial n (by simp only [Finset.mem_range] at hn; omega))
        (norm_nonneg _) (by positivity)
    _ = (L : ℝ) * B := by simp; field_simp

/-- The actual smoothing has the uniform minor arc pointwise estimate used on page 27. -/
theorem Sphi_minor261 {ϕ : ℝ → ℝ} (hϕ : IsPhi ϕ) {L : ℝ≥0} (hL : LipschitzWith L ϕ)
    {X N : ℕ} {R α : ℝ} (hX : 2 ≤ X) (hR : 1 ≤ R) (hRX : R ≤ X)
    (hNX : N ≤ X) (hminor : ¬ MajorArc X R α) :
    ‖Sphi ϕ N α‖ ≤ (L : ℝ) *
      (48600 * ((X : ℝ) / Real.sqrt R + (X : ℝ) ^ (4 / 5 : ℝ)) * Real.log X ^ 4) := by
  apply Sphi_of_partial_bound261 hϕ hL (by positivity)
  intro m hm
  exact minor_partial_sum261 hX hR hRX hminor (hm.trans hNX)

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.minor_partial_sum261
#print axioms LeanLab.BhowmikGrimmelt2026.Ssum_range261
#print axioms LeanLab.BhowmikGrimmelt2026.Sphi_of_partial_bound261
#print axioms LeanLab.BhowmikGrimmelt2026.Sphi_minor261
