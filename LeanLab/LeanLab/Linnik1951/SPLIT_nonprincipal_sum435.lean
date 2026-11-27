/-
Unit S6-29, burst-20261124. Assembly of nonprincipal_sum435 of
SPLIT_doubled_system_expansion435 from the general radius Mellin estimate
mellin_radius1622 of SPLIT1622_mellin, P0093 page 159 equation 5.2 at radius one
over R. Radius two over R is radius one over R over two when R is at least two.
For R below two, periodicity puts the interval inside two full periods of radius one.
The nonprincipal characters number at most the totient of q.
No new leaf. CONDITIONAL on the leaves of SPLIT1622_mellin and GRH.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_doubled_system_expansion435
import LeanLab.Linnik1951.SPLIT1622_mellin
import LeanLab.Linnik1951.Principal442

namespace LeanLab.Linnik1951

open MeasureTheory

/-- Radius two is at most twice radius one for any period one nonnegative
continuous function: the interval from minus two to two is two copies of the
interval from minus one to one. -/
theorem radius_two_le_S629 (f : ℝ → ℝ) (hf : Continuous f) (hper : Function.Periodic f 1) :
    (∫ z in (-2 : ℝ)..2, f z) = 2 * ∫ z in (-1 : ℝ)..1, f z := by
  have hper2 : Function.Periodic f 2 := by
    have h := hper.nat_mul 2
    simpa using h
  have h1 : (∫ z in (-2 : ℝ)..0, f z) = ∫ z in (-1 : ℝ)..1, f z := by
    have h := hper2.intervalIntegral_add_eq (-2) (-1)
    rw [show (-2 : ℝ) + 2 = 0 by norm_num, show (-1 : ℝ) + 2 = 1 by norm_num] at h
    exact h
  have h2 : (∫ z in (0 : ℝ)..2, f z) = ∫ z in (-1 : ℝ)..1, f z := by
    have h := hper2.intervalIntegral_add_eq 0 (-1)
    rw [show (0 : ℝ) + 2 = 2 by norm_num, show (-1 : ℝ) + 2 = 1 by norm_num] at h
    exact h
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := 0)
    (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _), h1, h2]
  ring

/-- P0093 page 159 equation 5.2 for one nonprincipal character at radius two over R,
R between one and N to the two sevenths. CONDITIONAL on mellin_radius1622. -/
theorem nonprincipal_single_S629 (hG : LeanLab.DERZ1997.GRH) :
    ∃ X : ℝ, 0 < X ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ (q : ℕ), 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) → ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
        ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
          (∫ z in -(2 / R)..(2 / R), ‖characterPrime280 χ N z‖ ^ 2) ≤
            X * ((N : ℝ) / R * Real.log N ^ 13) := by
  obtain ⟨B, hB, N0, hmel⟩ := mellin_radius1622 hG
  refine ⟨4 * B, by positivity, N0, ?_⟩
  intro N hN q hq hqt χ hχ R hR1 hR
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : 0 ≤ Real.log N ^ 13 := pow_nonneg (Real.log_nonneg hNr) 13
  have hRpos : 0 < R := by linarith
  have hNR : 0 ≤ (N : ℝ) / R * Real.log N ^ 13 := by positivity
  have hRne : R ≠ 0 := hRpos.ne'
  rcases le_or_gt 2 R with h2 | h2
  · have hR' : 1 ≤ R / 2 := by linarith
    have hR'' : R / 2 ≤ (N : ℝ) ^ (2 / 7 : ℝ) := by linarith
    have h := hmel N hN q hq hqt χ hχ (R / 2) hR' hR''
    rw [show 1 / (R / 2) = 2 / R by field_simp] at h
    refine h.trans ?_
    have he : B * (N : ℝ) / (R / 2) * Real.log N ^ 13 =
        2 * B * ((N : ℝ) / R * Real.log N ^ 13) := by
      field_simp
    rw [he]
    nlinarith
  · have hc : Continuous fun z : ℝ => ‖characterPrime280 χ N z‖ ^ 2 :=
      (continuous_character_prime357 χ N hN1).norm.pow 2
    have hper : Function.Periodic (fun z : ℝ => ‖characterPrime280 χ N z‖ ^ 2) 1 :=
      (character_periodic442 χ N).comp (fun z => ‖z‖ ^ 2)
    have h2R : 2 / R ≤ 2 := by
      rw [div_le_iff₀ hRpos]; linarith
    have h2R0 : 0 ≤ 2 / R := by positivity
    have hi := intervalIntegral.integral_mono_interval (μ := MeasureTheory.volume)
      (show (-2 : ℝ) ≤ -(2 / R) by linarith) (show -(2 / R) ≤ 2 / R by linarith) h2R
      (Filter.Eventually.of_forall (fun z => sq_nonneg ‖characterPrime280 χ N z‖))
      (hc.intervalIntegrable (-2 : ℝ) 2)
    have h1 : (1 : ℝ) ≤ (N : ℝ) ^ (2 / 7 : ℝ) := Real.one_le_rpow hNr (by norm_num)
    have hm := hmel N hN q hq hqt χ hχ 1 le_rfl h1
    rw [show (1 : ℝ) / 1 = 1 by norm_num, div_one] at hm
    have hi2 := hi.trans_eq (radius_two_le_S629 _ hc hper)
    beta_reduce at hi2
    have hNR2 : (N : ℝ) / 2 ≤ (N : ℝ) / R := div_le_div_of_nonneg_left hNpos.le hRpos h2.le
    have hkey : 2 * (B * (N : ℝ) * Real.log N ^ 13) ≤
        4 * B * ((N : ℝ) / R * Real.log N ^ 13) := by
      have : (N : ℝ) * Real.log N ^ 13 ≤ 2 * ((N : ℝ) / R * Real.log N ^ 13) := by
        nlinarith
      nlinarith
    linarith

/-- Assembly of nonprincipal_sum435, exactly its statement. P0093 page 159
equation 5.2 summed over the nonprincipal characters, at most the totient of q
of them. CONDITIONAL on mellin_radius1622 and GRH. No new leaf. -/
theorem nonprincipal_sum435_assembly_S629 (hG : LeanLab.DERZ1997.GRH) :
    ∃ X : ℝ, 0 < X ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ (q : ℕ) [NeZero q], 2 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) → ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ∫ z in -(2 / R)..(2 / R), ‖characterPrime280 χ N z‖ ^ 2) ≤
          X * (q.totient : ℝ) * ((N : ℝ) / R * Real.log N ^ 13) := by
  classical
  obtain ⟨X, hX, N0, hone⟩ := nonprincipal_single_S629 hG
  refine ⟨X, hX, N0, ?_⟩
  intro N hN q _ hq2 hqt R hR1 hR
  have hN1 : 1 ≤ N := by omega
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN1
  have hlog : 0 ≤ Real.log N ^ 13 := pow_nonneg (Real.log_nonneg hNr) 13
  have hRpos : 0 < R := by linarith
  have hNR : 0 ≤ X * ((N : ℝ) / R * Real.log N ^ 13) := by positivity
  have hcard : ((Finset.univ.filter
      (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℝ) ≤ q.totient := by
    have h1 := Finset.card_filter_le (Finset.univ : Finset (DirichletCharacter ℂ q))
      (fun χ => χ ≠ 1)
    have h2 : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
      rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
      exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
    exact_mod_cast h2 ▸ h1
  calc _ ≤ ∑ _χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
        X * ((N : ℝ) / R * Real.log N ^ 13) := by
        refine Finset.sum_le_sum fun χ hχ => ?_
        exact hone N hN q (by omega) hqt χ (Finset.mem_filter.mp hχ).2 R hR1 hR
    _ = ((Finset.univ.filter
          (fun χ : DirichletCharacter ℂ q => χ ≠ 1)).card : ℝ) *
          (X * ((N : ℝ) / R * Real.log N ^ 13)) := by simp
    _ ≤ (q.totient : ℝ) * (X * ((N : ℝ) / R * Real.log N ^ 13)) :=
        mul_le_mul_of_nonneg_right hcard hNR
    _ = X * (q.totient : ℝ) * ((N : ℝ) / R * Real.log N ^ 13) := by ring

end LeanLab.Linnik1951
