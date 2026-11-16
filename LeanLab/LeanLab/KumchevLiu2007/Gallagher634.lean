/-
Gallagher's lemma for the strict square windows of P0088 page 8.
The real frequency smoothing theorem is reused from Gallagher605.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Kernel634Base
import LeanLab.BHP1997.Gallagher605

namespace LeanLab.KumchevLiu2007.Task634

open Real Complex MeasureTheory Task556a Task556d
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 8 after display 31: closed and strict frequency windows agree
outside their finitely many upper endpoints. -/
theorem frequencyWindow_ae_strict (s : Finset ℕ) (c : ℕ → ℂ)
    (f : ℕ → ℝ) (H : ℝ) :
    LeanLab.BHP1997.Gallagher605.frequencyWindow s c f H =ᵐ[volume]
      fun t => ∑ m ∈ s.filter (fun m => t < f m ∧ f m ≤ t + H), c m := by
  have hn : ∀ᵐ t : ℝ, ∀ m : ℕ, t ≠ f m :=
    ae_all_iff.mpr fun m => volume.ae_ne (f m)
  filter_upwards [hn] with t ht
  unfold LeanLab.BHP1997.Gallagher605.frequencyWindow
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m hm
  have he : t ∈ Set.Icc (f m - H) (f m) ↔ t < f m ∧ f m ≤ t + H := by
    simp only [Set.mem_Icc]
    constructor
    · intro h
      exact ⟨lt_of_le_of_ne h.2 (ht m), by linarith [h.1]⟩
    · intro h
      exact ⟨by linarith [h.2], h.1.le⟩
  by_cases h : t < f m ∧ f m ≤ t + H
  · simp [he.mpr h, h]
  · rw [Set.indicator_of_notMem (fun hmem => h (he.mp hmem)), ite_eq_right h]

/-- P0088 page 8 after display 31: a finite frequency window is supported
between the least frequency minus H and the greatest frequency. -/
theorem frequencyWindow_energy_interval (s : Finset ℕ) (c : ℕ → ℂ)
    (f : ℕ → ℝ) (H lo hi : ℝ) (hH : 0 ≤ H) (hlh : lo ≤ hi)
    (hf : ∀ m ∈ s, lo ≤ f m ∧ f m ≤ hi) :
    (∫ t : ℝ, ‖LeanLab.BHP1997.Gallagher605.frequencyWindow s c f H t‖ ^ 2) =
      ∫ t in (lo - H)..hi,
        ‖∑ m ∈ s.filter (fun m => t < f m ∧ f m ≤ t + H), c m‖ ^ 2 := by
  have hz : ∀ t, t ∉ Set.Icc (lo - H) hi →
      LeanLab.BHP1997.Gallagher605.frequencyWindow s c f H t = 0 := by
    intro t ht
    unfold LeanLab.BHP1997.Gallagher605.frequencyWindow
    apply Finset.sum_eq_zero
    intro m hm
    apply Set.indicator_of_notMem
    intro hmem
    apply ht
    obtain ⟨hl, hu⟩ := hf m hm
    exact ⟨by linarith [hmem.1], hmem.2.trans hu⟩
  rw [← setIntegral_eq_integral_of_forall_compl_eq_zero
    (s := Set.Icc (lo - H) hi) (fun t ht => by rw [hz t ht]; simp),
    integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
  apply intervalIntegral.integral_congr_ae
  filter_upwards [frequencyWindow_ae_strict s c f H] with t ht
  intro _
  rw [ht]

/-- P0088 page 8 after display 31: Gallagher's real frequency lemma for the
rough quadratic sum, with its full initial interval included. -/
theorem roughSum_gallagher (Y P H α : ℝ) (hH : 0 < H) :
    (∫ β in (-(1 / (2 * H)))..(1 / (2 * H)), ‖roughSum Y P (α + β)‖ ^ 2) ≤
      (π / (2 * H)) ^ 2 *
        ((∫ t in (Y / 4 - H)..(Y / 4), ‖roughShortSum Y P H α t‖ ^ 2) +
          ∫ t in (Y / 4)..Y, ‖roughShortSum Y P H α t‖ ^ 2) := by
  by_cases hY : 0 ≤ Y
  · let c : ℕ → ℂ := fun m =>
      roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))
    let f : ℕ → ℝ := fun m => (m : ℝ) ^ 2
    have he (β : ℝ) : roughSum Y P (α + β) =
        ∑ m ∈ squareWindow Y, c m * LeanLab.PNTPort.LargeSieve.e (f m * β) := by
      unfold roughSum
      apply Finset.sum_congr rfl
      intro m hm
      dsimp only [c, f]
      rw [fourier_nat_eq_e (m ^ 2) (α + β), fourier_nat_eq_e (m ^ 2) α]
      simp only [Nat.cast_pow, mul_add, LeanLab.PNTPort.LargeSieve.e_add]
      ring
    have hs := LeanLab.BHP1997.Gallagher605.gallagher_window_smoothing
      (squareWindow Y) c f hH (T := 1 / (2 * H)) (by positivity)
      (by field_simp; linarith)
    have hf : ∀ m ∈ squareWindow Y, Y / 4 ≤ f m ∧ f m ≤ Y := by
      intro m hm
      simp only [squareWindow, Finset.mem_filter] at hm
      have hsq := Real.sq_sqrt hY
      have hroot := Real.sqrt_nonneg Y
      dsimp [f]
      constructor <;> nlinarith [hm.2.1, hm.2.2, sq_nonneg (m : ℝ)]
    have hi := LeanLab.BHP1997.Gallagher605.integrable_frequencyWindow_energy
      (squareWindow Y) c f H
    have hae := frequencyWindow_ae_strict (squareWindow Y) c f H
    have hi' : Integrable (fun t => ‖roughShortSum Y P H α t‖ ^ 2) := by
      apply hi.congr
      filter_upwards [hae] with t ht
      exact congrArg (fun z : ℂ => ‖z‖ ^ 2) ht
    have henergy := frequencyWindow_energy_interval (squareWindow Y) c f H
      (Y / 4) Y hH.le (by linarith) hf
    change (∫ t : ℝ,
      ‖LeanLab.BHP1997.Gallagher605.frequencyWindow (squareWindow Y) c f H t‖ ^ 2) =
        ∫ t in (Y / 4 - H)..Y, ‖roughShortSum Y P H α t‖ ^ 2 at henergy
    simp_rw [← he] at hs
    rw [henergy, ← intervalIntegral.integral_add_adjacent_intervals
      hi'.intervalIntegrable hi'.intervalIntegrable] at hs
    convert hs using 1; ring
  · have hempty : squareWindow Y = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro m hm
      simp only [squareWindow, Finset.mem_filter] at hm
      rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hY)] at hm
      exact (not_lt_of_ge (Nat.cast_nonneg m)) hm.2.2
    simp [roughSum, roughShortSum, hempty]

end LeanLab.KumchevLiu2007.Task634

#print axioms LeanLab.KumchevLiu2007.Task634.frequencyWindow_ae_strict
#print axioms LeanLab.KumchevLiu2007.Task634.frequencyWindow_energy_interval
#print axioms LeanLab.KumchevLiu2007.Task634.roughSum_gallagher
