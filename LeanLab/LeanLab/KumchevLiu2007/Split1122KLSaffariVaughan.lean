/-
BURST 2026-11-22 S111, step saffari-vaughan. SPLIT of the LEAF
Prep1122KLGallagherCut.saffari_vaughan_device. Kumchev and Liu 2007, P0088,
arXiv 0801.0130, page 6, the display before display 20, the device of Saffari and
Vaughan, reference 21 page 25.

With Y = windowY X eps, P = (log X)^B, R = q Q = q H / P, L = floor(R/2), N = floor(Y) + 1
and a the coefficient of W2 at n = m^2, the argument is:
* PROVED, Prep1122KLGallagherCut.win_sum_eq_integral: the Gallagher window mean square
  over integer k is the integral over -L < x < N of |A(x)|^2, A(x) the sum of a n over
  x < n <= x + L.
* LEAF edge_window_bound, MEDIUM: on -L < x < Y/4 the window meets at most L/sqrt Y + 1
  squares m^2 with m at least sqrt Y / 2, the coefficients are bounded, so
  (pi/(2L))^2 times this part is at most a constant times R/Y.
* LEAF saffari_vaughan_average, HARD, the device proper: on Y/4 < x < N the fixed
  window of length L is cut into a bounded number of relative windows t < n <= t + delta t,
  averaged over delta in a range of size R/Y, and one delta in c R/Y to R/Y with
  integral at least the average is chosen.
* PROVED here, saffari_vaughan_device_of_pieces: the split integral, the two leaves and
  (pi/(2L))^2 at most 4 pi^2 R^(-2) give the exact statement of the parent leaf, checked
  by type_of%.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1122KLGallagherCut

namespace LeanLab.KumchevLiu2007.Split1122KLSaffariVaughan

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Prep1121KLMajor
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 6, the display before display 20, the edge of the device of Saffari
and Vaughan, reference 21 page 25: the windows x < n <= x + L with -L < x < Y/4 meet
only the squares m^2 just above Y/4, at most L/sqrt Y + 1 of them, with bounded
coefficients of W2 from display 10 and the bounded f2 of page 15, so the edge part of
the Gallagher mean square is at most a constant times R/Y, R = qQ = q H/P.
Class MEDIUM. -/
theorem edge_window_bound :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C X0 : ℝ, 0 < C ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
        ∀ χ : DirichletCharacter ℂ q,
        ∀ (Y R : ℝ) (L : ℕ) (a : ℕ → ℂ), Y = windowY X ε →
          R = (q : ℝ) * (H / Real.log X ^ B) → L = ⌊R / 2⌋₊ →
          a = (fun n => ∑ m ∈ squareWindow Y, if m ^ 2 = n then
                (roughWeight (Y ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) m * χ m -
                  (if χ = 1 then ((Task556a.f2Weight
                    (Y ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
                   else 0)) else 0) →
          (π / (2 * (L : ℝ))) ^ 2 *
            (∫ x in (-(L : ℝ))..(Y / 4),
              ‖∑ n ∈ (Finset.range (⌊Y⌋₊ + 1)).filter
                  (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x + L), a n‖ ^ 2) ≤ C * (R / Y) := by
  sorry

/-- LEAF: P0088 page 6, the display before display 20, the device of Saffari and
Vaughan, reference 21 page 25, proper: for Y/4 < x < N the fixed window x < n <= x + L
is cut into a bounded number of relative windows t < n <= t + delta t with t in Y/4 to
Y; averaging over delta in a range of size R/Y and changing variables t = x, t = x + L
bounds the integral of the squared fixed window sums by a constant times the integral
of the squared sums of (A2.2) for one delta in c R/Y to R/Y, plus R^2 delta.
Class HARD, a citation wall: the device is not printed in P0088. -/
theorem saffari_vaughan_average :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C c X0 : ℝ, 0 < C ∧ 0 < c ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
        ∀ χ : DirichletCharacter ℂ q,
        ∀ (Y R : ℝ) (L : ℕ) (a : ℕ → ℂ), Y = windowY X ε →
          R = (q : ℝ) * (H / Real.log X ^ B) → L = ⌊R / 2⌋₊ →
          a = (fun n => ∑ m ∈ squareWindow Y, if m ^ 2 = n then
                (roughWeight (Y ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) m * χ m -
                  (if χ = 1 then ((Task556a.f2Weight
                    (Y ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
                   else 0)) else 0) →
          ∃ δ : ℝ, c * R / Y ≤ δ ∧ δ ≤ R / Y ∧
            (∫ x in (Y / 4)..((⌊Y⌋₊ + 1 : ℕ) : ℝ),
              ‖∑ n ∈ (Finset.range (⌊Y⌋₊ + 1)).filter
                  (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x + L), a n‖ ^ 2) ≤
              C * ((∫ t in Y / 4..Y, ‖roughDefect χ Y (Real.log X ^ B) δ t‖ ^ 2) +
                R ^ 2 * δ) := by
  sorry

/-- PROVED. The squared fixed window sum is interval integrable on -L to N, by the
Gallagher pieces of Prep1122KLGallagherCut.window_eq_win. -/
theorem window_sq_intervalIntegrable (a : ℕ → ℂ) (N L : ℕ) :
    IntervalIntegrable (fun x : ℝ =>
        ‖∑ n ∈ (Finset.range N).filter (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x + L), a n‖ ^ 2)
      volume (-(L : ℝ)) (N : ℝ) := by
  set f : ℝ → ℝ := fun x =>
    ‖∑ n ∈ (Finset.range N).filter (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x + L), a n‖ ^ 2 with hf
  have hpiece : ∀ k : ℕ, Set.EqOn f
      (fun _ => ‖LeanLab.PNTPort.Gallagher.win a N L k‖ ^ 2)
      (Set.uIoo ((k : ℝ) - L) (((k + 1 : ℕ) : ℝ) - L)) := by
    intro k x hx
    rw [Set.uIoo_of_le (by push_cast; linarith)] at hx
    have hx' : x ∈ Set.Ioo ((k : ℝ) - L) ((k : ℝ) - L + 1) := by
      push_cast at hx; constructor <;> linarith [hx.1, hx.2]
    simp only [hf, Prep1122KLGallagherCut.window_eq_win a N L k hx']
  have hint : ∀ k < N + L, IntervalIntegrable f volume ((k : ℝ) - L) (((k + 1 : ℕ) : ℝ) - L) :=
    fun k _ => (intervalIntegrable_const).congr_uIoo (fun x hx => (hpiece k hx).symm)
  have h := IntervalIntegrable.trans_iterate (a := fun k : ℕ => (k : ℝ) - L) hint
  simp only [Nat.cast_zero, zero_sub] at h
  have hN : ((N + L : ℕ) : ℝ) - L = N := by push_cast; ring
  rw [hN] at h
  exact h


/-- PROVED from the LEAFs edge_window_bound and saffari_vaughan_average, with the exact
type of the LEAF Prep1122KLGallagherCut.saffari_vaughan_device. P0088 page 6, the
display before display 20: the Gallagher mean square is the integral of the squared
fixed window sums, split at Y/4; the edge is at most C R/Y, at most C/c times delta,
and (pi/(2L))^2 is at most 4 pi^2 R^(-2) since L is at least R/4. -/
theorem saffari_vaughan_device_of_pieces :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C c X0 : ℝ, 0 < C ∧ 0 < c ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
        ∀ χ : DirichletCharacter ℂ q,
          ∃ δ : ℝ, c * ((q : ℝ) * (H / Real.log X ^ B)) / windowY X ε ≤ δ ∧
            δ ≤ (q : ℝ) * (H / Real.log X ^ B) / windowY X ε ∧
            (π / (2 * (⌊(q : ℝ) * (H / Real.log X ^ B) / 2⌋₊ : ℝ))) ^ 2 *
              ∑ k ∈ Finset.range (⌊windowY X ε⌋₊ + 1 + ⌊(q : ℝ) * (H / Real.log X ^ B) / 2⌋₊),
                ‖LeanLab.PNTPort.Gallagher.win
                  (fun n => ∑ m ∈ squareWindow (windowY X ε), if m ^ 2 = n then
                    (roughWeight (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) m * χ m -
                      (if χ = 1 then ((Task556a.f2Weight
                        (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
                       else 0)) else 0)
                  (⌊windowY X ε⌋₊ + 1) ⌊(q : ℝ) * (H / Real.log X ^ B) / 2⌋₊ k‖ ^ 2 ≤
              C * (((q : ℝ) * (H / Real.log X ^ B)) ^ (-2 : ℤ) *
                (∫ t in windowY X ε / 4..windowY X ε,
                  ‖roughDefect χ (windowY X ε) (Real.log X ^ B) δ t‖ ^ 2) + δ) := by
  intro B hB ε hε hε'
  obtain ⟨C1, X1, hC1, kE⟩ := edge_window_bound B hB ε hε hε'
  obtain ⟨C2, c, X2, hC2, hc, kM⟩ := saffari_vaughan_average B hB ε hε hε'
  obtain ⟨X3, hX3⟩ := Filter.eventually_atTop.mp (Prep1122KLGallagherCut.eventually_big B)
  refine ⟨4 * π ^ 2 * C2 + C1 / c, c, max (max X1 X2) X3, by positivity, hc, ?_⟩
  intro X H hX hlo hhi q hq hqP χ
  have hX1 : X1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX2 : X2 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  obtain ⟨hXa, hL1, hbig⟩ := hX3 X (le_trans (le_max_right _ _) hX)
  set Y := windowY X ε with hY
  set P := Real.log X ^ B with hPdef
  set R := (q : ℝ) * (H / P) with hR
  set L := ⌊R / 2⌋₊ with hLdef
  set a : ℕ → ℂ := (fun n => ∑ m ∈ squareWindow Y, if m ^ 2 = n then
                (roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m * χ m -
                  (if χ = 1 then ((Task556a.f2Weight
                    (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
                   else 0)) else 0) with ha
  have hE := kE X H hX1 hlo hhi q hq hqP χ Y R L a rfl rfl rfl rfl
  obtain ⟨δ, h1, h2, hM⟩ := kM X H hX2 hlo hhi q hq hqP χ Y R L a rfl rfl rfl rfl
  refine ⟨δ, h1, h2, ?_⟩
  -- size facts, as in Prep1122KLGallagherCut.gallagher_saffari_vaughan
  have hP1 : 1 ≤ P := Real.one_le_rpow hL1 hB.le
  have hP0 : 0 < P := by linarith
  have hP4 : P ^ (-4 : ℤ) = (P ^ 4)⁻¹ := by rw [zpow_neg]; norm_cast
  have hX7 : X ^ (7 / 18 : ℝ) ≤ X ^ (7 / 18 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hXa (by linarith)
  have hH2 : 2 * P ^ 2 ≤ H := by
    have hb : 2 * P ^ 2 * P ^ 4 ≤ X ^ (7 / 18 + ε) := by
      have : 2 * P ^ 2 * P ^ 4 = 2 * P ^ 6 := by ring
      rw [this]; linarith
    have hp4 : 0 < P ^ 4 := by positivity
    calc 2 * P ^ 2 = 2 * P ^ 2 * P ^ 4 * (P ^ 4)⁻¹ := by field_simp
      _ ≤ X ^ (7 / 18 + ε) * (P ^ 4)⁻¹ := by gcongr
      _ = X ^ (7 / 18 + ε) * P ^ (-4 : ℤ) := by rw [hP4]
      _ ≤ H := hlo
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hR2 : 2 ≤ R := by
    have : 2 * P ≤ H / P := by rw [le_div_iff₀ hP0]; nlinarith
    nlinarith
  have hRpos : 0 < R := by linarith
  have hL : 0 < L := Nat.floor_pos.mpr (by linarith)
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  have hL4 : R / 4 ≤ (L : ℝ) := by
    have h1' : R / 2 < (L : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2' : (1 : ℝ) ≤ L := by exact_mod_cast hL
    linarith
  have hYpos : 0 < Y := Real.rpow_pos_of_pos (by linarith) _
  have hδ0 : 0 ≤ δ := le_trans (by positivity) h1
  have hfac : (π / (2 * (L : ℝ))) ^ 2 ≤ 4 * π ^ 2 * (R ^ 2)⁻¹ := by
    rw [div_pow, mul_pow]
    rw [div_le_iff₀ (by positivity)]
    have : R ^ 2 ≤ 2 ^ 2 * (L : ℝ) ^ 2 * 4 := by nlinarith
    calc π ^ 2 = 4 * π ^ 2 * (R ^ 2)⁻¹ * R ^ 2 / 4 := by field_simp
      _ ≤ 4 * π ^ 2 * (R ^ 2)⁻¹ * (2 ^ 2 * (L : ℝ) ^ 2 * 4) / 4 := by gcongr
      _ = 4 * π ^ 2 * (R ^ 2)⁻¹ * (2 ^ 2 * (L : ℝ) ^ 2) := by ring
  -- the integral form and the split at Y/4
  set f : ℝ → ℝ := fun x =>
    ‖∑ n ∈ (Finset.range (⌊Y⌋₊ + 1)).filter (fun n : ℕ => x < n ∧ (n : ℝ) ≤ x + L), a n‖ ^ 2
    with hf
  have hsum := Prep1122KLGallagherCut.win_sum_eq_integral a (⌊Y⌋₊ + 1) L
  have hII := window_sq_intervalIntegrable a (⌊Y⌋₊ + 1) L
  have hYN : Y / 4 ≤ ((⌊Y⌋₊ + 1 : ℕ) : ℝ) := by
    have := Nat.lt_floor_add_one Y; push_cast; linarith
  have hLY : -(L : ℝ) ≤ Y / 4 := by linarith
  have hI1 : IntervalIntegrable f volume (-(L : ℝ)) (Y / 4) :=
    hII.mono_set (by rw [Set.uIcc_of_le hLY, Set.uIcc_of_le (by linarith)];
                     exact Set.Icc_subset_Icc le_rfl hYN)
  have hI2 : IntervalIntegrable f volume (Y / 4) ((⌊Y⌋₊ + 1 : ℕ) : ℝ) :=
    hII.mono_set (by rw [Set.uIcc_of_le hYN, Set.uIcc_of_le (by linarith)];
                     exact Set.Icc_subset_Icc hLY le_rfl)
  have hsplit := intervalIntegral.integral_add_adjacent_intervals hI1 hI2
  have hJ0 : 0 ≤ ∫ t in Y / 4..Y, ‖roughDefect χ Y P δ t‖ ^ 2 :=
    intervalIntegral.integral_nonneg (by linarith) (fun _ _ => by positivity)
  have hI2n : 0 ≤ ∫ x in (Y / 4)..((⌊Y⌋₊ + 1 : ℕ) : ℝ), f x :=
    intervalIntegral.integral_nonneg hYN (fun _ _ => by positivity)
  rw [hsum, ← hsplit, mul_add]
  have hedge : (π / (2 * (L : ℝ))) ^ 2 * ∫ x in (-(L : ℝ))..(Y / 4), f x ≤ C1 / c * δ := by
    refine hE.trans ?_
    rw [div_mul_eq_mul_div, le_div_iff₀ hc]
    have : c * R / Y ≤ δ := h1
    rw [div_le_iff₀ hYpos] at this
    calc C1 * (R / Y) * c = C1 * (c * R / Y) := by ring
      _ ≤ C1 * δ := by gcongr
  have hmain : (π / (2 * (L : ℝ))) ^ 2 * ∫ x in (Y / 4)..((⌊Y⌋₊ + 1 : ℕ) : ℝ), f x ≤
      4 * π ^ 2 * C2 * ((R ^ (-2 : ℤ)) *
        (∫ t in Y / 4..Y, ‖roughDefect χ Y P δ t‖ ^ 2) + δ) := by
    calc (π / (2 * (L : ℝ))) ^ 2 * ∫ x in (Y / 4)..((⌊Y⌋₊ + 1 : ℕ) : ℝ), f x
        ≤ 4 * π ^ 2 * (R ^ 2)⁻¹ * (C2 * ((∫ t in Y / 4..Y, ‖roughDefect χ Y P δ t‖ ^ 2) +
            R ^ 2 * δ)) := mul_le_mul hfac hM hI2n (by positivity)
      _ = 4 * π ^ 2 * C2 * ((R ^ (-2 : ℤ)) *
            (∫ t in Y / 4..Y, ‖roughDefect χ Y P δ t‖ ^ 2) + δ) := by
          rw [zpow_neg]; norm_cast; field_simp
  have hRJ : 0 ≤ R ^ (-2 : ℤ) * ∫ t in Y / 4..Y, ‖roughDefect χ Y P δ t‖ ^ 2 :=
    mul_nonneg (by positivity) hJ0
  have hcd : C1 / c * δ ≤ C1 / c * (R ^ (-2 : ℤ) *
      (∫ t in Y / 4..Y, ‖roughDefect χ Y P δ t‖ ^ 2) + δ) := by gcongr; linarith
  calc _ ≤ C1 / c * δ + 4 * π ^ 2 * C2 * ((R ^ (-2 : ℤ)) *
        (∫ t in Y / 4..Y, ‖roughDefect χ Y P δ t‖ ^ 2) + δ) := add_le_add hedge hmain
    _ ≤ _ := by rw [add_mul]; linarith

example : type_of% @Prep1122KLGallagherCut.saffari_vaughan_device :=
  saffari_vaughan_device_of_pieces

end LeanLab.KumchevLiu2007.Split1122KLSaffariVaughan

#print axioms LeanLab.KumchevLiu2007.Split1122KLSaffariVaughan.edge_window_bound
#print axioms LeanLab.KumchevLiu2007.Split1122KLSaffariVaughan.saffari_vaughan_average
#print axioms LeanLab.KumchevLiu2007.Split1122KLSaffariVaughan.window_sq_intervalIntegrable
#print axioms LeanLab.KumchevLiu2007.Split1122KLSaffariVaughan.saffari_vaughan_device_of_pieces
