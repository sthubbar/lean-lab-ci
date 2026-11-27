/-
BURST 2026-11-24 S4, unit S4-12. SPLIT of the LEAF
Prep1122KLGallagherCut.saffari_vaughan_device, Kumchev and Liu 2007, P0088,
arXiv 0801.0130, page 6, the display before display 20, the device of Saffari and
Vaughan, reference 21 page 25.

The leaf compares the discrete Gallagher window mean square of the W2 coefficients at
the squares with the relative window mean square of (A2.2). The cut:
* the discrete window mean square over integer k equals the integral over real x of
  the squared fixed window sums over x < n <= x + L. This is
  Prep1122KLGallagherCut.win_sum_eq_integral, already PROVED.
* L = floor(qQ/2) is at least qQ/4 once qQ is at least 2, which holds in the block
  range by eventually_big, so (pi/(2L))^2 is at most 4 pi^2 (qQ)^(-2). PROVED here.
* what is left is the device of Saffari and Vaughan in its integral form, the new
  LEAF sv_device_integral_form: for some delta between c qQ/Y and qQ/Y the integral
  of the squared fixed window sums of length L is at most a constant times the
  integral over Y/4 to Y of the squared relative window sums plus delta (qQ)^2, the
  edge of the t range below Y/4.

saffari_vaughan_device_of_leaves proves the exact statement of the parent leaf from
the new leaf. No new definition is made.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Prep1122KLGallagherCut

namespace LeanLab.KumchevLiu2007.Prep1122KLGallagherCut

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d Prep1121KLMajor
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/- Proof sketch for the LEAF below, from reference 21 of P0088: average over delta, split
a fixed window into two relative windows and change variables; the term delta (qQ)^2
carries the relative windows that start below Y/4, each holding at most about
qQ/sqrt Y + 1 squares with bounded coefficients. -/

/-- LEAF: P0088 page 6, the display before display 20, the Saffari and Vaughan device,
reference 21 page 25, in integral form. Class HARD, a citation wall. With L = floor(qQ/2),
the integral over x of the squared fixed window sums over x < n <= x + L of the W2
coefficients at the squares is at most C times the integral over Y/4 to Y of the
squared relative window sums of (A2.2) plus delta (qQ)^2, for some delta between
c qQ/Y and qQ/Y. -/
theorem sv_device_integral_form :
    ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε → ε ≤ 7 / 18 →
      ∃ C c X0 : ℝ, 0 < C ∧ 0 < c ∧ ∀ X H : ℝ, X0 ≤ X →
        X ^ (7 / 18 + ε) * (Real.log X ^ B) ^ (-4 : ℤ) ≤ H →
        H ≤ windowY X ε * (Real.log X ^ B) ^ (-4 : ℤ) →
        ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log X ^ B →
        ∀ χ : DirichletCharacter ℂ q,
          ∃ δ : ℝ, c * ((q : ℝ) * (H / Real.log X ^ B)) / windowY X ε ≤ δ ∧
            δ ≤ (q : ℝ) * (H / Real.log X ^ B) / windowY X ε ∧
            (∫ x in (-((⌊(q : ℝ) * (H / Real.log X ^ B) / 2⌋₊ : ℕ) : ℝ))..
                (((⌊windowY X ε⌋₊ + 1 : ℕ)) : ℝ),
              ‖∑ n ∈ (Finset.range (⌊windowY X ε⌋₊ + 1)).filter (fun n : ℕ => x < n ∧
                  (n : ℝ) ≤ x + ((⌊(q : ℝ) * (H / Real.log X ^ B) / 2⌋₊ : ℕ) : ℝ)),
                (fun n => ∑ m ∈ squareWindow (windowY X ε), if m ^ 2 = n then
                    (roughWeight (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) m * χ m -
                      (if χ = 1 then ((Task556a.f2Weight
                        (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
                       else 0)) else 0) n‖ ^ 2) ≤
              C * ((∫ t in windowY X ε / 4..windowY X ε,
                  ‖roughDefect χ (windowY X ε) (Real.log X ^ B) δ t‖ ^ 2) +
                δ * ((q : ℝ) * (H / Real.log X ^ B)) ^ 2) := by
  sorry

/-- PROVED. A natural floor of a real y at least one is at least y/2. -/
theorem half_le_floor_of_one_le {y : ℝ} (hy : 1 ≤ y) : y / 2 ≤ (⌊y⌋₊ : ℝ) := by
  have h1 : (1 : ℝ) ≤ (⌊y⌋₊ : ℝ) := by
    have : 1 ≤ ⌊y⌋₊ := Nat.floor_pos.mpr hy
    exact_mod_cast this
  have h2 : y < (⌊y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one y
  linarith

set_option maxHeartbeats 800000 in
/-- PROVED from the LEAF sv_device_integral_form and win_sum_eq_integral. The exact
statement of the LEAF Prep1122KLGallagherCut.saffari_vaughan_device, P0088 page 6, the
display before display 20. The discrete window mean square is the integral of the fixed
window sums, and (pi/(2L))^2 is at most 4 pi^2 (qQ)^(-2) since L is at least qQ/4. -/
theorem saffari_vaughan_device_of_leaves :
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
  obtain ⟨C, c, X0, hC, hc, kS⟩ := sv_device_integral_form B hB ε hε hε'
  obtain ⟨X1, hX1⟩ := Filter.eventually_atTop.mp (eventually_big B)
  refine ⟨4 * π ^ 2 * C, c, max X0 X1, by positivity, hc, ?_⟩
  intro X H hX hlo hhi q hq hqP χ
  obtain ⟨hXa, hL1, hbig⟩ := hX1 X (le_trans (le_max_right _ _) hX)
  obtain ⟨δ, h1, h2, h3⟩ := kS X H (le_trans (le_max_left _ _) hX) hlo hhi q hq hqP χ
  refine ⟨δ, h1, h2, ?_⟩
  have hP1 : 1 ≤ Real.log X ^ B := Real.one_le_rpow hL1 hB.le
  set P := Real.log X ^ B with hPdef
  have hP0 : 0 < P := by linarith
  have hX7 : X ^ (7 / 18 : ℝ) ≤ X ^ (7 / 18 + ε) :=
    Real.rpow_le_rpow_of_exponent_le hXa (by linarith)
  have hP4 : P ^ (-4 : ℤ) = (P ^ 4)⁻¹ := by rw [zpow_neg]; norm_cast
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
  have hQ2 : 2 ≤ (q : ℝ) * (H / P) := by
    have : 2 * P ≤ H / P := by rw [le_div_iff₀ hP0]; nlinarith
    nlinarith
  set y := (q : ℝ) * (H / P) with hy
  set L := ⌊y / 2⌋₊ with hLdef
  have hLge : y / 4 ≤ (L : ℝ) := by
    have := half_le_floor_of_one_le (y := y / 2) (by linarith)
    linarith
  have hy0 : 0 < y := by linarith
  have hLpos : (0 : ℝ) < L := by linarith
  -- the discrete mean square is the integral of the fixed window sums
  have hW := win_sum_eq_integral
    (fun n => ∑ m ∈ squareWindow (windowY X ε), if m ^ 2 = n then
      (roughWeight (windowY X ε ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m * χ m -
        (if χ = 1 then ((Task556a.f2Weight
          (windowY X ε ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
         else 0)) else 0)
    (⌊windowY X ε⌋₊ + 1) L
  rw [hW]
  set I := ∫ t in windowY X ε / 4..windowY X ε,
    ‖roughDefect χ (windowY X ε) P δ t‖ ^ 2 with hI
  have hI0 : 0 ≤ I := by
    rw [hI]
    refine intervalIntegral.integral_nonneg ?_ (fun _ _ => by positivity)
    have hY : 0 ≤ windowY X ε := Real.rpow_nonneg (by linarith) _
    linarith
  have hδ0 : 0 ≤ δ := le_trans (div_nonneg (mul_nonneg hc.le hy0.le) (Real.rpow_nonneg (by linarith) _)) h1
  -- (π / (2L))^2 ≤ 4 π^2 / y^2
  have hfac : (π / (2 * (L : ℝ))) ^ 2 ≤ 4 * π ^ 2 * y ^ (-2 : ℤ) := by
    have hb : y ^ 2 / 4 ≤ (2 * (L : ℝ)) ^ 2 := by nlinarith
    have hy2 : y ^ (-2 : ℤ) = (y ^ 2)⁻¹ := by rw [zpow_neg]; norm_cast
    calc (π / (2 * (L : ℝ))) ^ 2 = π ^ 2 / (2 * (L : ℝ)) ^ 2 := by rw [div_pow]
      _ ≤ π ^ 2 / (y ^ 2 / 4) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) hb
      _ = 4 * π ^ 2 * y ^ (-2 : ℤ) := by rw [hy2]; field_simp
  have hJ0 : 0 ≤ ∫ x in (-(L : ℝ))..(((⌊windowY X ε⌋₊ + 1 : ℕ)) : ℝ),
      ‖∑ n ∈ (Finset.range (⌊windowY X ε⌋₊ + 1)).filter (fun n : ℕ => x < n ∧
          (n : ℝ) ≤ x + (L : ℝ)),
        (fun n => ∑ m ∈ squareWindow (windowY X ε), if m ^ 2 = n then
          (roughWeight (windowY X ε ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m * χ m -
            (if χ = 1 then ((Task556a.f2Weight
              (windowY X ε ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (m : ℝ) : ℝ) : ℂ)
             else 0)) else 0) n‖ ^ 2 := by
    refine intervalIntegral.integral_nonneg ?_ (fun _ _ => by positivity)
    have : (0 : ℝ) ≤ (((⌊windowY X ε⌋₊ + 1 : ℕ)) : ℝ) := by positivity
    linarith
  have hy2pos : 0 < y ^ (-2 : ℤ) := zpow_pos hy0 _
  have hyy : y ^ (-2 : ℤ) * y ^ 2 = 1 := by
    rw [zpow_neg]; norm_cast; field_simp
  calc (π / (2 * (L : ℝ))) ^ 2 * _
      ≤ (4 * π ^ 2 * y ^ (-2 : ℤ)) * (C * (I + δ * y ^ 2)) :=
        mul_le_mul hfac h3 hJ0 (by positivity)
    _ = 4 * π ^ 2 * C * (y ^ (-2 : ℤ) * I + δ * (y ^ (-2 : ℤ) * y ^ 2)) := by ring
    _ = 4 * π ^ 2 * C * (y ^ (-2 : ℤ) * I + δ) := by rw [hyy, mul_one]

end LeanLab.KumchevLiu2007.Prep1122KLGallagherCut
