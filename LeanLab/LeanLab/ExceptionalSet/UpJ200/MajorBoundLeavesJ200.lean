import Mathlib
import LeanLab.ExceptionalSet.UpJ200.Decomp505a
import LeanLab.ExceptionalSet.BrudernPerelli1998
import LeanLab.ExceptionalSet.State1539
import LeanLab.ExceptionalSet.UpJ200.DecompJ200
import LeanLab.ExceptionalSet.UpJ200.Decomp371a

/-! Split of `DecompJ200.leaf_major_bound`, P0082 page 365 Lemma 8, second and third parts.

An existing file may not gain a `sorry`, so the two open steps of the major arc bound live here,
in the `UpJ200` cone that `DecompJ200` can import. The only definition of that file used below is
`window`, copied verbatim in `UpJ200/DecompJ200.lean`, so the leaves apply to the window of
`DecompJ200` by definition. `DecompJ200.leaf_major_bound` proves itself from these two leaves,
after the first part, the Fourier identity `leaf_major_identity`, which is proved there.

AI wrote this Lean code. Goldbach is open. -/

namespace LeanLab.ExceptionalSet.UpJ200.MajorBoundLeavesJ200

open Real Finset Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)

attribute [local instance] Classical.propDecidable

/-- P0082 page 358 Lemma 4, applied on page 364 after display (23). With `Δ = E^(-1/8)`, at most
`B N Δ` members of the window have `{F(n)} < Δ` or `{F(n)} > 1 - Δ`, for every small `κ`.

Proved from the sealed discrepancy input `U1539.Lemma4`, P0082 page 359, through the instance
`U1539.lemma4`, in the same way as `Decomp404a.boundary_of_lemma4`, which cannot be imported here
because `Decomp404a` imports `DecompJ200`. The window geometry is
`UpJ200.Decomp371a.window_subset_Ioc`. No `sorry` remains on this step; the axioms it carries are
those of `U1539.lemma4`, which is where the paper's exponential sum estimate enters. -/
theorem leaf_major_fractional_boundary (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
            1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
  classical
  obtain ⟨κa, A, hκa, hdisc⟩ := LeanLab.ExceptionalSet.U1539.lemma4 γ h1 h2
  refine ⟨8 * κa, by positivity, fun κ hκ hκsmall => ?_⟩
  let B := 2 * |A| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hE : Tendsto (fun N : ℕ => calE γ κ N) atTop atTop := by
    exact Real.tendsto_exp_atTop.comp
      (((tendsto_rpow_atTop (by linarith : 0 < 3 - 2 * γ)).comp hlog).const_mul_atTop hκ)
  obtain ⟨NE, hNE⟩ := eventually_atTop.mp (hE.eventually_ge_atTop 2)
  refine ⟨B, hB, max 16 NE, fun N hN => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hE1 : 1 < calE γ κ N := lt_of_lt_of_le (by norm_num) (hNE N ((le_max_right _ _).trans hN))
  let Δ := calE γ κ N ^ (-(1 / 8 : ℝ))
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hΔ1 : Δ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hE1 (by norm_num)
  have hF1 : 1 < F γ N := by
    rw [F]
    exact Real.one_lt_exp_iff.mpr (Real.rpow_pos_of_pos hL _)
  have hα : F γ N ^ (-(1 / 2 : ℝ)) < |(1 : ℝ)| := by
    simpa using Real.rpow_lt_one_of_one_lt_of_neg hF1 (by norm_num : -(1 / 2 : ℝ) < 0)
  have hlo := hdisc N hN1 1 hα (by norm_num) Δ 0 (by norm_num) hΔ hΔ1.le
  have hhi := hdisc N hN1 1 hα (by norm_num) 1 (1 - Δ) (by linarith) (by linarith) le_rfl
  simp only [one_mul, sub_zero, sub_sub_cancel] at hlo hhi
  have herr : Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) ≤ Δ := by
    dsimp [Δ, calE]
    rw [← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    have hp : 0 ≤ Real.log N ^ (3 - 2 * γ) := (Real.rpow_pos_of_pos hL _).le
    nlinarith [mul_le_mul_of_nonneg_right hκsmall hp]
  let L := (Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
    0 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < Δ)
  let R := (Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
    1 - Δ ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < 1)
  have hsubset : (window γ N).filter (fun n : ℕ =>
      Int.fract (F γ n) < Δ ∨ 1 - Δ < Int.fract (F γ n)) ⊆ L ∪ R := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnW, hn⟩
    have hnI := UpJ200.Decomp371a.window_subset_Ioc γ h1 N hN16 hnW
    rcases hn with hn | hn
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnI, Int.fract_nonneg _, hn⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnI, hn.le, Int.fract_lt_one _⟩)
  have hcard : (((window γ N).filter (fun n : ℕ =>
      Int.fract (F γ n) < Δ ∨ 1 - Δ < Int.fract (F γ n))).card : ℝ) ≤ L.card + R.card := by
    exact_mod_cast (Finset.card_le_card hsubset).trans (Finset.card_union_le L R)
  have hl : (L.card : ℝ) ≤ Δ * N / 2 + |A| * N * Δ := by
    have ha := (abs_le.mp hlo).2
    change (L.card : ℝ) - Δ * N / 2 ≤ _ at ha
    have hbound : A * N * Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) ≤ |A| * N * Δ := by
      calc _ ≤ |A| * N * Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) := by gcongr; exact le_abs_self _
           _ ≤ _ := by gcongr
    linarith
  have hr : (R.card : ℝ) ≤ Δ * N / 2 + |A| * N * Δ := by
    have ha := (abs_le.mp hhi).2
    change (R.card : ℝ) - Δ * N / 2 ≤ _ at ha
    have hbound : A * N * Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) ≤ |A| * N * Δ := by
      calc _ ≤ |A| * N * Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) := by gcongr; exact le_abs_self _
           _ ≤ _ := by gcongr
    linarith
  calc
    _ ≤ (L.card : ℝ) + R.card := hcard
    _ ≤ (Δ * N / 2 + |A| * N * Δ) + (Δ * N / 2 + |A| * N * Δ) := add_le_add hl hr
    _ = _ := by dsimp [B]; ring


/-- LEAF: P0082 page 362 Lemma 7, with the odd second moment of pages 366 to 369 displays (29) and
(30): the real part of `R₁(ν_n) + R₁(ν_n + 1)` is below `c₀ X E^(-1/10)` for at most
`B N E^(-1/12)` members of the window. -/
theorem leaf_major_coefficient_lower (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (((window γ N).filter (fun n : ℕ =>
            (U1539.R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
              U1539.R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
                c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
            B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  exact LeanLab.ExceptionalSet.UpJ200.Decomp505a.coefficient_lower_assembly γ h1 h2

/-- P0082 page368 display33, derived free width version of the boundary input.
Rescaling the small kappa cap allows every fixed positive power of E.
CONDITIONAL ON the discrepancy input U1539.lemma4 used by the sibling theorem. -/
theorem boundary_at_rate (γ a : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (ha : 0 < a) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((window γ N).filter (fun n : ℕ =>
          Int.fract (F γ n) < calE γ κ N ^ (-a) ∨
            1 - calE γ κ N ^ (-a) < Int.fract (F γ n))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-a) := by
  obtain ⟨κb, hκb, hb⟩ := leaf_major_fractional_boundary γ h1 h2
  refine ⟨κb / (8 * a), by positivity, fun κ hκ hκsmall => ?_⟩
  have hsmall : 8 * a * κ ≤ κb := by
    have h := (le_div_iff₀ (by positivity : 0 < 8 * a)).mp hκsmall
    nlinarith
  obtain ⟨B, hB, N₀, hb⟩ := hb (8 * a * κ) (by positivity) hsmall
  refine ⟨B, hB, N₀, fun N hN => ?_⟩
  have hpow : calE γ (8 * a * κ) N ^ (-(1 / 8 : ℝ)) = calE γ κ N ^ (-a) := by
    simp only [calE, ← Real.exp_mul]
    congr 1
    ring
  simpa only [hpow] using hb N hN

end LeanLab.ExceptionalSet.UpJ200.MajorBoundLeavesJ200
