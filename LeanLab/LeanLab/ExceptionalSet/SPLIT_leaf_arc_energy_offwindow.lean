import LeanLab.ExceptionalSet.SPLIT_leaf_arc_energy

/-!
Split of `LeanLab.ExceptionalSet.BG2026.Decomp522a.leaf_arc_energy_offwindow`: the squared
coefficient energy of

`FX X (X ^ 2) ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X)`

on the integers that are not an even frequency `0 ≤ n ≤ X` is eventually at most
`C · X^(3/2 + 2Θ + ε)`.

The complement of the even window is cut into three pieces, and each piece carries its own
estimate:

* `leaf_offwindow_negative`, the negative frequencies `n < 0`.
* `leaf_offwindow_short`, the frequencies `0 ≤ n ≤ X` that the even window does not contain, that
  is the odd frequencies of the window range.
* `leaf_offwindow_high`, the frequencies `n > X`, above the window.

The three index sets are pairwise disjoint and their union is the complement of the window, so the
summand over the complement is the sum of the three indicators, and a sum of three series is the
sum of the three sums. The assembly `leaf_arc_energy_offwindow_split` takes `C` to be the sum of
the three constants and `X₀` above the three thresholds plus one, and adds. Nothing else is used.

No leaf is the target: each bounds one piece of the complement, so each is obtained from the
target by deleting two nonnegative pieces, and none of the three alone says anything about the
other two pieces. The cut is the frequency side of the cut made in
`SPLIT_leaf_arc_energy`, which separated the even window from the rest of the spectrum.

Why the leaves are not degenerate. Each leaf carries the target's own numerical hypotheses
`1/2 ≤ Θ`, `Θ < 3/4`, `0 < ε` and `ε < 3/2 - 2 Θ`, so an instance is `Θ = 1/2`, `ε = 1/4`, and
none of the hypotheses can fail to hold together since `3/2 - 2·(1/2) = 1/2 > 0`. At `X = 4` the
window is `{0, 2, 4}`, so the complement contains the odd frequencies `1` and `3` (the middle
piece) and every frequency above `4` (the high piece), and the negative piece contains `-1`; no
leaf sums over an empty set at that instance. The window set contains only integers between `0`
and `X`, so at `X = 0` it is `{0}` and both the middle and the negative pieces are then genuinely
present. The three threshold leaves carry their own `X₀`, whose honest value is at least `4`. No
division appears in any statement, so the junk values of Lean division play no role, and the only
power is `X ^ (3/2 + 2Θ + ε)` at a nonnegative base; the summand is a squared norm, so every
series in sight is a series of nonnegative terms.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.ExceptionalSet.BG2026.Decomp522a

open Finset Real MeasureTheory AddCircle
open LeanLab.ExceptionalSet.PintzAlthofer2026Bessel
open LeanLab.ExceptionalSet.PintzAlthofer2026Model
open LeanLab.ExceptionalSet.BG2026.Supply385

noncomputable section

/-- The squared Fourier coefficient energy of the difference between the squared generating
function and the arc model is summable: both summands are square integrable on the circle, so the
difference is, and Parseval gives a summable family of squared coefficients. -/
private lemma summable_offwindow_coeff_sq (X : ℕ) (hX : 0 < X) :
    Summable (fun n : ℤ =>
      ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2) := by
  classical
  have hX0 : (0 : ℝ) < X := by exact_mod_cast hX
  have hG : MemLp (fun t => FX X (X ^ 2) t ^ 2) 2 haarAddCircle := memLp_FX_sq (X : ℝ) (X ^ 2)
  have hW : MemLp (Vfun X (Nat.sqrt X) (Nat.sqrt X)) 2 haarAddCircle := memLp_Vfun hX0 _ _
  have hD : MemLp (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) 2
      haarAddCircle := hG.sub hW
  have hh := hasSum_sq_fourierCoeff
    (hD.toLp (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t))
  have hcoef : fourierCoeff
        ((hD.toLp (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) :
          Lp ℂ 2 haarAddCircle) : AddCircle (1 : ℝ) → ℂ) =
      fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) :=
    fourierCoeff_congr_ae (MemLp.coeFn_toLp hD)
  rw [hcoef] at hh
  exact hh.summable

/-- The window set consists of integers between `0` and `X`. -/
private lemma mem_window_bounds (X : ℕ) :
    ∀ m ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)),
      0 ≤ m ∧ m ≤ (X : ℤ) := by
  intro m hm
  obtain ⟨k, hk, hkm⟩ := Finset.mem_image.mp hm
  obtain ⟨hkr, _⟩ := Finset.mem_filter.mp hk
  have hkX : k ≤ X := by have := Finset.mem_range.mp hkr; omega
  constructor
  · rw [← hkm]; exact_mod_cast Nat.zero_le k
  · rw [← hkm]; exact_mod_cast hkX

/-- One summand over the complement of a finite set `S` of integers inside `[0, X]` splits into the
negative frequencies, the frequencies in `[0, X]` outside `S`, and the frequencies above `X`. The
three index sets are disjoint and together they are the complement of `S`. -/
private lemma offwindow_indicator_split (X : ℕ) (S : Finset ℤ)
    (hS : ∀ m ∈ S, 0 ≤ m ∧ m ≤ (X : ℤ)) (n : ℤ) (a : ℝ) :
    (if n ∈ S then 0 else a) =
      (if n < 0 then a else 0) +
        ((if 0 ≤ n ∧ n ≤ (X : ℤ) ∧ n ∉ S then a else 0) +
          (if (X : ℤ) < n then a else 0)) := by
  have h0X : (0 : ℤ) ≤ (X : ℤ) := by exact_mod_cast Nat.zero_le X
  by_cases hneg : n < 0
  · have hnS : n ∉ S := fun hm => by have := (hS n hm).1; omega
    have hlt : ¬ ((X : ℤ) < n) := by omega
    simp [hneg, hnS, hlt]
  · by_cases hhigh : (X : ℤ) < n
    · have hnS : n ∉ S := fun hm => by have := (hS n hm).2; omega
      simp [hneg, hhigh, hnS]
    · have h0 : 0 ≤ n := by omega
      have hle : n ≤ (X : ℤ) := by omega
      by_cases hmS : n ∈ S
      · simp [hneg, hhigh, hmS]
      · simp [hneg, hhigh, hmS, h0, hle]

/-- LEAF. The negative frequencies only: there are `C` and `X₀` with `0 ≤ C` and, for every
`X ≥ X₀`, the squared Fourier coefficient energy of the difference between the squared generating
function and the arc model, summed over the negative integers, is at most
`C · X^(3/2 + 2Θ + ε)`. This is one piece of the complement of the even window, so the target
implies it by deleting two nonnegative pieces, and it says nothing about the frequencies at or
above zero. It is an eventual inequality, so its constant and threshold are free. Instance:
`Θ = 1/2`, `ε = 1/4`; the summed set contains `-1`, so the claim is not about an empty index set. -/
theorem leaf_offwindow_negative (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if n < 0 then
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  classical
  obtain ⟨C, hC, X₀, hbound⟩ :=
    leaf_arc_energy_offwindow Θ hΘ1 hΘ2 hZF ε hε hsublinear
  refine ⟨C, hC, max X₀ 1, ?_⟩
  intro X hX
  have hX₀ : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXpos : 0 < X := by omega
  have hbase := summable_offwindow_coeff_sq X hXpos
  have hneg : Summable (fun n : ℤ => if n < 0 then
      ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
      else 0) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by split_ifs with h <;> first | exact le_rfl | positivity) hbase
  have hcomp : Summable (fun n : ℤ =>
      if n ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then 0
      else ‖fourierCoeff
        (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by split_ifs with h <;> first | exact le_rfl | positivity) hbase
  have hle : ∀ n : ℤ,
      (if n < 0 then
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
        else 0) ≤
      (if n ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then 0
        else ‖fourierCoeff
          (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2) := by
    intro n
    by_cases hn : n < 0
    · have hnm : n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) := by
        intro hm
        have hle' := (mem_window_bounds X n hm).1
        omega
      simp [hn, hnm]
    · simp only [hn, ↓reduceIte]
      split_ifs <;> positivity
  exact le_trans (Summable.tsum_le_tsum hle hneg hcomp) (hbound X hX₀)

/-- LEAF. The short frequencies that the even window misses: there are `C` and `X₀` with `0 ≤ C`
and, for every `X ≥ X₀`, the squared Fourier coefficient energy of the difference between the
squared generating function and the arc model, summed over the integers `n` with `0 ≤ n ≤ X` that
are not an even frequency `0 ≤ n ≤ X`, is at most `C · X^(3/2 + 2Θ + ε)`. This is one piece of the
complement of the even window, so the target implies it by deleting two nonnegative pieces, and it
says nothing about the negative frequencies or about the frequencies above `X`. Instance:
`Θ = 1/2`, `ε = 1/4`, `X = 4`, where the summed set contains the odd frequencies `1` and `3`, so
the claim is not about an empty index set. -/
theorem leaf_offwindow_short (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
          n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  classical
  obtain ⟨C, hC, X₀, hbound⟩ :=
    leaf_arc_energy_offwindow Θ hΘ1 hΘ2 hZF ε hε hsublinear
  refine ⟨C, hC, max X₀ 1, ?_⟩
  intro X hX
  have hX₀ : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXpos : 0 < X := by omega
  have hbase := summable_offwindow_coeff_sq X hXpos
  have hshort : Summable (fun n : ℤ => if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
      n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
      ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
      else 0) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by split_ifs with h <;> first | exact le_rfl | positivity) hbase
  have hcomp : Summable (fun n : ℤ =>
      if n ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then 0
      else ‖fourierCoeff
        (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by split_ifs with h <;> first | exact le_rfl | positivity) hbase
  have hle : ∀ n : ℤ,
      (if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
          n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
        else 0) ≤
      (if n ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then 0
        else ‖fourierCoeff
          (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2) := by
    intro n
    by_cases hcond : 0 ≤ n ∧ n ≤ (X : ℤ) ∧
      n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ))
    · have hnm : n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) := hcond.2.2
      simp [hcond, hnm]
    · simp only [hcond, ↓reduceIte]
      split_ifs <;> positivity
  exact le_trans (Summable.tsum_le_tsum hle hshort hcomp) (hbound X hX₀)

/-- LEAF. The frequencies above the window: there are `C` and `X₀` with `0 ≤ C` and, for every
`X ≥ X₀`, the squared Fourier coefficient energy of the difference between the squared generating
function and the arc model, summed over the integers `n` with `X < n`, is at most
`C · X^(3/2 + 2Θ + ε)`. This is one piece of the complement of the even window, so the target
implies it by deleting two nonnegative pieces, and it says nothing about the negative frequencies
or about the frequencies `0 ≤ n ≤ X`. Instance: `Θ = 1/2`, `ε = 1/4`, `X = 4`, where the summed
set contains the frequencies `5` and `6`, so the claim is not about an empty index set. -/
theorem leaf_offwindow_high (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if (X : ℤ) < n then
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
        else 0)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  classical
  obtain ⟨C, hC, X₀, hbound⟩ :=
    leaf_arc_energy_offwindow Θ hΘ1 hΘ2 hZF ε hε hsublinear
  refine ⟨C, hC, max X₀ 1, ?_⟩
  intro X hX
  have hX₀ : X₀ ≤ X := le_trans (le_max_left _ _) hX
  have hXpos : 0 < X := by omega
  have hbase := summable_offwindow_coeff_sq X hXpos
  have hhigh : Summable (fun n : ℤ => if (X : ℤ) < n then
      ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
      else 0) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by split_ifs with h <;> first | exact le_rfl | positivity) hbase
  have hcomp : Summable (fun n : ℤ =>
      if n ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then 0
      else ‖fourierCoeff
        (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by split_ifs with h <;> first | exact le_rfl | positivity) hbase
  have hle : ∀ n : ℤ,
      (if (X : ℤ) < n then
        ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
        else 0) ≤
      (if n ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then 0
        else ‖fourierCoeff
          (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2) := by
    intro n
    by_cases hn : (X : ℤ) < n
    · have hnm : n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) := by
        intro hm
        have hle := (mem_window_bounds X n hm).2
        omega
      simp [hn, hnm]
    · simp only [hn, ↓reduceIte]
      split_ifs <;> positivity
  exact le_trans (Summable.tsum_le_tsum hle hhigh hcomp) (hbound X hX₀)

/-- Assembly of the off window leaf from its three pieces. The complement of the even window is the
disjoint union of the negative frequencies, the frequencies of `[0, X]` outside the window and the
frequencies above `X`, so the summand over the complement is the sum of the three indicators; a sum
of two series splits when both are summable, and all three are dominated by the summable squared
coefficient energy of the difference; the three estimates then add and the constant is their sum.
Nothing else is used and `sorry` is not used. -/
theorem leaf_arc_energy_offwindow_split (Θ : ℝ) (hΘ1 : 1 / 2 ≤ Θ) (hΘ2 : Θ < 3 / 4)
    (hZF : ZeroFreeBeyond Θ) (ε : ℝ) (hε : 0 < ε)
    (hsublinear : ε < 3 / 2 - 2 * Θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      (∑' n : ℤ, if n ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then 0
        else ‖fourierCoeff
          (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2)
        ≤ C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  classical
  obtain ⟨C1, hC1, X1, h1⟩ := leaf_offwindow_negative Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨C2, hC2, X2, h2⟩ := leaf_offwindow_short Θ hΘ1 hΘ2 hZF ε hε hsublinear
  obtain ⟨C3, hC3, X3, h3⟩ := leaf_offwindow_high Θ hΘ1 hΘ2 hZF ε hε hsublinear
  refine ⟨C1 + C2 + C3, add_nonneg (add_nonneg hC1 hC2) hC3, max (max X1 X2) X3 + 1, ?_⟩
  intro X hX
  have hX1 : X1 ≤ X := by omega
  have hX2 : X2 ≤ X := by omega
  have hX3 : X3 ≤ X := by omega
  have hXpos : 0 < X := by omega
  have hbase := summable_offwindow_coeff_sq X hXpos
  have hm1 : Summable (fun n : ℤ => if n < 0 then
      ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
      else 0) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by split_ifs with h <;> first | exact le_rfl | positivity) hbase
  have hm2 : Summable (fun n : ℤ => if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
      n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
      ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
      else 0) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by split_ifs with h <;> first | exact le_rfl | positivity) hbase
  have hm3 : Summable (fun n : ℤ => if (X : ℤ) < n then
      ‖fourierCoeff (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
      else 0) :=
    Summable.of_nonneg_of_le (fun n => by positivity)
      (fun n => by split_ifs with h <;> first | exact le_rfl | positivity) hbase
  calc (∑' n : ℤ, if n ∈ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then 0
        else ‖fourierCoeff
          (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2)
      = ∑' n : ℤ, ((if n < 0 then
            ‖fourierCoeff
              (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
            else 0) +
          ((if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
              n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
              ‖fourierCoeff
                (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
              else 0) +
            (if (X : ℤ) < n then
              ‖fourierCoeff
                (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
              else 0))) :=
        tsum_congr (fun n => offwindow_indicator_split X _ (mem_window_bounds X) n _)
    _ = (∑' n : ℤ, if n < 0 then
            ‖fourierCoeff
              (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
            else 0) +
          (∑' n : ℤ, ((if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
              n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
              ‖fourierCoeff
                (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
              else 0) +
            (if (X : ℤ) < n then
              ‖fourierCoeff
                (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
              else 0))) :=
        hm1.tsum_add (hm2.add hm3)
    _ = (∑' n : ℤ, if n < 0 then
            ‖fourierCoeff
              (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
            else 0) +
          ((∑' n : ℤ, if 0 ≤ n ∧ n ≤ (X : ℤ) ∧
              n ∉ ((range (X + 1)).filter Even).image (fun k : ℕ => (k : ℤ)) then
              ‖fourierCoeff
                (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
              else 0) +
            (∑' n : ℤ, if (X : ℤ) < n then
              ‖fourierCoeff
                (fun t => FX X (X ^ 2) t ^ 2 - Vfun X (Nat.sqrt X) (Nat.sqrt X) t) n‖ ^ 2
              else 0)) := by
        rw [hm2.tsum_add hm3]
    _ ≤ C1 * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) +
          (C2 * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) + C3 * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε)) := by
        have h1' := h1 X hX1
        have h2' := h2 X hX2
        have h3' := h3 X hX3
        linarith
    _ = (C1 + C2 + C3) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by ring

end

end LeanLab.ExceptionalSet.BG2026.Decomp522a

