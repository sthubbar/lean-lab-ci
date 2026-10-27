/-
P0045 Languasco, Pintz, Zaccagnini 2007, Section 3, and idea I-0091: the exceptional set from
a minor arc sup bound, for a general exponent σ.

Unit U-1220, T2 FRONTIER, PC run 20261020T1203Z-6833.

Source: P0045 preprint p.4, Section 3: `S(α) ≪ X^{4/5} L⁴` on the minor arcs, then
`Σ_{N ∈ J(X)} |R''_𝔪(N)|² ≪ X^{13/5} L^{2k+9}`, then (7), the count of even `N ∈ J(X)` with
`|R''_𝔪(N)| ≥ N L^{k−1/2}` is `≪ X^{3/5} L^{10}`.

What is here:
* `MinorL2σ σ` and `Eq7σ σ`: the two Section 3 statements with `4/5` replaced by any `σ`,
  exponents `2σ + 1` and `2σ − 1`. `minorL2_iff` and `eq7_iff`: at `σ = 4/5` they are the
  cited `MinorL2` and `Eq7` of Statements.lean exactly.
* `eq7σ_of_minorL2σ`: the counting step, PROVED unconditional for every `σ`.
* `eq7_of_minorL2`: the paper's (7) from its L² bound, PROVED unconditional, so the cited `eq7`
  is no longer an independent input: (7) follows from `minorL2`.
* `eq7_19_24`: I-0091's exponent, `MinorL2σ (19/24) → Eq7σ (19/24)`, exceptions `X^{7/12} L^{10}`,
  the shape the MPR 2026 minor arc bound `N^{19/24}` would give. CONDITIONAL, as an implication.

KNOWN mathematics, the paper's own counting step. AI wrote this Lean code. Checked only by the
Lean kernel. Binary Goldbach is OPEN; nothing here is Goldbach.
-/
import Mathlib
import LeanLab.LPZ2007.Statements

namespace LeanLab.LPZ2007.ExceptionalOfSup

open Finset Real LeanLab.LPZ2007

noncomputable section

open Classical in
/-- Section 3 with a general exponent: `Σ_{N ∈ J(X)} |R''_𝔪(N)|² ≪ X^{2σ+1} L^{2k+9}`. -/
def MinorL2σ (σ : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ B X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ P : ℝ, PRange X P →
    ∑ N ∈ (Icc 1 ⌊X⌋₊).filter (fun N : ℕ => 2 * X / 3 ≤ (N : ℝ)), ‖Rmpp k X P N‖ ^ 2 ≤
      B * X ^ (2 * σ + 1) * Lg X ^ (2 * k + 9)

/-- (7) with a general exponent: the exceptional set is `≪ X^{2σ−1} L^{10}`. -/
def Eq7σ (σ : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ B X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ P : ℝ, PRange X P →
    ((Exc7 k X P).card : ℝ) ≤ B * X ^ (2 * σ - 1) * Lg X ^ 10

/-- At `σ = 4/5` the general L² statement is the cited `MinorL2`. -/
theorem minorL2_iff : MinorL2 ↔ MinorL2σ (4 / 5) := by
  have h : (2 : ℝ) * (4 / 5) + 1 = 13 / 5 := by norm_num
  simp only [MinorL2, MinorL2σ, h]

/-- At `σ = 4/5` the general (7) is the cited `Eq7`. -/
theorem eq7_iff : Eq7 ↔ Eq7σ (4 / 5) := by
  have h : (2 : ℝ) * (4 / 5) - 1 = 3 / 5 := by norm_num
  simp only [Eq7, Eq7σ, h]

/-- `L = log₂ X ≥ 1` for `X ≥ 2`. -/
theorem one_le_Lg {X : ℝ} (hX : 2 ≤ X) : 1 ≤ Lg X := by
  unfold Lg
  rw [Real.le_logb_iff_rpow_le (by norm_num) (by linarith)]
  simpa using hX

/-- Exceptional `N` lie in the summation range of the L² bound. -/
theorem exc7_subset (k : ℕ) (X P : ℝ) :
    Exc7 k X P ⊆ (Icc 1 ⌊X⌋₊).filter (fun N : ℕ => 2 * X / 3 ≤ (N : ℝ)) := by
  intro N hN
  simp only [Exc7, mem_filter] at hN
  simp only [mem_filter]
  exact ⟨hN.1, hN.2.2.1.1⟩

/-- **The counting step of Section 3, PROVED unconditional for every `σ`.** -/
theorem eq7σ_of_minorL2σ {σ : ℝ} (h : MinorL2σ σ) : Eq7σ σ := by
  intro k hk
  obtain ⟨B, X0, hB⟩ := h k hk
  refine ⟨9 / 4 * max B 0, max X0 2, fun X hX P hP => ?_⟩
  have hX2 : 2 ≤ X := le_trans (le_max_right _ _) hX
  have hX0 : 0 < X := by linarith
  have hL1 : 1 ≤ Lg X := one_le_Lg hX2
  have hL0 : 0 < Lg X := by linarith
  set L := Lg X with hLdef
  set t : ℝ := L ^ ((k : ℝ) - 1 / 2) with ht
  have ht0 : 0 < t := Real.rpow_pos_of_pos hL0 _
  have hsum := hB X (le_trans (le_max_left _ _) hX) P hP
  set m : ℝ := 2 * X / 3 * t with hm
  have hm0 : 0 ≤ m := by positivity
  -- each exceptional `N` has `‖R‖ ≥ m`
  have hlow : ∀ N ∈ Exc7 k X P, m ≤ ‖Rmpp k X P N‖ := by
    intro N hN
    simp only [Exc7, mem_filter] at hN
    have h1 : 2 * X / 3 ≤ (N : ℝ) := hN.2.2.1.1
    calc m = 2 * X / 3 * t := rfl
      _ ≤ N * t := by gcongr
      _ = N * Lg X ^ ((k : ℝ) - 1 / 2) := rfl
      _ ≤ ‖Rmpp k X P N‖ := hN.2.2.2
  have hcard : ((Exc7 k X P).card : ℝ) * m ^ 2 ≤ ∑ N ∈ Exc7 k X P, ‖Rmpp k X P N‖ ^ 2 := by
    have : ∑ N ∈ Exc7 k X P, m ^ 2 ≤ ∑ N ∈ Exc7 k X P, ‖Rmpp k X P N‖ ^ 2 :=
      Finset.sum_le_sum fun N hN => pow_le_pow_left₀ hm0 (hlow N hN) 2
    rwa [Finset.sum_const, nsmul_eq_mul] at this
  have hsub : ∑ N ∈ Exc7 k X P, ‖Rmpp k X P N‖ ^ 2 ≤
      ∑ N ∈ (Icc 1 ⌊X⌋₊).filter (fun N : ℕ => 2 * X / 3 ≤ (N : ℝ)), ‖Rmpp k X P N‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (exc7_subset k X P) (fun _ _ _ => by positivity)
  -- exponent bookkeeping
  have htsq : t ^ 2 * L ^ (10 : ℕ) = L ^ (2 * k + 9) := by
    rw [ht, ← Real.rpow_natCast (L ^ _), ← Real.rpow_mul hL0.le, ← Real.rpow_natCast L 10,
      ← Real.rpow_add hL0, ← Real.rpow_natCast L (2 * k + 9)]
    congr 1
    have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
    push_cast; ring
  have hXp : X ^ (2 * σ + 1) = X ^ (2 * σ - 1) * X ^ (2 : ℕ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hX0]; congr 1; push_cast; ring
  have hmsq : m ^ 2 = 4 / 9 * X ^ (2 : ℕ) * t ^ 2 := by rw [hm]; ring
  have hmpos : 0 < m ^ 2 := by rw [hmsq]; positivity
  have hBle : B * X ^ (2 * σ + 1) * L ^ (2 * k + 9) ≤
      max B 0 * X ^ (2 * σ + 1) * L ^ (2 * k + 9) := by
    gcongr; exact le_max_left _ _
  have hmain : ((Exc7 k X P).card : ℝ) * m ^ 2 ≤
      (9 / 4 * max B 0 * X ^ (2 * σ - 1) * L ^ 10) * m ^ 2 := by
    calc ((Exc7 k X P).card : ℝ) * m ^ 2 ≤ max B 0 * X ^ (2 * σ + 1) * L ^ (2 * k + 9) :=
          hcard.trans (hsub.trans (hsum.trans hBle))
      _ = (9 / 4 * max B 0 * X ^ (2 * σ - 1) * L ^ 10) * m ^ 2 := by
          rw [hmsq, hXp, ← htsq]; ring
  exact le_of_mul_le_mul_right hmain hmpos

/-- **The paper's (7) from its L² bound, PROVED unconditional**: `MinorL2 → Eq7`. -/
theorem eq7_of_minorL2 (h : MinorL2) : Eq7 :=
  eq7_iff.mpr (eq7σ_of_minorL2σ (minorL2_iff.mp h))

/-- I-0091's exponent: an L² bound with `σ = 19/24` gives exceptions `≪ X^{7/12} L^{10}`.
CONDITIONAL ON `MinorL2σ (19/24)`, as an implication. -/
theorem eq7_19_24 (h : MinorL2σ (19 / 24)) :
    ∀ k : ℕ, 1 ≤ k → ∃ B X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ P : ℝ, PRange X P →
      ((Exc7 k X P).card : ℝ) ≤ B * X ^ (7 / 12 : ℝ) * Lg X ^ 10 := by
  have e : (2 : ℝ) * (19 / 24) - 1 = 7 / 12 := by norm_num
  have := eq7σ_of_minorL2σ h
  simpa only [Eq7σ, e] using this

/-- Vacuity check for `Eq7σ`: the exceptional set is a genuine finite set and the bound is
not empty, e.g. at `X = 2`, `L = 1` and `X^{2σ−1} = 2^{2σ−1} > 0`. -/
theorem bound_pos (σ : ℝ) : 0 < (2 : ℝ) ^ (2 * σ - 1) * Lg 2 ^ 10 := by
  have : Lg 2 = 1 := by unfold Lg; simp
  rw [this]; positivity

end

end LeanLab.LPZ2007.ExceptionalOfSup
