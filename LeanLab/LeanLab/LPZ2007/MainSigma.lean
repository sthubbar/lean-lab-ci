/-
P0045 Languasco, Pintz, Zaccagnini 2007, the repaired Theorem on J(X) with a general minor arc
exponent σ, and with (7) derived from the minor arc sup bound.

Unit U-1220, T2 FRONTIER, idea I-0091, PC run 20261020T1203Z-6833.

* `MainJCσ C σ`: the Theorem on `J(X)` with exceptions `≪ X^{2σ−1} (log X)^{10}`; at `σ = 4/5`
  it is `MainJC C`, `mainJCσ_iff`.
* `mainJCσ_of_sec5`: the Section 5 deduction of Repaired.lean with `Eq7σ σ` in place of `Eq7`,
  PROVED unconditional as an implication; the proof is Repaired.lean's with `3/5` replaced.
* `lpz_main_J_twoC0_minor`: the repaired Theorem, constant `2c₀ C(k, N)`, CONDITIONAL ON the cited
  `eq3`, `minorBound` and `eq25_twoC0`; the cited `eq7` and `minorL2` are no longer inputs.
* `main_19_24`: I-0091, exceptions `≪ X^{7/12} (log X)^{10}` CONDITIONAL ON `eq3`, `eq25_twoC0`
  and a minor arc sup `X^{19/24} L⁴` on P0045's arcs, `MinorBoundσ (19/24)`. That input is NOT
  known: MPR 2026 gives `N^{19/24+ε}` only with major arcs to `N^{5/12}`, while P0045 uses
  `P ≤ X^{0.41}`, and the extra `N^ε` would cost `X^{2ε}`. So this records the shape, not a result.

KNOWN mathematics. AI wrote this Lean code. Checked only by the Lean kernel.
Binary Goldbach is OPEN; nothing here is Goldbach.
-/
import Mathlib
import LeanLab.LPZ2007.Repaired
import LeanLab.LPZ2007.MinorBessel

namespace LeanLab.LPZ2007

open Finset Real LeanLab.LPZ2007.ExceptionalOfSup LeanLab.LPZ2007.MinorBessel

/-- The Theorem on `J(X)` with constant `C(k, N)` and exceptions `≪ X^{2σ−1} (log X)^{10}`. -/
def MainJCσ (C : ℕ → ℕ → ℝ) (σ : ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ B : ℝ, 0 < B ∧ ∀ η : ℝ, 0 < η → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
    ((ExcJC C k X η).card : ℝ) ≤ B * X ^ (2 * σ - 1) * Real.log X ^ 10

theorem mainJCσ_iff (C : ℕ → ℕ → ℝ) : MainJC C ↔ MainJCσ C (4 / 5) := by
  have h : (2 : ℝ) * (4 / 5) - 1 = 3 / 5 := by norm_num
  simp only [MainJC, MainJCσ, h]

theorem mainJCσ_of_sec5 (C : ℕ → ℕ → ℝ) {σ : ℝ} (h3 : Eq3) (h7 : Eq7σ σ) (h25 : Eq25C C) :
    MainJCσ C σ := by
  intro k hk
  obtain ⟨B7, X07, H7⟩ := h7 k hk
  obtain ⟨B1, X01, H3⟩ := h3 k hk
  obtain ⟨B2, η0, hη0, H25⟩ := h25 k hk
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨(|B7| + 1) / Real.log 2 ^ 10, by positivity, fun η hη => ?_⟩
  set B2' := |B2| + 1 with hB2'
  have hB2'pos : 0 < B2' := by positivity
  set η2 := min (η0 / 2) (η / (4 * B2')) with hη2
  have hη2pos : 0 < η2 := lt_min (by linarith) (by positivity)
  have hη2lt : η2 < η0 := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hB2η : B2 * η2 ≤ η / 4 := by
    have h1 : B2 * η2 ≤ B2' * η2 :=
      mul_le_mul_of_nonneg_right (by rw [hB2']; linarith [le_abs_self B2]) hη2pos.le
    have h2 : B2' * η2 ≤ B2' * (η / (4 * B2')) := mul_le_mul_of_nonneg_left (min_le_right _ _)
      hB2'pos.le
    have h3 : B2' * (η / (4 * B2')) = η / 4 := by field_simp
    linarith
  obtain ⟨X025, H25'⟩ := H25 η2 hη2pos hη2lt
  obtain ⟨Xa, HA⟩ := asymp_aux |B1| (abs_nonneg _) hη
  refine ⟨max (max (max X07 X01) (max X025 Xa)) 6, fun X hX => ?_⟩
  have hX6 : 6 ≤ X := (le_max_right _ _).trans hX
  have hXm := (le_max_left _ _).trans hX
  have hX07 : X07 ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hXm)
  have hX01 : X01 ≤ X := (le_max_right _ _).trans ((le_max_left _ _).trans hXm)
  have hX025 : X025 ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hXm)
  have hXa : Xa ≤ X := (le_max_right _ _).trans ((le_max_right _ _).trans hXm)
  obtain ⟨P, hP, HP⟩ := H25' X hX025
  have hLpos : 0 < Lg X := Lg_pos (by linarith)
  have hA := HA X hXa
  have hsub : ExcJC C k X η ⊆ Exc7 k X P := by
    intro N hN
    simp only [ExcJC, Exc7, mem_filter, mem_Icc] at hN ⊢
    obtain ⟨hNI, he, hJ, hR⟩ := hN
    refine ⟨hNI, he, hJ, ?_⟩
    by_contra hlt
    push_neg at hlt
    have hN4 : (4 : ℝ) ≤ N := by
      have := hJ.1
      have h' : (4 : ℝ) ≤ 2 * X / 3 := by linarith
      linarith
    have hN0 : (0 : ℝ) < N := by linarith
    have hlogN : 1 ≤ Real.log N := by
      rw [← Real.log_exp 1]
      exact Real.log_le_log (Real.exp_pos 1) (by linarith [Real.exp_one_lt_d9])
    have hll0 : 0 ≤ Real.log (Real.log N) := Real.log_nonneg hlogN
    have hll : Real.log (Real.log N) ≤ Real.log (Real.log X) :=
      Real.log_le_log (by linarith) (Real.log_le_log hN0 hJ.2)
    set a := Lg X ^ ((k : ℝ) - 1 / 2) with ha
    have ha0 : 0 < a := Real.rpow_pos_of_pos hLpos _
    have hak : a * √(Lg X) = Lg X ^ k := by
      rw [ha, Real.sqrt_eq_rpow, ← Real.rpow_add hLpos, ← Real.rpow_natCast]; congr 1; ring
    have e3 := H3 X hX01 P hP N he hJ
    have e25 := HP N he hJ
    set z1 := RMpp k X P N
    set z2 := Rmpp k X P N
    set c := C k N * N * Lg X ^ k with hc
    have hz1 : |z1.re - c| ≤ ‖z1 - (C k N * N * Lg X ^ k : ℂ)‖ := by
      have : z1.re - c = (z1 - (C k N * N * Lg X ^ k : ℂ)).re := by
        rw [hc, ← Complex.ofReal_pow, Complex.sub_re]
        simp only [← Complex.ofReal_natCast, ← Complex.ofReal_mul, Complex.ofReal_re]
      rw [this]; exact Complex.abs_re_le_norm _
    have hz2 : |z2.re| ≤ ‖z2‖ := Complex.abs_re_le_norm _
    have htri : |Rpp k X N - c| ≤ |Rpp k X N - (z1 + z2).re| + |z1.re - c| + |z2.re| := by
      have : Rpp k X N - c = (Rpp k X N - (z1 + z2).re) + (z1.re - c) + z2.re := by
        rw [Complex.add_re]; ring
      rw [this]
      exact abs_add_three _ _ _
    have hNa : 0 ≤ (N : ℝ) * a := by positivity
    have hB1 : B1 * N * a * Real.log (Real.log N) ≤ |B1| * N * a * Real.log (Real.log X) := by
      have i1 : B1 * (N * a * Real.log (Real.log N)) ≤ |B1| * (N * a * Real.log (Real.log N)) :=
        mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      have i2 : |B1| * (N * a * Real.log (Real.log N)) ≤ |B1| * (N * a * Real.log (Real.log X)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hll hNa) (abs_nonneg _)
      nlinarith
    have hfin : |Rpp k X N - c| ≤ 3 / 4 * (η * N * Lg X ^ k) := by
      have s1 : |Rpp k X N - c| ≤ (|B1| * Real.log (Real.log X) + 1) * (N * a) +
          B2 * η2 * N * Lg X ^ k := by
        nlinarith
      have s2 : (|B1| * Real.log (Real.log X) + 1) * (N * a) ≤ η / 2 * √(Lg X) * (N * a) :=
        mul_le_mul_of_nonneg_right hA hNa
      have s3 : η / 2 * √(Lg X) * (N * a) = η / 2 * (N * Lg X ^ k) := by rw [← hak]; ring
      have hNL : 0 ≤ (N : ℝ) * Lg X ^ k := by positivity
      have s4 : B2 * η2 * N * Lg X ^ k ≤ η / 4 * (N * Lg X ^ k) := by
        have := mul_le_mul_of_nonneg_right hB2η hNL
        linarith
      nlinarith
    have hpos : 0 < η * N * Lg X ^ k := by positivity
    linarith
  have hc := card_le_card hsub
  have hcard : ((ExcJC C k X η).card : ℝ) ≤ (Exc7 k X P).card := by exact_mod_cast hc
  have h7 := H7 X hX07 P hP
  have hLg : Lg X ^ 10 = Real.log X ^ 10 / Real.log 2 ^ 10 := by
    unfold Lg Real.logb; rw [div_pow]
  have hXp : 0 ≤ X ^ (2 * σ - 1) * Lg X ^ 10 := by positivity
  calc ((ExcJC C k X η).card : ℝ) ≤ B7 * X ^ (2 * σ - 1) * Lg X ^ 10 := hcard.trans h7
    _ ≤ (|B7| + 1) * X ^ (2 * σ - 1) * Lg X ^ 10 := by
        have : B7 ≤ |B7| + 1 := by linarith [le_abs_self B7]
        nlinarith
    _ = (|B7| + 1) / Real.log 2 ^ 10 * X ^ (2 * σ - 1) * Real.log X ^ 10 := by
        rw [hLg]; ring


/-- **The repaired Theorem on `J(X)`**, constant `2c₀ C(k, N)`, CONDITIONAL ON the cited `eq3`,
`minorBound` and `eq25_twoC0` only. -/
theorem lpz_main_J_twoC0_minor : MainJ_twoC0 :=
  mainJC_of_sec5 (fun k N => twoC0 * Ckn k N) eq3 eq7_from_cited eq25_twoC0

/-- The same implication, explicit in its three inputs, PROVED unconditional as an implication. -/
theorem mainJ_twoC0_of_minorBound (h3 : Eq3) (hm : MinorBound)
    (h25 : Eq25C (fun k N => twoC0 * Ckn k N)) : MainJ_twoC0 :=
  mainJC_of_sec5 _ h3 (eq7_of_minorBound hm) h25

/-- I-0091 at `σ = 19/24`: CONDITIONAL ON `Eq3`, `MinorBoundσ (19/24)` and a (25) with constant `C`,
exceptions `≪ X^{7/12} (log X)^{10}`. -/
theorem main_19_24 (C : ℕ → ℕ → ℝ) (h3 : Eq3) (hm : MinorBoundσ (19 / 24)) (h25 : Eq25C C) :
    ∀ k : ℕ, 1 ≤ k → ∃ B : ℝ, 0 < B ∧ ∀ η : ℝ, 0 < η → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
      ((ExcJC C k X η).card : ℝ) ≤ B * X ^ (7 / 12 : ℝ) * Real.log X ^ 10 := by
  have e : (2 : ℝ) * (19 / 24) - 1 = 7 / 12 := by norm_num
  have := mainJCσ_of_sec5 C h3 (exceptional_of_sup hm) h25
  simpa only [MainJCσ, e] using this

end LeanLab.LPZ2007
