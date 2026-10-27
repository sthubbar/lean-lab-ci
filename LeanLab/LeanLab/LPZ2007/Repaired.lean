/-
P0045 Languasco, Pintz, Zaccagnini 2007, preprint: the REPAIRED reading of (25) and the
Theorem, with the factor `2c0` that F-0038 says the printed (17), (23) dropped.

Why this file: VERIFY U-0999, run 20261019T0202Z-9877, found that the cited `eq25 : Eq25` and
`lpz_main_J : MainJ`, which keep the printed constant `C(k, N)`, are FALSE if F-0038 holds, so
citing them with `sorry` made the module inconsistent. They are now `def`s only, see
Statements.lean, and the cited input is the repaired `eq25_twoC0`.

* `ExcJC`, `Eq25C`, `MainJC`: the Section 5 objects for any constant function `C(k, N)`;
  `Eq25 = Eq25C Ckn`, `MainJ = MainJC Ckn` and `MainJ_twoC0 = MainJC (2c0 · Ckn)` by `rfl`.
* `mainJC_of_sec5`: the Section 5 deduction, (3), (7) and (25) give the Theorem on `J(X)`,
  for every `C`; the proof is the one of `mainJ_of_sec5`, which never uses a property of `C`.
* `lpz_main_J_twoC0`: the repaired Theorem on `J(X)`, CONDITIONAL ON the cited `eq3`, `eq7`
  and the repaired `eq25_twoC0`.

AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.LPZ2007.Elementary

open Finset Real Filter
open scoped ArithmeticFunction.vonMangoldt

namespace LeanLab.LPZ2007

open Classical in
/-- `ExcJ` with a general constant `C(k, N)`. -/
noncomputable def ExcJC (C : ℕ → ℕ → ℝ) (k : ℕ) (X η : ℝ) : Finset ℕ :=
  (Icc 1 ⌊X⌋₊).filter (fun N : ℕ => Even N ∧ InJ X N ∧
    η * N * Lg X ^ k < |Rpp k X N - C k N * N * Lg X ^ k|)

/-- (25) with a general constant `C(k, N)`. -/
def Eq25C (C : ℕ → ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ B η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 0 < η → η < η0 → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
    ∃ P : ℝ, PRange X P ∧ ∀ N : ℕ, Even N → InJ X N →
      ‖RMpp k X P N - C k N * N * Lg X ^ k‖ ≤ B * η * N * Lg X ^ k

/-- The Theorem on `J(X)` with a general constant `C(k, N)`. -/
def MainJC (C : ℕ → ℕ → ℝ) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∃ B : ℝ, 0 < B ∧ ∀ η : ℝ, 0 < η → ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X →
    ((ExcJC C k X η).card : ℝ) ≤ B * X ^ (3 / 5 : ℝ) * Real.log X ^ 10

theorem eq25_iff : Eq25 ↔ Eq25C Ckn := Iff.rfl
theorem mainJ_iff : MainJ ↔ MainJC Ckn := Iff.rfl
theorem mainJ_twoC0_iff : MainJ_twoC0 ↔ MainJC (fun k N => twoC0 * Ckn k N) := Iff.rfl

/-- The repaired (25) p.8: `R''_𝔐(N) = 2c0 C(k, N) N L^k (1 + O(η))`, F-0038. Cited, the
repaired reading, not the printed one. -/
theorem eq25_twoC0 : Eq25C (fun k N => twoC0 * Ckn k N) := by sorry

theorem mainJC_of_sec5 (C : ℕ → ℕ → ℝ) (h3 : Eq3) (h7 : Eq7) (h25 : Eq25C C) : MainJC C := by
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
  have hXp : 0 ≤ X ^ (3 / 5 : ℝ) * Lg X ^ 10 := by positivity
  calc ((ExcJC C k X η).card : ℝ) ≤ B7 * X ^ (3 / 5 : ℝ) * Lg X ^ 10 := hcard.trans h7
    _ ≤ (|B7| + 1) * X ^ (3 / 5 : ℝ) * Lg X ^ 10 := by
        have : B7 ≤ |B7| + 1 := by linarith [le_abs_self B7]
        nlinarith
    _ = (|B7| + 1) / Real.log 2 ^ 10 * X ^ (3 / 5 : ℝ) * Real.log X ^ 10 := by
        rw [hLg]; ring

/-- **The repaired Theorem on `J(X)`**, with the constant `2c0 C(k, N)`: CONDITIONAL ON the
cited `eq3`, `eq7` and the repaired `eq25_twoC0`. -/
theorem lpz_main_J_twoC0 : MainJ_twoC0 :=
  mainJC_of_sec5 (fun k N => twoC0 * Ckn k N) eq3 eq7 eq25_twoC0

/-- The old implication, now through the general form. -/
theorem mainJ_of_sec5' (h3 : Eq3) (h7 : Eq7) (h25 : Eq25) : MainJ :=
  mainJC_of_sec5 Ckn h3 h7 h25

#print axioms LeanLab.LPZ2007.mainJC_of_sec5
#print axioms LeanLab.LPZ2007.mainJ_of_sec5'
#print axioms LeanLab.LPZ2007.lpz_main_J_twoC0

end LeanLab.LPZ2007
