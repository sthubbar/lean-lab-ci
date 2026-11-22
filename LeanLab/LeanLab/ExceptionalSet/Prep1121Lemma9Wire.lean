import LeanLab.ExceptionalSet.Prep1121Trapezoid
import LeanLab.ExceptionalSet.DQLemma10S1
import LeanLab.ExceptionalSet.DQLemma4Decisions
import LeanLab.ExceptionalSet.UpJ200.Decomp539a
import LeanLab.ExceptionalSet.Selberg524

/-!
Prep 2026-11-21, ExceptionalSet route step ES-cited, wiring for `U1539.lemma9`.
P0082, J. Brüdern and A. Perelli, Ann. Inst. Fourier 48 (1998), doi 10.5802/aif.1621,
Lemma 9 page 368, proof page 370.

`DQLemma9Decisions.lemma9_of_theorem2_lemma4` proves `Lemma9` from `Theorem2` and `Lemma4`
but runs through its two open trapezoid LEAF lemmas. `Prep1121Trapezoid` proves both. Existing
files may not be edited, so the three theorems of `DQLemma9Decisions` that sit on those leaves
are restated here, with bodies copied verbatim except that the two leaf names point at the
proved splits. Result: `lemma9_of_theorem2_lemma4_wired` is CONDITIONAL ON `Theorem2` and
`Lemma4` only, no sorry anywhere below it in this chain.
AI wrote the Lean code. Binary Goldbach is open.
-/

/-!
2026-11-22 addition, same file and same unit. The section "Sharp Erdos-Turan from Selberg's
majorant" below discharges the Erdos-Turan input of this file: `Lemma4` is proved from the cited
Karatsuba input alone, through the one-sided Beurling-Selberg majorant of `Selberg524`, and the
single-wall wires `lemma9_of_karacuba` and `parity_gap_of_karacuba` are the result. The earlier
two-wall wires of this file are kept unchanged.
-/

namespace LeanLab.ExceptionalSet.Prep1121Lemma9Wire

open Real Finset Filter
open scoped Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539
open LeanLab.ExceptionalSet.DQLemma9

/-- P0082 page 370 display 40, as `DQLemma9.leaf_trapezoid_fourier_l9`, PROVED from
`Prep1121Trapezoid`. -/
theorem trapezoid_fourier_wired (Δ : ℝ) (hΔ0 : 0 < Δ) (hΔ1 : Δ < 1) :
    ∃ (ψ : ℝ → ℝ) (c : ℤ → ℂ),
      (∀ β : ℝ, 0 ≤ ψ β ∧ ψ β ≤ 1) ∧
      (∀ β : ℝ, 1 / 2 ≤ Int.fract β → ψ β = 0) ∧
      (∀ β : ℝ, Δ / 4 ≤ Int.fract β → Int.fract β ≤ 1 / 2 - Δ / 4 → ψ β = 1) ∧
      (∀ β : ℝ, HasSum (fun h : ℤ => c h * eC (h * β)) (ψ β : ℂ)) ∧
      (∀ h : ℤ, ‖c h‖ ≤ 1 / 2) ∧
      (∀ h : ℤ, h ≠ 0 → ‖c h‖ ≤ 41 / 100 / (Δ * (h : ℝ) ^ 2)) := by
  refine ⟨trapL9 Δ, hcheck (fun t => (trapL9 Δ t : ℂ)), fun β => ?_, fun β hβ => ?_,
    fun β h1 h2 => ?_, Prep1121Trapezoid.trapezoid_series_split Δ hΔ0 hΔ1,
    fun h => (Prep1121Trapezoid.trapezoid_coeff_split Δ hΔ0 hΔ1 h).1,
    fun h => (Prep1121Trapezoid.trapezoid_coeff_split Δ hΔ0 hΔ1 h).2⟩
  · exact ⟨le_max_left _ _, max_le zero_le_one (min_le_left _ _)⟩
  · have h1 : 4 * (1 / 2 - Int.fract β) / Δ ≤ 0 :=
      div_nonpos_of_nonpos_of_nonneg (by linarith) hΔ0.le
    unfold trapL9
    apply max_eq_left
    exact (min_le_right _ _).trans ((min_le_right _ _).trans h1)
  · unfold trapL9
    have ha : 1 ≤ 4 * Int.fract β / Δ := by rw [le_div_iff₀ hΔ0]; linarith
    have hb : 1 ≤ 4 * (1 / 2 - Int.fract β) / Δ := by rw [le_div_iff₀ hΔ0]; linarith
    rw [min_eq_left (le_min ha hb), max_eq_right zero_le_one]

set_option maxHeartbeats 1000000 in
/-- DQ5 leaf A, `leaf_large_value_shift_dq5`, P0082 page 370 displays 40 and 41:
a large even sum `Φ_e(α)` forces a large full sum `Φ(α - h/2)` with `|h| ≤ ℰ^{2/3}`.
CONDITIONAL ON `Lemma4`; no other open input, the trapezoid leaves are proved in Prep1121Trapezoid. -/
theorem large_value_shift_of_lemma4_wired (h4 : Lemma4) :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ α : ℝ, |α| ≤ F γ N ^ δ → N * calE γ κ N ^ (-(1 / 3 : ℝ)) < ‖Phie γ N α‖ →
          ∃ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (2 / 3 : ℝ) ∧
            N * calE γ κ N ^ (-(1 : ℝ)) <
              ‖∑ n ∈ Ioc (N / 2) N, eC ((α - h / 2) * F γ n)‖ := by
  intro γ hγ1 hγ2
  obtain ⟨κ₄, B₄, hκ₄, hL4⟩ := h4 γ hγ1 hγ2
  refine ⟨1, one_pos, fun δ _ _ => ⟨κ₄, hκ₄, fun κ hκ hκκ => ?_⟩⟩
  set B' := |B₄| + 1 with hB'
  have hB'pos : 0 < B' := by positivity
  have hLt := tendsto_L_l9 γ hγ2
  obtain ⟨Na, hNa⟩ := eventually_atTop.mp (hLt.eventually_ge_atTop (3 * Real.log 100 / κ))
  obtain ⟨Nb, hNb⟩ := eventually_atTop.mp
    (hLt.eventually_ge_atTop (Real.log (100 * B') / (2 * κ₄ / 3)))
  obtain ⟨Nc, hNc⟩ := eventually_atTop.mp
    ((tendsto_logpow_l9 γ (by linarith)).eventually_ge_atTop (2 * Real.log 2 + 1))
  refine ⟨max 2 (max Na (max Nb Nc)), fun N hN α _ hbig => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNa' := hNa N (((le_max_left _ _).trans (le_max_right _ _)).trans hN)
  have hNb' := hNb N ((((le_max_left _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans hN)
  have hNc' := hNc N ((((le_max_right _ _).trans (le_max_right _ _)).trans
    (le_max_right _ _)).trans hN)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  set L := Real.log (N : ℝ) ^ (3 - 2 * γ) with hLdef
  have hLnn : 0 ≤ L := Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))) _
  set x := Real.exp (-(κ * L / 3)) with hxdef
  have hx0 : 0 < x := Real.exp_pos _
  have hE13 : calE γ κ N ^ (-(1 / 3 : ℝ)) = x := by
    rw [calE_rpow_l9, hxdef]; congr 1; ring
  have hE1 : calE γ κ N ^ (-(1 : ℝ)) = x ^ 3 := by
    rw [calE_rpow_l9, hxdef, ← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hE23 : calE γ κ N ^ (2 / 3 : ℝ) = 1 / x ^ 2 := by
    rw [calE_rpow_l9, hxdef, ← Real.exp_nat_mul, one_div, ← Real.exp_neg]; congr 1; push_cast; ring
  have hx : x ≤ 1 / 100 := by
    have h1 : Real.log 100 ≤ κ * L / 3 := by
      have := (div_le_iff₀ hκ).mp hNa'
      linarith
    calc x ≤ Real.exp (-Real.log 100) := Real.exp_le_exp.mpr (by linarith)
      _ = 1 / 100 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hEerr : B' * Real.exp (-κ₄ * L) ≤ x / 100 := by
    have h1 : Real.log (100 * B') ≤ 2 * κ₄ / 3 * L := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * κ₄ / 3)).mp hNb'
      linarith
    have h2 : 100 * B' ≤ Real.exp (2 * κ₄ / 3 * L) := by
      calc 100 * B' = Real.exp (Real.log (100 * B')) := (Real.exp_log (by positivity)).symm
        _ ≤ _ := Real.exp_le_exp.mpr h1
    have h3 : Real.exp (-κ₄ * L) * Real.exp (2 * κ₄ / 3 * L) ≤ x := by
      rw [← Real.exp_add, hxdef]
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_right hκκ hLnn
      nlinarith
    have hq := Real.exp_pos (-κ₄ * L)
    nlinarith
  -- the Fourier data
  set Δ := 9 / 5 * x with hΔdef
  have hΔ0 : 0 < Δ := by positivity
  have hΔ1 : Δ < 1 := by rw [hΔdef]; linarith
  obtain ⟨ψ, c, hψ01, hψ0, hψ1, hser, hc0, hc⟩ := trapezoid_fourier_wired Δ hΔ0 hΔ1
  set K := ⌊1 / x ^ 2⌋₊ with hKdef
  have hK : 1 / x ^ 2 - 1 ≤ (K : ℝ) := by
    have := Nat.lt_floor_add_one (1 / x ^ 2); linarith
  have hKle : (K : ℝ) ≤ 1 / x ^ 2 := Nat.floor_le (by positivity)
  -- Lemma 4 count
  have hhalf : F γ N ^ (-(1 / 2 : ℝ)) < |(1 / 2 : ℝ)| := by
    rw [F, ← Real.exp_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    calc Real.exp (Real.log (N : ℝ) ^ γ * (-(1 / 2))) ≤ Real.exp (-(Real.log 2 + 1 / 2)) :=
          Real.exp_le_exp.mpr (by linarith)
      _ < Real.exp (-Real.log 2) := Real.exp_lt_exp.mpr (by linarith)
      _ = 1 / 2 := by rw [Real.exp_neg, Real.exp_log (by norm_num)]; norm_num
  have hcnt := fun z₁ z₂ (h0 : (0 : ℝ) ≤ z₂) (h1 : z₂ < z₁) (h2 : z₁ ≤ 1) =>
    hL4 N (by omega) (1 / 2) hhalf (by norm_num) z₁ z₂ h0 h1 h2
  set E := Real.exp (-κ₄ * Real.log N ^ (3 - 2 * γ)) with hEdef
  have hc1 := hcnt (Δ / 4) 0 le_rfl (by positivity) (by linarith)
  have hc2 := hcnt (1 / 2) (1 / 2 - Δ / 4) (by linarith) (by linarith) (by norm_num)
  have hB4 : B₄ * N * E ≤ N * (B' * E) := by
    have : B₄ ≤ B' := by rw [hB']; linarith [le_abs_self B₄]
    have hE0 : 0 ≤ E := (Real.exp_pos _).le
    calc B₄ * N * E = B₄ * (N * E) := by ring
      _ ≤ B' * (N * E) := mul_le_mul_of_nonneg_right this (mul_nonneg hNpos.le hE0)
      _ = N * (B' * E) := by ring
  have hbad : (((Ioc (N / 2) N).filter (fun n : ℕ =>
        (0 ≤ Int.fract (1 / 2 * F γ n) ∧ Int.fract (1 / 2 * F γ n) < Δ / 4) ∨
        (1 / 2 - Δ / 4 ≤ Int.fract (1 / 2 * F γ n) ∧ Int.fract (1 / 2 * F γ n) < 1 / 2))).card
        : ℝ) ≤ N * (9 / 5 * x) / 4 + 2 * N * (B' * E) := by
    rw [Finset.filter_or]
    have hu := Finset.card_union_le
      ((Ioc (N / 2) N).filter (fun n : ℕ =>
        0 ≤ Int.fract (1 / 2 * F γ n) ∧ Int.fract (1 / 2 * F γ n) < Δ / 4))
      ((Ioc (N / 2) N).filter (fun n : ℕ =>
        1 / 2 - Δ / 4 ≤ Int.fract (1 / 2 * F γ n) ∧ Int.fract (1 / 2 * F γ n) < 1 / 2))
    have hu' : (((Ioc (N / 2) N).filter (fun n : ℕ =>
        0 ≤ Int.fract (1 / 2 * F γ n) ∧ Int.fract (1 / 2 * F γ n) < Δ / 4) ∪
      (Ioc (N / 2) N).filter (fun n : ℕ =>
        1 / 2 - Δ / 4 ≤ Int.fract (1 / 2 * F γ n) ∧ Int.fract (1 / 2 * F γ n) < 1 / 2)).card
        : ℝ) ≤ (((Ioc (N / 2) N).filter (fun n : ℕ =>
        0 ≤ Int.fract (1 / 2 * F γ n) ∧ Int.fract (1 / 2 * F γ n) < Δ / 4)).card : ℝ) +
      (((Ioc (N / 2) N).filter (fun n : ℕ =>
        1 / 2 - Δ / 4 ≤ Int.fract (1 / 2 * F γ n) ∧ Int.fract (1 / 2 * F γ n) < 1 / 2)).card
        : ℝ) := by exact_mod_cast hu
    refine hu'.trans ?_
    rw [abs_le] at hc1 hc2
    rw [hΔdef] at hc1 hc2 ⊢
    nlinarith [hc1.2, hc2.2]
  -- the contrapositive
  by_contra hno
  push_neg at hno
  have hsmall : ∀ h : ℤ, |h| ≤ (K : ℤ) →
      ‖∑ n ∈ Ioc (N / 2) N, eC ((α + h / 2) * F γ n)‖ ≤ N * x ^ 3 := by
    intro h hh
    have hh' : (|((-h : ℤ) : ℝ)|) ≤ calE γ κ N ^ (2 / 3 : ℝ) := by
      rw [hE23]
      refine le_trans ?_ hKle
      push_cast
      rw [abs_neg, ← Int.cast_abs]
      exact_mod_cast hh
    have := hno (-h) hh'
    rw [hE1] at this
    convert this using 4
    push_cast; ring
  have hT := expansion_l9 γ N α ψ c hser
  have htr := truncated_l9 γ N α Δ hΔ0 c _ hT hc0 hc K (N * x ^ 3) hsmall
  have hsm := smoothing_l9 γ N α Δ ψ hψ01 hψ0 hψ1
  have hnum := numeric_l9 N x K (B' * E) hNpos.le hx0 hx hK (by rw [hEdef]; exact hEerr)
  have htot : ‖Phie γ N α‖ ≤ 95 / 100 * (N * x) := by
    calc ‖Phie γ N α‖ ≤ ‖Phie γ N α - ∑ n ∈ Ioc (N / 2) N,
            (ψ (1 / 2 * F γ n) : ℂ) * eC (α * F γ n)‖ +
          ‖∑ n ∈ Ioc (N / 2) N, (ψ (1 / 2 * F γ n) : ℂ) * eC (α * F γ n)‖ := norm_le_norm_sub_add _ _
      _ ≤ _ := by rw [hΔdef] at htr hsm; linarith
  rw [hE13] at hbig
  have hNx : 0 < N * x := by positivity
  linarith

/-! ### Lemma 9 -/


/-- `Lemma9`, P0082 page 368, by the page 370 proof. CONDITIONAL ON `Theorem2` and
`Lemma4`; no other open input. The type is
exactly the sealed `Lemma9` of State1539Data264. -/
theorem lemma9_of_theorem2_lemma4_wired (hT : Theorem2) (h4 : Lemma4) : Lemma9 := by
  intro γ hγ₁ hγ₂
  obtain ⟨δ₀, hδ₀, hA⟩ := large_value_shift_of_lemma4_wired h4 γ hγ₁ hγ₂
  refine ⟨min δ₀ (γ - 1), lt_min hδ₀ (by linarith), fun δ hδ hδlt => ?_⟩
  have hδA : δ < δ₀ := lt_of_lt_of_le hδlt (min_le_left _ _)
  have hδB : δ < γ - 1 := lt_of_lt_of_le hδlt (min_le_right _ _)
  obtain ⟨κ₀, hκ₀, hA⟩ := hA δ hδ hδA
  obtain ⟨κ₁, hκ₁, hB⟩ := shift_minor_of_theorem2 hT γ hγ₁ hγ₂ δ hδ hδB
  set κ := min κ₀ κ₁
  have hκ : 0 < κ := lt_min hκ₀ hκ₁
  obtain ⟨NA, hNA⟩ := hA κ hκ (min_le_left _ _)
  obtain ⟨NB, hNB⟩ := hB κ hκ (min_le_right _ _)
  obtain ⟨NH, hNH⟩ := height_below_window_l9 γ hγ₁ δ κ hδ
  refine ⟨κ, hκ, max NA (max NB NH), fun N hN α hα hlarge => ?_⟩
  have hNA' : NA ≤ N := (le_max_left _ _).trans hN
  have hNB' : NB ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNH' : NH ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  obtain ⟨h, hh, hbig⟩ := hNA N hNA' α hα hlarge
  refine ⟨h, hh, ?_⟩
  by_contra hfar
  rw [not_le] at hfar
  have hheight := hNH N hNH'
  have hFpos : 0 < F γ N ^ δ := Real.rpow_pos_of_pos (Real.exp_pos _) δ
  have hhalf : |(h : ℝ) / 2| ≤ F γ N ^ δ + 1 := by
    rw [abs_div, abs_two]
    linarith
  have hwin : |α - h / 2| ≤ 2 * F γ N ^ δ + 2 := by
    calc |α - h / 2| ≤ |α| + |(h : ℝ) / 2| := abs_sub _ _
      _ ≤ 2 * F γ N ^ δ + 2 := by linarith
  have hsmall := hNB N hNB' (α - h / 2) hfar hwin
  linarith

/-- `Lemma9` from Karacuba's `Lemma10` and `Lemma4`. CONDITIONAL ON `Lemma10` and `Lemma4`. -/
theorem lemma9_of_lemma10_lemma4_wired (h10 : Lemma10) (h4 : Lemma4) : Lemma9 :=
  lemma9_of_theorem2_lemma4_wired (theorem2_of_all_leaves h10) h4

/-- `Lemma9` from the two citation walls of the route: Karacuba 1971 Theorem 1, the named
`KaracubaThm1Named`, and the Erdős–Turán inequality, the named `ErdosTuranDQ4` that stands for
P0082 page 359's "standard argument of Vinogradov". CONDITIONAL ON those two named
hypotheses only. -/
theorem lemma9_of_karacuba_erdosTuran
    (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named)
    (hET : LeanLab.ExceptionalSet.DQLemma4.ErdosTuranDQ4) : Lemma9 :=
  lemma9_of_theorem2_lemma4_wired (LeanLab.ExceptionalSet.U1539.DQLemma10.theorem2_of_karacuba_named hK)
    (LeanLab.ExceptionalSet.DQLemma4.lemma4_of_erdosTuran_theorem2 hET
      (LeanLab.ExceptionalSet.U1539.DQLemma10.theorem2_of_karacuba_named hK))

#print axioms lemma9_of_theorem2_lemma4_wired
#print axioms lemma9_of_karacuba_erdosTuran

/-- P0082 pages 368 to 369. Both parity phases localize at half integers,
CONDITIONAL ON the named Karacuba and Erdos-Turan citation walls only. -/
theorem parity_gap_of_karacuba_erdosTuran
    (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named)
    (hET : LeanLab.ExceptionalSet.DQLemma4.ErdosTuranDQ4)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ j : ℤ, (j = 0 ∨ j = 1) →
          ∀ t : ℝ, |t| ≤ F γ N ^ δ →
            N * calE γ κ N ^ (-(5 / 6 : ℝ)) <
              ‖LeanLab.ExceptionalSet.UpJ200.Decomp539a.parityPhase γ N j t‖ →
            ∃ h : ℤ, |t - h / 2| ≤ F γ N ^ (δ - 1) := by
  have h9 := lemma9_of_karacuba_erdosTuran hK hET
  have h10 := LeanLab.ExceptionalSet.U1539.DQLemma10.lemma10_of_karacuba_named hK
  exact LeanLab.ExceptionalSet.UpJ200.Decomp539a.parity_gap_of_inputs h9 h10 γ h1 h2

#print axioms parity_gap_of_karacuba_erdosTuran

/-! ### Sharp Erdős–Turán from Selberg's majorant

The Selberg-majorant machinery of `SPLIT_lemma4`, restated with the true weight `‖S_h‖ / h`
(the split multiplies that sum by the point count, costing a factor `N`). -/

private theorem et_eC_add (a b : ℝ) : eC (a + b) = eC a * eC b := by
  unfold eC
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem et_eC_intCast (k : ℤ) : eC (k : ℝ) = 1 := by
  unfold eC
  have h : 2 * Real.pi * Complex.I * (k : ℝ) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
    push_cast
    ring
  rw [h, Complex.exp_int_mul_two_pi_mul_I]

private theorem et_eC_frac (h : ℕ) (y : ℝ) : eC ((h : ℝ) * Int.fract y) = eC ((h : ℝ) * y) := by
  have hfr : Int.fract y = y - (⌊y⌋ : ℝ) := (Int.self_sub_floor y).symm
  rw [hfr]
  have hsplit : (h : ℝ) * (y - (⌊y⌋ : ℝ)) = (h : ℝ) * y + (-(((h : ℤ) * ⌊y⌋ : ℤ)) : ℝ) := by
    push_cast
    ring
  rw [hsplit, et_eC_add,
    show (-(((h : ℤ) * ⌊y⌋ : ℤ)) : ℝ) = (((-((h : ℤ) * ⌊y⌋)) : ℤ) : ℝ) by push_cast; ring,
    et_eC_intCast, mul_one]

private theorem et_cos_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ) :
    |∑ n ∈ s, Real.cos (2 * Real.pi * f n)| ≤ ‖∑ n ∈ s, eC (f n)‖ := by
  have hpt : ∀ n : ι, (eC (f n)).re = Real.cos (2 * Real.pi * f n) := by
    intro n
    unfold eC
    rw [Complex.exp_re]
    have hre : (2 * Real.pi * Complex.I * (f n : ℂ)).re = 0 := by
      simp [Complex.mul_re, Complex.mul_im]
    have him : (2 * Real.pi * Complex.I * (f n : ℂ)).im = 2 * Real.pi * f n := by
      simp [Complex.mul_re, Complex.mul_im]
    rw [hre, him, Real.exp_zero, one_mul]
  have h1 : ∑ n ∈ s, Real.cos (2 * Real.pi * f n) = (∑ n ∈ s, eC (f n)).re := by
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun n _ => (hpt n).symm
  rw [h1]
  exact Complex.abs_re_le_norm _

/-- `cos (2π h (θ - k)) = cos (2π h θ)` for `k : ℤ`. -/
private theorem et_cos_sub_intCast (h : ℕ) (θ : ℝ) (k : ℤ) :
    Real.cos (2 * Real.pi * ((h : ℝ) * (θ - (k : ℝ)))) =
      Real.cos (2 * Real.pi * ((h : ℝ) * θ)) := by
  have harg : 2 * Real.pi * ((h : ℝ) * (θ - (k : ℝ)))
      = 2 * Real.pi * ((h : ℝ) * θ) - (((h : ℤ) * k : ℤ) : ℝ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [harg, Real.cos_sub_int_mul_two_pi]

/-- The majorant sum factors out of the point sum. -/
private theorem et_sum_majorant_eq {ι : Type*} (s : Finset ι) (v : ι → ℝ) (m : ℝ) (g : ℕ → ℝ)
    (H : ℕ) :
    ∑ i ∈ s, (m + ∑ h ∈ Finset.Icc 1 H, g h * Real.cos (2 * Real.pi * ((h : ℝ) * v i))) =
      (s.card : ℝ) * m +
        ∑ h ∈ Finset.Icc 1 H, g h * ∑ i ∈ s, Real.cos (2 * Real.pi * ((h : ℝ) * v i)) := by
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.sum_comm]
  congr 1
  exact Finset.sum_congr rfl fun h _ => by rw [Finset.mul_sum]

/-- Rotating the points multiplies the exponential sum by a unit, so the norms agree. -/
private theorem et_norm_rot {ι : Type*} (s : Finset ι) (x : ι → ℝ) (h : ℕ) (c : ℝ) :
    ‖∑ i ∈ s, eC ((h : ℝ) * (x i - c))‖ = ‖∑ i ∈ s, eC ((h : ℝ) * x i)‖ := by
  have hpt : ∀ i : ι, eC ((h : ℝ) * (x i - c))
      = eC ((h : ℝ) * x i) * eC ((h : ℝ) * (-c)) := by
    intro i
    rw [← et_eC_add]
    congr 1
    ring
  rw [Finset.sum_congr rfl fun i _ => hpt i, ← Finset.sum_mul, norm_mul,
    norm_eC, mul_one]

/-- **Erdős–Turán, upper half.**  A subset of the points that lies in the arc
`|x - c| ≤ w/2` (mod 1) is counted by the majorant's mean plus the coefficients against the
exponential sums. -/
private theorem et_majorant_upper {ι : Type*} (s t : Finset ι) (x : ι → ℝ) (m : ℝ) (g : ℕ → ℝ)
    (H : ℕ) (c w : ℝ) (hw : 0 < w) (hg0 : ∀ h ∈ Finset.Icc 1 H, |g h| ≤ 4 / (h : ℝ))
    (hnn : ∀ θ, 0 ≤ m + ∑ h ∈ Finset.Icc 1 H, g h * Real.cos (2 * Real.pi * ((h : ℝ) * θ)))
    (hmaj : ∀ θ, |θ| ≤ w / 2 →
      1 ≤ m + ∑ h ∈ Finset.Icc 1 H, g h * Real.cos (2 * Real.pi * ((h : ℝ) * θ)))
    (hts : t ⊆ s)
    (harc : ∀ i ∈ t, ∃ k : ℤ, |x i - c - (k : ℝ)| ≤ w / 2) :
    (t.card : ℝ) ≤ (s.card : ℝ) * m +
      ∑ h ∈ Finset.Icc 1 H, (4 / (h : ℝ)) * ‖∑ i ∈ s, eC ((h : ℝ) * x i)‖ := by
  classical
  have hone : ∀ i ∈ t, 1 ≤ m + ∑ h ∈ Finset.Icc 1 H,
      g h * Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c))) := by
    intro i hi
    obtain ⟨k, hk⟩ := harc i hi
    have hper : (∑ h ∈ Finset.Icc 1 H,
        g h * Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c - (k : ℝ)))))
        = ∑ h ∈ Finset.Icc 1 H,
          g h * Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c))) := by
      refine Finset.sum_congr rfl fun h _ => ?_
      rw [et_cos_sub_intCast h (x i - c) k]
    rw [← hper]
    exact hmaj _ hk
  have hstep : (t.card : ℝ) ≤ ∑ i ∈ s,
      (m + ∑ h ∈ Finset.Icc 1 H, g h * Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))) := by
    calc (t.card : ℝ) = ∑ i ∈ t, (1 : ℝ) := by simp
      _ ≤ ∑ i ∈ t, (m + ∑ h ∈ Finset.Icc 1 H,
            g h * Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))) :=
          Finset.sum_le_sum fun i hi => hone i hi
      _ ≤ ∑ i ∈ s, (m + ∑ h ∈ Finset.Icc 1 H,
            g h * Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))) :=
          Finset.sum_le_sum_of_subset_of_nonneg hts (fun i _ _ => hnn _)
  have hsquare : ∑ h ∈ Finset.Icc 1 H,
      g h * ∑ i ∈ s, Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))
      ≤ ∑ h ∈ Finset.Icc 1 H, (4 / (h : ℝ)) * ‖∑ i ∈ s, eC ((h : ℝ) * x i)‖ := by
    refine Finset.sum_le_sum fun h hh => ?_
    have hcos : |∑ i ∈ s, Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))| ≤
        ‖∑ i ∈ s, eC ((h : ℝ) * x i)‖ := by
      have h1 := et_cos_sum_le s (fun i => (h : ℝ) * (x i - c))
      have h2 : ‖∑ i ∈ s, eC ((h : ℝ) * (x i - c))‖ = ‖∑ i ∈ s, eC ((h : ℝ) * x i)‖ :=
        et_norm_rot s x h c
      rw [h2] at h1
      exact h1
    have h2 : g h * ∑ i ∈ s, Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))
        ≤ |g h| * |∑ i ∈ s, Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))| := by
      calc g h * ∑ i ∈ s, Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))
          ≤ |g h * ∑ i ∈ s, Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))| :=
            le_abs_self _
        _ = |g h| * |∑ i ∈ s, Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))| :=
            abs_mul _ _
    refine h2.trans ?_
    calc |g h| * |∑ i ∈ s, Real.cos (2 * Real.pi * ((h : ℝ) * (x i - c)))|
        ≤ (4 / (h : ℝ)) * ‖∑ i ∈ s, eC ((h : ℝ) * x i)‖ :=
          mul_le_mul (hg0 h hh) hcos (abs_nonneg _) (by
            have : (0 : ℝ) ≤ 4 / (h : ℝ) := by
              have h1 : (1 : ℝ) ≤ (h : ℝ) := by exact_mod_cast (Finset.mem_Icc.mp hh).1
              positivity
            exact this)
      _ = (4 / (h : ℝ)) * ‖∑ i ∈ s, eC ((h : ℝ) * x i)‖ := rfl
  rw [et_sum_majorant_eq s (fun i => x i - c) m g H] at hstep
  linarith

/-! ### Arc facts for the point count -/

private theorem et_arc_main {z₁ z₂ x : ℝ} (h1 : z₂ ≤ x) (h2 : x < z₁) :
    |x - (z₂ + z₁) / 2| ≤ (z₁ - z₂) / 2 := by
  rw [abs_le]
  constructor <;> linarith

private theorem et_arc_high {z₁ z₂ x : ℝ} (hz₂ : 0 ≤ z₂) (h2 : z₁ ≤ x) (h3 : x ≤ 1) :
    |x - ((z₂ + z₁) / 2 + 1 / 2)| ≤ (1 - (z₁ - z₂)) / 2 := by
  rw [abs_le]
  constructor <;> linarith

private theorem et_arc_low {z₁ z₂ x : ℝ} (hz₁ : z₁ ≤ 1) (h1 : 0 ≤ x) (h2 : x < z₂) :
    |x - ((z₂ + z₁) / 2 + 1 / 2) + 1| ≤ (1 - (z₁ - z₂)) / 2 := by
  rw [abs_le]
  constructor <;> linarith

private theorem et_card_Ioc (N : ℕ) : (Finset.Ioc (N / 2) N).card = N - N / 2 :=
  Nat.card_Ioc ..

private theorem et_parity (N : ℕ) :
    |(((Finset.Ioc (N / 2) N).card : ℕ) : ℝ) - (N : ℝ) / 2| ≤ 1 / 2 := by
  have hcard : (Finset.Ioc (N / 2) N).card = N - N / 2 := et_card_Ioc N
  have hdec : (N : ℝ) = 2 * ((N / 2 : ℕ) : ℝ) + ((N % 2 : ℕ) : ℝ) := by
    have h : 2 * (N / 2) + N % 2 = N := Nat.div_add_mod N 2
    have hcast : ((2 * (N / 2) + N % 2 : ℕ) : ℝ) = (N : ℝ) := by rw [h]
    push_cast at hcast
    linarith
  have hmod : ((N % 2 : ℕ) : ℝ) = 0 ∨ ((N % 2 : ℕ) : ℝ) = 1 := by
    rcases Nat.mod_two_eq_zero_or_one N with h | h
    · left; rw [h]; norm_num
    · right; rw [h]; norm_num
  rw [hcard]
  rw [show ((N - N / 2 : ℕ) : ℝ) = (N : ℝ) - ((N / 2 : ℕ) : ℝ) by
    rw [Nat.cast_sub (Nat.div_le_self N 2)]]
  have hrew : (N : ℝ) - ((N / 2 : ℕ) : ℝ) - (N : ℝ) / 2
      = (2 * ((N : ℝ) - ((N / 2 : ℕ) : ℝ)) - (N : ℝ)) / 2 := by ring
  rw [hrew, abs_div]
  have hkey : 2 * ((N : ℝ) - ((N / 2 : ℕ) : ℝ)) - (N : ℝ) = (((N % 2 : ℕ)) : ℝ) := by
    rw [hdec]; ring
  rw [hkey]
  rcases hmod with h | h <;> rw [h] <;> norm_num

/-! ### Erdős–Turán for the interval indicator, from Selberg's majorant -/

set_option maxHeartbeats 4000000 in
/-- **Erdős–Turán in the sharp form.**  The count in an interval is compared with `w` times the
*number of points* `M` (not with `w N/2`), and the exponential sums enter with the weight
`1/h`, not with `M/(h+1)`: the factor `M` of `SPLIT_lemma4` is what makes its absorption step
unprovable.  Valid for `M ≥ 2`. -/
private theorem et_card_raw (γ α z₁ z₂ : ℝ) (N H : ℕ)
    (hz₂ : 0 ≤ z₂) (hz1 : z₂ < z₁) (hz₁ : z₁ ≤ 1)
    (hM2 : 2 ≤ (Finset.Ioc (N / 2) N).card) :
    |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
        z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
      - (z₁ - z₂) * ((Finset.Ioc (N / 2) N).card : ℝ)| ≤
    4 * ((Finset.Ioc (N / 2) N).card : ℝ) / ((H : ℝ) + 1) +
      4 * ∑ h ∈ Finset.Icc 1 H,
          ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / (h : ℝ) := by
  classical
  set s : Finset ℕ := Finset.Ioc (N / 2) N with hs
  set w : ℝ := z₁ - z₂ with hwdef
  set A : ℝ := 4 / ((H : ℝ) + 1) with hAdef
  set Sn : ℕ → ℝ := fun h => ‖∑ n ∈ s, eC (h * α * F γ n)‖ with hSn
  set Sg : ℝ := ∑ h ∈ Finset.Icc 1 H, Sn h / (h : ℝ) with hSg
  set Cc : ℝ := ((s.filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
      Int.fract (α * F γ n) < z₁)).card : ℝ) with hCc
  set Mc : ℝ := (s.card : ℝ) with hMc
  have hMc2 : (2 : ℝ) ≤ Mc := by rw [hMc]; exact_mod_cast hM2
  have hMc0 : (0 : ℝ) ≤ Mc := by linarith
  have hw0 : 0 < w := by rw [hwdef]; linarith
  have hw1 : w ≤ 1 := by rw [hwdef]; linarith
  have hApos : 0 < A := by rw [hAdef]; positivity
  have hSg0 : 0 ≤ Sg := by
    rw [hSg]
    exact Finset.sum_nonneg fun h _ => div_nonneg (by rw [hSn]; positivity) (by positivity)
  have hCc0 : 0 ≤ Cc := by rw [hCc]; positivity
  have hCcM : Cc ≤ Mc := by
    rw [hCc, hMc]
    exact_mod_cast Finset.card_filter_le (p := fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
      Int.fract (α * F γ n) < z₁) s
  -- the exact weight identity `∑ 4 S_h / h = 4 Sg`
  have hconv : ∑ h ∈ Finset.Icc 1 H, (4 / (h : ℝ)) * Sn h = 4 * Sg := by
    rw [hSg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun h _ => ?_
    ring
  have hMAtarget : 4 * Mc / ((H : ℝ) + 1) = Mc * A := by rw [hAdef]; ring
  -- upper bound
  have hU : Cc - w * Mc ≤ Mc * A + 4 * Sg := by
    rcases lt_or_ge w (1 - A) with hlt | hge
    · have hwA : w + A < 1 := by linarith
      obtain ⟨m, g, hm, hg, hmaj⟩ :=
        LeanLab.ExceptionalSet.Selberg524.selberg_cosine_majorant524 w H hw0 hwA
      have hnn : ∀ θ : ℝ, 0 ≤ m + ∑ h ∈ Finset.Icc 1 H,
          g h * Real.cos (2 * Real.pi * ((h : ℝ) * θ)) := fun θ =>
        le_trans (by split_ifs <;> norm_num) (hmaj θ)
      have hmaj' : ∀ θ : ℝ, |θ| ≤ w / 2 → 1 ≤ m + ∑ h ∈ Finset.Icc 1 H,
          g h * Real.cos (2 * Real.pi * ((h : ℝ) * θ)) := by
        intro θ hθ
        have h := hmaj θ
        rwa [if_pos hθ] at h
      have hsub1 : (s.filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
            Int.fract (α * F γ n) < z₁)) ⊆
          s.filter (fun n : ℕ => |Int.fract (α * F γ n) - (z₂ + z₁) / 2| ≤ w / 2) := by
        intro n hn
        simp only [Finset.mem_filter] at hn ⊢
        exact ⟨hn.1, by rw [hwdef]; exact et_arc_main hn.2.1 hn.2.2⟩
      have harc1 : ∀ n ∈ s.filter (fun n : ℕ =>
            |Int.fract (α * F γ n) - (z₂ + z₁) / 2| ≤ w / 2),
          ∃ k : ℤ, |Int.fract (α * F γ n) - (z₂ + z₁) / 2 - (k : ℝ)| ≤ w / 2 := by
        intro n hn
        simp only [Finset.mem_filter] at hn
        exact ⟨0, by simpa using hn.2⟩
      have hmain1 := et_majorant_upper s (s.filter (fun n : ℕ =>
          |Int.fract (α * F γ n) - (z₂ + z₁) / 2| ≤ w / 2))
        (fun n => Int.fract (α * F γ n)) m g H ((z₂ + z₁) / 2) w hw0 hg hnn hmaj'
        (Finset.filter_subset _ _) harc1
      have hsumid : ∀ h : ℕ, ‖∑ n ∈ s, eC ((h : ℝ) * Int.fract (α * F γ n))‖ = Sn h := by
        intro h
        rw [hSn]
        congr 1
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [et_eC_frac h (α * F γ n)]
        congr 1
        ring
      have hCt : Cc ≤ ((s.filter (fun n : ℕ =>
          |Int.fract (α * F γ n) - (z₂ + z₁) / 2| ≤ w / 2)).card : ℝ) := by
        rw [hCc]
        exact_mod_cast Finset.card_le_card hsub1
      have hsum_eq : ∑ h ∈ Finset.Icc 1 H,
            (4 / (h : ℝ)) * ‖∑ i ∈ s, eC ((h : ℝ) * Int.fract (α * F γ i))‖
          = ∑ h ∈ Finset.Icc 1 H, (4 / (h : ℝ)) * Sn h :=
        Finset.sum_congr rfl fun h _ => by rw [hsumid h]
      have hstep : Cc ≤ Mc * m + ∑ h ∈ Finset.Icc 1 H, (4 / (h : ℝ)) * Sn h := by
        refine hCt.trans ?_
        refine hmain1.trans ?_
        rw [hMc, hsum_eq]
      have hb1 : Mc * m ≤ Mc * (w + A) := by
        refine mul_le_mul_of_nonneg_left ?_ hMc0
        have : 4 / ((H : ℝ) + 1) = A := hAdef.symm
        rw [← this]; exact hm
      nlinarith [hstep, hconv, hb1]
    · nlinarith [hCcM, hge, hMc0]
  -- lower bound
  have hL : w * Mc - Cc ≤ Mc * A + 4 * Sg := by
    rcases eq_or_lt_of_le hw1 with hwEq | hwlt
    · have hws : z₁ - z₂ = 1 := by rw [← hwdef]; exact hwEq
      have hz2 : z₂ = 0 := by linarith
      have hz1' : z₁ = 1 := by linarith
      have hf : s.filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
          Int.fract (α * F γ n) < z₁) = s := by
        refine Finset.filter_true_of_mem ?_
        intro n _
        exact ⟨by rw [hz2]; exact Int.fract_nonneg _, by rw [hz1']; exact Int.fract_lt_one _⟩
      have hCeq : Cc = Mc := by rw [hCc, hMc, hf]
      rw [hwEq, hCeq]
      nlinarith [hApos, hMc0, hSg0]
    · rcases le_or_gt w A with hle | hgt
      · nlinarith [hCc0, hle, hMc0]
      · have hwA' : (1 - w) + A < 1 := by linarith
        obtain ⟨m', g', hm', hg', hmaj'⟩ :=
          LeanLab.ExceptionalSet.Selberg524.selberg_cosine_majorant524 (1 - w) H
            (by linarith) hwA'
        have hnn' : ∀ θ : ℝ, 0 ≤ m' + ∑ h ∈ Finset.Icc 1 H,
            g' h * Real.cos (2 * Real.pi * ((h : ℝ) * θ)) := fun θ =>
          le_trans (by split_ifs <;> norm_num) (hmaj' θ)
        have hmaj'' : ∀ θ : ℝ, |θ| ≤ (1 - w) / 2 → 1 ≤ m' + ∑ h ∈ Finset.Icc 1 H,
            g' h * Real.cos (2 * Real.pi * ((h : ℝ) * θ)) := by
          intro θ hθ
          have h := hmaj' θ
          rwa [if_pos hθ] at h
        have hsub2 : (s.filter (fun n : ℕ =>
              ¬(z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁))) ⊆
            s.filter (fun n : ℕ =>
              |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2)| ≤ (1 - w) / 2 ∨
              |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2) + 1| ≤ (1 - w) / 2) := by
          intro n hn
          simp only [Finset.mem_filter] at hn ⊢
          obtain ⟨hns, hnot⟩ := hn
          have hx0 : (0 : ℝ) ≤ Int.fract (α * F γ n) := Int.fract_nonneg _
          have hx1 : Int.fract (α * F γ n) < 1 := Int.fract_lt_one _
          rcases lt_or_ge (Int.fract (α * F γ n)) z₂ with hlo | hhi
          · exact ⟨hns, Or.inr (by rw [hwdef]; exact et_arc_low hz₁ hx0 hlo)⟩
          · have hz₁x : z₁ ≤ Int.fract (α * F γ n) := by
              rcases lt_or_ge (Int.fract (α * F γ n)) z₁ with h' | h'
              · exact absurd ⟨hhi, h'⟩ hnot
              · exact h'
            exact ⟨hns, Or.inl (by rw [hwdef]; exact et_arc_high hz₂ hz₁x hx1.le)⟩
        have harc2 : ∀ n ∈ s.filter (fun n : ℕ =>
              |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2)| ≤ (1 - w) / 2 ∨
              |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2) + 1| ≤ (1 - w) / 2),
            ∃ k : ℤ, |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2) - (k : ℝ)| ≤
              (1 - w) / 2 := by
          intro n hn
          simp only [Finset.mem_filter] at hn
          rcases hn.2 with h | h
          · exact ⟨0, by simpa using h⟩
          · exact ⟨-1, by push_cast; simpa using h⟩
        have hmain2 := et_majorant_upper s (s.filter (fun n : ℕ =>
            |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2)| ≤ (1 - w) / 2 ∨
            |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2) + 1| ≤ (1 - w) / 2))
          (fun n => Int.fract (α * F γ n)) m' g' H ((z₂ + z₁) / 2 + 1 / 2) (1 - w)
          (by linarith) hg' hnn' hmaj'' (Finset.filter_subset _ _) harc2
        have hsumid : ∀ h : ℕ, ‖∑ n ∈ s, eC ((h : ℝ) * Int.fract (α * F γ n))‖ = Sn h := by
          intro h
          rw [hSn]
          congr 1
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [et_eC_frac h (α * F γ n)]
          congr 1
          ring
        have hcompl : Mc - Cc = ((s.filter (fun n : ℕ =>
            ¬(z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁))).card : ℝ) := by
          have h1 : s.filter (fun n : ℕ => ¬(z₂ ≤ Int.fract (α * F γ n) ∧
              Int.fract (α * F γ n) < z₁))
              = s \ s.filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
                Int.fract (α * F γ n) < z₁) := by
            ext n
            simp only [Finset.mem_filter, Finset.mem_sdiff]
            tauto
          have h2 : ((s \ s.filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
              Int.fract (α * F γ n) < z₁)).card : ℝ)
              = (s.card : ℝ) - ((s.filter (fun n : ℕ => z₂ ≤ Int.fract (α * F γ n) ∧
                Int.fract (α * F γ n) < z₁)).card : ℝ) := by
            rw [Finset.card_sdiff,
              Finset.inter_eq_left.mpr (Finset.filter_subset (p := fun n : ℕ =>
                z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁) s),
              Nat.cast_sub (Finset.card_le_card (Finset.filter_subset (p := fun n : ℕ =>
                z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁) s))]
          rw [h1, h2, hMc, hCc]
        have hcard2 : ((s.filter (fun n : ℕ =>
              ¬(z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁))).card : ℝ)
            ≤ ((s.filter (fun n : ℕ =>
              |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2)| ≤ (1 - w) / 2 ∨
              |Int.fract (α * F γ n) - ((z₂ + z₁) / 2 + 1 / 2) + 1| ≤ (1 - w) / 2)).card : ℝ) :=
          by exact_mod_cast Finset.card_le_card hsub2
        have hsum_eq : ∑ h ∈ Finset.Icc 1 H,
              (4 / (h : ℝ)) * ‖∑ i ∈ s, eC ((h : ℝ) * Int.fract (α * F γ i))‖
            = ∑ h ∈ Finset.Icc 1 H, (4 / (h : ℝ)) * Sn h :=
          Finset.sum_congr rfl fun h _ => by rw [hsumid h]
        have hstep2 : Mc - Cc ≤ Mc * m' + ∑ h ∈ Finset.Icc 1 H, (4 / (h : ℝ)) * Sn h := by
          rw [hcompl]
          refine le_trans hcard2 ?_
          refine hmain2.trans ?_
          rw [hMc, hsum_eq]
        have hb1 : Mc * m' ≤ Mc * ((1 - w) + A) := by
          refine mul_le_mul_of_nonneg_left ?_ hMc0
          have : 4 / ((H : ℝ) + 1) = A := hAdef.symm
          rw [← this]; exact hm'
        have hMA2 : Mc * ((1 - w) + A) = Mc - w * Mc + Mc * A := by ring
        nlinarith [hstep2, hconv, hb1, hMA2]
  rw [abs_le, hMAtarget]
  constructor <;> linarith

/-! ### Sharp count, exp domination, and the Karacuba input -/

/-- `exp` beats every affine function: the engine of the absorption step. -/
private theorem exp_dom_lin (c K : ℝ) (hc : 0 < c) (hK : 0 ≤ K) :
    ∃ T : ℝ, ∀ x : ℝ, T ≤ x → K * (1 + x) ≤ Real.exp (c * x) := by
  have hc2 : (0 : ℝ) < c ^ 2 := by positivity
  refine ⟨max 1 (max (8 * K / c ^ 2) (2 * Real.sqrt K / c + 1)), fun x hx => ?_⟩
  have hx1 : (1 : ℝ) ≤ x := (le_max_left _ _).trans hx
  have hx2 : 8 * K / c ^ 2 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hx
  have hx0 : (0 : ℝ) < x := lt_of_lt_of_le one_pos hx1
  have hexp : c ^ 2 * x ^ 2 / 4 ≤ Real.exp (c * x) := by
    have hsq : Real.exp (c * x) = (Real.exp (c * x / 2)) ^ 2 := by
      rw [show c * x = c * x / 2 + c * x / 2 by ring, Real.exp_add]
      ring
    have h1 : c * x / 2 + 1 ≤ Real.exp (c * x / 2) := Real.add_one_le_exp _
    have h0 : (0 : ℝ) ≤ c * x / 2 + 1 := by positivity
    have h2 : (c * x / 2) ^ 2 ≤ (c * x / 2 + 1) ^ 2 := by nlinarith
    calc c ^ 2 * x ^ 2 / 4 = (c * x / 2) ^ 2 := by ring
      _ ≤ (c * x / 2 + 1) ^ 2 := h2
      _ ≤ (Real.exp (c * x / 2)) ^ 2 := pow_le_pow_left₀ h0 h1 2
      _ = Real.exp (c * x) := hsq.symm
  have hlin : K * (1 + x) ≤ c ^ 2 * x ^ 2 / 4 := by
    have h1 : K * (1 + x) ≤ 2 * K * x := by nlinarith
    have h3 : 8 * K ≤ c ^ 2 * x := by
      have h4 := mul_le_mul_of_nonneg_left hx2 (le_of_lt hc2)
      have h5 : c ^ 2 * (8 * K / c ^ 2) = 8 * K := by
        rw [mul_comm]; exact div_mul_cancel₀ _ (ne_of_gt hc2)
      linarith [h4, h5]
    have h2 : 2 * K * x ≤ c ^ 2 * x ^ 2 / 4 := by nlinarith
    linarith
  linarith

/-- The exponential sum bound at every frequency `h ≤ F(N)^C`, from Karacuba's theorem. -/
private theorem et_exp_sum
    (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named)
    (γ : ℝ) (hγ1 : 1 < γ) (hγ2 : γ < 3 / 2) (C : ℝ) (hC : 0 < C) (hCγ : C < γ - 1) :
    ∃ κ B : ℝ, 0 < κ ∧ 0 < B ∧ ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ,
      F γ N ^ (-(1 / 2 : ℝ)) < |α| → |α| ≤ 1 → ∀ h : ℕ, 1 ≤ h →
      (h : ℝ) ≤ F γ N ^ C →
      ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ ≤
        B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) :=
  Decomp547a.integer_multiple_decay_full
    (LeanLab.ExceptionalSet.U1539.DQLemma10.theorem2_of_karacuba_named hK)
    γ hγ1 hγ2 C hC hCγ

/-- The count against the true point count, transferred to `(z₁ - z₂) N / 2`; the parity defect
costs only `1/2`. -/
private theorem et_count (γ α z₁ z₂ : ℝ) (N H : ℕ) (hN4 : 4 ≤ N)
    (hz₂ : 0 ≤ z₂) (hz1 : z₂ < z₁) (hz₁ : z₁ ≤ 1) :
    |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
        z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
      - (z₁ - z₂) * (N : ℝ) / 2| ≤
    4 * (N : ℝ) / ((H : ℝ) + 1) + 1 / 2 +
      4 * ∑ h ∈ Finset.Icc 1 H,
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / (h : ℝ) := by
  have hcard : (Finset.Ioc (N / 2) N).card = N - N / 2 := et_card_Ioc N
  have hM2 : 2 ≤ (Finset.Ioc (N / 2) N).card := by rw [hcard]; omega
  have hkey := et_card_raw γ α z₁ z₂ N H hz₂ hz1 hz₁ hM2
  have hw0 : (0 : ℝ) ≤ z₁ - z₂ := by linarith
  have hw1 : z₁ - z₂ ≤ 1 := by linarith
  have hMcN : ((Finset.Ioc (N / 2) N).card : ℝ) ≤ (N : ℝ) := by
    rw [hcard]
    exact_mod_cast Nat.sub_le N (N / 2)
  have hstep1 : 4 * ((Finset.Ioc (N / 2) N).card : ℝ) / ((H : ℝ) + 1)
      ≤ 4 * (N : ℝ) / ((H : ℝ) + 1) := by
    gcongr
  have hpar := et_parity N
  have hsplit : |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
        z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
      - (z₁ - z₂) * (N : ℝ) / 2| ≤
      |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
        z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
        - (z₁ - z₂) * ((Finset.Ioc (N / 2) N).card : ℝ)| + 1 / 2 := by
    have hre : (((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
        z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
          - (z₁ - z₂) * (N : ℝ) / 2 =
        ((((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
          - (z₁ - z₂) * ((Finset.Ioc (N / 2) N).card : ℝ)) +
        ((z₁ - z₂) * ((Finset.Ioc (N / 2) N).card : ℝ) - (z₁ - z₂) * (N : ℝ) / 2) := by ring
    rw [hre]
    refine (abs_add_le _ _).trans ?_
    have hlast : |(z₁ - z₂) * ((Finset.Ioc (N / 2) N).card : ℝ) - (z₁ - z₂) * (N : ℝ) / 2|
        ≤ 1 / 2 := by
      rw [show (z₁ - z₂) * ((Finset.Ioc (N / 2) N).card : ℝ) - (z₁ - z₂) * (N : ℝ) / 2
          = (z₁ - z₂) * (((Finset.Ioc (N / 2) N).card : ℝ) - (N : ℝ) / 2) by ring,
        abs_mul, abs_of_nonneg hw0]
      nlinarith [hpar, hw1]
    linarith
  linarith

#print axioms exp_dom_lin
#print axioms et_exp_sum
#print axioms et_count

/-- Cancellation of the two `rpow` factors. -/
private theorem rpow_sub_mul_rpow (L : ℝ) (hL : 0 < L) (a b : ℝ) :
    L ^ (a - b) * L ^ b = L ^ a := by
  rw [← Real.rpow_add hL]; ring_nf

/-- `L^(a-1) * L = L^a`; the `rpow_one` bookkeeping that `rpow_sub_mul_rpow` cannot do. -/
private theorem rpow_sub_one_mul (L : ℝ) (hL : 0 < L) (a : ℝ) :
    L ^ (a - 1) * L = L ^ a := by
  conv_rhs => rw [show a = (a - 1) + 1 by ring]
  rw [Real.rpow_add hL, Real.rpow_one]

set_option maxHeartbeats 2000000 in
/-- **`Lemma4`, P0082 page 359, from Karacuba's Theorem 1 alone.**  The one-sided
Beurling–Selberg majorant of `Selberg524` gives the sharp Erdős–Turán count with weight `1/h`;
Karacuba gives the exponential sums up to the frequency `exp((κ₁/2)(log N)^{3-2γ})`, and the
harmonic absorption then beats the exponential saving. No Erdős–Turán hypothesis is used. -/
theorem lemma4_of_karacuba
    (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named) : Lemma4 := by
  intro γ hγ1 hγ2
  have hp0 : 0 < 3 - 2 * γ := by linarith
  have hγ0 : 0 < γ := by linarith
  obtain ⟨κ₁, B₁, hκ₁, hB₁, hsum⟩ :=
    et_exp_sum hK γ hγ1 hγ2 ((γ - 1) / 2) (by linarith) (by linarith)
  have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hLp : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (3 - 2 * γ)) atTop atTop :=
    (tendsto_rpow_atTop hp0).comp hlog
  obtain ⟨T₁, hT₁⟩ :=
    exp_dom_lin (3 * κ₁ / 4) (max (8 * B₁ * (1 + Real.log 2)) (4 * B₁ * κ₁))
      (by linarith) (by positivity)
  have hmul : Tendsto (fun N : ℕ => κ₁ / 4 * Real.log (N : ℝ) ^ (3 - 2 * γ)) atTop atTop :=
    hLp.const_mul_atTop (by linarith : (0 : ℝ) < κ₁ / 4)
  have hdec : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ ((3 - 2 * γ) - 1)) atTop (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => x ^ ((3 - 2 * γ) - 1)) atTop (𝓝 0) := by
      have h0 := tendsto_rpow_neg_atTop (y := 1 - (3 - 2 * γ)) (by linarith)
      have he : -((1 : ℝ) - (3 - 2 * γ)) = (3 - 2 * γ) - 1 := by ring
      rw [he] at h0
      exact h0
    exact h.comp hlog
  have hdecγ : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ ((3 - 2 * γ) - γ)) atTop (𝓝 0) := by
    have h : Tendsto (fun x : ℝ => x ^ ((3 - 2 * γ) - γ)) atTop (𝓝 0) := by
      have h0 := tendsto_rpow_neg_atTop (y := γ - (3 - 2 * γ)) (by linarith)
      have he : -(γ - (3 - 2 * γ)) = (3 - 2 * γ) - γ := by ring
      rw [he] at h0
      exact h0
    exact h.comp hlog
  have hall : ∀ᶠ N : ℕ in atTop,
      (3 ≤ N ∧ 4 ≤ N ∧ (1 : ℝ) ≤ Real.log (N : ℝ) ∧
       Real.log 2 ≤ (1 / 2 : ℝ) * Real.log (N : ℝ) ∧
       Real.log (N : ℝ) ^ ((3 - 2 * γ) - 1) ≤ 2 / κ₁ ∧
       Real.log (N : ℝ) ^ ((3 - 2 * γ) - γ) ≤ (γ - 1) / (2 * κ₁) ∧
       (1 : ℝ) ≤ (γ - 1) / 4 * Real.log (N : ℝ) ^ γ ∧
       16 ≤ Real.exp (κ₁ / 4 * Real.log (N : ℝ) ^ (3 - 2 * γ)) ∧
       T₁ ≤ Real.log (N : ℝ) ^ (3 - 2 * γ)) := by
    have h1 : ∀ᶠ N : ℕ in atTop, 3 ≤ N := eventually_atTop.mpr ⟨3, fun N h => h⟩
    have h2 : ∀ᶠ N : ℕ in atTop, 4 ≤ N := eventually_atTop.mpr ⟨4, fun N h => h⟩
    have h3 : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ Real.log (N : ℝ) := hlog.eventually_ge_atTop 1
    have h4 : ∀ᶠ N : ℕ in atTop, Real.log 2 ≤ (1 / 2 : ℝ) * Real.log (N : ℝ) := by
      have hh := hlog.eventually_ge_atTop (2 * Real.log 2)
      filter_upwards [hh] with N hN
      linarith
    have h5 : ∀ᶠ N : ℕ in atTop, Real.log (N : ℝ) ^ ((3 - 2 * γ) - 1) ≤ 2 / κ₁ :=
      (hdec.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < 2 / κ₁))).mono
        fun N hN => le_of_lt hN
    have h6 : ∀ᶠ N : ℕ in atTop,
        Real.log (N : ℝ) ^ ((3 - 2 * γ) - γ) ≤ (γ - 1) / (2 * κ₁) :=
      (hdecγ.eventually (Iio_mem_nhds (by positivity : (0 : ℝ) < (γ - 1) / (2 * κ₁)))).mono
        fun N hN => le_of_lt hN
    have h7 : ∀ᶠ N : ℕ in atTop, (1 : ℝ) ≤ (γ - 1) / 4 * Real.log (N : ℝ) ^ γ := by
      have ht : Tendsto (fun N : ℕ => (γ - 1) / 4 * Real.log (N : ℝ) ^ γ) atTop atTop :=
        ((tendsto_rpow_atTop hγ0).comp hlog).const_mul_atTop
          (by linarith : (0 : ℝ) < (γ - 1) / 4)
      exact ht.eventually_ge_atTop 1
    have h8 : ∀ᶠ N : ℕ in atTop,
        16 ≤ Real.exp (κ₁ / 4 * Real.log (N : ℝ) ^ (3 - 2 * γ)) :=
      (Real.tendsto_exp_atTop.comp hmul).eventually_ge_atTop 16
    have h9 : ∀ᶠ N : ℕ in atTop, T₁ ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) :=
      hLp.eventually_ge_atTop T₁
    filter_upwards [h1, h2, h3, h4, h5, h6, h7, h8, h9] with N k1 k2 k3 k4 k5 k6 k7 k8 k9
    exact ⟨k1, k2, k3, k4, k5, k6, k7, k8, k9⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hall
  refine ⟨κ₁ / 4, max 1 (Real.exp (κ₁ / 4 * Real.log (N₀ : ℝ) ^ (3 - 2 * γ)) + 4),
    by positivity, ?_⟩
  intro N hN α hlow hhigh z₁ z₂ hz₂ hz1 hz₁
  have hNR : (0 : ℝ) < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  rcases Nat.lt_or_ge N N₀ with hlt | hge
  · -- finitely many `N`: the trivial bound and a constant absorbing the exponential
    have hp : (0 : ℝ) ≤ 3 - 2 * γ := hp0.le
    have hL0 : (0 : ℝ) ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))
    have hLM : Real.log (N : ℝ) ≤ Real.log (N₀ : ℝ) := by
      rcases Nat.eq_zero_or_pos N₀ with h0 | h0
      · omega
      · exact Real.log_le_log (by exact_mod_cast (by omega : 0 < N)) (by exact_mod_cast hlt.le)
    have hpow : Real.log (N : ℝ) ^ (3 - 2 * γ) ≤ Real.log (N₀ : ℝ) ^ (3 - 2 * γ) :=
      Real.rpow_le_rpow hL0 hLM hp
    have hcard : (((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
        z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ) ≤ (N : ℝ) := by
      have h1 : (Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁) ⊆ Finset.Ioc (N / 2) N :=
        Finset.filter_subset _ _
      have h2 : (Finset.Ioc (N / 2) N).card = N - N / 2 := et_card_Ioc N
      have h3 := Finset.card_le_card h1
      rw [h2] at h3
      exact_mod_cast h3.trans (Nat.sub_le N (N / 2))
    have htriv : |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
        - (z₁ - z₂) * (N : ℝ) / 2| ≤ (N : ℝ) := by
      rw [abs_le]
      have hw : z₁ - z₂ ≤ 1 := by linarith
      constructor <;> nlinarith
    have hone : (1 : ℝ) ≤ max 1 (Real.exp (κ₁ / 4 * Real.log (N₀ : ℝ) ^ (3 - 2 * γ)) + 4) *
        Real.exp (-(κ₁ / 4) * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by
      have h6 : Real.exp (κ₁ / 4 * Real.log (N₀ : ℝ) ^ (3 - 2 * γ)) ≤
          max 1 (Real.exp (κ₁ / 4 * Real.log (N₀ : ℝ) ^ (3 - 2 * γ)) + 4) :=
        le_trans (by linarith) (le_max_right _ _)
      have h7 := mul_le_mul_of_nonneg_right h6
        (Real.exp_pos (-(κ₁ / 4) * Real.log (N : ℝ) ^ (3 - 2 * γ))).le
      refine le_trans ?_ h7
      rw [← Real.exp_add, ← Real.exp_zero]
      refine Real.exp_le_exp.mpr ?_
      have h8 : κ₁ / 4 * Real.log (N : ℝ) ^ (3 - 2 * γ) ≤
          κ₁ / 4 * Real.log (N₀ : ℝ) ^ (3 - 2 * γ) := by
        have := mul_le_mul_of_nonneg_left hpow (le_of_lt (by linarith : (0:ℝ) < κ₁ / 4))
        linarith
      linarith
    calc |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
          - (z₁ - z₂) * (N : ℝ) / 2| ≤ (N : ℝ) := htriv
      _ = (N : ℝ) * 1 := by ring
      _ ≤ (N : ℝ) * (max 1 (Real.exp (κ₁ / 4 * Real.log (N₀ : ℝ) ^ (3 - 2 * γ)) + 4) *
            Real.exp (-(κ₁ / 4) * Real.log (N : ℝ) ^ (3 - 2 * γ))) :=
          mul_le_mul_of_nonneg_left hone hNR.le
      _ = max 1 (Real.exp (κ₁ / 4 * Real.log (N₀ : ℝ) ^ (3 - 2 * γ)) + 4) * (N : ℝ) *
            Real.exp (-(κ₁ / 4) * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by ring
  · -- the main range
    obtain ⟨h3N, h4N, hL1, hL2, hL3, hL4, hL5, h16, hT⟩ := hN₀ N hge
    set L : ℝ := Real.log (N : ℝ) with hLdef
    have hLpos : (0 : ℝ) < L := by rw [hLdef]; linarith
    set P : ℝ := L ^ (3 - 2 * γ) with hPdef
    have hP0 : (0 : ℝ) ≤ P := Real.rpow_nonneg hLpos.le _
    set E₁ : ℝ := Real.exp (-κ₁ * P) with hE₁def
    set E : ℝ := Real.exp (-(κ₁ / 4) * P) with hEdef
    have hE0 : (0 : ℝ) < E := Real.exp_pos _
    set H : ℕ := Nat.ceil (Real.exp (κ₁ / 2 * P)) with hHdef
    have hHub1 : (1 : ℝ) ≤ Real.exp (κ₁ / 2 * P) := Real.one_le_exp (by positivity)
    have hH1 : 1 ≤ H := by
      rw [hHdef]
      have h : (1 : ℝ) ≤ (Nat.ceil (Real.exp (κ₁ / 2 * P)) : ℝ) :=
        le_trans hHub1 (Nat.le_ceil _)
      exact_mod_cast h
    have hHlb : Real.exp (κ₁ / 2 * P) ≤ (H : ℝ) := Nat.le_ceil _
    have hHub3 : (H : ℝ) ≤ 2 * Real.exp (κ₁ / 2 * P) := by
      have h := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ Real.exp (κ₁ / 2 * P) by positivity)
      rw [hHdef]
      linarith
    have hHpos : (0 : ℝ) < (H : ℝ) := by exact_mod_cast hH1
    have hHpos' : (0 : ℝ) < (H : ℝ) + 1 := by positivity
    have hlogH : Real.log (H : ℝ) ≤ Real.log 2 + κ₁ / 2 * P := by
      calc Real.log (H : ℝ) ≤ Real.log (2 * Real.exp (κ₁ / 2 * P)) := Real.log_le_log hHpos hHub3
        _ = Real.log 2 + κ₁ / 2 * P := by
            rw [Real.log_mul (by norm_num) (by positivity), Real.log_exp]
    -- the frequency range
    have hPrel : L ^ ((3 - 2 * γ) - γ) * L ^ γ = P := by
      rw [rpow_sub_mul_rpow L hLpos, hPdef]
    have hPκ : κ₁ * P ≤ (γ - 1) / 2 * L ^ γ := by
      have h := mul_le_mul_of_nonneg_right hL4 (by positivity : (0 : ℝ) ≤ κ₁ * L ^ γ)
      have h2 : L ^ ((3 - 2 * γ) - γ) * (κ₁ * L ^ γ) = κ₁ * P := by
        rw [show L ^ ((3 - 2 * γ) - γ) * (κ₁ * L ^ γ)
            = κ₁ * (L ^ ((3 - 2 * γ) - γ) * L ^ γ) by ring, rpow_sub_mul_rpow L hLpos, hPdef]
      have h' : (γ - 1) / (2 * κ₁) * (κ₁ * L ^ γ) = (γ - 1) / 2 * L ^ γ := by
        field_simp
      linarith [h, h', h2]
    have hHF : (H : ℝ) ≤ F γ N ^ ((γ - 1) / 2) := by
      have hFpos : (0 : ℝ) < F γ N := Real.exp_pos _
      rw [Real.rpow_def_of_pos hFpos]
      have hFlog : Real.log (F γ N) = L ^ γ := by rw [F, Real.log_exp]
      rw [hFlog]
      have hlog2 : Real.log 2 ≤ 1 := by
        have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
        linarith
      have hLγ : (0 : ℝ) ≤ L ^ γ := (Real.rpow_pos_of_pos hLpos γ).le
      have hhalf : κ₁ / 2 * P ≤ (γ - 1) / 4 * L ^ γ := by linarith [hPκ]
      have harg : Real.log 2 + κ₁ / 2 * P ≤ ((γ - 1) / 2) * L ^ γ := by
        linarith [hhalf, hlog2, hL5, hLγ]
      have hstep1 : (H : ℝ) ≤ 2 * Real.exp (κ₁ / 2 * P) := hHub3
      have hstep2 : 2 * Real.exp (κ₁ / 2 * P) = Real.exp (Real.log 2 + κ₁ / 2 * P) := by
        rw [Real.exp_add, Real.exp_log (by norm_num)]
      have hstep3 : Real.exp (Real.log 2 + κ₁ / 2 * P) ≤ Real.exp (L ^ γ * ((γ - 1) / 2)) :=
        Real.exp_le_exp.mpr (by linarith [harg])
      have hstep4 : Real.exp (L ^ γ * ((γ - 1) / 2)) = Real.exp (((γ - 1) / 2) * L ^ γ) := by
        rw [mul_comm]
      linarith [hstep1, hstep2, hstep3, hstep4]
    -- the count
    have hcnt := et_count γ α z₁ z₂ N H h4N hz₂ hz1 hz₁
    have hSb : ∀ h ∈ Finset.Icc 1 H,
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ ≤ B₁ * N * E₁ := by
      intro h hh
      obtain ⟨hh1, hh2⟩ := Finset.mem_Icc.mp hh
      exact hsum N (by omega) α hlow hhigh h hh1 (le_trans (by exact_mod_cast hh2) hHF)
    have hhsum : ∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ) ≤ 1 + Real.log (H : ℝ) := by
      have h1 : ∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ) = (harmonic H : ℝ) := by
        rw [harmonic_eq_sum_Icc]
        push_cast
        refine Finset.sum_congr rfl fun h _ => ?_
        simp [one_div]
      rw [h1]
      exact harmonic_le_one_add_log H
    have hSg : ∑ h ∈ Finset.Icc 1 H,
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / (h : ℝ) ≤
        (B₁ * (N : ℝ) * E₁) * (1 + Real.log (H : ℝ)) := by
      calc ∑ h ∈ Finset.Icc 1 H,
            ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / (h : ℝ)
          ≤ ∑ h ∈ Finset.Icc 1 H, (B₁ * (N : ℝ) * E₁) * (1 / (h : ℝ)) := by
            refine Finset.sum_le_sum fun h hh => ?_
            obtain ⟨hh1, -⟩ := Finset.mem_Icc.mp hh
            have hhpos : (0 : ℝ) < (h : ℝ) := by exact_mod_cast hh1
            rw [div_eq_mul_one_div]
            exact mul_le_mul_of_nonneg_right (hSb h hh) (by positivity)
        _ = (B₁ * (N : ℝ) * E₁) * ∑ h ∈ Finset.Icc 1 H, (1 : ℝ) / (h : ℝ) := by
            rw [Finset.mul_sum]
        _ ≤ (B₁ * (N : ℝ) * E₁) * (1 + Real.log (H : ℝ)) := by
            refine mul_le_mul_of_nonneg_left hhsum (by positivity)
    -- absorption
    have hexpNeg : Real.exp (-(κ₁ / 2) * P) = (Real.exp (κ₁ / 2 * P))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    have hEeq : Real.exp (-(κ₁ / 4) * P) = (Real.exp (κ₁ / 4 * P))⁻¹ := by
      rw [← Real.exp_neg]; congr 1; ring
    have hterm1 : 4 * (N : ℝ) / ((H : ℝ) + 1) ≤ (N : ℝ) * E / 4 := by
      have h1 : 1 / ((H : ℝ) + 1) ≤ Real.exp (-(κ₁ / 2) * P) := by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (H : ℝ) + 1)]
        have hHge : Real.exp (κ₁ / 2 * P) ≤ (H : ℝ) + 1 := by linarith
        have hm := mul_le_mul_of_nonneg_right hHge (Real.exp_pos (-(κ₁ / 2) * P)).le
        have hone : Real.exp (κ₁ / 2 * P) * Real.exp (-(κ₁ / 2) * P) = 1 := by
          rw [← Real.exp_add, show κ₁ / 2 * P + -(κ₁ / 2) * P = 0 by ring, Real.exp_zero]
        rw [hone] at hm
        linarith [hm]
      have h2 : 4 * Real.exp (-(κ₁ / 2) * P) ≤ Real.exp (-(κ₁ / 4) * P) / 4 := by
        have h3 : 16 * Real.exp (-(κ₁ / 2) * P) ≤ Real.exp (-(κ₁ / 4) * P) := by
          have h4 := mul_le_mul_of_nonneg_right h16 (Real.exp_pos (-(κ₁ / 2) * P)).le
          rwa [show Real.exp (κ₁ / 4 * P) * Real.exp (-(κ₁ / 2) * P)
            = Real.exp (-(κ₁ / 4) * P) by rw [← Real.exp_add]; congr 1; ring] at h4
        linarith
      calc 4 * (N : ℝ) / ((H : ℝ) + 1) = 4 * (N : ℝ) * (1 / ((H : ℝ) + 1)) := by ring
        _ ≤ 4 * (N : ℝ) * Real.exp (-(κ₁ / 2) * P) := by
            refine mul_le_mul_of_nonneg_left h1 (by positivity)
        _ = (N : ℝ) * (4 * Real.exp (-(κ₁ / 2) * P)) := by ring
        _ ≤ (N : ℝ) * (Real.exp (-(κ₁ / 4) * P) / 4) := by
            refine mul_le_mul_of_nonneg_left h2 hNR.le
        _ = (N : ℝ) * E / 4 := by rw [hEdef]; try ring
    have hterm3 : (1 : ℝ) / 2 ≤ (N : ℝ) * E / 4 := by
      have hlogP : κ₁ / 4 * P ≤ (1 / 2) * L := by
        have h := mul_le_mul_of_nonneg_right hL3 (by positivity : (0 : ℝ) ≤ κ₁ * L / 4)
        have h2 : L ^ ((3 - 2 * γ) - 1) * (κ₁ * L / 4) = κ₁ / 4 * P := by
          rw [show L ^ ((3 - 2 * γ) - 1) * (κ₁ * L / 4)
              = κ₁ / 4 * (L ^ ((3 - 2 * γ) - 1) * L) by ring,
            rpow_sub_one_mul L hLpos (3 - 2 * γ), hPdef]
        have h3 : (2 / κ₁) * (κ₁ * L / 4) = L / 2 := by
          have hκ : κ₁ ≠ 0 := ne_of_gt hκ₁
          field_simp
          try ring
        linarith [h, h2, h3]
      have hNE : 2 ≤ (N : ℝ) * E := by
        have h1 : Real.log 2 ≤ L + (-(κ₁ / 4) * P) := by linarith
        have h2 : Real.log ((N : ℝ) * E) = L + (-(κ₁ / 4) * P) := by
          rw [Real.log_mul hNR.ne' hE0.ne', hEdef, Real.log_exp, hLdef]
        calc (2 : ℝ) = Real.exp (Real.log 2) := (Real.exp_log (by norm_num)).symm
          _ ≤ Real.exp (Real.log ((N : ℝ) * E)) := Real.exp_le_exp.mpr (by rw [h2]; exact h1)
          _ = (N : ℝ) * E := Real.exp_log (by positivity)
      linarith
    have hterm2 : 4 * (B₁ * (N : ℝ) * E₁) * (1 + Real.log (H : ℝ)) ≤ (N : ℝ) * E / 2 := by
      have h1 : 8 * B₁ * (1 + Real.log (H : ℝ)) ≤ Real.exp (3 * κ₁ / 4 * P) := by
        have hK0 : 8 * B₁ * (1 + Real.log 2) ≤
            max (8 * B₁ * (1 + Real.log 2)) (4 * B₁ * κ₁) := le_max_left _ _
        have hK1 : 4 * B₁ * κ₁ ≤ max (8 * B₁ * (1 + Real.log 2)) (4 * B₁ * κ₁) := le_max_right _ _
        have hb : 8 * B₁ * (1 + Real.log 2 + κ₁ / 2 * P) ≤
            max (8 * B₁ * (1 + Real.log 2)) (4 * B₁ * κ₁) * (1 + P) := by
          have h5 := mul_le_mul_of_nonneg_right hK1 hP0
          nlinarith [hK0, h5, hP0]
        have hT' := hT₁ P hT
        have h6 := mul_le_mul_of_nonneg_left hlogH (by positivity : (0 : ℝ) ≤ 8 * B₁)
        nlinarith [hb, hT', h6, hlogH, hB₁.le]
      have h2 : Real.exp (3 * κ₁ / 4 * P) * E₁ = E := by
        rw [hE₁def, hEdef, ← Real.exp_add]; congr 1; ring
      have h3 := mul_le_mul_of_nonneg_right h1
        (by positivity : (0 : ℝ) ≤ (N : ℝ) * E₁ / 2)
      calc 4 * (B₁ * (N : ℝ) * E₁) * (1 + Real.log (H : ℝ))
          = (8 * B₁ * (1 + Real.log (H : ℝ))) * ((N : ℝ) * E₁ / 2) := by ring
        _ ≤ Real.exp (3 * κ₁ / 4 * P) * ((N : ℝ) * E₁ / 2) := h3
        _ = (N : ℝ) * E / 2 := by rw [← h2]; ring
    have hBmax : (1 : ℝ) ≤ max 1 (Real.exp (κ₁ / 4 * Real.log (N₀ : ℝ) ^ (3 - 2 * γ)) + 4) :=
      le_max_left _ _
    calc |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
          - (z₁ - z₂) * (N : ℝ) / 2|
        ≤ 4 * (N : ℝ) / ((H : ℝ) + 1) + 1 / 2 +
            4 * ∑ h ∈ Finset.Icc 1 H,
              ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / (h : ℝ) := hcnt
      _ ≤ 4 * (N : ℝ) / ((H : ℝ) + 1) + 1 / 2 +
            4 * ((B₁ * (N : ℝ) * E₁) * (1 + Real.log (H : ℝ))) := by linarith [hSg]
      _ ≤ (N : ℝ) * E := by linarith [hterm1, hterm2, hterm3]
      _ ≤ max 1 (Real.exp (κ₁ / 4 * Real.log (N₀ : ℝ) ^ (3 - 2 * γ)) + 4) * (N : ℝ) * E := by
          have h := mul_le_mul_of_nonneg_right hBmax (by positivity : (0 : ℝ) ≤ (N : ℝ) * E)
          linarith [h]

/-- `Lemma9` from Karacuba's Theorem 1 alone: `Lemma4` is now proved, so the only remaining
input is the cited Karacuba theorem behind `Lemma10`. -/
theorem lemma9_of_karacuba
    (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named) : Lemma9 :=
  lemma9_of_theorem2_lemma4_wired
    (LeanLab.ExceptionalSet.U1539.DQLemma10.theorem2_of_karacuba_named hK)
    (lemma4_of_karacuba hK)

/-- P0082 pages 368 to 369. The parity gap, CONDITIONAL ON the single named citation wall
`KaracubaThm1Named`: the Erdős–Turán wall of `lemma9_of_karacuba_erdosTuran` is discharged by
`lemma4_of_karacuba`. -/
theorem parity_gap_of_karacuba
    (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ j : ℤ, (j = 0 ∨ j = 1) →
          ∀ t : ℝ, |t| ≤ F γ N ^ δ →
            N * calE γ κ N ^ (-(5 / 6 : ℝ)) <
              ‖LeanLab.ExceptionalSet.UpJ200.Decomp539a.parityPhase γ N j t‖ →
            ∃ h : ℤ, |t - h / 2| ≤ F γ N ^ (δ - 1) :=
  LeanLab.ExceptionalSet.UpJ200.Decomp539a.parity_gap_of_inputs
    (lemma9_of_karacuba hK)
    (LeanLab.ExceptionalSet.U1539.DQLemma10.lemma10_of_karacuba_named hK) γ h1 h2

#print axioms lemma4_of_karacuba
#print axioms lemma9_of_karacuba
#print axioms parity_gap_of_karacuba

end LeanLab.ExceptionalSet.Prep1121Lemma9Wire
