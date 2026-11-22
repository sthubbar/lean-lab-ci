import LeanLab.ExceptionalSet.Prep1121Trapezoid
import LeanLab.ExceptionalSet.DQLemma10S1
import LeanLab.ExceptionalSet.DQLemma4Decisions
import LeanLab.ExceptionalSet.UpJ200.Decomp539a

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

end LeanLab.ExceptionalSet.Prep1121Lemma9Wire
