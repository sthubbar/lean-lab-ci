import LeanLab.ExceptionalSet.SPLIT_lemma4

/-!
Burst burst-20261122 unit P1122-0117, the `lemma4_split` route audit of `SPLIT_lemma4.lean`.

The LEAF `leaf_absorption` of `LeanLab.ExceptionalSet.SPLIT_lemma4` is FALSE.
With `H = ⌈log N⌉` its left side contains the term `4N/(⌈log N⌉ + 1)`, of size about
`4N / log N`, while its right side is `B N exp(-κ (log N)^{3-2γ})`. For `0 < 3 - 2γ` the factor
`exp(-κ (log N)^{3-2γ})` decays faster than any power of `1/log N`, so no `κ > 0` and `B ≥ 1`
absorb the first term. This file proves the negation of the leaf statement, verbatim, at
`γ = 5/4`, `κ₁ = B₁ = 1`.

The same statement is `DecompF2078Leaves.leaf_F2078_absorption`, whose negation was recorded
by omos_tick 20261121T1959Z off main; this is the first negation on main, for the copy in
`SPLIT_lemma4`. Consequence: `lemma4_split` rests on a false leaf, so that route is dead. The
live routes to `Lemma4` are `Prep1121Lemma9Wire.lemma4_of_karacuba`, CONDITIONAL ON
`KaracubaThm1Named` only, and `DQLemma4.lemma4_of_erdosTuran_theorem2`. P0082 page 359 does
not use this bookkeeping; the defect is in the lab's choice of the cutoff `H`, not in the paper.

The leaf statement is not changed and this file does not use it.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.U1539.FalseLeafAbsorptionLemma4

open Real Filter
open scoped Topology

/-- Standard real analysis: `B (x² + 2) exp(-κ x) → 0` as `x → ∞`. -/
theorem tendsto_poly_exp_neg (κ B : ℝ) (hκ : 0 < κ) :
    Tendsto (fun x : ℝ => B * (x ^ (2 : ℝ) * Real.exp (-κ * x) + 2 * Real.exp (-κ * x)))
      atTop (𝓝 0) := by
  have h1 : Tendsto (fun x : ℝ => x ^ (2 : ℝ) * Real.exp (-κ * x)) atTop (𝓝 0) :=
    tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 2 κ hκ
  have h2 : Tendsto (fun x : ℝ => Real.exp (-κ * x)) atTop (𝓝 0) := by
    have : Tendsto (fun x : ℝ => -κ * x) atTop atBot :=
      tendsto_id.const_mul_atTop_of_neg (by linarith)
    exact Real.tendsto_exp_atBot.comp this
  simpa using (h1.add (h2.const_mul 2)).const_mul B

/-- The negation of `SPLIT_lemma4.leaf_absorption`, statement copied verbatim. -/
theorem leaf_absorption_false :
    ¬ (∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ κ₁ B₁ : ℝ, 0 < κ₁ → 0 < B₁ →
      ∃ κ B : ℝ, 0 < κ ∧ 1 ≤ B ∧ ∀ N : ℕ, 3 ≤ N →
        4 * N / ((Nat.ceil (Real.log N) : ℝ) + 1) +
          4 * N * (B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ))
            * ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)), 1 / ((h : ℝ) + 1))
          ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ))) := by
  intro h
  obtain ⟨κ, B, hκ, hB, hle⟩ := h (5 / 4) (by norm_num) (by norm_num) 1 1 one_pos one_pos
  have ha : (3 - 2 * (5 / 4 : ℝ)) = 1 / 2 := by norm_num
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hsq : Tendsto (fun N : ℕ => Real.log N ^ (1 / 2 : ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num)).comp hlog
  have hev := ((tendsto_poly_exp_neg κ B hκ).comp hsq).eventually
    (gt_mem_nhds (show (0 : ℝ) < 4 by norm_num))
  obtain ⟨N, hN⟩ := eventually_atTop.mp (hev.and (eventually_ge_atTop 3))
  obtain ⟨hbig, hN3⟩ := hN N le_rfl
  simp only [Function.comp_apply] at hbig
  have hN3r : (3 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN3
  have hNpos : (0 : ℝ) < N := by linarith
  set L := Real.log (N : ℝ) with hLdef
  have hL : 0 < L := Real.log_pos (by linarith)
  have hsqL : (L ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = L := by
    rw [← Real.rpow_mul hL.le]; norm_num
  rw [hsqL] at hbig
  set E := Real.exp (-κ * L ^ (1 / 2 : ℝ)) with hEdef
  have hE : 0 < E := Real.exp_pos _
  have h0 := hle N hN3
  rw [ha] at h0
  set c : ℝ := (Nat.ceil L : ℝ) with hcdef
  have hc0 : 0 ≤ c := Nat.cast_nonneg _
  have hcL : c + 1 ≤ L + 2 := by
    have := Nat.ceil_lt_add_one hL.le
    linarith
  have hsum : 0 ≤ ∑ h ∈ Finset.Icc 1 (Nat.ceil L), 1 / ((h : ℝ) + 1) :=
    Finset.sum_nonneg (fun h _ => by positivity)
  have hsecond : 0 ≤ 4 * (N : ℝ) * (1 * N * Real.exp (-1 * L ^ (1 / 2 : ℝ))
      * ∑ h ∈ Finset.Icc 1 (Nat.ceil L), 1 / ((h : ℝ) + 1)) := by
    have := Real.exp_pos (-1 * L ^ (1 / 2 : ℝ))
    positivity
  have hfirst : 4 * (N : ℝ) / (c + 1) ≤ B * N * E := by linarith
  rw [div_le_iff₀ (by linarith)] at hfirst
  have hBNE : 0 ≤ B * N * E := by positivity
  have h3 : B * N * E * (c + 1) ≤ B * N * E * (L + 2) :=
    mul_le_mul_of_nonneg_left hcL hBNE
  have h4 : B * N * E * (L + 2) = N * (B * (L * E + 2 * E)) := by ring
  have h5 : N * (B * (L * E + 2 * E)) < N * 4 := mul_lt_mul_of_pos_left hbig hNpos
  linarith

/-- The same negation stated through the type of the leaf itself, so the copy above cannot
drift from `SPLIT_lemma4.leaf_absorption`. -/
theorem not_leaf_absorption : ¬ (type_of% @LeanLab.ExceptionalSet.U1539.leaf_absorption) :=
  leaf_absorption_false

#print axioms tendsto_poly_exp_neg
#print axioms leaf_absorption_false
#print axioms not_leaf_absorption

end LeanLab.ExceptionalSet.U1539.FalseLeafAbsorptionLemma4
