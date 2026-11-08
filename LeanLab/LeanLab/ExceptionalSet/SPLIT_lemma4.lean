/-
Split of `lemma4` in ExceptionalSet/State1539.lean into smaller leaves.

The statement being split, verbatim after its name:

: Lemma4

`lemma4_split` below proves `Lemma4` from the leaves, with no `sorry` of its own and without
using the target theorem.  The leaves are the steps of Vinogradov's equidistribution
argument, in the order the assembly uses them:

1. `leaf_fejer_majorant` - the discrepancy of the count against `(z₁ - z₂)N/2` is controlled
   by the first `H` exponential sums `Σ e(hαF(n))`; no decay and no unknown constants.
2. `leaf_exp_sum_bound` - each of those sums is small, at frequency `h α` and on the index
   range `N/2 < n ≤ N` that the count runs over, uniformly in `h ≤ F(N)^C`.
3. `leaf_log_regime` - past a threshold, `⌈log N⌉` lies in the frequency range of step 2 and
   is at least 1.
4. `leaf_absorption` - the bookkeeping: the `4N/(⌈log N⌉+1)` term and the geometrically
   small sum are dominated by one term of the same shape with a smaller `κ`.
5. `leaf_small_N` - the finitely many `N` below the threshold, with a constant absorbing the
   `exp` factor there.

AI wrote the Lean code.  The leaves are open; the assembly is proved.
-/
import LeanLab.ExceptionalSet.State1539

namespace LeanLab.ExceptionalSet.U1539

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Leaves -/

/-- LEAF. Step 1, the counting inequality: for every `H`, the excess of the number of
`N/2 < n ≤ N` with `z₂ ≤ {αF(n)} < z₁` over `(z₁ - z₂)N/2` is at most `4N/(H+1)` plus the
first `H` exponential sums at the frequencies `hα`, each weighted by `4N/(h+1)`.  This is the
Fejér-kernel majorant for the indicator of an interval of fractional parts. -/
theorem leaf_fejer_majorant (γ α z₁ z₂ : ℝ) (N H : ℕ)
    (hz₂ : 0 ≤ z₂) (hz1 : z₂ < z₁) (hz₁ : z₁ ≤ 1) :
    |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
        z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
      - (z₁ - z₂) * N / 2| ≤
    4 * N / ((H : ℝ) + 1) +
      4 * N * ∑ h ∈ Finset.Icc 1 H,
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1) := by
  sorry

/-- LEAF. Step 2, the exponential-sum input at the frequencies `hα`: it has the shape of the
sealed Theorem 2 of this unit at frequency `h α` and at the scale `N/2`, with `c = 1/2` and
the exponent `C`, summed over `N/2 < n ≤ N`. -/
theorem leaf_exp_sum_bound :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ C : ℝ, 0 < C → C < γ - 1 →
      ∃ κ B : ℝ, 0 < κ ∧ 0 < B ∧ ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ,
        F γ N ^ (-(1 / 2 : ℝ)) < |α| → |α| ≤ 1 → ∀ h : ℕ, 1 ≤ h →
        (h : ℝ) ≤ F γ N ^ C →
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ ≤
          B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  sorry

/-- LEAF. Step 3, the regime: past a threshold, `N ≥ 3`, `log N ≥ 1`, `⌈log N⌉ ≥ 1`, and
`⌈log N⌉ ≤ F(N)^C` for every `C > 0`.  The last is what lets step 2 be applied at every
frequency `h ≤ ⌈log N⌉`. -/
theorem leaf_log_regime :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ C : ℝ, 0 < C →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        3 ≤ N ∧ 1 ≤ Real.log N ∧ (1 : ℝ) ≤ (Nat.ceil (Real.log N) : ℝ) ∧
        (Nat.ceil (Real.log N) : ℝ) ≤ F γ N ^ C := by
  intro γ hγ1 hγ2 C hC
  have hδ : 0 < γ - 1 := by linarith
  obtain ⟨L₀, hL₀1, hL₀e, hL₀X⟩ :
      ∃ L₀ : ℝ, (1 : ℝ) ≤ L₀ ∧ Real.exp 1 ≤ L₀ ∧ (1 / C) ^ (1 / (γ - 1)) ≤ L₀ :=
    ⟨max 1 (max (Real.exp 1) ((1 / C) ^ (1 / (γ - 1)))),
      le_max_left _ _, le_trans (le_max_left _ _) (le_max_right _ _),
      le_trans (le_max_right _ _) (le_max_right _ _)⟩
  have hexp1 : (3 : ℝ) ≤ Real.exp (Real.exp 1) := by
    have h1 : 2 * Real.exp 1 ≤ Real.exp (Real.exp 1) := Real.two_mul_le_exp
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp 1]
    nlinarith
  refine ⟨Nat.ceil (Real.exp L₀) + 1, ?_⟩
  intro N hN
  have hNge : Real.exp L₀ ≤ (N : ℝ) := by
    have h1 : Real.exp L₀ ≤ (Nat.ceil (Real.exp L₀) : ℝ) := Nat.le_ceil _
    have h2 : (Nat.ceil (Real.exp L₀) : ℝ) ≤ ((Nat.ceil (Real.exp L₀) + 1 : ℕ) : ℝ) := by
      push_cast; linarith
    linarith [h2.trans (by exact_mod_cast hN :
      ((Nat.ceil (Real.exp L₀) + 1 : ℕ) : ℝ) ≤ (N : ℝ))]
  have hL : L₀ ≤ Real.log (N : ℝ) :=
    (Real.le_log_iff_exp_le (by have h := Real.exp_pos L₀; linarith)).mpr hNge
  have hL1 : (1 : ℝ) ≤ Real.log (N : ℝ) := le_trans hL₀1 hL
  have hL3 : (3 : ℝ) ≤ (N : ℝ) := by
    have h1 : (3 : ℝ) ≤ Real.exp L₀ := le_trans hexp1 (Real.exp_le_exp.mpr hL₀e)
    linarith
  have hLpos : (0 : ℝ) < Real.log (N : ℝ) := by linarith
  have hX0 : (0 : ℝ) ≤ (1 / C) ^ (1 / (γ - 1)) := Real.rpow_nonneg (by positivity) _
  have hXpow : ((1 / C) ^ (1 / (γ - 1))) ^ (γ - 1) = 1 / C := by
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 1 / C)]
    have h1 : 1 / (γ - 1) * (γ - 1) = 1 := by field_simp
    rw [h1, Real.rpow_one]
  have hLδ : 1 / C ≤ (Real.log (N : ℝ)) ^ (γ - 1) := by
    have h := Real.rpow_le_rpow hX0 (le_trans hL₀X hL) hδ.le
    rwa [hXpow] at h
  have hγsplit : (Real.log (N : ℝ)) ^ γ =
      Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ (γ - 1) := by
    have h : γ = (γ - 1) + 1 := by ring
    conv_lhs => rw [h]
    rw [Real.rpow_add hLpos, Real.rpow_one]
    ring
  have hmain : Real.log (N : ℝ) + 1 ≤ Real.exp (C * (Real.log (N : ℝ)) ^ γ) := by
    have h1 : C * (Real.log (N : ℝ)) ^ γ =
        C * Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ (γ - 1) := by
      rw [hγsplit]; ring
    have h3 : 2 * (C * Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ (γ - 1)) ≤
        Real.exp (C * (Real.log (N : ℝ)) ^ γ) := by
      rw [h1]; exact Real.two_mul_le_exp
    have h4 : 2 * (C * Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ (γ - 1)) ≥
        2 * Real.log (N : ℝ) := by
      have hCL : (0 : ℝ) < C * Real.log (N : ℝ) := by positivity
      have h6 : C * Real.log (N : ℝ) * (1 / C) ≤
          C * Real.log (N : ℝ) * (Real.log (N : ℝ)) ^ (γ - 1) :=
        mul_le_mul_of_nonneg_left hLδ hCL.le
      have h5 : C * Real.log (N : ℝ) * (1 / C) = Real.log (N : ℝ) := by field_simp
      linarith
    linarith
  have hceil : (Nat.ceil (Real.log (N : ℝ)) : ℝ) ≤
      Real.exp (C * (Real.log (N : ℝ)) ^ γ) := by
    have h1 : (Nat.ceil (Real.log (N : ℝ)) : ℝ) < Real.log (N : ℝ) + 1 :=
      Nat.ceil_lt_add_one hLpos.le
    linarith
  have hceil1 : (1 : ℝ) ≤ (Nat.ceil (Real.log (N : ℝ)) : ℝ) := le_trans hL1 (Nat.le_ceil _)
  have hF : F γ N ^ C = Real.exp (C * (Real.log (N : ℝ)) ^ γ) := by
    have hpos : 0 < F γ N := Real.exp_pos _
    rw [Real.rpow_def_of_pos hpos]
    congr 1
    simp [F, Real.log_exp, mul_comm]
  refine ⟨?_, hL1, hceil1, ?_⟩
  · exact_mod_cast hL3
  · rw [hF]; exact hceil

/-- LEAF. Step 4, the bookkeeping of the geometric decay: with `H = ⌈log N⌉`, the term
`4N/(H+1)` and the sum of the equally decaying terms weighted by `1/(h+1)` are both dominated
by `B N exp(-κ (log N)^{3-2γ})` for a strictly smaller `κ` and a large enough `B`, once
`N ≥ 3`. -/
theorem leaf_absorption :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ κ₁ B₁ : ℝ, 0 < κ₁ → 0 < B₁ →
      ∃ κ B : ℝ, 0 < κ ∧ 1 ≤ B ∧ ∀ N : ℕ, 3 ≤ N →
        4 * N / ((Nat.ceil (Real.log N) : ℝ) + 1) +
          4 * N * (B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ))
            * ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)), 1 / ((h : ℝ) + 1))
          ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  sorry

/-- LEAF. Step 5, the finitely many small `N`: below any fixed bound the trivial bound
`|count - (z₁ - z₂)N/2| ≤ N` is absorbed by a large constant times
`N exp(-κ (log N)^{3-2γ})`, since on that finite range the `exp` factor is bounded below. -/
theorem leaf_small_N :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ κ : ℝ, 0 < κ → ∀ N₀ : ℕ, ∃ B : ℝ, 0 ≤ B ∧
      ∀ N : ℕ, 1 ≤ N → N ≤ N₀ → ∀ α z₁ z₂ : ℝ, 0 ≤ z₂ → z₂ < z₁ → z₁ ≤ 1 →
        |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
            z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
          - (z₁ - z₂) * N / 2| ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
  intro γ hγ1 hγ2 κ hκ N₀
  refine ⟨Real.exp (κ * Real.log (N₀ : ℝ) ^ (3 - 2 * γ)), (Real.exp_pos _).le, ?_⟩
  intro N hN hNN₀ α z₁ z₂ hz₂ hz1 hz₁
  have hp : (0 : ℝ) ≤ 3 - 2 * γ := by linarith
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hcard : (((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
      z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ) ≤ (N : ℝ) := by
    have h1 : ((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
        z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card ≤ N := by
      refine le_trans (Finset.card_filter_le _ _) ?_
      rw [Nat.card_Ioc]
      omega
    exact_mod_cast h1
  have hx0 : 0 ≤ (z₁ - z₂) * (N : ℝ) / 2 := by
    have h2 : 0 ≤ z₁ - z₂ := by linarith
    positivity
  have hxN : (z₁ - z₂) * (N : ℝ) / 2 ≤ (N : ℝ) := by
    have h1 : z₁ - z₂ ≤ 1 := by linarith
    have h2 : (z₁ - z₂) * (N : ℝ) / 2 ≤ 1 * (N : ℝ) / 2 := by
      have h3 : (0 : ℝ) ≤ (N : ℝ) / 2 := by positivity
      nlinarith
    linarith
  have hL0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg (by exact_mod_cast hN)
  have hLM : Real.log (N : ℝ) ≤ Real.log (N₀ : ℝ) :=
    Real.log_le_log hNR (by exact_mod_cast hNN₀)
  have hpow : Real.log (N : ℝ) ^ (3 - 2 * γ) ≤ Real.log (N₀ : ℝ) ^ (3 - 2 * γ) :=
    Real.rpow_le_rpow hL0 hLM hp
  have hexp : (1 : ℝ) ≤
      Real.exp (κ * Real.log (N₀ : ℝ) ^ (3 - 2 * γ)) *
        Real.exp (-κ * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by
    rw [← Real.exp_add, ← Real.exp_zero]
    refine Real.exp_le_exp.mpr ?_
    nlinarith
  have hmain : |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
      z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
      - (z₁ - z₂) * (N : ℝ) / 2| ≤ (N : ℝ) := by
    rw [abs_le]
    constructor <;> linarith
  calc |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
        - (z₁ - z₂) * (N : ℝ) / 2|
      ≤ (N : ℝ) := hmain
    _ = (N : ℝ) * 1 := by ring
    _ ≤ (N : ℝ) * (Real.exp (κ * Real.log (N₀ : ℝ) ^ (3 - 2 * γ)) *
          Real.exp (-κ * Real.log (N : ℝ) ^ (3 - 2 * γ))) := by
        exact mul_le_mul_of_nonneg_left hexp hNR.le
    _ = Real.exp (κ * Real.log (N₀ : ℝ) ^ (3 - 2 * γ)) * (N : ℝ) *
          Real.exp (-κ * Real.log (N : ℝ) ^ (3 - 2 * γ)) := by ring

/-! ### Assembly -/

/-- `Lemma4`: the count of `N/2 < n ≤ N` with `z₂ ≤ {αF(n)} < z₁` is `(z₁ - z₂)N/2` up to
`O(N exp(-κ (log N)^{3-2γ}))`, uniformly for `F(N)^{-1/2} < |α| ≤ 1`.  Proved from the leaves
above, with no `sorry` here and without using the target theorem. -/
theorem lemma4_split : Lemma4 := by
  intro γ hγ1 hγ2
  obtain ⟨κ₁, B₁, hκ₁, hB₁, hsum⟩ :=
    leaf_exp_sum_bound γ hγ1 hγ2 ((γ - 1) / 2) (by linarith) (by linarith)
  obtain ⟨N₀, hN₀⟩ := leaf_log_regime γ hγ1 hγ2 ((γ - 1) / 2) (by linarith)
  obtain ⟨κ, B, hκ, hB, habs⟩ := leaf_absorption γ hγ1 hγ2 κ₁ B₁ hκ₁ hB₁
  obtain ⟨B₂, -, hsmall⟩ := leaf_small_N γ hγ1 hγ2 κ hκ (max N₀ 1)
  refine ⟨κ, max B B₂, hκ, ?_⟩
  intro N hN α hlow hhigh z₁ z₂ hz₂ hz1 hz₁
  have hE : (0 : ℝ) ≤ Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := (Real.exp_pos _).le
  rcases lt_or_ge N (max N₀ 1) with hlt | hge
  · have hs := hsmall N hN (le_of_lt hlt) α z₁ z₂ hz₂ hz1 hz₁
    calc |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
            z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
          - (z₁ - z₂) * N / 2|
        ≤ B₂ * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := hs
      _ ≤ max B B₂ * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
          refine mul_le_mul_of_nonneg_right ?_ hE
          exact mul_le_mul_of_nonneg_right (le_max_right _ _) (by positivity)
  · obtain ⟨h3, -, -, hceilF⟩ := hN₀ N (le_trans (le_max_left _ _) hge)
    have hfej := leaf_fejer_majorant γ α z₁ z₂ N (Nat.ceil (Real.log N)) hz₂ hz1 hz₁
    have hterm : ∀ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)),
        ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ ≤
          B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ)) := by
      intro h hh
      obtain ⟨hh1, hh2⟩ := Finset.mem_Icc.mp hh
      have hhF : (h : ℝ) ≤ F γ N ^ ((γ - 1) / 2) := by
        refine le_trans (by exact_mod_cast hh2) hceilF
      exact hsum N hN α hlow hhigh h hh1 hhF
    have hS : ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)),
          ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1)
        ≤ B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ))
            * ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)), 1 / ((h : ℝ) + 1) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun h hh => ?_
      have ht := hterm h hh
      have hpos : (0 : ℝ) ≤ ((h : ℝ) + 1)⁻¹ := by positivity
      calc ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1)
          = ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ * ((h : ℝ) + 1)⁻¹ := by
            ring
        _ ≤ (B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ))) * ((h : ℝ) + 1)⁻¹ :=
            mul_le_mul_of_nonneg_right ht hpos
        _ = B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ)) * (1 / ((h : ℝ) + 1)) := by
            ring
    have hstep : 4 * N * ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)),
          ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (h * α * F γ n)‖ / ((h : ℝ) + 1)
        ≤ 4 * N * (B₁ * N * Real.exp (-κ₁ * Real.log N ^ (3 - 2 * γ))
            * ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)), 1 / ((h : ℝ) + 1)) :=
      mul_le_mul_of_nonneg_left hS (by positivity)
    have hmain : |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
        - (z₁ - z₂) * N / 2| ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) :=
      le_trans hfej (le_trans (add_le_add_right hstep _) (habs N h3))
    calc |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
            z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
          - (z₁ - z₂) * N / 2|
        ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := hmain
      _ ≤ max B B₂ * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) := by
          refine mul_le_mul_of_nonneg_right ?_ hE
          exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)

end LeanLab.ExceptionalSet.U1539
