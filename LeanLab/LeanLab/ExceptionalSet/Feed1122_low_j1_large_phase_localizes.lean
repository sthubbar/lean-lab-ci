import LeanLab.ExceptionalSet.SPLIT_leaf_inner_low_j1

/-!
Split of `Decomp553c.leaf_low_j1_large_phase_localizes`, the localization of large
values of the assigned lower block phase, from `SPLIT_leaf_inner_low_j1`.

Source: P0082, J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences,
Ann. Inst. Fourier 48 (1998), doi 10.5802/aif.1621, Lemma 9 page 368 and its proof in
section 7 page 370, displays 40 and 41, with Theorem 2 as the exponential sum input.

The localization is the lab form of Lemma 9 for the block `low_j1`: the lower half
`n ≤ 3N/4` of `(N/2, N]` with `⌊F(n)⌋` odd, that is `ν_n + 1` even. Its proof has two steps.

  * Display 40 and 41: the parity condition is removed by the trapezoid Fourier
    expansion and Lemma 4, so a large block phase forces a large unrestricted phase
    `Σ e((t - h/2) F(n))` over the same sub-block, with `|h| ≤ ℰ^2`.
  * Theorem 2 on the sub-block: away from `X^{δ-1}` and below `3 ℰ^2`, the
    unrestricted phase over the sub-block is at most `N ℰ^{-2}` once `κ` is small.

The assembly is the closing contradiction of page 370. AI wrote the Lean code.
Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp553c

open Real Finset MeasureTheory Set Filter Topology
open LeanLab.ExceptionalSet.U1539 (Sp eC nu calE majorArcs)
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.UpJ200.Decomp539a
open LeanLab.ExceptionalSet.Decomp553a
open LeanLab.ExceptionalSet.DQLemma9

/-- LEAF: P0082 page 370 displays 40 and 41, proof of Lemma 9, the removal of the
parity condition on the assigned lower block. HARD. The indicator of `⌊F(n)⌋` odd is
replaced by the trapezoid function `Υ((F(n) - 1)/2)` with Fourier coefficients
`c_h ≪ min(A, A^{-1} h^{-2})`; Lemma 4 with `α = 1/2` bounds the `n` of `(N/2, N]` where
the two differ, the tail `|h| > ℰ^2` is removed by the coefficient bound, and the
remaining sum over `|h| ≤ ℰ^2` has total coefficient mass `≪ A^{-1/2}`. With
`A ≍ ℰ^{-5/6}` a block phase above `N ℰ^{-5/6}` forces some unrestricted shifted phase
over the sub-block `n ≤ 3N/4` above `N ℰ^{-2}`. The shift `F(n) - 1` only
multiplies each term by the unimodular factor `e(-t)`. -/
theorem leaf_low_j1_parity_shift (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t : ℝ,
        |t| ≤ 2 * calE γ κ N ^ (2 / 3 : ℝ) →
        (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
            ‖blockPhase (indices_low_j1 γ N) (fun n => F γ n - (1 : ℤ)) t‖ →
          ∃ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (2 : ℝ) ∧
            (N : ℝ) * calE γ κ N ^ (-(2 : ℝ)) <
              ‖∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4),
                eC ((t - (h : ℝ) / 2) * F γ n)‖ := by
  have h4 : LeanLab.ExceptionalSet.U1539.Lemma4 := by sorry
  have h_main : ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ t : ℝ,
        |t| ≤ 2 * calE γ κ N ^ (2 / 3 : ℝ) →
        (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
            ‖blockPhase (indices_low_j1 γ N) (fun n => F γ n - (1 : ℤ)) t‖ →
          ∃ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (2 : ℝ) ∧
            (N : ℝ) * calE γ κ N ^ (-(2 : ℝ)) <
              ‖∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4),
                eC ((t - (h : ℝ) / 2) * F γ n)‖ := by
    -- Step 1: Extract Lemma 4 parameters κ₄, B₄
    obtain ⟨κ₄, B₄, hκ₄, hL4⟩ := h4 γ h1 h2
    -- Step 2: Set up constants. We use κ₀ = κ₄ / 2 (smaller than Lemma 4's κ)
    -- The proof follows large_value_shift_of_lemma4 with adjusted exponents:
    -- x = ℰ^{-5/12}, so x² = ℰ^{-5/6} (hypothesis exponent)
    -- Δ = (9/5) * x, K = ⌊ℰ²⌋
    -- The mass bound gives ∑_{|h|≤K} |c_h| ≪ Δ^{-1} = ℰ^{5/6}
    -- Then mass * Nℰ^{-2} = Nℰ^{-7/6} < Nℰ^{-5/6} for ℰ ≥ 1
    refine' ⟨κ₄ / 2, by linarith, fun κ hκ hκ₁ => ?_⟩
    -- Step 3: Asymptotic conditions for N
    have hLt : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (3 - 2 * γ)) atTop atTop := by
      have hpos : 0 < (3 - 2 * γ : ℝ) := by linarith
      have h : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (3 - 2 * γ)) atTop atTop :=
        (tendsto_rpow_atTop hpos).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
      exact h
    -- N_a: log N^{3-2γ} large enough for ℰ ≥ 1 and other bounds
    obtain ⟨Na, hNa⟩ := (hLt.eventually_ge_atTop (3 * Real.log 100 / κ)).mp (Filter.eventually_of_forall fun N => by
      have hN : N ≥ 1 := by
        by_contra h
        have hN' : N = 0 := by
          omega
        simp_all [hN']
        <;> norm_num at * <;> linarith)
    -- N_b: Lemma 4 error bound B' * exp(-κ₄ L) ≤ x / 100
    set B' := |B₄| + 1 with hB'
    have hB'pos : 0 < B' := by positivity
    obtain ⟨Nb, hNb⟩ := (hLt.eventually_ge_atTop (Real.log (100 * B') / (2 * κ₄ / 3))).mp (Filter.eventually_of_forall fun N => by
      have hN : N ≥ 1 := by
        by_contra h
        have hN' : N = 0 := by omega
        simp_all [hN']
        <;> norm_num at * <;> linarith)
    -- N_c: log N large enough for various inequalities
    have hlog : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    obtain ⟨Nc, hNc⟩ := (hlog.eventually_ge_atTop (2 * Real.log 2 + 1)).mp (Filter.eventually_of_forall fun N => by
      have hN : N ≥ 1 := by
        by_contra h
        have hN' : N = 0 := by omega
        simp_all [hN']
        <;> norm_num at * <;> linarith)
    -- N_e: log N^{1-(3-2γ)} large
    have hratio : Tendsto (fun N : ℕ => Real.log (N : ℝ) ^ (1 - (3 - 2 * γ))) atTop atTop := by
      have hpos : 0 < (1 - (3 - 2 * γ) : ℝ) := by linarith
      exact (tendsto_rpow_atTop hpos).comp hlog
    obtain ⟨Ne, hNe⟩ := (hratio.eventually_ge_atTop (100)).mp (Filter.eventually_of_forall fun N => by
      have hN : N ≥ 1 := by
        by_contra h
        have hN' : N = 0 := by omega
        simp_all [hN']
        <;> norm_num at * <;> linarith)
    -- Step 4: Define N₀
    refine' ⟨max 2 (max Na (max Nb (max Nc Ne))), fun N hN => ?_⟩
    intro t ht hbig
    -- Step 5: Local parameters for this N
    have hN2 : 2 ≤ N := by
      have h₁ : 2 ≤ max 2 (max Na (max Nb (max Nc Ne))) := by apply le_max_left
      linarith
    have hNa' : Na ≤ N := by
      have h₁ : Na ≤ max Na (max Nb (max Nc Ne)) := le_max_left _ _
      have h₂ : max Na (max Nb (max Nc Ne)) ≤ max 2 (max Na (max Nb (max Nc Ne))) := le_max_right _ _
      linarith
    have hNb' : Nb ≤ N := by
      have h₁ : Nb ≤ max Nb (max Nc Ne) := le_max_left _ _
      have h₂ : max Nb (max Nc Ne) ≤ max Na (max Nb (max Nc Ne)) := le_max_right _ _
      have h₃ : max Na (max Nb (max Nc Ne)) ≤ max 2 (max Na (max Nb (max Nc Ne))) := le_max_right _ _
      linarith
    have hNc' : Nc ≤ N := by
      have h₁ : Nc ≤ max Nc Ne := le_max_left _ _
      have h₂ : max Nc Ne ≤ max Nb (max Nc Ne) := le_max_right _ _
      have h₃ : max Nb (max Nc Ne) ≤ max Na (max Nb (max Nc Ne)) := le_max_right _ _
      have h₄ : max Na (max Nb (max Nc Ne)) ≤ max 2 (max Na (max Nb (max Nc Ne))) := le_max_right _ _
      linarith
    have hNe' : Ne ≤ N := by
      have h₁ : Ne ≤ max Nc Ne := le_max_right _ _
      have h₂ : max Nc Ne ≤ max Nb (max Nc Ne) := le_max_right _ _
      have h₃ : max Nb (max Nc Ne) ≤ max Na (max Nb (max Nc Ne)) := le_max_right _ _
      have h₄ : max Na (max Nb (max Nc Ne)) ≤ max 2 (max Na (max Nb (max Nc Ne))) := le_max_right _ _
      linarith
    -- Step 6: Define x = ℰ^{-5/12}, Δ = (9/5)x, K = ⌊ℰ²⌋
    have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    set L := Real.log (N : ℝ) ^ (3 - 2 * γ) with hLdef
    have hLnn : 0 ≤ L := Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N))) _
    set x := Real.exp (-(κ * L * (5 / 12 : ℝ))) with hxdef
    have hx0 : 0 < x := Real.exp_pos _
    have hE56 : calE γ κ N ^ (-(5 / 6 : ℝ)) = x ^ 2 := by
      have h₁ : calE γ κ N = Real.exp (κ * L) := by
        rw [U1539.calE, hLdef]
        <;> ring_nf
        <;> simp [Real.exp_mul]
        <;> field_simp
        <;> ring_nf
      rw [h₁]
      have h₂ : (Real.exp (κ * L) : ℝ) > 0 := Real.exp_pos _
      have h₃ : (Real.exp (κ * L) : ℝ) ^ (-(5 / 6 : ℝ)) = Real.exp (-(κ * L * (5 / 6 : ℝ))) := by
        rw [Real.rpow_neg (by positivity), Real.rpow_mul (by positivity)]
        <;> ring_nf
        <;> field_simp
        <;> ring_nf
      rw [h₃]
      have h₄ : Real.exp (-(κ * L * (5 / 6 : ℝ))) = (Real.exp (-(κ * L * (5 / 12 : ℝ)))) ^ 2 := by
        have h₅ : (-(κ * L * (5 / 6 : ℝ)) : ℝ) = 2 * (-(κ * L * (5 / 12 : ℝ)) : ℝ) := by ring
        rw [h₅]
        rw [Real.exp_two_mul]
        <;> ring_nf
        <;> field_simp [Real.exp_neg]
        <;> ring_nf
      rw [h₄]
      <;> simp [hxdef]
      <;> ring_nf
    have hE2 : calE γ κ N ^ (-(2 : ℝ)) = x ^ (24 / 5 : ℝ) := by
      have h₁ : calE γ κ N = Real.exp (κ * L) := by
        rw [U1539.calE, hLdef]
        <;> ring_nf
        <;> simp [Real.exp_mul]
        <;> field_simp
        <;> ring_nf
      rw [h₁]
      have h₂ : (Real.exp (κ * L) : ℝ) > 0 := Real.exp_pos _
      have h₃ : (Real.exp (κ * L) : ℝ) ^ (-(2 : ℝ)) = Real.exp (-(κ * L * 2)) := by
        rw [Real.rpow_neg (by positivity), Real.rpow_mul (by positivity)]
        <;> ring_nf
        <;> field_simp
        <;> ring_nf
      rw [h₃]
      have h₄ : Real.exp (-(κ * L * 2)) = (Real.exp (-(κ * L * (5 / 12 : ℝ)))) ^ (24 / 5 : ℝ) := by
        have h₅ : (-(κ * L * 2 : ℝ) : ℝ) = (24 / 5 : ℝ) * (-(κ * L * (5 / 12 : ℝ)) : ℝ) := by ring
        rw [h₅]
        rw [Real.exp_mul]
        <;> ring_nf
        <;> field_simp [Real.exp_neg]
        <;> ring_nf
      rw [h₄]
      <;> simp [hxdef]
      <;> ring_nf
    have hE23 : calE γ κ N ^ (2 : ℝ) = 1 / x ^ (24 / 5 : ℝ) := by
      have h₁ : calE γ κ N = Real.exp (κ * L) := by
        rw [U1539.calE, hLdef]
        <;> ring_nf
        <;> simp [Real.exp_mul]
        <;> field_simp
        <;> ring_nf
      rw [h₁]
      have h₂ : (Real.exp (κ * L) : ℝ) > 0 := Real.exp_pos _
      have h₃ : (Real.exp (κ * L) : ℝ) ^ (2 : ℝ) = Real.exp (κ * L * 2) := by
        rw [Real.rpow_mul (by positivity)]
        <;> ring_nf
        <;> field_simp
        <;> ring_nf
      rw [h₃]
      have h₄ : Real.exp (κ * L * 2) = 1 / (Real.exp (-(κ * L * 2)) : ℝ) := by
        rw [show (κ * L * 2 : ℝ) = -(-(κ * L * 2 : ℝ)) by ring]
        rw [Real.exp_neg]
        <;> field_simp
      rw [h₄]
      have h₅ : Real.exp (-(κ * L * 2)) = (Real.exp (-(κ * L * (5 / 12 : ℝ)))) ^ (24 / 5 : ℝ) := by
        have h₆ : (-(κ * L * 2 : ℝ) : ℝ) = (24 / 5 : ℝ) * (-(κ * L * (5 / 12 : ℝ)) : ℝ) := by ring
        rw [h₆]
        rw [Real.exp_mul]
        <;> ring_nf
        <;> field_simp [Real.exp_neg]
        <;> ring_nf
      rw [h₅]
      <;> simp [hxdef]
      <;> field_simp [Real.exp_neg]
      <;> ring_nf
      <;> simp_all [Real.exp_neg]
      <;> field_simp
      <;> ring_nf
    -- Step 7: Prove basic set and function properties (no Lemma4/Theorem2 needed)
    have h_subblock_eq : (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4) = Finset.Ioc (N / 2) (3 * N / 4) := by
      apply Finset.ext
      intro n
      simp [Finset.mem_filter, Finset.mem_Ioc]
      <;>
      (try omega) <;>
      (try
        {
          constructor <;> intro h <;>
          (try omega) <;>
          (try
            {
              cases' le_or_lt n (3 * N / 4) with h₁ h₁ <;>
              simp_all [Nat.div_eq_of_lt] <;>
              omega
            })
        }) <;>
      (try
        {
          by_cases h₁ : n ≤ 3 * N / 4 <;>
          simp_all [Nat.div_eq_of_lt] <;>
          omega
        })
    have h_indices_low_j1_spec : ∀ n, n ∈ indices_low_j1 γ N → N / 2 < n ∧ n ≤ 3 * N / 4 ∧ Odd (⌊F γ n⌋) := by
      intro n hn
      simp only [indices_low_j1, Finset.mem_filter, Finset.mem_Ioc] at hn
      have h₁ : N / 2 < n := by omega
      have h₂ : n ≤ N := by omega
      have h₃ : Even (nu γ n + 1) := by omega
      have h₄ : n ≤ 3 * N / 4 := by omega
      have h₅ : Odd (⌊F γ n⌋) := by
        have h₅₁ : Even (nu γ n + 1) := h₃
        have h₅₂ : Odd (nu γ n) := by
          rw [Int.even_iff] at h₅₁
          simp [Int.odd_iff_not_even, Int.emod_eq_of_lt] at h₅₁ ⊢
          <;> omega
        have h₅₃ : nu γ n = ⌊F γ n⌋ := rfl
        rw [h₅₃] at h₅₂
        exact h₅₂
      exact ⟨h₁, h₄, h₅⟩
    have h_blockPhase_eq : blockPhase (indices_low_j1 γ N) (fun n => F γ n - (1 : ℤ)) t = ‖∑ n in indices_low_j1 γ N, eC (t * (F γ n - 1))‖ := by
      simp [blockPhase]
      <;>
      simp_all [Finset.sum_congr]
      <;>
      norm_cast
      <;>
      ring_nf
    have h_shift_unimodular : ‖∑ n in indices_low_j1 γ N, eC (t * (F γ n - 1))‖ = ‖∑ n in indices_low_j1 γ N, eC (t * F γ n)‖ := by
      have h₁ : (∑ n in indices_low_j1 γ N, eC (t * (F γ n - 1))) = (∑ n in indices_low_j1 γ N, eC (-t) * eC (t * F γ n)) := by
        apply Finset.sum_congr rfl
        intro n hn
        have h₂ : eC (t * (F γ n - 1)) = eC (t * (F γ n : ℝ) - t) := by
          norm_cast
          <;> ring_nf
          <;> simp [Complex.ext_iff, eC, Complex.exp_sub, Complex.exp_neg]
          <;> field_simp [Real.exp_neg]
          <;> ring_nf
        rw [h₂]
        have h₃ : eC (t * (F γ n : ℝ) - t) = eC (-t) * eC (t * F γ n) := by
          rw [show (t * (F γ n : ℝ) - t : ℝ) = (-t : ℝ) + (t * F γ n : ℝ) by ring]
          rw [eC_add]
          <;> ring_nf
          <;> simp [Complex.ext_iff, eC, Complex.exp_neg]
          <;> field_simp [Real.exp_neg]
          <;> ring_nf
        rw [h₃]
        <;> ring_nf
      rw [h₁]
      have h₂ : ‖(∑ n in indices_low_j1 γ N, eC (-t) * eC (t * F γ n))‖ = ‖∑ n in indices_low_j1 γ N, eC (t * F γ n)‖ := by
        have h₃ : (∑ n in indices_low_j1 γ N, eC (-t) * eC (t * F γ n)) = eC (-t) * ∑ n in indices_low_j1 γ N, eC (t * F γ n) := by
          rw [Finset.mul_sum]
          <;> simp [mul_comm]
        rw [h₃]
        have h₄ : ‖(eC (-t) : ℂ)‖ = 1 := by
          simp [Complex.norm_eq_abs, eC, Complex.abs_exp, Complex.norm_re, Complex.norm_im, Real.exp_neg]
          <;> ring_nf
          <;> simp [Real.exp_zero]
        calc
          ‖(eC (-t) : ℂ) * ∑ n in indices_low_j1 γ N, eC (t * F γ n)‖ = ‖(eC (-t) : ℂ)‖ * ‖∑ n in indices_low_j1 γ N, eC (t * F γ n)‖ := by
            simp [norm_mul]
          _ = 1 * ‖∑ n in indices_low_j1 γ N, eC (t * F γ n)‖ := by rw [h₄]
          _ = ‖∑ n in indices_low_j1 γ N, eC (t * F γ n)‖ := by ring
      rw [h₂]
    have h_odd_sum_split : ‖∑ n in indices_low_j1 γ N, eC (t * F γ n)‖ ≤ ‖∑ n in (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4), eC (t * F γ n)‖ := by
      have h₁ : indices_low_j1 γ N ⊆ (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4) := by
        intro n hn
        simp only [indices_low_j1, Finset.mem_filter, Finset.mem_Ioc] at hn ⊢
        exact ⟨by omega, by omega, by omega⟩
      have h₂ : ‖∑ n in indices_low_j1 γ N, eC (t * F γ n)‖ ≤ ‖∑ n in (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4), eC (t * F γ n)‖ := by
        calc
          ‖∑ n in indices_low_j1 γ N, eC (t * F γ n)‖ = ‖∑ n in indices_low_j1 γ N, eC (t * F γ n)‖ := rfl
          _ ≤ ∑ n in indices_low_j1 γ N, ‖eC (t * F γ n)‖ := norm_sum_le _ _
          _ = ∑ n in indices_low_j1 γ N, 1 := by
            apply Finset.sum_congr rfl
            intro n _
            simp [Complex.norm_eq_abs, eC, Complex.abs_exp, Complex.norm_re, Complex.norm_im]
            <;> ring_nf
            <;> simp [Real.exp_zero]
          _ = (indices_low_j1 γ N).card := by simp [Finset.sum_const, Finset.card_univ]
          _ ≤ ((Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4)).card := by
            apply Finset.card_le_of_subset h₁
          _ = ∑ n in (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4), 1 := by
            simp [Finset.sum_const, Finset.card_univ]
          _ = ∑ n in (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4), ‖eC (t * F γ n)‖ := by
            apply Finset.sum_congr rfl
            intro n _
            simp [Complex.norm_eq_abs, eC, Complex.abs_exp, Complex.norm_re, Complex.norm_im]
            <;> ring_nf
            <;> simp [Real.exp_zero]
          _ ≥ ‖∑ n in (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4), eC (t * F γ n)‖ := by
            exact norm_sum_le _ _
      exact h₂
    -- Step 8: The main proof follows the structure of large_value_shift_of_lemma4
    -- We need to:
    -- 1. Relate the odd-indicator sum to the trapezoid expansion (using ψ(β) = trapL9 Δ (β - 1/2))
    -- 2. Use Lemma 4 to bound the error (adapt smoothing_l9 for odd indicator)
    -- 3. Fourier expand the trapezoid (adapt expansion_l9)
    -- 4. Truncate at |h| ≤ ℰ² (adapt truncated_l9)
    -- 5. Use numeric bounds to extract h (adapt numeric_l9 with x = ℰ^{-5/12})
    -- This requires adapting the entire DQLemma9 proof with new parameters
    -- OUT OF REACH: The full adaptation of DQLemma9.large_value_shift_of_lemma4 to the odd-indicator
    -- sub-block case with exponents -5/6, -2, and ℰ² is a significant formalization effort.
    -- Missing: (1) odd-indicator version of smoothing_l9, (2) odd-indicator version of expansion_l9,
    -- (3) adjusted numeric_l9 for x = ℰ^{-5/12}, K = ⌊ℰ²⌋, Δ = (9/5)x.
    sorry
  exact h_main

/-- LEAF: P0082 Theorem 2 page 354 with its proof in section 8 from Karacuba's
Lemma 10 page 370, applied on the sub-block `N/2 < n ≤ 3N/4` as used on page 370 after
display 41. HARD. For `X^{δ-1} < |β| ≤ 3 ℰ^2`, a range inside the range
`F(2N)^{-c} ≤ |β| ≤ F(N)^C` of Theorem 2, the unrestricted phase
`Σ e(β F(n))` over the sub-block is at most `N ℰ^{-2}` once `κ` is small. -/
theorem leaf_low_j1_subblock_theorem2 (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ β : ℝ,
          F γ N ^ (δ - 1) < |β| → |β| ≤ 3 * calE γ κ N ^ (2 : ℝ) →
            ‖∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4),
                eC (β * F γ n)‖ ≤ (N : ℝ) * calE γ κ N ^ (-(2 : ℝ)) := by
  have hT : LeanLab.ExceptionalSet.U1539.Theorem2 := by sorry
  have h_main : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ β : ℝ,
          F γ N ^ (δ - 1) < |β| → |β| ≤ 3 * calE γ κ N ^ (2 : ℝ) →
            ‖∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4),
                eC (β * F γ n)‖ ≤ (N : ℝ) * calE γ κ N ^ (-(2 : ℝ)) := by
    -- Use the shift_minor_of_theorem2 from DQLemma9 which gives a bound on Ioc (N/2) N
    -- The sub-block is a subset, so its sum is bounded by the full block sum
    have h_shift : ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ δ : ℝ, 0 < δ → δ < γ - 1 →
        ∃ κ₁ : ℝ, 0 < κ₁ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₁ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ β : ℝ, F γ N ^ (δ - 1) < |β| → |β| ≤ 2 * F γ N ^ δ + 2 →
            ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (β * F γ n)‖ ≤ N * calE γ κ N ^ (-(1 : ℝ)) := by
      intro γ hγ1 hγ2 δ hδ hδγ
      have hT2 : LeanLab.ExceptionalSet.U1539.Theorem2 := hT
      have h_shift' : ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ δ : ℝ, 0 < δ → δ < γ - 1 →
          ∃ κ₁ : ℝ, 0 < κ₁ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₁ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
            ∀ β : ℝ, F γ N ^ (δ - 1) < |β| → |β| ≤ 2 * F γ N ^ δ + 2 →
              ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (β * F γ n)‖ ≤ N * calE γ κ N ^ (-(1 : ℝ)) :=
        LeanLab.ExceptionalSet.DQLemma9.shift_minor_of_theorem2 hT2
      exact h_shift' γ hγ1 hγ2 δ hδ hδγ
    -- Choose δ₀ small enough so that δ < γ - 1 and 3 * calE² ≤ 2 * F^δ + 2 for large N
    have hγ : 1 < γ := h1
    have hγ' : γ < 3 / 2 := h2
    have hγ1 : γ - 1 > 0 := by linarith
    -- We need δ₀ < γ - 1 and also 3 * ℰ² ≤ 2 * F^δ + 2 eventually
    -- Since ℰ = exp(κ (log N)^{3-2γ}) grows slower than any power of F = exp((log N)^γ)
    -- we can choose δ₀ = min((γ - 1)/2, 1/2) and then for small κ, 3ℰ² ≤ F^δ for large N
    have hδ₀_exists : ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ < γ - 1 ∧ δ₀ < 1 / 2 := by
      refine' ⟨min ((γ - 1) / 2) (1 / 4), by
        have h₁ : 0 < (γ - 1 : ℝ) := by linarith
        have h₂ : 0 < (1 / 4 : ℝ) := by norm_num
        exact lt_min (by linarith) (by norm_num), _⟩
      have h₁ : (min ((γ - 1) / 2) (1 / 4) : ℝ) ≤ (γ - 1) / 2 := by apply min_le_left
      have h₂ : (γ - 1 : ℝ) / 2 < γ - 1 := by linarith
      linarith
    obtain ⟨δ₀, hδ₀_pos, hδ₀_lt_γ, hδ₀_lt_half⟩ := hδ₀_exists
    refine' ⟨δ₀, hδ₀_pos, fun δ hδ hδlt => ?_⟩
    have hδ_lt_γ : δ < γ - 1 := by linarith
    -- Use shift_minor_of_theorem2 with this δ
    obtain ⟨κ₁, hκ₁_pos, h_shift'⟩ := h_shift γ h1 h2 δ hδ hδ_lt_γ
    -- We need to ensure 3 * calE² ≤ 2 * F^δ + 2 for large N
    have h_calE_vs_F : ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → 3 * calE γ κ N ^ (2 : ℝ) ≤ 2 * F γ N ^ δ + 2 := by sorry
    obtain ⟨κ₂, hκ₂_pos, h_calE⟩ := h_calE_vs_F
    refine' ⟨min κ₁ κ₂, lt_min hκ₁_pos hκ₂_pos, fun κ hκ hκle => ?_⟩
    have hκle₁ : κ ≤ κ₁ := (min_le_left _ _).trans hκle
    have hκle₂ : κ ≤ κ₂ := (min_le_right _ _).trans hκle
    obtain ⟨N₁, hN₁⟩ := h_shift' κ hκ hκle₁
    obtain ⟨N₂, hN₂⟩ := h_calE κ hκ hκle₂
    refine' ⟨max N₁ N₂, fun N hN => ?_⟩
    have hN₁' : N₁ ≤ N := (le_max_left _ _).trans hN
    have hN₂' : N₂ ≤ N := (le_max_right _ _).trans hN
    intro β hβ_lo hβ_hi
    have hβ_hi' : |β| ≤ 2 * F γ N ^ δ + 2 := by
      have h₁ : 3 * calE γ κ N ^ (2 : ℝ) ≤ 2 * F γ N ^ δ + 2 := hN₂ N hN₂'
      linarith
    have h_full_bound : ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (β * F γ n)‖ ≤ N * calE γ κ N ^ (-(1 : ℝ)) :=
      hN₁ N hN₁' β hβ_lo hβ_hi'
    -- The sub-block is a subset of the full block
    have h_subblock_subset : (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4) ⊆ Finset.Ioc (N / 2) N := by
      apply Finset.filter_subset
    have h_subblock_bound : ‖∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4), eC (β * F γ n)‖ ≤ ‖∑ n ∈ Finset.Ioc (N / 2) N, eC (β * F γ n)‖ := by
      calc
        _ = ‖∑ n in (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4), eC (β * F γ n)‖ := by rfl
        _ ≤ ‖∑ n in Finset.Ioc (N / 2) N, eC (β * F γ n)‖ := by
          -- Use the fact that the norm of a sum over a subset is ≤ norm over the full set
          have h₁ : ∑ n in (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4), eC (β * F γ n) =
              ∑ n in Finset.Ioc (N / 2) N, if n ∈ (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4) then eC (β * F γ n) else 0 := by
            calc
              _ = ∑ n in (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4), eC (β * F γ n) := rfl
              _ = ∑ n in Finset.Ioc (N / 2) N, if n ∈ (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4) then eC (β * F γ n) else 0 := by
                rw [Finset.sum_filter]
                <;> simp [Finset.sum_ite_of_true]
                <;> aesop
          rw [h₁]
          have h₂ : ‖∑ n in Finset.Ioc (N / 2) N, (if n ∈ (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4) then eC (β * F γ n) else 0 : ℂ)‖ ≤ ‖∑ n in Finset.Ioc (N / 2) N, eC (β * F γ n)‖ := by
            calc
              _ ≤ ∑ n in Finset.Ioc (N / 2) N, ‖(if n ∈ (Finset.Ioc (N / 2) N).filter (fun n => n ≤ 3 * N / 4) then eC (β * F γ n) else 0 : ℂ)‖ := norm_sum_le _ _
              _ ≤ ∑ n in Finset.Ioc (N / 2) N, ‖eC (β * F γ n)‖ := by
                apply Finset.sum_le_sum
                intro n _
                split_ifs <;> simp_all [norm_zero]
                <;> aesop
              _ = ∑ n in Finset.Ioc (N / 2) N, ‖eC (β * F γ n)‖ := rfl
              _ ≥ ‖∑ n in Finset.Ioc (N / 2) N, eC (β * F γ n)‖ := by
                have h₃ : ‖∑ n in Finset.Ioc (N / 2) N, eC (β * F γ n)‖ ≤ ∑ n in Finset.Ioc (N / 2) N, ‖eC (β * F γ n)‖ := norm_sum_le _ _
                linarith
          exact h₂
    -- Relate N * calE^{-1} to N * calE^{-2}
    have h_calE_ge_one : 1 ≤ calE γ κ N := by
      exact feed1122_low_j1_calE_one_le γ κ (by linarith) N
    have h_calE_pow : calE γ κ N ^ (-(1 : ℝ)) ≥ calE γ κ N ^ (-(2 : ℝ)) := by
      apply Real.rpow_le_rpow_of_exponent_le
      · exact by linarith
      · norm_num
    -- The shift_minor_of_theorem2 gives N * calE^{-1}, but we need N * calE^{-2}
    -- We can adjust the parameters in Theorem 2 (choose smaller c, larger C) to get a better exponent
    -- OUT OF REACH: Strengthening the exponent from -1 to -2 requires re-proving shift_minor_of_theorem2
    -- with adjusted parameters c, C in Theorem2. The current proof uses c = 1-δ, C = (δ+γ-1)/2.
    -- To get N * calE^{-2}, we would need a stronger decay from Theorem 2, which may require
    -- different parameter choices or a stronger version of Theorem 2.
    sorry
  exact h_main

/-- `ℰ ≥ 1` for `κ ≥ 0`, since `log N ≥ 0`. Proved helper. -/
theorem feed1122_low_j1_calE_one_le (γ κ : ℝ) (hκ : 0 ≤ κ) (N : ℕ) :
    1 ≤ calE γ κ N := by
  unfold U1539.calE
  exact Real.one_le_exp (mul_nonneg hκ (Real.rpow_nonneg (Real.log_natCast_nonneg N) _))

/-- Assembly, page 370 closing argument of the proof of Lemma 9. Statement copied
verbatim from `leaf_low_j1_large_phase_localizes`. -/
theorem leaf_low_j1_large_phase_localizes_feed (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ a ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
            ∀ b ∈ oddDomain (F γ N ^ (6 * δ)) (F γ N) (calE γ κ N),
              (N : ℝ) * calE γ κ N ^ (-(5 / 6 : ℝ)) <
                  ‖blockPhase (indices_low_j1 γ N) (fun n => F γ n - (1 : ℤ)) (b - a)‖ →
                ∃ h : ℤ, |(b - a) - (h : ℝ) / 2| ≤ F γ N ^ (δ - 1) := by
  obtain ⟨κS, hκS, hS⟩ := leaf_low_j1_parity_shift γ h1 h2
  obtain ⟨δT, hδT, hT⟩ := leaf_low_j1_subblock_theorem2 γ h1 h2
  refine ⟨δT, hδT, fun δ hδ hδs => ?_⟩
  obtain ⟨κT, hκT, hT⟩ := hT δ hδ hδs
  refine ⟨min κS κT, lt_min hκS hκT, fun κ hκ hκs => ?_⟩
  obtain ⟨NS, hS⟩ := hS κ hκ (hκs.trans (min_le_left _ _))
  obtain ⟨NT, hT⟩ := hT κ hκ (hκs.trans (min_le_right _ _))
  refine ⟨max NS NT, fun N hN a ha b hb hlarge => ?_⟩
  have hNS : NS ≤ N := (le_max_left _ _).trans hN
  have hNT : NT ≤ N := (le_max_right _ _).trans hN
  have hE1 := feed1122_low_j1_calE_one_le γ κ hκ.le N
  have hba : |b - a| ≤ 2 * calE γ κ N ^ (2 / 3 : ℝ) := by
    have hb1 : b ≤ calE γ κ N ^ (2 / 3 : ℝ) := hb.2.2
    have hb2 : -(calE γ κ N ^ (2 / 3 : ℝ)) ≤ b := hb.2.1
    have ha1 : a ≤ calE γ κ N ^ (2 / 3 : ℝ) := ha.2.2
    have ha2 : -(calE γ κ N ^ (2 / 3 : ℝ)) ≤ a := ha.2.1
    rw [abs_le]
    constructor <;> linarith
  obtain ⟨h, hh, hbig⟩ := hS N hNS (b - a) hba hlarge
  refine ⟨h, ?_⟩
  by_contra hfar'
  have hfar := not_le.mp hfar'
  have h23 : calE γ κ N ^ (2 / 3 : ℝ) ≤ calE γ κ N ^ (2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hE1 (by norm_num)
  have hE2 : 0 ≤ calE γ κ N ^ (2 : ℝ) := Real.rpow_nonneg (by linarith) _
  have hrange : |(b - a) - (h : ℝ) / 2| ≤ 3 * calE γ κ N ^ (2 : ℝ) := by
    have hh' : |(h : ℝ) / 2| ≤ calE γ κ N ^ (2 : ℝ) / 2 := by
      rw [abs_div, abs_two]; linarith
    calc |(b - a) - (h : ℝ) / 2| ≤ |b - a| + |(h : ℝ) / 2| := abs_sub _ _
      _ ≤ 3 * calE γ κ N ^ (2 : ℝ) := by linarith
  have hsmall := hT N hNT ((b - a) - (h : ℝ) / 2) hfar hrange
  linarith

end LeanLab.ExceptionalSet.Decomp553c