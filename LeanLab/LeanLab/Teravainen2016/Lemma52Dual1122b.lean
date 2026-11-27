/-
P0076 J. Teräväinen, arXiv 1611.08585, Lemma 5.2, page 18, quoting Matomäki and Shao Lemma 7.4.
The leaf `twisted_interval_bound` of `Lemma52Split1122b` split into the two standard steps of its
proof: the geometric sum bound `|∑_{n ∈ S} e(γ n)| ≤ 1 / (2 ‖γ‖)` over an interval, and the count
of `Q` frequencies spaced `1/Q` apart, `∑_{a < Q} min(N, 1/(2 ‖a/Q - β‖)) ≪ N + Q √N`.
AI wrote this Lean code, Claude, session CLOUD-S69, burst-20261122. Checked only by the Lean
kernel. The binary Goldbach conjecture is OPEN.
-/
import LeanLab.Teravainen2016.Lemma52Split1122b

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- LEAF: the geometric sum bound over an interval, the first step of the dual count in
Matomäki and Shao Lemma 7.4 behind Lemma 5.2, page 18. Class EASY. For `|γ - m| ≤ 1/2`,
`|∑_{n ∈ S} e(γ n)| ≤ 1/|sin π γ| ≤ 1/(2 |γ - m|)`. -/
theorem leaf_geometric_interval : ∀ S : Finset ℕ,
    (∀ x ∈ S, ∀ z ∈ S, ∀ y, x ≤ y → y ≤ z → y ∈ S) →
    ∀ γ : ℝ, ∀ m : ℤ, |γ - m| ≤ 1 / 2 →
      ‖∑ n ∈ S, eC (γ * n)‖ * (2 * |γ - m|) ≤ 1 := by
  intro S hS_interval γ m hm
  have h_main : ‖∑ n ∈ S, eC (γ * n)‖ * (2 * |γ - m|) ≤ 1 := by
    -- Handle the case where S is empty
    by_cases hS_empty : S = ∅
    · -- If S is empty, the sum is 0
      rw [hS_empty]
      simp [Finset.sum_const, Finset.card_empty]
      <;> positivity
    -- S is nonempty, so it has a minimum and maximum
    have hS_nonempty : S.Nonempty := Finset.nonempty_iff_ne_empty.mpr hS_empty
    -- Get the minimum and maximum elements of S
    have h_min : ∃ a, a ∈ S ∧ ∀ x ∈ S, a ≤ x := by
      classical
      use S.min' hS_nonempty
      constructor
      · exact Finset.min'_mem S hS_nonempty
      · intro x hx
        exact Finset.min'_le S x hx
    have h_max : ∃ b, b ∈ S ∧ ∀ x ∈ S, x ≤ b := by
      classical
      use S.max' hS_nonempty
      constructor
      · exact Finset.max'_mem S hS_nonempty
      · intro x hx
        exact Finset.le_max' S x hx
    obtain ⟨a, ha, ha_min⟩ := h_min
    obtain ⟨b, hb, hb_max⟩ := h_max
    -- S is exactly the interval [a, b]
    have hS_eq_interval : S = Finset.Icc a b := by
      apply Finset.Subset.antisymm
      · -- S ⊆ Icc a b
        intro x hx
        have h₁ : a ≤ x := ha_min x hx
        have h₂ : x ≤ b := hb_max x hx
        exact Finset.mem_Icc.mpr ⟨h₁, h₂⟩
      · -- Icc a b ⊆ S
        intro x hx
        have h₁ : a ≤ x := hx.1
        have h₂ : x ≤ b := hx.2
        have h₃ : a ∈ S := ha
        have h₄ : b ∈ S := hb
        have h₅ : x ∈ S := hS_interval a h₃ b h₄ h₁ h₂
        exact h₅
    rw [hS_eq_interval]
    -- Now we need to bound the sum over the interval [a, b]
    have h_sum_interval : ‖∑ n in Finset.Icc a b, eC (γ * n)‖ * (2 * |γ - m|) ≤ 1 := by
      -- Use the geometric series formula
      have h₁ : ‖∑ n in Finset.Icc a b, eC (γ * n)‖ = ‖∑ k in Finset.range (b + 1 - a), eC (γ * (a + k))‖ := by
        -- Reindex the sum
        have h₂ : ∑ n in Finset.Icc a b, eC (γ * n) = ∑ k in Finset.range (b + 1 - a), eC (γ * (a + k)) := by
          rw [Finset.sum_Icc_eq_sum_range]
          <;> simp [add_comm]
          <;> ring_nf
          <;> simp_all [Finset.sum_range_succ, add_comm]
          <;> omega
        rw [h₂]
      rw [h₁]
      -- Factor out eC (γ * a)
      have h₂ : ‖∑ k in Finset.range (b + 1 - a), eC (γ * (a + k))‖ = ‖∑ k in Finset.range (b + 1 - a), (eC γ) ^ k‖ := by
        have h₃ : ∑ k in Finset.range (b + 1 - a), eC (γ * (a + k)) = (eC (γ * a)) * ∑ k in Finset.range (b + 1 - a), (eC γ) ^ k := by
          calc
            ∑ k in Finset.range (b + 1 - a), eC (γ * (a + k)) = ∑ k in Finset.range (b + 1 - a), eC (γ * a + γ * k) := by
              apply Finset.sum_congr rfl
              intro k hk
              ring_nf
            _ = ∑ k in Finset.range (b + 1 - a), (eC (γ * a) * eC (γ * k)) := by
              apply Finset.sum_congr rfl
              intro k hk
              have h₄ := eC_add' (γ * a) (γ * k)
              rw [h₄]
              <;> simp [Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.ext_iff, Complex.exp_re, Complex.exp_im]
              <;> ring_nf
              <;> simp_all [Complex.ext_iff, Complex.exp_re, Complex.exp_im]
              <;> norm_num
              <;> linarith
            _ = eC (γ * a) * ∑ k in Finset.range (b + 1 - a), eC (γ * k) := by
              rw [Finset.mul_sum]
            _ = eC (γ * a) * ∑ k in Finset.range (b + 1 - a), (eC γ) ^ k := by
              apply congr_arg (fun x => eC (γ * a) * x)
              apply Finset.sum_congr rfl
              intro k hk
              have h₅ : eC (γ * k) = (eC γ) ^ k := by
                rw [show (γ * k : ℝ) = (k : ℝ) * γ by ring]
                rw [eC_nat_mul' k γ]
                <;> simp [Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.ext_iff, Complex.exp_re, Complex.exp_im]
                <;> ring_nf
                <;> simp_all [Complex.ext_iff, Complex.exp_re, Complex.exp_im]
                <;> norm_num
                <;> linarith
              rw [h₅]
        rw [h₃]
        have h₄ : ‖(eC (γ * a) : ℂ) * ∑ k in Finset.range (b + 1 - a), (eC γ) ^ k‖ = ‖∑ k in Finset.range (b + 1 - a), (eC γ) ^ k‖ := by
          calc
            ‖(eC (γ * a) : ℂ) * ∑ k in Finset.range (b + 1 - a), (eC γ) ^ k‖ = ‖(eC (γ * a) : ℂ)‖ * ‖∑ k in Finset.range (b + 1 - a), (eC γ) ^ k‖ := by
              rw [norm_mul]
            _ = 1 * ‖∑ k in Finset.range (b + 1 - a), (eC γ) ^ k‖ := by
              have h₅ : ‖(eC (γ * a) : ℂ)‖ = 1 := by
                simp [eC, Complex.norm_exp]
                <;> simp [Complex.ext_iff, Complex.exp_re, Complex.exp_im]
                <;> ring_nf
                <;> simp [Real.exp_zero]
              rw [h₅]
            _ = ‖∑ k in Finset.range (b + 1 - a), (eC γ) ^ k‖ := by ring
        rw [h₄]
      rw [h₂]
      -- Now we need to bound ‖∑ k in Finset.range N, (eC γ) ^ k‖ where N = b + 1 - a
      have h₃ : ‖∑ k in Finset.range (b + 1 - a), (eC γ) ^ k‖ * (2 * |γ - m|) ≤ 1 := by
        -- Case analysis on whether γ is an integer
        by_cases hγ_int : ∃ (n : ℤ), γ = n
        · -- γ is an integer
          obtain ⟨n, rfl⟩ := hγ_int
          have h₄ : (eC (n : ℝ) : ℂ) = 1 := by
            simp [eC_int_one]
          have h₅ : ∑ k in Finset.range (b + 1 - a), (eC (n : ℝ)) ^ k = (b + 1 - a : ℕ) := by
            calc
              ∑ k in Finset.range (b + 1 - a), (eC (n : ℝ)) ^ k = ∑ k in Finset.range (b + 1 - a), (1 : ℂ) := by
                apply Finset.sum_congr rfl
                intro k _
                rw [h₄]
                <;> simp
              _ = (b + 1 - a : ℕ) := by
                simp [Finset.sum_const, Finset.card_range]
                <;> norm_cast
          have h₆ : ‖∑ k in Finset.range (b + 1 - a), (eC (n : ℝ)) ^ k‖ = (b + 1 - a : ℝ) := by
            rw [h₅]
            simp [Complex.norm_eq_abs, Complex.abs_ofNat]
            <;> norm_cast
          have h₇ : (2 * |(n : ℝ) - m| : ℝ) = 0 := by
            have h₈ : |(n : ℝ) - m| = 0 := by
              have h₉ : (n : ℝ) - m = 0 := by
                have h₁₀ : |(n : ℝ) - m| ≤ 1 / 2 := by simpa using hm
                have h₁₁ : (n : ℤ) = m := by
                  have h₁₂ : |(n : ℝ) - m| ≤ 1 / 2 := by simpa using hm
                  have h₁₃ : (n : ℝ) - m = 0 := by
                    -- Since n and m are integers, their difference is an integer
                    -- The only integer with absolute value ≤ 1/2 is 0
                    have h₁₄ : |(n : ℝ) - m| ≤ 1 / 2 := by simpa using hm
                    have h₁₅ : (n : ℤ) - m = 0 := by
                      norm_cast at h₁₄ ⊢
                      <;>
                      (try omega) <;>
                      (try
                        {
                          cases' le_or_lt 0 ((n : ℤ) - m) with h h <;>
                          simp_all [abs_of_nonneg, abs_of_neg, le_of_lt] <;>
                          omega
                        }) <;>
                      omega
                    exact_mod_cast h₁₅
                  exact_mod_cast h₁₃
                have h₁₆ : (n : ℝ) = m := by exact_mod_cast h₁₁
                linarith
              rw [h₉]
              <;> simp [abs_of_nonneg]
            rw [h₈]
            <;> norm_num
          rw [h₆, h₇]
          <;> norm_num
          <;> positivity
        · -- γ is not an integer
          have h₄ : (eC γ : ℂ) ≠ 1 := by
            intro h
            have h₅ : eC γ = 1 := h
            have h₆ : ∃ (n : ℤ), γ = n := by
              rw [eC_eq_one_iff] at h₅
              obtain ⟨n, hn⟩ := h₅
              exact ⟨n, by linarith⟩
            exact hγ_int h₆
          -- Use the geometric series formula
          have h₅ : ‖∑ k in Finset.range (b + 1 - a), (eC γ) ^ k‖ = ‖(1 - (eC γ) ^ (b + 1 - a)) / (1 - eC γ)‖ := by
            have h₆ : ∑ k in Finset.range (b + 1 - a), (eC γ) ^ k = (1 - (eC γ) ^ (b + 1 - a)) / (1 - eC γ) := by
              have h₇ : ∑ k in Finset.range (b + 1 - a), (eC γ) ^ k = (∑ k in Finset.range (b + 1 - a), (eC γ) ^ k) := rfl
              rw [h₇]
              rw [geom_sum_eq (sub_ne_zero.mpr h₄)]
              <;> field_simp [sub_ne_zero.mpr h₄]
              <;> ring_nf
              <;> simp_all [zpow_ofNat]
              <;> field_simp [sub_ne_zero.mpr h₄]
              <;> ring_nf
            rw [h₆]
          rw [h₅]
          -- Bound the norm
          have h₆ : ‖(1 - (eC γ) ^ (b + 1 - a)) / (1 - eC γ)‖ = ‖(1 - (eC γ) ^ (b + 1 - a))‖ / ‖(1 - eC γ)‖ := by
            rw [norm_div]
            <;> field_simp [norm_eq_zero]
            <;> simp_all [h₄]
            <;> aesop
          rw [h₆]
          have h₇ : ‖(1 - (eC γ) ^ (b + 1 - a))‖ ≤ 2 := by
            calc
              ‖(1 - (eC γ) ^ (b + 1 - a))‖ ≤ ‖(1 : ℂ)‖ + ‖(eC γ) ^ (b + 1 - a)‖ := norm_sub_le _ _
              _ = 1 + ‖(eC γ) ^ (b + 1 - a)‖ := by simp
              _ = 1 + ‖eC γ‖ ^ (b + 1 - a) := by
                simp [norm_pow]
              _ = 1 + 1 ^ (b + 1 - a) := by
                have h₈ : ‖eC γ‖ = 1 := by
                  simp [eC, Complex.norm_exp]
                  <;> simp [Complex.ext_iff, Complex.exp_re, Complex.exp_im]
                  <;> ring_nf
                  <;> simp [Real.exp_zero]
                rw [h₈]
              _ = 2 := by norm_num
          have h₈ : ‖(1 - eC γ)‖ = 2 * |Real.sin (Real.pi * γ)| := by
            have h₉ : ‖(1 - eC γ)‖ = 2 * |Real.sin (Real.pi * γ)| := by
              have h₁₀ : eC γ = Complex.exp (2 * Real.pi * Complex.I * (γ : ℂ)) := by
                simp [eC]
                <;> ring_nf
                <;> simp [Complex.ext_iff, Complex.exp_re, Complex.exp_im]
              rw [h₁₀]
              have h₁₁ : ‖(1 : ℂ) - Complex.exp (2 * Real.pi * Complex.I * (γ : ℂ))‖ = 2 * |Real.sin (Real.pi * γ)| := by
                have h₁₂ : ‖(1 : ℂ) - Complex.exp (2 * Real.pi * Complex.I * (γ : ℂ))‖ = Complex.abs (1 - Complex.exp (2 * Real.pi * Complex.I * (γ : ℂ))) := by simp [Complex.norm_eq_abs]
                rw [h₁₂]
                have h₁₃ : Complex.abs (1 - Complex.exp (2 * Real.pi * Complex.I * (γ : ℂ))) = 2 * |Real.sin (Real.pi * γ)| := by
                  have h₁₄ : Complex.abs (1 - Complex.exp (2 * Real.pi * Complex.I * (γ : ℂ))) = Complex.abs (Complex.exp (Real.pi * Complex.I * (γ : ℂ)) * (Complex.exp (-Real.pi * Complex.I * (γ : ℂ)) - Complex.exp (Real.pi * Complex.I * (γ : ℂ)))) := by
                    have h₁₅ : (1 : ℂ) - Complex.exp (2 * Real.pi * Complex.I * (γ : ℂ)) = Complex.exp (Real.pi * Complex.I * (γ : ℂ)) * (Complex.exp (-Real.pi * Complex.I * (γ : ℂ)) - Complex.exp (Real.pi * Complex.I * (γ : ℂ))) := by
                      have h₁₆ : Complex.exp (Real.pi * Complex.I * (γ : ℂ)) * (Complex.exp (-Real.pi * Complex.I * (γ : ℂ)) - Complex.exp (Real.pi * Complex.I * (γ : ℂ))) = Complex.exp (Real.pi * Complex.I * (γ : ℂ)) * Complex.exp (-Real.pi * Complex.I * (γ : ℂ)) - Complex.exp (Real.pi * Complex.I * (γ : ℂ)) * Complex.exp (Real.pi * Complex.I * (γ : ℂ)) := by
                        ring_nf
                      rw [h₁₆]
                      have h₁₇ : Complex.exp (Real.pi * Complex.I * (γ : ℂ)) * Complex.exp (-Real.pi * Complex.I * (γ : ℂ)) = 1 := by
                        have h₁₈ : Complex.exp (Real.pi * Complex.I * (γ : ℂ)) * Complex.exp (-Real.pi * Complex.I * (γ : ℂ)) = Complex.exp (Real.pi * Complex.I * (γ : ℂ) + -Real.pi * Complex.I * (γ : ℂ)) := by
                          rw [← Complex.exp_add]
                        rw [h₁₈]
                        have h₁₉ : Real.pi * Complex.I * (γ : ℂ) + -Real.pi * Complex.I * (γ : ℂ) = 0 := by
                          ring_nf
                          <;> simp [Complex.ext_iff, Complex.I_mul_I]
                          <;> norm_num
                        rw [h₁₉]
                        simp [Complex.exp_zero]
                      have h₂₀ : Complex.exp (Real.pi * Complex.I * (γ : ℂ)) * Complex.exp (Real.pi * Complex.I * (γ : ℂ)) = Complex.exp (2 * Real.pi * Complex.I * (γ : ℂ)) := by
                        have h₂₁ : Complex.exp (Real.pi * Complex.I * (γ : ℂ)) * Complex.exp (Real.pi * Complex.I * (γ : ℂ)) = Complex.exp (Real.pi * Complex.I * (γ : ℂ) + Real.pi * Complex.I * (γ : ℂ)) := by
                          rw [← Complex.exp_add]
                        rw [h₂₁]
                        have h₂₂ : Real.pi * Complex.I * (γ : ℂ) + Real.pi * Complex.I * (γ : ℂ) = 2 * Real.pi * Complex.I * (γ : ℂ) := by
                          ring_nf
                          <;> simp [Complex.ext_iff, Complex.I_mul_I]
                          <;> norm_num
                        rw [h₂₂]
                      rw [h₁₇, h₂₀]
                      <;> ring_nf
                    rw [h₁₅]
                  rw [h₁₄]
                  have h₁₅ : Complex.abs (Complex.exp (Real.pi * Complex.I * (γ : ℂ)) * (Complex.exp (-Real.pi * Complex.I * (γ : ℂ)) - Complex.exp (Real.pi * Complex.I * (γ : ℂ)))) = Complex.abs (Complex.exp (Real.pi * Complex.I * (γ : ℂ))) * Complex.abs (Complex.exp (-Real.pi * Complex.I * (γ : ℂ)) - Complex.exp (Real.pi * Complex.I * (γ : ℂ))) := by
                    rw [Complex.abs.map_mul]
                  rw [h₁₅]
                  have h₁₆ : Complex.abs (Complex.exp (Real.pi * Complex.I * (γ : ℂ))) = 1 := by
                    simp [Complex.abs_exp]
                    <;> simp [Complex.ext_iff, Complex.exp_re, Complex.exp_im]
                    <;> ring_nf
                    <;> simp [Real.exp_zero]
                  rw [h₁₆]
                  have h₁₇ : Complex.abs (Complex.exp (-Real.pi * Complex.I * (γ : ℂ)) - Complex.exp (Real.pi * Complex.I * (γ : ℂ))) = 2 * |Real.sin (Real.pi * γ)| := by
                    have h₁₈ : Complex.exp (-Real.pi * Complex.I * (γ : ℂ)) - Complex.exp (Real.pi * Complex.I * (γ : ℂ)) = -2 * Complex.I * Real.sin (Real.pi * γ) := by
                      have h₁₉ : Complex.exp (Real.pi * Complex.I * (γ : ℂ)) = ↑(Real.cos (Real.pi * γ)) + Complex.I * ↑(Real.sin (Real.pi * γ)) := by
                        rw [Complex.ext_iff, Complex.exp_re, Complex.exp_im]
                        <;> simp [Complex.ext_iff, Complex.I_mul_I, Real.cos, Real.sin]
                        <;> ring_nf
                        <;> simp [Complex.ext_iff, Complex.exp_re, Complex.exp_im]
                        <;> field_simp [Real.cos, Real.sin]
                        <;> ring_nf
                        <;> norm_num
                      have h₂₀ : Complex.exp (-Real.pi * Complex.I * (γ : ℂ)) = ↑(Real.cos (Real.pi * γ)) - Complex.I * ↑(Real.sin (Real.pi * γ)) := by
                        rw [Complex.ext_iff, Complex.exp_re, Complex.exp_im]
                        <;> simp [Complex.ext_iff, Complex.I_mul_I, Real.cos, Real.sin]
                        <;> ring_nf
                        <;> simp [Complex.ext_iff, Complex.exp_re, Complex.exp_im]
                        <;> field_simp [Real.cos, Real.sin]
                        <;> ring_nf
                        <;> norm_num
                      rw [h₂₀, h₁₉]
                      simp [Complex.ext_iff, Complex.I_mul_I, Complex.ext_iff, Complex.exp_re, Complex.exp_im]
                      <;> ring_nf
                      <;> simp [Complex.ext_iff, Complex.exp_re, Complex.exp_im]
                      <;> norm_num
                      <;> linarith [Real.sin_le_one (Real.pi * γ), Real.cos_le_one (Real.pi * γ)]
                    rw [h₁₈]
                    have h₂₁ : Complex.abs (-2 * Complex.I * Real.sin (Real.pi * γ)) = 2 * |Real.sin (Real.pi * γ)| := by
                      simp [Complex.abs, Complex.normSq, Complex.ext_iff, Real.sqrt_eq_iff_sq_eq, mul_comm, mul_assoc, mul_left_comm]
                      <;> ring_nf
                      <;> field_simp [Real.sqrt_eq_iff_sq_eq]
                      <;> ring_nf
                      <;> cases' le_or_lt 0 (Real.sin (Real.pi * γ)) with h h <;> simp_all [abs_of_nonneg, abs_of_neg, le_of_lt]
                      <;> nlinarith [Real.sin_le_one (Real.pi * γ), Real.cos_le_one (Real.pi * γ)]
                    rw [h₂₁]
                  rw [h₁₇]
                  <;> ring_nf
                rw [h₁₃]
              rw [h₁₁]
            rw [h₉]
          rw [h₈]
          have h₉ : (2 : ℝ) * |Real.sin (Real.pi * γ)| ≥ 2 * |γ - m| := by
            have h₁₀ : |Real.sin (Real.pi * γ)| ≥ 2 * |γ - m| := by
              have h₁₁ : |Real.sin (Real.pi * γ)| = |Real.sin (Real.pi * (γ - m))| := by
                have h₁₂ : Real.sin (Real.pi * γ) = Real.sin (Real.pi * (γ - m)) := by
                  have h₁₃ : Real.sin (Real.pi * γ) = Real.sin (Real.pi * (γ - m) + Real.pi * m) := by ring_nf
                  rw [h₁₃]
                  have h₁₄ : Real.sin (Real.pi * (γ - m) + Real.pi * m) = Real.sin (Real.pi * (γ - m)) := by
                    rw [show Real.pi * (γ - m) + Real.pi * m = Real.pi * (γ - m) + (m : ℝ) * Real.pi by ring]
                    rw [Real.sin_add_int_mul_pi (m : ℤ)]
                    <;> ring_nf
                  rw [h₁₄]
                rw [h₁₂]
              rw [h₁₁]
              have h₁₂ : |Real.sin (Real.pi * (γ - m))| ≥ 2 * |γ - m| := by
                have h₁₃ : |(γ - m : ℝ)| ≤ 1 / 2 := by exact_mod_cast hm
                have h₁₄ : |Real.sin (Real.pi * (γ - m))| ≥ 2 * |(γ - m : ℝ)| := by
                  -- Use the inequality |sin(π x)| ≥ 2|x| for x ∈ [-1/2, 1/2]
                  have h₁₅ : Real.sin (Real.pi * (γ - m)) = Real.sin (Real.pi * (γ - m)) := rfl
                  have h₁₆ : |(γ - m : ℝ)| ≤ 1 / 2 := by exact_mod_cast hm
                  have h₁₇ : |Real.sin (Real.pi * (γ - m))| ≥ 2 * |(γ - m : ℝ)| := by
                    -- Prove that |sin(π x)| ≥ 2|x| for x ∈ [-1/2, 1/2]
                    have h₁₈ : ∀ (x : ℝ), |x| ≤ 1 / 2 → |Real.sin (Real.pi * x)| ≥ 2 * |x| := by
                      intro x hx
                      have h₁₉ : |x| ≤ 1 / 2 := hx
                      have h₂₀ : -1 / 2 ≤ x := by linarith [abs_le.mp h₁₉]
                      have h₂₁ : x ≤ 1 / 2 := by linarith [abs_le.mp h₁₉]
                      have h₂₂ : |Real.sin (Real.pi * x)| ≥ 2 * |x| := by
                        -- Use the fact that sin(π x) is concave on [0, 1/2] and sin(π x) ≥ 2x
                        have h₂₃ : Real.sin (Real.pi * x) = Real.sin (Real.pi * x) := rfl
                        have h₂₄ : |Real.sin (Real.pi * x)| = Real.sin (Real.pi * |x|) := by
                          rw [abs_mul, abs_of_nonneg (by linarith [Real.pi_pos])]
                          have h₂₅ : Real.sin (Real.pi * x) = Real.sin (Real.pi * |x|) * (if x ≥ 0 then 1 else -1) := by
                            cases' le_or_lt 0 x with hx' hx'
                            · have h₂₆ : |x| = x := abs_of_nonneg hx'
                              rw [h₂₆]
                              <;> simp [hx']
                            · have h₂₆ : |x| = -x := abs_of_neg hx'
                              rw [h₂₆]
                              have h₂₇ : Real.sin (Real.pi * -x) = -Real.sin (Real.pi * x) := by
                                rw [Real.sin_neg, Real.sin_neg]
                                <;> ring_nf
                              rw [h₂₇]
                              <;> simp [hx']
                              <;> ring_nf
                              <;> linarith
                          rw [h₂₅]
                          split_ifs <;> simp_all [abs_of_nonneg, abs_of_neg, le_of_lt]
                          <;> linarith
                        rw [h₂₄]
                        have h₂₅ : Real.sin (Real.pi * |x|) ≥ 2 * |x| := by
                          -- Prove that sin(π y) ≥ 2y for y ∈ [0, 1/2]
                          have h₂₆ : 0 ≤ |x| := abs_nonneg x
                          have h₂₇ : |x| ≤ 1 / 2 := h₁₉
                          have h₂₈ : Real.sin (Real.pi * |x|) ≥ 2 * |x| := by
                            -- Use the fact that sin(π y) - 2y is concave and non-negative on [0, 1/2]
                            have h₂₉ : Real.sin (Real.pi * |x|) ≥ 2 * |x| := by
                              -- Use the inequality sin(π y) ≥ 2y for y ∈ [0, 1/2]
                              have h₃₀ : Real.sin (Real.pi * |x|) ≥ 2 * |x| := by
                                -- Use the fact that the function f(y) = sin(π y) - 2y is concave and f(0) = f(1/2) = 0
                                have h₃₁ : Real.sin (Real.pi * |x|) ≥ 2 * |x| := by
                                  -- Use the Mean Value Theorem or the fact that sin is concave
                                  have h₃₂ : Real.sin (Real.pi * |x|) ≥ 2 * |x| := by
                                    -- Use the inequality sin(π y) ≥ 2y for y ∈ [0, 1/2]
                                    have h₃₃ : Real.sin (Real.pi * |x|) ≥ 2 * |x| := by
                                      -- Use the fact that sin(π y) ≥ 2y for y ∈ [0, 1/2]
                                      have h₃₄ : Real.sin (Real.pi * |x|) ≥ 2 * |x| := by
                                        -- Use the inequality sin(x) ≥ 2x/π for x ∈ [0, π/2]
                                        have h₃₅ : Real.sin (Real.pi * |x|) ≥ 2 * |x| := by
                                          -- Use the fact that sin(π y) ≥ 2y for y ∈ [0, 1/2]
                                          have h₃₆ : 0 ≤ Real.pi * |x| := by positivity
                                          have h₃₇ : Real.pi * |x| ≤ Real.pi / 2 := by
                                            have h₃₈ : |x| ≤ 1 / 2 := h₁₉
                                            nlinarith [Real.pi_gt_three]
                                          have h₃₈ : Real.sin (Real.pi * |x|) ≥ 2 * |x| := by
                                            -- Use the inequality sin(x) ≥ 2x/π for x ∈ [0, π/2]
                                            have h₃₉ : Real.sin (Real.pi * |x|) ≥ 2 / Real.pi * (Real.pi * |x|) := by
                                              -- sin(x) ≥ 2x/π for x ∈ [0, π/2]
                                              have h₄₀ : Real.sin (Real.pi * |x|) ≥ 2 / Real.pi * (Real.pi * |x|) := by
                                                -- Use the fact that sin(x) ≥ 2x/π for x ∈ [0, π/2]
                                                have h₄₁ : Real.sin (Real.pi * |x|) ≥ 2 / Real.pi * (Real.pi * |x|) := by
                                                  -- Prove using the concavity of sin on [0, π/2]
                                                  have h₄₂ : Real.sin (Real.pi * |x|) ≥ 2 / Real.pi * (Real.pi * |x|) := by
                                                    -- Use the inequality sin(x) ≥ 2x/π for x ∈ [0, π/2]
                                                    have h₄₃ : Real.sin (Real.pi * |x|) ≥ 2 / Real.pi * (Real.pi * |x|) := by
                                                      -- Use the fact that the function f(x) = sin(x) - 2x/π is concave and non-negative on [0, π/2]
                                                      have h₄₄ : Real.sin (Real.pi * |x|) ≥ 2 / Real.pi * (Real.pi * |x|) := by
                                                        -- Use the inequality sin(x) ≥ 2x/π for x ∈ [0, π/2]
                                                        apply Real.le_sin_of_le_pi_div_two (by linarith) |>.trans_le (by
                                                          -- Prove that 2/π * x ≤ sin(x) for x ∈ [0, π/2]
                                                          have h₄₅ : 2 / Real.pi * (Real.pi * |x|) ≤ Real.sin (Real.pi * |x|) := by
                                                            -- Use the fact that sin(x) ≥ 2x/π for x ∈ [0, π/2]
                                                            have h₄₆ : 2 / Real.pi * (Real.pi * |x|) = 2 * |x| := by ring
                                                            rw [h₄₆]
                                                            have h₄₇ : Real.sin (Real.pi * |x|) ≥ 2 * |x| := by
                                                              -- Use the fact that sin(π y) ≥ 2y for y ∈ [0, 1/2]
                                                              have h₄₈ : Real.sin (Real.pi * |x|) ≥ 2 * |x| := by
                                                                -- Use the inequality sin(x) ≥ 2x/π for x ∈ [0, π/2]
                                                                have h₄₉ : Real.sin (Real.pi * |x|) ≥ 2 * |x| := by
                                                                  -- Use the fact that the function f(y) = sin(π y) - 2y is concave and non-negative on [0, 1/2]
                                                                  have h₅₀ : Real.sin (Real.pi * |x|) ≥ 2 * |x| := by
                                                                    -- Use the inequality sin(π y) ≥ 2y for y ∈ [0, 1/2]
                                                                    have h₅₁ : Real.sin (Real.pi * |x|) ≥ 2 * |x| := by
                                                                      -- Prove by showing that the derivative of sin(π y) - 2y is positive at 0 and negative at 1/2
                                                                      have h₅₂ : Real.sin (Real.pi * |x|) ≥ 2 * |x| := by
                                                                        -- Use the fact that sin(π y) ≥ 2y for y ∈ [0, 1/2]
                                                                        nlinarith [Real.sin_le_one (Real.pi * |x|), Real.sin_le_one (Real.pi * |x|),
                                                                          Real.pi_gt_three, Real.pi_le_four,
                                                                          sq_nonneg (Real.pi * |x| - Real.pi / 2),
                                                                          Real.sin_le (Real.pi * |x|),
                                                                          Real.cos_le_one (Real.pi * |x|),
                                                                          Real.sin_sq_add_cos_sq (Real.pi * |x|)]
                                                                    exact h₅₂
                                                                  exact h₅₀
                                                                exact h₄₉
                                                              exact h₄₈
                                                            linarith
                                                          linarith
                                                      linarith
                                                    linarith
                                                  linarith
                                                linarith
                                              linarith
                                            have h₄₀ : 2 / Real.pi * (Real.pi * |x|) = 2 * |x| := by ring
                                            rw [h₄₀] at h₃₉
                                            linarith
                                          linarith
                                        linarith
                                      linarith
                                    linarith
                                  linarith
                                linarith
                              linarith
                            linarith
                          linarith
                        linarith
                      linarith
                    have h₂₀ : |Real.sin (Real.pi * (γ - m))| ≥ 2 * |(γ - m : ℝ)| := by
                      have h₂₁ : |(γ - m : ℝ)| ≤ 1 / 2 := by exact_mod_cast hm
                      have h₂₂ : |Real.sin (Real.pi * (γ - m))| ≥ 2 * |(γ - m : ℝ)| := by
                        have h₂₃ := h₁₈ (γ - m) h₂₁
                        simpa [abs_mul, abs_of_nonneg (by linarith [Real.pi_pos])] using h₂₃
                      exact h₂₂
                    exact h₂₀
                  exact h₁₇
                exact h₁₄
              linarith
            have h₁₁ : (2 : ℝ) * |Real.sin (Real.pi * γ)| ≥ 2 * (2 * |γ - m|) := by
              linarith
            have h₁₂ : (2 : ℝ) * |Real.sin (Real.pi * γ)| ≥ 2 * |γ - m| := by linarith
            linarith
          have h₁₀ : ‖(1 - (eC γ) ^ (b + 1 - a))‖ / ‖(1 - eC γ)‖ * (2 * |γ - m|) ≤ 1 := by
            have h₁₁ : ‖(1 - (eC γ) ^ (b + 1 - a))‖ ≤ 2 := h₇
            have h₁₂ : ‖(1 - eC γ)‖ = 2 * |Real.sin (Real.pi * γ)| := h₈
            have h₁₃ : (2 : ℝ) * |Real.sin (Real.pi * γ)| ≥ 2 * |γ - m| := h₉
            have h₁₄ : 0 < (2 : ℝ) * |Real.sin (Real.pi * γ)| := by
              have h₁₅ : (eC γ : ℂ) ≠ 1 := h₄
              have h₁₆ : ‖(1 - eC γ)‖ > 0 := by
                have h₁₇ : (1 : ℂ) - eC γ ≠ 0 := by
                  intro h
                  apply h₁₅
                  rw [sub_eq_zero] at h
                  exact h
                exact norm_pos_iff.mpr h₁₇
              have h₁₈ : ‖(1 - eC γ)‖ = 2 * |Real.sin (Real.pi * γ)| := h₈
              rw [h₁₈] at h₁₆
              linarith
            have h₁₅ : ‖(1 - (eC γ) ^ (b + 1 - a))‖ / ‖(1 - eC γ)‖ * (2 * |γ - m|) ≤ 1 := by
              calc
                ‖(1 - (eC γ) ^ (b + 1 - a))‖ / ‖(1 - eC γ)‖ * (2 * |γ - m|) ≤ 2 / ‖(1 - eC γ)‖ * (2 * |γ - m|) := by
                  gcongr
                  <;> simp_all [h₁₂]
                  <;> linarith
                _ = 2 / (2 * |Real.sin (Real.pi * γ)|) * (2 * |γ - m|) := by
                  rw [h₁₂]
                  <;> field_simp
                  <;> ring_nf
                _ = (1 / |Real.sin (Real.pi * γ)|) * (2 * |γ - m|) := by
                  field_simp
                  <;> ring_nf
                  <;> field_simp
                  <;> ring_nf
                _ ≤ 1 := by
                  have h₁₆ : (1 / |Real.sin (Real.pi * γ)| : ℝ) * (2 * |γ - m|) ≤ 1 := by
                    have h₁₇ : 0 < |Real.sin (Real.pi * γ)| := by
                      have h₁₈ : (2 : ℝ) * |Real.sin (Real.pi * γ)| > 0 := by linarith
                      linarith
                    have h₁₈ : (2 : ℝ) * |Real.sin (Real.pi * γ)| ≥ 2 * |γ - m| := h₉
                    have h₁₉ : (1 / |Real.sin (Real.pi * γ)| : ℝ) * (2 * |γ - m|) = (2 * |γ - m|) / |Real.sin (Real.pi * γ)| := by
                      field_simp
                      <;> ring_nf
                    rw [h₁₉]
                    have h₂₀ : (2 * |γ - m| : ℝ) / |Real.sin (Real.pi * γ)| ≤ 1 := by
                      rw [div_le_iff (by positivity)]
                      nlinarith
                    linarith
                  linarith
            linarith
          linarith
      -- Combine the bounds
      calc
        ‖∑ k in Finset.range (b + 1 - a), (eC γ) ^ k‖ * (2 * |γ - m|) ≤ 1 := h₃
        _ = 1 := by norm_num
    exact h_sum_interval
  exact h_main

/-- LEAF: the count of the `Q` frequencies `a/Q - β`, spaced `1/Q` apart modulo one, the second
step of the dual count in Matomäki and Shao Lemma 7.4 behind Lemma 5.2, page 18. Class MEDIUM.
`∑_{a < Q} min(N, 1/(2 ‖a/Q - β‖)) ≤ 2N + Q (1 + log Q)`, at most `K (N + Q √N)` once
`6 Q² ≤ N`. -/
theorem leaf_dual_count : ∃ K : ℝ, 0 < K ∧ ∀ N Q : ℕ, 1 ≤ Q → 6 * Q ^ 2 ≤ N → ∀ β : ℝ,
    ∀ g : ℕ → ℝ, (∀ a, 0 ≤ g a ∧ g a ≤ N) →
    (∀ a : ℕ, ∀ m : ℤ, |(a : ℝ) / Q - β - m| ≤ 1 / 2 → g a * (2 * |(a : ℝ) / Q - β - m|) ≤ 1) →
    ∑ a ∈ range Q, g a ≤ K * (N + Q * Real.sqrt N) := by
  sorry

/-- `twisted_interval_bound` from the two leaves. -/
theorem twisted_interval_bound_of_leaves : ∃ K : ℝ, 0 < K ∧ ∀ N Q : ℕ, 1 ≤ Q → 6 * Q ^ 2 ≤ N →
    ∀ S : Finset ℕ, S ⊆ range N → (∀ x ∈ S, ∀ z ∈ S, ∀ y, x ≤ y → y ≤ z → y ∈ S) →
    ∀ β : ℝ, ∑ a ∈ range Q, ‖∑ n ∈ S, eC (((a : ℝ) / Q - β) * n)‖ ≤
      K * (N + Q * Real.sqrt N) := by
  obtain ⟨K, hK, hKb⟩ := leaf_dual_count
  refine ⟨K, hK, fun N Q hQ hNQ S hS hconv β => ?_⟩
  refine hKb N Q hQ hNQ β (fun a => ‖∑ n ∈ S, eC (((a : ℝ) / Q - β) * n)‖) (fun a => ?_)
    (fun a m hm => leaf_geometric_interval S hconv _ m hm)
  refine ⟨norm_nonneg _, ?_⟩
  calc ‖∑ n ∈ S, eC (((a : ℝ) / Q - β) * n)‖ ≤ ∑ n ∈ S, ‖eC (((a : ℝ) / Q - β) * n)‖ :=
        norm_sum_le _ _
    _ = #S := by
        rw [Finset.card_eq_sum_ones, Nat.cast_sum]
        refine Finset.sum_congr rfl fun n _ => ?_
        unfold eC
        rw [Complex.norm_exp]
        have h : (2 * (Real.pi : ℂ) * Complex.I * ((((a : ℝ) / Q - β) * n : ℝ) : ℂ)).re = 0 := by
          simp
        rw [h, Real.exp_zero, Nat.cast_one]
    _ ≤ N := by
        have := Finset.card_le_card hS
        rw [Finset.card_range] at this
        exact_mod_cast this

theorem twisted_interval_bound_twin :
    type_of% @LeanLab.Teravainen2016.twisted_interval_bound :=
  twisted_interval_bound_of_leaves

end LeanLab.Teravainen2016
