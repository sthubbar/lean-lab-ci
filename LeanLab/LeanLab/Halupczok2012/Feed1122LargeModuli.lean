import LeanLab.Halupczok2012.U1495PPS

/-!
Feed split of `Decomp398c.large_moduli`, burst-20261122.
Source: Perelli Pintz Salerno 1984 page 531 display 6 through page 538.
https://www.numdam.org/item/ASNSP_1984_4_11_4_529_0/
The moduli above x to the 1 over 100 are cut into dyadic blocks. The Heath Brown
identity and the two polynomial estimates bound one block with one extra log saving;
the number of blocks is at most 3 log x. Only the counting is proved here.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Feed1122LargeModuli

open Finset
open scoped Classical

/-- LEAF: PPS1984 page 531 display 6 through page 538, one dyadic block of moduli
x to the 1/100 times 2 to the j at most q below twice that, above x to the 1/100,
bounded through the Heath Brown identity and the type I and type II polynomial
estimates, uniformly in j. Class HARD. -/
theorem dyadic_block :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ B : ℝ, 0 < B ∧ ∃ C x0 : ℝ, ∀ x y Q : ℝ,
      x0 ≤ x → x ^ (3 / 5 + ε) ≤ y → y ≤ x →
      Q ≤ y * x ^ (-(1 / 2) : ℝ) * Real.log x ^ (-B) →
      ∀ (a : ℕ → ℤ) (h z : ℕ → ℝ), (∀ q, Int.gcd (a q) q = 1) →
      (∀ q, 0 < h q ∧ h q ≤ y) → (∀ q, x / 2 < z q ∧ z q ≤ x) → ∀ j : ℕ,
      ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => x ^ (1 / 100 : ℝ) < (q : ℝ) ∧
          x ^ (1 / 100 : ℝ) * 2 ^ j ≤ (q : ℝ) ∧ (q : ℝ) < x ^ (1 / 100 : ℝ) * 2 ^ (j + 1)),
        ppsTerm (z q) (h q) q (a q) ≤ C * y * Real.log x ^ (-A) := by
  sorry

/-- The dyadic block leaf gives `Decomp398c.large_moduli`, same statement. -/
theorem large_moduli_of_leaves :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ B : ℝ, 0 < B ∧ ∃ C x0 : ℝ, ∀ x y Q : ℝ,
      x0 ≤ x → x ^ (3 / 5 + ε) ≤ y → y ≤ x →
      Q ≤ y * x ^ (-(1 / 2) : ℝ) * Real.log x ^ (-B) →
      ∀ (a : ℕ → ℤ) (h z : ℕ → ℝ), (∀ q, Int.gcd (a q) q = 1) →
      (∀ q, 0 < h q ∧ h q ≤ y) → (∀ q, x / 2 < z q ∧ z q ≤ x) →
      ∑ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => x ^ (1 / 100 : ℝ) < (q : ℝ)),
        ppsTerm (z q) (h q) q (a q) ≤ C * y * Real.log x ^ (-A) := by
  intro A ε hA hε
  obtain ⟨B, hB, C, x0, hblk⟩ := dyadic_block (A + 1) ε (by linarith) hε
  refine ⟨B, hB, 3 * max C 0, max x0 (Real.exp 1), ?_⟩
  intro x y Q hx hxy hyx hQ a h z ha hh hz
  have hx0 : x0 ≤ x := (le_max_left _ _).trans hx
  have hxe : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have he2 : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hx1 : 1 ≤ x := by linarith
  have hxpos : 0 < x := by linarith
  have hL : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  have hy0 : 0 ≤ y := (Real.rpow_nonneg hxpos.le _).trans hxy
  have hM1 : 1 ≤ x ^ (1 / 100 : ℝ) := Real.one_le_rpow hx1 (by norm_num)
  have hMpos : 0 < x ^ (1 / 100 : ℝ) := by linarith
  have hQx : Q ≤ x := by
    have h1 : x ^ (-(1 / 2) : ℝ) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hx1 (by norm_num)
    have h2 : Real.log x ^ (-B) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
    have h1' : 0 ≤ x ^ (-(1 / 2) : ℝ) := Real.rpow_nonneg hxpos.le _
    have h2' : 0 ≤ Real.log x ^ (-B) := Real.rpow_nonneg (by linarith) _
    have h3 : y * x ^ (-(1 / 2) : ℝ) ≤ y := by
      calc y * x ^ (-(1 / 2) : ℝ) ≤ y * 1 := mul_le_mul_of_nonneg_left h1 hy0
        _ = y := mul_one y
    have h4 : y * x ^ (-(1 / 2) : ℝ) * Real.log x ^ (-B) ≤ y * x ^ (-(1 / 2) : ℝ) := by
      calc y * x ^ (-(1 / 2) : ℝ) * Real.log x ^ (-B) ≤ y * x ^ (-(1 / 2) : ℝ) * 1 :=
            mul_le_mul_of_nonneg_left h2 (mul_nonneg hy0 h1')
        _ = _ := mul_one _
    linarith
  have hcastQ : ∀ q : ℕ, 1 ≤ q → q ≤ ⌊Q⌋₊ → (q : ℝ) ≤ Q := by
    intro q hq1 hqn
    have hQ0 : 0 ≤ Q := by
      by_contra hneg
      have : ⌊Q⌋₊ = 0 := Nat.floor_of_nonpos (by linarith)
      omega
    exact (Nat.cast_le.mpr hqn).trans (Nat.floor_le hQ0)
  let g : ℕ → ℕ := fun q => Nat.log 2 ⌊(q : ℝ) / x ^ (1 / 100 : ℝ)⌋₊
  have hmaps : ∀ q ∈ (Icc 1 ⌊Q⌋₊).filter (fun q : ℕ => x ^ (1 / 100 : ℝ) < (q : ℝ)),
      g q ∈ range (Nat.log 2 ⌊Q⌋₊ + 1) := by
    intro q hq
    simp only [mem_filter, mem_Icc] at hq
    rw [mem_range, Nat.lt_succ_iff]
    apply Nat.log_mono_right
    apply Nat.floor_mono
    have : (q : ℝ) / x ^ (1 / 100 : ℝ) ≤ q := div_le_self (Nat.cast_nonneg _) hM1
    linarith [hcastQ q hq.1.1 hq.1.2]
  rw [← sum_fiberwise_of_maps_to hmaps (fun q => ppsTerm (z q) (h q) q (a q))]
  have hK : 0 ≤ max C 0 * y * Real.log x ^ (-(A + 1)) :=
    mul_nonneg (mul_nonneg (le_max_right _ _) hy0) (Real.rpow_nonneg (by linarith) _)
  have hblock : ∀ j : ℕ, ∑ i ∈ ((Icc 1 ⌊Q⌋₊).filter
      (fun q : ℕ => x ^ (1 / 100 : ℝ) < (q : ℝ))).filter (fun i => g i = j),
      ppsTerm (z i) (h i) i (a i) ≤ max C 0 * y * Real.log x ^ (-(A + 1)) := by
    intro j
    refine le_trans (sum_le_sum_of_subset_of_nonneg ?_ ?_)
      ((hblk x y Q hx0 hxy hyx hQ a h z ha hh hz j).trans ?_)
    · intro q hq
      simp only [mem_filter, mem_Icc] at hq ⊢
      obtain ⟨⟨⟨h1, h2⟩, hMq⟩, hg⟩ := hq
      have hfl : 1 ≤ ⌊(q : ℝ) / x ^ (1 / 100 : ℝ)⌋₊ :=
        Nat.le_floor (by rw [Nat.cast_one, le_div_iff₀ hMpos]; linarith)
      have hp1 : 2 ^ j ≤ ⌊(q : ℝ) / x ^ (1 / 100 : ℝ)⌋₊ := by
        rw [← hg]; exact Nat.pow_log_le_self 2 (by omega)
      have hp2 : ⌊(q : ℝ) / x ^ (1 / 100 : ℝ)⌋₊ < 2 ^ (j + 1) := by
        rw [← hg]; exact Nat.lt_pow_succ_log_self (by norm_num) _
      refine ⟨⟨h1, h2⟩, hMq, ?_, ?_⟩
      · have h3 : ((2 ^ j : ℕ) : ℝ) ≤ (q : ℝ) / x ^ (1 / 100 : ℝ) :=
          (Nat.le_floor_iff (by positivity)).mp hp1
        push_cast at h3
        rw [le_div_iff₀ hMpos] at h3
        linarith
      · have h3 := Nat.lt_floor_add_one ((q : ℝ) / x ^ (1 / 100 : ℝ))
        have h4 : ((⌊(q : ℝ) / x ^ (1 / 100 : ℝ)⌋₊ : ℕ) : ℝ) + 1 ≤ ((2 ^ (j + 1) : ℕ) : ℝ) := by
          exact_mod_cast hp2
        push_cast at h4
        have h5 : (q : ℝ) / x ^ (1 / 100 : ℝ) < 2 ^ (j + 1) := by linarith
        rw [div_lt_iff₀ hMpos] at h5
        linarith
    · intro i _ _
      exact abs_nonneg _
    · exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hy0)
        (Real.rpow_nonneg (by linarith) _)
  have hlog : (Nat.log 2 ⌊Q⌋₊ : ℝ) ≤ 2 * Real.log x := by
    rcases Nat.eq_zero_or_pos ⌊Q⌋₊ with hn | hn
    · rw [hn]; simp; linarith
    · have h2n : 2 ^ Nat.log 2 ⌊Q⌋₊ ≤ ⌊Q⌋₊ := Nat.pow_log_le_self 2 hn.ne'
      have hnx : (⌊Q⌋₊ : ℝ) ≤ x := (hcastQ ⌊Q⌋₊ hn le_rfl).trans hQx
      have h3 : ((2 : ℝ) ^ Nat.log 2 ⌊Q⌋₊) ≤ x := by
        have : ((2 ^ Nat.log 2 ⌊Q⌋₊ : ℕ) : ℝ) ≤ (⌊Q⌋₊ : ℝ) := by exact_mod_cast h2n
        push_cast at this
        linarith
      have hl := Real.log_le_log (by positivity) h3
      rw [Real.log_pow] at hl
      have hk : (0 : ℝ) ≤ (Nat.log 2 ⌊Q⌋₊ : ℝ) := Nat.cast_nonneg _
      nlinarith [Real.log_two_gt_d9]
  have hJ : ((range (Nat.log 2 ⌊Q⌋₊ + 1)).card : ℝ) ≤ 3 * Real.log x := by
    rw [card_range]; push_cast; linarith
  have hpow : Real.log x ^ (-(A + 1)) * Real.log x = Real.log x ^ (-A) := by
    rw [show -A = -(A + 1) + 1 by ring, Real.rpow_add (by linarith), Real.rpow_one]
  calc _ ≤ ∑ j ∈ range (Nat.log 2 ⌊Q⌋₊ + 1), max C 0 * y * Real.log x ^ (-(A + 1)) :=
        sum_le_sum fun j _ => hblock j
    _ = ((range (Nat.log 2 ⌊Q⌋₊ + 1)).card : ℝ) * (max C 0 * y * Real.log x ^ (-(A + 1))) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ 3 * Real.log x * (max C 0 * y * Real.log x ^ (-(A + 1))) :=
        mul_le_mul_of_nonneg_right hJ hK
    _ = 3 * max C 0 * y * (Real.log x ^ (-(A + 1)) * Real.log x) := by ring
    _ = 3 * max C 0 * y * Real.log x ^ (-A) := by rw [hpow]

end LeanLab.Halupczok2012.Feed1122LargeModuli

#print axioms LeanLab.Halupczok2012.Feed1122LargeModuli.large_moduli_of_leaves
