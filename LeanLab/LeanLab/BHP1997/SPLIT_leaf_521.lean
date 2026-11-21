/-
Split of `DQLowerExceptionalMeanSquare.leaf_521`, P0069 Baker Harman Pintz 1997, page 52
display 5.21, burst 2026-11-20b, unit U3c.

Route: `W(y, z') - z' H(y)` is the contour integral of `G(s, χ0) y^s k(s)` with
`k(s) = ((1 + z')^s - 1)/s - z'`, and `|k(s)| ≤ (|s| + 1) z'^2` when `|s| z' ≤ 1`. The printed
"proof of (4.4)" bounds `G` trivially, which at `z' = z0 = 1/T0^2` gives no saving, so the
route bounds `∫ |G|` through the mean value of `|G|^2` on `[-T0, T0]` instead. This file holds
the one cited input, the mean value theorem for Dirichlet polynomials, as a LEAF, and PROVES
from it and from the lab's divisor moments the mean square bound for `G` over J.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a
import LeanLab.BHP1997.Route512MajorMoment

namespace LeanLab.BHP1997.SPLITLeaf521
open Classical Complex DecompC165b LowerShortC165
open scoped BigOperators

/-- LEAF: the mean value theorem for Dirichlet polynomials used for `G` in display 5.21.
CITED-LEFT: Montgomery and Vaughan 1974, Hilbert's inequality, J. London Math. Soc. 8,
Corollary 3: `∫_0^T |Σ a_n n^(-it)|^2 dt = Σ |a_n|^2 (T + O(n))`; here on `[-T, T]` as an
upper bound with an absolute constant `C`. Not in the lab. -/
theorem leaf521_dirichlet_mvt :
    ∃ C : ℝ, ∀ (S : Finset ℕ) (a : ℕ → ℂ) (T : ℝ), 0 ≤ T → (∀ n ∈ S, 1 ≤ n) →
      ∫ t in (-T)..T, ‖∑ n ∈ S, a n * (n : ℂ) ^ (-((t : ℂ) * I))‖ ^ 2 ≤
        ∑ n ∈ S, (2 * T + C * n) * ‖a n‖ ^ 2 := by
  sorry

/-- P0069 page 3 condition ii with page 7 display 2.5, the divisor moment over J: the
squares of b0 on J sum to `O(Y L^c)`. PROVED from `lowerShortWeight_divisor_bound` and
`Route512Major.long_divisor_moment512j`. -/
theorem lowerShortWeight_sq_sum (ω : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c C : ℝ, ∀ x : ℝ, C ≤ x →
      ∑ m ∈ rightInterval ε x, (lowerShortWeight ω ε x m) ^ 2 ≤
        C * x ^ (11 / 20 + ε) * Real.log x ^ c := by
  obtain ⟨Cb, hCb⟩ := lowerShortWeight_divisor_bound ω ε (B := 4) (by norm_num)
  obtain ⟨c, Cd, hCd⟩ := Route512Major.long_divisor_moment512j 8 ε hε
  refine ⟨c, max (max Cd 1) (Cb ^ 2 * Cd), fun x hx => ?_⟩
  have hx' : Cd ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hmom := hCd x hx'
  have hpt : ∀ m ∈ rightInterval ε x, (lowerShortWeight ω ε x m) ^ 2 ≤
      Cb ^ 2 * ((m.divisors.card : ℕ) : ℝ) ^ (8 : ℝ) := by
    intro m _
    have h := hCb x m
    have hd0 : (0 : ℝ) ≤ ((m.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
    have h4 : ((m.divisors.card : ℕ) : ℝ) ^ (4 : ℝ) = ((m.divisors.card : ℕ) : ℝ) ^ (4 : ℕ) := by
      rw [← Real.rpow_natCast]; norm_num
    have h8 : ((m.divisors.card : ℕ) : ℝ) ^ (8 : ℝ) = ((m.divisors.card : ℕ) : ℝ) ^ (8 : ℕ) := by
      rw [← Real.rpow_natCast]; norm_num
    rw [h4] at h
    rw [h8]
    have hb : (lowerShortWeight ω ε x m) ^ 2 = |lowerShortWeight ω ε x m| ^ 2 := (sq_abs _).symm
    rw [hb]
    have hab := abs_nonneg (lowerShortWeight ω ε x m)
    calc |lowerShortWeight ω ε x m| ^ 2 ≤ (Cb * ((m.divisors.card : ℕ) : ℝ) ^ 4) ^ 2 :=
          pow_le_pow_left₀ hab h 2
      _ = Cb ^ 2 * ((m.divisors.card : ℕ) : ℝ) ^ 8 := by ring
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hL : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ c :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _)
      (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  calc ∑ m ∈ rightInterval ε x, (lowerShortWeight ω ε x m) ^ 2
      ≤ ∑ m ∈ rightInterval ε x, Cb ^ 2 * ((m.divisors.card : ℕ) : ℝ) ^ (8 : ℝ) :=
        Finset.sum_le_sum hpt
    _ = Cb ^ 2 * ∑ m ∈ rightInterval ε x, ((m.divisors.card : ℕ) : ℝ) ^ (8 : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ Cb ^ 2 * (Cd * x ^ (11 / 20 + ε) * Real.log x ^ c) :=
        mul_le_mul_of_nonneg_left hmom (sq_nonneg _)
    _ = (Cb ^ 2 * Cd) * (x ^ (11 / 20 + ε) * Real.log x ^ c) := by ring
    _ ≤ max (max Cd 1) (Cb ^ 2 * Cd) * (x ^ (11 / 20 + ε) * Real.log x ^ c) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hL
    _ = max (max Cd 1) (Cb ^ 2 * Cd) * x ^ (11 / 20 + ε) * Real.log x ^ c := by ring

/-- P0069 page 43 Lemma 29 and page 52 display 5.21, the mean square of `G(1/2 + it, χ)` over
`[-T, T]` for `T ≤ Y`: `O(Y L^c)`. PROVED from the cited `leaf521_dirichlet_mvt` and
`lowerShortWeight_sq_sum`, since `(2T + C m)/m ≤ 2 + |C|` for `m` in J. -/
theorem lowerG_mean_square (ω : ℝ → ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ c C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, ∀ χ : DirichletCharacter ℂ q, ∀ T : ℝ, 0 ≤ T →
      T ≤ x ^ (11 / 20 + ε) →
      ∫ t in (-T)..T, ‖∑ m ∈ rightInterval ε x,
          (lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) /
            (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
        C * x ^ (11 / 20 + ε) * Real.log x ^ c := by
  obtain ⟨K, hK⟩ := leaf521_dirichlet_mvt
  obtain ⟨c, C1, hC1⟩ := lowerShortWeight_sq_sum ω hε
  refine ⟨c, max (max C1 1) ((2 + |K|) * C1), fun x hx q χ T hT0 hTY => ?_⟩
  have hx1 : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxC : C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  set Y : ℝ := x ^ (11 / 20 + ε) with hY
  have hY0 : 0 ≤ Y := Real.rpow_nonneg (by linarith) _
  have hJ : ∀ m ∈ rightInterval ε x, Y < (m : ℝ) ∧ 1 ≤ m := by
    intro m hm
    unfold rightInterval at hm
    rw [Finset.mem_Ioc] at hm
    have h1 : Y < (⌊Y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Y
    have h2 : ((⌊Y⌋₊ + 1 : ℕ) : ℝ) ≤ m := by exact_mod_cast hm.1
    push_cast at h2
    exact ⟨by linarith, by omega⟩
  set a : ℕ → ℂ := fun m => (lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) /
    (m : ℂ) ^ (1 / 2 : ℂ) with ha
  have hrw : ∀ t : ℝ, (∑ m ∈ rightInterval ε x,
      (lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) /
        (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) =
      ∑ m ∈ rightInterval ε x, a m * (m : ℂ) ^ (-((t : ℂ) * I)) := by
    intro t
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm0 : (m : ℂ) ≠ 0 := by
      have := (hJ m hm).2
      exact_mod_cast (show m ≠ 0 by omega)
    rw [ha, Complex.cpow_add _ _ hm0, Complex.cpow_neg]
    have h1 : (m : ℂ) ^ (1 / 2 : ℂ) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hm0)
    have h2 : (m : ℂ) ^ ((t : ℂ) * I) ≠ 0 := Complex.cpow_ne_zero_iff.mpr (Or.inl hm0)
    field_simp
  have hint : ∫ t in (-T)..T, ‖∑ m ∈ rightInterval ε x,
      (lowerShortWeight ω ε x m : ℂ) * χ (m : ZMod q) /
        (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 =
      ∫ t in (-T)..T, ‖∑ m ∈ rightInterval ε x, a m * (m : ℂ) ^ (-((t : ℂ) * I))‖ ^ 2 := by
    congr 1
    funext t
    rw [hrw t]
  rw [hint]
  have hmv := hK (rightInterval ε x) a T hT0 (fun m hm => (hJ m hm).2)
  have hterm : ∀ m ∈ rightInterval ε x, (2 * T + K * m) * ‖a m‖ ^ 2 ≤
      (2 + |K|) * (lowerShortWeight ω ε x m) ^ 2 := by
    intro m hm
    obtain ⟨hYm, hm1⟩ := hJ m hm
    have hmpos : (0 : ℝ) < m := by exact_mod_cast hm1
    have hnorm : ‖a m‖ ^ 2 ≤ (lowerShortWeight ω ε x m) ^ 2 / m := by
      have hc : ‖(m : ℂ) ^ (1 / 2 : ℂ)‖ = (m : ℝ) ^ (1 / 2 : ℝ) := by
        rw [show (m : ℂ) = ((m : ℝ) : ℂ) by push_cast; rfl,
          Complex.norm_cpow_eq_rpow_re_of_pos hmpos]
        norm_num
      have hcpos : 0 < (m : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hmpos _
      have hsq : ((m : ℝ) ^ (1 / 2 : ℝ)) ^ 2 = m := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hmpos.le]; norm_num
      have hχ : ‖χ (m : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
      rw [ha]
      simp only
      rw [norm_div, norm_mul, hc, Complex.norm_real, Real.norm_eq_abs, div_pow, mul_pow, hsq]
      apply div_le_div_of_nonneg_right _ hmpos.le
      rw [← sq_abs (lowerShortWeight ω ε x m)]
      have : ‖χ (m : ZMod q)‖ ^ 2 ≤ 1 := by
        have h0 := norm_nonneg (χ (m : ZMod q))
        nlinarith
      nlinarith [sq_nonneg (|lowerShortWeight ω ε x m|)]
    have hlin : 2 * T + K * m ≤ (2 + |K|) * m := by
      have := le_abs_self K
      nlinarith
    have ha0 : 0 ≤ ‖a m‖ ^ 2 := sq_nonneg _
    calc (2 * T + K * m) * ‖a m‖ ^ 2 ≤ ((2 + |K|) * m) * ‖a m‖ ^ 2 :=
          mul_le_mul_of_nonneg_right hlin ha0
      _ ≤ ((2 + |K|) * m) * ((lowerShortWeight ω ε x m) ^ 2 / m) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = (2 + |K|) * (lowerShortWeight ω ε x m) ^ 2 := by field_simp
  have hL : 0 ≤ Y * Real.log x ^ c :=
    mul_nonneg hY0 (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  calc _ ≤ ∑ m ∈ rightInterval ε x, (2 * T + K * m) * ‖a m‖ ^ 2 := hmv
    _ ≤ ∑ m ∈ rightInterval ε x, (2 + |K|) * (lowerShortWeight ω ε x m) ^ 2 :=
        Finset.sum_le_sum hterm
    _ = (2 + |K|) * ∑ m ∈ rightInterval ε x, (lowerShortWeight ω ε x m) ^ 2 := by
        rw [Finset.mul_sum]
    _ ≤ (2 + |K|) * (C1 * Y * Real.log x ^ c) :=
        mul_le_mul_of_nonneg_left (hC1 x hxC) (by positivity)
    _ = ((2 + |K|) * C1) * (Y * Real.log x ^ c) := by ring
    _ ≤ max (max C1 1) ((2 + |K|) * C1) * (Y * Real.log x ^ c) :=
        mul_le_mul_of_nonneg_right (le_max_right _ _) hL
    _ = max (max C1 1) ((2 + |K|) * C1) * Y * Real.log x ^ c := by ring

end LeanLab.BHP1997.SPLITLeaf521
