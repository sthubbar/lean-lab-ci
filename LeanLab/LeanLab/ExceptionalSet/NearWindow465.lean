import LeanLab.ExceptionalSet.NearGamma465
import LeanLab.ExceptionalSet.Totient465

/-!
P0082 page361 display18, a logarithmic envelope for the finite tail.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465
open Real Finset

/-- P0082 page361 display18. Uniform totient and divisor bounds turn the
finite tail estimate into a logarithmic envelope. CONDITIONAL ON the
explicit progression and divisor bounds. -/
theorem near_gammaTwo_window_log (s : Finset ℕ) (m : ℕ → ℤ) (r Y : ℕ)
    (X P E C A D : ℝ) (N : ℕ) (hr : 1 ≤ r) (hX : 1 ≤ X)
    (hP : 2 ≤ P) (hPY : ⌊P⌋₊ ≤ Y) (hYX : (Y : ℝ) ≤ X)
    (hE : 0 < E) (hC : 0 ≤ C) (hA : 0 ≤ A) (hD : 0 ≤ D)
    (hφ : ∀ q : ℕ, 1 ≤ q → (q : ℝ) / q.totient ≤ A * (1 + Real.log q))
    (hτ : ∀ q ∈ Ioc ⌊P⌋₊ Y, (q.divisors.card : ℝ) ≤ D * P ^ (1 / 2 : ℝ))
    (hprog : ∀ d : ℕ, 1 ≤ d → d ≤ Y →
      ((s.filter (fun n => (d : ℤ) ∣ m n)).card : ℝ) ≤ C * ((N : ℝ) / d + N / E)) :
    (r : ℝ) * ∑ q ∈ (Ioc ⌊P⌋₊ Y).filter (fun q => r ∣ q),
      ∑ n ∈ s, 1 / ((q.totient : ℝ) * ((q / Int.gcd (m n) q).totient : ℝ)) ≤
        A ^ 2 * (4 * D + 1) * C * N * (1 + Real.log X) ^ 4 *
          (P ^ (-(1 / 2 : ℝ)) + 1 / E) := by
  let H := 1 + Real.log X
  have hH1 : 1 ≤ H := by dsimp [H]; have := Real.log_nonneg hX; linarith
  have hH : 0 ≤ H := by linarith
  have hR : 1 ≤ ⌊P⌋₊ := Nat.le_floor (by norm_num; linarith)
  have hY : 1 ≤ Y := hR.trans hPY
  have hR0 : (0 : ℝ) < ⌊P⌋₊ := by exact_mod_cast (show 0 < ⌊P⌋₊ by omega)
  have hPhalf : P / 2 ≤ (⌊P⌋₊ : ℝ) := by
    have := Nat.lt_floor_add_one P
    have : (1 : ℝ) ≤ ⌊P⌋₊ := by exact_mod_cast hR
    linarith
  have hφY : ∀ q : ℕ, 1 ≤ q → q ≤ Y → (q : ℝ) / q.totient ≤ A * H := by
    intro q hq hqY
    apply (hφ q hq).trans
    apply mul_le_mul_of_nonneg_left _ hA
    have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
    have hqX : (q : ℝ) ≤ X := (by exact_mod_cast hqY : (q : ℝ) ≤ Y).trans hYX
    dsimp [H]
    exact add_le_add_right (Real.log_le_log hq0 hqX) 1
  have hm := near_gammaTwo_mean_explicit s m r ⌊P⌋₊ Y E C (A * H)
    (D * P ^ (1 / 2 : ℝ)) N hr hR hPY hE hC (by positivity) (by positivity)
    hφY hτ hprog
  have hterm : 2 * (D * P ^ (1 / 2 : ℝ)) / (⌊P⌋₊ : ℝ) ≤
      4 * D * P ^ (-(1 / 2 : ℝ)) := by
    calc
      _ ≤ 2 * (D * P ^ (1 / 2 : ℝ)) / (P / 2) :=
        div_le_div_of_nonneg_left (by positivity) (by positivity) hPhalf
      _ = 4 * D * P ^ (-(1 / 2 : ℝ)) := by
        rw [show 2 * (D * P ^ (1 / 2 : ℝ)) / (P / 2) =
          4 * D * (P ^ (1 / 2 : ℝ) / P) by ring, ← Real.rpow_sub_one (by linarith : P ≠ 0)]
        norm_num
  have hHY : (1 + Real.log (Y : ℝ)) ^ 2 ≤ H ^ 2 := by
    apply pow_le_pow_left₀
      (by have := Real.log_nonneg (by exact_mod_cast hY : (1 : ℝ) ≤ Y); linarith)
    dsimp [H]
    exact add_le_add_right (Real.log_le_log (by positivity : (0 : ℝ) < Y) hYX) 1
  have hH2 : 1 ≤ H ^ 2 := one_le_pow₀ hH1
  have hsum : 2 * (D * P ^ (1 / 2 : ℝ)) / (⌊P⌋₊ : ℝ) +
      (1 + Real.log (Y : ℝ)) ^ 2 / E ≤
      (4 * D + 1) * H ^ 2 * (P ^ (-(1 / 2 : ℝ)) + 1 / E) := by
    have ha := mul_le_mul_of_nonneg_left hH2 (by positivity : 0 ≤ 4 * D * P ^ (-(1 / 2 : ℝ)))
    have hb := div_le_div_of_nonneg_right hHY hE.le
    have hz : 0 ≤ P ^ (-(1 / 2 : ℝ)) := by positivity
    have hz2 : 0 ≤ H ^ 2 / E := by positivity
    have hc : 0 ≤ H ^ 2 * P ^ (-(1 / 2 : ℝ)) := by positivity
    have hd : 0 ≤ 4 * D * (H ^ 2 / E) := by positivity
    calc
      _ ≤ 4 * D * P ^ (-(1 / 2 : ℝ)) * H ^ 2 + H ^ 2 / E := add_le_add (hterm.trans (by simpa using ha)) hb
      _ ≤ _ := by simp only [div_eq_mul_inv] at *; nlinarith
  calc
    _ ≤ C * N * (A * H) ^ 2 * (2 * (D * P ^ (1 / 2 : ℝ)) / (⌊P⌋₊ : ℝ) +
        (1 + Real.log (Y : ℝ)) ^ 2 / E) := hm
    _ ≤ C * N * (A * H) ^ 2 * ((4 * D + 1) * H ^ 2 * (P ^ (-(1 / 2 : ℝ)) + 1 / E)) :=
      mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = _ := by dsimp [H]; ring
end LeanLab.ExceptionalSet.Supply465
