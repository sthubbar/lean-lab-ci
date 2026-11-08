import LeanLab.ExceptionalSet.GammaSplit465
import LeanLab.ExceptionalSet.Progressions465
import LeanLab.HeathBrown1985.DivisorEps

/-!
P0082 page362 display19 on the literal floor window.
The divisor bound is elementary and the exceptional character is absent.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Supply465

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu)
open LeanLab.ExceptionalSet.DecompJ200 (window)

/-- P0082 page362 display19. A global divisor bound at exponent one
sixteenth gives a uniform squared divisor bound at each adjacent window integer.
CONDITIONAL ON the explicit arithmetic envelope. -/
theorem window_divisor_sq_le (γ : ℝ) (N n : ℕ) (hn : n ∈ window γ N)
    (j : ℤ) (hj : j = 0 ∨ j = 1) (hX : 1 ≤ F γ N) (D : ℝ) (hD : 0 ≤ D)
    (hτ : ∀ k : ℕ, 1 ≤ k → (k.divisors.card : ℝ) ≤ D * (k : ℝ) ^ (1 / 16 : ℝ)) :
    (((nu γ n + j).natAbs.divisors.card : ℝ)) ^ 2 ≤ 2 * D ^ 2 * F γ N ^ (1 / 8 : ℝ) := by
  let m := nu γ n + j
  have hX0 : 0 < F γ N := Real.exp_pos _
  have hlo := (mem_filter.mp hn).2.1
  have hhi := (mem_filter.mp hn).2.2
  have hj0 : (0 : ℝ) ≤ j := by rcases hj with rfl | rfl <;> norm_num
  have hj1 : (j : ℝ) ≤ 1 := by rcases hj with rfl | rfl <;> norm_num
  have hmpos : (0 : ℝ) < m := by dsimp [m]; push_cast; linarith
  have hmInt : 0 < m := by exact_mod_cast hmpos
  have hmNat : 1 ≤ m.natAbs := by have := Int.natAbs_pos.mpr hmInt.ne'; omega
  have habs : (m.natAbs : ℝ) = (m : ℝ) := by rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos hmpos]
  have hmX : (m.natAbs : ℝ) ≤ 2 * F γ N := by rw [habs]; dsimp [m]; push_cast; linarith
  have ht := hτ m.natAbs hmNat
  have hs := pow_le_pow_left₀ (Nat.cast_nonneg m.natAbs.divisors.card) ht 2
  rw [mul_pow, ← Real.rpow_mul_natCast (Nat.cast_nonneg m.natAbs)] at hs
  norm_num only [show (1 / 16 : ℝ) * 2 = 1 / 8 by norm_num] at hs
  have hpow : (m.natAbs : ℝ) ^ (1 / 8 : ℝ) ≤ 2 * F γ N ^ (1 / 8 : ℝ) := by
    calc
      _ ≤ (2 * F γ N) ^ (1 / 8 : ℝ) := Real.rpow_le_rpow (Nat.cast_nonneg _) hmX (by norm_num)
      _ = (2 : ℝ) ^ (1 / 8 : ℝ) * F γ N ^ (1 / 8 : ℝ) := Real.mul_rpow (by norm_num) hX0.le
      _ ≤ 2 * F γ N ^ (1 / 8 : ℝ) := by
        apply mul_le_mul_of_nonneg_right _ (Real.rpow_nonneg hX0.le _)
        simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le
          (by norm_num : (1 : ℝ) ≤ 2) (by norm_num : (1 / 8 : ℝ) ≤ 1)
  calc
    _ ≤ D ^ 2 * (m.natAbs : ℝ) ^ (1 / 8 : ℝ) := hs
    _ ≤ D ^ 2 * (2 * F γ N ^ (1 / 8 : ℝ)) := mul_le_mul_of_nonneg_left hpow (sq_nonneg _)
    _ = _ := by ring

/-- P0082 page362 display19, the far divisor envelope summed over the
floor window. The small delta condition makes its power at most X to
minus one eighth. No discrepancy or major arc estimate is assumed. -/
theorem far_gammaTwo_window_bound :
    ∃ B : ℝ, 0 < B ∧ ∀ (γ δ : ℝ), 1 < γ → 0 < δ → δ ≤ 1 / 100 →
      ∀ N : ℕ, 16 ≤ N → 2 ≤ F γ N ^ (1 / 3 : ℝ) →
        ∀ r : ℕ, (r : ℝ) ≤ F γ N ^ (6 * δ) → ∀ j : ℤ, (j = 0 ∨ j = 1) →
          (r : ℝ) * ∑ n ∈ window γ N,
            4 * (6 + 2 * Real.log (⌊F γ N ^ (1 / 3 : ℝ)⌋₊ : ℕ)) *
              (((nu γ n + j).natAbs.divisors.card : ℝ)) ^ 2 /
                (⌊F γ N ^ (1 / 3 : ℝ)⌋₊ : ℕ) ≤
            B * N * (1 + Real.log (F γ N)) * F γ N ^ (-(1 / 8 : ℝ)) := by
  obtain ⟨D, hD, hτ⟩ := LeanLab.HeathBrown1985.card_divisors_le_rpow 16 (by norm_num)
  have hτ16 : ∀ k : ℕ, 1 ≤ k → (k.divisors.card : ℝ) ≤ D * (k : ℝ) ^ (1 / 16 : ℝ) := by simpa using hτ
  refine ⟨128 * D ^ 2, by positivity, fun γ δ hγ hδ hδsmall N hN hXthird r hr j hj => ?_⟩
  let X := F γ N
  let Y := ⌊X ^ (1 / 3 : ℝ)⌋₊
  let H := 1 + Real.log X
  have hX0 : 0 < X := Real.exp_pos _
  have hX : 1 ≤ X := by
    apply Real.one_le_exp
    exact Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _
  have hY : 1 ≤ Y := Nat.le_floor (by dsimp [Y, X]; linarith)
  have hY0 : (0 : ℝ) < Y := by exact_mod_cast (show 0 < Y by omega)
  have hYhalf : X ^ (1 / 3 : ℝ) / 2 ≤ (Y : ℝ) := by
    have hf := Nat.lt_floor_add_one (X ^ (1 / 3 : ℝ))
    have hY1 : (1 : ℝ) ≤ Y := by exact_mod_cast hY
    dsimp [Y] at hY1 ⊢
    linarith
  have hYX : (Y : ℝ) ≤ X := by
    refine (Nat.floor_le (Real.rpow_pos_of_pos hX0 _).le).trans ?_
    simpa only [Real.rpow_one] using Real.rpow_le_rpow_of_exponent_le hX (by norm_num : (1 / 3 : ℝ) ≤ 1)
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hH : 0 ≤ H := by dsimp [H]; linarith
  have hCY : 0 ≤ 6 + 2 * Real.log (Y : ℝ) := by
    have := Real.log_nonneg (by exact_mod_cast hY : (1 : ℝ) ≤ Y)
    linarith
  have hlogY : 6 + 2 * Real.log (Y : ℝ) ≤ 8 * H := by
    have := Real.log_le_log hY0 hYX
    dsimp [H]
    linarith
  have hpoint (n : ℕ) (hn : n ∈ window γ N) :
      (r : ℝ) * (4 * (6 + 2 * Real.log (Y : ℝ)) *
        (((nu γ n + j).natAbs.divisors.card : ℝ)) ^ 2 / Y) ≤
          128 * D ^ 2 * H * X ^ (-(1 / 8 : ℝ)) := by
    have ht := window_divisor_sq_le γ N n hn j hj hX D hD.le hτ16
    have hnum : 4 * (6 + 2 * Real.log (Y : ℝ)) * (((nu γ n + j).natAbs.divisors.card : ℝ)) ^ 2 ≤
        (4 * (8 * H)) * (2 * D ^ 2 * X ^ (1 / 8 : ℝ)) :=
      mul_le_mul (mul_le_mul_of_nonneg_left hlogY (by norm_num)) ht (sq_nonneg _) (by positivity)
    have hquot := (div_le_div_of_nonneg_right hnum hY0.le).trans
      (div_le_div_of_nonneg_left (by positivity) (by positivity : 0 < X ^ (1 / 3 : ℝ) / 2) hYhalf)
    calc
      _ ≤ X ^ (6 * δ) * ((4 * (8 * H)) * (2 * D ^ 2 * X ^ (1 / 8 : ℝ)) /
          (X ^ (1 / 3 : ℝ) / 2)) :=
        mul_le_mul hr hquot (by positivity) (Real.rpow_pos_of_pos hX0 _).le
      _ = (128 * D ^ 2 * H) * (X ^ (6 * δ) * X ^ (1 / 8 : ℝ) / X ^ (1 / 3 : ℝ)) := by ring
      _ = (128 * D ^ 2 * H) * X ^ (6 * δ + 1 / 8 - 1 / 3 : ℝ) := by
        rw [Real.rpow_sub hX0, Real.rpow_add hX0]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_exponent_le hX (by linarith)) (by positivity)
  have hcard : ((window γ N).card : ℝ) ≤ N := by
    have hc := card_le_card (Decomp371a.window_subset_Ioc γ hγ N hN)
    have hn : (Ioc (N / 2) N).card ≤ N := by rw [Nat.card_Ioc]; omega
    exact_mod_cast hc.trans hn
  calc
    _ = ∑ n ∈ window γ N, (r : ℝ) * (4 * (6 + 2 * Real.log (Y : ℝ)) *
        (((nu γ n + j).natAbs.divisors.card : ℝ)) ^ 2 / Y) := by rw [mul_sum]
    _ ≤ ∑ _n ∈ window γ N, 128 * D ^ 2 * H * X ^ (-(1 / 8 : ℝ)) := sum_le_sum hpoint
    _ = ((window γ N).card : ℝ) * (128 * D ^ 2 * H * X ^ (-(1 / 8 : ℝ))) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (N : ℝ) * (128 * D ^ 2 * H * X ^ (-(1 / 8 : ℝ))) :=
      mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = _ := by ring

end LeanLab.ExceptionalSet.Supply465
