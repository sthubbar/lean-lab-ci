/-
Burst 2026-11-22, BHP1997, split of `DQLowerExceptionalMeanSquare.sub_517_window`.
Source: P0069 Baker Harman Pintz 1997, page 51, display 5.17: "It is a straightforward
consequence of the prime number theorem, with error term `Y exp(-ε L^(1/2))`, that for `y ~ Y`,
`z' ≤ L^(-1)`, `Σ_{y ≤ m ≤ y + y z'} b0(m) = v0 y z' / L' + O(Y (T0^(-5) + z'^2))`".

The lab b0 is `lowerShortWeight = lowerFactor * rawLower`, with `rawLower` the three terms of
display 5.15 on page 50: the prime indicator, the E2 sum and the E4 sum of page 51. The paper's
consequence of the prime number theorem is applied to each of the three terms separately; this
file cuts along exactly that, with the error of 5.17, `Y T0^(-5)`, on every integer subinterval
of J:
* `theta_window`, the prime term in theta form, PROVED here from the lab strong prime number
  theorem `DQ517StrongPNTInput.psi_interval_error_stretched` and Mathlib's bound on psi minus
  theta, and turned into the prime count by the PROVED `prime_window`;
* `leaf_two_window`, the E2 term, HARD: the same theorem for `p1`, `p2` and the rough `n3`;
* `leaf_four_window`, the E4 term, HARD: the same for `p1` to `p4` and the rough `n5`.
The rest is PROVED here: the factor identity `lowerFactor * V(s) / log Z = v0 / log Y` on J,
from the existing `factor_unclipped_near_one` and `leaf_density_slope`; the summation by parts
against the factor, whose increments are at most `1 / (2 Y)` by `factor_increment_of_density`;
and the window as an integer interval. `sub_517_window_of_leaves` has exactly the statement of
`sub_517_window`, checked by `sub_517_window_split_twin`.

The `z'^2` part of the printed error is not needed in the lab form: the lab main term is
constant per integer, by the U-1624 normalization, so no variation of the main term over the
window arises. The printed bound is still the conclusion, since `z0^2 ≥ 0`.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DQLowerExceptional520Split
import LeanLab.BHP1997.LowerPrincipal517e
import LeanLab.BHP1997.DQ517StrongPNTInput
import LeanLab.BHP1997.DQ517WindowLeaves

namespace LeanLab.BHP1997.DQ517Window
open Classical Complex Decomp132 DecompC165b DecompC165d LowerShortC165 LowerShortMeanSquare
open LeanLab.BHP1997.DQLowerExceptionalMeanSquare
open scoped BigOperators

/-! ### The three terms of display 5.15: the prime term proved, two leaves -/

set_option maxHeartbeats 1000000 in
/-- PROVED: page 51 display 5.17, the prime term of b0, display 5.15 on page 50, in its theta
form. P0069 Baker Harman Pintz 1997: 5.17 is "a straightforward consequence of the
prime number theorem, with error term `Y exp(-ε L^(1/2))`". On every integer subinterval of J
the sum of `log p` over primes minus the length is `O(Y T0^(-5))`, since `exp(-ε L^(1/2))` beats
every power of `T0 = exp(L^(1/3))`. Route: `DQ517StrongPNTInput.psi_interval_error_stretched`
with `N = 7`, since `log Y ≥ (11/20) L`; then Mathlib `Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log`
at both ends, `O(Y^(1/2) L)`, which is below `Y T0^(-5)` for large `x`; and `θ` as the sum of
`primeWeight m * log m` by `Chebyshev.theta`. -/
theorem theta_window {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ a b : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ ≤ a →
      b ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc a b, (primeWeight m * Real.log m - 1)| ≤
        C * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := by
  obtain ⟨Cp, Xp, hCp, hP⟩ := DQ517StrongPNTInput.psi_interval_error_stretched 7
  refine ⟨max (max (Real.exp 343) ((2 * |Xp| + 2) ^ 2)) (4 * Cp + 32),
    fun x hx a b ha hb => ?_⟩
  have hxe : Real.exp 343 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxX : (2 * |Xp| + 2) ^ 2 ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxK : 4 * Cp + 32 ≤ max (max (Real.exp 343) ((2 * |Xp| + 2) ^ 2)) (4 * Cp + 32) :=
    le_max_right _ _
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hL : 343 ≤ Real.log x := by
    rw [← Real.log_exp 343]; exact Real.log_le_log (Real.exp_pos _) hxe
  set L := Real.log x with hLdef
  set u := L ^ (1 / 3 : ℝ) with hu
  have hu3 : u ^ 3 = L := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hu0 : 0 ≤ u := Real.rpow_nonneg (by linarith) _
  have hu7 : 7 ≤ u := by
    by_contra h
    push_neg at h
    have : u ^ 3 < 7 ^ 3 := pow_lt_pow_left₀ h hu0 (by norm_num)
    linarith
  have h5u : 5 * u ≤ L / 8 := by
    have h49 : 49 ≤ u ^ 2 := by nlinarith
    have h40 : 40 * u ≤ u ^ 3 := by
      have := mul_le_mul_of_nonneg_left (show (40 : ℝ) ≤ u ^ 2 by linarith) hu0
      calc 40 * u = u * 40 := by ring
        _ ≤ u * u ^ 2 := this
        _ = u ^ 3 := by ring
    linarith
  set Y := x ^ (11 / 20 + ε) with hY
  have hLY : Real.log Y = (11 / 20 + ε) * L := Real.log_rpow hx0 _
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hx0 _
  have hT : (perronT0 x ^ 5)⁻¹ = Real.exp (-(5 * u)) := by
    unfold perronT0
    rw [← hLdef, ← hu, ← Real.exp_nat_mul, ← Real.exp_neg]; push_cast; ring_nf
  rw [hT]
  set Tm := Real.exp (-(5 * u)) with hTm
  have hTm0 : 0 < Tm := Real.exp_pos _
  have hY2 : 2 ≤ Y := by
    have h1 : 1 ≤ Real.log Y := by rw [hLY]; nlinarith
    have h2 : (2 : ℝ) ≤ Real.exp 1 := by have := Real.add_one_le_exp (1 : ℝ); linarith
    calc (2 : ℝ) ≤ Real.exp 1 := h2
      _ ≤ Real.exp (Real.log Y) := Real.exp_le_exp.mpr h1
      _ = Y := Real.exp_log hY0
  -- the stretched error of the prime number theorem is below `T0^(-5)` on `[Y/2, ∞)`
  have hE1 : ∀ t : ℝ, Y / 2 ≤ t → Real.exp (-7 * Real.log t ^ (1 / 3 : ℝ)) ≤ Tm := by
    intro t ht
    have ht0 : 0 < t := by linarith
    have hlt : L / 2 ≤ Real.log t := by
      have h := Real.log_le_log (by positivity) ht
      rw [Real.log_div hY0.ne' (by norm_num), hLY] at h
      have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
      nlinarith
    set v := Real.log t ^ (1 / 3 : ℝ) with hv
    have hv3 : v ^ 3 = Real.log t := by
      rw [hv, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
    have hv0 : 0 ≤ v := Real.rpow_nonneg (by linarith) _
    have hvu : 5 * u ≤ 7 * v := by
      by_contra h
      push_neg at h
      have h1 : (7 * v) ^ 3 < (5 * u) ^ 3 := pow_lt_pow_left₀ h (by positivity) (by norm_num)
      nlinarith
    rw [hTm]; apply Real.exp_le_exp.mpr; linarith
  -- psi minus theta is below `Y T0^(-5)` on `[1, 2Y]`
  have hE2 : ∀ t : ℝ, 1 ≤ t → t ≤ 2 * Y → 2 * Real.sqrt t * Real.log t ≤ 16 * Y * Tm := by
    intro t ht1 ht2
    have hlog := Real.log_le_rpow_div (x := t) (by linarith) (show (0 : ℝ) < 1 / 4 by norm_num)
    have hst : Real.sqrt t * t ^ (1 / 4 : ℝ) = t ^ (3 / 4 : ℝ) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by linarith)]; norm_num
    have h34 : t ^ (3 / 4 : ℝ) ≤ (2 * Y) ^ (3 / 4 : ℝ) :=
      Real.rpow_le_rpow (by linarith) ht2 (by norm_num)
    have h2Y : (2 * Y) ^ (3 / 4 : ℝ) = 2 ^ (3 / 4 : ℝ) * Y ^ (3 / 4 : ℝ) :=
      Real.mul_rpow (by norm_num) hY0.le
    have h2 : (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (3 / 4 : ℝ) ≤ 2 ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hY34 : Y ^ (3 / 4 : ℝ) ≤ Y * Tm := by
      rw [Real.rpow_def_of_pos hY0, show Y * Tm = Real.exp (Real.log Y + -(5 * u)) by
        rw [Real.exp_add, Real.exp_log hY0]]
      apply Real.exp_le_exp.mpr; rw [hLY]; nlinarith
    have hYp : 0 ≤ Y ^ (3 / 4 : ℝ) := by positivity
    calc 2 * Real.sqrt t * Real.log t ≤ 2 * Real.sqrt t * (t ^ (1 / 4 : ℝ) / (1 / 4)) := by
          gcongr
      _ = 8 * (Real.sqrt t * t ^ (1 / 4 : ℝ)) := by ring
      _ = 8 * t ^ (3 / 4 : ℝ) := by rw [hst]
      _ ≤ 8 * (2 * Y ^ (3 / 4 : ℝ)) := by
          have : t ^ (3 / 4 : ℝ) ≤ 2 * Y ^ (3 / 4 : ℝ) := by
            rw [h2Y] at h34; nlinarith
          linarith
      _ ≤ 16 * Y * Tm := by nlinarith
  have hCpos : 0 ≤ max (max (Real.exp 343) ((2 * |Xp| + 2) ^ 2)) (4 * Cp + 32) * Y * Tm := by
    have : (0 : ℝ) ≤ 4 * Cp + 32 := by linarith
    have := this.trans hxK
    positivity
  rcases le_or_gt a b with hab | hab
  swap
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, abs_zero]; exact hCpos
  -- theta as a sum of `primeWeight m * log m`
  have hθ : ∀ n : ℕ, Chebyshev.theta (n : ℝ) =
      ∑ m ∈ Finset.Ioc 0 n, primeWeight m * Real.log m := by
    intro n
    rw [Chebyshev.theta, Nat.floor_natCast, Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    unfold primeWeight; split_ifs <;> simp
  have hsum : ∑ m ∈ Finset.Ioc a b, (primeWeight m * Real.log m - 1) =
      (Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ)) - ((b : ℝ) - a) := by
    have hc := Finset.sum_Ioc_consecutive (fun m => primeWeight m * Real.log m)
      (Nat.zero_le a) hab
    rw [Finset.sum_sub_distrib, Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, mul_one,
      Nat.cast_sub hab, hθ, hθ]
    linarith
  rw [hsum]
  -- the ends lie in `[Y/2, 2Y]` and past the threshold of the prime number theorem
  have hfl : Y < (⌊Y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Y
  have ha' : (⌊Y⌋₊ : ℝ) ≤ a := by exact_mod_cast ha
  have hb' : (b : ℝ) ≤ ⌊2 * Y⌋₊ := by exact_mod_cast hb
  have hfl2 : (⌊2 * Y⌋₊ : ℝ) ≤ 2 * Y := Nat.floor_le (by positivity)
  have habr : (a : ℝ) ≤ b := by exact_mod_cast hab
  have haY : Y / 2 ≤ (a : ℝ) := by linarith
  have hbY : (b : ℝ) ≤ 2 * Y := by linarith
  have hsx : 2 * |Xp| + 2 ≤ Real.sqrt x := by
    have h := Real.sqrt_le_sqrt hxX
    rwa [Real.sqrt_sq (by positivity)] at h
  have hsY : Real.sqrt x ≤ Y := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (by linarith [Real.add_one_le_exp (343 : ℝ)])
      (by linarith)
  have hXa : Xp ≤ (a : ℝ) := by have := le_abs_self Xp; linarith
  have hXb : Xp ≤ (b : ℝ) := hXa.trans habr
  have hP' := hP a b hXa hXb
  have hpa := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := (a : ℝ)) (by linarith)
  have hpb := Chebyshev.abs_psi_sub_theta_le_sqrt_mul_log (x := (b : ℝ)) (by linarith)
  have ea := hE1 a haY
  have eb := hE1 b (haY.trans habr)
  have pa := hE2 a (by linarith) (by linarith)
  have pb := hE2 b (by linarith) hbY
  have hb0 : (0 : ℝ) ≤ b := by linarith
  have ha0 : (0 : ℝ) ≤ a := by linarith
  have k1 : Cp * b * Real.exp (-7 * Real.log b ^ (1 / 3 : ℝ)) ≤ Cp * (2 * Y) * Tm :=
    mul_le_mul (mul_le_mul_of_nonneg_left hbY hCp) eb (Real.exp_pos _).le (by positivity)
  have k2 : Cp * a * Real.exp (-7 * Real.log a ^ (1 / 3 : ℝ)) ≤ Cp * (2 * Y) * Tm :=
    mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hCp) ea (Real.exp_pos _).le
      (by positivity)
  have e : Chebyshev.theta (b : ℝ) - Chebyshev.theta (a : ℝ) - ((b : ℝ) - a) =
      ((Chebyshev.psi b - Chebyshev.psi a) - ((b : ℝ) - a)) -
        (Chebyshev.psi b - Chebyshev.theta b) + (Chebyshev.psi a - Chebyshev.theta a) := by ring
  rw [e]
  calc _ ≤ |((Chebyshev.psi b - Chebyshev.psi a) - ((b : ℝ) - a)) -
          (Chebyshev.psi b - Chebyshev.theta b)| +
          |Chebyshev.psi a - Chebyshev.theta a| := abs_add_le _ _
    _ ≤ |(Chebyshev.psi b - Chebyshev.psi a) - ((b : ℝ) - a)| +
          |Chebyshev.psi b - Chebyshev.theta b| + |Chebyshev.psi a - Chebyshev.theta a| := by
        gcongr; exact abs_sub _ _
    _ ≤ (Cp * (2 * Y) * Tm + Cp * (2 * Y) * Tm) + 16 * Y * Tm + 16 * Y * Tm := by
        gcongr
        · exact hP'.trans (add_le_add k1 k2)
        · exact hpb.trans pb
        · exact hpa.trans pa
    _ = (4 * Cp + 32) * Y * Tm := by ring
    _ ≤ _ := by gcongr

/-- CONDITIONAL ON the three LEAFs of `DQ517WindowLeaves`, by `two_window_of_leaves`; was a LEAF.
Page 51 display 5.17, the E2 term of b0, the sum over `p1 p2 n3 = m` of display 5.15
with exponents in E2 of page 51. HARD. P0069: "a straightforward consequence of the prime
number theorem, with error term `Y exp(-ε L^(1/2))`", for `p1`, `p2` and the primes of the rough
`n3`, with the Buchstab identity. Local density `(1 / log Z) ∫∫_{E2} ω((s - β1 - β2) / β2) /
(β1 β2^2)` at `m = Z^s`, error `O(Y T0^(-5))` on every integer subinterval of J: the short
window form of `LowerShortC165.leaf_two_rough_density`. -/
theorem leaf_two_window (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ a b : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ ≤ a →
      b ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc a b, (lowerTwoTerms ε x m -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := by
  exact two_window_of_leaves ω hω hz hε hε8

/-- CONDITIONAL ON the three LEAFs of `DQ517WindowLeaves`, by `four_window_of_leaves`; was a LEAF.
Page 51 display 5.17, the E4 term of b0, the sum over `p1 p2 p3 p4 n5 = m` with
exponents in E4 of page 51, reached from display 5.15 on page 50 by two more Buchstab steps.
HARD. P0069 Baker Harman Pintz 1997: "a straightforward consequence of the prime number
theorem, with error term `Y exp(-ε L^(1/2))`", applied to `p1` to `p4` and each prime factor of
the rough `n5`. The local density at `m = Z^s` is the E4 integral of page 51 with `1` replaced
by `s`, over `log Z`, and on every integer subinterval of J the error is `O(Y T0^(-5))`. This
is the short window form of `LowerShortC165.leaf_four_rough_density`. -/
theorem leaf_four_window (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ a b : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ ≤ a →
      b ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc a b, (lowerFourTerms ε x m -
          lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := by
  exact four_window_of_leaves ω hω hz hε hε8

/-! ### Proved steps -/

/-- Summation by parts on an integer interval: a weight `f` bounded by one, with increments at
most `δ`, against `d` whose tail sums are at most `E`. Used for the lab factor in 5.17. -/
theorem abel_window (f d : ℕ → ℝ) {a b : ℕ} (hab : a ≤ b) {E δ : ℝ} (hE : 0 ≤ E) (hδ : 0 ≤ δ)
    (hR : ∀ c : ℕ, a ≤ c → c ≤ b → |∑ m ∈ Finset.Ioc c b, d m| ≤ E)
    (hf : ∀ i : ℕ, a < i → i < b → |f (i + 1) - f i| ≤ δ)
    (hf1 : ∀ i : ℕ, a < i → i ≤ b → |f i| ≤ 1) :
    |∑ m ∈ Finset.Ioc a b, f m * d m| ≤ (1 + ((b - a : ℕ) : ℝ) * δ) * E := by
  -- `G c = S c - f (c + 1) R c` loses at most `δ E` per step
  have key : ∀ k : ℕ, ∀ c : ℕ, b - c = k → a ≤ c → c ≤ b →
      |(∑ m ∈ Finset.Ioc c b, f m * d m) - f (c + 1) * ∑ m ∈ Finset.Ioc c b, d m| ≤
        (k : ℝ) * δ * E := by
    intro k
    induction k with
    | zero =>
      intro c hk _ hcb
      have hc : c = b := by omega
      subst hc
      simp
    | succ k ih =>
      intro c hk hac hcb
      have hc1 : c + 1 ≤ b := by omega
      have h1 := ih (c + 1) (by omega) (by omega) hc1
      have sS := Finset.sum_Ioc_consecutive (fun m => f m * d m) (Nat.le_succ c) hc1
      have sR := Finset.sum_Ioc_consecutive d (Nat.le_succ c) hc1
      rw [Nat.Ioc_succ_singleton, Finset.sum_singleton] at sS sR
      rw [← sS, ← sR]
      have e : f (c + 1) * d (c + 1) + (∑ m ∈ Finset.Ioc (c + 1) b, f m * d m) -
          f (c + 1) * (d (c + 1) + ∑ m ∈ Finset.Ioc (c + 1) b, d m) =
          ((∑ m ∈ Finset.Ioc (c + 1) b, f m * d m) -
            f (c + 1 + 1) * ∑ m ∈ Finset.Ioc (c + 1) b, d m) +
          (f (c + 1 + 1) - f (c + 1)) * ∑ m ∈ Finset.Ioc (c + 1) b, d m := by ring
      rw [e]
      have h2 : |(f (c + 1 + 1) - f (c + 1)) * ∑ m ∈ Finset.Ioc (c + 1) b, d m| ≤ δ * E := by
        rcases Nat.lt_or_ge (c + 1) b with hlt | hge
        · rw [abs_mul]
          exact mul_le_mul (hf (c + 1) (by omega) hlt) (hR (c + 1) (by omega) hc1)
            (abs_nonneg _) hδ
        · have hb : c + 1 = b := by omega
          rw [hb, Finset.Ioc_self, Finset.sum_empty, mul_zero, abs_zero]
          exact mul_nonneg hδ hE
      calc _ ≤ _ := abs_add_le _ _
        _ ≤ (k : ℝ) * δ * E + δ * E := add_le_add h1 h2
        _ = ((k + 1 : ℕ) : ℝ) * δ * E := by push_cast; ring
  rcases Nat.eq_or_lt_of_le hab with h | h
  · subst h; simp; positivity
  have hG := key (b - a) a rfl le_rfl hab
  have hfa : |f (a + 1)| ≤ 1 := hf1 (a + 1) (by omega) (by omega)
  have hRa := hR a le_rfl hab
  have hfR : |f (a + 1) * ∑ m ∈ Finset.Ioc a b, d m| ≤ E := by
    rw [abs_mul]
    calc |f (a + 1)| * |∑ m ∈ Finset.Ioc a b, d m| ≤ 1 * E :=
          mul_le_mul hfa hRa (abs_nonneg _) zero_le_one
      _ = E := one_mul E
  have e : ∑ m ∈ Finset.Ioc a b, f m * d m =
      ((∑ m ∈ Finset.Ioc a b, f m * d m) - f (a + 1) * ∑ m ∈ Finset.Ioc a b, d m) +
        f (a + 1) * ∑ m ∈ Finset.Ioc a b, d m := by ring
  rw [e]
  calc _ ≤ _ := abs_add_le _ _
    _ ≤ ((b - a : ℕ) : ℝ) * δ * E + E := add_le_add hG hfR
    _ = _ := by ring

/-- The window of 5.17 inside J is an integer interval. -/
theorem window_eq_Ioc (ε x y z : ℝ) (hy : 0 < y) (hz : 0 ≤ z) :
    (rightInterval ε x).filter (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z) =
      Finset.Ioc (max ⌊x ^ (11 / 20 + ε)⌋₊ (⌈y⌉₊ - 1))
        (min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊y + y * z⌋₊) := by
  have hc1 : 1 ≤ ⌈y⌉₊ := Nat.one_le_iff_ne_zero.mpr (Nat.ceil_pos.mpr hy).ne'
  have hw : 0 ≤ y + y * z := by positivity
  ext m
  simp only [rightInterval, Finset.mem_filter, Finset.mem_Ioc, max_lt_iff, le_min_iff]
  rw [← Nat.ceil_le, ← Nat.le_floor_iff hw]
  omega

/-- `1 / log` moves by at most `1 / i` from `i` to `i + 1` once `log i ≥ 1`. -/
theorem inv_log_increment {i : ℕ} (hi : 3 ≤ i) :
    |1 / Real.log ((i + 1 : ℕ) : ℝ) - 1 / Real.log (i : ℝ)| ≤ 1 / (i : ℝ) := by
  have hi3 : (3 : ℝ) ≤ i := by exact_mod_cast hi
  have he : Real.exp 1 ≤ (i : ℝ) := le_trans (le_of_lt (by
    have := Real.exp_one_lt_d9; linarith)) hi3
  have hu : 1 ≤ Real.log (i : ℝ) := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) he
  have hi0 : (0 : ℝ) < i := by linarith
  have hlt : (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hv : Real.log (i : ℝ) ≤ Real.log ((i + 1 : ℕ) : ℝ) := Real.log_le_log hi0 hlt
  have hvu : Real.log ((i + 1 : ℕ) : ℝ) - Real.log (i : ℝ) ≤ 1 / (i : ℝ) := by
    rw [← Real.log_div (by positivity) hi0.ne']
    have h1 := Real.log_le_sub_one_of_pos (show 0 < ((i + 1 : ℕ) : ℝ) / (i : ℝ) by positivity)
    have h2 : ((i + 1 : ℕ) : ℝ) / (i : ℝ) - 1 = 1 / (i : ℝ) := by
      push_cast; field_simp; ring
    linarith
  set u := Real.log (i : ℝ)
  set v := Real.log ((i + 1 : ℕ) : ℝ)
  have hu0 : 0 < u := by linarith
  have hv0 : 0 < v := by linarith
  have e : 1 / v - 1 / u = -((v - u) / (u * v)) := by field_simp; ring
  rw [e, abs_neg, abs_of_nonneg (div_nonneg (by linarith) (by positivity))]
  have huv : 1 ≤ u * v := by nlinarith
  calc (v - u) / (u * v) ≤ (v - u) / 1 :=
        div_le_div_of_nonneg_left (by linarith) one_pos huv
    _ = v - u := div_one _
    _ ≤ _ := hvu

/-- P0069 page 51 display 5.17, the prime term of b0, display 5.15 on page 50: on every integer
subinterval of J the count of primes minus the sum of `1 / log m` is `O(Y T0^(-5))`. PROVED from
`theta_window` by summation by parts against `1 / log m`. -/
theorem prime_window {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ a b : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ ≤ a →
      b ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc a b, (primeWeight m - 1 / Real.log m)| ≤
        C * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := by
  obtain ⟨C1, hC1⟩ := theta_window hε hε8
  refine ⟨max (max C1 16) (5 * |C1|), fun x hx a b ha hb => ?_⟩
  have hx1 : C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx16 : 16 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx5 : 5 * |C1| ≤ x := le_trans (le_max_right _ _) hx
  set Y := x ^ (11 / 20 + ε) with hYdef
  have hY4 : 4 ≤ Y := by
    have hs : Real.sqrt x ≤ Y := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
    have : (4 : ℝ) ≤ Real.sqrt x := by
      rw [show (4 : ℝ) = Real.sqrt 16 by
        rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hx16
    linarith
  have hY0 : 0 < Y := by linarith
  have hT : 0 < (perronT0 x ^ 5)⁻¹ := by unfold perronT0; positivity
  have hfl : Y < (⌊Y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Y
  have hfl3 : 3 ≤ ⌊Y⌋₊ := Nat.le_floor (by norm_num; linarith)
  rcases le_or_gt a b with hab | hab
  swap
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, abs_zero]; positivity
  set f : ℕ → ℝ := fun m => 1 / Real.log m with hf
  set d : ℕ → ℝ := fun m => primeWeight m * Real.log m - 1 with hd
  have hsum : ∑ m ∈ Finset.Ioc a b, (primeWeight m - 1 / Real.log m) =
      ∑ m ∈ Finset.Ioc a b, f m * d m := by
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm3 : 3 ≤ m := by have := (Finset.mem_Ioc.mp hm).1; omega
    have hlog : 0 < Real.log (m : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < m by omega))
    simp only [hf, hd]; field_simp
  rw [hsum]
  have hR : ∀ c : ℕ, a ≤ c → c ≤ b → |∑ m ∈ Finset.Ioc c b, d m| ≤ |C1| * Y * (perronT0 x ^ 5)⁻¹ :=
    fun c h1 _ => (hC1 x hx1 c b (ha.trans h1) hb).trans (by gcongr; exact le_abs_self _)
  have hfi : ∀ i : ℕ, a < i → i < b → |f (i + 1) - f i| ≤ 2 / Y := by
    intro i h1 _
    have hi3 : 3 ≤ i := by omega
    have hiY : Y ≤ (i : ℝ) := by
      have : (⌊Y⌋₊ : ℝ) + 1 ≤ i := by exact_mod_cast (show ⌊Y⌋₊ + 1 ≤ i by omega)
      linarith
    have h := inv_log_increment hi3
    simp only [hf]
    calc _ ≤ 1 / (i : ℝ) := h
      _ ≤ 1 / Y := one_div_le_one_div_of_le hY0 hiY
      _ ≤ 2 / Y := by gcongr; norm_num
  have hf1 : ∀ i : ℕ, a < i → i ≤ b → |f i| ≤ 1 := by
    intro i h1 _
    have hi3 : (3 : ℝ) ≤ i := by exact_mod_cast (show 3 ≤ i by omega)
    have he : Real.exp 1 ≤ (i : ℝ) := le_trans (le_of_lt (by
      have := Real.exp_one_lt_d9; linarith)) hi3
    have hu : 1 ≤ Real.log (i : ℝ) := by
      rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) he
    simp only [hf]
    rw [abs_of_pos (by positivity)]
    exact (div_le_one (by linarith)).mpr hu
  have hA := abel_window f d hab (by positivity) (by positivity) hR hfi hf1
  have hlen : 1 + ((b - a : ℕ) : ℝ) * (2 / Y) ≤ 5 := by
    have hfl1 : (⌊2 * Y⌋₊ : ℝ) ≤ 2 * Y := Nat.floor_le (by positivity)
    have hba : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := by rw [Nat.cast_sub hab]
    have hb' : (b : ℝ) ≤ ⌊2 * Y⌋₊ := by exact_mod_cast hb
    have ha' : (⌊Y⌋₊ : ℝ) ≤ a := by exact_mod_cast ha
    have h1 : ((b - a : ℕ) : ℝ) ≤ 2 * Y := by linarith
    have h2 : ((b - a : ℕ) : ℝ) * (2 / Y) ≤ 4 := by
      rw [mul_div_assoc', div_le_iff₀ hY0]; nlinarith
    linarith
  calc _ ≤ _ := hA
    _ ≤ 5 * (|C1| * Y * (perronT0 x ^ 5)⁻¹) :=
        mul_le_mul_of_nonneg_right hlen (by positivity)
    _ = (5 * |C1|) * Y * (perronT0 x ^ 5)⁻¹ := by ring
    _ ≤ _ := by gcongr; exact le_max_right _ _

/-- On J, for large `x`, the lab factor turns the density of the raw weight into the constant
`v0 / log Y`: `b0(m) - v0 / log Y = f(m) (dP(m) - dT(m) - dF(m))`, with `dP`, `dT`, `dF` the
three terms of display 5.15 minus their local densities, and `V(s) / log Z = 1 / log m - D2(s) /
log Z - D4(s) / log Z` since `V(s) = 1 / s - D2(s) - D4(s)`. From `factor_unclipped_near_one`
and `leaf_density_slope`. PROVED, conditional only through those existing results. -/
theorem weight_sub_center (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ m : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ < m →
      m ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      lowerShortWeight ω ε x m - lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) =
        lowerFactor ω ε x m * ((primeWeight m - 1 / Real.log m) -
          (lowerTwoTerms ε x m - lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x)) -
          (lowerFourTerms ε x m - lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))) := by
  obtain ⟨hv0, s1, hs1, hV⟩ := leaf_density_slope ω hω hz hε hε8
  rcases hv0.eq_or_lt with h0 | hpos
  · refine ⟨0, fun x _ m _ _ => ?_⟩
    have hF : lowerFactor ω ε x m = 0 := by unfold lowerFactor; simp [← h0]
    rw [lowerShortWeight, hF, ← h0]; simp
  obtain ⟨C0, hC0⟩ := factor_unclipped_near_one ω hε hs1 hpos hV
  refine ⟨max C0 (Real.exp 1), fun x hx m hm1 hm2 => ?_⟩
  have hxC : C0 ≤ x := (le_max_left _ _).trans hx
  have hxe : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  obtain ⟨-, -, hVge, hfac⟩ := hC0 x hxC m hm1.le hm2
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hx1 : 1 < x := lt_of_lt_of_le (by
    have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num); linarith) hxe
  have hY1 : 1 < x ^ (11 / 20 + ε) := Real.one_lt_rpow hx1 (by linarith)
  have hLY : 0 < Real.log (x ^ (11 / 20 + ε)) := Real.log_pos hY1
  have hLZ : 0 < Real.log (scaleZ ε x) := Real.log_pos (by unfold scaleZ shortY; linarith)
  have hm1' : 1 ≤ ⌊x ^ (11 / 20 + ε)⌋₊ := Nat.le_floor (by exact_mod_cast hY1.le)
  have hm2r : (2 : ℝ) ≤ m := by exact_mod_cast (show 2 ≤ m by omega)
  have hLm : 0 < Real.log m := Real.log_pos (by linarith)
  set V := lowerDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) with hVdef
  have hVpos : 0 < V := lt_of_lt_of_le hpos hVge
  have hVsplit : V = Real.log (scaleZ ε x) / Real.log m -
      lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) -
      lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) := by
    rw [hVdef, lowerDensityAt, one_div_div]
  have hcen : lowerFactor ω ε x m * (V / Real.log (scaleZ ε x)) =
      lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) := by
    rw [hfac]; field_simp
  have hV' : V / Real.log (scaleZ ε x) = 1 / Real.log m -
      lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) / Real.log (scaleZ ε x) -
      lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) / Real.log (scaleZ ε x) := by
    rw [hVsplit]; field_simp
  rw [← hcen, hV', lowerShortWeight, rawLower]
  ring

/-! ### The route step from the leaves -/

/-- P0069 page 51 display 5.17 at `z' = z0`, in the lab form of `sub_517_window`, with exactly
its statement. PROVED from the two LEAF statements `leaf_two_window` and `leaf_four_window`
and the PROVED prime term `prime_window`, by `weight_sub_center` and summation by parts against
the lab factor, whose increments are at most `1 / (2 Y)` on J by `factor_increment_of_density`.
The window is any integer subinterval of J here, so its shortness is not used. CONDITIONAL on
the two leaves only: `leaf_density_slope` and `factor_increment_of_density` are proved on main,
with axioms propext, Classical.choice and Quot.sound. -/
theorem sub_517_window_of_leaves (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      ∀ y ∈ Set.Icc (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)),
        ‖∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * perronZ0 x),
            ((lowerShortWeight ω ε x m : ℂ) -
              ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ))‖ ≤
          C * x ^ (11 / 20 + ε) * ((perronT0 x ^ 5)⁻¹ + perronZ0 x ^ 2) := by
  obtain ⟨C1, hC1⟩ := prime_window hε hε8
  obtain ⟨C2, hC2⟩ := leaf_two_window ω hω hz hε hε8
  obtain ⟨C3, hC3⟩ := leaf_four_window ω hω hz hε hε8
  obtain ⟨C4, hC4⟩ := weight_sub_center ω hω hz hε hε8
  obtain ⟨C5, hC5⟩ := factor_increment_of_density ω hω hz hε hε8
  set K : ℝ := 2 * (|C1| + |C2| + |C3|) with hK
  refine ⟨max (max (max (max C1 C2) (max C3 C4)) (max C5 (Real.exp 1))) K,
    fun x hx y hy => ?_⟩
  have hxM := le_trans (le_max_left _ _) hx
  have hx1 : C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hxM
  have hx2 : C2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_left _ _)
    (le_max_left _ _))) hxM
  have hx3 : C3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hxM
  have hx4 : C4 ≤ x := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_max_left _ _))) hxM
  have hx5 : C5 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hxM
  have hxe : Real.exp 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hxM
  have hxK : K ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hx1' : 1 ≤ x := le_trans (by
    have := Real.add_one_lt_exp (show (1 : ℝ) ≠ 0 by norm_num); linarith) hxe
  set Y := x ^ (11 / 20 + ε) with hYdef
  have hY1 : 1 ≤ Y := Real.one_le_rpow hx1' (by linarith)
  have hY0 : 0 < Y := by linarith
  set T := perronT0 x with hTdef
  have hT0 : 0 < (T ^ 5)⁻¹ := by
    have : 0 < T := by rw [hTdef]; unfold perronT0; positivity
    positivity
  have hy0 : 0 < y := lt_of_lt_of_le (by linarith) hy.1
  rw [window_eq_Ioc ε x y (perronZ0 x) hy0 (perronZ0_pos x).le]
  set a := max ⌊Y⌋₊ (⌈y⌉₊ - 1) with ha
  set b := min ⌊2 * Y⌋₊ ⌊y + y * perronZ0 x⌋₊ with hb
  have haY : ⌊Y⌋₊ ≤ a := le_max_left _ _
  have hbY : b ≤ ⌊2 * Y⌋₊ := min_le_left _ _
  -- the complex sum is the real sum
  have hcast : (∑ m ∈ Finset.Ioc a b, ((lowerShortWeight ω ε x m : ℂ) -
      ((lowerV0 ω ε / Real.log Y : ℝ) : ℂ))) =
      ((∑ m ∈ Finset.Ioc a b, (lowerShortWeight ω ε x m - lowerV0 ω ε / Real.log Y) : ℝ) : ℂ) := by
    push_cast; rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs]
  -- the identity on J
  set f : ℕ → ℝ := fun m => lowerFactor ω ε x m with hf
  set dP : ℕ → ℝ := fun m => primeWeight m - 1 / Real.log m with hdP
  set dT : ℕ → ℝ := fun m => lowerTwoTerms ε x m -
    lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) / Real.log (scaleZ ε x) with hdT
  set dF : ℕ → ℝ := fun m => lowerFourTerms ε x m -
    lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) / Real.log (scaleZ ε x) with hdF
  have hid : ∑ m ∈ Finset.Ioc a b, (lowerShortWeight ω ε x m - lowerV0 ω ε / Real.log Y) =
      (∑ m ∈ Finset.Ioc a b, f m * dP m) - (∑ m ∈ Finset.Ioc a b, f m * dT m) -
        ∑ m ∈ Finset.Ioc a b, f m * dF m := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun m hm => ?_
    have hm' := Finset.mem_Ioc.mp hm
    rw [hC4 x hx4 m (lt_of_le_of_lt haY hm'.1) (hm'.2.trans hbY)]
    simp only [hf, hdP, hdT, hdF]; ring
  rw [hid]
  -- summation by parts for each term
  have hfinc : ∀ i : ℕ, a < i → i < b → |f (i + 1) - f i| ≤ 1 / (2 * Y) := fun i h1 h2 =>
    hC5 x hx5 hx1' i (Finset.mem_Ico.mpr ⟨(haY.trans h1.le), lt_of_lt_of_le h2 hbY⟩)
  have hf1 : ∀ i : ℕ, a < i → i ≤ b → |f i| ≤ 1 := fun i _ _ => by
    rw [abs_le]; exact ⟨by linarith [lowerFactor_nonneg ω ε x i], lowerFactor_le_one ω ε x i⟩
  have hδ : 0 ≤ 1 / (2 * Y) := by positivity
  -- the length factor is at most two
  have hlen : ∀ hab : a ≤ b, (1 + ((b - a : ℕ) : ℝ) * (1 / (2 * Y))) ≤ 2 := by
    intro hab
    have h1 : ((b - a : ℕ) : ℝ) ≤ Y + 1 := by
      have hfl1 : (⌊2 * Y⌋₊ : ℝ) ≤ 2 * Y := Nat.floor_le (by positivity)
      have hfl2 : Y < (⌊Y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Y
      have hba : ((b - a : ℕ) : ℝ) = (b : ℝ) - a := by rw [Nat.cast_sub hab]
      have hb' : (b : ℝ) ≤ ⌊2 * Y⌋₊ := by exact_mod_cast hbY
      have ha' : (⌊Y⌋₊ : ℝ) ≤ a := by exact_mod_cast haY
      linarith
    have h2 : ((b - a : ℕ) : ℝ) * (1 / (2 * Y)) ≤ 1 := by
      rw [mul_one_div, div_le_one (by positivity)]; linarith
    linarith
  have hE : ∀ (d : ℕ → ℝ) (Ci : ℝ), (∀ c : ℕ, a ≤ c → c ≤ b →
      |∑ m ∈ Finset.Ioc c b, d m| ≤ Ci * Y * (T ^ 5)⁻¹) →
      |∑ m ∈ Finset.Ioc a b, f m * d m| ≤ 2 * |Ci| * Y * (T ^ 5)⁻¹ := by
    intro d Ci hR
    rcases le_or_gt a b with hab | hab
    · have hR' : ∀ c : ℕ, a ≤ c → c ≤ b → |∑ m ∈ Finset.Ioc c b, d m| ≤ |Ci| * Y * (T ^ 5)⁻¹ :=
        fun c h1 h2 => (hR c h1 h2).trans (by gcongr; exact le_abs_self _)
      have := abel_window f d hab (by positivity) hδ hR' hfinc hf1
      calc _ ≤ _ := this
        _ ≤ 2 * (|Ci| * Y * (T ^ 5)⁻¹) :=
            mul_le_mul_of_nonneg_right (hlen hab) (by positivity)
        _ = _ := by ring
    · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, abs_zero]; positivity
  have b1 := hE dP C1 fun c h1 h2 => hC1 x hx1 c b (haY.trans h1) hbY
  have b2 := hE dT C2 fun c h1 h2 => hC2 x hx2 c b (haY.trans h1) hbY
  have b3 := hE dF C3 fun c h1 h2 => hC3 x hx3 c b (haY.trans h1) hbY
  have hz2 : 0 ≤ perronZ0 x ^ 2 := sq_nonneg _
  have htot : |(∑ m ∈ Finset.Ioc a b, f m * dP m) - (∑ m ∈ Finset.Ioc a b, f m * dT m) -
      ∑ m ∈ Finset.Ioc a b, f m * dF m| ≤ K * Y * (T ^ 5)⁻¹ := by
    calc _ ≤ |(∑ m ∈ Finset.Ioc a b, f m * dP m) - (∑ m ∈ Finset.Ioc a b, f m * dT m)| +
          |∑ m ∈ Finset.Ioc a b, f m * dF m| := abs_sub _ _
      _ ≤ |∑ m ∈ Finset.Ioc a b, f m * dP m| + |∑ m ∈ Finset.Ioc a b, f m * dT m| +
          |∑ m ∈ Finset.Ioc a b, f m * dF m| := by gcongr; exact abs_sub _ _
      _ ≤ 2 * |C1| * Y * (T ^ 5)⁻¹ + 2 * |C2| * Y * (T ^ 5)⁻¹ + 2 * |C3| * Y * (T ^ 5)⁻¹ := by
          gcongr
      _ = K * Y * (T ^ 5)⁻¹ := by rw [hK]; ring
  have hK0 : 0 ≤ K := by positivity
  set M := max (max (max (max C1 C2) (max C3 C4)) (max C5 (Real.exp 1))) K
  have hKM : K ≤ M := le_max_right _ _
  calc _ ≤ K * Y * (T ^ 5)⁻¹ := htot
    _ ≤ M * Y * ((T ^ 5)⁻¹ + perronZ0 x ^ 2) := by
        have : K * Y * (T ^ 5)⁻¹ ≤ K * Y * ((T ^ 5)⁻¹ + perronZ0 x ^ 2) := by
          gcongr; linarith
        exact this.trans (by gcongr)

/-- Twin check: `sub_517_window_of_leaves` has exactly the type of `sub_517_window`. -/
theorem sub_517_window_split_twin : type_of% @sub_517_window := @sub_517_window_of_leaves

end LeanLab.BHP1997.DQ517Window
