/-
Burst 2026-11-20b, BHP1997, split of `DQLowerExceptionalMeanSquare.leaf_520`.
Source: P0069 Baker Harman Pintz 1997, page 52, display 5.20, "Combining (5.19), (5.17)",
with 5.17 on page 51 and Lemma 29 on page 43.

The leaf is cut along the paper's own two inputs, two LEAF statements, plus the one step the
paper leaves tacit, which is proved here:
* `sub_519_principal`, display 5.19 at `z' = z0` for the principal character `χ0`;
* `sub_517_window`, display 5.17 at `z' = z0`, in the lab form, main term restricted to J;
* `sub_principal_coprime`, PROVED, the tacit step: 5.19 is about `b0 χ0` and 5.17 about `b0`,
  and they agree since every `m` in the support of b0 is coprime to every `q ≤ Q`.
`leaf_520_of_subleaves` has exactly the statement of `leaf_520` and is PROVED from them.
The sub-leaves need `perronW`, which lives in `DQLowerExceptionalMeanSquareDecisions`, so this
file imports that one and the sorry of `leaf_520` stays.

AI wrote the Lean code. Goldbach is open.

NOTE U-1745, 2026-11-22: P0069 pages 20 and 43 print `[29], Lemma 3.19`, but [29] is Saffari and
Vaughan 1977, which has no Lemma 3.19. The result used is Titchmarsh [30], second edition 1986,
Lemma 3.19, book p. 70, the finite Perron formula with error, which follows from Lemma 3.12,
book p. 60, display 3.12.1. Page 22 of P0069 calls it Theorem 3.19 of [30]. Read from
copies/Titchmarsh1986-chIII.pdf, page images. Below, [30] Lemma 3.19 replaces the printed label.
-/
import LeanLab.BHP1997.DQLowerExceptionalMeanSquareDecisions
import LeanLab.BHP1997.DQ517WindowSplit

namespace LeanLab.BHP1997.DQLowerExceptionalMeanSquare
open Classical Complex Decomp132 DecompC165b DecompC165d LowerShortC165 LowerShortMeanSquare
open scoped BigOperators
open MeasureTheory

/-! ### The sub-leaves -/

/-- LEAF: page 52 display 5.19 at `z' = z0 = 1/T0^2`, the principal character term.
P0069 Baker Harman Pintz 1997: "(5.1) and (5.2) hold a fortiori if `T2` is replaced by a
smaller positive number, so the same argument yields (5.19)", here with `T2` replaced by
`1/z0 = T0^2`. In the proof of Lemma 29 on page 43, via [30] Lemma 3.19, the principal
character is treated by (5.2) alone, `F = E_q^c \ {χ0}`, so its term holds whether or not
`χ0` lies in `E_q`. Integrability included. CONDITIONAL on the cited Theorem 4 and Lemma 9,
which give (5.1) and (5.2) for b0 through Lemmas 33 to 35. -/
theorem sub_519_principal (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      IntervalIntegrable (fun y =>
          ‖(∑ m ∈ (rightInterval ε x).filter
              (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * perronZ0 x),
              (lowerShortWeight ω ε x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q)) -
            perronW ω ε x q y (perronZ0 x)‖ ^ 2) volume
        (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) ∧
      ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
          ‖(∑ m ∈ (rightInterval ε x).filter
              (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * perronZ0 x),
              (lowerShortWeight ω ε x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q)) -
            perronW ω ε x q y (perronZ0 x)‖ ^ 2 ≤
        C * perronZ0 x ^ 2 * (x ^ (11 / 20 + ε)) ^ 3 * Real.log x ^ (-A) := by
  sorry

/-- LEAF: page 51 display 5.17 at `z' = z0`. P0069 Baker Harman Pintz 1997, "It is a
straightforward consequence of the prime number theorem, with error term `Y exp(-ε L^(1/2))`,
that for `y ~ Y`, `z' ≤ L^(-1)`, `Σ_{y ≤ m ≤ y + y z'} b0(m) = v0 y z' / L' + O(Y (T0^(-5) +
z'^2))`". Lab form: the main term is `v0 / L'` per integer of J in the window, the lab's
normalization of b0 by `lowerFactor`, and the sum runs over J only. For `y` in `[Y/2, 3Y]`
the part of the window inside J is an interval of length at most `y z0` near `Y` or `2Y`, to
which the printed 5.17 applies with a smaller `z'`; integer rounding costs `O(1)`. The
pointwise form with the short window is what QUESTION 5 of the 2026-11-20 notes asks for: the
prefix form `lower_principal_density` is too weak here. -/
theorem sub_517_window (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
      ∀ y ∈ Set.Icc (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)),
        ‖∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * perronZ0 x),
            ((lowerShortWeight ω ε x m : ℂ) -
              ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ))‖ ≤
          C * x ^ (11 / 20 + ε) * ((perronT0 x ^ 5)⁻¹ + perronZ0 x ^ 2) :=
  -- Feed1122 S82: closed by the split in `DQ517WindowSplit`, CONDITIONAL on its LEAFs
  -- `leaf_two_window` and `leaf_four_window`.
  LeanLab.BHP1997.DQ517Window.sub_517_window_of_leaves ω hω hz hε hε8

/-- `Q < Z^(c1')` and `Q < Y`: the modulus bound `q ≤ Q` of page 3 lies below the rough
threshold of b0 used by `rawLower_coprime`, since `Q ≤ Y^(1/16)/2` and `Z = 4Y`. -/
theorem sieveQ_lt_rough {ε x : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (hx : 1 ≤ x) :
    (sieveQ ε x : ℝ) < scaleZ ε x ^ ((1+7*(2*(1/16-1/10^5)))/15-ε) ∧
      (sieveQ ε x : ℝ) < x ^ (11 / 20 + ε) := by
  set Y := x ^ (11 / 20 + ε) with hY
  have hx0 : 0 ≤ x := by linarith
  have hY1 : 1 ≤ Y := Real.one_le_rpow hx (by linarith)
  have hY0 : 0 ≤ Y := by linarith
  set c : ℝ := 1 / 16 - 1 / 10 ^ 5 with hc
  have hfl : (sieveQ ε x : ℝ) ≤ (Y ^ ((2 : ℝ) * c)) ^ (1 / 2 : ℝ) / 2 := by
    unfold sieveQ
    exact Nat.floor_le (by positivity)
  have e1 : (Y ^ ((2 : ℝ) * c)) ^ (1 / 2 : ℝ) = Y ^ c := by
    rw [← Real.rpow_mul hY0]; congr 1; ring
  rw [e1] at hfl
  have hYc : 0 < Y ^ c := Real.rpow_pos_of_pos (by linarith) _
  have hlt : (sieveQ ε x : ℝ) < Y ^ c := lt_of_le_of_lt hfl (half_lt_self hYc)
  have e2 : Y ^ c = x ^ ((11 / 20 + ε) * c) := by rw [hY, ← Real.rpow_mul hx0]
  have e3 : x ^ ((11 / 20 + ε) * c) ≤ x ^ (11 / 200 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by rw [hc]; nlinarith)
  obtain ⟨hZc, -⟩ := scaleZ_rpow_ge hε hε8 hx
  have e4 : Y ^ c ≤ Y := by
    calc Y ^ c ≤ Y ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hY1 (by rw [hc]; norm_num)
      _ = Y := Real.rpow_one Y
  refine ⟨?_, by linarith⟩
  calc (sieveQ ε x : ℝ) < Y ^ c := hlt
    _ = x ^ ((11 / 20 + ε) * c) := e2
    _ ≤ x ^ (11 / 200 : ℝ) := e3
    _ ≤ _ := hZc

/-- P0069 page 52, the tacit step inside "Combining (5.19), (5.17)": 5.19 is about
`b0(m) χ0(m)` and 5.17 about `b0(m)`. They agree term by term: every `m` with `b0(m) ≠ 0`
has no prime factor below `Z^c1`, page 50 display 5.15, and `q ≤ Q` lies below that threshold,
so `χ0(m) = 1` there, by `rawLower_coprime`. So the left side is zero. PROVED. -/
theorem sub_principal_coprime (ω : ℝ → ℝ)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ y ∈ Set.Icc (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)),
        ‖∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * perronZ0 x),
            (lowerShortWeight ω ε x m : ℂ) *
              ((1 : DirichletCharacter ℂ q) (m : ZMod q) - 1)‖ ≤
          C * perronZ0 x * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A _
  refine ⟨1, fun x hx q hq hqQ y _ => ?_⟩
  obtain ⟨hQZ, hQY⟩ := sieveQ_lt_rough hε hε8 hx
  obtain ⟨-, hZ1⟩ := scaleZ_rpow_ge hε hε8 hx
  have hqQ' : (q : ℝ) ≤ sieveQ ε x := by exact_mod_cast hqQ
  have hzero : ∑ m ∈ (rightInterval ε x).filter
      (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * perronZ0 x),
      (lowerShortWeight ω ε x m : ℂ) * ((1 : DirichletCharacter ℂ q) (m : ZMod q) - 1) = 0 := by
    refine Finset.sum_eq_zero fun m hm => ?_
    by_cases h0 : rawLower ε x m = 0
    · simp [lowerShortWeight, h0]
    · have hmJ := (Finset.mem_filter.mp hm).1
      unfold rightInterval at hmJ
      have hmY : ⌊x ^ (11 / 20 + ε)⌋₊ < m := (Finset.mem_Ioc.mp hmJ).1
      have hYm : x ^ (11 / 20 + ε) < (m : ℝ) := by
        have := Nat.lt_floor_add_one (x ^ (11 / 20 + ε))
        have h' : ((⌊x ^ (11 / 20 + ε)⌋₊ : ℕ) : ℝ) + 1 ≤ (m : ℝ) := by exact_mod_cast hmY
        linarith
      have hqm : q < m := by
        have : (q : ℝ) < m := by linarith
        exact_mod_cast this
      have hqZ : (q : ℝ) < scaleZ ε x ^ ((1+7*(2*(1/16-1/10^5)))/15-ε) := by linarith
      have hcop := rawLower_coprime hZ1 hq hqm hqZ h0
      have hu : IsUnit (m : ZMod q) := (ZMod.isUnit_iff_coprime m q).mpr hcop
      rw [MulChar.one_apply hu, sub_self, mul_zero]
  rw [hzero, norm_zero]
  have hx0 : 0 ≤ x := by linarith
  have h1 := perronZ0_pos x
  have h2 := Real.rpow_nonneg hx0 (11 / 20 + ε)
  have h3 := Real.rpow_nonneg (Real.log_nonneg hx) (-A)
  exact mul_nonneg (mul_nonneg (mul_nonneg zero_le_one h1.le) h2) h3

/-! ### Proved helpers -/

/-- `L^A ≤ n! T0` with `n = ⌈3A⌉`, for `L = log x ≥ 1`: `T0 = exp(L^(1/3))` beats every power
of `L`. -/
theorem log_rpow_le_factorial_mul_T0 {A x : ℝ} (hL : 1 ≤ Real.log x) :
    Real.log x ^ A ≤ (Nat.ceil (3 * A)).factorial * perronT0 x := by
  set L := Real.log x with hLdef
  set n := Nat.ceil (3 * A)
  set u := L ^ (1 / 3 : ℝ) with hu
  have hL0 : 0 ≤ L := by linarith
  have hu1 : 1 ≤ u := Real.one_le_rpow hL (by norm_num)
  have hLA : L ^ A = u ^ (3 * A) := by
    rw [hu, ← Real.rpow_mul hL0]; congr 1; ring
  have h1 : u ^ (3 * A) ≤ u ^ (n : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hu1 (Nat.le_ceil _)
  have h2 : u ^ n / (n.factorial : ℝ) ≤ Real.exp u :=
    Real.pow_div_factorial_le_exp u (by linarith) n
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  rw [div_le_iff₀ hf] at h2
  rw [Real.rpow_natCast] at h1
  rw [hLA]
  unfold perronT0
  rw [← hLdef, ← hu]
  calc u ^ (3 * A) ≤ u ^ n := h1
    _ ≤ Real.exp u * n.factorial := h2
    _ = _ := by ring

/-- `T0^(-5) + z0^2 ≤ 2 z0 T0^(-1)` for `T0 ≥ 1`. -/
theorem T0_err_le {x : ℝ} (hT : 1 ≤ perronT0 x) :
    (perronT0 x ^ 5)⁻¹ + perronZ0 x ^ 2 ≤ 2 * perronZ0 x * (perronT0 x)⁻¹ := by
  unfold perronZ0
  set T := perronT0 x
  have hT0 : 0 < T := by linarith
  set w := T⁻¹ with hw
  have hw0 : 0 < w := inv_pos.mpr hT0
  have hw1 : w ≤ 1 := inv_le_one_of_one_le₀ hT
  have e1 : (T ^ 5)⁻¹ = w ^ 5 := by rw [hw, inv_pow]
  have e2 : 1 / T ^ 2 = w ^ 2 := by rw [hw, inv_pow, one_div]
  rw [e1, e2]
  have a1 : w ^ 5 ≤ w ^ 3 := pow_le_pow_of_le_one hw0.le hw1 (by norm_num)
  have a2 : w ^ 4 ≤ w ^ 3 := pow_le_pow_of_le_one hw0.le hw1 (by norm_num)
  nlinarith

/-- `W(y, z)` is measurable in `y`: an integral over `t` of an integrand jointly measurable
in `(y, t)`. -/
theorem perronW_measurable (ω : ℝ → ℝ) (ε x : ℝ) (q : ℕ) (z : ℝ) :
    Measurable (fun y => perronW ω ε x q y z) := by
  unfold perronW
  refine Measurable.const_mul ?_ _
  have hle : -perronT0 x ≤ perronT0 x := by
    have : 0 < perronT0 x := by unfold perronT0; positivity
    linarith
  simp_rw [intervalIntegral.integral_of_le hle]
  refine (StronglyMeasurable.integral_prod_right ?_).measurable
  refine Measurable.stronglyMeasurable ?_
  unfold lowerG
  fun_prop

/-- A window sum over J is measurable in `y`. -/
theorem window_measurable (ε x z : ℝ) (c : ℕ → ℂ) :
    Measurable (fun y : ℝ => ∑ m ∈ (rightInterval ε x).filter
      (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z), c m) := by
  simp_rw [Finset.sum_filter]
  refine Finset.measurable_sum _ fun m _ => ?_
  refine Measurable.ite ?_ measurable_const measurable_const
  exact (measurableSet_le measurable_id measurable_const).inter
    (measurableSet_le measurable_const (measurable_id.add (measurable_id.mul_const z)))

/-- `|a - b|^2 ≤ 2 |a - c|^2 + 2 |c - b|^2`, the pointwise combination of 5.19 and 5.17. -/
theorem norm_sub_sq_le_two (a b c : ℂ) :
    ‖a - b‖ ^ 2 ≤ 2 * ‖c - a‖ ^ 2 + 2 * ‖c - b‖ ^ 2 := by
  have h := norm_add_sq_le_two (a - c) (c - b)
  rw [show a - c + (c - b) = a - b by ring, norm_sub_rev a c] at h
  linarith

/-! ### The leaf from the sub-leaves -/

/-- P0069 page 52 display 5.20, "Combining (5.19), (5.17)", with exactly the statement of
`leaf_520`. PROVED from the LEAF statements `sub_519_principal` and `sub_517_window`
and the proved `sub_principal_coprime`:
the window sum of `b0 χ0` is close to `W(y, z0)` in mean square, and pointwise it differs from
the J restricted main term by `O(y z0 L^(-A))`, since `T0^(-5) + z0^2 ≤ 2 z0 / T0` and `T0`
beats every power of `L`. CONDITIONAL on the two LEAF statements and the cited Theorem 4
and Lemma 9. -/
theorem leaf_520_of_subleaves (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      IntervalIntegrable (fun y => ‖perronW ω ε x q y (perronZ0 x) -
          ∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * perronZ0 x),
            ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ)‖ ^ 2) volume
        (x ^ (11 / 20 + ε) / 2) (3 * x ^ (11 / 20 + ε)) ∧
      ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
          ‖perronW ω ε x q y (perronZ0 x) -
            ∑ m ∈ (rightInterval ε x).filter
              (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * perronZ0 x),
              ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ)‖ ^ 2 ≤
        C * perronZ0 x ^ 2 * (x ^ (11 / 20 + ε)) ^ 3 * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, hC1⟩ := sub_519_principal h4 h9 ω hω hz hε hε8 A hA
  obtain ⟨C2, hC2⟩ := sub_517_window ω hω hz hε hε8
  obtain ⟨C3, hC3⟩ := sub_principal_coprime ω hε hε8 A hA
  set K : ℝ := ((Nat.ceil (3 * A)).factorial : ℝ) with hK
  have hK0 : 0 ≤ K := by positivity
  set c : ℝ := |C3| + 2 * |C2| * K with hc
  have hc0 : 0 ≤ c := by positivity
  set D : ℝ := 2 * |C1| + 5 * c ^ 2 with hD
  refine ⟨max D (max (max C1 C2) (max C3 (Real.exp 1))), fun x hx q hq1 hqQ => ?_⟩
  have hxD : D ≤ x := le_trans (le_max_left _ _) hx
  have hx1 : C1 ≤ x := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_right _ _))) hx
  have hx2 : C2 ≤ x := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) (le_max_right _ _))) hx
  have hx3 : C3 ≤ x := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hL1 : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  set L := Real.log x with hLdef
  set Y := x ^ (11 / 20 + ε) with hYdef
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hxpos _
  set z0 := perronZ0 x with hz0def
  have hz00 : 0 < z0 := perronZ0_pos x
  set T := perronT0 x with hTdef
  have hT1 : 1 ≤ T := by
    rw [hTdef]; unfold perronT0
    exact Real.one_le_exp (Real.rpow_nonneg (le_trans zero_le_one hL1) _)
  have hT0 : 0 < T := by linarith
  have hLA0 : 0 < L ^ (-A) := Real.rpow_pos_of_pos (by linarith) _
  have hLA1 : L ^ (-A) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
  -- `T0⁻¹ ≤ K L^(-A)`
  have hTinv : T⁻¹ ≤ K * L ^ (-A) := by
    have h := log_rpow_le_factorial_mul_T0 (A := A) hL1
    rw [← hLdef, ← hTdef, ← hK] at h
    have hLApos : 0 < L ^ A := Real.rpow_pos_of_pos (by linarith) _
    rw [Real.rpow_neg (by linarith), ← div_eq_mul_inv, le_div_iff₀ hLApos, inv_mul_eq_div,
      div_le_iff₀ hT0]
    exact h
  -- the three pieces
  set Aw : ℝ → ℂ := fun y => ∑ m ∈ (rightInterval ε x).filter
      (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z0),
      (lowerShortWeight ω ε x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q) with hAw
  set Mw : ℝ → ℂ := fun y => ∑ m ∈ (rightInterval ε x).filter
      (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z0),
      ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ) with hMw
  set Ww : ℝ → ℂ := fun y => perronW ω ε x q y z0 with hWw
  obtain ⟨hI1, hB1⟩ := hC1 x hx1 q hq1 hqQ
  -- pointwise bound on `A - M`
  have hAM : ∀ y ∈ Set.Icc (Y / 2) (3 * Y), ‖Aw y - Mw y‖ ≤ c * z0 * Y * L ^ (-A) := by
    intro y hy
    have e : Aw y - Mw y =
        (∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z0),
            (lowerShortWeight ω ε x m : ℂ) *
              ((1 : DirichletCharacter ℂ q) (m : ZMod q) - 1)) +
        ∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z0),
            ((lowerShortWeight ω ε x m : ℂ) -
              ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ)) := by
      simp only [hAw, hMw]
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun m _ => ?_
      ring
    have b3 := hC3 x hx3 q hq1 hqQ y hy
    have b2 := hC2 x hx2 y hy
    have hE := T0_err_le hT1
    rw [← hTdef, ← hz0def] at hE
    have hY0' : 0 ≤ Y := hY0.le
    have hEpos : 0 ≤ (T ^ 5)⁻¹ + z0 ^ 2 := by positivity
    have k2 : C2 * Y * ((T ^ 5)⁻¹ + z0 ^ 2) ≤ |C2| * Y * (2 * z0 * (K * L ^ (-A))) := by
      calc C2 * Y * ((T ^ 5)⁻¹ + z0 ^ 2) ≤ |C2| * Y * ((T ^ 5)⁻¹ + z0 ^ 2) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hY0') hEpos
        _ ≤ |C2| * Y * (2 * z0 * T⁻¹) := mul_le_mul_of_nonneg_left hE (by positivity)
        _ ≤ |C2| * Y * (2 * z0 * (K * L ^ (-A))) :=
            mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hTinv (by positivity))
              (by positivity)
    have hzYL : 0 ≤ z0 * Y * L ^ (-A) := mul_nonneg (by positivity) hLA0.le
    have k3 : C3 * z0 * Y * L ^ (-A) ≤ |C3| * z0 * Y * L ^ (-A) := by
      calc C3 * z0 * Y * L ^ (-A) = C3 * (z0 * Y * L ^ (-A)) := by ring
        _ ≤ |C3| * (z0 * Y * L ^ (-A)) := mul_le_mul_of_nonneg_right (le_abs_self _) hzYL
        _ = |C3| * z0 * Y * L ^ (-A) := by ring
    rw [e]
    calc _ ≤ _ := norm_add_le _ _
      _ ≤ C3 * z0 * Y * L ^ (-A) + C2 * Y * ((T ^ 5)⁻¹ + z0 ^ 2) := add_le_add b3 b2
      _ ≤ |C3| * z0 * Y * L ^ (-A) + |C2| * Y * (2 * z0 * (K * L ^ (-A))) := add_le_add k3 k2
      _ = c * z0 * Y * L ^ (-A) := by rw [hc]; ring
  -- measurability
  have hmeas : Measurable (fun y => ‖Ww y - Mw y‖ ^ 2) := by
    have h1 := perronW_measurable ω ε x q z0
    have h2 := window_measurable ε x z0
      (fun _ => ((lowerV0 ω ε / Real.log (x ^ (11 / 20 + ε)) : ℝ) : ℂ))
    exact ((h1.sub h2).norm).pow_const 2
  have hab : Y / 2 ≤ 3 * Y := by linarith
  have hdom : ∀ y ∈ Set.Icc (Y / 2) (3 * Y), ‖Ww y - Mw y‖ ^ 2 ≤
      2 * ‖Aw y - Ww y‖ ^ 2 + 2 * (c * z0 * Y * L ^ (-A)) ^ 2 := by
    intro y hy
    have h := norm_sub_sq_le_two (Ww y) (Mw y) (Aw y)
    have h2 : ‖Aw y - Mw y‖ ^ 2 ≤ (c * z0 * Y * L ^ (-A)) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hAM y hy) 2
    linarith
  have hRint : IntervalIntegrable (fun y => 2 * ‖Aw y - Ww y‖ ^ 2 +
      2 * (c * z0 * Y * L ^ (-A)) ^ 2) volume (Y / 2) (3 * Y) :=
    (hI1.const_mul 2).add intervalIntegrable_const
  have hInt : IntervalIntegrable (fun y => ‖Ww y - Mw y‖ ^ 2) volume (Y / 2) (3 * Y) := by
    refine IntervalIntegrable.mono_fun' hRint hmeas.aestronglyMeasurable ?_
    rw [Set.uIoc_of_le hab]
    refine (ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall ?_)
    intro y hy
    dsimp only
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    exact hdom y (Set.Ioc_subset_Icc_self hy)
  refine ⟨hInt, ?_⟩
  have hmono := intervalIntegral.integral_mono_on hab hInt hRint hdom
  rw [intervalIntegral.integral_add (hI1.const_mul 2) intervalIntegrable_const,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const] at hmono
  simp only [smul_eq_mul] at hmono
  have hsq : (c * z0 * Y * L ^ (-A)) ^ 2 ≤ c ^ 2 * z0 ^ 2 * Y ^ 2 * L ^ (-A) := by
    have : (L ^ (-A)) ^ 2 ≤ L ^ (-A) := by nlinarith
    calc (c * z0 * Y * L ^ (-A)) ^ 2 = c ^ 2 * z0 ^ 2 * Y ^ 2 * (L ^ (-A)) ^ 2 := by ring
      _ ≤ c ^ 2 * z0 ^ 2 * Y ^ 2 * L ^ (-A) := by gcongr
  have hP : 0 ≤ z0 ^ 2 * Y ^ 3 * L ^ (-A) := by positivity
  have hB1' : 2 * (∫ y in (Y / 2)..(3 * Y), ‖Aw y - Ww y‖ ^ 2) ≤
      2 * |C1| * (z0 ^ 2 * Y ^ 3 * L ^ (-A)) := by
    have : C1 * z0 ^ 2 * Y ^ 3 * L ^ (-A) ≤ |C1| * (z0 ^ 2 * Y ^ 3 * L ^ (-A)) := by
      rw [show C1 * z0 ^ 2 * Y ^ 3 * L ^ (-A) = C1 * (z0 ^ 2 * Y ^ 3 * L ^ (-A)) by ring]
      exact mul_le_mul_of_nonneg_right (le_abs_self _) hP
    linarith
  have hconst : (3 * Y - Y / 2) * (2 * (c * z0 * Y * L ^ (-A)) ^ 2) ≤
      5 * c ^ 2 * (z0 ^ 2 * Y ^ 3 * L ^ (-A)) := by
    have : (3 * Y - Y / 2) * (2 * (c * z0 * Y * L ^ (-A)) ^ 2) ≤
        (3 * Y - Y / 2) * (2 * (c ^ 2 * z0 ^ 2 * Y ^ 2 * L ^ (-A))) := by
      gcongr
    calc _ ≤ _ := this
      _ = 5 * c ^ 2 * (z0 ^ 2 * Y ^ 3 * L ^ (-A)) := by ring
  have hfin : ∫ y in (Y / 2)..(3 * Y), ‖Ww y - Mw y‖ ^ 2 ≤ D * (z0 ^ 2 * Y ^ 3 * L ^ (-A)) := by
    rw [hD]; nlinarith
  have hmax : D * (z0 ^ 2 * Y ^ 3 * L ^ (-A)) ≤
      max D (max (max C1 C2) (max C3 (Real.exp 1))) * (z0 ^ 2 * Y ^ 3 * L ^ (-A)) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) hP
  calc _ ≤ _ := hfin
    _ ≤ _ := hmax
    _ = _ := by ring

/-- Twin check: `leaf_520_of_subleaves` has exactly the type of `leaf_520`. -/
theorem leaf_520_split_twin : type_of% @leaf_520 := @leaf_520_of_subleaves

end LeanLab.BHP1997.DQLowerExceptionalMeanSquare
