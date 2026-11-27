/-
Burst 2026-11-24, session S4, burst-20261124, unit S4-20. SPLIT of the LEAF
`DQ517Window.leaf_four_window` of `DQ517WindowSplit.lean`.
Source: P0069 Baker Harman Pintz 1997, page 51, display 5.17, the E4 term of b0: "a
straightforward consequence of the prime number theorem, with error term `Y exp(-ε L^(1/2))`",
applied to `p1` to `p4` and to the primes of the rough cofactor `n5`.

The cut is the one the lab already uses for the prefix form `leaf_four_rough_density`, in
`LowerPrincipal517g.four_rough_density_of_leaves`: the E4 sum is a family sum over prime
quadruples; the rough cofactor `n5` is replaced by its Buchstab density, and what remains is
the sum over the quadruples of that density. Here the error is `Y T0^(-5)` on every integer
subinterval of J, as display 5.17 needs, in place of a log power on prefixes:
* `leaf_rough_window`, LEAF, the rough cofactor step with error `b T0^(-6)`;
* `leaf_four_main_window`, LEAF, the outer prime step on subintervals with error `Y T0^(-5)`;
* `rough_family_density_sum_E`, PROVED, the summation of the rough step over the quadruples,
  the lemma `rough_family_density_sum` with a general error;
* `log_four_le_perronT0`, PROVED, the reciprocal sum `(1 + log 2Y)^4` is at most `T0`;
* `leaf_four_window_of_leaves`, PROVED from the two leaves, with exactly the statement of
  `leaf_four_window`, checked by the `example` at the end.

No new definition. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.BHP1997.DQ517WindowSplit
import LeanLab.BHP1997.LowerPrincipal517g

namespace LeanLab.BHP1997.DQ517FourWindow
open Classical Complex Decomp132 DecompC165b DecompC165d LowerShortC165 LowerShortMeanSquare
open LeanLab.BHP1997.DQLowerExceptionalMeanSquare
open scoped BigOperators

/-! ### The two LEAFs -/

/-- LEAF: P0069 page 51 display 5.17, the rough cofactor `n5` of the E4 term, "a
straightforward consequence of the prime number theorem, with error term `Y exp(-ε L^(1/2))`".
Class HARD. The integers of `(a, b]`, `b ≤ 2Y`, with no prime factor below `z ≥ (2Y)^(1/10)`
have local density `ω(log n / log z) / log z` with error `b T0^(-6)`: each such integer is a
product of at most ten primes, the prime number theorem with error `exp(-ε L^(1/2))` is applied
to each prime and the Buchstab identity sums the densities. Since `exp(-ε L^(1/2))` beats every
power of `T0 = exp(L^(1/3))` the exponent 6 is one admissible choice. This is the `T0` power form
of the proved log power statement `LowerShortC165.leaf_rough_interval_density`. -/
theorem leaf_rough_window (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, C ≤ x → ∀ z : ℕ,
      (2 * x ^ (11 / 20 + ε)) ^ (1 / 10 : ℝ) ≤ (z : ℝ) →
      ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ 2 * x ^ (11 / 20 + ε) →
        |∑ n ∈ Finset.Ioc a b, (Task308.roughIndicator n z -
            ω (Real.log n / Real.log z) / Real.log z)| ≤
          C * b * (perronT0 x ^ 6)⁻¹ := by
  sorry

/-- LEAF: P0069 page 51 display 5.17, the outer primes `p1`, `p2`, `p3`, `p4` of the E4 term,
"a straightforward consequence of the prime number theorem, with error term
`Y exp(-ε L^(1/2))`". Class HARD. With the rough cofactor `n5 = m / (p1 p2 p3 p4)` replaced by
its Buchstab density at level `p4`, the sum over prime quadruples with exponents in E4 has local
density the E4 integral of page 51 with `1` replaced by `s`, over `log Z`, at `m = Z^s`, with
error `Y T0^(-5)` on every integer subinterval of J. This is the window form of the proved
prefix statement `LowerShortC165.leaf_four_density_main`. -/
theorem leaf_four_main_window (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ a b : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ ≤ a →
      b ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc a b,
        ((∑ i ∈ ((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
              (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
              i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
                i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
                lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
                  (expo ε x i.2.2.2)),
            if i.1 * i.2.1 * i.2.2.1 * i.2.2.2 ∣ m then
              ω (Real.log ((m / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2) : ℕ) : ℝ) /
                  Real.log (i.2.2.2 : ℝ)) / Real.log (i.2.2.2 : ℝ)
            else 0) -
          lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := by
  sorry

/-! ### Proved steps -/

/-- PROVED. P0069 page 51 display 5.17: the rough density estimate summed over the outer
prime products `d i ≤ L`, as `LowerShortC165.rough_family_density_sum` with a general error
`E ≥ 0` in place of a log power. -/
theorem rough_family_density_sum_E (ω : ℝ → ℝ) {c C E X : ℝ} (hC : 0 < C) (hE : 0 ≤ E)
    (hmain : ∀ z : ℕ, X ^ c ≤ (z : ℝ) → ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
      |∑ n ∈ Finset.Ioc a b, (Task308.roughIndicator n z -
          ω (Real.log n / Real.log z) / Real.log z)| ≤ C * b * E)
    {ι : Type} (I : Finset ι) (d z : ι → ℕ) (L U : ℕ) (M : ℝ)
    (hI : ∀ i ∈ I, 1 ≤ d i ∧ d i ≤ L ∧ X ^ c ≤ (z i : ℝ)) (hU : (U : ℝ) ≤ X)
    (hM : ∑ i ∈ I, (1 : ℝ) / (d i : ℝ) ≤ M) :
    |∑ m ∈ Finset.Ioc L U, ∑ i ∈ I, (if d i ∣ m then
        Task308.roughIndicator (m / d i) (z i) -
          ω (Real.log ((m / d i : ℕ) : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ)
        else 0)| ≤ C * M * U * E := by
  have hUnn : (0 : ℝ) ≤ (U : ℝ) := Nat.cast_nonneg U
  rw [Finset.sum_comm]
  have hterm : ∀ i ∈ I, |∑ m ∈ Finset.Ioc L U, (if d i ∣ m then
        Task308.roughIndicator (m / d i) (z i) -
          ω (Real.log ((m / d i : ℕ) : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ)
        else 0)| ≤ C * U * E * ((1 : ℝ) / (d i : ℝ)) := by
    intro i hi
    obtain ⟨hd1, hdL, hz⟩ := hI i hi
    have hd0 : 0 < d i := hd1
    rw [real_sum_dvd_reindex hd1 L U
      (fun m => Task308.roughIndicator (m / d i) (z i) -
          ω (Real.log ((m / d i : ℕ) : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ))]
    have hre : ∑ n ∈ Finset.Ioc (L / d i) (U / d i),
        (Task308.roughIndicator (d i * n / d i) (z i) -
          ω (Real.log ((d i * n / d i : ℕ) : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ)) =
        ∑ n ∈ Finset.Ioc (L / d i) (U / d i),
          (Task308.roughIndicator n (z i) -
            ω (Real.log (n : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ)) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Nat.mul_div_cancel_left n hd0]
    rw [hre]
    have hcast : ((U / d i : ℕ) : ℝ) ≤ (U : ℝ) / (d i : ℝ) := Nat.cast_div_le
    have hUd : (U : ℝ) / (d i : ℝ) ≤ U :=
      div_le_self hUnn (by exact_mod_cast hd1)
    have hb := hmain (z i) hz (L / d i) (U / d i)
      (Nat.div_pos hdL hd0) (hcast.trans (hUd.trans hU))
    calc |∑ n ∈ Finset.Ioc (L / d i) (U / d i),
          (Task308.roughIndicator n (z i) -
            ω (Real.log (n : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ))|
        ≤ C * ((U / d i : ℕ) : ℝ) * E := hb
      _ ≤ C * ((U : ℝ) / (d i : ℝ)) * E :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcast hC.le) hE
      _ = C * U * E * ((1 : ℝ) / (d i : ℝ)) := by ring
  have hK : 0 ≤ C * U * E := mul_nonneg (mul_nonneg hC.le hUnn) hE
  calc |∑ i ∈ I, ∑ m ∈ Finset.Ioc L U, (if d i ∣ m then
        Task308.roughIndicator (m / d i) (z i) -
          ω (Real.log ((m / d i : ℕ) : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ)
        else 0)|
      ≤ ∑ i ∈ I, C * U * E * ((1 : ℝ) / (d i : ℝ)) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = C * U * E * ∑ i ∈ I, (1 : ℝ) / (d i : ℝ) := by rw [Finset.mul_sum]
    _ ≤ C * U * E * M := mul_le_mul_of_nonneg_left hM hK
    _ = C * M * U * E := by ring

/-- PROVED. The reciprocal sum over the quadruples, `(1 + log 2Y)^4`, is at most
`T0 = exp(L^(1/3))` once `L^(1/3) ≥ 81 * 13!`, by `u^13 / 13! ≤ exp u`. -/
theorem log_four_le_perronT0 {ε x : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hx : Real.exp ((81 * (Nat.factorial 13 : ℝ)) ^ 3) ≤ x) :
    (1 + Real.log (2 * x ^ (11 / 20 + ε))) ^ 4 ≤ perronT0 x := by
  set K : ℝ := 81 * (Nat.factorial 13 : ℝ) with hK
  have hK1 : 1 ≤ K := by
    have h13 : 1 ≤ Nat.factorial 13 := Nat.one_le_iff_ne_zero.mpr (Nat.factorial_ne_zero 13)
    have : (1 : ℝ) ≤ (Nat.factorial 13 : ℝ) := by exact_mod_cast h13
    rw [hK]; linarith
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hx
  have hL : K ^ 3 ≤ Real.log x := by
    rw [← Real.log_exp (K ^ 3)]; exact Real.log_le_log (Real.exp_pos _) hx
  set L := Real.log x with hLdef
  have hK3 : 1 ≤ K ^ 3 := one_le_pow₀ hK1
  have hL1 : 1 ≤ L := le_trans hK3 hL
  set u := L ^ (1 / 3 : ℝ) with hu
  have hu3 : u ^ 3 = L := by
    rw [hu, ← Real.rpow_natCast, ← Real.rpow_mul (by linarith)]; norm_num
  have hu0 : 0 ≤ u := Real.rpow_nonneg (by linarith) _
  have huK : K ≤ u := by
    by_contra h
    push_neg at h
    have : u ^ 3 < K ^ 3 := pow_lt_pow_left₀ h hu0 (by norm_num)
    linarith
  -- `1 + log (2Y) ≤ 3 L`
  have hY0 : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx0 _
  have hlogY : Real.log (x ^ (11 / 20 + ε)) = (11 / 20 + ε) * L := Real.log_rpow hx0 _
  have hlog2Y : Real.log (2 * x ^ (11 / 20 + ε)) = Real.log 2 + (11 / 20 + ε) * L := by
    rw [Real.log_mul (by norm_num) hY0.ne', hlogY]
  have hl2 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hA0 : 0 ≤ 1 + Real.log (2 * x ^ (11 / 20 + ε)) := by
    rw [hlog2Y]; nlinarith
  have hA3 : 1 + Real.log (2 * x ^ (11 / 20 + ε)) ≤ 3 * u ^ 3 := by
    rw [hlog2Y, hu3]; nlinarith
  have hpow : (1 + Real.log (2 * x ^ (11 / 20 + ε))) ^ 4 ≤ (3 * u ^ 3) ^ 4 :=
    pow_le_pow_left₀ hA0 hA3 4
  have hexp := Real.pow_div_factorial_le_exp u hu0 13
  have hT : perronT0 x = Real.exp u := by unfold perronT0; rw [← hLdef, ← hu]
  rw [hT]
  have hfac : (0 : ℝ) < (Nat.factorial 13 : ℝ) := by exact_mod_cast Nat.factorial_pos 13
  have hu12 : 0 ≤ u ^ 12 := by positivity
  have key : (3 * u ^ 3) ^ 4 ≤ u ^ 13 / (Nat.factorial 13 : ℝ) := by
    rw [le_div_iff₀ hfac]
    have e1 : (3 * u ^ 3) ^ 4 * (Nat.factorial 13 : ℝ) = u ^ 12 * K := by rw [hK]; ring
    have e2 : u ^ 13 = u ^ 12 * u := by ring
    rw [e1, e2]
    exact mul_le_mul_of_nonneg_left huK hu12
  linarith

/-- PROVED from `leaf_rough_window` and `leaf_four_main_window`, CONDITIONAL ON them. The exact
statement of `DQ517Window.leaf_four_window`, P0069 page 51 display 5.17, the E4 term on every
integer subinterval of J. Route of `four_rough_density_of_leaves`: the E4 sum is the family sum
`four_terms_eq_family`; `family_density_split` separates the rough step from the outer step;
the rough step is summed by `rough_family_density_sum_E` with the reciprocal sum
`four_reciprocal_sum_le`, which `log_four_le_perronT0` absorbs into one power of `T0`. -/
theorem leaf_four_window_of_leaves (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ a b : ℕ, ⌊x ^ (11 / 20 + ε)⌋₊ ≤ a →
      b ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ →
      |∑ m ∈ Finset.Ioc a b, (lowerFourTerms ε x m -
          lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * (perronT0 x ^ 5)⁻¹ := by
  obtain ⟨C0, hC0, hR⟩ := leaf_rough_window ω hω hz hε hε8
  obtain ⟨C1, hM⟩ := leaf_four_main_window ω hω hz hε hε8
  set K : ℝ := Real.exp ((81 * (Nat.factorial 13 : ℝ)) ^ 3) with hKdef
  refine ⟨max (max (2 * C0 + C1) C0) (max C1 (max ((2 : ℝ) ^ 12) K)), ?_⟩
  intro x hx a b ha hb
  have hxC : 2 * C0 + C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hxC0 : C0 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxC1 : C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx12 : (2 : ℝ) ^ 12 ≤ x := le_trans (le_trans (le_trans (le_max_left _ _)
    (le_max_right _ _)) (le_max_right _ _)) hx
  have hxK : K ≤ x := le_trans (le_trans (le_trans (le_max_right _ _)
    (le_max_right _ _)) (le_max_right _ _)) hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx12
  have hY43 : (4 : ℝ) ^ 3 ≤ x ^ (11 / 20 + ε) := by
    refine Decomp514a.four_shortY_ge_of_sq_le hε hx1 ?_
    have h43 : ((4 : ℝ) ^ 3) ^ 2 = (2 : ℝ) ^ 12 := by norm_num
    rw [h43]
    exact hx12
  set Y := x ^ (11 / 20 + ε) with hYdef
  have hY1 : (1 : ℝ) ≤ Y := le_trans (by norm_num) hY43
  set T := perronT0 x with hTdef
  have hT1 : 1 ≤ T := by
    rw [hTdef]; unfold perronT0
    exact Real.one_le_exp (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  have hT0 : 0 < T := by linarith
  have hCnn : 0 ≤ max (max (2 * C0 + C1) C0) (max C1 (max ((2 : ℝ) ^ 12) K)) :=
    le_trans (by norm_num) (le_trans (le_max_left _ _) (le_max_right _ _) |>.trans
      (le_max_right _ _))
  have hscale : 0 ≤ Y * (T ^ 5)⁻¹ := by positivity
  rcases lt_or_ge b a with hba | hab
  · rw [Finset.Ioc_eq_empty (by omega), Finset.sum_empty, abs_zero]
    have := mul_nonneg hCnn hscale
    calc (0 : ℝ) ≤ _ := this
      _ = _ := by ring
  set N := ⌊2 * Y⌋₊ with hN
  have hNle : (N : ℝ) ≤ 2 * Y := Nat.floor_le (by linarith)
  have hN1 : 1 ≤ N := Nat.le_floor (by rw [Nat.cast_one]; linarith)
  have hbR : (b : ℝ) ≤ 2 * Y := (Nat.cast_le.mpr hb).trans hNle
  set I := ((Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N) ×ˢ
          (Finset.Icc 1 N)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
          i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
            i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
            lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
              (expo ε x i.2.2.2)) with hIdef
  have hsp := family_density_split I (Finset.Ioc a b)
      (lowerFourTerms ε x)
      (fun m : ℕ => lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))
      (fun (i : ℕ × ℕ × ℕ × ℕ) (m : ℕ) =>
        Task308.roughIndicator (m / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2)) i.2.2.2)
      (fun (i : ℕ × ℕ × ℕ × ℕ) (m : ℕ) =>
        ω (Real.log ((m / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2) : ℕ) : ℝ) /
            Real.log (i.2.2.2 : ℝ)) / Real.log (i.2.2.2 : ℝ))
      (fun (i : ℕ × ℕ × ℕ × ℕ) (m : ℕ) => i.1 * i.2.1 * i.2.2.1 * i.2.2.2 ∣ m)
      (fun m hm => by
        have hm' := Finset.mem_Ioc.mp hm
        exact Decomp514a.four_terms_eq_family ε x (by omega) (hm'.2.trans hb))
  have hRx := hR x hxC0
  have hM4 : ∑ i ∈ I, (1 : ℝ) / ((i.1 * i.2.1 * i.2.2.1 * i.2.2.2 : ℕ) : ℝ) ≤
      (1 + Real.log N) ^ 4 :=
    Decomp514a.four_reciprocal_sum_le N I (Finset.filter_subset _ _)
  have h1 := rough_family_density_sum_E ω hC0 (E := (T ^ 6)⁻¹) (by positivity)
      (X := 2 * Y) (c := 1 / 10)
      (fun z hz a' b' ha' hb' => hRx z hz a' b' ha' hb')
      I (fun i : ℕ × ℕ × ℕ × ℕ => i.1 * i.2.1 * i.2.2.1 * i.2.2.2)
      (fun i : ℕ × ℕ × ℕ × ℕ => i.2.2.2) a b ((1 + Real.log N) ^ 4)
      (by
        intro i hi
        obtain ⟨-, hp1, hp2, hp3, hp4, -, -, -, hreg⟩ := Finset.mem_filter.mp hi
        obtain ⟨hb1, hb2⟩ := Decomp514a.four_outer_bounds hε hε8 hY43 hp1 hp2 hp3 hp4 hreg
        exact ⟨Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp1.pos hp2.pos) hp3.pos) hp4.pos,
          hb1.trans ha, hb2⟩)
      hbR hM4
  have h2 := hM x hxC1 a b ha hb
  -- the reciprocal sum is absorbed by one power of `T0`
  have hNR : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hlogN0 : 0 ≤ Real.log (N : ℝ) := Real.log_nonneg hNR
  have hlogN : Real.log (N : ℝ) ≤ Real.log (2 * Y) := Real.log_le_log (by linarith) hNle
  have hMT : (1 + Real.log N) ^ 4 ≤ T :=
    (pow_le_pow_left₀ (by linarith) (by linarith) 4).trans
      (log_four_le_perronT0 hε hε8 hxK)
  have hb0 : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have hM0 : 0 ≤ (1 + Real.log N) ^ 4 := by positivity
  have h3 : C0 * (1 + Real.log N) ^ 4 * b * (T ^ 6)⁻¹ ≤ 2 * C0 * (Y * (T ^ 5)⁻¹) := by
    calc C0 * (1 + Real.log N) ^ 4 * b * (T ^ 6)⁻¹ ≤ C0 * T * (2 * Y) * (T ^ 6)⁻¹ := by
          gcongr
      _ = 2 * C0 * (Y * (T ^ 5)⁻¹) := by field_simp
  refine (congrArg abs hsp).le.trans ((abs_add_le _ _).trans
    ((add_le_add (h1.trans h3) h2).trans ?_))
  calc 2 * C0 * (Y * (T ^ 5)⁻¹) + C1 * Y * (T ^ 5)⁻¹
      = (2 * C0 + C1) * (Y * (T ^ 5)⁻¹) := by ring
    _ ≤ max (max (2 * C0 + C1) C0) (max C1 (max ((2 : ℝ) ^ 12) K)) * (Y * (T ^ 5)⁻¹) :=
        mul_le_mul_of_nonneg_right (le_trans (le_max_left _ _) (le_max_left _ _)) hscale
    _ = _ := by ring

/-- PROVED. The assembly has the exact type of the LEAF `DQ517Window.leaf_four_window`. -/
example : type_of% @DQ517Window.leaf_four_window := @leaf_four_window_of_leaves

end LeanLab.BHP1997.DQ517FourWindow

#print axioms LeanLab.BHP1997.DQ517FourWindow.rough_family_density_sum_E
#print axioms LeanLab.BHP1997.DQ517FourWindow.log_four_le_perronT0
#print axioms LeanLab.BHP1997.DQ517FourWindow.leaf_four_window_of_leaves
