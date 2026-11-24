/-
Schoenfeld 1976, Math. Comp. 30, p. 340: "A direct calculation shows that (6.18) holds for
2,657 ≤ x < 2,659". This file splits that direct calculation.

* The one numerical input is the value of the logarithmic integral at 2657,
  `li 2657 ≅ 399.5968`: a MEDIUM numerical LEAF, stated as an enclosure.
* Everything else is PROVED here: `π x = 384` on the range by a kernel computation,
  the increment `li x - li 2657 ≤ (x - 2657) / 7.87`, the bounds `log x ≥ 7.87` and
  `√x ≥ 51.5`, and the final inequality `|π x - li x| < √x log x / (8π)`.

Schoenfeld's `π` is `primeCount` and his `li` is the principal value `liPV`.

AI wrote this Lean code, Claude, ROUTE BURST S70 burst-20261122, unit direct_2657.
Binary Goldbach is OPEN.
-/
import LeanLab.BS2022GRH.PaperInputs148
import LeanLab.BS2022GRH.LiPV
import LeanLab.BS2022GRH.BrentRangeS63

namespace LeanLab.BS2022GRH.SchoenfeldFiniteS70
open Real MeasureTheory intervalIntegral Set
open LeanLab.BS2022GRH.PaperInputs148

noncomputable section

/-- LEAF: Schoenfeld 1976 p. 340, the value of `li 2657` behind "A direct calculation shows
that (6.18) holds for 2,657 ≤ x < 2,659". MEDIUM. Numerically `li 2657 ≅ 399.5968`, the
principal value logarithmic integral of Rosser-Schoenfeld 1962; stated as an enclosure. -/
theorem liPV_2657_encl : 399.59 ≤ liPV 2657 ∧ liPV 2657 ≤ 399.61 := by
  sorry

/-- For `n < 52²`, trial division by `d < 52` with `d² ≤ n` decides primality. -/
lemma trial_iff {n : ℕ} (hn : n < 2704) :
    (decide (2 ≤ n) && (List.range 52).all (fun d => d < 2 || n < d * d || n % d != 0)) = true
      ↔ n.Prime := by
  rw [Nat.prime_def_le_sqrt]
  simp only [Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, bne_iff_ne, ne_eq]
  constructor
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun m hm hms hdvd => ?_⟩
    have hmm : m * m ≤ n := Nat.le_sqrt.mp hms
    have hm52 : m < 52 := by
      by_contra hc
      have : 52 * 52 ≤ m * m := Nat.mul_le_mul (by omega) (by omega)
      omega
    have := h m hm52
    rcases this with (h1 | h1) | h1
    · omega
    · omega
    · exact h1 (Nat.mod_eq_zero_of_dvd hdvd)
  · rintro ⟨h2, h⟩
    refine ⟨h2, fun d _ => ?_⟩
    by_cases hd : d < 2
    · left; left; exact hd
    by_cases hdn : n < d * d
    · left; right; exact hdn
    right
    intro hmod
    exact h d (by omega) (Nat.le_sqrt.mpr (by omega)) (Nat.dvd_of_mod_eq_zero hmod)

/-- The number of primes below `N ≤ 2704`, through the trial division test. -/
lemma card_primes_eq {N : ℕ} (hN : N ≤ 2704) [DecidablePred Nat.Prime] :
    ((Finset.range N).filter (fun n => n.Prime)).card =
      ((Finset.range N).filter (fun n => (decide (2 ≤ n) && (List.range 52).all
        (fun d => d < 2 || n < d * d || n % d != 0)) = true)).card := by
  rw [Finset.filter_congr (fun n hn => (trial_iff (by simp at hn; omega)).symm)]

/-- `π 2657 = π 2658 = 384`: the count of primes in `range 2658` and `range 2659`. PROVED
by a kernel computation. -/
lemma card_primes_2658 [DecidablePred Nat.Prime] :
    ((Finset.range 2658).filter (fun n => n.Prime)).card = 384 ∧
      ((Finset.range 2659).filter (fun n => n.Prime)).card = 384 := by
  rw [card_primes_eq (by norm_num), card_primes_eq (by norm_num)]
  constructor <;> decide +kernel

/-- `π x = 384` for `2657 ≤ x < 2659`. -/
theorem primeCount_eq_384 (x : ℝ) (h1 : 2657 ≤ x) (h2 : x < 2659) : primeCount x = 384 := by
  have hx0 : (0 : ℝ) ≤ x := by linarith
  have hf1 : 2657 ≤ ⌊x⌋₊ := Nat.le_floor (by exact_mod_cast h1)
  have hf2 : ⌊x⌋₊ < 2659 := (Nat.floor_lt hx0).mpr (by exact_mod_cast h2)
  unfold primeCount
  obtain ⟨c1, c2⟩ := card_primes_2658
  rcases (show ⌊x⌋₊ = 2657 ∨ ⌊x⌋₊ = 2658 by omega) with h | h
  · rw [h]; exact_mod_cast c1
  · rw [h]; exact_mod_cast c2

lemma exp_eight_lt : exp 8 < 2981 := by
  have h : exp 8 = exp 1 ^ 8 := by rw [← exp_nat_mul]; norm_num
  rw [h]
  have h1 := exp_one_lt_d9
  have h0 := exp_pos 1
  calc exp 1 ^ 8 < (2.7182818286 : ℝ) ^ 8 := by gcongr
    _ < 2981 := by norm_num

/-- `7.87 ≤ log x` for `x ≥ 2657`, from `e⁸ < 2981` and `e^{0.13} ≥ 1.13`. -/
lemma log_ge_787 {x : ℝ} (hx : 2657 ≤ x) : 7.87 ≤ log x := by
  rw [le_log_iff_exp_le (by linarith)]
  have h : exp 7.87 * exp 0.13 = exp 8 := by rw [← exp_add]; norm_num
  have h2 := add_one_le_exp (0.13 : ℝ)
  have h3 := exp_eight_lt
  have h4 := exp_pos 7.87
  nlinarith

/-- `li x - li 2657 ≤ (x - 2657) / 7.87` for `2657 ≤ x`, from `1 / log t ≤ 1 / 7.87`. -/
lemma liPV_incr (x : ℝ) (hx : 2657 ≤ x) : liPV x ≤ liPV 2657 + (x - 2657) / 7.87 := by
  have hii : ∀ u v : ℝ, 2 ≤ u → 2 ≤ v →
      IntervalIntegrable (fun t => 1 / log t) MeasureTheory.volume u v := by
    intro u v hu hv
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.div continuousOn_const
    · exact Real.continuousOn_log.mono (fun t ht => by
        rw [Set.mem_uIcc] at ht
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith)
    · intro t ht
      rw [Set.mem_uIcc] at ht
      have : (1 : ℝ) < t := by rcases ht with ⟨h, _⟩ | ⟨h, _⟩ <;> linarith
      exact (Real.log_pos this).ne'
  rw [liPV_eq_add (by linarith), liPV_eq_add (by norm_num : (2 : ℝ) ≤ 2657),
    ← intervalIntegral.integral_add_adjacent_intervals (hii 2 2657 (by norm_num) (by norm_num))
      (hii 2657 x (by norm_num) (by linarith))]
  have hI : (∫ t in (2657 : ℝ)..x, 1 / log t) ≤ ∫ t in (2657 : ℝ)..x, (1 / 7.87 : ℝ) := by
    apply intervalIntegral.integral_mono_on hx (hii 2657 x (by norm_num) (by linarith))
      intervalIntegrable_const
    intro t ht
    have hl := log_ge_787 ht.1
    exact one_div_le_one_div_of_le (by norm_num) hl
  rw [intervalIntegral.integral_const, smul_eq_mul] at hI
  have : (x - 2657) * (1 / 7.87 : ℝ) = (x - 2657) / 7.87 := by ring
  linarith

/-- Schoenfeld 1976 p. 340: (6.18) holds for `2657 ≤ x < 2659`. PROVED from the LEAF
`liPV_2657_encl`. -/
theorem direct_2657_of_leaf : ∀ x : ℝ, 2657 ≤ x → x < 2659 →
    |primeCount x - liPV x| < √x * log x / (8 * π) := by
  intro x h1 h2
  obtain ⟨lo, hi⟩ := liPV_2657_encl
  have hpc := primeCount_eq_384 x h1 h2
  have hmono := BrentRangeS63.liPV_mono 2657 x (by norm_num) h1
  have hinc := liPV_incr x h1
  have hl := log_ge_787 h1
  have hs : 51.5 ≤ √x := by
    rw [le_sqrt (by norm_num) (by linarith)]; linarith
  have hpi : π < 3.1416 := pi_lt_d4
  have hpi0 : 0 < π := pi_pos
  rw [hpc, abs_sub_comm, abs_of_pos (by linarith), lt_div_iff₀ (by positivity)]
  have hprod : 51.5 * 7.87 ≤ √x * log x := by nlinarith
  have hd : liPV x - 384 ≤ 15.87 := by
    have : (x - 2657) / 7.87 ≤ 2 / 7.87 := by gcongr; linarith
    have : (2 : ℝ) / 7.87 ≤ 0.26 := by norm_num
    linarith
  have hd0 : 0 ≤ liPV x - 384 := by linarith
  nlinarith

/-! ### (6.20) with 2.444 on `[2659, 3169)` -/

/-- LEAF: Schoenfeld 1976 p. 340, the numerical table behind "(6.20) with 2.523 replaced by
2.444" for `2659 ≤ x < 3169`, evaluated at the integers. MEDIUM. For every integer `n` with
`2659 ≤ n < 3169`: `li n - π n > 0` and `(li (n+1) - π n) log n / √n < 2.444`.
Numerically the minimum of `li n - π n` is about 9.05 and the maximum of the second quantity
is about 2.44362, a thin margin of about 0.0004. -/
theorem table_6_20_low_int : ∀ n : ℕ, 2659 ≤ n → n < 3169 →
    0 < liPV n - primeCount n ∧
      (liPV (n + 1) - primeCount n) * log n / √n < 2.444 := by
  sorry

/-- `primeCount x` only depends on `⌊x⌋₊`. -/
lemma primeCount_floor (x : ℝ) : primeCount x = primeCount (⌊x⌋₊ : ℝ) := by
  unfold primeCount
  rw [Nat.floor_natCast]

/-- `exp 2 ≤ 2659`. -/
lemma exp_two_le : exp 2 ≤ 2659 := by
  have h : exp 2 = exp 1 ^ 2 := by rw [← exp_nat_mul]; norm_num
  rw [h]
  have h1 := exp_one_lt_d9
  have h0 := exp_pos 1
  nlinarith

/-- Schoenfeld 1976 p. 340, (6.20) with 2.444 on `2659 ≤ x < 3169`. PROVED from the LEAF
`table_6_20_low_int`, monotonicity of `li` and the decrease of `log x / √x` for `x ≥ e²`. -/
theorem display_6_20_low_of_leaf : ∀ x : ℝ, 2659 ≤ x → x < 3169 →
    0 < (liPV x - primeCount x) * log x / √x ∧
      (liPV x - primeCount x) * log x / √x < 2.444 := by
  intro x h1 h2
  have hx0 : (0 : ℝ) ≤ x := by linarith
  set n := ⌊x⌋₊ with hn
  have hn1 : 2659 ≤ n := Nat.le_floor (by exact_mod_cast h1)
  have hn2 : n < 3169 := (Nat.floor_lt hx0).mpr (by exact_mod_cast h2)
  have hnx : (n : ℝ) ≤ x := Nat.floor_le hx0
  have hxn : x < (n : ℝ) + 1 := Nat.lt_floor_add_one x
  have hnR : (2659 : ℝ) ≤ n := by exact_mod_cast hn1
  obtain ⟨t0, t1⟩ := table_6_20_low_int n hn1 hn2
  rw [primeCount_floor x, ← hn]
  have hm1 := BrentRangeS63.liPV_mono (n : ℝ) x (by linarith) hnx
  have hm2 := BrentRangeS63.liPV_mono x ((n : ℝ) + 1) (by linarith) hxn.le
  have hl : 0 < log x := log_pos (by linarith)
  have hs : 0 < √x := sqrt_pos.mpr (by linarith)
  have hA : 0 < liPV x - primeCount (n : ℝ) := by linarith
  refine ⟨by positivity, ?_⟩
  have e2 := exp_two_le
  have hanti : log x / √x ≤ log (n : ℝ) / √(n : ℝ) :=
    Real.log_div_sqrt_antitoneOn (show exp 2 ≤ (n : ℝ) by linarith)
      (show exp 2 ≤ x by linarith) hnx
  have hh : 0 < log x / √x := div_pos hl hs
  rw [mul_div_assoc] at t1 ⊢
  calc (liPV x - primeCount (n : ℝ)) * (log x / √x)
      ≤ (liPV ((n : ℝ) + 1) - primeCount (n : ℝ)) * (log (n : ℝ) / √(n : ℝ)) := by
        apply mul_le_mul (by linarith) hanti hh.le (by linarith)
    _ < 2.444 := t1

end

end LeanLab.BS2022GRH.SchoenfeldFiniteS70

#print axioms LeanLab.BS2022GRH.SchoenfeldFiniteS70.trial_iff
#print axioms LeanLab.BS2022GRH.SchoenfeldFiniteS70.primeCount_eq_384
#print axioms LeanLab.BS2022GRH.SchoenfeldFiniteS70.log_ge_787
#print axioms LeanLab.BS2022GRH.SchoenfeldFiniteS70.liPV_incr
#print axioms LeanLab.BS2022GRH.SchoenfeldFiniteS70.direct_2657_of_leaf
#print axioms LeanLab.BS2022GRH.SchoenfeldFiniteS70.primeCount_floor
#print axioms LeanLab.BS2022GRH.SchoenfeldFiniteS70.display_6_20_low_of_leaf
