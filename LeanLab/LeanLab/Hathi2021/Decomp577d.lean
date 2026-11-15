/-
Hu 2019 page 195 and Rieger 1968 pages 94 to 96, Satz 3.
DOI https://doi.org/10.1515/crll.1968.231.89
Finite Fourier reduction of the prime square fourth moment.
AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.Hathi2021.Decomp577b

open Finset Real MeasureTheory Filter Topology
open LeanLab.Hathi2021.Decomp319a LeanLab.Hathi2021.Decomp570b

namespace LeanLab.Hathi2021.Decomp577d

/-- Helper for Hu page 195 and Rieger page 94. The second moment of a
finite real weighted Fourier sum is its equal frequency energy. -/
theorem finite_fourier_second_moment {ι : Type*} (P : Finset ι)
    (w : ι → ℝ) (m : ι → ℤ) :
    (∫ x in Set.Icc (0 : ℝ) 1, ‖∑ i ∈ P, (w i : ℂ) * e ((m i : ℝ) * x)‖ ^ 2) =
      ∑ i ∈ P, ∑ j ∈ P, if m i = m j then w i * w j else 0 := by
  classical
  let F : ℝ → ℂ := fun x => ∑ i ∈ P, (w i : ℂ) * e ((m i : ℝ) * x)
  have hFc : Continuous F := by dsimp [F]; unfold e; fun_prop
  have hprod : IntegrableOn (fun x => F x * (starRingEnd ℂ) (F x)) (Set.Icc (0 : ℝ) 1) :=
    (hFc.mul (continuous_star.comp hFc)).continuousOn.integrableOn_compact isCompact_Icc
  have hexpand (x : ℝ) : F x * (starRingEnd ℂ) (F x) =
      ∑ i ∈ P, ∑ j ∈ P, ((w i * w j : ℝ) : ℂ) * e (((m i - m j : ℤ) : ℝ) * x) := by
    dsimp [F]
    rw [map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    have heconj (t : ℝ) : (starRingEnd ℂ) (e t) = e (-t) := by
      unfold e
      rw [← Complex.exp_conj]
      congr 1
      simp only [map_mul, map_ofNat, Complex.conj_ofReal, Complex.conj_I, Complex.ofReal_neg]
      ring
    rw [map_mul, Complex.conj_ofReal, heconj]
    calc
      (w i : ℂ) * e ((m i : ℝ) * x) * ((w j : ℂ) * e (-((m j : ℝ) * x))) =
          ((w i * w j : ℝ) : ℂ) * (e ((m i : ℝ) * x) * e (-((m j : ℝ) * x))) := by
        push_cast; ring
      _ = _ := by rw [← e_add]; congr 2; push_cast; ring
  have hint : (∫ x in Set.Icc (0 : ℝ) 1, F x * (starRingEnd ℂ) (F x)) =
      ((∑ i ∈ P, ∑ j ∈ P, if m i = m j then w i * w j else 0 : ℝ) : ℂ) := by
    simp_rw [hexpand]
    rw [integral_finsetSum]
    · rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro i hi
      rw [integral_finsetSum, Complex.ofReal_sum]
      · apply Finset.sum_congr rfl
        intro j hj
        rw [integral_const_mul, setIntegral_e_int]
        by_cases hm : m i = m j <;> simp [hm, sub_eq_zero]
      · intro j hj
        have hc : Continuous (fun x : ℝ => ((w i * w j : ℝ) : ℂ) *
            e (((m i - m j : ℤ) : ℝ) * x)) := by unfold e; fun_prop
        exact hc.continuousOn.integrableOn_compact isCompact_Icc
    · intro i hi
      have hc : Continuous (fun x : ℝ => ∑ j ∈ P, ((w i * w j : ℝ) : ℂ) *
          e (((m i - m j : ℤ) : ℝ) * x)) := by unfold e; fun_prop
      exact hc.continuousOn.integrableOn_compact isCompact_Icc
  have hpoint (x : ℝ) : (F x * (starRingEnd ℂ) (F x)).re = ‖F x‖ ^ 2 := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  have hre2 : (∫ x in Set.Icc (0 : ℝ) 1, (F x * (starRingEnd ℂ) (F x)).re) =
      (∫ x in Set.Icc (0 : ℝ) 1, F x * (starRingEnd ℂ) (F x)).re := by
    simpa using integral_re hprod
  have hre : (∫ x in Set.Icc (0 : ℝ) 1, ‖F x‖ ^ 2) =
      (∫ x in Set.Icc (0 : ℝ) 1, F x * (starRingEnd ℂ) (F x)).re := by
    rw [← hre2]
    exact setIntegral_congr_fun measurableSet_Icc (fun x hx => (hpoint x).symm)
  rw [hint, Complex.ofReal_re] at hre
  exact hre

/-- Hu page 192. The exact finite prime range used by T. -/
noncomputable def squarePrimes (n₁ n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter (fun p : ℕ =>
    p.Prime ∧ cutoff n₁ n < (p : ℝ) ^ 2 ∧ p ^ 2 ≤ n)

/-- Helper for Hu page 195. The log weight of an ordered pair. -/
noncomputable def pairWeight (p : ℕ × ℕ) : ℝ := Real.log p.1 * Real.log p.2

/-- Helper for Hu page 195. The integer frequency of a prime square pair. -/
def pairFrequency (p : ℕ × ℕ) : ℤ := (p.1 : ℤ) ^ 2 + (p.2 : ℤ) ^ 2

/-- Rieger page 94, the collisions C x before the parameterization in
 display 15, with four log weights and the Hu lower cutoff.
Both orders of each pair are retained. The two trivial pair matches are excluded. -/
noncomputable def offDiagonalEnergy (n₁ n : ℕ) : ℝ :=
  let Q := (squarePrimes n₁ n).product (squarePrimes n₁ n)
  ∑ i ∈ Q, ∑ j ∈ Q,
    if pairFrequency i = pairFrequency j ∧ j ≠ i ∧ j ≠ i.swap
    then pairWeight i * pairWeight j else 0

/-- Helper for Hu page 195. Squaring T gives the finite Fourier sum on
ordered prime pairs, with their exact square frequencies and log weights. -/
theorem T_sq_eq_pair_sum (n₁ n : ℕ) (x : ℝ) :
    T n₁ n x ^ 2 =
      ∑ p ∈ (squarePrimes n₁ n).product (squarePrimes n₁ n),
        (pairWeight p : ℂ) * e ((pairFrequency p : ℝ) * x) := by
  unfold T squarePrimes
  simp only [Finset.product_eq_sprod]
  rw [pow_two, Finset.sum_mul_sum, Finset.sum_product]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr rfl
  intro q hq
  dsimp [pairWeight, pairFrequency]
  calc
    (Real.log p : ℂ) * e ((p : ℝ) ^ 2 * x) *
        ((Real.log q : ℂ) * e ((q : ℝ) ^ 2 * x)) =
      ((Real.log p * Real.log q : ℝ) : ℂ) *
        (e ((p : ℝ) ^ 2 * x) * e ((q : ℝ) ^ 2 * x)) := by push_cast; ring
    _ = _ := by rw [← e_add]; congr 2; push_cast; ring

/-- Helper for Hu page 195 and Rieger page 94. The prime square fourth
moment is the full equal frequency energy of the ordered prime pairs. -/
theorem fourth_moment_eq_pair_energy (n₁ n : ℕ) :
    primeSquareFourthMoment n₁ n =
      ∑ i ∈ (squarePrimes n₁ n).product (squarePrimes n₁ n),
        ∑ j ∈ (squarePrimes n₁ n).product (squarePrimes n₁ n),
          if pairFrequency i = pairFrequency j then pairWeight i * pairWeight j else 0 := by
  rw [← finite_fourier_second_moment]
  unfold primeSquareFourthMoment
  apply setIntegral_congr_fun measurableSet_Icc
  intro x hx
  change ‖T n₁ n x‖ ^ 4 = ‖∑ p ∈ (squarePrimes n₁ n).product (squarePrimes n₁ n),
    (pairWeight p : ℂ) * e ((pairFrequency p : ℝ) * x)‖ ^ 2
  rw [← T_sq_eq_pair_sum, norm_pow, ← pow_mul]

/-- Helper for Hu page 195 and Rieger page 94. The two trivial ordered
pair matches contribute at most twice the square of the second prime weight sum.
All nontrivial collisions stay in offDiagonalEnergy. -/
theorem fourth_moment_le_diagonal_offDiagonal (n₁ n : ℕ) :
    primeSquareFourthMoment n₁ n ≤
      2 * (∑ p ∈ squarePrimes n₁ n, (Real.log p) ^ 2) ^ 2 + offDiagonalEnergy n₁ n := by
  classical
  let P := squarePrimes n₁ n
  let Q := P.product P
  have hswap (i : ℕ × ℕ) (hi : i ∈ Q) : i.swap ∈ Q := by
    apply Finset.mem_product.mpr
    have hi' := Finset.mem_product.mp hi
    exact ⟨hi'.2, hi'.1⟩
  have hterm (i j : ℕ × ℕ) :
      (if pairFrequency i = pairFrequency j then pairWeight i * pairWeight j else 0) ≤
        (if j = i then pairWeight i ^ 2 else 0) +
        (if j = i.swap then pairWeight i ^ 2 else 0) +
        (if pairFrequency i = pairFrequency j ∧ j ≠ i ∧ j ≠ i.swap
          then pairWeight i * pairWeight j else 0) := by
    by_cases hji : j = i
    · subst j
      simp only [eq_self, ite_true, ne_eq, not_true_eq_false, and_false, false_and, true_and, ite_false]
      by_cases hs : i = i.swap
      · rw [if_pos hs]; nlinarith [sq_nonneg (pairWeight i)]
      · rw [if_neg hs]; nlinarith [sq_nonneg (pairWeight i)]
    · by_cases hjs : j = i.swap
      · subst j
        have hw : pairWeight i.swap = pairWeight i := by simp [pairWeight, mul_comm]
        have hf : pairFrequency i = pairFrequency i.swap := by simp [pairFrequency, add_comm]
        simp [hji, hw, hf, pow_two]
      · by_cases hfreq : pairFrequency i = pairFrequency j <;> simp [hji, hjs, hfreq]
  have hinner (i : ℕ × ℕ) (hi : i ∈ Q) :
      (∑ j ∈ Q, ((if j = i then pairWeight i ^ 2 else 0) +
        (if j = i.swap then pairWeight i ^ 2 else 0) +
        (if pairFrequency i = pairFrequency j ∧ j ≠ i ∧ j ≠ i.swap
          then pairWeight i * pairWeight j else 0))) =
        2 * pairWeight i ^ 2 + ∑ j ∈ Q,
          if pairFrequency i = pairFrequency j ∧ j ≠ i ∧ j ≠ i.swap
          then pairWeight i * pairWeight j else 0 := by
    have h₁ : (∑ j ∈ Q, if j = i then pairWeight i ^ 2 else 0) = pairWeight i ^ 2 := by simp [hi]
    have h₂ : (∑ j ∈ Q, if j = i.swap then pairWeight i ^ 2 else 0) = pairWeight i ^ 2 := by
      simp [hswap i hi]
    rw [Finset.sum_add_distrib, Finset.sum_add_distrib, h₁, h₂]
    ring
  have hdiag : (∑ i ∈ Q, pairWeight i ^ 2) = (∑ p ∈ P, (Real.log p) ^ 2) ^ 2 := by
    dsimp [Q]
    simp only [Finset.product_eq_sprod, Finset.sum_product, pairWeight, mul_pow]
    rw [← Finset.sum_mul_sum, ← pow_two]
  rw [fourth_moment_eq_pair_energy]
  change (∑ i ∈ Q, ∑ j ∈ Q, if pairFrequency i = pairFrequency j
    then pairWeight i * pairWeight j else 0) ≤ _
  calc
    _ ≤ ∑ i ∈ Q, ∑ j ∈ Q, ((if j = i then pairWeight i ^ 2 else 0) +
        (if j = i.swap then pairWeight i ^ 2 else 0) +
        (if pairFrequency i = pairFrequency j ∧ j ≠ i ∧ j ≠ i.swap
          then pairWeight i * pairWeight j else 0)) :=
      Finset.sum_le_sum (fun i hi => Finset.sum_le_sum (fun j hj => hterm i j))
    _ = ∑ i ∈ Q, (2 * pairWeight i ^ 2 + ∑ j ∈ Q,
        if pairFrequency i = pairFrequency j ∧ j ≠ i ∧ j ≠ i.swap
        then pairWeight i * pairWeight j else 0) := Finset.sum_congr rfl hinner
    _ = _ := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, hdiag]
      rfl

/-- Helper for Hu page 195. Chebyshev theta bounds the diagonal fourth
moment contribution uniformly in the common logarithmic cutoff. -/
theorem diagonal_weight_bound (n₁ n : ℕ) (hn : 16 ≤ n) :
    2 * (∑ p ∈ squarePrimes n₁ n, (Real.log p) ^ 2) ^ 2 ≤
      (2 * Real.log 4 ^ 2) * (n : ℝ) * Real.log n ^ 2 := by
  classical
  let P := squarePrimes n₁ n
  let Q := (range (Nat.sqrt n + 1)).filter (fun p : ℕ => p.Prime)
  have hPmem (p : ℕ) (hp : p ∈ P) : p.Prime ∧ p ^ 2 ≤ n := by
    have h := Finset.mem_filter.mp hp
    exact ⟨h.2.1, h.2.2.2⟩
  have hsub : P ⊆ Q := by
    intro p hp
    have h := hPmem p hp
    simp only [Q, Finset.mem_filter, Finset.mem_range]
    exact ⟨Nat.lt_succ_iff.mpr (Nat.le_sqrt'.2 h.2), h.1⟩
  have hp0 (p : ℕ) (hp : p ∈ P) : 0 ≤ Real.log p := by
    exact Real.log_nonneg (by exact_mod_cast (hPmem p hp).1.one_le)
  have hpUpper (p : ℕ) (hp : p ∈ P) : Real.log p ≤ Real.log n := by
    have h := hPmem p hp
    apply Real.log_le_log (by exact_mod_cast h.1.pos)
    exact_mod_cast (le_trans (Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) p) h.2)
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hsumlog : (∑ p ∈ P, Real.log p) ≤ Chebyshev.theta (Nat.sqrt n : ℝ) := by
    calc
      _ ≤ ∑ p ∈ Q, Real.log p := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro p hp hnot
        have hprime := (Finset.mem_filter.mp hp).2
        exact Real.log_nonneg (by exact_mod_cast hprime.one_le)
      _ = _ := by rw [Chebyshev.theta_eq_sum_primesLE_log, Nat.primesLE_eq_filter_range]
  have hwt : (∑ p ∈ P, (Real.log p) ^ 2) ≤
      Real.log 4 * (Nat.sqrt n : ℝ) * Real.log n := by
    calc
      _ = ∑ p ∈ P, Real.log p * Real.log p := by simp only [pow_two]
      _ ≤ ∑ p ∈ P, Real.log n * Real.log p :=
        Finset.sum_le_sum (fun p hp => mul_le_mul_of_nonneg_right (hpUpper p hp) (hp0 p hp))
      _ = Real.log n * ∑ p ∈ P, Real.log p := by rw [Finset.mul_sum]
      _ ≤ Real.log n * Chebyshev.theta (Nat.sqrt n : ℝ) := mul_le_mul_of_nonneg_left hsumlog hlogn
      _ ≤ Real.log n * (Real.log 4 * (Nat.sqrt n : ℝ)) :=
        mul_le_mul_of_nonneg_left (Chebyshev.theta_le_log4_mul_x (by positivity)) hlogn
      _ = _ := by ring
  have hs0 : 0 ≤ ∑ p ∈ P, (Real.log p) ^ 2 := Finset.sum_nonneg (fun p hp => sq_nonneg _)
  have hsqrt : (Nat.sqrt n : ℝ) ^ 2 ≤ n := by exact_mod_cast Nat.sqrt_le' n
  calc
    _ ≤ 2 * (Real.log 4 * (Nat.sqrt n : ℝ) * Real.log n) ^ 2 := by gcongr
    _ = (2 * Real.log 4 ^ 2) * (Nat.sqrt n : ℝ) ^ 2 * Real.log n ^ 2 := by ring
    _ ≤ _ := by gcongr

/-- Rieger page 94. Count the nontrivial ordered prime square collisions.
The real valued sum is the cardinality of those collisions. -/
noncomputable def collisionCount (n₁ n : ℕ) : ℝ :=
  let Q := (squarePrimes n₁ n).product (squarePrimes n₁ n)
  ∑ i ∈ Q, ∑ j ∈ Q,
    if pairFrequency i = pairFrequency j ∧ j ≠ i ∧ j ≠ i.swap then (1 : ℝ) else 0

/-- Helper for Hu page 195 and Rieger page 94. Four logarithmic weights
cost at most log n to power four on the allowed prime range. -/
theorem offDiagonalEnergy_le_count (n₁ n : ℕ) (hn : 16 ≤ n) :
    offDiagonalEnergy n₁ n ≤ Real.log n ^ 4 * collisionCount n₁ n := by
  classical
  let P := squarePrimes n₁ n
  let Q := P.product P
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast (show 1 ≤ n by omega))
  have hlog (p : ℕ) (hp : p ∈ P) : 0 ≤ Real.log p ∧ Real.log p ≤ Real.log n := by
    have hm := Finset.mem_filter.mp hp
    have hpprime := hm.2.1
    have hple : p ≤ n := (Nat.le_self_pow (by norm_num : (2 : ℕ) ≠ 0) p).trans hm.2.2.2
    exact ⟨Real.log_nonneg (by exact_mod_cast hpprime.one_le),
      Real.log_le_log (by exact_mod_cast hpprime.pos) (by exact_mod_cast hple)⟩
  have hw (i : ℕ × ℕ) (hi : i ∈ Q) : 0 ≤ pairWeight i ∧ pairWeight i ≤ Real.log n ^ 2 := by
    have hp := Finset.mem_product.mp hi
    have h₁ := hlog i.1 hp.1
    have h₂ := hlog i.2 hp.2
    dsimp [pairWeight]
    constructor
    · exact mul_nonneg h₁.1 h₂.1
    · simpa only [pow_two] using mul_le_mul h₁.2 h₂.2 h₂.1 hlogn
  have hpw (i j : ℕ × ℕ) (hi : i ∈ Q) (hj : j ∈ Q) :
      pairWeight i * pairWeight j ≤ Real.log n ^ 4 := by
    have h := mul_le_mul (hw i hi).2 (hw j hj).2 (hw j hj).1 (sq_nonneg (Real.log n))
    nlinarith
  unfold offDiagonalEnergy collisionCount
  change (∑ i ∈ Q, ∑ j ∈ Q,
    if pairFrequency i = pairFrequency j ∧ j ≠ i ∧ j ≠ i.swap
    then pairWeight i * pairWeight j else 0) ≤
      Real.log n ^ 4 * (∑ i ∈ Q, ∑ j ∈ Q,
        if pairFrequency i = pairFrequency j ∧ j ≠ i ∧ j ≠ i.swap then (1 : ℝ) else 0)
  simp_rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i hi
  apply Finset.sum_le_sum
  intro j hj
  split_ifs <;> simp only [mul_one, mul_zero]
  · exact hpw i j hi hj
  · exact le_rfl

/-- LEAF. Rieger 1968 page 94, Satz 3 and display 15, proved on pages 95
and 96 by displays 18 to 20. The ordered nontrivial collision count is
bounded by n divided by log n cubed. The Hu lower cutoff only removes
collisions. This leaf contains no Fourier sum, integral or logarithmic weight. -/
theorem rieger_nontrivial_collision_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n : ℕ,
      N₀ ≤ n → n ≤ n₁ → collisionCount n₁ n ≤ K * (n : ℝ) / Real.log n ^ 3 := by
  sorry

/-- Hu page 195. CONDITIONAL ON the unweighted nontrivial collision bound.
All Fourier and logarithmic weight steps are proved in this file. -/
theorem rieger_fourth_moment_bound_of_count
    (hcount : ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n : ℕ,
      N₀ ≤ n → n ≤ n₁ → collisionCount n₁ n ≤ K * (n : ℝ) / Real.log n ^ 3) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n : ℕ,
      N₀ ≤ n → n ≤ n₁ →
      primeSquareFourthMoment n₁ n ≤ K * (n : ℝ) * Real.log n ^ 2 := by
  obtain ⟨K, hK, N, hN⟩ := hcount
  refine ⟨2 * Real.log 4 ^ 2 + K, by positivity, max 16 N, ?_⟩
  intro n₁ n hn hle
  have hn16 : 16 ≤ n := (le_max_left _ _).trans hn
  have hnN : N ≤ n := (le_max_right _ _).trans hn
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hlogpos : 0 < Real.log n := Real.log_pos (by exact_mod_cast (show 1 < n by omega))
  have hlogone : 1 ≤ Real.log n := by
    have hlog16 := Real.log_le_log (by norm_num : (0 : ℝ) < 16)
      (show (16 : ℝ) ≤ n by exact_mod_cast hn16)
    have heq : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    rw [heq] at hlog16
    linarith [Real.log_two_gt_d9]
  have hoff : offDiagonalEnergy n₁ n ≤ K * (n : ℝ) * Real.log n := by
    calc
      _ ≤ Real.log n ^ 4 * collisionCount n₁ n := offDiagonalEnergy_le_count n₁ n hn16
      _ ≤ Real.log n ^ 4 * (K * (n : ℝ) / Real.log n ^ 3) := mul_le_mul_of_nonneg_left (hN n₁ n hnN hle) (by positivity)
      _ = _ := by field_simp [ne_of_gt hlogpos]
  calc
    _ ≤ 2 * (∑ p ∈ squarePrimes n₁ n, (Real.log p) ^ 2) ^ 2 + offDiagonalEnergy n₁ n :=
      fourth_moment_le_diagonal_offDiagonal n₁ n
    _ ≤ (2 * Real.log 4 ^ 2) * (n : ℝ) * Real.log n ^ 2 + K * (n : ℝ) * Real.log n :=
      add_le_add (diagonal_weight_bound n₁ n hn16) hoff
    _ ≤ (2 * Real.log 4 ^ 2) * (n : ℝ) * Real.log n ^ 2 + K * (n : ℝ) * Real.log n ^ 2 := by
      gcongr
      nlinarith
    _ = _ := by ring

/-- Hu page 195. CONDITIONAL ON Rieger's nontrivial collision count.
This supplies the exact sealed fourth moment statement with no sorry of its own. -/
theorem rieger_fourth_moment_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ N₀ : ℕ, ∀ n₁ n : ℕ,
      N₀ ≤ n → n ≤ n₁ →
      primeSquareFourthMoment n₁ n ≤ K * (n : ℝ) * Real.log n ^ 2 := by
  exact rieger_fourth_moment_bound_of_count rieger_nontrivial_collision_bound

end LeanLab.Hathi2021.Decomp577d
