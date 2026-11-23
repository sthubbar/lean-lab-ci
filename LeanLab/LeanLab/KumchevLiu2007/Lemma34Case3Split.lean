/-
Split of `leaf_case3_block` of `LeanLab.KumchevLiu2007.Lemma34FirstSumCases`
along Kumchev and Liu 2007, P0088, page 12, Case 3 of the proof of Lemma 3.4,
with x = Y / 4, y = H, M = 1 and V = y x^(-1/2) L^(-B).

The paper's Case 3 has three steps, and this file follows them:

* page 12, the factorization d = d1 p p' d2 and Lemma 3.3: "using Lemma 3.3
  to remove the summation conditions p' < p, p p' d1 d2 ∼ D, and d1 p p' ≥ V,
  we can show that the left side of (42) is bounded by" L^c times the mean
  square of the bilinear form in u = m k p' d2 and v = p d1 with
  L^B ≤ v ≤ V, plus a small error. The LEAF `leaf_case3_lemma33_reduction`.
* page 12, last line of Case 3, "Thus, (42) follows from Lemma 3.2": the range
  L^B ≤ v ≤ V is cut into the dyadic blocks v ∼ L^B 2^i. Proved here in
  `range_dyadic_split` and `case3_block_of_leaves`.
* page 10, Lemma 3.2 itself, in the form with |b_u| ≤ tau(u)^c that the new
  variable u = m k p' d2 needs, since the coefficient b_u is a convolution.
  The LEAF `leaf_lemma32_divisor_bounded`. The lab form
  `leaf_lemma32_type_two` has |b_k| ≤ 1 and does not cover this.

The exponent c of the paper's L^c is kept as one constant c ≥ 0, and the
divisor bound tau(u)^c as tau(u)^κ for a natural number κ.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SPLIT_lemma34_first_sum

namespace LeanLab.KumchevLiu2007.Eq33RouteD

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators Topology ArithmeticFunction
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 12, Case 3 of Lemma 3.4, the display after "using
Lemma 3.3 to remove the summation conditions", with M = 1, x = Y / 4, y = H,
D = 2^j > V = y x^(-1/2) L^(-B). The block is at most L^c times the mean
square of the form in v = p d1, L^B ≤ v ≤ V, and u = k p' d2, with |a_v| ≤ 1,
|b_u| ≤ tau(u)^κ, plus the Lemma 3.3 error, here C L^c H. The form is the sum
over n = u v of the divisor weight. Lemma 3.3 is cited to Kumchev 2006 Lemma
2.7; its Perron twists do not depend on t. Class HARD. -/
theorem leaf_case3_lemma33_reduction :
    ∃ c : ℝ, 0 ≤ c ∧ ∃ κ : ℕ, ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ v : ℤ, IsCoprime v (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - v| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        ∀ j : ℕ, H / Real.sqrt (windowY X ε / 4) / Real.log X ^ B < (2 : ℝ) ^ j →
        ∃ a b : ℕ → ℂ, (∀ m : ℕ, ‖a m‖ ≤ 1) ∧
          (∀ k : ℕ, ‖b k‖ ≤ (k.divisors.card : ℝ) ^ κ) ∧
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ n ∈ (squareWindow (windowY X ε)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (n.divisors.filter
                (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
          C * Real.log X ^ c *
            ((∫ t in (windowY X ε / 4)..(windowY X ε / 2),
              ‖∑ n ∈ (squareWindow (windowY X ε)).filter
                  (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
                (∑ m ∈ n.divisors.filter (fun m : ℕ => Real.log X ^ B ≤ (m : ℝ) ∧
                    (m : ℝ) ≤ H / Real.sqrt (windowY X ε / 4) / Real.log X ^ B),
                  a m * b (n / m)) *
                  fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) + H) := by
  sorry

/-- LEAF: P0088 page 10, Lemma 3.2, cited to Liu and Zhan 1997 Lemma 3.2, in
the lab form of `leaf_lemma32_type_two` but with the paper's bound
|b_k| ≤ tau(k)^c, here tau(k)^κ, in place of |b_k| ≤ 1; the coefficients
a_m keep |a_m| ≤ 1, the case c = 0. The paper's B0(A) may depend on the fixed
c, so B0 here depends on A and κ. Needed in Case 3 of Lemma 3.4, where
b_u is a convolution over u = m k p' d2. Class HARD, a cited type II
estimate. QUESTION: the same H range remark as `leaf_lemma31_type_one`, the
target keeps H up to X^(1 - eps), above the paper's y ≤ x. -/
theorem leaf_lemma32_divisor_bounded (A : ℝ) (hA : 0 < A) (κ : ℕ) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ v : ℤ, IsCoprime v (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - v| < (H / Real.log X ^ B)⁻¹ →
        ∀ a b : ℕ → ℂ, (∀ m : ℕ, ‖a m‖ ≤ 1) →
        (∀ k : ℕ, ‖b k‖ ≤ (k.divisors.card : ℝ) ^ κ) →
        ∀ M : ℝ, Real.log X ^ B ≤ M →
        M ≤ H / Real.sqrt (windowY X ε / 4) / Real.log X ^ B →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ n ∈ (squareWindow (windowY X ε)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
            (∑ m ∈ n.divisors.filter (fun m : ℕ => M ≤ (m : ℝ) ∧ (m : ℝ) < 2 * M),
                a m * b (n / m)) *
              fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- P0088 page 12, the dyadic blocks behind "Thus, (42) follows from
Lemma 3.2": for P > 0 a real r ≥ P lies in the block P 2^i ≤ r < 2 P 2^i
exactly for i the base 2 logarithm of the floor of r / P. -/
theorem mem_scaled_block_iff (P r : ℝ) (hP : 0 < P) (i : ℕ) :
    (P * 2 ^ i ≤ r ∧ r < 2 * (P * 2 ^ i)) ↔ (P ≤ r ∧ Nat.log 2 ⌊r / P⌋₊ = i) := by
  have h2i : (1 : ℝ) ≤ 2 ^ i := one_le_pow₀ (by norm_num)
  constructor
  · rintro ⟨h1, h2⟩
    have hPr : P ≤ r := le_trans (le_mul_of_one_le_right hP.le h2i) h1
    refine ⟨hPr, ?_⟩
    have hr0 : 0 ≤ r / P := div_nonneg (hP.le.trans hPr) hP.le
    have hlo : (2 : ℝ) ^ i ≤ r / P := by rw [le_div_iff₀ hP]; linarith
    have hhi : r / P < (2 : ℝ) ^ (i + 1) := by
      rw [div_lt_iff₀ hP, pow_succ]; linarith
    have hf1 : 2 ^ i ≤ ⌊r / P⌋₊ := by
      rw [Nat.le_floor_iff hr0]; exact_mod_cast hlo
    have hf2 : ⌊r / P⌋₊ < 2 ^ (i + 1) := by
      rw [Nat.floor_lt hr0]; exact_mod_cast hhi
    have hne : ⌊r / P⌋₊ ≠ 0 := by
      have : 1 ≤ 2 ^ i := Nat.one_le_two_pow
      omega
    exact (Nat.log_eq_iff (Or.inr ⟨by norm_num, hne⟩)).mpr ⟨hf1, hf2⟩
  · rintro ⟨hPr, hlog⟩
    have hr0 : 0 ≤ r / P := div_nonneg (hP.le.trans hPr) hP.le
    have hone : (1 : ℝ) ≤ r / P := by rw [le_div_iff₀ hP]; linarith
    have hne : ⌊r / P⌋₊ ≠ 0 := by
      have : 1 ≤ ⌊r / P⌋₊ := by rw [Nat.one_le_floor_iff]; exact hone
      omega
    obtain ⟨hf1, hf2⟩ := (Nat.log_eq_iff (Or.inr ⟨by norm_num, hne⟩)).mp hlog
    have hlo : (2 : ℝ) ^ i ≤ r / P := by
      have := (Nat.le_floor_iff hr0).mp hf1
      exact_mod_cast this
    have hhi : r / P < (2 : ℝ) ^ (i + 1) := by
      have := (Nat.floor_lt hr0).mp hf2
      exact_mod_cast this
    rw [le_div_iff₀ hP] at hlo
    rw [div_lt_iff₀ hP, pow_succ] at hhi
    constructor <;> linarith

/-- P0088 page 12, the last line of Case 3 of the proof of Lemma 3.4: the
weight over the divisors v of n with P ≤ v ≤ V, with P = L^B, is the sum of
the weights over the dyadic blocks v ∼ P 2^i for i up to the base 2
logarithm of V / P, with the coefficient a_v cut off above V. These are the
ranges m ∼ M of Lemma 3.2. -/
theorem range_dyadic_split (P V : ℝ) (hP : 0 < P) (a b : ℕ → ℂ) (n : ℕ) :
    ∑ m ∈ n.divisors.filter (fun m : ℕ => P ≤ (m : ℝ) ∧ (m : ℝ) ≤ V), a m * b (n / m) =
    ∑ i ∈ Finset.range (Nat.log 2 ⌊V / P⌋₊ + 1),
      ∑ m ∈ n.divisors.filter
          (fun m : ℕ => P * 2 ^ i ≤ (m : ℝ) ∧ (m : ℝ) < 2 * (P * 2 ^ i)),
        (if (m : ℝ) ≤ V then a m else 0) * b (n / m) := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp_rw [mem_scaled_block_iff P (m : ℝ) hP]
  by_cases hPm : P ≤ (m : ℝ)
  · simp only [hPm, true_and]
    rw [Finset.sum_ite_eq]
    by_cases hmV : (m : ℝ) ≤ V
    · have hlt : Nat.log 2 ⌊(m : ℝ) / P⌋₊ ∈ Finset.range (Nat.log 2 ⌊V / P⌋₊ + 1) := by
        rw [Finset.mem_range, Nat.lt_succ_iff]
        apply Nat.log_mono_right
        apply Nat.floor_le_floor
        exact div_le_div_of_nonneg_right hmV hP.le
      simp [hmV, hlt]
    · simp [hmV]
  · simp [hPm]

/-- P0088 page 12, Case 3 of the proof of Lemma 3.4, with M = 1: the dyadic
block 2^j ≤ d < 2^(j+1) of display 42 when 2^j exceeds
V = y x^(-1/2) L^(-B), with x = Y / 4 and y = H. The statement of
`leaf_case3_block`. The Lemma 3.3 reduction gives L^c times the mean square
of the bilinear form with L^B ≤ v ≤ V; that range is cut into at most 3 L
dyadic blocks v ∼ L^B 2^i, and each block is Lemma 3.2 with A + c + 2 in
place of A. CONDITIONAL ON leaf_case3_lemma33_reduction and
leaf_lemma32_divisor_bounded. -/
theorem case3_block_of_leaves (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ v : ℤ, IsCoprime v (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - v| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        ∀ j : ℕ, H / Real.sqrt (windowY X ε / 4) / Real.log X ^ B < (2 : ℝ) ^ j →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ n ∈ (squareWindow (windowY X ε)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (n.divisors.filter
                (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨c, hc, κ, hred⟩ := leaf_case3_lemma33_reduction
  have hA' : 0 < A + c + 2 := by linarith
  obtain ⟨B0, hB0, hL32⟩ := leaf_lemma32_divisor_bounded (A + c + 2) hA' κ
  refine ⟨B0, hB0, ?_⟩
  intro B hB ε hε
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := hred B (hB0.trans_le hB) ε hε
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := hL32 B hB ε hε
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop (A + c) (by norm_num : (0 : ℝ) < 1 / 4)).bound
      (by norm_num : (0 : ℝ) < 1))
  refine ⟨9 * C1 * C2 + C1, max (max X1 X2) (max T ((4 : ℝ) ^ 12)), by positivity,
    hX1.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro X H hX hlow hhigh α q v hcop hqP hqQ hclose z hz2 hzY j hj
  have hXX1 : X1 ≤ X := ((le_max_left _ _).trans (le_max_left _ _)).trans hX
  have hXX2 : X2 ≤ X := ((le_max_right _ _).trans (le_max_left _ _)).trans hX
  have hXT : T ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hX4 : (4 : ℝ) ^ 12 ≤ X := ((le_max_right _ _).trans (le_max_right _ _)).trans hX
  have hX0 : 0 < X := by linarith
  have hX1' : 1 ≤ X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    have := Real.exp_one_lt_d9
    linarith
  have hL0 : 0 < Real.log X := by linarith
  have hHpos : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hX0 _) hlow
  -- L^(A + c) ≤ X^(1/4) ≤ H
  have hLAc : Real.log X ^ A * Real.log X ^ c ≤ H := by
    have h := hT X hXT
    rw [← Real.rpow_add hL0]
    have h' : Real.log X ^ (A + c) ≤ X ^ (1 / 4 : ℝ) := by
      simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hL0 (A + c)),
        abs_of_pos (Real.rpow_pos_of_pos hX0 (1 / 4 : ℝ)), one_mul] using h
    exact h'.trans ((Real.rpow_le_rpow_of_exponent_le hX1' (by linarith)).trans hlow)
  -- Y / 4 ≥ 1
  have hY4 : 1 ≤ windowY X ε / 4 := by
    rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 4), one_mul]
    unfold windowY
    have h4 : (4 : ℝ) ≤ X ^ (1 / 12 : ℝ) := by
      have h := Real.rpow_le_rpow (by positivity) hX4 (by norm_num : (0 : ℝ) ≤ 1 / 12)
      have e : ((4 : ℝ) ^ 12) ^ (1 / 12 : ℝ) = 4 := by
        rw [show (1 / 12 : ℝ) = ((12 : ℕ) : ℝ)⁻¹ by norm_num]
        exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)
      linarith
    exact h4.trans (Real.rpow_le_rpow_of_exponent_le hX1' (by linarith))
  obtain ⟨a, b, ha, hb, hk1⟩ :=
    k1 X H hXX1 hlow hhigh α q v hcop hqP hqQ hclose z hz2 hzY j hj
  set L := Real.log X with hLdef
  have hP : 0 < L ^ B := Real.rpow_pos_of_pos hL0 _
  have hLB1 : 1 ≤ L ^ B := Real.one_le_rpow hL1 (hB0.trans_le hB).le
  set Y := windowY X ε with hYdef
  have hYpos : 0 < Y := by linarith
  set V := H / Real.sqrt (Y / 4) / L ^ B with hVdef
  have hsq1 : 1 ≤ Real.sqrt (Y / 4) := by
    rw [show (1 : ℝ) = Real.sqrt 1 from Real.sqrt_one.symm]
    exact Real.sqrt_le_sqrt hY4
  have hV0 : 0 ≤ V := by rw [hVdef]; positivity
  have hVH : V ≤ H := by
    rw [hVdef]
    exact (div_le_self (by positivity) hLB1).trans (div_le_self hHpos.le hsq1)
  set I := Nat.log 2 ⌊V / L ^ B⌋₊ + 1 with hIdef
  set a' : ℕ → ℂ := fun m => if (m : ℝ) ≤ V then a m else 0 with ha'def
  have ha' : ∀ m : ℕ, ‖a' m‖ ≤ 1 := by
    intro m
    simp only [ha'def]
    split_ifs
    · exact ha m
    · simp
  set W : ℕ → ℕ → ℂ := fun i n => ∑ m ∈ n.divisors.filter
      (fun m : ℕ => L ^ B * 2 ^ i ≤ (m : ℝ) ∧ (m : ℝ) < 2 * (L ^ B * 2 ^ i)),
        a' m * b (n / m) with hWdef
  set K := C2 * H ^ 2 / L ^ (A + c + 2) with hKdef
  have hK0 : 0 ≤ K := by rw [hKdef]; positivity
  -- the reduced mean square, cut into the dyadic blocks v ∼ L^B 2^i
  have hsplit : (∫ t in (Y / 4)..(Y / 2),
      ‖∑ n ∈ (squareWindow Y).filter
          (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
        (∑ m ∈ n.divisors.filter (fun m : ℕ => L ^ B ≤ (m : ℝ) ∧ (m : ℝ) ≤ V),
          a m * b (n / m)) * fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) =
      (∫ t in (Y / 4)..(Y / 2),
      ‖∑ n ∈ (squareWindow Y).filter
          (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
        (∑ i ∈ Finset.range I, W i n) *
          fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    congr 2
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [range_dyadic_split (L ^ B) V hP a b n]
  -- each dyadic block is Lemma 3.2 with A + c + 2 in place of A
  have hblk : ∀ i ∈ Finset.range I, (∫ t in (Y / 4)..(Y / 2),
      ‖∑ n ∈ (squareWindow Y).filter
          (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
        W i n * fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤ K := by
    intro i _
    by_cases hM : L ^ B * 2 ^ i ≤ V
    · exact k2 X H hXX2 hlow hhigh α q v hcop hqP hqQ hclose a' b ha' hb
        (L ^ B * 2 ^ i) (le_mul_of_one_le_right hP.le (one_le_pow₀ (by norm_num))) hM
    · have hzero : ∀ n : ℕ, W i n = 0 := by
        intro n
        simp only [hWdef]
        refine Finset.sum_eq_zero fun m hm => ?_
        have hm1 := (Finset.mem_filter.mp hm).2.1
        have hmV : ¬ (m : ℝ) ≤ V := fun h => hM (hm1.trans h)
        simp [ha'def, hmV]
      simp only [hzero, zero_mul, Finset.sum_const_zero, norm_zero]
      norm_num
      exact hK0
  have hmain := dyadic_mean_square_le (squareWindow Y) I W
    (fun n => fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H (Y / 4) (Y / 2) K
    (by linarith) hblk
  -- the number of dyadic blocks is at most 3 L
  have hI : (I : ℝ) ≤ 3 * L := by
    have hNX : (⌊V / L ^ B⌋₊ : ℝ) ≤ X := by
      have h1 : (⌊V / L ^ B⌋₊ : ℝ) ≤ V / L ^ B := Nat.floor_le (by positivity)
      have h2 : V / L ^ B ≤ V := div_le_self hV0 hLB1
      have h3 : H ≤ X := hhigh.trans (by
        calc X ^ (1 - ε) ≤ X ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le hX1' (by linarith)
          _ = X := Real.rpow_one X)
      linarith
    have hk : (Nat.log 2 ⌊V / L ^ B⌋₊ : ℝ) ≤ 2 * L := by
      rcases Nat.eq_zero_or_pos ⌊V / L ^ B⌋₊ with h0 | hpos
      · rw [h0]; simp; positivity
      · have hpow : (2 : ℝ) ^ (Nat.log 2 ⌊V / L ^ B⌋₊) ≤ (⌊V / L ^ B⌋₊ : ℝ) := by
          exact_mod_cast Nat.pow_log_le_self 2 hpos.ne'
        have hlog1 : (Nat.log 2 ⌊V / L ^ B⌋₊ : ℝ) * Real.log 2 ≤ L := by
          rw [← Real.log_pow, hLdef]
          exact Real.log_le_log (by positivity) (hpow.trans hNX)
        have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
          have := Real.log_two_gt_d9
          linarith
        have hk0 : (0 : ℝ) ≤ (Nat.log 2 ⌊V / L ^ B⌋₊ : ℝ) := Nat.cast_nonneg _
        nlinarith [mul_le_mul_of_nonneg_left hl2.le hk0]
    rw [hIdef]
    push_cast
    linarith
  have hLc : 0 < L ^ c := Real.rpow_pos_of_pos hL0 c
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hL0 A
  refine hk1.trans (le_trans (mul_le_mul_of_nonneg_left
    (add_le_add_left (hsplit.le.trans hmain) H) (by positivity)) ?_)
  have hsplitpow : L ^ (A + c + 2) = L ^ A * L ^ c * L ^ 2 := by
    rw [Real.rpow_add hL0, Real.rpow_add hL0, Real.rpow_two]
  have hI2 : (I : ℝ) ^ 2 ≤ 9 * L ^ 2 := by
    have h := pow_le_pow_left₀ (Nat.cast_nonneg I) hI 2
    rw [mul_pow] at h
    norm_num at h
    exact h
  rw [hKdef, hsplitpow]
  have e1 : C1 * L ^ c * ((I : ℝ) ^ 2 * (C2 * H ^ 2 / (L ^ A * L ^ c * L ^ 2)) + H) =
      C1 * C2 * H ^ 2 * ((I : ℝ) ^ 2 / L ^ 2) / L ^ A + C1 * (L ^ c * H) := by
    field_simp
  rw [e1]
  have t1 : (I : ℝ) ^ 2 / L ^ 2 ≤ 9 := by
    rw [div_le_iff₀ (by positivity)]
    linarith
  have t2 : L ^ c * H ≤ H ^ 2 / L ^ A := by
    rw [le_div_iff₀ hLA]
    have h := mul_le_mul_of_nonneg_left hLAc hHpos.le
    calc L ^ c * H * L ^ A = H * (L ^ A * L ^ c) := by ring
      _ ≤ H * H := h
      _ = H ^ 2 := by ring
  calc C1 * C2 * H ^ 2 * ((I : ℝ) ^ 2 / L ^ 2) / L ^ A + C1 * (L ^ c * H)
      ≤ C1 * C2 * H ^ 2 * 9 / L ^ A + C1 * (H ^ 2 / L ^ A) := by gcongr
    _ = (9 * C1 * C2 + C1) * H ^ 2 / L ^ A := by ring

end LeanLab.KumchevLiu2007.Eq33RouteD

#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.leaf_case3_lemma33_reduction
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.leaf_lemma32_divisor_bounded
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.mem_scaled_block_iff
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.range_dyadic_split
#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.case3_block_of_leaves
