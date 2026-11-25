/-
Split of `leaf_case3_block_right` along P0088 page 12, Case 3 of the proof
of Lemma 3.4: the Lemma 3.3 reduction to a bilinear form in v = p d1 with
L^B ≤ v ≤ V, then Lemma 3.2 with divisor bounded coefficients b_u.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.SPLIT_leaf_large_cutoff_right_half

namespace LeanLab.KumchevLiu2007.Eq33RouteD

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators Topology ArithmeticFunction
attribute [local instance] Classical.propDecidable

/-- Diophantine step used to wire `leaf_lemma32_tau_right` to
`leaf_lemma32_liu_zhan`: an approximation v/q to α at level L2, that is
L2 < q ≤ H / L2 and |q α - v| < L2 / H, yields by the Dirichlet theorem a
reduced approximation v'/q' at the lower level L1, provided
L1 L2 / H + L1 / L2 ≤ 1. Elementary, no citation. -/
theorem reapprox_lower_level (α : ℝ) (q : ℕ) (v : ℤ) (hcop : IsCoprime v (q : ℤ))
    (L1 L2 H : ℝ) (hL1 : 0 < L1) (hL2 : 0 < L2) (hH : 0 < H) (hL12 : L1 ≤ L2)
    (hq1 : L2 < (q : ℝ)) (hq2 : (q : ℝ) ≤ H / L2) (hclose : |(q : ℝ) * α - v| < (H / L2)⁻¹)
    (hkey : L1 * L2 / H + L1 / L2 ≤ 1) :
    ∃ q' : ℕ, ∃ v' : ℤ, IsCoprime v' (q' : ℤ) ∧ L1 < (q' : ℝ) ∧ (q' : ℝ) ≤ H / L1 ∧
      |(q' : ℝ) * α - v'| < (H / L1)⁻¹ := by
  have hQq : H / L2 ≤ H / L1 := div_le_div_of_nonneg_left hH.le hL1 hL12
  have hq0 : (0 : ℝ) < q := hL2.trans hq1
  have hq1' : (1 : ℝ) ≤ q := by
    have : 0 < q := by exact_mod_cast hq0
    exact_mod_cast this
  set Q := H / L1 with hQ
  have hQ1 : 1 ≤ Q := hq1'.trans (hq2.trans hQq)
  set n := ⌊Q⌋₊ with hn
  have hnpos : 0 < n := Nat.floor_pos.mpr hQ1
  obtain ⟨j, k, hk0, hkn, hjk⟩ := Real.exists_int_int_abs_mul_sub_le α hnpos
  have hQlt : Q < (n : ℝ) + 1 := Nat.lt_floor_add_one Q
  have hQ0 : 0 < Q := by linarith
  have hjk' : |(k : ℝ) * α - j| < Q⁻¹ := by
    refine lt_of_le_of_lt hjk ?_
    rw [one_div]
    exact inv_strictAnti₀ hQ0 hQlt
  -- reduce j / k
  set g := Int.gcd j k with hg
  have hg0 : 0 < g := Int.gcd_pos_of_ne_zero_right j hk0.ne'
  have hgj : (g : ℤ) ∣ j := Int.gcd_dvd_left j k
  have hgk : (g : ℤ) ∣ k := Int.gcd_dvd_right j k
  obtain ⟨j', hj'⟩ := hgj
  obtain ⟨k', hk'⟩ := hgk
  have hgz : (0 : ℤ) < g := by exact_mod_cast hg0
  have hk'0 : 0 < k' := by
    rw [hk'] at hk0
    exact pos_of_mul_pos_right hk0 hgz.le
  have hcop' : IsCoprime j' k' := by
    rw [Int.isCoprime_iff_gcd_eq_one]
    have h := Int.gcd_div_gcd_div_gcd (i := j) (j := k) hg0
    rw [← hg] at h
    have e1 : j / (g : ℤ) = j' := by rw [hj']; exact Int.mul_ediv_cancel_left _ hgz.ne'
    have e2 : k / (g : ℤ) = k' := by rw [hk']; exact Int.mul_ediv_cancel_left _ hgz.ne'
    rw [e1, e2] at h
    exact h
  have hgR : (1 : ℝ) ≤ (g : ℝ) := by exact_mod_cast hg0
  have hred : |(k' : ℝ) * α - j'| < Q⁻¹ := by
    have h1 : (k : ℝ) * α - j = (g : ℝ) * ((k' : ℝ) * α - j') := by
      rw [hk', hj']; push_cast; ring
    rw [h1, abs_mul, abs_of_pos (by linarith : (0 : ℝ) < g)] at hjk'
    have h2 : 0 ≤ |(k' : ℝ) * α - j'| := abs_nonneg _
    nlinarith
  have hk'le : (k' : ℝ) ≤ Q := by
    have h1 : (k' : ℝ) ≤ (k : ℝ) := by
      rw [hk']; push_cast
      have : (0 : ℝ) < k' := by exact_mod_cast hk'0
      nlinarith
    have h2 : (k : ℝ) ≤ (n : ℝ) := by exact_mod_cast hkn
    exact h1.trans (h2.trans (Nat.floor_le hQ0.le))
  refine ⟨k'.toNat, j', ?_, ?_, ?_, ?_⟩
  · rw [Int.toNat_of_nonneg hk'0.le]; exact hcop'
  · have hcast : ((k'.toNat : ℕ) : ℝ) = (k' : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hk'0.le]
    rw [hcast]
    by_contra hle0
    have hle : (k' : ℝ) ≤ L1 := not_lt.mp hle0
    -- N = v k' - j' q is an integer of absolute value below 1
    have hN : |((v * k' - j' * (q : ℤ) : ℤ) : ℝ)| < 1 := by
      have e : ((v * k' - j' * (q : ℤ) : ℤ) : ℝ) =
          (k' : ℝ) * ((v : ℝ) - q * α) + (q : ℝ) * ((k' : ℝ) * α - j') := by
        push_cast; ring
      rw [e]
      have hk'R : (0 : ℝ) < k' := by exact_mod_cast hk'0
      have t1 : |(k' : ℝ) * ((v : ℝ) - q * α)| < (k' : ℝ) * (L2 / H) := by
        rw [abs_mul, abs_of_pos hk'R, abs_sub_comm]
        have : (H / L2)⁻¹ = L2 / H := inv_div H L2
        rw [this] at hclose
        exact mul_lt_mul_of_pos_left hclose hk'R
      have t2 : |(q : ℝ) * ((k' : ℝ) * α - j')| ≤ (q : ℝ) * (L1 / H) := by
        rw [abs_mul, abs_of_pos hq0]
        have : Q⁻¹ = L1 / H := by rw [hQ, inv_div]
        rw [this] at hred
        exact mul_le_mul_of_nonneg_left hred.le hq0.le
      have t3 : (k' : ℝ) * (L2 / H) ≤ L1 * L2 / H := by
        rw [mul_div_assoc]
        exact mul_le_mul_of_nonneg_right hle (div_nonneg hL2.le hH.le)
      have t4 : (q : ℝ) * (L1 / H) ≤ L1 / L2 := by
        calc (q : ℝ) * (L1 / H) ≤ H / L2 * (L1 / H) :=
              mul_le_mul_of_nonneg_right hq2 (div_nonneg hL1.le hH.le)
          _ = L1 / L2 := by field_simp
      calc |(k' : ℝ) * ((v : ℝ) - q * α) + (q : ℝ) * ((k' : ℝ) * α - j')|
          ≤ |(k' : ℝ) * ((v : ℝ) - q * α)| + |(q : ℝ) * ((k' : ℝ) * α - j')| := abs_add_le _ _
        _ < L1 * L2 / H + L1 / L2 := by linarith
        _ ≤ 1 := hkey
    have hN0 : v * k' - j' * (q : ℤ) = 0 := by
      have : |v * k' - j' * (q : ℤ)| < 1 := by
        have h := hN
        rw [← Int.cast_abs] at h
        exact_mod_cast h
      exact Int.abs_lt_one_iff.mp this
    have hdvd : (q : ℤ) ∣ v * k' := ⟨j', by linarith⟩
    have hqk : (q : ℤ) ∣ k' := hcop.symm.dvd_of_dvd_mul_left hdvd
    have hqle : (q : ℤ) ≤ k' := Int.le_of_dvd hk'0 hqk
    have hqleR : (q : ℝ) ≤ (k' : ℝ) := by exact_mod_cast hqle
    linarith
  · have hcast : ((k'.toNat : ℕ) : ℝ) = (k' : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hk'0.le]
    rw [hcast]; exact hk'le
  · have hcast : ((k'.toNat : ℕ) : ℝ) = (k' : ℝ) := by
      rw [← Int.cast_natCast, Int.toNat_of_nonneg hk'0.le]
    rw [hcast]; exact hred

/-- LEAF: P0088 page 10, Lemma 3.2, cited to Liu and Zhan 1997 Lemma 3.2,
with |a_m| ≤ 1 and |b_k| ≤ tau(k)^c as in the paper, lab form with
x = Y / 2, t over [Y / 2, Y], y = H, L^B ≤ M ≤ y x^(-1/2) L^(-B), m ~ M read
as M ≤ m < 2M. B0 may depend on A and c. Class HARD, cited type II. -/
theorem leaf_lemma32_tau_right (A : ℝ) (hA : 0 < A) (c : ℕ) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ v : ℤ, IsCoprime v (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - v| < (H / Real.log X ^ B)⁻¹ →
        ∀ a b : ℕ → ℂ, (∀ m : ℕ, ‖a m‖ ≤ 1) →
        (∀ k : ℕ, ‖b k‖ ≤ (k.divisors.card : ℝ) ^ c) →
        ∀ M : ℝ, Real.log X ^ B ≤ M →
        M ≤ H / Real.sqrt (windowY X ε / 2) / Real.log X ^ B →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ n ∈ (squareWindow (windowY X ε)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
            (∑ m ∈ n.divisors.filter (fun m : ℕ => M ≤ (m : ℝ) ∧ (m : ℝ) < 2 * M),
                a m * b (n / m)) *
              fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B0, hB0, hLZ⟩ := LargeRight1122.leaf_lemma32_liu_zhan c A hA
  refine ⟨B0 + 1, by linarith, ?_⟩
  intro B hB ε hε
  obtain ⟨C, X1, hC, hX1, hmain⟩ := hLZ (B - 1) (by linarith) ε hε
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    ((isLittleO_log_rpow_rpow_atTop (2 * B - 1) (by norm_num : (0 : ℝ) < 7 / 18)).bound
      (by norm_num : (0 : ℝ) < 1 / 2))
  refine ⟨C, max X1 (max T (Real.exp 2)), hC, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hlow hhigh α q v hcop hqP hqQ hclose a b ha hb M hM1 hM2
  have hXX1 : X1 ≤ X := (le_max_left _ _).trans hX
  have hXT : T ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hXe : Real.exp 2 ≤ X := ((le_max_right _ _).trans (le_max_right _ _)).trans hX
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos 2) hXe
  have hX1' : 1 ≤ X := le_trans (by linarith [Real.add_one_le_exp (2 : ℝ)]) hXe
  have hL2 : 2 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]; exact hXe
  have hL : 0 < Real.log X := by linarith
  have hLB : 0 < Real.log X ^ B := Real.rpow_pos_of_pos hL B
  have hLB1 : 0 < Real.log X ^ (B - 1) := Real.rpow_pos_of_pos hL _
  have hsplit : Real.log X ^ B = Real.log X ^ (B - 1) * Real.log X := by
    conv_lhs => rw [show B = (B - 1) + 1 by ring]
    rw [Real.rpow_add hL, Real.rpow_one]
  have hH0 : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hX0 _) hlow
  have hpow : Real.log X ^ (2 * B - 1) ≤ 1 / 2 * X ^ (7 / 18 : ℝ) := by
    have h0 := hT X hXT
    simpa only [Real.norm_eq_abs, abs_of_pos (Real.rpow_pos_of_pos hL _),
      abs_of_pos (Real.rpow_pos_of_pos hX0 (7 / 18 : ℝ))] using h0
  have hXH : X ^ (7 / 18 : ℝ) ≤ H :=
    (Real.rpow_le_rpow_of_exponent_le hX1' (by linarith)).trans hlow
  have hprod : Real.log X ^ (B - 1) * Real.log X ^ B = Real.log X ^ (2 * B - 1) := by
    rw [← Real.rpow_add hL]; congr 1; ring
  have hkey : Real.log X ^ (B - 1) * Real.log X ^ B / H +
      Real.log X ^ (B - 1) / Real.log X ^ B ≤ 1 := by
    have e1 : Real.log X ^ (B - 1) * Real.log X ^ B / H ≤ 1 / 2 := by
      rw [hprod, div_le_iff₀ hH0]; linarith
    have e2 : Real.log X ^ (B - 1) / Real.log X ^ B ≤ 1 / 2 := by
      rw [hsplit, div_le_iff₀ (mul_pos hLB1 hL)]; nlinarith
    linarith
  have hL12 : Real.log X ^ (B - 1) ≤ Real.log X ^ B := by
    rw [hsplit]; nlinarith
  obtain ⟨q', v', hcop', hq'1, hq'2, hclose'⟩ :=
    reapprox_lower_level α q v hcop _ _ H hLB1 hLB hH0 hL12 hqP hqQ hclose hkey
  -- the coefficient a, set to zero at 0, is bounded by tau^c
  have ha' : ∀ m : ℕ, ‖(fun m : ℕ => if m = 0 then (0 : ℂ) else a m) m‖ ≤
      (m.divisors.card : ℝ) ^ c := by
    intro m
    by_cases hm : m = 0
    · simp [hm]
    · simp only [hm, ↓reduceIte]
      have hcard : (1 : ℝ) ≤ (m.divisors.card : ℝ) := by
        have : 0 < m.divisors.card :=
          Finset.card_pos.mpr ⟨m, Nat.mem_divisors_self m hm⟩
        exact_mod_cast this
      exact (ha m).trans (one_le_pow₀ hcard)
  -- the M range of the main leaf at level B - 1
  have hY0 : 0 < windowY X ε := by unfold windowY; exact Real.rpow_pos_of_pos hX0 _
  have hs2 : 0 < Real.sqrt (windowY X ε / 2) := Real.sqrt_pos.mpr (by linarith)
  have hM0 : 0 < M := lt_of_lt_of_le hLB hM1
  have hMH : M * Real.sqrt (windowY X ε / 2) * Real.log X ^ B ≤ H := by
    rw [div_div, le_div_iff₀ (mul_pos hs2 hLB)] at hM2
    linarith
  have hsqY : Real.sqrt (windowY X ε) = Real.sqrt 2 * Real.sqrt (windowY X ε / 2) := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]; congr 1; ring
  have hsqrt2 : Real.sqrt 2 ≤ 2 := by
    nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
  have hM2' : M * Real.sqrt (windowY X ε) * Real.log X ^ (B - 1) ≤ H := by
    set P := M * Real.sqrt (windowY X ε / 2) * Real.log X ^ (B - 1) with hP
    have hP0 : 0 ≤ P := by positivity
    have e1 : M * Real.sqrt (windowY X ε) * Real.log X ^ (B - 1) = Real.sqrt 2 * P := by
      rw [hsqY, hP]; ring
    have e2 : M * Real.sqrt (windowY X ε / 2) * Real.log X ^ B = Real.log X * P := by
      rw [hsplit, hP]; ring
    rw [e1]
    rw [e2] at hMH
    nlinarith
  have hM1' : Real.log X ^ (B - 1) ≤ M := hL12.trans hM1
  have hbound := hmain X H hXX1 hlow hhigh α q' v' hcop' hq'1 hq'2 hclose'
    (fun m : ℕ => if m = 0 then (0 : ℂ) else a m) b ha' hb M hM1' hM2'
  refine le_of_eq_of_le ?_ hbound
  congr 1
  funext t
  congr 2
  refine Finset.sum_congr rfl fun n _ => ?_
  congr 1
  refine Finset.sum_congr rfl fun m hm => ?_
  have hm0 : m ≠ 0 := Nat.pos_iff_ne_zero.mp
    (Nat.pos_of_mem_divisors (Finset.mem_filter.mp hm).1)
  simp [hm0]

/-- LEAF: P0088 page 12, Case 3 of Lemma 3.4: write d = d1 p p' d2 with
L^B ≤ d1 p < V ≤ d1 p p', remove p' < p, d ~ 2^j and d1 p p' ≥ V by
Lemma 3.3 at a cost L^c, split v = p d1 in [L^B, V] into dyadic blocks,
keep the worst block M. Here a_v is the coefficient of v, b_u that of
u = k p' d2 with |b_u| ≤ tau(u)^c. Class HARD. -/
theorem leaf_case3_lemma33_reduction_right :
    ∃ c : ℕ, ∀ B : ℝ, 0 < B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        ∀ j : ℕ, H / Real.sqrt (windowY X ε / 2) / Real.log X ^ B < (2 : ℝ) ^ j →
        ∃ a b : ℕ → ℂ, (∀ m : ℕ, ‖a m‖ ≤ 1) ∧
          (∀ k : ℕ, ‖b k‖ ≤ (k.divisors.card : ℝ) ^ c) ∧
          ∃ M : ℝ, Real.log X ^ B ≤ M ∧
            M ≤ H / Real.sqrt (windowY X ε / 2) / Real.log X ^ B ∧
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ n ∈ (squareWindow (windowY X ε)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (n.divisors.filter
                (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
          C * Real.log X ^ c *
          (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ n ∈ (squareWindow (windowY X ε)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
            (∑ m ∈ n.divisors.filter (fun m : ℕ => M ≤ (m : ℝ) ∧ (m : ℝ) < 2 * M),
                a m * b (n / m)) *
              fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) := by
  sorry

/-- `leaf_case3_block_right` from the two leaves above. -/
theorem leaf_case3_block_right_split (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ v : ℤ, IsCoprime v (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - v| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, 2 < z → z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        ∀ j : ℕ, H / Real.sqrt (windowY X ε / 2) / Real.log X ^ B < (2 : ℝ) ^ j →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ n ∈ (squareWindow (windowY X ε)).filter
              (fun n : ℕ => t < (n : ℝ) ^ 2 ∧ (n : ℝ) ^ 2 ≤ t + H),
            (∑ d ∈ (n.divisors.filter
                (fun d : ℕ => ∀ p : ℕ, p.Prime → p ∣ d → (p : ℝ) < z)).filter
                (fun d : ℕ => (2 : ℝ) ^ j ≤ (d : ℝ) ∧ (d : ℝ) < 2 * 2 ^ j),
              ((ArithmeticFunction.moebius d : ℤ) : ℂ)) *
              fourier ((n ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨c, hR⟩ := leaf_case3_lemma33_reduction_right
  obtain ⟨B0, hB0, hT⟩ := leaf_lemma32_tau_right (A + c) (by positivity) c
  refine ⟨B0, hB0, ?_⟩
  intro B hB ε hε
  obtain ⟨C1, X1, hC1, hX1, hT'⟩ := hT B hB ε hε
  obtain ⟨C2, X2, hC2, hX2, hR'⟩ := hR B (lt_of_lt_of_le hB0 hB) ε hε
  refine ⟨C2 * C1, max X1 X2, by positivity, hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hlow hhigh α q v hcop hqP hqQ hclose z hz2 hzY j hj
  have hXX1 : X1 ≤ X := (le_max_left _ _).trans hX
  have hXX2 : X2 ≤ X := (le_max_right _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  obtain ⟨a, b, ha, hb, M, hM1, hM2, hred⟩ :=
    hR' X H hXX2 hlow hhigh α z hz2 hzY j hj
  have hbil := hT' X H hXX1 hlow hhigh α q v hcop hqP hqQ hclose a b ha hb M hM1 hM2
  refine hred.trans ?_
  have hLc : 0 ≤ C2 * Real.log X ^ c := by positivity
  calc C2 * Real.log X ^ c * _ ≤ C2 * Real.log X ^ c * (C1 * H ^ 2 / Real.log X ^ (A + c)) :=
        mul_le_mul_of_nonneg_left hbil hLc
    _ = C2 * C1 * H ^ 2 / Real.log X ^ A := by
        rw [Real.rpow_add hL, Real.rpow_natCast]
        have h1 : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hL _
        have h2 : 0 < Real.log X ^ c := pow_pos hL _
        field_simp

end LeanLab.KumchevLiu2007.Eq33RouteD

#print axioms LeanLab.KumchevLiu2007.Eq33RouteD.leaf_case3_block_right_split
