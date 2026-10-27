/-
Platt, Trudgian 2014, P0024, arXiv 1404.5669v2, Sections 1 and 2.
Page images of v2 pages 2 to 5 read 2026-10-18 by CLOUD 20261018T2230Z-cloud10.

* `C2_bounds`: Pintz's 1.2783521041 < C₂C₀ < 1.2784421041 with Wrench's (3) gives
  1.93642 < C₂ < 1.93656, page 2.
* `old_admissible_12` and the three others: the "old" quintuple of page 3 gives K = 12 and,
  with c = 1/2 on GRH, K = 7, and not 11 or 6: "This proves only what is already known".
* `H`, `H_succ`, `hbp_formula`: the count H(d; N, K) of page 3 and the Heath-Brown-Puchta
  closed form quoted on page 3, PROVED for every modulus d where ν ↦ 2^ν, 1 ≤ ν ≤ d - 1,
  hits each nonzero residue once, that is 2 a primitive root mod a prime d.
* `hbp_C3_D5`: Heath-Brown and Puchta's C₃ ≥ 2.7895 with D = 5, for every K ≥ 6 and every N.
* `tail_integral`, `tail_lt`: 2 ∫_{40000}^∞ dt / (t (t - 2)) < 5.1e-5, page 5.
* `alg1`, `alg1_wrong_3_2`, `alg1_wrong_11_2`: Algorithm 1 as printed on page 4 does not
  compute min_N H(d; N, K): at d = 3, K = 2 it returns 0, the true value is 1.

AI-written Lean code, Claude, 2026-10-18. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.PlattTrudgian2014.Statements

namespace LeanLab.PlattTrudgian2014.Section2

open Finset MeasureTheory Filter Topology

/-! ## C₂ from Pintz's C₂C₀ and Wrench's C₀, page 2 -/

theorem C2_bounds (C₀ C₂ : ℝ) (h0 : 0.6601618158 < C₀) (h0' : C₀ < 0.6601618159)
    (h1 : 1.2783521041 < C₂ * C₀) (h1' : C₂ * C₀ < 1.2784421041) :
    1.93642 < C₂ ∧ C₂ < 1.93656 := by
  have hC₂ : 0 < C₂ := by
    by_contra h
    push Not at h
    nlinarith
  constructor <;> nlinarith

/-! ## The old quintuple of page 3 -/

theorem rhs_bounds_old_uncond :
    0.2464 < rhs 0.6601618159 7.8209 1.93656 2.96169 (109 / 154) ∧
      rhs 0.6601618159 7.8209 1.93656 2.96169 (109 / 154) < 0.2466 := by
  obtain ⟨h1, h2⟩ := log2_bounds
  unfold rhs
  have hd : 0 < (7.8209 - 2) * 1.93656 + 109 / 154 / 0.6601618159 * Real.log 2 := by positivity
  constructor
  · rw [lt_div_iff₀ hd]; nlinarith
  · rw [div_lt_iff₀ hd]; nlinarith

theorem rhs_bounds_old_GRH :
    0.2509 < rhs 0.6601618159 7.8209 1.93656 2.96169 (1 / 2) ∧
      rhs 0.6601618159 7.8209 1.93656 2.96169 (1 / 2) < 0.2512 := by
  obtain ⟨h1, h2⟩ := log2_bounds
  unfold rhs
  have hd : 0 < (7.8209 - 2) * 1.93656 + 1 / 2 / 0.6601618159 * Real.log 2 := by positivity
  constructor
  · rw [lt_div_iff₀ hd]; nlinarith
  · rw [div_lt_iff₀ hd]; nlinarith

/-- Page 3: the old quintuple with λ = 0.862327 gives K = 12, threshold 11.4549. -/
theorem old_admissible_12 :
    Admissible 0.862327 0.6601618159 7.8209 1.93656 2.96169 (109 / 154) 12 := by
  unfold Admissible
  have := rhs_bounds_old_uncond.1
  norm_num at this ⊢
  linarith

theorem old_not_admissible_11 :
    ¬ Admissible 0.862327 0.6601618159 7.8209 1.93656 2.96169 (109 / 154) 11 := by
  unfold Admissible
  have := rhs_bounds_old_uncond.2
  norm_num at this ⊢
  linarith

/-- Page 3: with λ = 0.716344 and c = 1/2, K = 7 on GRH, threshold 6.1432. -/
theorem old_admissible_7_GRH :
    Admissible 0.716344 0.6601618159 7.8209 1.93656 2.96169 (1 / 2) 7 := by
  unfold Admissible
  have := rhs_bounds_old_GRH.1
  norm_num at this ⊢
  linarith

theorem old_not_admissible_6_GRH :
    ¬ Admissible 0.716344 0.6601618159 7.8209 1.93656 2.96169 (1 / 2) 6 := by
  unfold Admissible
  have := rhs_bounds_old_GRH.2
  norm_num at this ⊢
  linarith

/-! ## H(d; N, K) and the Heath-Brown-Puchta formula, page 3

`H d e K a` counts tuples (ν₁, …, ν_K) with 1 ≤ νᵢ ≤ e and a = Σ 2^{νᵢ} in ZMod d;
with e = ε(d) and a = N mod d it is the paper's H(d; N, K). Here νᵢ = vᵢ + 1, vᵢ : Fin e. -/

/-- The paper's H(d; N, K), with e standing for ε(d) and `a` for N mod d. -/
def H (d e K : ℕ) (a : ZMod d) : ℕ :=
  (univ.filter fun v : Fin K → Fin e => a = ∑ i, (2 : ZMod d) ^ ((v i : ℕ) + 1)).card

theorem H_zero (d e : ℕ) (a : ZMod d) : H d e 0 a = if a = 0 then 1 else 0 := by
  unfold H
  by_cases ha : a = 0 <;> simp [ha, Finset.filter_true_of_mem, Finset.filter_false_of_mem]

/-- One power of two split off: H(K + 1) at a is the sum over ν of H(K) at a - 2^ν. -/
theorem H_succ (d e K : ℕ) (a : ZMod d) :
    H d e (K + 1) a = ∑ j : Fin e, H d e K (a - 2 ^ ((j : ℕ) + 1)) := by
  unfold H
  simp only [Finset.card_filter]
  rw [← (Fin.consEquiv (fun _ : Fin (K + 1) => Fin e)).sum_comp]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun w _ => ?_
  simp only [Fin.consEquiv_apply, Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
  congr 1
  apply propext
  constructor <;> intro h
  · rw [h]; ring
  · rw [sub_eq_iff_eq_add] at h; rw [h]; ring

theorem H_total (d e K : ℕ) [NeZero d] : ∑ a : ZMod d, H d e K a = e ^ K := by
  induction K with
  | zero => simp [H_zero]
  | succ K ih =>
    simp_rw [H_succ]
    rw [Finset.sum_comm]
    have : ∀ j : Fin e, ∑ a : ZMod d, H d e K (a - 2 ^ ((j : ℕ) + 1)) = e ^ K := fun j => by
      rw [← ih]
      exact (Equiv.subRight _).sum_comp (H d e K)
    rw [Finset.sum_congr rfl fun j _ => this j]
    simp [pow_succ, mul_comm]

/-- When the powers 2^ν, 1 ≤ ν ≤ e, run once through the nonzero residues,
H(K + 1) at a is e^K - H(K) at a. -/
theorem H_succ_of_primRoot (d e K : ℕ) [NeZero d]
    (hinj : Function.Injective fun j : Fin e => (2 : ZMod d) ^ ((j : ℕ) + 1))
    (himg : (univ.image fun j : Fin e => (2 : ZMod d) ^ ((j : ℕ) + 1)) = univ.erase 0)
    (a : ZMod d) : (H d e (K + 1) a : ℤ) + H d e K a = e ^ K := by
  rw [H_succ]
  have h1 : ∑ j : Fin e, H d e K (a - 2 ^ ((j : ℕ) + 1)) =
      ∑ x ∈ univ.erase (0 : ZMod d), H d e K (a - x) := by
    rw [← himg, Finset.sum_image fun x _ y _ h => hinj h]
  have h2 : ∑ x ∈ univ.erase (0 : ZMod d), H d e K (a - x) + H d e K a = e ^ K := by
    rw [← H_total d e K, ← (Equiv.subLeft a).sum_comp (H d e K)]
    rw [← Finset.sum_erase_add _ _ (Finset.mem_univ (0 : ZMod d))]
    simp
  rw [h1]
  exact_mod_cast h2

/-- The Heath-Brown-Puchta formula quoted on page 3, with e = d - 1:
d H = (d - 1)^K - (-1)^K for d ∤ N and d H = (d - 1)^K + (-1)^K (d - 1) for d ∣ N. -/
theorem hbp_formula (d K : ℕ) [NeZero d]
    (hinj : Function.Injective fun j : Fin (d - 1) => (2 : ZMod d) ^ ((j : ℕ) + 1))
    (himg : (univ.image fun j : Fin (d - 1) => (2 : ZMod d) ^ ((j : ℕ) + 1)) = univ.erase 0)
    (a : ZMod d) :
    (d : ℤ) * H d (d - 1) K a =
      ((d : ℤ) - 1) ^ K + (-1) ^ K * (if a = 0 then (d : ℤ) - 1 else -1) := by
  have hd : 1 ≤ d := Nat.one_le_iff_ne_zero.mpr (NeZero.ne d)
  have hcast : ((d - 1 : ℕ) : ℤ) = (d : ℤ) - 1 := by push_cast [hd]; ring
  induction K with
  | zero => by_cases ha : a = 0 <;> simp [H_zero, ha]
  | succ K ih =>
    have hs := H_succ_of_primRoot d (d - 1) K hinj himg a
    rw [hcast] at hs
    have : (H d (d - 1) (K + 1) a : ℤ) = ((d : ℤ) - 1) ^ K - H d (d - 1) K a := by linarith
    rw [this, mul_sub, ih]
    ring

/-- 2 is a primitive root mod 3 and mod 5, as the formula needs. -/
theorem primRoot_3 : (Function.Injective fun j : Fin 2 => (2 : ZMod 3) ^ ((j : ℕ) + 1)) ∧
    (univ.image fun j : Fin 2 => (2 : ZMod 3) ^ ((j : ℕ) + 1)) = univ.erase 0 := by
  constructor
  · decide
  · decide

theorem primRoot_5 : (Function.Injective fun j : Fin 4 => (2 : ZMod 5) ^ ((j : ℕ) + 1)) ∧
    (univ.image fun j : Fin 4 => (2 : ZMod 5) ^ ((j : ℕ) + 1)) = univ.erase 0 := by
  constructor
  · decide
  · decide

theorem eps_3 : orderOf (2 : ZMod 3) = 2 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m
  decide

theorem eps_5 : orderOf (2 : ZMod 5) = 4 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

/-! ## C₃ ≥ 2.7895 with D = 5, Heath-Brown and Puchta, page 3

C₃ is a lower bound for 2 Σ_{d ≤ D} k(d) H(d; N, K) ε(d)^{-K}. For D = 5 the d with k(d) ≠ 0
are 1, 3, 5, with k = 1, 1, 1/3 and ε = 1, 2, 4; H(1; N, K) = 1. -/

/-- The D = 5 sum, with N given by its residues mod 3 and mod 5. -/
noncomputable def C3sum5 (K : ℕ) (a : ZMod 3) (b : ZMod 5) : ℝ :=
  2 * (1 + (H 3 2 K a : ℝ) / 2 ^ K + 1 / 3 * ((H 5 4 K b : ℝ) / 4 ^ K))

theorem H3_ratio (K : ℕ) (a : ZMod 3) :
    (H 3 2 K a : ℝ) / 2 ^ K = 1 / 3 * (1 + (-1) ^ K * (if a = 0 then 2 else -1) / 2 ^ K) := by
  have h := hbp_formula 3 K primRoot_3.1 primRoot_3.2 a
  have h' : (3 : ℝ) * H 3 2 K a = 2 ^ K + (-1) ^ K * (if a = 0 then 2 else -1) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at this
    split_ifs at this ⊢ <;> norm_num at this ⊢ <;> linarith
  field_simp
  linarith

theorem H5_ratio (K : ℕ) (b : ZMod 5) :
    (H 5 4 K b : ℝ) / 4 ^ K = 1 / 5 * (1 + (-1) ^ K * (if b = 0 then 4 else -1) / 4 ^ K) := by
  have h := hbp_formula 5 K primRoot_5.1 primRoot_5.2 b
  have h' : (5 : ℝ) * H 5 4 K b = 4 ^ K + (-1) ^ K * (if b = 0 then 4 else -1) := by
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at this
    split_ifs at this ⊢ <;> norm_num at this ⊢ <;> linarith
  field_simp
  linarith

/-- Heath-Brown and Puchta's C₃ ≥ 2.7895 with D = 5 holds for every K ≥ 6 and every N;
at K = 6 and 7 the minimum is 2.78955078125. -/
theorem hbp_C3_D5 (K : ℕ) (hK : 6 ≤ K) (a : ZMod 3) (b : ZMod 5) :
    2.7895 ≤ C3sum5 K a b := by
  unfold C3sum5
  rw [H3_ratio, H5_ratio]
  have h2 : (64 : ℝ) ≤ 2 ^ K := by
    calc (64 : ℝ) = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hK
  have h4 : (4096 : ℝ) ≤ 4 ^ K := by
    calc (4096 : ℝ) = 4 ^ 6 := by norm_num
      _ ≤ 4 ^ K := pow_le_pow_right₀ (by norm_num) hK
  -- the parity of K decides the sign; split on it
  rcases Nat.even_or_odd K with he | ho
  · rw [he.neg_one_pow]
    have h3 : -1 / 64 ≤ (if a = 0 then (2 : ℝ) else -1) / 2 ^ K := by
      split_ifs
      · exact le_trans (b := 0) (by norm_num) (div_nonneg (by norm_num) (by positivity))
      · rw [le_div_iff₀ (by positivity)]; linarith
    have h5 : -1 / 4096 ≤ (if b = 0 then (4 : ℝ) else -1) / 4 ^ K := by
      split_ifs
      · exact le_trans (b := 0) (by norm_num) (div_nonneg (by norm_num) (by positivity))
      · rw [le_div_iff₀ (by positivity)]; linarith
    simp only [one_mul]
    nlinarith
  · -- odd K ≥ 7: 2^K ≥ 128, 4^K ≥ 16384
    have hK7 : 7 ≤ K := by
      rcases ho with ⟨m, rfl⟩; omega
    have h2' : (128 : ℝ) ≤ 2 ^ K := by
      calc (128 : ℝ) = 2 ^ 7 := by norm_num
        _ ≤ 2 ^ K := pow_le_pow_right₀ (by norm_num) hK7
    have h4' : (16384 : ℝ) ≤ 4 ^ K := by
      calc (16384 : ℝ) = 4 ^ 7 := by norm_num
        _ ≤ 4 ^ K := pow_le_pow_right₀ (by norm_num) hK7
    rw [ho.neg_one_pow]
    have h3 : -1 / 64 ≤ -1 * (if a = 0 then (2 : ℝ) else -1) / 2 ^ K := by
      split_ifs
      · rw [le_div_iff₀ (by positivity)]; linarith
      · exact le_trans (b := 0) (by norm_num) (div_nonneg (by norm_num) (by positivity))
    have h5 : -1 / 4096 ≤ -1 * (if b = 0 then (4 : ℝ) else -1) / 4 ^ K := by
      split_ifs
      · rw [le_div_iff₀ (by positivity)]; linarith
      · exact le_trans (b := 0) (by norm_num) (div_nonneg (by norm_num) (by positivity))
    nlinarith

/-- The bound is sharp at K = 6: N ≢ 0 mod 3 and mod 5 gives 2.78955078125. -/
theorem hbp_C3_D5_K6 : C3sum5 6 1 1 = 2.78955078125 := by
  unfold C3sum5
  rw [H3_ratio, H5_ratio]
  have h3 : (1 : ZMod 3) ≠ 0 := by decide
  have h5 : (1 : ZMod 5) ≠ 0 := by decide
  simp only [h3, h5, ite_false]
  norm_num

/-! ## The tail beyond d = 40000, page 5 -/

theorem tail_integral :
    ∫ t in Set.Ioi (40000 : ℝ), 1 / (t * (t - 2)) = Real.log (40000 / 39998) / 2 := by
  let g : ℝ → ℝ := fun t => Real.log ((t - 2) / t) / 2
  have hderiv : ∀ x ∈ Set.Ioi (40000 : ℝ), HasDerivAt g (1 / (x * (x - 2))) x := by
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hx0 : x ≠ 0 := by positivity
    have hx2 : x - 2 ≠ 0 := by linarith
    have hq : HasDerivAt (fun t => (t - 2) / t) ((1 * x - (x - 2) * 1) / x ^ 2) x :=
      ((hasDerivAt_id x).sub_const 2).div (hasDerivAt_id x) hx0
    have hpos : (x - 2) / x ≠ 0 := div_ne_zero hx2 hx0
    have := (hq.log hpos).div_const 2
    convert this using 1
    field_simp
    ring
  have hcont : ContinuousWithinAt g (Set.Ici 40000) 40000 := by
    apply ContinuousAt.continuousWithinAt
    apply ContinuousAt.div_const
    apply ContinuousAt.log
    · exact (continuousAt_id.sub continuousAt_const).div continuousAt_id (by norm_num)
    · norm_num
  have hlim : Tendsto g atTop (𝓝 0) := by
    have h1 : Tendsto (fun t : ℝ => (t - 2) / t) atTop (𝓝 1) := by
      have : (fun t : ℝ => (t - 2) / t) =ᶠ[atTop] fun t => 1 - 2 * t⁻¹ := by
        filter_upwards [eventually_gt_atTop 0] with t ht
        field_simp
      rw [tendsto_congr' this]
      simpa using (tendsto_inv_atTop_zero.const_mul 2).const_sub (1 : ℝ)
    have h2 := ((Real.continuousAt_log one_ne_zero).tendsto.comp h1).div_const 2
    simpa [g] using h2
  have hnn : ∀ x ∈ Set.Ioi (40000 : ℝ), 0 ≤ 1 / (x * (x - 2)) := by
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have : 0 < x - 2 := by linarith
    positivity
  rw [integral_Ioi_of_hasDerivAt_of_nonneg hcont hderiv hnn hlim]
  simp only [g]
  rw [show ((40000 : ℝ) - 2) / 40000 = (40000 / 39998)⁻¹ by norm_num, Real.log_inv]
  ring

/-- Page 5: 2 ∫_{40000}^∞ dt / (t (t - 2)) < 5.1 × 10⁻⁵. The value is about 5.00013e-5. -/
theorem tail_lt : 2 * ∫ t in Set.Ioi (40000 : ℝ), 1 / (t * (t - 2)) < 5.1e-5 := by
  rw [tail_integral]
  have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 40000 / 39998 by norm_num)
  norm_num at this ⊢
  linarith

/-! ## Algorithm 1 as printed, page 4

Read literally from the page image: W[i] starts at #{ν : 1 ≤ ν ≤ ε, 2(K-1) + 2^ν ≡ i};
then for k = 2..K and j = 2..ε-1, with r = 2^j - 2, Y[i + r] ← W[i] and W[i] ← W[i] + Y[i],
updating W in place; the result is min_i W[i]. -/

/-- One j step: W ← W + (W shifted by r), in place. -/
def alg1Step (d : ℕ) (W : ZMod d → ℕ) (r : ZMod d) : ZMod d → ℕ := fun i => W i + W (i - r)

/-- The vector Algorithm 1 holds at the end, read literally. -/
def alg1W (d e K : ℕ) : ZMod d → ℕ :=
  let W0 : ZMod d → ℕ := fun i =>
    ((Finset.Icc 1 e).filter fun ν => ((2 * (K - 1) + 2 ^ ν : ℕ) : ZMod d) = i).card
  let inner (W : ZMod d → ℕ) : ZMod d → ℕ :=
    ((List.range' 2 (e - 2)).foldl fun W j => alg1Step d W ((2 ^ j - 2 : ℕ) : ZMod d)) W
  (List.range (K - 1)).foldl (fun W _ => inner W) W0

/-- Algorithm 1 as printed, its returned `res`. -/
def alg1 (d e K : ℕ) [NeZero d] : ℕ := univ.inf' univ_nonempty (alg1W d e K)

/-- At d = 3, K = 2, with ε(3) = 2: the printed algorithm returns 0. -/
theorem alg1_3_2 : alg1 3 2 2 = 0 := by decide

/-- The true min over N of H(3; N, 2) is 1: N ≡ 1, 2 give 1, N ≡ 0 gives 2. -/
theorem H_3_2 : H 3 2 2 0 = 2 ∧ H 3 2 2 1 = 1 ∧ H 3 2 2 2 = 1 := by decide

theorem alg1_wrong_3_2 : alg1 3 2 2 ≠ univ.inf' univ_nonempty (H 3 2 2) := by
  rw [alg1_3_2]
  have : univ.inf' univ_nonempty (H 3 2 2) = 1 := by decide
  rw [this]
  decide

/-- At d = 11, K = 2, with ε(11) = 10: the printed algorithm returns 232, more than the
100 pairs (ν₁, ν₂) there are; the true minimum is 9. -/
theorem alg1_11_2 : alg1 11 10 2 = 232 := by decide

theorem H_11_2_min : univ.inf' univ_nonempty (H 11 10 2) = 9 := by decide

theorem eps_11 : orderOf (2 : ZMod 11) = 10 := by
  rw [orderOf_eq_iff (by norm_num)]
  refine ⟨by decide, fun m hm hm0 => ?_⟩
  interval_cases m <;> decide

end LeanLab.PlattTrudgian2014.Section2
