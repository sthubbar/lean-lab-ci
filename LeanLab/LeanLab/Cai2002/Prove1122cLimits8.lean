/-
Proofs of the LEAFs leafB8_IQ_tendsto and leafB8_J_tendsto of Split1122bBoundary8.lean,
Nathanson Theorem 9.4 as quoted by Bordignon, Johnston and Starichkova, arXiv 2207.09452v6,
papers/P0009.pdf, page 6: the invariants I and J of the adjoint method tend to 0 and 2.
Both use only the PROVED bound 18 with Lemma 8, key_l8306, with c_n = 0.9607, summed as a
geometric series; Table 2 and Lemma 7 are not used.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122bBoundary8
open Finset Real
noncomputable section
namespace LeanLab.Cai2002
theorem parity_bound_s77 (P : ℕ → Prop) [DecidablePred P] (s : ℝ) (hs : 2 ≤ s) :
    0 ≤ (∑' n : ℕ, if P n then bjsF306 n s else 0) ∧
    (∑' n : ℕ, if P n then bjsF306 n s else 0) ≤
      2 * exp 2 * LeanLab.ChenExplicit.hSieve s * (1 - 0.9607)⁻¹ := by
  have hP : ∀ n, P n → (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s) := by
    intro n _
    rcases Nat.even_or_odd n with h | h
    · exact Or.inr ⟨h, hs⟩
    · exact Or.inl ⟨h, by linarith⟩
  have hsum := parity_summableB8 P s hP (by linarith)
  have hh := hSieve_nonneg306 s (by linarith)
  have hnn : ∀ n, 0 ≤ (if P n then bjsF306 n s else 0) := by
    intro n; split_ifs with h
    · exact leaf306_fn_nonneg _ s (hP _ h)
    · exact le_rfl
  refine ⟨tsum_nonneg hnn, ?_⟩
  rw [hsum.tsum_eq_zero_add]
  have h0 : (if P 0 then bjsF306 0 s else 0) = 0 := by
    split_ifs <;> simp [bjsF306]
  rw [h0, zero_add]
  set C := 2 * exp 2 * LeanLab.ChenExplicit.hSieve s with hC
  have hg : Summable (fun k : ℕ => C * (0.9607 : ℝ) ^ k) :=
    (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 0.9607) (by norm_num)).mul_left C
  have hle : ∀ k : ℕ, (if P (k + 1) then bjsF306 (k + 1) s else 0) ≤ C * (0.9607 : ℝ) ^ k := by
    intro k
    split_ifs with h
    · have := key_l8306 (k + 1) (by omega) s (hP _ h)
      rw [show k + 1 - 1 = k by omega] at this
      rw [hC]; linarith
    · positivity
  calc (∑' k : ℕ, if P (k + 1) then bjsF306 (k + 1) s else 0)
      ≤ ∑' k : ℕ, C * (0.9607 : ℝ) ^ k :=
        Summable.tsum_le_tsum hle ((summable_nat_add_iff 1).2 hsum) hg
    _ = C * (1 - 0.9607)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]

theorem q_bound_s77 (t : ℝ) (ht : 3 ≤ t) :
    0 ≤ oSumB8 t + eSumB8 t ∧
      oSumB8 t + eSumB8 t ≤ 2 * (2 * exp 2 * (1 - 0.9607)⁻¹) * exp (-t) := by
  obtain ⟨o1, o2⟩ := parity_bound_s77 Odd t (by linarith)
  obtain ⟨e1, e2⟩ := parity_bound_s77 Even t (by linarith)
  have hhle : LeanLab.ChenExplicit.hSieve t ≤ exp (-t) := by
    unfold LeanLab.ChenExplicit.hSieve
    split_ifs with h1 h2
    · linarith
    · have : t = 3 := by linarith
      subst this; exact le_rfl
    · have hpos : 0 < t := by linarith
      have : 3 * t⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one hpos]; linarith
      have := exp_pos (-t)
      nlinarith
  have hK : 0 ≤ 2 * exp 2 * (1 - (0.9607:ℝ))⁻¹ := by
    have : (0:ℝ) ≤ (1 - 0.9607)⁻¹ := by norm_num
    positivity
  unfold oSumB8 eSumB8
  refine ⟨by linarith, ?_⟩
  have h1 : 2 * exp 2 * LeanLab.ChenExplicit.hSieve t * (1 - 0.9607)⁻¹ ≤
      2 * exp 2 * (1 - 0.9607)⁻¹ * exp (-t) := by
    rw [mul_right_comm]; exact mul_le_mul_of_nonneg_left hhle hK
  linarith

/-- Proof of the LEAF leafB8_IQ_tendsto of Split1122bBoundary8.lean, statement verbatim:
Nathanson Theorem 9.4, I(s) → 0, since O + E ≤ C e ^ -s for s ≥ 3 by display 18 with
Lemma 8, key_l8306 summed geometrically. -/
theorem leafB8_IQ_tendsto_s77 : Filter.Tendsto qInvB8 Filter.atTop (nhds 0) := by
  set M := 2 * (2 * exp 2 * (1 - (0.9607:ℝ))⁻¹) with hM
  have hM0 : 0 ≤ M := by
    have : (0:ℝ) ≤ (1 - 0.9607)⁻¹ := by norm_num
    rw [hM]; positivity
  have hlim : Filter.Tendsto (fun s : ℝ => M * (s ^ 2 * exp (-s)) + M * exp 1 * (s ^ 1 * exp (-s)))
      Filter.atTop (nhds 0) := by
    have := ((tendsto_pow_mul_exp_neg_atTop_nhds_zero 2).const_mul M).add
      ((tendsto_pow_mul_exp_neg_atTop_nhds_zero 1).const_mul (M * exp 1))
    simpa using this
  refine squeeze_zero_norm' ?_ hlim
  filter_upwards [Filter.eventually_ge_atTop (4:ℝ)] with s hs
  obtain ⟨q1, q2⟩ := q_bound_s77 s (by linarith)
  have hint : ‖∫ t in (s - 1)..s, t * (oSumB8 t + eSumB8 t)‖ ≤ (s * M * exp (-(s-1))) * |s - (s - 1)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    obtain ⟨ht1, ht2⟩ := ht
    obtain ⟨r1, r2⟩ := q_bound_s77 t (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by linarith) r1)]
    have he : exp (-t) ≤ exp (-(s-1)) := exp_le_exp.2 (by linarith)
    calc t * (oSumB8 t + eSumB8 t) ≤ s * (M * exp (-t)) :=
          mul_le_mul ht2 r2 r1 (by linarith)
      _ ≤ s * M * exp (-(s - 1)) := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left he (by positivity)
  have habs : |s - (s - 1)| = 1 := by norm_num
  rw [habs, mul_one] at hint
  have hes : exp (-(s - 1)) = exp 1 * exp (-s) := by rw [← exp_add]; ring_nf
  rw [hes] at hint
  unfold qInvB8
  have hA : ‖s * (s - 1) * (oSumB8 s + eSumB8 s)‖ ≤ M * (s ^ 2 * exp (-s)) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (mul_nonneg (by linarith) (by linarith)) q1)]
    have : s * (s - 1) ≤ s ^ 2 := by nlinarith
    calc s * (s - 1) * (oSumB8 s + eSumB8 s) ≤ s ^ 2 * (M * exp (-s)) :=
          mul_le_mul this q2 q1 (by positivity)
      _ = M * (s ^ 2 * exp (-s)) := by ring
  refine (norm_sub_le _ _).trans ?_
  have : s * M * (exp 1 * exp (-s)) = M * exp 1 * (s ^ 1 * exp (-s)) := by ring
  linarith

theorem hSieve_le_exp_s77 (s : ℝ) (hs : 3 ≤ s) :
    LeanLab.ChenExplicit.hSieve s ≤ exp (-s) := by
  unfold LeanLab.ChenExplicit.hSieve
  by_cases h3 : s ≤ 3
  · have : s = 3 := le_antisymm h3 hs
    subst this; norm_num
  · have h2 : ¬ s ≤ 2 := by linarith
    simp only [h2, h3, ite_false]
    have hspos : 0 < s := by linarith
    have : 3 * s⁻¹ ≤ 1 := by rw [← div_eq_mul_inv, div_le_one hspos]; exact hs
    have he := (exp_pos (-s)).le
    nlinarith

theorem paritySum_bound_s77 (P : ℕ → Prop) [DecidablePred P] (s : ℝ) (hs : 3 ≤ s) :
    0 ≤ (∑' n : ℕ, if P n then bjsF306 n s else 0) ∧
    (∑' n : ℕ, if P n then bjsF306 n s else 0) ≤
      2 * exp 2 * LeanLab.ChenExplicit.hSieve s * (1 - 0.9607)⁻¹ := by
  have hP : ∀ n, P n → (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s) := by
    intro n _
    rcases Nat.even_or_odd n with h | h
    · exact Or.inr ⟨h, by linarith⟩
    · exact Or.inl ⟨h, by linarith⟩
  have hsum := parity_summableB8 P s hP (by linarith)
  have hnn : ∀ n, 0 ≤ (if P n then bjsF306 n s else 0) := by
    intro n; split_ifs with h
    · exact leaf306_fn_nonneg _ s (hP _ h)
    · exact le_rfl
  refine ⟨tsum_nonneg hnn, ?_⟩
  rw [hsum.tsum_eq_zero_add]
  have h0 : (if P 0 then bjsF306 0 s else 0) = 0 := by split_ifs <;> simp [bjsF306]
  rw [h0, zero_add]
  have hh := hSieve_nonneg306 s (by linarith)
  have hg := (summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 0.9607) (by norm_num)).mul_left
    (2 * exp 2 * LeanLab.ChenExplicit.hSieve s)
  calc (∑' k : ℕ, if P (k + 1) then bjsF306 (k + 1) s else 0)
      ≤ ∑' k : ℕ, 2 * exp 2 * LeanLab.ChenExplicit.hSieve s * (0.9607 : ℝ) ^ k := by
        refine Summable.tsum_le_tsum (fun k => ?_) ((summable_nat_add_iff 1).2 hsum) hg
        split_ifs with h
        · have := key_l8306 (k + 1) (by omega) s (hP _ h)
          rw [show k + 1 - 1 = k by omega] at this
          linarith
        · positivity
    _ = 2 * exp 2 * LeanLab.ChenExplicit.hSieve s * (1 - 0.9607)⁻¹ := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one (by norm_num) (by norm_num)]

theorem pSumB8_bound_s77 (s : ℝ) (hs : 3 ≤ s) :
    |pSumB8 s - 2| ≤ 2 * exp 2 * exp (-s) * (1 - 0.9607)⁻¹ := by
  obtain ⟨o1, o2⟩ := paritySum_bound_s77 Odd s hs
  obtain ⟨e1, e2⟩ := paritySum_bound_s77 Even s hs
  have hb : 2 * exp 2 * LeanLab.ChenExplicit.hSieve s * (1 - 0.9607 : ℝ)⁻¹ ≤
      2 * exp 2 * exp (-s) * (1 - 0.9607)⁻¹ := by
    have := hSieve_le_exp_s77 s hs
    have : (0 : ℝ) ≤ (1 - 0.9607 : ℝ)⁻¹ := by norm_num
    gcongr
  unfold pSumB8 oSumB8 eSumB8
  rw [abs_le]; constructor <;> linarith

theorem pSumB8_tendsto_s77 : Filter.Tendsto pSumB8 Filter.atTop (nhds 2) := by
  have hlim : Filter.Tendsto (fun s : ℝ => 2 * exp 2 * exp (-s) * (1 - 0.9607 : ℝ)⁻¹)
      Filter.atTop (nhds 0) := by
    have := (Real.tendsto_exp_neg_atTop_nhds_zero.const_mul (2 * exp 2)).mul_const
      ((1 - 0.9607 : ℝ)⁻¹)
    simpa using this
  have h1 : Filter.Tendsto (fun s => pSumB8 s - 2) Filter.atTop (nhds 0) := by
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [Filter.eventually_ge_atTop (3 : ℝ)] with s hs
    rw [Real.norm_eq_abs]; exact pSumB8_bound_s77 s hs
  have := h1.add_const 2
  simpa using this

/-- Proof of the LEAF leafB8_J_tendsto of Split1122bBoundary8.lean, statement verbatim:
Nathanson Theorem 9.4, J(s) → 2, since P(s) → 2 by display 18 with Lemma 8, s q(s) → 1, and
the integral term is at most 6 / s. -/
theorem leafB8_J_tendsto_s77 (q : ℝ → ℝ) (hq : IsAdjB8 q) :
    Filter.Tendsto (jInvB8 q) Filter.atTop (nhds 2) := by
  have hP := pSumB8_tendsto_s77
  have hA : Filter.Tendsto (fun s => s * q s * pSumB8 s) Filter.atTop (nhds 2) := by
    have := hq.2.mul hP; simpa using this
  -- eventual bounds
  have hP3 : ∀ᶠ s in Filter.atTop, |pSumB8 s| ≤ 3 := by
    have := hP.eventually (Metric.ball_mem_nhds (2 : ℝ) (by norm_num : (0:ℝ) < 1))
    filter_upwards [this] with s hs
    rw [Real.dist_eq, abs_lt] at hs
    rw [abs_le]; constructor <;> linarith
  have hQ : ∀ᶠ u in Filter.atTop, u * q u ∈ Set.Ioo (0 : ℝ) 2 :=
    hq.2.eventually (Ioo_mem_nhds (by norm_num) (by norm_num))
  obtain ⟨S1, hS1⟩ := Filter.eventually_atTop.1 hP3
  obtain ⟨S2, hS2⟩ := Filter.eventually_atTop.1 hQ
  have hB : Filter.Tendsto (fun s => ∫ t in (s - 1)..s, pSumB8 t * q (t + 1))
      Filter.atTop (nhds 0) := by
    have hlim : Filter.Tendsto (fun s : ℝ => 6 * s⁻¹) Filter.atTop (nhds 0) := by
      simpa using tendsto_inv_atTop_zero.const_mul (6 : ℝ)
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [Filter.eventually_ge_atTop (max (S1 + 1) (max S2 1))] with s hs
    have hs1 : S1 + 1 ≤ s := le_trans (le_max_left _ _) hs
    have hs2 : S2 ≤ s := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hs
    have hs3 : 1 ≤ s := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hs
    have hspos : 0 < s := by linarith
    have key := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := s - 1) (b := s) (C := 6 * s⁻¹) (f := fun t => pSumB8 t * q (t + 1)) ?_
    · rw [show |s - (s - 1)| = 1 by norm_num, mul_one] at key
      exact key
    · intro t ht
      rw [Set.uIoc_of_le (by linarith)] at ht
      obtain ⟨ht1, ht2⟩ := ht
      have hp := hS1 t (by linarith)
      have hu := hS2 (t + 1) (by linarith)
      obtain ⟨hu1, hu2⟩ := hu
      have htp : 0 < t + 1 := by linarith
      have hqabs : |q (t + 1)| ≤ 2 * s⁻¹ := by
        have hqpos : 0 < q (t + 1) := by
          by_contra hc; rw [not_lt] at hc; nlinarith
        rw [abs_of_pos hqpos]
        have : q (t + 1) * (t + 1) < 2 := by linarith
        have h2 : q (t + 1) * s ≤ q (t + 1) * (t + 1) := by
          apply mul_le_mul_of_nonneg_left (by linarith) hqpos.le
        rw [← div_eq_mul_inv, le_div_iff₀ hspos]; linarith
      rw [Real.norm_eq_abs, abs_mul]
      have := abs_nonneg (pSumB8 t)
      have := abs_nonneg (q (t + 1))
      calc |pSumB8 t| * |q (t + 1)| ≤ 3 * (2 * s⁻¹) := by gcongr
        _ = 6 * s⁻¹ := by ring
  have := hA.add hB
  rw [add_zero] at this
  exact this.congr (fun s => rfl)

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leafB8_IQ_tendsto_s77
#print axioms LeanLab.Cai2002.leafB8_J_tendsto_s77
