/-
Twin proofs of the LEAFs `leafB8_J_tendsto` and `leafB8_J_const` of
`Split1122bBoundary8.lean`.

Source: Bordignon, Johnston, Starichkova, arXiv 2207.09452, papers/P0009.pdf, page 6,
displays 8 and 13 to 18, quoting Nathanson Theorem 9.4 and the adjoint function method of
the linear sieve. P = F + f = 2 + O - E, with O, E the odd and even sums of the f_n.

* leafB8_J_tendsto: by display 18 with Lemma 8, key_l8306 with c_n = 0.9607, both O(s) and
  E(s) lie in [0, C h(s)] with h(s) = 3 e ^ -s / s → 0, so P(s) → 2 and P is bounded on
  [2, ∞). With s q(s) → 1 also q(s) → 0, hence the integral of P(t) q(t + 1) over
  [s - 1, s] tends to 0 and J(s) → 2.
* leafB8_J_const: O and E are continuous on [2, ∞) by the Weierstrass test, so the
  integrand of J extends continuously to ℝ through t ↦ max t 2. For s > 3,
  (s P(s))' = P(s - 1) from the PROVED derivative twins of displays 16 and 17, and with
  s q'(s) = - q(s + 1) the derivative of J vanishes; the mean value theorem on [3, s]
  with right continuity at 3 gives J(s) = J(3).

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122bBoundary8
import LeanLab.Cai2002.Prove1122bDerivOdd8

open Finset Real

noncomputable section

namespace LeanLab.Cai2002

/-- Display 18 with Lemma 8, uniform in x: each term of a parity sum is at most
2 · 0.9607 ^ (n - 2) in norm. -/
theorem term_bound_j8 (P : ℕ → Prop) [DecidablePred P] (x : ℝ)
    (hP : ∀ n, P n → (Odd n ∧ 1 ≤ x) ∨ (Even n ∧ 2 ≤ x)) (n : ℕ) :
    ‖(if P n then bjsF306 n x else 0)‖ ≤ 2 * (0.9607 : ℝ) ^ (n - 2) := by
  have hu : 0 ≤ 2 * (0.9607 : ℝ) ^ (n - 2) := by positivity
  split_ifs with h
  · rcases Nat.eq_zero_or_pos n with h0 | hn
    · subst h0
      rw [show bjsF306 0 x = 0 from rfl, norm_zero]
      exact hu
    · rw [Real.norm_eq_abs]
      have h1 := abs_fn_le_d8 n hn x (hP n h)
      have h2 := hSieve_le_d8 x
      have h3 : exp 2 * exp (-2) = 1 := by rw [← exp_add]; norm_num
      have h4 : 0 ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) := by positivity
      have h5 : (0.9607 : ℝ) ^ (n - 1) ≤ (0.9607 : ℝ) ^ (n - 2) :=
        pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
      calc |bjsF306 n x|
          ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * LeanLab.ChenExplicit.hSieve x := h1
        _ ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * exp (-2) := mul_le_mul_of_nonneg_left h2 h4
        _ = 2 * (0.9607 : ℝ) ^ (n - 1) * (exp 2 * exp (-2)) := by ring
        _ ≤ 2 * (0.9607 : ℝ) ^ (n - 2) := by rw [h3, mul_one]; linarith
  · simpa using hu

/-- O is continuous on [2, ∞): Weierstrass test with fn_continuous_d8. -/
theorem oSum_cont_j8 : ContinuousOn oSumB8 (Set.Ici 2) := by
  have : ContinuousOn (fun x => ∑' n : ℕ, if Odd n then bjsF306 n x else 0) (Set.Ici 2) := by
    refine continuousOn_tsum (fun n => ?_) bound_summable_d8 (fun n x hx => ?_)
    · by_cases h : Odd n
      · simp only [if_pos h]
        exact ((fn_continuous_d8 n).1 h).mono (fun x hx => by
          have : (2 : ℝ) ≤ x := hx
          show (1 : ℝ) < x
          linarith)
      · simp only [if_neg h]; exact continuousOn_const
    · have : (2 : ℝ) ≤ x := hx
      exact term_bound_j8 Odd x (fun n h => Or.inl ⟨h, by linarith⟩) n
  exact this

/-- E is continuous on [2, ∞): Weierstrass test with fn_even_contIci_o8. -/
theorem eSum_cont_j8 : ContinuousOn eSumB8 (Set.Ici 2) := by
  have : ContinuousOn (fun x => ∑' n : ℕ, if Even n then bjsF306 n x else 0) (Set.Ici 2) := by
    refine continuousOn_tsum (fun n => ?_) bound_summable_d8 (fun n x hx => ?_)
    · by_cases h : Even n
      · simp only [if_pos h]
        exact fn_even_contIci_o8 n h
      · simp only [if_neg h]; exact continuousOn_const
    · have : (2 : ℝ) ≤ x := hx
      exact term_bound_j8 Even x (fun n h => Or.inr ⟨h, this⟩) n
  exact this

/-- P = 2 + O - E is continuous on [2, ∞). -/
theorem pSum_cont_j8 : ContinuousOn pSumB8 (Set.Ici 2) := by
  exact fun x hx => (continuousWithinAt_const.add (oSum_cont_j8 x hx)).sub (eSum_cont_j8 x hx)

/-- The constant C of the summed bound 18. -/
def Cj8 : ℝ := ∑' n : ℕ, 2 * exp 2 * (0.9607 : ℝ) ^ (n - 2)

theorem Cj8_summable : Summable (fun n : ℕ => 2 * exp 2 * (0.9607 : ℝ) ^ (n - 2)) := by
  have := bound_summable_d8.mul_left (exp 2)
  exact this.congr (fun n => by ring)

theorem Cj8_nonneg : 0 ≤ Cj8 := tsum_nonneg (fun n => by positivity)

/-- Display 18 summed: 0 ≤ a parity sum ≤ C h(s). -/
theorem parity_le_j8 (P : ℕ → Prop) [DecidablePred P] (s : ℝ)
    (hP : ∀ n, P n → (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s)) (hs : 0 ≤ s) :
    0 ≤ (∑' n : ℕ, if P n then bjsF306 n s else 0) ∧
    (∑' n : ℕ, if P n then bjsF306 n s else 0) ≤ Cj8 * LeanLab.ChenExplicit.hSieve s := by
  have hh := hSieve_nonneg306 s hs
  have hsum := parity_summableB8 P s hP hs
  refine ⟨tsum_nonneg (fun n => ?_), ?_⟩
  · split_ifs with h
    · exact leaf306_fn_nonneg n s (hP n h)
    · exact le_rfl
  · unfold Cj8
    rw [← tsum_mul_right]
    refine hsum.tsum_le_tsum (fun n => ?_) (Cj8_summable.mul_right _)
    split_ifs with h
    · rcases Nat.eq_zero_or_pos n with h0 | hn
      · subst h0
        rw [show bjsF306 0 s = 0 from rfl]
        exact mul_nonneg (by positivity) hh
      · have h1 := key_l8306 n hn s (hP n h)
        have h5 : (0.9607 : ℝ) ^ (n - 1) ≤ (0.9607 : ℝ) ^ (n - 2) :=
          pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)
        have h6 : 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * LeanLab.ChenExplicit.hSieve s ≤
            2 * exp 2 * (0.9607 : ℝ) ^ (n - 2) * LeanLab.ChenExplicit.hSieve s :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h5 (by positivity)) hh
        linarith
    · exact mul_nonneg (by positivity) hh

theorem oSum_le_j8 (t : ℝ) (ht : 2 ≤ t) :
    0 ≤ oSumB8 t ∧ oSumB8 t ≤ Cj8 * LeanLab.ChenExplicit.hSieve t :=
  parity_le_j8 Odd t (fun _ h => Or.inl ⟨h, by linarith⟩) (by linarith)

theorem eSum_le_j8 (t : ℝ) (ht : 2 ≤ t) :
    0 ≤ eSumB8 t ∧ eSumB8 t ≤ Cj8 * LeanLab.ChenExplicit.hSieve t :=
  parity_le_j8 Even t (fun _ h => Or.inr ⟨h, ht⟩) (by linarith)

/-- h(s) → 0 at infinity, h of display 18. -/
theorem hSieve_tendsto_j8 :
    Filter.Tendsto LeanLab.ChenExplicit.hSieve Filter.atTop (nhds 0) := by
  refine squeeze_zero' (Filter.eventually_atTop.2 ⟨0, fun s hs => hSieve_nonneg306 s hs⟩)
    (Filter.eventually_atTop.2 ⟨4, fun s hs => ?_⟩) Real.tendsto_exp_neg_atTop_nhds_zero
  unfold LeanLab.ChenExplicit.hSieve
  rw [if_neg (by linarith), if_neg (by linarith)]
  have h3 : 3 * s⁻¹ ≤ 1 := by
    rw [← div_eq_mul_inv, div_le_one (by linarith)]; linarith
  have := exp_pos (-s)
  nlinarith

theorem oSum_tendsto_j8 : Filter.Tendsto oSumB8 Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto (fun s => Cj8 * LeanLab.ChenExplicit.hSieve s) Filter.atTop
      (nhds 0) := by simpa using hSieve_tendsto_j8.const_mul Cj8
  exact squeeze_zero' (Filter.eventually_atTop.2 ⟨2, fun s hs => (oSum_le_j8 s hs).1⟩)
    (Filter.eventually_atTop.2 ⟨2, fun s hs => (oSum_le_j8 s hs).2⟩) hg

theorem eSum_tendsto_j8 : Filter.Tendsto eSumB8 Filter.atTop (nhds 0) := by
  have hg : Filter.Tendsto (fun s => Cj8 * LeanLab.ChenExplicit.hSieve s) Filter.atTop
      (nhds 0) := by simpa using hSieve_tendsto_j8.const_mul Cj8
  exact squeeze_zero' (Filter.eventually_atTop.2 ⟨2, fun s hs => (eSum_le_j8 s hs).1⟩)
    (Filter.eventually_atTop.2 ⟨2, fun s hs => (eSum_le_j8 s hs).2⟩) hg

theorem pSum_tendsto_j8 : Filter.Tendsto pSumB8 Filter.atTop (nhds 2) := by
  have := ((tendsto_const_nhds (x := (2 : ℝ))).add oSum_tendsto_j8).sub eSum_tendsto_j8
  rw [show (2 : ℝ) + 0 - 0 = 2 by norm_num] at this
  exact this

/-- |P(t)| ≤ 2 + C on [2, ∞). -/
theorem pSum_bound_j8 : ∃ M : ℝ, 0 < M ∧ ∀ t : ℝ, 2 ≤ t → |pSumB8 t| ≤ M := by
  have hC := Cj8_nonneg
  refine ⟨2 + Cj8, by linarith, fun t ht => ?_⟩
  obtain ⟨o0, o1⟩ := oSum_le_j8 t ht
  obtain ⟨e0, e1⟩ := eSum_le_j8 t ht
  have h1 := hSieve_le_d8 t
  have h2 : exp (-2 : ℝ) ≤ 1 := Real.exp_le_one_iff.2 (by norm_num)
  have h3 : Cj8 * LeanLab.ChenExplicit.hSieve t ≤ Cj8 := by
    have := mul_le_mul_of_nonneg_left (h1.trans h2) hC
    rwa [mul_one] at this
  unfold pSumB8
  rw [abs_le]
  constructor <;> linarith

/-- q(s) → 0 from s q(s) → 1. -/
theorem q_tendsto_j8 (q : ℝ → ℝ) (hq : IsAdjB8 q) :
    Filter.Tendsto q Filter.atTop (nhds 0) := by
  have h := hq.2.mul (tendsto_inv_atTop_zero (𝕜 := ℝ))
  rw [one_mul] at h
  refine h.congr' (Filter.eventually_atTop.2 ⟨1, fun s hs => ?_⟩)
  have : s ≠ 0 := by linarith
  field_simp

/-- The integral of P(t) q(t + 1) over [s - 1, s] tends to 0. -/
theorem integral_tendsto_j8 (q : ℝ → ℝ) (hq0 : Filter.Tendsto q Filter.atTop (nhds 0)) :
    Filter.Tendsto (fun s => ∫ t in (s - 1)..s, pSumB8 t * q (t + 1)) Filter.atTop
      (nhds 0) := by
  obtain ⟨M, hM0, hM⟩ := pSum_bound_j8
  rw [Metric.tendsto_atTop] at hq0 ⊢
  intro ε hε
  obtain ⟨U, hU⟩ := hq0 (ε / (2 * M)) (by positivity)
  refine ⟨max U 3, fun s hs => ?_⟩
  have hs3 : 3 ≤ s := le_trans (le_max_right _ _) hs
  have hsU : U ≤ s := le_trans (le_max_left _ _) hs
  rw [Real.dist_eq, sub_zero]
  have hb : ∀ t ∈ Set.uIoc (s - 1) s, ‖pSumB8 t * q (t + 1)‖ ≤ M * (ε / (2 * M)) := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    obtain ⟨ht1, ht2⟩ := ht
    have hqt := hU (t + 1) (by linarith)
    rw [Real.dist_eq, sub_zero] at hqt
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hM t (by linarith)) hqt.le (abs_nonneg _) hM0.le
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs, show |s - (s - 1)| = 1 by norm_num] at h1
  have h2 : M * (ε / (2 * M)) = ε / 2 := by field_simp
  linarith

/-- Twin of the LEAF `leafB8_J_tendsto` of `Split1122bBoundary8.lean`, statement copied
verbatim. -/
theorem leafB8_J_tendsto_twin (q : ℝ → ℝ) (hq : IsAdjB8 q) :
    Filter.Tendsto (jInvB8 q) Filter.atTop (nhds 2) := by
  have h1 : Filter.Tendsto (fun s => s * q s * pSumB8 s) Filter.atTop (nhds (1 * 2)) :=
    hq.2.mul pSum_tendsto_j8
  have h2 := integral_tendsto_j8 q (q_tendsto_j8 q hq)
  have h3 := h1.add h2
  rw [show (1 : ℝ) * 2 + 0 = 2 by norm_num] at h3
  exact h3

/-- The continuous extension of the integrand of J through t ↦ max t 2. -/
def gExtJ8 (q : ℝ → ℝ) (t : ℝ) : ℝ := pSumB8 (max t 2) * q (max t 2 + 1)

/-- Its primitive from 2. -/
def GExtJ8 (q : ℝ → ℝ) (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, gExtJ8 q t

/-- J rewritten with the extension, equal to J on [3, ∞). -/
def KJ8 (q : ℝ → ℝ) (s : ℝ) : ℝ :=
  s * q s * pSumB8 (max s 2) + GExtJ8 q s - GExtJ8 q (s - 1)

/-- Twin of the LEAF `leafB8_J_const` of `Split1122bBoundary8.lean`, statement copied
verbatim. -/
theorem leafB8_J_const_twin (q : ℝ → ℝ) (hq : IsAdjB8 q) (s : ℝ) (hs : 3 ≤ s) :
    jInvB8 q s = jInvB8 q 3 := by
  have hqc : ContinuousOn q (Set.Ioi 0) := fun x hx =>
    (hq.1 x hx).continuousAt.continuousWithinAt
  have hpc : Continuous (fun t : ℝ => pSumB8 (max t 2)) :=
    pSum_cont_j8.comp_continuous (continuous_id.max continuous_const)
      (fun t => le_max_right t 2)
  have hgc : Continuous (gExtJ8 q) := by
    have hq1 : Continuous (fun t : ℝ => q (max t 2 + 1)) :=
      hqc.comp_continuous ((continuous_id.max continuous_const).add continuous_const)
        (fun t => by
          show (0 : ℝ) < max t 2 + 1
          linarith [le_max_right t 2])
    exact hpc.mul hq1
  have hG : ∀ x, HasDerivAt (GExtJ8 q) (gExtJ8 q x) x := fun x =>
    (hgc.integral_hasStrictDerivAt 2 x).hasDerivAt
  have hGc : Continuous (GExtJ8 q) :=
    continuous_iff_continuousAt.2 fun x => (hG x).continuousAt
  have hint_eq : ∀ s : ℝ, 3 ≤ s →
      ∫ t in (s - 1)..s, pSumB8 t * q (t + 1) = GExtJ8 q s - GExtJ8 q (s - 1) := by
    intro s hs
    unfold GExtJ8
    rw [intervalIntegral.integral_interval_sub_left (hgc.intervalIntegrable _ _)
      (hgc.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by linarith)] at ht
    have : max t 2 = t := max_eq_left (by linarith [ht.1])
    simp only [gExtJ8, this]
  have hJK : ∀ s : ℝ, 3 ≤ s → jInvB8 q s = KJ8 q s := by
    intro s hs
    unfold jInvB8 KJ8
    rw [hint_eq s hs, max_eq_left (by linarith : (2 : ℝ) ≤ s)]
    ring
  have hKc : ContinuousOn (KJ8 q) (Set.Ioi 0) := by
    have h1 : ContinuousOn (fun s : ℝ => s * q s * pSumB8 (max s 2)) (Set.Ioi 0) :=
      (continuousOn_id.mul hqc).mul hpc.continuousOn
    have h2 : Continuous (fun s : ℝ => GExtJ8 q (s - 1)) :=
      hGc.comp (continuous_id.sub continuous_const)
    exact (h1.add hGc.continuousOn).sub h2.continuousOn
  have hKd : ∀ x : ℝ, 3 < x → HasDerivAt (KJ8 q) 0 x := by
    intro x hx
    have hx0 : (0 : ℝ) < x := by linarith
    have hO : HasDerivAt (fun t => t * oSumB8 t) (-eSumB8 (x - 1)) x :=
      leaf8_deriv_odd_twin.1 x hx
    have hE : HasDerivAt (fun t => t * eSumB8 t) (-oSumB8 (x - 1)) x :=
      leaf8_deriv_even_twin x (by linarith)
    have hP : HasDerivAt (fun t => t * pSumB8 t) (pSumB8 (x - 1)) x := by
      have h := (((hasDerivAt_id x).const_mul 2).add hO).sub hE
      convert h using 1
      · funext t; simp only [pSumB8, id, Pi.add_apply, Pi.sub_apply]; ring
      · simp only [pSumB8]; ring
    have hG1 : HasDerivAt (fun y => GExtJ8 q (y - 1)) (gExtJ8 q (x - 1)) x := by
      have := (hG (x - 1)).comp x ((hasDerivAt_id' x).sub_const 1)
      rw [mul_one] at this
      exact this
    have hd := ((hq.1 x hx0).mul hP).add (hG x) |>.sub hG1
    have hval : -q (x + 1) / x * (x * pSumB8 x) + q x * pSumB8 (x - 1) + gExtJ8 q x -
        gExtJ8 q (x - 1) = 0 := by
      have e1 : max x 2 = x := max_eq_left (by linarith)
      have e2 : max (x - 1) 2 = x - 1 := max_eq_left (by linarith)
      simp only [gExtJ8, e1, e2, show x - 1 + 1 = x by ring]
      field_simp
      ring
    rw [hval] at hd
    refine hd.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds (show (2 : ℝ) < x by linarith)] with y hy
    have hy' : (2 : ℝ) < y := hy
    simp only [KJ8, max_eq_left hy'.le, Pi.add_apply, Pi.sub_apply, Pi.mul_apply]
    ring
  rcases eq_or_lt_of_le hs with h | h
  · rw [h]
  · obtain ⟨c, hc, hcd⟩ := exists_hasDerivAt_eq_slope (KJ8 q) (fun _ => (0 : ℝ)) h
      (hKc.mono (fun y hy => by
        show (0 : ℝ) < y
        linarith [hy.1]))
      (fun y hy => hKd y hy.1)
    have hne : s - 3 ≠ 0 := by linarith
    have hK : KJ8 q s = KJ8 q 3 := by
      have := hcd.symm
      rw [div_eq_zero_iff] at this
      rcases this with h1 | h1
      · linarith
      · exact absurd h1 hne
    rw [hJK s hs, hJK 3 le_rfl, hK]

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leafB8_J_tendsto_twin
#print axioms LeanLab.Cai2002.leafB8_J_const_twin
