/-
Proofs of five LEAFs of the Nathanson Theorem 9.4 track, as quoted by Bordignon, Johnston and
Starichkova, arXiv 2207.09452v6, papers/P0009.pdf, page 6, displays 8 and 13 to 18:
* leaf8_continuous of Split1122bSeries8.lean, as leaf8_continuous_s77;
* leafB8_IQ_const and leafB8_J_const of Split1122bBoundary8.lean, as leafB8_IQ_const_s77 and
  leafB8_J_const_s77, each taking that continuity as a hypothesis hc;
* leafB8_IQ3 and leafB8_J3 of Split1122bBoundary8.lean, as leafB8_IQ3_s77 and leafB8_J3_s77.
Only the PROVED bound 18 with Lemma 8, c_n = 0.9607, is used, not Table 2.
Helpers with suffix _s77M repeat some helpers with suffix _s77; they were written by separate
workflow subagents and are kept apart to avoid any renaming risk.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split1122bBoundary8
import LeanLab.Cai2002.Prove1122bDerivOdd8
open Finset Real
noncomputable section
namespace LeanLab.Cai2002

/-- Display 15 on [1, ∞): f_1(s) = max (3 - s) 0 / s. -/
theorem f1_eq_s77 (s : ℝ) (hs : 1 ≤ s) : bjsF306 1 s = max (3 - s) 0 / s := by
  simp only [bjsF306]
  split_ifs with h
  · rw [max_eq_left (by linarith)]
  · rw [max_eq_right (by linarith), zero_div]

/-- Odd f_k is continuous on [1, ∞), including s = 1. -/
theorem fn_odd_contIci_s77 (k : ℕ) (ho : Odd k) : ContinuousOn (bjsF306 k) (Set.Ici 1) := by
  match k, ho with
  | 0, ho => exact absurd ho (by decide)
  | 1, _ =>
    have hc : ContinuousOn (fun s : ℝ => max (3 - s) 0 / s) (Set.Ici 1) := by
      refine ContinuousOn.div (by fun_prop) continuousOn_id ?_
      intro x hx; have : (1 : ℝ) ≤ x := hx; exact ne_of_gt (by linarith)
    exact hc.congr (fun s hs => f1_eq_s77 s hs)
  | m + 2, ho =>
    have hev : Even (m + 1) := even_of_odd_o8 m ho
    have hc1 := (fn_continuous_d8 (m + 1)).2 hev
    have hi := phi_integrable_d8 (m + 1) 3 (by norm_num)
      (fun x hx => Or.inr ⟨hev, by linarith⟩) (by norm_num; exact hc1)
    have hG := contG_d8 (fun u => bjsF306 (m + 1) (u - 1)) 3 hi
    have hcomp : ContinuousOn
        (fun s : ℝ => (∫ u in Set.Ioi (max s 3), bjsF306 (m + 1) (u - 1)) / s)
        (Set.Ici 1) := by
      refine ContinuousOn.div ?_ continuousOn_id ?_
      · refine hG.comp (continuous_id.max continuous_const).continuousOn ?_
        intro x _; exact le_max_right x 3
      · intro x hx; have : (1 : ℝ) ≤ x := hx; exact ne_of_gt (by linarith)
    refine hcomp.congr (fun s hs => ?_)
    simp only [bjsF306]
    split_ifs with h
    · rw [max_eq_right h.2]
    · have : 3 < s := by
        by_contra hc; exact h ⟨ho, by linarith⟩
      rw [max_eq_left this.le]

/-- Uniform bound from display 18 with Lemma 8: |f_n(x)| ≤ 2 · 0.9607 ^ (n - 1). -/
theorem fn_unif_bound_s77 (n : ℕ) (x : ℝ) (hx : (Odd n ∧ 1 ≤ x) ∨ (Even n ∧ 2 ≤ x)) :
    |bjsF306 n x| ≤ 2 * (0.9607 : ℝ) ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; simp [bjsF306]
  have h1 := abs_fn_le_d8 n hn x hx
  have h2 := hSieve_le_d8 x
  have h3 : exp 2 * exp (-2) = 1 := by rw [← exp_add]; norm_num
  have h4 : 0 ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) := by positivity
  calc |bjsF306 n x|
      ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * LeanLab.ChenExplicit.hSieve x := h1
    _ ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * exp (-2) := mul_le_mul_of_nonneg_left h2 h4
    _ = 2 * (0.9607 : ℝ) ^ (n - 1) * (exp 2 * exp (-2)) := by ring
    _ = 2 * (0.9607 : ℝ) ^ (n - 1) := by rw [h3, mul_one]

theorem bound_summable_s77 : Summable (fun n : ℕ => 2 * (0.9607 : ℝ) ^ (n - 1)) := by
  rw [← summable_nat_add_iff 1]
  have : (fun m : ℕ => 2 * (0.9607 : ℝ) ^ (m + 1 - 1)) = fun m => 2 * (0.9607 : ℝ) ^ m := by
    funext m; rw [show m + 1 - 1 = m by omega]
  rw [this]
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

/-- Proof of the LEAF leaf8_continuous of Split1122bSeries8.lean, statement verbatim: the
sums of the series 13 and 14 are continuous, by the Weierstrass test with the bound
2 * 0.9607 ^ (n - 1) from display 18 with Lemma 8. -/
theorem leaf8_continuous_s77 :
    ContinuousOn (fun s : ℝ => ∑' n : ℕ, if Odd n then bjsF306 n s else 0) (Set.Ici 1) ∧
    ContinuousOn (fun s : ℝ => ∑' n : ℕ, if Even n then bjsF306 n s else 0) (Set.Ici 2) := by
  have hu0 : ∀ n : ℕ, 0 ≤ 2 * (0.9607 : ℝ) ^ (n - 1) := fun n => by positivity
  constructor
  · refine continuousOn_tsum (fun n => ?_) bound_summable_s77 (fun n x hx => ?_)
    · by_cases ho : Odd n
      · simp only [if_pos ho]; exact fn_odd_contIci_s77 n ho
      · simp only [if_neg ho]; exact continuousOn_const
    · by_cases ho : Odd n
      · rw [if_pos ho, Real.norm_eq_abs]
        exact fn_unif_bound_s77 n x (Or.inl ⟨ho, hx⟩)
      · rw [if_neg ho, norm_zero]; exact hu0 n
  · refine continuousOn_tsum (fun n => ?_) bound_summable_s77 (fun n x hx => ?_)
    · by_cases he : Even n
      · simp only [if_pos he]; exact fn_even_contIci_o8 n he
      · simp only [if_neg he]; exact continuousOn_const
    · by_cases he : Even n
      · rw [if_pos he, Real.norm_eq_abs]
        exact fn_unif_bound_s77 n x (Or.inr ⟨he, hx⟩)
      · rw [if_neg he, norm_zero]; exact hu0 n


/-- Window lemma: if A' = -(G x - G (x - 1)) on (3, ∞), A continuous on [3, ∞) and G
continuous on [2, ∞), then A s + the integral of G over [s - 1, s] is constant on [3, ∞). -/
theorem window_const_s77 (A G : ℝ → ℝ) (hG : ContinuousOn G (Set.Ici 2))
    (hA : ContinuousOn A (Set.Ici 3))
    (hAd : ∀ x : ℝ, 3 < x → HasDerivAt A (-(G x - G (x - 1))) x) (s : ℝ) (hs : 3 ≤ s) :
    A s + ∫ t in (s - 1)..s, G t = A 3 + ∫ t in (3 - 1)..3, G t := by
  set Gt : ℝ → ℝ := fun t => G (max t 2) with hGt
  have hGtc : Continuous Gt :=
    hG.comp_continuous (continuous_id.max continuous_const) (fun t => le_max_right t 2)
  set Ψ : ℝ → ℝ := fun u => ∫ t in (0 : ℝ)..u, Gt t with hΨ
  have hwin : ∀ x : ℝ, 3 ≤ x → ∫ t in (x - 1)..x, G t = Ψ x - Ψ (x - 1) := by
    intro x hx
    rw [hΨ]
    simp only
    rw [intervalIntegral.integral_interval_sub_left (hGtc.intervalIntegrable _ _)
      (hGtc.intervalIntegrable _ _)]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by linarith)] at ht
    simp only [hGt, max_eq_left (show (2 : ℝ) ≤ t by linarith [ht.1])]
  have hΨd : ∀ x, HasDerivAt Ψ (Gt x) x := fun x =>
    (hGtc.integral_hasStrictDerivAt 0 x).hasDerivAt
  have hΨc : Continuous Ψ := continuous_iff_continuousAt.2 fun x => (hΨd x).continuousAt
  set F : ℝ → ℝ := fun x => A x + (Ψ x - Ψ (x - 1)) with hF
  have hFeq : ∀ x : ℝ, 3 ≤ x → A x + ∫ t in (x - 1)..x, G t = F x := by
    intro x hx; rw [hwin x hx]
  rw [hFeq s hs, hFeq 3 le_rfl]
  rcases eq_or_lt_of_le hs with h | h
  · rw [h]
  have hFc : ContinuousOn F (Set.Icc 3 s) := by
    refine (hA.mono Set.Icc_subset_Ici_self).add ?_
    exact (hΨc.sub (hΨc.comp (continuous_id.sub continuous_const))).continuousOn
  have hFd : ∀ x ∈ Set.Ioo 3 s, HasDerivAt F 0 x := by
    intro x hx
    have h1 := hAd x hx.1
    have h2 := hΨd x
    have h3 : HasDerivAt (fun y => Ψ (y - 1)) (Gt (x - 1)) x := by
      have := (hΨd (x - 1)).comp x ((hasDerivAt_id x).sub_const 1)
      rw [mul_one] at this
      exact this
    have h4 := h1.add (h2.sub h3)
    convert h4 using 1
    simp only [hGt, max_eq_left (show (2 : ℝ) ≤ x by linarith [hx.1]),
      max_eq_left (show (2 : ℝ) ≤ x - 1 by linarith [hx.1])]
    ring
  obtain ⟨c, _, hc⟩ := exists_hasDerivAt_eq_slope F (fun _ => (0 : ℝ)) h hFc hFd
  have hne : s - 3 ≠ 0 := by linarith
  field_simp at hc
  linarith

/-- Proof of the LEAF leafB8_IQ_const of Split1122bBoundary8.lean from continuity of the sums:
I is constant on [3, ∞), its derivative vanishing by leaf8_deriv_even_twin and
leaf8_deriv_odd_twin. -/
theorem leafB8_IQ_const_s77 (hc : ContinuousOn (fun s : ℝ => ∑' n : ℕ, if Odd n then bjsF306 n s else 0) (Set.Ici 1) ∧ ContinuousOn (fun s : ℝ => ∑' n : ℕ, if Even n then bjsF306 n s else 0) (Set.Ici 2)) (s : ℝ) (hs : 3 ≤ s) : qInvB8 s = qInvB8 3 := by
  have hO : ContinuousOn oSumB8 (Set.Ici 2) := hc.1.mono (Set.Ici_subset_Ici.2 (by norm_num))
  have hE : ContinuousOn eSumB8 (Set.Ici 2) := hc.2
  have hG : ContinuousOn (fun t => -(t * (oSumB8 t + eSumB8 t))) (Set.Ici 2) :=
    (continuousOn_id.mul (hO.add hE)).neg
  have hA : ContinuousOn (fun s => s * (s - 1) * (oSumB8 s + eSumB8 s)) (Set.Ici 3) :=
    ((continuousOn_id.mul (continuousOn_id.sub continuousOn_const)).mul
      (hO.add hE)).mono (Set.Ici_subset_Ici.2 (by norm_num))
  have hAd : ∀ x : ℝ, 3 < x → HasDerivAt (fun s => s * (s - 1) * (oSumB8 s + eSumB8 s))
      (-((-(x * (oSumB8 x + eSumB8 x))) - (-((x - 1) * (oSumB8 (x - 1) + eSumB8 (x - 1)))))) x := by
    intro x hx
    have hod := (leaf8_deriv_odd_twin.1 x hx)
    have hev := leaf8_deriv_even_twin x (by linarith)
    have hsum : HasDerivAt (fun t => t * oSumB8 t + t * eSumB8 t)
        (-(eSumB8 (x - 1)) + -(oSumB8 (x - 1))) x := hod.add hev
    have hm := ((hasDerivAt_id x).sub_const 1).mul hsum
    have heq : (fun s => s * (s - 1) * (oSumB8 s + eSumB8 s)) =
        fun s => (id s - 1) * (s * oSumB8 s + s * eSumB8 s) := by
      funext s; simp only [id]; ring
    rw [heq]
    convert hm using 1
    simp only [id]; ring
  have := window_const_s77 _ _ hG hA hAd s hs
  simp only [intervalIntegral.integral_neg] at this
  unfold qInvB8
  linarith

/-- Proof of the LEAF leafB8_J_const of Split1122bBoundary8.lean from continuity of the sums:
J is constant on [3, ∞) for any adjoint function q. -/
theorem leafB8_J_const_s77 (hc : ContinuousOn (fun s : ℝ => ∑' n : ℕ, if Odd n then bjsF306 n s else 0) (Set.Ici 1) ∧ ContinuousOn (fun s : ℝ => ∑' n : ℕ, if Even n then bjsF306 n s else 0) (Set.Ici 2)) (q : ℝ → ℝ) (hq : IsAdjB8 q) (s : ℝ) (hs : 3 ≤ s) : jInvB8 q s = jInvB8 q 3 := by
  have hO : ContinuousOn oSumB8 (Set.Ici 2) := hc.1.mono (Set.Ici_subset_Ici.2 (by norm_num))
  have hE : ContinuousOn eSumB8 (Set.Ici 2) := hc.2
  have hP : ContinuousOn pSumB8 (Set.Ici 2) := (continuousOn_const.add hO).sub hE
  have hqc : ContinuousOn q (Set.Ioi 0) := fun x hx =>
    (hq.1 x hx).continuousAt.continuousWithinAt
  have hq1 : ContinuousOn (fun t => q (t + 1)) (Set.Ici 2) :=
    hqc.comp (continuousOn_id.add continuousOn_const) (fun t ht => by
      simp only [Set.mem_Ioi]; have : (2:ℝ) ≤ t := ht; linarith)
  have hG : ContinuousOn (fun t => pSumB8 t * q (t + 1)) (Set.Ici 2) := hP.mul hq1
  have hA : ContinuousOn (fun s => s * q s * pSumB8 s) (Set.Ici 3) :=
    ((continuousOn_id.mul (hqc.mono (fun t ht => by
      simp only [Set.mem_Ioi]; have : (3:ℝ) ≤ t := ht; linarith))).mul
      (hP.mono (Set.Ici_subset_Ici.2 (by norm_num))))
  have hAd : ∀ x : ℝ, 3 < x → HasDerivAt (fun s => s * q s * pSumB8 s)
      (-(pSumB8 x * q (x + 1) - pSumB8 (x - 1) * q (x - 1 + 1))) x := by
    intro x hx
    have hod := (leaf8_deriv_odd_twin.1 x hx)
    have hev := leaf8_deriv_even_twin x (by linarith)
    have hsP : HasDerivAt (fun t => 2 * t + t * oSumB8 t - t * eSumB8 t)
        (2 * 1 + -(eSumB8 (x - 1)) - -(oSumB8 (x - 1))) x :=
      (((hasDerivAt_id x).const_mul 2).add hod).sub hev
    have hqd := hq.1 x (by linarith)
    have hm := hqd.mul hsP
    have heq : (fun s => s * q s * pSumB8 s) =
        fun s => q s * (2 * s + s * oSumB8 s - s * eSumB8 s) := by
      funext s; unfold pSumB8; ring
    rw [heq]
    convert hm using 1
    have hx0 : x ≠ 0 := by linarith
    unfold pSumB8
    rw [show x - 1 + 1 = x by ring]
    field_simp
    ring
  have := window_const_s77 _ _ hG hA hAd s hs
  unfold jInvB8
  linarith

/-- Display 15 on [1, ∞): f_1(s) = max (3 - s) 0 / s. -/
theorem f1_eq_s77M (s : ℝ) (hs : 1 ≤ s) : bjsF306 1 s = max (3 - s) 0 / s := by
  simp only [bjsF306]
  split_ifs with h
  · rw [max_eq_left (by linarith)]
  · rw [max_eq_right (by linarith), zero_div]

/-- Odd f_k is continuous on [1, ∞), including s = 1. -/
theorem fn_odd_contIci_s77M (k : ℕ) (ho : Odd k) : ContinuousOn (bjsF306 k) (Set.Ici 1) := by
  match k, ho with
  | 0, ho => exact absurd ho (by decide)
  | 1, _ =>
    have hc : ContinuousOn (fun s : ℝ => max (3 - s) 0 / s) (Set.Ici 1) := by
      refine ContinuousOn.div (by fun_prop) continuousOn_id ?_
      intro x hx; have : (1 : ℝ) ≤ x := hx; exact ne_of_gt (by linarith)
    exact hc.congr (fun s hs => f1_eq_s77M s hs)
  | m + 2, ho =>
    have hev : Even (m + 1) := even_of_odd_o8 m ho
    have hc1 := (fn_continuous_d8 (m + 1)).2 hev
    have hi := phi_integrable_d8 (m + 1) 3 (by norm_num)
      (fun x hx => Or.inr ⟨hev, by linarith⟩) (by norm_num; exact hc1)
    have hG := contG_d8 (fun u => bjsF306 (m + 1) (u - 1)) 3 hi
    have hcomp : ContinuousOn
        (fun s : ℝ => (∫ u in Set.Ioi (max s 3), bjsF306 (m + 1) (u - 1)) / s)
        (Set.Ici 1) := by
      refine ContinuousOn.div ?_ continuousOn_id ?_
      · refine hG.comp (continuous_id.max continuous_const).continuousOn ?_
        intro x _; exact le_max_right x 3
      · intro x hx; have : (1 : ℝ) ≤ x := hx; exact ne_of_gt (by linarith)
    refine hcomp.congr (fun s hs => ?_)
    simp only [bjsF306]
    split_ifs with h
    · rw [max_eq_right h.2]
    · have : 3 < s := by
        by_contra hc; exact h ⟨ho, by linarith⟩
      rw [max_eq_left this.le]

/-- Uniform bound from display 18 with Lemma 8: |f_n(x)| ≤ 2 · 0.9607 ^ (n - 1). -/
theorem fn_unif_bound_s77M (n : ℕ) (x : ℝ) (hx : (Odd n ∧ 1 ≤ x) ∨ (Even n ∧ 2 ≤ x)) :
    |bjsF306 n x| ≤ 2 * (0.9607 : ℝ) ^ (n - 1) := by
  rcases Nat.eq_zero_or_pos n with h0 | hn
  · subst h0; simp [bjsF306]
  have h1 := abs_fn_le_d8 n hn x hx
  have h2 := hSieve_le_d8 x
  have h3 : exp 2 * exp (-2) = 1 := by rw [← exp_add]; norm_num
  have h4 : 0 ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) := by positivity
  calc |bjsF306 n x|
      ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * LeanLab.ChenExplicit.hSieve x := h1
    _ ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (n - 1) * exp (-2) := mul_le_mul_of_nonneg_left h2 h4
    _ = 2 * (0.9607 : ℝ) ^ (n - 1) * (exp 2 * exp (-2)) := by ring
    _ = 2 * (0.9607 : ℝ) ^ (n - 1) := by rw [h3, mul_one]

theorem bound_summable_s77M : Summable (fun n : ℕ => 2 * (0.9607 : ℝ) ^ (n - 1)) := by
  rw [← summable_nat_add_iff 1]
  have : (fun m : ℕ => 2 * (0.9607 : ℝ) ^ (m + 1 - 1)) = fun m => 2 * (0.9607 : ℝ) ^ m := by
    funext m; rw [show m + 1 - 1 = m by omega]
  rw [this]
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

theorem leaf8_continuous_s77M :
    ContinuousOn (fun s : ℝ => ∑' n : ℕ, if Odd n then bjsF306 n s else 0) (Set.Ici 1) ∧
    ContinuousOn (fun s : ℝ => ∑' n : ℕ, if Even n then bjsF306 n s else 0) (Set.Ici 2) := by
  have hu0 : ∀ n : ℕ, 0 ≤ 2 * (0.9607 : ℝ) ^ (n - 1) := fun n => by positivity
  constructor
  · refine continuousOn_tsum (fun n => ?_) bound_summable_s77M (fun n x hx => ?_)
    · by_cases ho : Odd n
      · simp only [if_pos ho]; exact fn_odd_contIci_s77M n ho
      · simp only [if_neg ho]; exact continuousOn_const
    · by_cases ho : Odd n
      · rw [if_pos ho, Real.norm_eq_abs]
        exact fn_unif_bound_s77M n x (Or.inl ⟨ho, hx⟩)
      · rw [if_neg ho, norm_zero]; exact hu0 n
  · refine continuousOn_tsum (fun n => ?_) bound_summable_s77M (fun n x hx => ?_)
    · by_cases he : Even n
      · simp only [if_pos he]; exact fn_even_contIci_o8 n he
      · simp only [if_neg he]; exact continuousOn_const
    · by_cases he : Even n
      · rw [if_pos he, Real.norm_eq_abs]
        exact fn_unif_bound_s77M n x (Or.inr ⟨he, hx⟩)
      · rw [if_neg he, norm_zero]; exact hu0 n


/-- O(3) as the sum over odd n ≥ 3 at 3. -/
theorem hasSum_odd3_s77M :
    HasSum (fun n : ℕ => if Odd n ∧ 3 ≤ n then bjsF306 n 3 else 0) (oSumB8 3) := by
  convert (parity_summableB8 Odd 3 (fun _ h => Or.inl ⟨h, by norm_num⟩) (by norm_num)).hasSum
    using 1
  funext n
  match n with
  | 0 => simp
  | 1 => simp [bjsF306]
  | m + 2 =>
    by_cases ho : Odd (m + 2)
    · rw [if_pos ⟨ho, three_le_of_odd_s8 m ho⟩, if_pos ho]
    · rw [if_neg (fun h => ho h.1), if_neg ho]
  · rfl

/-- Display 17: O(t) = A / t - 1 on [1, 3], A = 3 (1 + O(3)). -/
theorem oSum_le3_s77M (t : ℝ) (h1 : 1 ≤ t) (h3 : t ≤ 3) :
    oSumB8 t = 3 * (1 + oSumB8 3) / t - 1 := by
  have ht0 : 0 < t := by linarith
  have hsum := (hasSum_ite_eq 1 ((3 - t) / t)).add (hasSum_odd3_s77M.mul_left (3 / t))
  have hh : HasSum (fun n : ℕ => if Odd n then bjsF306 n t else 0)
      ((3 - t) / t + 3 / t * oSumB8 3) := by
    convert hsum using 1
    funext n
    rw [odd_terms_le3_s8 t h1 h3 n]
  rw [oSumB8, hh.tsum_eq]
  field_simp
  ring

theorem eSum_cont_s77M : ContinuousOn eSumB8 (Set.Ici 2) := leaf8_continuous_s77M.2

/-- Display 16 summed on [2, 3]: t E(t) = 2 E(2) - A log (t - 1) + t - 2. -/
theorem tE_le3_s77M (t : ℝ) (h2 : 2 ≤ t) (h3 : t ≤ 3) :
    t * eSumB8 t = 2 * eSumB8 2 - 3 * (1 + oSumB8 3) * log (t - 1) + t - 2 := by
  set A := 3 * (1 + oSumB8 3) with hA
  set g : ℝ → ℝ := fun x => x * eSumB8 x - (2 * eSumB8 2 - A * log (x - 1) + x - 2) with hg
  suffices hgt : g t = g 2 by
    simp only [hg] at hgt
    norm_num at hgt
    linarith
  rcases h2.lt_or_eq with h2 | h2
  · have hc : ContinuousOn g (Set.Icc 2 t) := by
      have hE : ContinuousOn eSumB8 (Set.Icc 2 t) :=
        eSum_cont_s77M.mono Set.Icc_subset_Ici_self
      have hL : ContinuousOn (fun x : ℝ => log (x - 1)) (Set.Icc 2 t) := by
        refine ContinuousOn.log (by fun_prop) ?_
        intro x hx; have := hx.1; linarith
      exact (continuousOn_id.mul hE).sub
        ((((continuousOn_const.sub (continuousOn_const.mul hL)).add continuousOn_id)).sub
          continuousOn_const)
    have hd : ∀ x ∈ Set.Ioo 2 t, HasDerivAt g 0 x := by
      intro x hx
      have hx2 : 2 < x := hx.1
      have hx1 : x - 1 ≠ 0 := by linarith
      have hD := leaf8_deriv_even_twin x hx2
      have hlog : HasDerivAt (fun y : ℝ => log (y - 1)) (1 / (x - 1)) x := by
        have := ((hasDerivAt_id x).sub_const 1).log hx1
        simpa using this
      have hR : HasDerivAt (fun y : ℝ => 2 * eSumB8 2 - A * log (y - 1) + y - 2)
          (-(A * (1 / (x - 1))) + 1) x := by
        have := (((hasDerivAt_const x (2 * eSumB8 2)).sub (hlog.const_mul A)).add
          (hasDerivAt_id x)).sub_const 2
        simpa using this
      have hO : (∑' n : ℕ, if Odd n then bjsF306 n (x - 1) else 0) = A / (x - 1) - 1 :=
        oSum_le3_s77M (x - 1) (by linarith) (by linarith [hx.2])
      have key : HasDerivAt g (-(A / (x - 1) - 1) - (-(A * (1 / (x - 1))) + 1)) x := by
        rw [← hO]; exact hD.sub hR
      convert key using 1
      field_simp
      ring
    obtain ⟨c, _, hc'⟩ := exists_hasDerivAt_eq_slope g (fun _ => (0 : ℝ)) h2 hc hd
    have hne : t - 2 ≠ 0 := by linarith
    field_simp at hc'
    linarith
  · rw [h2]

/-- t Q(t) on [2, 3]. -/
theorem tQ_le3_s77M (t : ℝ) (h2 : 2 ≤ t) (h3 : t ≤ 3) :
    t * (oSumB8 t + eSumB8 t) =
      3 * (1 + oSumB8 3) + 2 * eSumB8 2 - 2 - 3 * (1 + oSumB8 3) * log (t - 1) := by
  have hO := oSum_le3_s77M t (by linarith) h3
  have hE := tE_le3_s77M t h2 h3
  have ht0 : t ≠ 0 := by linarith
  rw [mul_add, hE, hO]
  field_simp
  ring

theorem integral_log_sub_one_s77M : ∫ t in (2 : ℝ)..3, log (t - 1) = 2 * log 2 - 1 := by
  have hd : ∀ x ∈ Set.uIcc (2 : ℝ) 3,
      HasDerivAt (fun y : ℝ => (y - 1) * log (y - 1) - (y - 1)) (log (x - 1)) x := by
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    have hx1 : x - 1 ≠ 0 := by linarith [hx.1]
    have h1 : HasDerivAt (fun y : ℝ => y - 1) 1 x := (hasDerivAt_id x).sub_const 1
    have h2 := h1.log hx1
    have := (h1.mul h2).sub h1
    convert this using 1
    field_simp
    ring
  have hcont : ContinuousOn (fun x : ℝ => log (x - 1)) (Set.uIcc 2 3) := by
    refine ContinuousOn.log (by fun_prop) ?_
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    linarith [hx.1]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hd (hcont.intervalIntegrable)]
  norm_num
  ring

/-- Proof of the LEAF leafB8_IQ3 of Split1122bBoundary8.lean, statement verbatim, displays 16
and 17 on [2, 3]. -/
theorem leafB8_IQ3_s77 : qInvB8 3 = 2 * eSumB8 2 - 2 := by
  set A := 3 * (1 + oSumB8 3) with hA
  have hint : ∫ t in (3 - 1 : ℝ)..3, t * (oSumB8 t + eSumB8 t) =
      ∫ t in (2 : ℝ)..3, (A + 2 * eSumB8 2 - 2 - A * log (t - 1)) := by
    rw [show (3 - 1 : ℝ) = 2 by norm_num]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by norm_num)] at ht
    exact tQ_le3_s77M t ht.1 ht.2
  have hlogi : IntervalIntegrable (fun t : ℝ => log (t - 1)) MeasureTheory.volume 2 3 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine ContinuousOn.log (by fun_prop) ?_
    intro x hx
    rw [Set.uIcc_of_le (by norm_num)] at hx
    linarith [hx.1]
  have h3 := tQ_le3_s77M 3 (by norm_num) le_rfl
  unfold qInvB8
  rw [hint, intervalIntegral.integral_sub intervalIntegrable_const (hlogi.const_mul A),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
    integral_log_sub_one_s77M]
  norm_num at h3 ⊢
  nlinarith [h3]

/-- Proof of the LEAF leafB8_J3 of Split1122bBoundary8.lean, statement verbatim; the
hypothesis hq is not used. -/
theorem leafB8_J3_s77 (q : ℝ → ℝ) (hq : IsAdjB8 q) (he : eSumB8 2 = 1) :
    jInvB8 q 3 = 3 * (1 + oSumB8 3) * kConstB8 q := by
  set A := 3 * (1 + oSumB8 3) with hA
  have hP : ∀ t : ℝ, 2 ≤ t → t ≤ 3 → pSumB8 t = A * (1 + log (t - 1)) / t := by
    intro t h2 h3
    have hO := oSum_le3_s77M t (by linarith) h3
    have hE := tE_le3_s77M t h2 h3
    rw [he] at hE
    have ht0 : t ≠ 0 := by linarith
    have hE' : eSumB8 t = (2 * 1 - A * log (t - 1) + t - 2) / t := by
      rw [← hE]; field_simp
    unfold pSumB8
    rw [hO, hE']
    field_simp
    ring
  have hint : ∫ t in (3 - 1 : ℝ)..3, pSumB8 t * q (t + 1) =
      ∫ t in (2 : ℝ)..3, A * ((1 + log (t - 1)) * q (t + 1) / t) := by
    rw [show (3 - 1 : ℝ) = 2 by norm_num]
    refine intervalIntegral.integral_congr (fun t ht => ?_)
    rw [Set.uIcc_of_le (by norm_num)] at ht
    rw [hP t ht.1 ht.2]
    ring
  unfold jInvB8 kConstB8
  rw [hint, intervalIntegral.integral_const_mul, hP 3 (by norm_num) le_rfl]
  norm_num
  ring

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leaf8_continuous_s77
#print axioms LeanLab.Cai2002.leafB8_IQ_const_s77
#print axioms LeanLab.Cai2002.leafB8_J_const_s77
#print axioms LeanLab.Cai2002.leafB8_IQ3_s77
#print axioms LeanLab.Cai2002.leafB8_J3_s77
