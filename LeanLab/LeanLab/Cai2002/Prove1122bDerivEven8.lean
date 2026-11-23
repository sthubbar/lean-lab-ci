/-
Twin proof of the LEAF `leaf8_deriv_even` of `Split1122bSeries8.lean`.

Source: Bordignon, Johnston, Starichkova, arXiv 2207.09452, page 6, displays 16 and 18,
quoting Nathanson Theorem 9.4: for even n ≥ 2 and s > 2,
s f_n(s) = the integral over t > s of f_(n-1)(t - 1), display 16, so by the fundamental
theorem of calculus (s f_n(s))' = - f_(n-1)(s - 1); summing over even n is justified by
the bound 18 with c_n = 0.9607, Lemma 8, which gives a summable bound on the derivatives
uniformly for s > 2.

The proof uses the PROVED bound key_l8306 of `Split306Theorem6.lean`, Lemma 8 with
c_n = 0.9607 for every n ≥ 1, and leaf306_fn_nonneg; it does not use Lemma 7.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Prove1122bSummable8

open Finset Real

noncomputable section

namespace LeanLab.Cai2002

/-- h(s) ≤ e ^ -2 for every s, from the definition of h in display 18. -/
theorem hSieve_le_d8 (x : ℝ) : LeanLab.ChenExplicit.hSieve x ≤ exp (-2) := by
  unfold LeanLab.ChenExplicit.hSieve
  split_ifs with h1 h2
  · exact le_rfl
  · exact exp_le_exp.mpr (by linarith)
  · have hx : 3 < x := by linarith
    have hinv0 : 0 < x⁻¹ := inv_pos.mpr (by linarith)
    have h3 : 3 * x⁻¹ ≤ 1 := by
      rw [← div_eq_mul_inv, div_le_one (by linarith)]; linarith
    have he : exp (-x) ≤ exp (-2) := exp_le_exp.mpr (by linarith)
    have := exp_pos (-x)
    nlinarith

/-- Display 18 with Lemma 8, two sided: |f_k(x)| ≤ 2 e ^ 2 0.9607 ^ (k - 1) h(x). -/
theorem abs_fn_le_d8 (k : ℕ) (hk : 1 ≤ k) (x : ℝ) (hx : (Odd k ∧ 1 ≤ x) ∨ (Even k ∧ 2 ≤ x)) :
    |bjsF306 k x| ≤ 2 * exp 2 * (0.9607 : ℝ) ^ (k - 1) * LeanLab.ChenExplicit.hSieve x := by
  rw [abs_of_nonneg (leaf306_fn_nonneg k x hx)]
  exact key_l8306 k hk x hx

/-- The integrand of display 16, t ↦ f_k(t - 1), is integrable on t > a when f_k is
continuous beyond a - 1 and the parity range of display 18 holds there. -/
theorem phi_integrable_d8 (k : ℕ) (a : ℝ) (ha : 1 ≤ a)
    (hpar : ∀ x, a - 1 < x → (Odd k ∧ 1 ≤ x) ∨ (Even k ∧ 2 ≤ x))
    (hc : ContinuousOn (bjsF306 k) (Set.Ioi (a - 1))) :
    MeasureTheory.IntegrableOn (fun u => bjsF306 k (u - 1)) (Set.Ioi a) := by
  rcases Nat.eq_zero_or_pos k with h0 | hk
  · subst h0
    simp [bjsF306]
  have hc' : ContinuousOn (fun u => bjsF306 k (u - 1)) (Set.Ioi a) := by
    refine hc.comp (continuousOn_id.sub continuousOn_const) ?_
    intro u hu
    show a - 1 < u - 1
    have : a < u := hu
    linarith
  have hI := (leaf306_hshift_integrable a ha).const_mul (2 * exp 2 * (0.9607 : ℝ) ^ (k - 1))
  refine hI.mono' (hc'.aestronglyMeasurable measurableSet_Ioi) ?_
  filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with u hu
  have hu' : a < u := hu
  rw [Real.norm_eq_abs]
  exact abs_fn_le_d8 k hk (u - 1) (hpar _ (by linarith))

/-- The tail integral z ↦ ∫ over t > z of φ is continuous on [a, ∞) when φ is integrable
on t > a. -/
theorem contG_d8 (φ : ℝ → ℝ) (a : ℝ) (hi : MeasureTheory.IntegrableOn φ (Set.Ioi a)) :
    ContinuousOn (fun z => ∫ u in Set.Ioi z, φ u) (Set.Ici a) := by
  set ψ := (Set.Ioi a).indicator φ with hψ
  have hψi : MeasureTheory.Integrable ψ :=
    (MeasureTheory.integrable_indicator_iff measurableSet_Ioi).2 hi
  have hcont : Continuous fun z => (∫ u in Set.Ioi a, φ u) - ∫ u in a..z, ψ u :=
    continuous_const.sub (intervalIntegral.continuous_primitive
      (fun _ _ => hψi.intervalIntegrable) a)
  refine hcont.continuousOn.congr ?_
  intro z hz
  have hz' : a ≤ z := hz
  show ∫ u in Set.Ioi z, φ u = (∫ u in Set.Ioi a, φ u) - ∫ u in a..z, ψ u
  have h1 : ∫ u in a..z, ψ u = ∫ u in a..z, φ u := by
    rw [intervalIntegral.integral_of_le hz', intervalIntegral.integral_of_le hz']
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioc (fun u hu => ?_)
    exact Set.indicator_of_mem (show u ∈ Set.Ioi a from hu.1) φ
  rw [h1, ← intervalIntegral.integral_Ioi_sub_Ioi hi hz']
  ring

/-- Fundamental theorem of calculus for the tail integral of display 16: if φ is
integrable on t > a and continuous at s > a, then z ↦ ∫ over t > z of φ has derivative
- φ(s) at s. -/
theorem derivG_d8 (φ : ℝ → ℝ) (a s : ℝ) (has : a < s)
    (hi : MeasureTheory.IntegrableOn φ (Set.Ioi a)) (hc : ContinuousAt φ s) :
    HasDerivAt (fun z => ∫ u in Set.Ioi z, φ u) (-φ s) s := by
  have hII : IntervalIntegrable φ MeasureTheory.volume a s :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le has.le).2
      (hi.mono_set Set.Ioc_subset_Ioi_self)
  have hmeas : StronglyMeasurableAtFilter φ (nhds s) :=
    AEStronglyMeasurable.stronglyMeasurableAtFilter_of_mem hi.aestronglyMeasurable
      (Ioi_mem_nhds has)
  have hd := (intervalIntegral.integral_hasDerivAt_right hII hmeas hc).const_sub
    (∫ u in Set.Ioi a, φ u)
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds has] with z hz
  have hz' : a ≤ z := le_of_lt hz
  rw [← intervalIntegral.integral_Ioi_sub_Ioi hi hz']
  ring

/-- Display 15 continuity: on s > 1, f_1(s) = max (3 - s) 0 / s. -/
theorem f1_eq_d8 (s : ℝ) (hs : 1 < s) : bjsF306 1 s = max (3 - s) 0 / s := by
  simp only [bjsF306]
  split_ifs with h
  · rw [max_eq_left (by linarith)]
  · rw [max_eq_right (by linarith), zero_div]

/-- Continuity of the functions f_n of displays 15 to 17 where the paper uses them:
odd n on s > 1 and even n on s > 2, by induction on n from the tail integrals. -/
theorem fn_continuous_d8 (k : ℕ) :
    (Odd k → ContinuousOn (bjsF306 k) (Set.Ioi 1)) ∧
    (Even k → ContinuousOn (bjsF306 k) (Set.Ioi 2)) := by
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    match k, ih with
    | 0, _ =>
      refine ⟨fun h => absurd h (by decide), fun _ => ?_⟩
      simp only [bjsF306]; exact continuousOn_const
    | 1, _ =>
      refine ⟨fun _ => ?_, fun h => absurd h (by decide)⟩
      have hc : ContinuousOn (fun s : ℝ => max (3 - s) 0 / s) (Set.Ioi 1) := by
        refine ContinuousOn.div (by fun_prop) continuousOn_id ?_
        intro x hx; have : (1 : ℝ) < x := hx; exact ne_of_gt (by linarith)
      exact hc.congr (fun s hs => f1_eq_d8 s hs)
    | m + 2, ih =>
      refine ⟨fun ho => ?_, fun he => ?_⟩
      · -- odd n = m + 2: f_n(s) = G(max s 3) / s on s > 1, displays 16 and 17
        have hev : Even (m + 1) := by
          rcases Nat.even_or_odd (m + 1) with h | h
          · exact h
          · exact absurd ho (by rw [Nat.not_odd_iff_even]; exact h.add_one)
        have hc1 := (ih (m + 1) (by omega)).2 hev
        have hi := phi_integrable_d8 (m + 1) 3 (by norm_num)
          (fun x hx => Or.inr ⟨hev, by linarith⟩) (by norm_num; exact hc1)
        have hG := contG_d8 (fun u => bjsF306 (m + 1) (u - 1)) 3 hi
        have hcomp : ContinuousOn
            (fun s : ℝ => (∫ u in Set.Ioi (max s 3), bjsF306 (m + 1) (u - 1)) / s)
            (Set.Ioi 1) := by
          refine ContinuousOn.div ?_ continuousOn_id ?_
          · refine hG.comp (continuous_id.max continuous_const).continuousOn ?_
            intro x _; exact le_max_right x 3
          · intro x hx; have : (1 : ℝ) < x := hx; exact ne_of_gt (by linarith)
        refine hcomp.congr (fun s hs => ?_)
        simp only [bjsF306]
        split_ifs with h
        · rw [max_eq_right h.2]
        · have : 3 < s := by
            by_contra hc; exact h ⟨ho, by linarith⟩
          rw [max_eq_left this.le]
      · -- even n = m + 2: f_n(s) = G(s) / s on s > 2, display 16
        have hod : Odd (m + 1) := by
          rcases Nat.even_or_odd (m + 1) with h | h
          · exact absurd he (by rw [Nat.not_even_iff_odd]; exact h.add_one)
          · exact h
        have hc1 := (ih (m + 1) (by omega)).1 hod
        have hi := phi_integrable_d8 (m + 1) 2 (by norm_num)
          (fun x hx => Or.inl ⟨hod, by linarith⟩) (by norm_num; exact hc1)
        have hG := contG_d8 (fun u => bjsF306 (m + 1) (u - 1)) 2 hi
        have hcomp : ContinuousOn
            (fun s : ℝ => (∫ u in Set.Ioi s, bjsF306 (m + 1) (u - 1)) / s) (Set.Ioi 2) := by
          refine ContinuousOn.div (hG.mono Set.Ioi_subset_Ici_self) continuousOn_id ?_
          intro x hx; have : (2 : ℝ) < x := hx; exact ne_of_gt (by linarith)
        refine hcomp.congr (fun s hs => ?_)
        have hno : ¬ (Odd (m + 2) ∧ s ≤ 3) := fun h =>
          absurd h.1 (by rw [Nat.not_odd_iff_even]; exact he)
        simp only [bjsF306, if_neg hno]

/-- Display 16 differentiated, BJS page 6: for even n = m + 2 and y > 2,
(s f_n(s))' = - f_(n-1)(y - 1) at s = y. -/
theorem deriv_term_even_d8 (m : ℕ) (he : Even (m + 2)) (y : ℝ) (hy : 2 < y) :
    HasDerivAt (fun z => z * bjsF306 (m + 2) z) (-bjsF306 (m + 1) (y - 1)) y := by
  have hod : Odd (m + 1) := by
    rcases Nat.even_or_odd (m + 1) with h | h
    · exact absurd he (by rw [Nat.not_even_iff_odd]; exact h.add_one)
    · exact h
  have hc1 := (fn_continuous_d8 (m + 1)).1 hod
  have hi := phi_integrable_d8 (m + 1) 2 (by norm_num)
    (fun x hx => Or.inl ⟨hod, by linarith⟩) (by norm_num; exact hc1)
  have hca : ContinuousAt (fun u => bjsF306 (m + 1) (u - 1)) y := by
    have : ContinuousAt (bjsF306 (m + 1)) (y - 1) :=
      hc1.continuousAt (Ioi_mem_nhds (by linarith))
    exact ContinuousAt.comp_of_eq this (by fun_prop) rfl
  have hd := derivG_d8 (fun u => bjsF306 (m + 1) (u - 1)) 2 y hy hi hca
  refine hd.congr_of_eventuallyEq ?_
  filter_upwards [Ioi_mem_nhds hy] with z hz
  have hz' : (2 : ℝ) < z := hz
  have hno : ¬ (Odd (m + 2) ∧ z ≤ 3) := fun h =>
    absurd h.1 (by rw [Nat.not_odd_iff_even]; exact he)
  simp only [bjsF306, if_neg hno]
  field_simp

/-- The summable bound on the termwise derivatives, uniform for y > 2, from display 18. -/
theorem deriv_bound_d8 (n : ℕ) (y : ℝ) (hy : 2 < y) :
    ‖(if Even n then -bjsF306 (n - 1) (y - 1) else 0)‖ ≤ 2 * (0.9607 : ℝ) ^ (n - 2) := by
  have hu : 0 ≤ 2 * (0.9607 : ℝ) ^ (n - 2) := by positivity
  split_ifs with he
  · match n, he with
    | 0, _ => simpa [bjsF306] using hu
    | 1, he => exact absurd he (by decide)
    | m + 2, he =>
      have hod : Odd (m + 1) := by
        rcases Nat.even_or_odd (m + 1) with h | h
        · exact absurd he (by rw [Nat.not_even_iff_odd]; exact h.add_one)
        · exact h
      rw [show m + 2 - 1 = m + 1 by omega, show m + 2 - 2 = m by omega, norm_neg,
        Real.norm_eq_abs]
      have h1 := abs_fn_le_d8 (m + 1) (by omega) (y - 1) (Or.inl ⟨hod, by linarith⟩)
      rw [show m + 1 - 1 = m by omega] at h1
      have h2 := hSieve_le_d8 (y - 1)
      have h3 : exp 2 * exp (-2) = 1 := by rw [← exp_add]; norm_num
      have h4 : 0 ≤ 2 * exp 2 * (0.9607 : ℝ) ^ m := by positivity
      calc |bjsF306 (m + 1) (y - 1)|
          ≤ 2 * exp 2 * (0.9607 : ℝ) ^ m * LeanLab.ChenExplicit.hSieve (y - 1) := h1
        _ ≤ 2 * exp 2 * (0.9607 : ℝ) ^ m * exp (-2) := mul_le_mul_of_nonneg_left h2 h4
        _ = 2 * (0.9607 : ℝ) ^ m * (exp 2 * exp (-2)) := by ring
        _ = 2 * (0.9607 : ℝ) ^ m := by rw [h3, mul_one]
  · simpa using hu

/-- The bound sequence 2 · 0.9607 ^ (n - 2) is summable. -/
theorem bound_summable_d8 : Summable (fun n : ℕ => 2 * (0.9607 : ℝ) ^ (n - 2)) := by
  rw [← summable_nat_add_iff 2]
  have : (fun m : ℕ => 2 * (0.9607 : ℝ) ^ (m + 2 - 2)) = fun m => 2 * (0.9607 : ℝ) ^ m := by
    funext m; rw [show m + 2 - 2 = m by omega]
  rw [this]
  exact (summable_geometric_of_lt_one (by norm_num) (by norm_num)).mul_left _

/-- The series of s f_n(s) over even n converges for s ≥ 2, display 18 with Lemma 8. -/
theorem even_summable_d8 (s : ℝ) (hs : 2 ≤ s) :
    Summable (fun n : ℕ => if Even n then s * bjsF306 n s else 0) := by
  rw [← summable_nat_add_iff 1]
  have hspos : 0 ≤ s := by linarith
  have hh := hSieve_nonneg306 s hspos
  set C := s * (2 * exp 2 * LeanLab.ChenExplicit.hSieve s) with hC
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 0.9607) (by norm_num)).mul_left C)
  · split_ifs with h
    · exact mul_nonneg hspos (leaf306_fn_nonneg _ s (Or.inr ⟨h, hs⟩))
    · exact le_rfl
  · split_ifs with h
    · have := key_l8306 (k + 1) (by omega) s (Or.inr ⟨h, hs⟩)
      rw [show k + 1 - 1 = k by omega] at this
      rw [hC]
      have : s * bjsF306 (k + 1) s ≤ s * (2 * exp 2 * (0.9607 : ℝ) ^ k *
          LeanLab.ChenExplicit.hSieve s) := mul_le_mul_of_nonneg_left this hspos
      linarith
    · positivity

/-- Twin of the LEAF `leaf8_deriv_even` of `Split1122bSeries8.lean`: display 16 for even
n ≥ 2 differentiated and summed, BJS page 6, Nathanson Theorem 9.4. -/
theorem leaf8_deriv_even_twin (s : ℝ) (hs : 2 < s) :
    HasDerivAt (fun t : ℝ => t * ∑' n : ℕ, if Even n then bjsF306 n t else 0)
      (-(∑' n : ℕ, if Odd n then bjsF306 n (s - 1) else 0)) s := by
  set g : ℕ → ℝ → ℝ := fun n z => if Even n then z * bjsF306 n z else 0 with hg
  set g' : ℕ → ℝ → ℝ := fun n y => if Even n then -bjsF306 (n - 1) (y - 1) else 0 with hg'
  have hfun : (fun t : ℝ => t * ∑' n : ℕ, if Even n then bjsF306 n t else 0) =
      fun z => ∑' n, g n z := by
    funext t
    rw [← tsum_mul_left]
    congr 1; funext n
    simp only [hg]
    split_ifs <;> simp
  have hderiv : ∀ n y, y ∈ Set.Ioi (2 : ℝ) → HasDerivAt (g n) (g' n y) y := by
    intro n y hy
    have hy' : (2 : ℝ) < y := hy
    by_cases he : Even n
    · match n, he with
      | 0, _ =>
        have h00 : ∀ x, bjsF306 0 x = 0 := fun _ => rfl
        simpa [hg, hg', h00] using (hasDerivAt_const y (0 : ℝ))
      | 1, he => exact absurd he (by decide)
      | m + 2, he =>
        simp only [hg, hg', if_pos he, show m + 2 - 1 = m + 1 by omega]
        exact deriv_term_even_d8 m he y hy'
    · simp only [hg, hg', if_neg he]
      exact hasDerivAt_const y (0 : ℝ)
  have hmain := hasDerivAt_tsum_of_isPreconnected bound_summable_d8 isOpen_Ioi
    isPreconnected_Ioi hderiv (fun n y hy => deriv_bound_d8 n y hy)
    (show s ∈ Set.Ioi (2 : ℝ) from hs) (even_summable_d8 s hs.le)
    (show s ∈ Set.Ioi (2 : ℝ) from hs)
  rw [hfun]
  convert hmain using 1
  have hsum : Summable (fun n => g' n s) :=
    Summable.of_norm_bounded bound_summable_d8 (fun n => deriv_bound_d8 n s hs)
  rw [hsum.tsum_eq_zero_add]
  have h0 : g' 0 s = 0 := by simp [hg', bjsF306]
  rw [h0, zero_add, ← tsum_neg]
  congr 1; funext k
  simp only [hg', Nat.even_add_one, Nat.not_even_iff_odd, Nat.add_sub_cancel]
  split_ifs <;> simp

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leaf8_deriv_even_twin
