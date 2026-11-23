/-
Twin proof of the LEAF `leaf8_deriv_odd` of `Split1122bSeries8.lean`.

Source: Bordignon, Johnston, Starichkova, arXiv 2207.09452, page 6, displays 15 to 18,
quoting Nathanson Theorem 9.4: f_1(s) = 0 for s > 3, display 15; for odd n ≥ 3 and
s ≥ 3, s f_n(s) = the integral over t > s of f_(n-1)(t - 1), display 16, with display 17
agreeing at s = 3. By the fundamental theorem of calculus (s f_n(s))' = - f_(n-1)(s - 1),
one sided at s = 3; summing over odd n is justified by the bound 18 with c_n = 0.9607,
Lemma 8, uniformly in s.

Method: each odd term on [3, ∞) is the restriction of a function defined on all of ℝ,
a constant minus the primitive of the continuous extension u ↦ f_(n-1)(max u 3 - 1);
the series of these extensions is differentiated termwise on ℝ, and both parts of the
LEAF follow by congruence on a neighbourhood of s > 3, resp. on [3, ∞).

The proof uses the PROVED results of `Prove1122bDerivEven8.lean` and key_l8306 of
`Split306Theorem6.lean`, Lemma 8 with c_n = 0.9607 for every n ≥ 1.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Prove1122bDerivEven8

open Finset Real

noncomputable section

namespace LeanLab.Cai2002

/-- Display 16 for even k: f_k is continuous on [2, ∞), including the endpoint. -/
theorem fn_even_contIci_o8 (k : ℕ) (he : Even k) :
    ContinuousOn (bjsF306 k) (Set.Ici 2) := by
  match k, he with
  | 0, _ => simp only [bjsF306]; exact continuousOn_const
  | 1, he => exact absurd he (by decide)
  | j + 2, he =>
    have hod : Odd (j + 1) := by
      rcases Nat.even_or_odd (j + 1) with h | h
      · exact absurd he (by rw [Nat.not_even_iff_odd]; exact h.add_one)
      · exact h
    have hc1 := (fn_continuous_d8 (j + 1)).1 hod
    have hi := phi_integrable_d8 (j + 1) 2 (by norm_num)
      (fun x hx => Or.inl ⟨hod, by linarith⟩) (by norm_num; exact hc1)
    have hG := contG_d8 (fun u => bjsF306 (j + 1) (u - 1)) 2 hi
    have hcomp : ContinuousOn
        (fun s : ℝ => (∫ u in Set.Ioi s, bjsF306 (j + 1) (u - 1)) / s) (Set.Ici 2) := by
      refine ContinuousOn.div hG continuousOn_id ?_
      intro x hx; have : (2 : ℝ) ≤ x := hx; exact ne_of_gt (by linarith)
    refine hcomp.congr (fun s hs => ?_)
    have hno : ¬ (Odd (j + 2) ∧ s ≤ 3) := fun h =>
      absurd h.1 (by rw [Nat.not_odd_iff_even]; exact he)
    simp only [bjsF306, if_neg hno]

/-- The continuous extension u ↦ f_(m+1)(max u 3 - 1) of the integrand of display 16. -/
def phiExt_o8 (m : ℕ) (u : ℝ) : ℝ := bjsF306 (m + 1) (max u 3 - 1)

theorem phiExt_cont_o8 (m : ℕ) (he : Even (m + 1)) : Continuous (phiExt_o8 m) := by
  have hc := fn_even_contIci_o8 (m + 1) he
  unfold phiExt_o8
  refine hc.comp_continuous (by fun_prop) (fun u => ?_)
  show (2 : ℝ) ≤ max u 3 - 1
  have := le_max_right u 3; linarith

/-- The extension of t ↦ ∫ over u > t of f_(m+1)(u - 1) to all of ℝ. -/
def KExt_o8 (m : ℕ) (t : ℝ) : ℝ :=
  (∫ u in Set.Ioi (3 : ℝ), bjsF306 (m + 1) (u - 1)) - ∫ u in (3 : ℝ)..t, phiExt_o8 m u

theorem KExt_eq_o8 (m : ℕ) (he : Even (m + 1)) (t : ℝ) (ht : 3 ≤ t) :
    KExt_o8 m t = ∫ u in Set.Ioi t, bjsF306 (m + 1) (u - 1) := by
  have hc1 := fn_even_contIci_o8 (m + 1) he
  have hi := phi_integrable_d8 (m + 1) 3 (by norm_num)
    (fun x hx => Or.inr ⟨he, by linarith⟩)
    ((hc1.mono (fun x hx => by have : (3 : ℝ) - 1 < x := hx; show (2:ℝ) ≤ x; linarith)))
  unfold KExt_o8
  have h1 : ∫ u in (3 : ℝ)..t, phiExt_o8 m u = ∫ u in (3 : ℝ)..t, bjsF306 (m + 1) (u - 1) := by
    refine intervalIntegral.integral_congr (fun u hu => ?_)
    rw [Set.uIcc_of_le ht] at hu
    simp only [phiExt_o8, max_eq_left hu.1]
  rw [h1, ← intervalIntegral.integral_Ioi_sub_Ioi hi ht]
  ring

theorem KExt_deriv_o8 (m : ℕ) (he : Even (m + 1)) (y : ℝ) :
    HasDerivAt (KExt_o8 m) (-phiExt_o8 m y) y := by
  have h := ((phiExt_cont_o8 m he).integral_hasStrictDerivAt 3 y).hasDerivAt.const_sub
    (∫ u in Set.Ioi (3 : ℝ), bjsF306 (m + 1) (u - 1))
  exact h

/-- Odd n = m + 2 forces m + 1 even. -/
theorem even_of_odd_o8 (m : ℕ) (ho : Odd (m + 2)) : Even (m + 1) := by
  rcases Nat.even_or_odd (m + 1) with h | h
  · exact h
  · exact absurd ho (by rw [Nat.not_odd_iff_even]; exact h.add_one)

/-- The odd terms of the extended series. -/
def gOdd_o8 (n : ℕ) (t : ℝ) : ℝ := if Odd n ∧ 2 ≤ n then KExt_o8 (n - 2) t else 0

/-- The termwise derivatives of gOdd_o8, minus the integrand of display 16. -/
def gOdd'_o8 (n : ℕ) (y : ℝ) : ℝ := if Odd n ∧ 2 ≤ n then -phiExt_o8 (n - 2) y else 0

/-- Displays 15, 16 and 17: for t ≥ 3 the extended odd term is t f_n(t). -/
theorem gOdd_eq_o8 (n : ℕ) (t : ℝ) (ht : 3 ≤ t) :
    gOdd_o8 n t = if Odd n then t * bjsF306 n t else 0 := by
  have htp : t ≠ 0 := by intro h; linarith
  match n with
  | 0 => simp [gOdd_o8]
  | 1 =>
    simp only [gOdd_o8, show ¬ (Odd 1 ∧ 2 ≤ 1) from by omega, if_false, if_pos odd_one,
      bjsF306]
    split_ifs with h
    · have : t = 3 := le_antisymm h ht
      subst this; norm_num
    · simp
  | m + 2 =>
    by_cases ho : Odd (m + 2)
    · have he := even_of_odd_o8 m ho
      simp only [gOdd_o8, if_pos (And.intro ho (by omega : 2 ≤ m + 2)), if_pos ho,
        show m + 2 - 2 = m by omega, KExt_eq_o8 m he t ht, bjsF306]
      split_ifs with h
      · have : t = 3 := le_antisymm h.2 ht
        subst this; field_simp
      · field_simp
    · simp [gOdd_o8, ho]

theorem gOdd_deriv_o8 (n : ℕ) (y : ℝ) : HasDerivAt (gOdd_o8 n) (gOdd'_o8 n y) y := by
  by_cases h : Odd n ∧ 2 ≤ n
  · have hfun : gOdd_o8 n = KExt_o8 (n - 2) := by
      funext t; simp only [gOdd_o8, if_pos h]
    rw [hfun]; simp only [gOdd'_o8, if_pos h]
    obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    rw [show m + 2 - 2 = m by omega]
    exact KExt_deriv_o8 m (even_of_odd_o8 m h.1) y
  · have hfun : gOdd_o8 n = fun _ => 0 := by
      funext t; simp only [gOdd_o8, if_neg h]
    rw [hfun]; simp only [gOdd'_o8, if_neg h]
    exact hasDerivAt_const y (0 : ℝ)

theorem gOdd_bound_o8 (n : ℕ) (y : ℝ) : ‖gOdd'_o8 n y‖ ≤ 2 * (0.9607 : ℝ) ^ (n - 2) := by
  have hu : 0 ≤ 2 * (0.9607 : ℝ) ^ (n - 2) := by positivity
  unfold gOdd'_o8
  split_ifs with h
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
    have he := even_of_odd_o8 m h.1
    rw [show m + 2 - 2 = m by omega, norm_neg, Real.norm_eq_abs]
    unfold phiExt_o8
    have hx : (2 : ℝ) ≤ max y 3 - 1 := by have := le_max_right y 3; linarith
    have h1 := abs_fn_le_d8 (m + 1) (by omega) (max y 3 - 1) (Or.inr ⟨he, hx⟩)
    rw [show m + 1 - 1 = m by omega] at h1
    have h2 := hSieve_le_d8 (max y 3 - 1)
    have h3 : exp 2 * exp (-2) = 1 := by rw [← exp_add]; norm_num
    have h4 : 0 ≤ 2 * exp 2 * (0.9607 : ℝ) ^ m := by positivity
    calc |bjsF306 (m + 1) (max y 3 - 1)|
        ≤ 2 * exp 2 * (0.9607 : ℝ) ^ m * LeanLab.ChenExplicit.hSieve (max y 3 - 1) := h1
      _ ≤ 2 * exp 2 * (0.9607 : ℝ) ^ m * exp (-2) := mul_le_mul_of_nonneg_left h2 h4
      _ = 2 * (0.9607 : ℝ) ^ m * (exp 2 * exp (-2)) := by ring
      _ = 2 * (0.9607 : ℝ) ^ m := by rw [h3, mul_one]
  · simpa using hu

/-- The series of s f_n(s) over odd n converges for s ≥ 1, display 18 with Lemma 8. -/
theorem odd_summable_o8 (s : ℝ) (hs : 1 ≤ s) :
    Summable (fun n : ℕ => if Odd n then s * bjsF306 n s else 0) := by
  rw [← summable_nat_add_iff 1]
  have hspos : 0 ≤ s := by linarith
  have hh := hSieve_nonneg306 s hspos
  set C := s * (2 * exp 2 * LeanLab.ChenExplicit.hSieve s) with hC
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 0.9607) (by norm_num)).mul_left C)
  · split_ifs with h
    · exact mul_nonneg hspos (leaf306_fn_nonneg _ s (Or.inl ⟨h, hs⟩))
    · exact le_rfl
  · split_ifs with h
    · have := key_l8306 (k + 1) (by omega) s (Or.inl ⟨h, hs⟩)
      rw [show k + 1 - 1 = k by omega] at this
      rw [hC]
      have : s * bjsF306 (k + 1) s ≤ s * (2 * exp 2 * (0.9607 : ℝ) ^ k *
          LeanLab.ChenExplicit.hSieve s) := mul_le_mul_of_nonneg_left this hspos
      linarith
    · positivity

/-- The extended series has derivative ∑ gOdd' at every y, termwise by the bound 18. -/
theorem gsum_deriv_o8 (y : ℝ) :
    HasDerivAt (fun z => ∑' n, gOdd_o8 n z) (∑' n, gOdd'_o8 n y) y := by
  have hs3 : Summable (fun n => gOdd_o8 n 3) := by
    have := odd_summable_o8 3 (by norm_num)
    refine this.congr (fun n => ?_)
    rw [gOdd_eq_o8 n 3 le_rfl]
  exact hasDerivAt_tsum_of_isPreconnected bound_summable_d8 isOpen_univ isPreconnected_univ
    (fun n y _ => gOdd_deriv_o8 n y) (fun n y _ => gOdd_bound_o8 n y) (Set.mem_univ 3) hs3
    (Set.mem_univ y)

/-- For y ≥ 3 the summed derivative is - the sum of f_n(y - 1) over even n. -/
theorem gsum'_eq_o8 (y : ℝ) (hy : 3 ≤ y) :
    ∑' n, gOdd'_o8 n y = -(∑' n : ℕ, if Even n then bjsF306 n (y - 1) else 0) := by
  have hsum : Summable (fun n => gOdd'_o8 n y) :=
    Summable.of_norm_bounded bound_summable_d8 (fun n => gOdd_bound_o8 n y)
  rw [hsum.tsum_eq_zero_add]
  have h0 : gOdd'_o8 0 y = 0 := by simp [gOdd'_o8]
  rw [h0, zero_add, ← tsum_neg]
  congr 1; funext k
  rcases k with _ | k
  · simp [gOdd'_o8, bjsF306]
  · have hmax : max y 3 = y := max_eq_left hy
    simp only [gOdd'_o8, phiExt_o8, hmax, show k + 1 + 1 - 2 = k by omega,
      show 2 ≤ k + 1 + 1 by omega, and_true, Nat.odd_add_one, Nat.not_odd_iff_even]
    split_ifs <;> simp_all [Nat.even_add_one]

/-- Twin of the LEAF `leaf8_deriv_odd` of `Split1122bSeries8.lean`: displays 15 and 16
for odd n differentiated and summed, BJS page 6, Nathanson Theorem 9.4. -/
theorem leaf8_deriv_odd_twin :
    (∀ s : ℝ, 3 < s →
      HasDerivAt (fun t : ℝ => t * ∑' n : ℕ, if Odd n then bjsF306 n t else 0)
        (-(∑' n : ℕ, if Even n then bjsF306 n (s - 1) else 0)) s) ∧
    HasDerivWithinAt (fun t : ℝ => t * ∑' n : ℕ, if Odd n then bjsF306 n t else 0)
        (-(∑' n : ℕ, if Even n then bjsF306 n 2 else 0)) (Set.Ici 3) 3 := by
  have hF : ∀ t : ℝ, 3 ≤ t →
      (t * ∑' n : ℕ, if Odd n then bjsF306 n t else 0) = ∑' n, gOdd_o8 n t := by
    intro t ht
    rw [← tsum_mul_left]
    congr 1; funext n
    rw [gOdd_eq_o8 n t ht]
    split_ifs <;> simp
  refine ⟨fun s hs => ?_, ?_⟩
  · have h := gsum_deriv_o8 s
    rw [gsum'_eq_o8 s hs.le] at h
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hs] with z hz
    exact hF z (le_of_lt hz)
  · have h := (gsum_deriv_o8 3).hasDerivWithinAt (s := Set.Ici 3)
    rw [gsum'_eq_o8 3 le_rfl, show (3 : ℝ) - 1 = 2 by norm_num] at h
    exact h.congr (fun t ht => hF t ht) (hF 3 le_rfl)

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leaf8_deriv_odd_twin
