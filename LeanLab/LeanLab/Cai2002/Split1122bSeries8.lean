/-
Split of leaf306_series_solve8 of Split306Theorem6.lean: the existence half of
Nathanson Theorem 9.4 as quoted by Bordignon, Johnston and Starichkova,
arXiv 2207.09452v6, papers/P0009.pdf, page 6, displays 8 and 13 to 18.
The twin leaf306_series_solve8_twin is proved from LEAF lemmas:
* summability of the series 13 and 14 from the bound 18 with Lemma 8;
* continuity of their sums, uniform convergence from the same bound;
* the termwise derivatives of s f_n(s) from displays 15 and 16, summed;
* F(3) = 2 e ^ γ / 3, the analytic core of Theorem 9.4, with display 17;
* f(2) = 0 for the series 14, the second analytic boundary value.
The reduction of the series 13 on [1, 3] to its value at s = 3 by display 17 and the
assembly into the delay differential system 8 are proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Split306Theorem6
import LeanLab.Cai2002.Prove2672Series8

open Finset Real
noncomputable section
namespace LeanLab.Cai2002

/-- LEAF: BJS display 18 with Lemma 8, Nathanson Lemma 9.7, page 6: f_n(s) ≤ 2 e ^ 2 c_n ^ (n - 1) h(s)
with c_n ≤ 0.9607 for n ≥ 2, so the series 13 converges for s ≥ 1 and the series 14
for s ≥ 2. Class MEDIUM: needs the bound 18 for all n, a geometric comparison and
nonnegativity, leaf306_fn_nonneg. -/
theorem leaf8_summable :
    (∀ s : ℝ, 1 ≤ s → Summable (fun n : ℕ => if Odd n then bjsF306 n s else 0)) ∧
    (∀ s : ℝ, 2 ≤ s → Summable (fun n : ℕ => if Even n then bjsF306 n s else 0)) := by
  have hsum (P : ℕ → Prop) [DecidablePred P] (s : ℝ)
      (hP : ∀ n, P n → (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s)) :
      Summable (fun n : ℕ => if P n then bjsF306 n s else 0) := by
    rw [← summable_nat_add_iff 1]
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_)
      ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 0.9607)
        (by norm_num)).mul_left (2 * exp 2 * |LeanLab.ChenExplicit.hSieve s|))
    · split_ifs with h
      · exact leaf306_fn_nonneg _ s (hP _ h)
      · exact le_rfl
    · split_ifs with h
      · have hb := key_l8306 (n + 1) (by omega) s (hP _ h)
        rw [Nat.add_sub_cancel] at hb
        calc bjsF306 (n + 1) s
            ≤ 2 * exp 2 * (0.9607 : ℝ) ^ n * |LeanLab.ChenExplicit.hSieve s| :=
              hb.trans (mul_le_mul_of_nonneg_left (le_abs_self _) (by positivity))
          _ = _ := by ring
      · positivity
  exact ⟨fun s hs => hsum Odd s (fun _ h => Or.inl ⟨h, hs⟩),
    fun s hs => hsum Even s (fun _ h => Or.inr ⟨h, hs⟩)⟩

/-- LEAF: continuity of the sums of the series 13 and 14 of BJS page 6, Nathanson
Theorem 9.4: each f_n is continuous where used, displays 15 to 17, and the bound 18
gives uniform convergence by the Weierstrass test. Class MEDIUM. -/
theorem leaf8_continuous :
    ContinuousOn (fun s : ℝ => ∑' n : ℕ, if Odd n then bjsF306 n s else 0) (Set.Ici 1) ∧
    ContinuousOn (fun s : ℝ => ∑' n : ℕ, if Even n then bjsF306 n s else 0) (Set.Ici 2) := by
  constructor
  · refine continuousOn_tsum (u := Series8Proof2672.majU8) (fun n => ?_)
      Series8Proof2672.majU8_summable
      (fun n s hs => Series8Proof2672.term_le_majU8 Odd s
        (fun _ h => Or.inl ⟨h, hs⟩) n)
    by_cases h : Odd n
    · simp only [h, ite_true]; exact (Series8Proof2672.contOn_fn_c8 n).1 h
    · simp only [h, ite_false]; exact continuousOn_const
  · refine continuousOn_tsum (u := Series8Proof2672.majU8) (fun n => ?_)
      Series8Proof2672.majU8_summable
      (fun n s hs => Series8Proof2672.term_le_majU8 Even s
        (fun _ h => Or.inr ⟨h, hs⟩) n)
    by_cases h : Even n
    · simp only [h, ite_true]; exact (Series8Proof2672.contOn_fn_c8 n).2 h
    · simp only [h, ite_false]; exact continuousOn_const

/-- LEAF: display 16 for even n ≥ 2 differentiated and summed, BJS page 6, Nathanson
Theorem 9.4: (s f_n(s))' = - f_(n-1)(s - 1) for s > 2, summed over even n, which needs
termwise differentiation justified by the bound 18. Class MEDIUM. -/
theorem leaf8_deriv_even (s : ℝ) (hs : 2 < s) :
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
    by_cases he : Even n
    · match n, he with
      | 0, _ =>
        have h00 : ∀ x, bjsF306 0 x = 0 := fun _ => rfl
        simpa [hg, hg', h00] using (hasDerivAt_const y (0 : ℝ))
      | 1, he => exact absurd he (by decide)
      | m + 2, he =>
        simp only [hg, hg', if_pos he, show m + 2 - 1 = m + 1 by omega]
        exact Series8Proof2672.deriv_term_even_d8 m he y hy
    · simp only [hg, hg', if_neg he]
      exact hasDerivAt_const y (0 : ℝ)
  have hanchor : Summable (fun n => g n s) :=
    ((leaf8_summable.2 s hs.le).mul_left s).congr (fun n => by
      simp only [hg]
      split_ifs <;> simp)
  have hmain := hasDerivAt_tsum_of_isPreconnected Series8Proof2672.bound_summable_d8
    isOpen_Ioi isPreconnected_Ioi hderiv
    (fun n y hy => Series8Proof2672.deriv_bound_d8 n y hy)
    (show s ∈ Set.Ioi (2 : ℝ) from hs) hanchor
    (show s ∈ Set.Ioi (2 : ℝ) from hs)
  rw [hfun]
  convert hmain using 1
  have hsum : Summable (fun n => g' n s) :=
    Summable.of_norm_bounded Series8Proof2672.bound_summable_d8
      (fun n => Series8Proof2672.deriv_bound_d8 n s hs)
  rw [hsum.tsum_eq_zero_add]
  have h0 : g' 0 s = 0 := by simp [hg', bjsF306]
  rw [h0, zero_add, ← tsum_neg]
  congr 1; funext k
  simp only [hg', Nat.even_add_one, Nat.not_even_iff_odd, Nat.add_sub_cancel]
  split_ifs <;> simp

/-- LEAF: displays 15 and 16 for odd n differentiated and summed, BJS page 6, Nathanson
Theorem 9.4: s f_1(s) = 0 for s > 3 and (s f_n(s))' = - f_(n-1)(s - 1) for odd n ≥ 3
and s ≥ 3, one sided at s = 3 where display 17 takes over. Class MEDIUM. -/
theorem leaf8_deriv_odd :
    (∀ s : ℝ, 3 < s →
      HasDerivAt (fun t : ℝ => t * ∑' n : ℕ, if Odd n then bjsF306 n t else 0)
        (-(∑' n : ℕ, if Even n then bjsF306 n (s - 1) else 0)) s) ∧
    HasDerivWithinAt (fun t : ℝ => t * ∑' n : ℕ, if Odd n then bjsF306 n t else 0)
        (-(∑' n : ℕ, if Even n then bjsF306 n 2 else 0)) (Set.Ici 3) 3 := by
  have hF : ∀ t : ℝ, 3 ≤ t →
      (t * ∑' n : ℕ, if Odd n then bjsF306 n t else 0) =
        ∑' n, Series8Proof2672.gOdd_o8 n t := by
    intro t ht
    rw [← tsum_mul_left]
    congr 1; funext n
    rw [Series8Proof2672.gOdd_eq_o8 n t ht]
    split_ifs <;> simp
  have hanchor : Summable (fun n => Series8Proof2672.gOdd_o8 n 3) :=
    ((leaf8_summable.1 3 (by norm_num)).mul_left 3).congr (fun n => by
      rw [Series8Proof2672.gOdd_eq_o8 n 3 le_rfl]
      split_ifs <;> simp)
  have hd (y : ℝ) :
      HasDerivAt (fun z => ∑' n, Series8Proof2672.gOdd_o8 n z)
        (∑' n, Series8Proof2672.gOdd'_o8 n y) y :=
    hasDerivAt_tsum_of_isPreconnected Series8Proof2672.bound_summable_d8
      isOpen_univ isPreconnected_univ
      (fun n y _ => Series8Proof2672.gOdd_deriv_o8 n y)
      (fun n y _ => Series8Proof2672.gOdd_bound_o8 n y)
      (Set.mem_univ 3) hanchor (Set.mem_univ y)
  refine ⟨fun s hs => ?_, ?_⟩
  · have h := hd s
    rw [Series8Proof2672.gsum'_eq_o8 s hs.le] at h
    refine h.congr_of_eventuallyEq ?_
    filter_upwards [Ioi_mem_nhds hs] with z hz
    exact hF z (le_of_lt hz)
  · have h := (hd 3).hasDerivWithinAt (s := Set.Ici 3)
    rw [Series8Proof2672.gsum'_eq_o8 3 le_rfl, show (3 : ℝ) - 1 = 2 by norm_num] at h
    exact h.congr (fun t ht => hF t ht) (hF 3 le_rfl)

/-- LEAF: the analytic core of Nathanson Theorem 9.4 as used by BJS page 6, display 13 at
s = 3: 1 + the sum of f_n(3) over odd n equals F(3) = 2 e ^ γ / 3. With display 17 this
gives F(s) = 2 e ^ γ / s on [1, 3], proved below. Class HARD: this is where e ^ γ enters,
through the asymptotics F(s), f(s) → 1 and the adjoint function argument. -/
theorem leaf8_F3 :
    HasSum (fun n : ℕ => if Odd n then bjsF306 n 3 else 0)
      (2 * exp eulerMascheroniConstant / 3 - 1) := by
  convert (leaf8_summable.1 3 (by norm_num)).hasSum using 1
  sorry

/-- LEAF: Nathanson Theorem 9.4 as used by BJS page 6, display 14 at s = 2: the sum of
f_n(2) over even n is 1, that is f(2) = 0, the continuity of f at 2 in display 8.
Class HARD: a boundary value of the series 14, part of the analytic core with leaf8_F3. -/
theorem leaf8_f2 :
    HasSum (fun n : ℕ => if Even n then bjsF306 n 2 else 0) 1 := by
  convert (leaf8_summable.2 2 (by norm_num)).hasSum using 1
  sorry

/-- Odd n ≥ 2 is at least 3. Helper. -/
theorem three_le_of_odd_s8 (m : ℕ) (ho : Odd (m + 2)) : 3 ≤ m + 2 := by
  rcases m with _ | m
  · exact absurd ho (by decide)
  · omega

/-- Display 17 and 15: for 1 ≤ s ≤ 3 the odd terms are f_1(s) = (3 - s) / s plus
3 / s times the odd terms at s = 3 with n ≥ 3. -/
theorem odd_terms_le3_s8 (s : ℝ) (hs1 : 1 ≤ s) (hs3 : s ≤ 3) (n : ℕ) :
    (if Odd n then bjsF306 n s else 0) =
      (if n = 1 then (3 - s) / s else 0) +
        3 / s * (if Odd n ∧ 3 ≤ n then bjsF306 n 3 else 0) := by
  have hs0 : 0 < s := by linarith
  match n with
  | 0 => simp
  | 1 => simp [bjsF306, hs3]
  | m + 2 =>
    by_cases ho : Odd (m + 2)
    · rw [if_pos ho, if_neg (show m + 2 ≠ 1 by omega),
        if_pos (show Odd (m + 2) ∧ 3 ≤ m + 2 from ⟨ho, three_le_of_odd_s8 m ho⟩)]
      simp only [bjsF306, if_pos (And.intro ho hs3), if_pos (And.intro ho (le_refl (3 : ℝ)))]
      field_simp
      ring
    · rw [if_neg ho, if_neg (show m + 2 ≠ 1 by omega),
        if_neg (show ¬(Odd (m + 2) ∧ 3 ≤ m + 2) from fun h => ho h.1)]
      ring

/-- BJS display 13 on [1, 3] from leaf8_F3 and display 17: the odd series sums to
2 e ^ γ / s - 1. -/
theorem hasSum_odd_le3_s8 (s : ℝ) (hs1 : 1 ≤ s) (hs3 : s ≤ 3) :
    HasSum (fun n : ℕ => if Odd n then bjsF306 n s else 0)
      (2 * exp eulerMascheroniConstant / s - 1) := by
  have hs0 : 0 < s := by linarith
  have h3 : HasSum (fun n : ℕ => if Odd n ∧ 3 ≤ n then bjsF306 n 3 else 0)
      (2 * exp eulerMascheroniConstant / 3 - 1) := by
    convert leaf8_F3 using 1
    funext n
    match n with
    | 0 => simp
    | 1 => simp [bjsF306]
    | m + 2 =>
      by_cases ho : Odd (m + 2)
      · rw [if_pos ⟨ho, three_le_of_odd_s8 m ho⟩, if_pos ho]
      · rw [if_neg (fun h => ho h.1), if_neg ho]
  have hsum := (hasSum_ite_eq 1 ((3 - s) / s)).add (h3.mul_left (3 / s))
  convert hsum using 1
  · funext n
    rw [odd_terms_le3_s8 s hs1 hs3 n]
  · field_simp
    ring

/-- Assembly: from the sums O, E of the series 13 and 14 with the LEAF properties, the
functions F = 2 e ^ γ / s on (0, 2], 1 + O on (2, ∞) and f = 0 on (0, 2], 1 - E on
(2, ∞) solve the system 8. Proved here. -/
theorem assembly_s8 (O E : ℝ → ℝ)
    (hOs : ∀ s : ℝ, 1 ≤ s → HasSum (fun n : ℕ => if Odd n then bjsF306 n s else 0) (O s))
    (hEs : ∀ s : ℝ, 2 ≤ s → HasSum (fun n : ℕ => if Even n then bjsF306 n s else 0) (E s))
    (hO13 : ∀ s : ℝ, 1 ≤ s → s ≤ 3 → O s = 2 * exp eulerMascheroniConstant / s - 1)
    (hE2 : E 2 = 1)
    (hOc : ContinuousOn O (Set.Ici 1)) (hEc : ContinuousOn E (Set.Ici 2))
    (hdE : ∀ s : ℝ, 2 < s → HasDerivAt (fun t => t * E t) (-O (s - 1)) s)
    (hdO : ∀ s : ℝ, 3 < s → HasDerivAt (fun t => t * O t) (-E (s - 1)) s)
    (hdO3 : HasDerivWithinAt (fun t => t * O t) (-E 2) (Set.Ici 3) 3) :
    ∃ F' f' : ℝ → ℝ, LeanLab.ChenExplicit.IsLinearSieveFns F' f' ∧
      (∀ s : ℝ, 1 ≤ s → HasSum (fun n : ℕ => if Odd n then bjsF306 n s else 0) (F' s - 1)) ∧
      (∀ s : ℝ, 2 ≤ s → HasSum (fun n : ℕ => if Even n then bjsF306 n s else 0) (1 - f' s)) := by
  set c := 2 * exp eulerMascheroniConstant with hc
  set F' : ℝ → ℝ := fun s => if s ≤ 2 then c / s else 1 + O s with hF'
  set f' : ℝ → ℝ := fun s => if s ≤ 2 then 0 else 1 - E s with hf'
  have hF1 : ∀ t : ℝ, 1 ≤ t → F' t = 1 + O t := by
    intro t ht
    simp only [hF']
    split_ifs with h
    · rw [hO13 t ht (by linarith)]; ring
    · rfl
  have hF3 : ∀ t : ℝ, 0 < t → t ≤ 3 → F' t = c / t := by
    intro t ht0 ht3
    simp only [hF']
    split_ifs with h
    · rfl
    · rw [hO13 t (by linarith) ht3]; ring
  have hf2 : ∀ t : ℝ, 2 ≤ t → f' t = 1 - E t := by
    intro t ht
    simp only [hf']
    split_ifs with h
    · have : t = 2 := le_antisymm h ht
      rw [this, hE2]; ring
    · rfl
  have hf0 : ∀ t : ℝ, t ≤ 2 → f' t = 0 := by
    intro t ht; simp only [hf', if_pos ht]
  refine ⟨F', f', ⟨?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · intro s hs hs2
    exact ⟨by simp only [hF', if_pos hs2, hc], hf0 s hs2⟩
  · intro x hx
    have hx0 : (0 : ℝ) < x := hx
    apply ContinuousAt.continuousWithinAt
    by_cases hx3 : x < 3
    · have hev : (fun t => c / t) =ᶠ[nhds x] F' := by
        filter_upwards [Ioo_mem_nhds hx0 hx3] with t ht
        exact (hF3 t ht.1 ht.2.le).symm
      exact ((continuousAt_const.div continuousAt_id hx0.ne')).congr hev
    · push_neg at hx3
      have hev : (fun t => 1 + O t) =ᶠ[nhds x] F' := by
        filter_upwards [Ioi_mem_nhds (show (1 : ℝ) < x by linarith)] with t ht
        exact (hF1 t (le_of_lt ht)).symm
      have hOx : ContinuousAt O x := hOc.continuousAt (Ici_mem_nhds (by linarith))
      exact (continuousAt_const.add hOx).congr hev
  · intro x hx
    have hx0 : (0 : ℝ) < x := hx
    apply ContinuousAt.continuousWithinAt
    rcases lt_trichotomy x 2 with hx2 | hx2 | hx2
    · have hev : (fun _ => (0 : ℝ)) =ᶠ[nhds x] f' := by
        filter_upwards [Iio_mem_nhds hx2] with t ht
        exact (hf0 t (le_of_lt ht)).symm
      exact continuousAt_const.congr hev
    · subst hx2
      have h1 : ContinuousWithinAt f' (Set.Iic 2) 2 := by
        have : ContinuousWithinAt (fun _ : ℝ => (0 : ℝ)) (Set.Iic (2 : ℝ)) 2 := continuousWithinAt_const
        refine this.congr (fun t ht => hf0 t ht) (hf0 2 le_rfl)
      have h2 : ContinuousWithinAt f' (Set.Ici 2) 2 := by
        have : ContinuousWithinAt (fun t => 1 - E t) (Set.Ici 2) 2 :=
          continuousWithinAt_const.sub (hEc 2 Set.self_mem_Ici)
        refine this.congr (fun t ht => hf2 t ht) (hf2 2 le_rfl)
      have := h1.union h2
      rw [Set.Iic_union_Ici, continuousWithinAt_univ] at this
      exact this
    · have hev : (fun t => 1 - E t) =ᶠ[nhds x] f' := by
        filter_upwards [Ioi_mem_nhds hx2] with t ht
        exact (hf2 t (le_of_lt ht)).symm
      have hEx : ContinuousAt E x := hEc.continuousAt (Ici_mem_nhds hx2)
      exact (continuousAt_const.sub hEx).congr hev
  · intro s hs
    constructor
    · -- (s F(s))' = f(s - 1)
      rcases lt_trichotomy s 3 with hs3 | hs3 | hs3
      · have hev : (fun _ : ℝ => c) =ᶠ[nhds s] (fun t => t * F' t) := by
          filter_upwards [Ioo_mem_nhds (show (0 : ℝ) < s by linarith) hs3] with t ht
          rw [hF3 t ht.1 ht.2.le]; field_simp [ht.1.ne']
        rw [hf0 (s - 1) (by linarith)]
        exact (hasDerivAt_const s c).congr_of_eventuallyEq hev.symm
      · subst hs3
        rw [show (3 : ℝ) - 1 = 2 by norm_num, hf0 2 le_rfl]
        have h1 : HasDerivWithinAt (fun t => t * F' t) 0 (Set.Iic 3) 3 := by
          have hc0 : HasDerivWithinAt (fun _ : ℝ => c) 0 (Set.Iic (3 : ℝ)) 3 := hasDerivWithinAt_const _ _ _
          refine hc0.congr_of_eventuallyEq ?_ ?_
          · filter_upwards [inter_mem_nhdsWithin (Set.Iic (3 : ℝ))
              (Ioi_mem_nhds (show (0 : ℝ) < 3 by norm_num))] with t ht
            rw [hF3 t ht.2 ht.1]; field_simp [(show (0 : ℝ) < t from ht.2).ne']
          · rw [hF3 3 (by norm_num) le_rfl]; field_simp
        have h2 : HasDerivWithinAt (fun t => t * F' t) 0 (Set.Ici 3) 3 := by
          have hh := (hasDerivWithinAt_id (3 : ℝ) (Set.Ici 3)).add hdO3
          rw [hE2] at hh
          norm_num at hh
          refine hh.congr_of_eventuallyEq ?_ ?_
          · filter_upwards [self_mem_nhdsWithin] with t ht
            have ht' : (3 : ℝ) ≤ t := ht
            show t * F' t = id t + t * O t
            rw [hF1 t (by linarith)]; simp only [id]; ring
          · show (3 : ℝ) * F' 3 = id 3 + 3 * O 3
            rw [hF1 3 (by norm_num)]; simp only [id]; ring
        have := h1.union h2
        rw [Set.Iic_union_Ici, hasDerivWithinAt_univ] at this
        exact this
      · have hev : (fun t => t + t * O t) =ᶠ[nhds s] (fun t => t * F' t) := by
          filter_upwards [Ioi_mem_nhds (show (1 : ℝ) < s by linarith)] with t ht
          rw [hF1 t ht.le]; ring
        rw [hf2 (s - 1) (by linarith)]
        have hh := (hasDerivAt_id s).add (hdO s hs3)
        rw [show (1 : ℝ) + -E (s - 1) = 1 - E (s - 1) by ring] at hh
        exact hh.congr_of_eventuallyEq hev.symm
    · -- (s f(s))' = F(s - 1)
      have hev : (fun t => t - t * E t) =ᶠ[nhds s] (fun t => t * f' t) := by
        filter_upwards [Ioi_mem_nhds hs] with t ht
        rw [hf2 t ht.le]; ring
      rw [hF1 (s - 1) (by linarith)]
      have hh := (hasDerivAt_id s).sub (hdE s hs)
      rw [show (1 : ℝ) - -O (s - 1) = 1 + O (s - 1) by ring] at hh
      exact hh.congr_of_eventuallyEq hev.symm
  · intro s hs
    rw [hF1 s hs, add_sub_cancel_left]
    exact hOs s hs
  · intro s hs
    rw [hf2 s hs, sub_sub_cancel]
    exact hEs s hs

/-- Twin of leaf306_series_solve8, Nathanson Theorem 9.4 existence half, BJS page 6,
displays 8, 13 and 14, proved from the LEAF lemmas above by assembly_s8. -/
theorem leaf306_series_solve8_twin :
    ∃ F' f' : ℝ → ℝ, LeanLab.ChenExplicit.IsLinearSieveFns F' f' ∧
      (∀ s : ℝ, 1 ≤ s → HasSum (fun n : ℕ => if Odd n then bjsF306 n s else 0) (F' s - 1)) ∧
      (∀ s : ℝ, 2 ≤ s → HasSum (fun n : ℕ => if Even n then bjsF306 n s else 0) (1 - f' s)) := by
  refine assembly_s8 (fun s => ∑' n : ℕ, if Odd n then bjsF306 n s else 0)
    (fun s => ∑' n : ℕ, if Even n then bjsF306 n s else 0)
    (fun s hs => (leaf8_summable.1 s hs).hasSum) (fun s hs => (leaf8_summable.2 s hs).hasSum)
    (fun s hs1 hs3 => (hasSum_odd_le3_s8 s hs1 hs3).tsum_eq) leaf8_f2.tsum_eq
    leaf8_continuous.1 leaf8_continuous.2 leaf8_deriv_even leaf8_deriv_odd.1 ?_
  have h := leaf8_deriv_odd.2
  simpa [show (3 : ℝ) - 1 = 2 by norm_num] using h

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.leaf306_series_solve8_twin

#print axioms LeanLab.Cai2002.leaf8_summable
#print axioms LeanLab.Cai2002.leaf8_continuous
#print axioms LeanLab.Cai2002.leaf8_deriv_even
#print axioms LeanLab.Cai2002.leaf8_deriv_odd
