/-
First derivative saving for the case `S = {1}` of Karacuba's Theorem 1, used to prove the two
leaves `leaf_s1_saving_sign_pos` and `leaf_s1_saving_sign_neg` of
`LeanLab.ExceptionalSet.SPLIT_leaf_s1_monotone_saving`.

The hypotheses give `N ^ (-θ) ≤ f' ≤ N ^ (-Θ)` and `|f^(k) / k!| ≤ N ^ (-Θ₀ k)` with
`θ < Θ₀`, but no monotonicity of `f'`, so the Kusmin Landau inequality is applied to the
Taylor polynomial of `f` on blocks of length about `N ^ ((θ + Θ₀) / 2)`:

* `taylor_poly_approx`: Taylor polynomial with the Lagrange bounds for `f` and `f'`.
* `poly_deriv_mono_of_no_root`, `poly_phase_run`, `piecewise_sum_bound`, `poly_phase_block`:
  the derivative of a polynomial of degree below `k` is monotone or antitone between the at
  most `k - 3` roots of its second derivative, and on each such run the lab theorem
  `kusmin_landau` of `LeanLab.BakerHarmanPintz1997.PortedVanDerCorput` applies.
* `s1_block`, `block_sum_bound`, `s1_saving_core`: the block bound for `f`, the cut into
  blocks, and the exponent bookkeeping, with the saving `(Θ₀ - θ) / 2`.

All steps are standard mathematics.  No new definitions.  AI wrote the Lean code, Claude.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.BakerHarmanPintz1997.PortedVanDerCorput

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit.S1Saving

open LeanLab.BakerHarmanPintz1997.PortedVanDerCorput

/-! ### A. Taylor polynomial with Lagrange remainder -/

private theorem a_core {U : Set ℝ} (hU : IsOpen U) {a b : ℝ} (hsub : Set.Icc a b ⊆ U) (C : ℝ) :
    ∀ (m : ℕ) (g : ℝ → ℝ), ContDiffOn ℝ m g U → (∀ j < m, iteratedDeriv j g a = 0) →
      (∀ x ∈ Set.Icc a b, |iteratedDeriv m g x| ≤ C) →
      ∀ x ∈ Set.Icc a b, |g x| ≤ C * (x - a) ^ m / m.factorial := by
  intro m
  induction m with
  | zero =>
    intro g _ _ hb x hx
    have := hb x hx
    simpa using this
  | succ m ih =>
    intro g hg h0 hb
    have hg' : ContDiffOn ℝ m (deriv g) U := hg.deriv_of_isOpen hU (by exact_mod_cast le_rfl)
    have ih' := ih (deriv g) hg'
      (fun j hj => by rw [← iteratedDeriv_succ']; exact h0 (j + 1) (by omega))
      (fun x hx => by rw [← iteratedDeriv_succ']; exact hb x hx)
    have hga : g a = 0 := by simpa using h0 0 (Nat.succ_pos m)
    have hdiff : ∀ x ∈ U, DifferentiableAt ℝ g x := fun x hx =>
      (hg.differentiableOn (by simp)).differentiableAt (hU.mem_nhds hx)
    intro x hx
    have key := image_norm_le_of_norm_deriv_right_le_deriv_boundary (f := g) (f' := deriv g)
      (a := a) (b := b) (B := fun y => C * (y - a) ^ (m + 1) / (m + 1).factorial)
      (B' := fun y => C * (y - a) ^ m / m.factorial)
      (fun y hy => (hdiff y (hsub hy)).continuousAt.continuousWithinAt)
      (fun y hy => (hdiff y (hsub (Set.Ico_subset_Icc_self hy))).hasDerivAt.hasDerivWithinAt)
      (by simp [hga])
      (by
        intro y
        have h1 : HasDerivAt (fun y : ℝ => (y - a) ^ (m + 1)) (((m + 1 : ℕ) : ℝ) * (y - a) ^ m) y := by
          have := ((hasDerivAt_id' y).sub_const a).fun_pow (m + 1)
          simpa using this
        have h2 := (h1.const_mul C).div_const ((m + 1).factorial : ℝ)
        convert h2 using 1
        rw [Nat.factorial_succ]
        have hf : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
        have hm : ((m : ℝ) + 1) ≠ 0 := by positivity
        push_cast
        field_simp)
      (fun y hy => by rw [Real.norm_eq_abs]; exact ih' y (Set.Ico_subset_Icc_self hy)) hx
    simpa [Real.norm_eq_abs] using key

private theorem a_iterDeriv_poly (Q : Polynomial ℝ) (j : ℕ) :
    iteratedDeriv j (fun x => Q.eval x) = fun x => (Polynomial.derivative^[j] Q).eval x := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [iteratedDeriv_succ, ih, Function.iterate_succ_apply']
    funext x
    exact Polynomial.deriv _

/-- A. Taylor polynomial with Lagrange bounds for f and f'. -/
theorem taylor_poly_approx {f : ℝ → ℝ} {k : ℕ} (hk : 1 ≤ k) {U : Set ℝ} (hU : IsOpen U)
    {a b : ℝ} (hab : a ≤ b) (hsub : Set.Icc a b ⊆ U) (hf : ContDiffOn ℝ k f U) {M : ℝ}
    (hM : ∀ x ∈ Set.Icc a b, |iteratedDeriv k f x / k.factorial| ≤ M) :
    ∃ P : Polynomial ℝ, P.natDegree < k ∧
      (∀ x ∈ Set.Icc a b, |f x - P.eval x| ≤ M * (x - a) ^ k) ∧
      (∀ x ∈ Set.Icc a b, |deriv f x - P.derivative.eval x| ≤ k * M * (x - a) ^ (k - 1)) := by
  classical
  set Q : Polynomial ℝ := ∑ j ∈ Finset.range k,
    Polynomial.monomial j (iteratedDeriv j f a / j.factorial) with hQ
  have hQdeg : Q.natDegree < k := by
    have : Q.natDegree ≤ k - 1 :=
      Polynomial.natDegree_sum_le_of_forall_le _ _ (fun i hi =>
        (Polynomial.natDegree_monomial_le _).trans (by have := Finset.mem_range.mp hi; omega))
    omega
  have hQc : ∀ j < k, Q.coeff j = iteratedDeriv j f a / j.factorial := by
    intro j hj
    rw [hQ, Polynomial.finsetSum_coeff]
    simp only [Polynomial.coeff_monomial]
    rw [Finset.sum_ite_eq' (Finset.range k) j]
    simp [hj]
  set P : Polynomial ℝ := Q.comp (Polynomial.X - Polynomial.C a) with hP
  have hPe : ∀ x, P.eval x = Q.eval (x - a) := by
    intro x; simp [hP, Polynomial.eval_comp]
  have hPdeg : P.natDegree < k := by
    rw [hP, Polynomial.natDegree_comp, Polynomial.natDegree_X_sub_C, mul_one]; exact hQdeg
  set p : ℝ → ℝ := fun x => P.eval x with hp_def
  have hp : ∀ n : WithTop ℕ∞, ContDiff ℝ n p := fun n => by
    have h := Polynomial.contDiff_aeval (𝕜 := ℝ) P n
    simpa [hp_def] using h
  have hpj : ∀ j x, iteratedDeriv j p x = (Polynomial.derivative^[j] Q).eval (x - a) := by
    intro j x
    have h1 : p = fun z => (fun y => Q.eval y) (z - a) := by funext z; exact hPe z
    have h2 := iteratedDeriv_comp_sub_const (n := j) (f := fun y => Q.eval y) (s := a)
    rw [a_iterDeriv_poly] at h2
    rw [h1]; exact congrFun h2 x
  have hpa : ∀ j < k, iteratedDeriv j p a = iteratedDeriv j f a := by
    intro j hj
    rw [hpj, sub_self, ← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_iterate_derivative,
      zero_add, Nat.descFactorial_self, hQc j hj, nsmul_eq_mul]
    have : (j.factorial : ℝ) ≠ 0 := by exact_mod_cast j.factorial_ne_zero
    field_simp
  have hpk : ∀ x, iteratedDeriv k p x = 0 := by
    intro x
    rw [hpj, Polynomial.iterate_derivative_eq_zero hQdeg, Polynomial.eval_zero]
  have hh : ContDiffOn ℝ k (f - p) U := hf.sub (hp k).contDiffOn
  have hhj : ∀ j ≤ k, ∀ x ∈ U,
      iteratedDeriv j (f - p) x = iteratedDeriv j f x - iteratedDeriv j p x := by
    intro j hj x hx
    exact iteratedDeriv_sub ((hf.contDiffAt (hU.mem_nhds hx)).of_le (by exact_mod_cast hj))
      (hp j).contDiffAt
  have haU : a ∈ U := hsub ⟨le_rfl, hab⟩
  have hkf : (0 : ℝ) < k.factorial := by exact_mod_cast k.factorial_pos
  have hbound : ∀ x ∈ Set.Icc a b, |iteratedDeriv k (f - p) x| ≤ M * k.factorial := by
    intro x hx
    rw [hhj k le_rfl x (hsub hx), hpk, sub_zero]
    have := hM x hx
    rwa [abs_div, abs_of_pos hkf, div_le_iff₀ hkf] at this
  have hzero : ∀ j < k, iteratedDeriv j (f - p) a = 0 := by
    intro j hj
    rw [hhj j hj.le a haU, hpa j hj, sub_self]
  refine ⟨P, hPdeg, ?_, ?_⟩
  · intro x hx
    have h1 := a_core hU hsub (M * k.factorial) k (f - p) hh hzero hbound x hx
    have h2 : M * k.factorial * (x - a) ^ k / k.factorial = M * (x - a) ^ k := by
      field_simp
    rw [h2] at h1
    exact h1
  · obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
    intro x hx
    have h1 := a_core hU hsub (M * (m + 1).factorial) m (deriv (f - p))
      (hh.deriv_of_isOpen hU (by exact_mod_cast le_rfl))
      (fun j hj => by rw [← iteratedDeriv_succ']; exact hzero (j + 1) (by omega))
      (fun y hy => by rw [← iteratedDeriv_succ']; exact hbound y hy) x hx
    have hfd : DifferentiableAt ℝ f x :=
      (hf.differentiableOn (by simp)).differentiableAt (hU.mem_nhds (hsub hx))
    have hpd : DifferentiableAt ℝ p x := P.differentiableAt
    have h3 : deriv (f - p) x = deriv f x - P.derivative.eval x := by
      rw [deriv_sub hfd hpd]
      congr 1
      exact Polynomial.deriv _
    rw [h3] at h1
    have h2 : M * (m + 1).factorial * (x - a) ^ m / m.factorial
        = ((m + 1 : ℕ) : ℝ) * M * (x - a) ^ (m + 1 - 1) := by
      have hm : (m.factorial : ℝ) ≠ 0 := by exact_mod_cast m.factorial_ne_zero
      rw [Nat.factorial_succ, Nat.add_sub_cancel]
      push_cast
      field_simp
    rw [h2] at h1
    exact h1

/-! ### B1. Kusmin Landau on one monotone run -/

private theorem b1_mvt (P : Polynomial ℝ) (x : ℝ) :
    ∃ ξ ∈ Set.Ioo x (x + 1), P.eval (x + 1) - P.eval x = P.derivative.eval ξ := by
  have hlt : x < x + 1 := by linarith
  obtain ⟨c, hc, hd⟩ := exists_deriv_eq_slope (fun y => P.eval y) hlt
    P.continuous.continuousOn P.differentiable.differentiableOn
  refine ⟨c, hc, ?_⟩
  rw [Polynomial.deriv] at hd
  rw [hd]
  have : x + 1 - x = 1 := by ring
  rw [this, div_one]

private theorem b1_diff (P : Polynomial ℝ) {u v : ℕ}
    (n : ℕ) (hun : u < n) (hnv : n ≤ v) :
    ∃ ξ ∈ Set.Icc (u : ℝ) ((v : ℝ) + 1), (n : ℝ) < ξ ∧ ξ < (n : ℝ) + 1 ∧
      P.eval (((n + 1 : ℕ) : ℝ)) - P.eval (n : ℝ) = P.derivative.eval ξ := by
  obtain ⟨ξ, hξ, h⟩ := b1_mvt P (n : ℝ)
  have h1 : (u : ℝ) < n := by exact_mod_cast hun
  have h2 : (n : ℝ) ≤ v := by exact_mod_cast hnv
  refine ⟨ξ, ⟨by linarith [hξ.1], by linarith [hξ.2]⟩, hξ.1, hξ.2, ?_⟩
  rw [← h]; push_cast; rfl

/-- B1. Kusmin Landau on one run where P' is monotone or antitone. -/
theorem poly_phase_run (P : Polynomial ℝ) {u v : ℕ} (huv : u ≤ v) {lam : ℝ} (hlam0 : 0 < lam)
    (hP : ∀ x ∈ Set.Icc (u : ℝ) ((v : ℝ) + 1),
      lam ≤ P.derivative.eval x ∧ P.derivative.eval x ≤ 1 / 2)
    (hmono : MonotoneOn (fun x => P.derivative.eval x) (Set.Icc (u : ℝ) ((v : ℝ) + 1)) ∨
      AntitoneOn (fun x => P.derivative.eval x) (Set.Icc (u : ℝ) ((v : ℝ) + 1))) :
    ‖∑ n ∈ Finset.Ioc u v, eK (P.eval (n : ℝ))‖ ≤ 1 / lam := by
  have huv' : (u : ℝ) ≤ v := by exact_mod_cast huv
  have hlam : lam ≤ 1 / 2 := by
    have := hP (u : ℝ) ⟨le_refl _, by linarith⟩
    linarith [this.1, this.2]
  rcases hmono with hm | hm
  · refine kusmin_landau (f := fun n : ℕ => P.eval (n : ℝ)) (m := 0) hlam0 hlam ?_ ?_ ?_
    · intro n hun hnv
      obtain ⟨ξ, hξ, -, -, h⟩ := b1_diff P n hun hnv
      show ((0 : ℤ) : ℝ) + lam ≤ P.eval (((n + 1 : ℕ) : ℝ)) - P.eval (n : ℝ)
      rw [h]; simp only [Int.cast_zero, zero_add]; exact (hP ξ hξ).1
    · intro n hun hnv
      obtain ⟨ξ, hξ, -, -, h⟩ := b1_diff P n hun hnv
      show P.eval (((n + 1 : ℕ) : ℝ)) - P.eval (n : ℝ) ≤ ((0 : ℤ) : ℝ) + 1 - lam
      rw [h]; simp only [Int.cast_zero, zero_add]; linarith [(hP ξ hξ).2]
    · intro n hun hnv
      obtain ⟨ξ1, hξ1, -, h1b, h1⟩ := b1_diff P n hun hnv.le
      obtain ⟨ξ2, hξ2, h2a, -, h2⟩ := b1_diff (u := u) (v := v) P (n + 1) (by omega) (by omega)
      show P.eval (((n + 1 : ℕ) : ℝ)) - P.eval (n : ℝ)
        ≤ P.eval (((n + 1 + 1 : ℕ) : ℝ)) - P.eval (((n + 1 : ℕ) : ℝ))
      rw [h1, h2]
      have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; rfl
      exact hm hξ1 hξ2 (by rw [hc] at h2a; linarith)
  · have key : ‖∑ n ∈ Finset.Ioc u v, eK (-(P.eval (n : ℝ)))‖ ≤ 1 / lam := by
      refine kusmin_landau (f := fun n : ℕ => -(P.eval (n : ℝ))) (m := -1) hlam0 hlam ?_ ?_ ?_
      · intro n hun hnv
        obtain ⟨ξ, hξ, -, -, h⟩ := b1_diff P n hun hnv
        show ((-1 : ℤ) : ℝ) + lam ≤ -P.eval (((n + 1 : ℕ) : ℝ)) - -P.eval (n : ℝ)
        have := (hP ξ hξ).2
        push_cast at h ⊢
        linarith
      · intro n hun hnv
        obtain ⟨ξ, hξ, -, -, h⟩ := b1_diff P n hun hnv
        show -P.eval (((n + 1 : ℕ) : ℝ)) - -P.eval (n : ℝ) ≤ ((-1 : ℤ) : ℝ) + 1 - lam
        have := (hP ξ hξ).1
        push_cast at h ⊢
        linarith
      · intro n hun hnv
        obtain ⟨ξ1, hξ1, -, h1b, h1⟩ := b1_diff P n hun hnv.le
        obtain ⟨ξ2, hξ2, h2a, -, h2⟩ := b1_diff (u := u) (v := v) P (n + 1) (by omega) (by omega)
        show -P.eval (((n + 1 : ℕ) : ℝ)) - -P.eval (n : ℝ)
          ≤ -P.eval (((n + 1 + 1 : ℕ) : ℝ)) - -P.eval (((n + 1 : ℕ) : ℝ))
        have hc : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by push_cast; rfl
        have := hm hξ1 hξ2 (by rw [hc] at h2a; linarith)
        simp only at this
        linarith
    have heq : ∑ n ∈ Finset.Ioc u v, eK (-(P.eval (n : ℝ)))
        = (starRingEnd ℂ) (∑ n ∈ Finset.Ioc u v, eK (P.eval (n : ℝ))) := by
      rw [map_sum]; exact Finset.sum_congr rfl (fun n _ => eK_neg _)
    rw [heq, RCLike.norm_conj] at key
    exact key

/-! ### B2. Cutting at finitely many bad points -/

private theorem b2_gen (F : ℕ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 1) (S : Finset ℝ) (A : ℝ) (hA : 0 ≤ A) :
    ∀ c : ℕ, ∀ a b : ℕ, a ≤ b →
      (S.filter (fun s => (a:ℝ) < s ∧ s < (b:ℝ)+1)).card = c →
      (∀ u v : ℕ, a ≤ u → u ≤ v → v ≤ b →
        (∀ s ∈ S, s ∉ Set.Ioo (u : ℝ) ((v : ℝ) + 1)) → ‖∑ n ∈ Finset.Ioc u v, F n‖ ≤ A) →
      ‖∑ n ∈ Finset.Ioc a b, F n‖ ≤ ((c : ℝ) + 1) * A + 2 * (c : ℝ) := by
  intro c
  induction c using Nat.strong_induction_on with
  | _ c ih =>
  intro a b hab hc h
  have hc0 : (0:ℝ) ≤ c := Nat.cast_nonneg c
  by_cases hemp : S.filter (fun s => (a:ℝ) < s ∧ s < (b:ℝ)+1) = ∅
  · have h1 := h a b le_rfl hab le_rfl (by
      intro s hs hmem
      have : s ∈ S.filter (fun s => (a:ℝ) < s ∧ s < (b:ℝ)+1) :=
        Finset.mem_filter.mpr ⟨hs, hmem.1, hmem.2⟩
      rw [hemp] at this
      exact absurd this (Finset.notMem_empty _))
    nlinarith [mul_nonneg hc0 hA]
  · obtain ⟨s, hs⟩ := Finset.nonempty_iff_ne_empty.mpr hemp
    rw [Finset.mem_filter] at hs
    obtain ⟨hsS, has, hsb⟩ := hs
    have hs0 : (0:ℝ) ≤ s := le_trans (Nat.cast_nonneg a) has.le
    obtain ⟨n0, hn0⟩ : ∃ n0 : ℕ, n0 = ⌊s⌋₊ := ⟨_, rfl⟩
    have hn0s : (n0:ℝ) ≤ s := by rw [hn0]; exact Nat.floor_le hs0
    have hsn0 : s < (n0:ℝ) + 1 := by rw [hn0]; exact Nat.lt_floor_add_one s
    have han0 : a ≤ n0 := by rw [hn0]; exact Nat.le_floor has.le
    have hn0b : n0 ≤ b := by
      have h1 : (n0:ℝ) < (b:ℝ) + 1 := lt_of_le_of_lt hn0s hsb
      have h2 : n0 < b + 1 := by exact_mod_cast h1
      omega
    have han0R : (a:ℝ) ≤ n0 := by exact_mod_cast han0
    have hn0bR : (n0:ℝ) ≤ b := by exact_mod_cast hn0b
    obtain ⟨TL, hTL⟩ : ∃ T, T = S.filter (fun t => (a:ℝ) < t ∧ t < (n0:ℝ)) := ⟨_, rfl⟩
    obtain ⟨TR, hTR⟩ : ∃ T, T = S.filter (fun t => ((n0:ℝ)+1) < t ∧ t < (b:ℝ)+1) := ⟨_, rfl⟩
    have hTLm : ∀ t, t ∈ TL ↔ t ∈ S ∧ (a:ℝ) < t ∧ t < (n0:ℝ) := by
      intro t; rw [hTL, Finset.mem_filter]
    have hTRm : ∀ t, t ∈ TR ↔ t ∈ S ∧ ((n0:ℝ)+1) < t ∧ t < (b:ℝ)+1 := by
      intro t; rw [hTR, Finset.mem_filter]
    have hdisj : Disjoint TL TR := by
      rw [Finset.disjoint_left]
      intro t h1 h2
      have h3 := ((hTLm t).mp h1).2.2
      have h4 := ((hTRm t).mp h2).2.1
      linarith
    have hcard : TL.card + TR.card < c := by
      rw [← hc, ← Finset.card_union_of_disjoint hdisj]
      apply Finset.card_lt_card
      rw [Finset.ssubset_iff_of_subset]
      · refine ⟨s, Finset.mem_filter.mpr ⟨hsS, has, hsb⟩, ?_⟩
        intro hmem
        rcases Finset.mem_union.mp hmem with h1 | h1
        · have h3 := ((hTLm s).mp h1).2.2; linarith
        · have h3 := ((hTRm s).mp h1).2.1; linarith
      · intro t ht
        rcases Finset.mem_union.mp ht with h1 | h1
        · obtain ⟨h2, h3, h4⟩ := (hTLm t).mp h1
          exact Finset.mem_filter.mpr ⟨h2, h3, by linarith⟩
        · obtain ⟨h2, h3, h4⟩ := (hTRm t).mp h1
          exact Finset.mem_filter.mpr ⟨h2, by linarith, h4⟩
    have hcL0 : (0:ℝ) ≤ TL.card := Nat.cast_nonneg _
    have hcR0 : (0:ℝ) ≤ TR.card := Nat.cast_nonneg _
    have hL : ‖∑ n ∈ Finset.Ioc a n0, F n‖ ≤ ((TL.card:ℝ)+1)*A + 2*(TL.card:ℝ) + 1 := by
      rcases Nat.eq_or_lt_of_le han0 with heq | hlt
      · rw [← heq, Finset.Ioc_self, Finset.sum_empty, norm_zero]
        nlinarith [mul_nonneg hcL0 hA]
      · obtain ⟨m, hm⟩ : ∃ m, n0 = m+1 := ⟨n0-1, by omega⟩
        have ham : a ≤ m := by omega
        have hceq : (S.filter (fun s => (a:ℝ) < s ∧ s < (m:ℝ)+1)).card = TL.card := by
          rw [hTL, hm]
          congr 1
          apply Finset.filter_congr
          intro t _
          simp only [Nat.cast_add, Nat.cast_one]
        have ihL := ih TL.card (by omega) a m ham hceq
          (fun u v hu huv hv hS => h u v hu huv (by omega) hS)
        rw [hm, Finset.sum_Ioc_succ_top ham]
        have h1 := norm_add_le (∑ n ∈ Finset.Ioc a m, F n) (F (m+1))
        linarith [hF (m+1)]
    have hR : ‖∑ n ∈ Finset.Ioc n0 b, F n‖ ≤ ((TR.card:ℝ)+1)*A + 2*(TR.card:ℝ) + 1 := by
      rcases Nat.eq_or_lt_of_le hn0b with heq | hlt
      · rw [heq, Finset.Ioc_self, Finset.sum_empty, norm_zero]
        nlinarith [mul_nonneg hcR0 hA]
      · have hlt' : n0 + 1 ≤ b := hlt
        have hceq : (S.filter (fun s => ((n0+1:ℕ):ℝ) < s ∧ s < (b:ℝ)+1)).card = TR.card := by
          rw [hTR]
          congr 1
          apply Finset.filter_congr
          intro t _
          simp only [Nat.cast_add, Nat.cast_one]
        have ihR := ih TR.card (by omega) (n0+1) b hlt' hceq
          (fun u v hu huv hv hS => h u v (by omega) huv hv hS)
        rw [← Finset.sum_Ioc_consecutive F (Nat.le_succ n0) hlt', Nat.Ioc_succ_singleton,
          Finset.sum_singleton]
        have h1 := norm_add_le (F (n0+1)) (∑ n ∈ Finset.Ioc (n0+1) b, F n)
        linarith [hF (n0+1)]
    rw [← Finset.sum_Ioc_consecutive F han0 hn0b]
    have h1 := norm_add_le (∑ n ∈ Finset.Ioc a n0, F n) (∑ n ∈ Finset.Ioc n0 b, F n)
    have hcR : (TL.card:ℝ) + (TR.card:ℝ) + 1 ≤ c := by
      have : TL.card + TR.card + 1 ≤ c := hcard
      exact_mod_cast this
    nlinarith [mul_nonneg (sub_nonneg.mpr hcR) hA]

/-- B2. Cutting an integer interval at finitely many real bad points. -/
theorem piecewise_sum_bound (F : ℕ → ℂ) (hF : ∀ n, ‖F n‖ ≤ 1) (S : Finset ℝ) (A : ℝ)
    (hA : 0 ≤ A) (a b : ℕ) (hab : a ≤ b)
    (h : ∀ u v : ℕ, a ≤ u → u ≤ v → v ≤ b →
      (∀ s ∈ S, s ∉ Set.Ioo (u : ℝ) ((v : ℝ) + 1)) → ‖∑ n ∈ Finset.Ioc u v, F n‖ ≤ A) :
    ‖∑ n ∈ Finset.Ioc a b, F n‖ ≤ ((S.card : ℝ) + 1) * A + 2 * (S.card : ℝ) := by
  have h1 := b2_gen F hF S A hA _ a b hab rfl h
  have h2 : ((S.filter (fun s => (a:ℝ) < s ∧ s < (b:ℝ)+1)).card : ℝ) ≤ S.card := by
    exact_mod_cast Finset.card_filter_le S _
  nlinarith [mul_nonneg (sub_nonneg.mpr h2) hA]

/-! ### B3 and D. Sign of the second derivative, and blocks -/

/-- Sign dichotomy for a polynomial without roots in an open interval. -/
private theorem b3d_sign (Q : Polynomial ℝ) {u w : ℝ}
    (h : ∀ s ∈ Q.roots.toFinset, s ∉ Set.Ioo u w) :
    (∀ x ∈ Set.Ioo u w, 0 ≤ Q.eval x) ∨ (∀ x ∈ Set.Ioo u w, Q.eval x ≤ 0) := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hc1, hc2⟩ := hcon
  push Not at hc1 hc2
  obtain ⟨x, hx, hxneg⟩ := hc1
  obtain ⟨y, hy, hypos⟩ := hc2
  have hQ : Q ≠ 0 := by
    intro h0
    rw [h0, Polynomial.eval_zero] at hxneg
    exact lt_irrefl _ hxneg
  have hcont : ContinuousOn (fun t => Q.eval t) (Set.uIcc x y) :=
    Q.continuous.continuousOn
  have hmem : (0 : ℝ) ∈ Set.uIcc (Q.eval x) (Q.eval y) := by
    rw [Set.mem_uIcc]
    left
    exact ⟨hxneg.le, hypos.le⟩
  obtain ⟨z, hz, hz0⟩ := intermediate_value_uIcc hcont hmem
  have hzI : z ∈ Set.Ioo u w := by
    rw [Set.mem_uIcc] at hz
    rcases hz with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨lt_of_lt_of_le hx.1 h1, lt_of_le_of_lt h2 hy.2⟩
    · exact ⟨lt_of_lt_of_le hy.1 h1, lt_of_le_of_lt h2 hx.2⟩
  have hroot : z ∈ Q.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hQ]
    exact hz0
  exact h z hroot hzI

/-- B3. With no root of P'' inside, P' is monotone or antitone. -/
theorem poly_deriv_mono_of_no_root (P : Polynomial ℝ) {u w : ℝ} (huw : u ≤ w)
    (h : ∀ s ∈ P.derivative.derivative.roots.toFinset, s ∉ Set.Ioo u w) :
    MonotoneOn (fun x => P.derivative.eval x) (Set.Icc u w) ∨
      AntitoneOn (fun x => P.derivative.eval x) (Set.Icc u w) := by
  have hcont : ContinuousOn (fun x => P.derivative.eval x) (Set.Icc u w) :=
    P.derivative.continuous.continuousOn
  have hdiff : DifferentiableOn ℝ (fun x => P.derivative.eval x) (interior (Set.Icc u w)) :=
    P.derivative.differentiable.differentiableOn
  have hderiv : ∀ x : ℝ, deriv (fun x => P.derivative.eval x) x
      = P.derivative.derivative.eval x := fun x => Polynomial.deriv _
  rcases b3d_sign P.derivative.derivative h with hs | hs
  · left
    refine monotoneOn_of_deriv_nonneg (convex_Icc u w) hcont hdiff ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [hderiv x]
    exact hs x hx
  · right
    refine antitoneOn_of_deriv_nonpos (convex_Icc u w) hcont hdiff ?_
    intro x hx
    rw [interior_Icc] at hx
    rw [hderiv x]
    exact hs x hx

private theorem b3d_block_aux (F : ℕ → ℂ) (L : ℕ) (hL : 0 < L) (A : ℝ) (hA : 0 ≤ A) (b : ℕ) :
    ∀ n a : ℕ, a ≤ b → b - a = n →
      (∀ u v : ℕ, a ≤ u → u ≤ v → v ≤ b → v - u ≤ L → ‖∑ n ∈ Finset.Ioc u v, F n‖ ≤ A) →
      ‖∑ n ∈ Finset.Ioc a b, F n‖ ≤ ((n : ℝ) / L + 1) * A := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro a hab hn h
    have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
    by_cases hle : b - a ≤ L
    · have h1 := h a b le_rfl hab le_rfl hle
      have h2 : (0 : ℝ) ≤ (n : ℝ) / L := div_nonneg (Nat.cast_nonneg n) hLpos.le
      have h3 : (0 : ℝ) ≤ (n : ℝ) / L * A := mul_nonneg h2 hA
      linarith
    · have hlt : L < b - a := Nat.lt_of_not_le hle
      have haL : a + L ≤ b := by omega
      have hsplit := Finset.sum_Ioc_consecutive F (Nat.le_add_right a L) haL
      have h1 : ‖∑ i ∈ Finset.Ioc a (a + L), F i‖ ≤ A :=
        h a (a + L) le_rfl (Nat.le_add_right a L) haL (by omega)
      have hnL : L ≤ n := by omega
      have h2 : ‖∑ i ∈ Finset.Ioc (a + L) b, F i‖ ≤ (((n - L : ℕ) : ℝ) / L + 1) * A := by
        refine ih (n - L) (by omega) (a + L) haL (by omega) ?_
        intro u v hu huv hv hvu
        exact h u v (by omega) huv hv hvu
      rw [Nat.cast_sub hnL] at h2
      have h3 : (((n : ℝ) - (L : ℝ)) / L + 1) * A + A = ((n : ℝ) / L + 1) * A := by
        field_simp
        ring
      calc ‖∑ i ∈ Finset.Ioc a b, F i‖
          = ‖∑ i ∈ Finset.Ioc a (a + L), F i + ∑ i ∈ Finset.Ioc (a + L) b, F i‖ := by
            rw [hsplit]
        _ ≤ ‖∑ i ∈ Finset.Ioc a (a + L), F i‖ + ‖∑ i ∈ Finset.Ioc (a + L) b, F i‖ :=
            norm_add_le _ _
        _ ≤ ((n : ℝ) / L + 1) * A := by linarith

/-- D. Cutting an integer interval into blocks of length at most L. -/
theorem block_sum_bound (F : ℕ → ℂ) (L : ℕ) (hL : 0 < L) (A : ℝ) (hA : 0 ≤ A) (a b : ℕ)
    (hab : a ≤ b)
    (h : ∀ u v : ℕ, a ≤ u → u ≤ v → v ≤ b → v - u ≤ L → ‖∑ n ∈ Finset.Ioc u v, F n‖ ≤ A) :
    ‖∑ n ∈ Finset.Ioc a b, F n‖ ≤ ((((b - a : ℕ) : ℝ)) / L + 1) * A :=
  b3d_block_aux F L hL A hA b (b - a) a hab rfl h

/-! ### E. Polynomial phase on a block -/

/-- E. Polynomial phase of degree below k on a block: from B1, B2, B3. -/
theorem poly_phase_block (P : Polynomial ℝ) {k : ℕ} (hk : 3 ≤ k) (hdeg : P.natDegree < k)
    {a b : ℕ} (hab : a ≤ b) {lam : ℝ} (hlam0 : 0 < lam)
    (hP : ∀ x ∈ Set.Icc (a : ℝ) ((b : ℝ) + 1),
      lam ≤ P.derivative.eval x ∧ P.derivative.eval x ≤ 1 / 2) :
    ‖∑ n ∈ Finset.Ioc a b, eK (P.eval (n : ℝ))‖ ≤ k * (1 / lam) + 2 * k := by
  have hcard : (P.derivative.derivative.roots.toFinset.card : ℝ) + 1 ≤ k := by
    have h1 := Multiset.toFinset_card_le P.derivative.derivative.roots
    have h2 := Polynomial.card_roots' P.derivative.derivative
    have h3 := Polynomial.natDegree_derivative_le P.derivative
    have h4 := Polynomial.natDegree_derivative_le P
    have h5 : P.derivative.derivative.roots.toFinset.card + 1 ≤ k := by omega
    exact_mod_cast h5
  have hA : (0 : ℝ) ≤ 1 / lam := by positivity
  have hmain := piecewise_sum_bound (fun n : ℕ => eK (P.eval (n : ℝ)))
    (fun n => le_of_eq (eK_norm _)) P.derivative.derivative.roots.toFinset (1 / lam) hA a b hab
    (by
      intro u v hau huv hvb hS
      have hu : (a : ℝ) ≤ u := by exact_mod_cast hau
      have hv : (v : ℝ) ≤ b := by exact_mod_cast hvb
      have huv' : (u : ℝ) ≤ (v : ℝ) + 1 := by
        have : (u : ℝ) ≤ v := by exact_mod_cast huv
        linarith
      exact poly_phase_run P huv hlam0
        (fun x hx => hP x ⟨le_trans hu hx.1, le_trans hx.2 (by linarith)⟩)
        (poly_deriv_mono_of_no_root P huv' hS))
  refine le_trans hmain ?_
  have hc0 : (0 : ℝ) ≤ (P.derivative.derivative.roots.toFinset.card : ℝ) := Nat.cast_nonneg _
  have e1 : ((P.derivative.derivative.roots.toFinset.card : ℝ) + 1) * (1 / lam)
      ≤ (k : ℝ) * (1 / lam) := mul_le_mul_of_nonneg_right hcard hA
  linarith

/-! ### F. Smooth phase on a block -/

private theorem f_eK_lip (x y : ℝ) : ‖eK x - eK y‖ ≤ 2 * Real.pi * |x - y| := by
  have h1 : eK x - eK y = eK y * (eK (x - y) - 1) := by
    have h2 : eK x = eK y * eK (x - y) := by
      rw [← eK_add]; congr 1; ring
    rw [h2]; ring
  have h3 : eK (x - y) = Complex.exp (Complex.I * ((2 * Real.pi * (x - y) : ℝ) : ℂ)) := by
    unfold eK; rw [mul_comm]
  rw [h1, norm_mul, eK_norm, one_mul, h3]
  refine le_trans Real.norm_exp_I_mul_ofReal_sub_one_le ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

/-- F. One block for the smooth phase f: from A and E. -/
theorem s1_block {f : ℝ → ℝ} {k : ℕ} (hk : 3 ≤ k) {U : Set ℝ} (hU : IsOpen U) {a b : ℕ}
    (hab : a ≤ b) (hsub : Set.Icc (a : ℝ) ((b : ℝ) + 1) ⊆ U) (hf : ContDiffOn ℝ k f U)
    {M lam H : ℝ}
    (hM : ∀ x ∈ Set.Icc (a : ℝ) ((b : ℝ) + 1), |iteratedDeriv k f x / k.factorial| ≤ M)
    (hH : (b : ℝ) + 1 - a ≤ H) (hlam0 : 0 < lam)
    (hder : ∀ x ∈ Set.Icc (a : ℝ) ((b : ℝ) + 1), 2 * lam ≤ deriv f x ∧ deriv f x ≤ 1 / 4)
    (hsmall : k * M * H ^ (k - 1) ≤ lam) :
    ‖∑ n ∈ Finset.Ioc a b, eK (f n)‖ ≤
      k * (1 / lam) + 2 * k + 2 * Real.pi * ((b : ℝ) - a) * M * H ^ k := by
  have habR : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab
  have hab' : (a : ℝ) ≤ (b : ℝ) + 1 := by linarith
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM a ⟨le_refl _, hab'⟩)
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  obtain ⟨P, hdeg, hP1, hP2⟩ := taylor_poly_approx (show 1 ≤ k by omega) hU hab' hsub hf hM
  have hxa : ∀ x ∈ Set.Icc (a : ℝ) ((b : ℝ) + 1), 0 ≤ x - a ∧ x - a ≤ H := by
    intro x hx
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hF : ∀ x ∈ Set.Icc (a : ℝ) ((b : ℝ) + 1), |f x - P.eval x| ≤ M * H ^ k := by
    intro x hx
    obtain ⟨h0, h1⟩ := hxa x hx
    exact le_trans (hP1 x hx)
      (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 k) hM0)
  have hD : ∀ x ∈ Set.Icc (a : ℝ) ((b : ℝ) + 1),
      |deriv f x - P.derivative.eval x| ≤ lam := by
    intro x hx
    obtain ⟨h0, h1⟩ := hxa x hx
    refine le_trans (hP2 x hx) (le_trans ?_ hsmall)
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 h1 (k - 1)) (mul_nonneg hk0 hM0)
  have hE : ∀ x ∈ Set.Icc (a : ℝ) ((b : ℝ) + 1),
      lam ≤ P.derivative.eval x ∧ P.derivative.eval x ≤ 1 / 2 := by
    intro x hx
    have h1 := abs_le.mp (hD x hx)
    have h2 := hder x hx
    exact ⟨by linarith [h1.2, h2.1], by linarith [h1.1, h2.1, h2.2]⟩
  have hEb := poly_phase_block P hk hdeg hab hlam0 hE
  have hsplit : ∑ n ∈ Finset.Ioc a b, eK (f n) =
      ∑ n ∈ Finset.Ioc a b, eK (P.eval (n : ℝ)) +
        ∑ n ∈ Finset.Ioc a b, (eK (f n) - eK (P.eval (n : ℝ))) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun n _ => by ring)
  have hterm : ∀ n ∈ Finset.Ioc a b,
      ‖eK (f n) - eK (P.eval (n : ℝ))‖ ≤ 2 * Real.pi * (M * H ^ k) := by
    intro n hn
    rw [Finset.mem_Ioc] at hn
    have hnI : (n : ℝ) ∈ Set.Icc (a : ℝ) ((b : ℝ) + 1) := by
      have h1 : (a : ℝ) ≤ n := by exact_mod_cast hn.1.le
      have h2 : (n : ℝ) ≤ b := by exact_mod_cast hn.2
      exact ⟨h1, by linarith⟩
    exact le_trans (f_eK_lip _ _)
      (mul_le_mul_of_nonneg_left (hF _ hnI) (by positivity))
  have hsum : ‖∑ n ∈ Finset.Ioc a b, (eK (f n) - eK (P.eval (n : ℝ)))‖ ≤
      2 * Real.pi * ((b : ℝ) - a) * M * H ^ k := by
    refine le_trans (norm_sum_le _ _) (le_trans (Finset.sum_le_sum hterm) ?_)
    rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.cast_sub hab]
    exact le_of_eq (by ring)
  rw [hsplit]
  exact le_trans (norm_add_le _ _) (add_le_add hEb hsum)

/-! ### G. The saving for an increasing phase -/

private lemma g_three_pow (k : ℕ) (K : ℝ) (h : (k : ℝ) ≤ K) : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ K := by
  rw [← Real.rpow_natCast]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) h

private lemma g_pow_rpow (x β : ℝ) (n : ℕ) (hx : 0 < x) : (x ^ β) ^ n = x ^ (β * (n : ℝ)) := by
  rw [Real.rpow_mul hx.le, Real.rpow_natCast]

private lemma g_big (D e x : ℝ) (hD : 0 < D) (he : 0 < e) (h : D ^ (1 / e) ≤ x) : D ≤ x ^ e := by
  calc D = (D ^ (1 / e)) ^ e := by
        rw [← Real.rpow_mul hD.le, one_div_mul_cancel he.ne', Real.rpow_one]
    _ ≤ x ^ e := Real.rpow_le_rpow (Real.rpow_nonneg hD.le _) h he.le

private lemma g_hsmall (x β Θ₀ K H : ℝ) (k : ℕ) (hx : 1 ≤ x) (hk : 1 ≤ k) (hkK : (k : ℝ) ≤ K)
    (hβ : β ≤ Θ₀) (hH0 : 0 ≤ H) (hH : H ≤ 3 * x ^ β) :
    (k : ℝ) * x ^ (-(Θ₀ * k)) * H ^ (k - 1) ≤ K * (3 : ℝ) ^ K * x ^ (-Θ₀) := by
  have hx0 : 0 < x := by linarith
  have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have hc : (((k - 1 : ℕ)) : ℝ) = (k : ℝ) - 1 := by
    rw [Nat.cast_sub hk]; simp
  have h1 : H ^ (k - 1) ≤ (3 * x ^ β) ^ (k - 1) := pow_le_pow_left₀ hH0 hH _
  have h2 : (3 * x ^ β) ^ (k - 1) = 3 ^ (k - 1) * x ^ (β * (((k - 1 : ℕ)) : ℝ)) := by
    rw [mul_pow, g_pow_rpow x β (k - 1) hx0]
  have h3 : (3 : ℝ) ^ (k - 1) ≤ (3 : ℝ) ^ K := g_three_pow (k - 1) K (by rw [hc]; linarith)
  have h4 : x ^ (-(Θ₀ * k)) * x ^ (β * (((k - 1 : ℕ)) : ℝ)) ≤ x ^ (-Θ₀) := by
    rw [← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx
    rw [hc]
    nlinarith [mul_nonneg (sub_nonneg.mpr hβ) (sub_nonneg.mpr hk1)]
  have hM0 : 0 < x ^ (-(Θ₀ * k)) := Real.rpow_pos_of_pos hx0 _
  have hP0 : 0 < x ^ (β * (((k - 1 : ℕ)) : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have h30 : (0 : ℝ) < 3 ^ (k - 1) := by positivity
  have hK0 : 0 ≤ K := by linarith
  calc (k : ℝ) * x ^ (-(Θ₀ * k)) * H ^ (k - 1)
      ≤ (k : ℝ) * x ^ (-(Θ₀ * k)) * (3 ^ (k - 1) * x ^ (β * (((k - 1 : ℕ)) : ℝ))) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 (by positivity)
    _ = ((k : ℝ) * 3 ^ (k - 1)) * (x ^ (-(Θ₀ * k)) * x ^ (β * (((k - 1 : ℕ)) : ℝ))) := by ring
    _ ≤ (K * (3 : ℝ) ^ K) * x ^ (-Θ₀) := by
        apply mul_le_mul _ h4 (by positivity) (by positivity)
        exact mul_le_mul hkK h3 h30.le hK0

private lemma g_tail (x β Θ₀ K H : ℝ) (k : ℕ) (hx : 1 ≤ x) (hk : 3 ≤ k) (hkK : (k : ℝ) ≤ K)
    (hβ : β ≤ Θ₀) (hH0 : 0 ≤ H) (hH : H ≤ 3 * x ^ β) :
    x ^ (-(Θ₀ * k)) * H ^ k ≤ (3 : ℝ) ^ K * x ^ (-(3 * (Θ₀ - β))) := by
  have hx0 : 0 < x := by linarith
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have h1 : H ^ k ≤ (3 * x ^ β) ^ k := pow_le_pow_left₀ hH0 hH _
  have h2 : (3 * x ^ β) ^ k = 3 ^ k * x ^ (β * (k : ℝ)) := by
    rw [mul_pow, g_pow_rpow x β k hx0]
  have h3 : (3 : ℝ) ^ k ≤ (3 : ℝ) ^ K := g_three_pow k K hkK
  have h4 : x ^ (-(Θ₀ * k)) * x ^ (β * (k : ℝ)) ≤ x ^ (-(3 * (Θ₀ - β))) := by
    rw [← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx
    nlinarith [mul_nonneg (sub_nonneg.mpr hβ) (sub_nonneg.mpr hk3)]
  have hM0 : 0 < x ^ (-(Θ₀ * k)) := Real.rpow_pos_of_pos hx0 _
  have hP0 : 0 < x ^ (β * (k : ℝ)) := Real.rpow_pos_of_pos hx0 _
  have h30 : (0 : ℝ) < 3 ^ k := by positivity
  calc x ^ (-(Θ₀ * k)) * H ^ k
      ≤ x ^ (-(Θ₀ * k)) * (3 ^ k * x ^ (β * (k : ℝ))) := by
        rw [← h2]; exact mul_le_mul_of_nonneg_left h1 hM0.le
    _ = 3 ^ k * (x ^ (-(Θ₀ * k)) * x ^ (β * (k : ℝ))) := by ring
    _ ≤ (3 : ℝ) ^ K * x ^ (-(3 * (Θ₀ - β))) :=
        mul_le_mul h3 h4 (by positivity) (by positivity)

/-- G. The saving for increasing phase, in terms of eK and deriv: from D and F. -/
theorem s1_saving_core :
    ∀ θ Θ Θ₀ δ : ℝ, 0 < δ → δ < 1 → 0 < Θ → Θ < θ → θ < Θ₀ → Θ₀ < 1 →
      ∃ B c N₀ : ℝ, 0 < B ∧ 0 < c ∧ 0 < N₀ ∧
        ∀ N : ℕ, N₀ ≤ (N : ℝ) → ∀ (f : ℝ → ℝ) (k : ℕ),
        3 ≤ k → (∃ U : Set ℝ, IsOpen U ∧ Set.Icc (N : ℝ) (2 * N) ⊆ U ∧ ContDiffOn ℝ k f U) →
        (∀ x ∈ Set.Icc (N : ℝ) (2 * N),
          |iteratedDeriv k f x / k.factorial| ≤ (N : ℝ) ^ (-(Θ₀ * k))) →
        δ * k ≤ 1 →
        (∀ x ∈ Set.Icc (N : ℝ) (2 * N),
          (N : ℝ) ^ (-θ) ≤ deriv f x ∧ deriv f x ≤ (N : ℝ) ^ (-Θ)) →
        ‖∑ n ∈ Finset.Ioc N (2 * N), eK (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2) := by
  intro θ Θ Θ₀ δ hδ hδ1 hΘ hΘθ hθΘ₀ hΘ₀1
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = 1 / δ := ⟨_, rfl⟩
  obtain ⟨C, hCdef⟩ : ∃ C : ℝ, C = (3 : ℝ) ^ K := ⟨_, rfl⟩
  obtain ⟨β, hβdef⟩ : ∃ β : ℝ, β = (θ + Θ₀) / 2 := ⟨_, rfl⟩
  obtain ⟨γ, hγdef⟩ : ∃ γ : ℝ, γ = (Θ₀ - θ) / 2 := ⟨_, rfl⟩
  have hK0 : 0 < K := by rw [hKdef]; positivity
  have hC0 : 0 < C := by rw [hCdef]; positivity
  have hγ0 : 0 < γ := by rw [hγdef]; linarith
  have hθ0 : 0 < θ := by linarith
  have hβ0 : 0 < β := by rw [hβdef]; linarith
  have hβ1 : β < 1 := by rw [hβdef]; linarith
  have hβΘ₀ : β ≤ Θ₀ := by rw [hβdef]; linarith
  have hΘβ : Θ₀ - β = γ := by rw [hβdef, hγdef]; ring
  have hπ : 0 < Real.pi := Real.pi_pos
  have hD0 : 0 < 2 * K * C := by positivity
  have hT1 : 0 < (4 : ℝ) ^ (1 / Θ) := by positivity
  have hT2 : 0 < (2 * K * C) ^ (1 / (Θ₀ - θ)) := Real.rpow_pos_of_pos hD0 _
  refine ⟨8 * K + 8 * Real.pi * C + 1, γ,
    2 + (4 : ℝ) ^ (1 / Θ) + (2 * K * C) ^ (1 / (Θ₀ - θ)), by positivity, hγ0, by positivity, ?_⟩
  intro N hN f k hk hU hMf hδk hderf
  obtain ⟨U, hUo, hUsub, hfU⟩ := hU
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = (N : ℝ) := ⟨_, rfl⟩
  rw [← hxdef] at hN hMf hderf hUsub ⊢
  have hx2 : 2 ≤ x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hx0 : 0 < x := by linarith
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ (N : ℝ) := by rw [← hxdef]; exact hx1
    exact_mod_cast this
  have hk3 : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hkK : (k : ℝ) ≤ K := by
    rw [hKdef, le_div_iff₀ hδ]; linarith
  -- the three largeness facts
  have hbig1 : (4 : ℝ) ≤ x ^ Θ := g_big 4 Θ x (by norm_num) hΘ (by linarith)
  have hbig2 : 2 * K * C ≤ x ^ (Θ₀ - θ) :=
    g_big (2 * K * C) (Θ₀ - θ) x hD0 (by linarith) (by linarith)
  have hquarter : x ^ (-Θ) ≤ 1 / 4 := by
    rw [Real.rpow_neg hx0.le, one_div]
    exact inv_anti₀ (by norm_num) hbig1
  -- basic powers
  have hq1 : 1 ≤ x ^ θ := Real.one_le_rpow hx1 hθ0.le
  have hb1 : 1 ≤ x ^ β := Real.one_le_rpow hx1 hβ0.le
  have hp1 : 1 ≤ x ^ (1 - β) := Real.one_le_rpow hx1 (by linarith)
  have hE1 : 1 ≤ x ^ (1 - γ) := Real.one_le_rpow hx1 (by rw [hγdef]; linarith)
  -- L and H
  obtain ⟨L, hLdef⟩ : ∃ L : ℕ, L = ⌈x ^ β⌉₊ := ⟨_, rfl⟩
  have hLlow : x ^ β ≤ (L : ℝ) := by rw [hLdef]; exact Nat.le_ceil _
  have hLup : (L : ℝ) ≤ 2 * x ^ β := by
    have := Nat.ceil_lt_add_one (show 0 ≤ x ^ β by linarith)
    rw [hLdef]; linarith
  have hLpos : 0 < L := by
    have : (0 : ℝ) < (L : ℝ) := by linarith
    exact_mod_cast this
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hLpos
  have hH0 : (0 : ℝ) ≤ (L : ℝ) + 1 := by linarith
  have hH3 : (L : ℝ) + 1 ≤ 3 * x ^ β := by linarith
  -- lam
  have hlam0 : 0 < x ^ (-θ) / 2 := by
    have := Real.rpow_pos_of_pos hx0 (-θ); linarith
  have hlaminv : 1 / (x ^ (-θ) / 2) = 2 * x ^ θ := by
    rw [Real.rpow_neg hx0.le]
    have : x ^ θ ≠ 0 := by positivity
    field_simp
  -- hsmall
  have hsmall : (k : ℝ) * x ^ (-(Θ₀ * k)) * ((L : ℝ) + 1) ^ (k - 1) ≤ x ^ (-θ) / 2 := by
    have h1 := g_hsmall x β Θ₀ K ((L : ℝ) + 1) k hx1 (by omega) hkK hβΘ₀ hH0 hH3
    rw [← hCdef] at h1
    have h2 : x ^ (Θ₀ - θ) * x ^ (-Θ₀) = x ^ (-θ) := by
      rw [← Real.rpow_add hx0]; congr 1; ring
    have h3 : 0 < x ^ (-Θ₀) := Real.rpow_pos_of_pos hx0 _
    have h4 : 2 * K * C * x ^ (-Θ₀) ≤ x ^ (Θ₀ - θ) * x ^ (-Θ₀) :=
      mul_le_mul_of_nonneg_right hbig2 h3.le
    linarith
  -- tail
  have htail : x ^ (-(Θ₀ * k)) * ((L : ℝ) + 1) ^ k ≤ C * x ^ (-(3 * γ)) := by
    have h1 := g_tail x β Θ₀ K ((L : ℝ) + 1) k hx1 hk hkK hβΘ₀ hH0 hH3
    rw [← hCdef, hΘβ] at h1
    exact h1
  have hr0 : 0 < x ^ (β - 3 * γ) := Real.rpow_pos_of_pos hx0 _
  have hbr : x ^ β * x ^ (-(3 * γ)) = x ^ (β - 3 * γ) := by
    rw [← Real.rpow_add hx0]; congr 1
  have hM0 : 0 < x ^ (-(Θ₀ * k)) := Real.rpow_pos_of_pos hx0 _
  have hg3 : 0 < x ^ (-(3 * γ)) := Real.rpow_pos_of_pos hx0 _
  -- the block bound
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 4 * K * x ^ θ + 4 * Real.pi * C * x ^ (β - 3 * γ) := ⟨_, rfl⟩
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hblock : ∀ u v : ℕ, N ≤ u → u ≤ v → v ≤ 2 * N - 1 → v - u ≤ L →
      ‖∑ n ∈ Finset.Ioc u v, eK (f n)‖ ≤ A := by
    intro u v hNu huv hv hvu
    have hNu' : x ≤ (u : ℝ) := by rw [hxdef]; exact_mod_cast hNu
    have huv' : (u : ℝ) ≤ (v : ℝ) := by exact_mod_cast huv
    have hv' : (v : ℝ) + 1 ≤ 2 * x := by
      have : v + 1 ≤ 2 * N := by omega
      rw [hxdef]; exact_mod_cast this
    have hvuL : (v : ℝ) - u ≤ (L : ℝ) := by
      have : v ≤ L + u := by omega
      have h' : (v : ℝ) ≤ (L : ℝ) + u := by exact_mod_cast this
      linarith
    have hmem : ∀ y ∈ Set.Icc (u : ℝ) ((v : ℝ) + 1), y ∈ Set.Icc x (2 * x) := by
      intro y hy
      exact ⟨le_trans hNu' hy.1, le_trans hy.2 hv'⟩
    have hmain := s1_block (f := f) (k := k) hk hUo huv
      (fun y hy => hUsub (hmem y hy)) hfU
      (M := x ^ (-(Θ₀ * k))) (lam := x ^ (-θ) / 2) (H := (L : ℝ) + 1)
      (fun y hy => hMf y (hmem y hy)) (by linarith) hlam0
      (fun y hy => by
        have := hderf y (hmem y hy)
        exact ⟨by linarith [this.1], le_trans this.2 hquarter⟩)
      hsmall
    rw [hlaminv] at hmain
    have hk0 : (0 : ℝ) ≤ k := by linarith
    have ht1 : (k : ℝ) * (2 * x ^ θ) + 2 * k ≤ 4 * K * x ^ θ := by
      nlinarith [mul_nonneg hk0 (sub_nonneg.mpr hq1),
        mul_nonneg (sub_nonneg.mpr hkK) (by linarith : (0 : ℝ) ≤ x ^ θ)]
    have ht2 : 2 * Real.pi * ((v : ℝ) - u) * x ^ (-(Θ₀ * k)) * ((L : ℝ) + 1) ^ k
        ≤ 4 * Real.pi * C * x ^ (β - 3 * γ) := by
      have hMH0 : 0 ≤ x ^ (-(Θ₀ * k)) * ((L : ℝ) + 1) ^ k := by positivity
      have hvu0 : (0 : ℝ) ≤ (v : ℝ) - u := by linarith
      calc 2 * Real.pi * ((v : ℝ) - u) * x ^ (-(Θ₀ * k)) * ((L : ℝ) + 1) ^ k
          = 2 * Real.pi * (((v : ℝ) - u) * (x ^ (-(Θ₀ * k)) * ((L : ℝ) + 1) ^ k)) := by ring
        _ ≤ 2 * Real.pi * ((2 * x ^ β) * (C * x ^ (-(3 * γ)))) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact mul_le_mul (le_trans hvuL hLup) htail hMH0 (by positivity)
        _ = 4 * Real.pi * C * (x ^ β * x ^ (-(3 * γ))) := by ring
        _ = 4 * Real.pi * C * x ^ (β - 3 * γ) := by rw [hbr]
    rw [hAdef]; linarith
  -- sum over blocks
  have hsum := block_sum_bound (fun n => eK (f n)) L hLpos A hA0 N (2 * N - 1) (by omega) hblock
  have hcnt : (((2 * N - 1 - N : ℕ)) : ℝ) / L + 1 ≤ 2 * x ^ (1 - β) := by
    have h1 : (((2 * N - 1 - N : ℕ)) : ℝ) ≤ x := by
      have : 2 * N - 1 - N ≤ N := by omega
      rw [hxdef]; exact_mod_cast this
    have h2 : (((2 * N - 1 - N : ℕ)) : ℝ) / L ≤ x / x ^ β := by
      calc (((2 * N - 1 - N : ℕ)) : ℝ) / L ≤ x / L := by
            exact div_le_div_of_nonneg_right h1 hL0.le
        _ ≤ x / x ^ β := div_le_div_of_nonneg_left hx0.le (by linarith) hLlow
    have h3 : x / x ^ β = x ^ (1 - β) := by
      rw [Real.rpow_sub hx0, Real.rpow_one]
    rw [h3] at h2
    linarith
  have hsplit : ∑ n ∈ Finset.Ioc N (2 * N), eK (f n)
      = ∑ n ∈ Finset.Ioc N (2 * N - 1), eK (f n) + eK (f ((2 * N : ℕ) : ℝ)) := by
    have h := Finset.sum_Ioc_succ_top (show N ≤ 2 * N - 1 by omega) (fun n : ℕ => eK (f n))
    rw [show 2 * N - 1 + 1 = 2 * N by omega] at h
    exact h
  have hpq : x ^ (1 - β) * x ^ θ = x ^ (1 - γ) := by
    rw [← Real.rpow_add hx0]; congr 1; rw [hβdef, hγdef]; ring
  have hpr : x ^ (1 - β) * x ^ (β - 3 * γ) ≤ x ^ (1 - γ) := by
    rw [← Real.rpow_add hx0]
    apply Real.rpow_le_rpow_of_exponent_le hx1
    linarith
  have htotal : ‖∑ n ∈ Finset.Ioc N (2 * N), eK (f n)‖
      ≤ (8 * K + 8 * Real.pi * C + 1) * x ^ (1 - γ) := by
    rw [hsplit]
    have hn := norm_add_le (∑ n ∈ Finset.Ioc N (2 * N - 1), eK (f n)) (eK (f ((2 * N : ℕ) : ℝ)))
    rw [eK_norm] at hn
    have h1 : ((((2 * N - 1 - N : ℕ)) : ℝ) / L + 1) * A ≤ 2 * x ^ (1 - β) * A :=
      mul_le_mul_of_nonneg_right hcnt hA0
    have h2 : 2 * x ^ (1 - β) * A
        = 8 * K * (x ^ (1 - β) * x ^ θ) + 8 * Real.pi * C * (x ^ (1 - β) * x ^ (β - 3 * γ)) := by
      rw [hAdef]; ring
    have h3 : 8 * Real.pi * C * (x ^ (1 - β) * x ^ (β - 3 * γ))
        ≤ 8 * Real.pi * C * x ^ (1 - γ) :=
      mul_le_mul_of_nonneg_left hpr (by positivity)
    rw [hpq] at h2
    linarith
  have hexp : x ^ (1 - γ) ≤ x ^ (1 - γ / (k : ℝ) ^ 2) := by
    apply Real.rpow_le_rpow_of_exponent_le hx1
    have hk2 : (1 : ℝ) ≤ (k : ℝ) ^ 2 := one_le_pow₀ (by linarith)
    have : γ / (k : ℝ) ^ 2 ≤ γ := div_le_self hγ0.le hk2
    linarith
  have hB0 : (0 : ℝ) ≤ 8 * K + 8 * Real.pi * C + 1 := by positivity
  have hfin : (8 * K + 8 * Real.pi * C + 1) * x ^ (1 - γ)
      ≤ (8 * K + 8 * Real.pi * C + 1) * x ^ (1 - γ / (k : ℝ) ^ 2) :=
    mul_le_mul_of_nonneg_left hexp hB0
  exact le_trans htotal hfin

end LeanLab.ExceptionalSet.U1539.KaracubaSplit.S1Saving
