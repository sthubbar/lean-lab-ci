import LeanLab.ChenDoubleSieve.I1Bounds
import LeanLab.ChenDoubleSieve.Task587Kernel
import LeanLab.ChenDoubleSieve.Task587PolynomialTools

/-!
Additivity of integrals over the ordered boxes of Wu 2004 Lemma 5.2 page 26 when one
coordinate range is cut at a point. This is the first tool of the grid certificate
plan for the window LEAFs of the Decomp587 splits, Table 1 page 30.
Source: https://arxiv.org/abs/0705.1652. No new definitions.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Set MeasureTheory
namespace LeanLab.ChenDoubleSieve.Task587.DomainSplit
open Wu04Functional

/-- Cutting the j-th range of an ordered box at c splits the integral of any function
integrable on the box into the integrals over the two ordered sub boxes; the common
face x j = c is a null set. Used for the cell decomposition of the Buchstab integrals
of Wu 2004 Lemma 5.2 page 26. -/
theorem integral_domain_split {n : ℕ} (lo hi : Fin n → ℝ) (j : Fin n) (c : ℝ)
    (hlo : lo j ≤ c) (hhi : c ≤ hi j) {f : (Fin n → ℝ) → ℝ}
    (hf : IntegrableOn f (domain lo hi)) :
    ∫ x in domain lo hi, f x =
      (∫ x in domain lo (Function.update hi j c), f x) +
        ∫ x in domain (Function.update lo j c) hi, f x := by
  classical
  set A := domain lo (Function.update hi j c) with hA
  set B := domain (Function.update lo j c) hi with hB
  have hAsub : A ⊆ domain lo hi := by
    rintro x ⟨hm, hx⟩
    refine ⟨hm, fun k => ⟨(hx k).1, ?_⟩⟩
    by_cases hk : k = j
    · subst hk
      have := (hx k).2
      rw [Function.update_self] at this
      linarith
    · have := (hx k).2
      rwa [Function.update_of_ne hk] at this
  have hBsub : B ⊆ domain lo hi := by
    rintro x ⟨hm, hx⟩
    refine ⟨hm, fun k => ⟨?_, (hx k).2⟩⟩
    by_cases hk : k = j
    · subst hk
      have := (hx k).1
      rw [Function.update_self] at this
      linarith
    · have := (hx k).1
      rwa [Function.update_of_ne hk] at this
  have hunion : domain lo hi = A ∪ B := by
    apply Subset.antisymm
    · rintro x ⟨hm, hx⟩
      rcases le_total (x j) c with h | h
      · left
        refine ⟨hm, fun k => ⟨(hx k).1, ?_⟩⟩
        by_cases hk : k = j
        · subst hk
          rw [Function.update_self]
          exact h
        · rw [Function.update_of_ne hk]
          exact (hx k).2
      · right
        refine ⟨hm, fun k => ⟨?_, (hx k).2⟩⟩
        by_cases hk : k = j
        · subst hk
          rw [Function.update_self]
          exact h
        · rw [Function.update_of_ne hk]
          exact (hx k).1
    · exact union_subset hAsub hBsub
  have hnull : volume ((fun x : Fin n → ℝ => x j) ⁻¹' ({c} : Set ℝ)) = 0 := by
    rw [MeasureTheory.volume_pi]
    exact Measure.pi_eval_preimage_null (μ := fun _ : Fin n => (volume : Measure ℝ)) (by simp)
  have hdisj : AEDisjoint volume A B := by
    apply measure_mono_null _ hnull
    rintro x ⟨⟨_, hxA⟩, ⟨_, hxB⟩⟩
    have h1 := (hxA j).2
    have h2 := (hxB j).1
    rw [Function.update_self] at h1 h2
    show x j = c
    linarith
  have hBm : NullMeasurableSet B volume :=
    (Wu04I1.domain_isCompact _ _).measurableSet.nullMeasurableSet
  rw [hunion]
  exact setIntegral_union₀ hdisj hBm (hf.mono_set hAsub) (hf.mono_set hBsub)

/-- The Buchstab integral of Wu 2004 Lemma 5.2 page 26 is additive under a cut of the
j-th range at c, whenever the kernel argument is at least 1 on the box, as on the
whole of the r2j16 window_mid range, where it is at least 1.05. -/
theorem buchstabIntegral_split {ω : ℝ → ℝ} (hω : IsBuchstab ω) {n : ℕ}
    (lo hi : Fin (n + 2) → ℝ) (φ : ℝ) (hl : ∀ k, 0 < lo k)
    (harg : ∀ x ∈ domain lo hi, 1 ≤ (φ - ∑ k, x k) / x ⟨n, by omega⟩)
    (j : Fin (n + 2)) (c : ℝ) (hlo : lo j ≤ c) (hhi : c ≤ hi j) :
    buchstabIntegral ω n lo hi φ =
      buchstabIntegral ω n lo (Function.update hi j c) φ +
        buchstabIntegral ω n (Function.update lo j c) hi φ := by
  unfold buchstabIntegral
  exact integral_domain_split lo hi j c hlo hhi
    (Task587.kernel_integrable_above_one hω lo hi φ hl harg)

/-- The ordered part of a cube with common range a to b in dimension d has measure
(b - a) ^ d over momentDenom d 0, that is d factorial; the volume of a diagonal grid
cell in the cell plan for Wu 2004 Lemma 5.2 page 26. From Task587.integral_listEvalN
with the constant polynomial 1. -/
theorem integral_one_ordered_cube {d : ℕ} {a b : ℚ} (hab : a ≤ b) :
    (∫ x in domain (fun _ : Fin d => (a : ℝ)) (fun _ => (b : ℝ)), (1 : ℝ)) =
      (((b - a) ^ d / (Task562.momentDenom d (fun _ => 0) : ℚ) : ℚ) : ℝ) := by
  have h := Task587.integral_listEvalN (d := d) [((1 : ℚ), fun _ => 0)] hab
  simp only [Task587.listEvalN, Task587.listMomentN, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, pow_zero, Finset.prod_const_one, Rat.cast_one, mul_one,
    add_zero, Finset.sum_const_zero, zero_add, one_mul] at h
  exact h

/-- The zeroth order cell estimate of the grid plan for Wu 2004 Lemma 5.2 page 26: if the
kernel argument is at least 1 and omega of it is at most C on the ordered box, the
Buchstab integral is at most C over lo0 ... lo_last times lo_n, times the measure of the
ordered box. -/
theorem buchstabIntegral_le_cell {ω : ℝ → ℝ} (hω : IsBuchstab ω) {n : ℕ}
    (lo hi : Fin (n + 2) → ℝ) (φ C : ℝ) (hl : ∀ k, 0 < lo k) (hC : 0 ≤ C)
    (harg : ∀ x ∈ domain lo hi, 1 ≤ (φ - ∑ k, x k) / x ⟨n, by omega⟩)
    (hcap : ∀ x ∈ domain lo hi, ω ((φ - ∑ k, x k) / x ⟨n, by omega⟩) ≤ C) :
    buchstabIntegral ω n lo hi φ ≤
      C / ((∏ k, lo k) * lo ⟨n, by omega⟩) * ∫ x in domain lo hi, (1 : ℝ) := by
  have hf := Task587.kernel_integrable_above_one hω lo hi φ hl harg
  have hc : IntegrableOn (fun _ : Fin (n + 2) → ℝ => C / ((∏ k, lo k) * lo ⟨n, by omega⟩))
      (domain lo hi) volume :=
    continuousOn_const.integrableOn_compact (Wu04I1.domain_isCompact lo hi)
  have hD0 : 0 < (∏ k, lo k) * lo ⟨n, by omega⟩ :=
    mul_pos (Finset.prod_pos fun k _ => hl k) (hl _)
  have hm := setIntegral_mono_on hf hc (Wu04I1.domain_isCompact lo hi).measurableSet
    (fun x hx => by
      have hp (k : Fin (n + 2)) : 0 < x k := (hl k).trans_le (hx.2 k).1
      have hprod : ∏ k, lo k ≤ ∏ k, x k := by
        apply Finset.prod_le_prod₀
        · intro k _
          exact (hl k).le
        · intro k _
          exact (hx.2 k).1
      have hD : (∏ k, lo k) * lo ⟨n, by omega⟩ ≤ (∏ k, x k) * x ⟨n, by omega⟩ :=
        mul_le_mul hprod (hx.2 _).1 (hl _).le (Finset.prod_pos fun k _ => hp k).le
      calc ω ((φ - ∑ k, x k) / x ⟨n, by omega⟩) / ((∏ k, x k) * x ⟨n, by omega⟩)
          ≤ C / ((∏ k, x k) * x ⟨n, by omega⟩) :=
            div_le_div_of_nonneg_right (hcap x hx) (hD0.le.trans hD)
        _ ≤ C / ((∏ k, lo k) * lo ⟨n, by omega⟩) := div_le_div_of_nonneg_left hC hD0 hD)
  rw [setIntegral_const, smul_eq_mul, mul_comm] at hm
  rw [setIntegral_const, smul_eq_mul, mul_one]
  exact hm

end LeanLab.ChenDoubleSieve.Task587.DomainSplit
