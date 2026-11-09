/-
Split of `leaf_fold`, the periodisation step of the Poisson fold of this folder, into the
five ingredients of the written fold: the period of `h` moves the shift off `h` onto the
kernel alone, the integral over one unit interval is the integral over the translated
interval, the real line partitions into countably many unit intervals, each translate of
an integrable function is interval integrable, the translated norms are summable in `ℓ¹`,
and a sum of integrable functions integrates termwise.

`leaf_fold_split` below states the split target unchanged and is assembled from the leaves,
so it carries no `sorry` of its own. The leaves are open work items.

AI wrote this Lean code, checked only by the Lean kernel. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_lemma1
import LeanLab.ExceptionalSet.State1539Data264

namespace LeanLab.ExceptionalSet.U1539

open Real MeasureTheory Polynomial
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ### Leaves -/

/-- LEAF. Step 1 of the proof, the period of `h` moves the shift off `h`: for `h` of period
one, a real shift `n` changes neither `h` nor the phase on the kernel, so the integrand at
`α + n` is `h α` times the modulated translate of `K` alone. This is a pointwise identity
at fixed `α` and `n`; it mentions no integral and no integrability, and it is exactly the
step that makes the period of `h` usable. At `n = 0` both sides are the same term, at
`v = 0` the phase is `1` on both sides, and negative `n` is the same identity since the
period is used for every integer shift. -/
theorem leaf_periodic_translate (h K : ℝ → ℂ) (hper : Function.Periodic h 1) (v α : ℝ)
    (n : ℤ) :
    h (α + n) * K (α + n) * eC (-((α + n) * v)) =
      h α * (K (α + n) * eC (-((α + n) * v))) := by
  have H : h (α + n) = h α := by
    have : (n : ℝ) = n • (1 : ℝ) := by simp
    rw [this, hper.zsmul]
  rw [H, mul_assoc]

/-- LEAF. Step 2 of the proof, one term of the fold: the integral of `f` over the unit
interval translated to `n` equals the integral over the fixed interval `[0,1]` of the
translate `α ↦ f (α + n)`. This is the change of variable for a real shift, with no
hypothesis on `f`: the two interval integrals are equal for every function. At `n = 0` it
is an identity of the same integral, and at `n = -1` the translated interval is `[-1,0]`,
which is the corresponding instance. -/
theorem leaf_translate_interval (f : ℝ → ℂ) (n : ℤ) :
    (∫ α in (n : ℝ)..((n : ℝ) + 1), f α) = ∫ α in (0 : ℝ)..1, f (α + n) := by
  have : ∫ α in (0 : ℝ)..1, f (α + n) = ∫ α in (0 + (n : ℝ))..(1 + (n : ℝ)), f α := by
    exact intervalIntegral.integral_comp_add_right f (n : ℝ)
  rw [this]
  congr 1
  · ring
  · ring

/-- LEAF. Step 3 of the proof, the fold of the real line: the integral of an integrable
function over the whole line is the sum over the integers of its integrals over the unit
intervals `(n, n+1]`. The unit intervals are disjoint and cover the line, so the series of
norms is the integral of the norm and converges. This is the step that turns one integral
over the line into a series; it uses no periodicity and no kernel, and it holds for the
zero function with both sides `0`. -/
theorem leaf_partition (f : ℝ → ℂ) (hf : Integrable f) :
    (∫ α, f α) = ∑' n : ℤ, ∫ α in (n : ℝ)..((n : ℝ) + 1), f α := by
  have H : (∫ α, f α) = ∫ α in Set.univ, f α := by
    exact setIntegral_univ.symm
  rw [H, ← iUnion_Ioc_intCast ℝ]
  have hd : Pairwise (Function.onFun (AEDisjoint volume) (fun n : ℤ => Set.Ioc (n : ℝ) ((n : ℝ) + 1))) := by
    intro i j hij
    have : Disjoint (Set.Ioc (i : ℝ) (i + 1)) (Set.Ioc (j : ℝ) (j + 1)) := by
      apply Set.disjoint_left.mpr
      rintro x ⟨_, h2⟩ ⟨h3, _⟩
      have : (i : ℝ) + 1 ≤ (j : ℝ) ∨ (j : ℝ) + 1 ≤ (i : ℝ) := by
        rcases lt_trichotomy i j with h | h | h
        · left; exact_mod_cast h
        · exfalso; exact hij h
        · right; exact_mod_cast h
      cases this with
      | inl h => linarith
      | inr h => linarith
    exact this.aedisjoint
  have hn : ∀ n : ℤ, NullMeasurableSet (Set.Ioc (n : ℝ) ((n : ℝ) + 1)) volume := by
    intro n
    exact nullMeasurableSet_Ioc
  have hi : IntegrableOn f (⋃ n : ℤ, Set.Ioc (n : ℝ) ((n : ℝ) + 1)) := by
    rw [iUnion_Ioc_intCast ℝ]
    exact hf.integrableOn
  have hint := hasSum_integral_iUnion_ae hn hd hi
  rw [← hint.tsum_eq]
  congr 1
  ext n
  rw [intervalIntegral.integral_of_le]
  linarith

/-- LEAF. Step 4 of the proof, each translate is interval integrable on one period: a
translate of an integrable function is integrable on the whole line, hence interval
integrable over `[0,1]`. This is the hypothesis the termwise integration needs, stated
alone; it is a consequence of integrability and involves no sum and no value of the
integral. -/
theorem leaf_translate_intervalIntegrable (f : ℝ → ℂ) (hf : Integrable f) (n : ℤ) :
    IntervalIntegrable (fun α : ℝ => f (α + n)) volume 0 1 := by
  have H : Integrable (fun α : ℝ => f (α + n)) := by
    apply Integrable.comp_add_right hf (n : ℝ)
  exact H.intervalIntegrable

/-- LEAF. Step 5 of the proof, the translated norms are summable: for an integrable `f`
the series over the integers of `∫ α in (0,1), ‖f (α + n)‖` converges, with sum the
integral of `‖f‖` over the line, which is finite. This is the domination hypothesis of the
termwise integration, in `ℓ¹` form, and it is where the absolute convergence of the fold
lives. For the zero function every term is `0` and the series converges. -/
theorem leaf_shift_norm_summable (f : ℝ → ℂ) (hf : Integrable f) :
    Summable (fun n : ℤ => ∫ α in (0 : ℝ)..1, ‖f (α + n)‖) := by
  have h1 : (fun n : ℤ => ∫ α in (0 : ℝ)..1, ‖f (α + n)‖) = (fun n : ℤ => ∫ α in (n : ℝ)..((n : ℝ) + 1), ‖f α‖) := by
    ext n
    have : ∫ α in (0 : ℝ)..1, ‖f (α + n)‖ = ∫ α in (0 + (n : ℝ))..(1 + (n : ℝ)), ‖f α‖ := by
      exact intervalIntegral.integral_comp_add_right (fun x => ‖f x‖) (n : ℝ)
    rw [this]
    congr 1
    · ring
    · ring
  rw [h1]
  have h_int : Integrable (fun α => ‖f α‖) := hf.norm
  have hn : ∀ n : ℤ, NullMeasurableSet (Set.Ioc (n : ℝ) ((n : ℝ) + 1)) volume := by
    intro n
    exact nullMeasurableSet_Ioc
  have hd : Pairwise (Function.onFun (AEDisjoint volume) (fun n : ℤ => Set.Ioc (n : ℝ) ((n : ℝ) + 1))) := by
    intro i j hij
    have : Disjoint (Set.Ioc (i : ℝ) (i + 1)) (Set.Ioc (j : ℝ) (j + 1)) := by
      apply Set.disjoint_left.mpr
      rintro x ⟨_, h2⟩ ⟨h3, _⟩
      have : (i : ℝ) + 1 ≤ (j : ℝ) ∨ (j : ℝ) + 1 ≤ (i : ℝ) := by
        rcases lt_trichotomy i j with h | h | h
        · left; exact_mod_cast h
        · exfalso; exact hij h
        · right; exact_mod_cast h
      cases this with
      | inl h => linarith
      | inr h => linarith
    exact this.aedisjoint
  have hi : IntegrableOn (fun α => ‖f α‖) (⋃ n : ℤ, Set.Ioc (n : ℝ) ((n : ℝ) + 1)) := by
    rw [iUnion_Ioc_intCast ℝ]
    exact h_int.integrableOn
  have hint := hasSum_integral_iUnion_ae hn hd hi
  have hint_sum := hint.summable
  have H : (fun n : ℤ => ∫ α in (n : ℝ)..((n : ℝ) + 1), ‖f α‖) = (fun n : ℤ => ∫ α in Set.Ioc (n : ℝ) ((n : ℝ) + 1), ‖f α‖) := by
    ext n
    rw [intervalIntegral.integral_of_le]
    linarith
  rw [H]
  exact hint_sum

/-- LEAF. Step 6 of the proof, the termwise integration: if every translate of `f` is
interval integrable on `[0,1]` and the integrals of the translated norms are summable,
then the integral over `[0,1]` of the sum of the translates is the sum of their integrals.
This is the interchange of an integral and a series on a finite measure space, under the
`ℓ¹` domination of step 5; it says nothing about the value of either side. -/
theorem leaf_interval_tsum_integral (f : ℝ → ℂ)
    (hint : ∀ n : ℤ, IntervalIntegrable (fun α : ℝ => f (α + n)) volume 0 1)
    (hsum : Summable (fun n : ℤ => ∫ α in (0 : ℝ)..1, ‖f (α + n)‖)) :
    (∫ α in (0 : ℝ)..1, ∑' n : ℤ, f (α + n)) =
      ∑' n : ℤ, ∫ α in (0 : ℝ)..1, f (α + n) := by
  have H : (∫ α in Set.Ioc 0 1, ∑' n : ℤ, f (α + n)) = ∑' n : ℤ, ∫ α in Set.Ioc 0 1, f (α + n) := by
    apply integral_tsum
    · intro i
      have h1 := hint i
      have h2 := h1.1
      exact h2.aestronglyMeasurable
    · have h_pos : ∀ n : ℤ, 0 ≤ ∫ α in Set.Ioc (0 : ℝ) (1 : ℝ), ‖f (α + n)‖ := by
        intro n
        apply integral_nonneg
        intro x
        exact norm_nonneg _
      have h_sum2 : Summable (fun n : ℤ => ∫ α in Set.Ioc (0 : ℝ) (1 : ℝ), ‖f (α + n)‖) := by
        have H_hsum : (fun n : ℤ => ∫ α in Set.Ioc (0 : ℝ) (1 : ℝ), ‖f (α + n)‖) = (fun n : ℤ => ∫ α in (0 : ℝ)..1, ‖f (α + n)‖) := by
          ext n
          rw [intervalIntegral.integral_of_le]
          linarith
        rw [H_hsum]
        exact hsum
      have h_sum3 := ENNReal.ofReal_tsum_of_nonneg h_pos h_sum2
      have h_top : ENNReal.ofReal (∑' n : ℤ, ∫ α in Set.Ioc (0 : ℝ) (1 : ℝ), ‖f (α + n)‖) ≠ ⊤ := ENNReal.ofReal_ne_top
      rw [h_sum3] at h_top
      have H_eq : ∀ n : ℤ, ENNReal.ofReal (∫ α in Set.Ioc (0 : ℝ) (1 : ℝ), ‖f (α + n)‖) = ∫⁻ α in Set.Ioc (0 : ℝ) (1 : ℝ), ‖f (α + n)‖ₑ := by
        intro n
        apply ofReal_integral_norm_eq_lintegral_enorm
        have h1 := hint n
        exact h1.1
      have h_top2 : (∑' n : ℤ, ∫⁻ α in Set.Ioc (0 : ℝ) (1 : ℝ), ‖f (α + n)‖ₑ) ≠ ⊤ := by
        have : (fun n : ℤ => ENNReal.ofReal (∫ α in Set.Ioc (0 : ℝ) (1 : ℝ), ‖f (α + n)‖)) = (fun n : ℤ => ∫⁻ α in Set.Ioc (0 : ℝ) (1 : ℝ), ‖f (α + n)‖ₑ) := by
          ext n
          exact H_eq n
        rw [← this]
        exact h_top
      exact h_top2
  have h1 : (∫ α in (0 : ℝ)..1, ∑' n : ℤ, f (α + n)) = ∫ α in Set.Ioc 0 1, ∑' n : ℤ, f (α + n) := by
    rw [intervalIntegral.integral_of_le]
    linarith
  have h2 : (fun n : ℤ => ∫ α in (0 : ℝ)..1, f (α + n)) = (fun n : ℤ => ∫ α in Set.Ioc 0 1, f (α + n)) := by
    ext n
    rw [intervalIntegral.integral_of_le]
    linarith
  rw [h1, h2, H]

/-! ### Assembly -/

/-- The split target unchanged: the fold of the line into one period of `h`. The line is
partitioned into unit intervals (step 3), each unit interval is moved back to `[0,1]` with
the shift carried by the integrand (step 2), the sum is integrated termwise using the
interval integrability of the translates (step 4) and the `ℓ¹` bound on their norms
(step 5) through the interchange (step 6), and finally the period of `h` pulls it out of
the sum (step 1). -/
theorem leaf_fold_split (h K : ℝ → ℂ) (hper : Function.Periodic h 1) (v : ℝ)
    (hg : Integrable (fun α : ℝ => h α * K α * eC (-(α * v)))) :
    (∫ α, h α * K α * eC (-(α * v))) =
      ∫ α in (0 : ℝ)..1, h α * (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) := by
  have hswap :
      (∑' n : ℤ, ∫ α in (0 : ℝ)..1,
          (fun β : ℝ => h β * K β * eC (-(β * v))) (α + n)) =
        ∫ α in (0 : ℝ)..1,
          ∑' n : ℤ, (fun β : ℝ => h β * K β * eC (-(β * v))) (α + n) :=
    (leaf_interval_tsum_integral (fun β : ℝ => h β * K β * eC (-(β * v)))
      (fun n =>
        leaf_translate_intervalIntegrable (fun β : ℝ => h β * K β * eC (-(β * v))) hg n)
      (leaf_shift_norm_summable (fun β : ℝ => h β * K β * eC (-(β * v))) hg)).symm
  calc
    (∫ α, h α * K α * eC (-(α * v)))
        = ∑' n : ℤ, ∫ α in (n : ℝ)..((n : ℝ) + 1),
            (fun β : ℝ => h β * K β * eC (-(β * v))) α :=
          leaf_partition (fun β : ℝ => h β * K β * eC (-(β * v))) hg
    _ = ∑' n : ℤ, ∫ α in (0 : ℝ)..1,
            (fun β : ℝ => h β * K β * eC (-(β * v))) (α + n) := by
          apply tsum_congr
          intro n
          exact leaf_translate_interval (fun β : ℝ => h β * K β * eC (-(β * v))) n
    _ = ∫ α in (0 : ℝ)..1,
            ∑' n : ℤ, (fun β : ℝ => h β * K β * eC (-(β * v))) (α + n) := hswap
    _ = ∫ α in (0 : ℝ)..1, h α * (∑' n : ℤ, K (α + n) * eC (-((α + n) * v))) := by
          apply intervalIntegral.integral_congr
          intro α _
          dsimp only
          rw [← tsum_mul_left]
          exact tsum_congr (fun n => leaf_periodic_translate h K hper v α n)

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.leaf_fold_split
