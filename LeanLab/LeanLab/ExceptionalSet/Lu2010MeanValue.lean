/-
P0095 W. C. Lu 2010, Section 9 tools. Unit U-6847, CLOUD MANUAL-M1, 2026-10-21, track T1.

The mean value ∫ over a period of |Σ_{n<K} a_n e(nα)|² dα = Σ a_n², for real a_n, by
orthogonality, `meanValue`; its instance for S(x, y, α) = Σ_{y<n≤x} Λ(n) e(nα),
`meanValue_S`: ∫ |S(x, y, α)|² dα = Σ_{y<n≤x} Λ(n)², the "∫|S|² ≪ d log N" step behind the
minor arc estimate of Section 9; and the Cauchy-Schwarz form (∫_s f)² ≤ |s| ∫_s f² on a set
of finite measure, `sq_setIntegral_le`.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach itself is OPEN.
-/
import Mathlib
import LeanLab.ExceptionalSet.Lu2010Sec9

namespace LeanLab.ExceptionalSet.Lu2010MeanValue
open Real Filter Topology Finset ArithmeticFunction MeasureTheory Complex ComplexConjugate
  LeanLab.ExceptionalSet LeanLab.ExceptionalSet.Lu2010Assembly LeanLab.ExceptionalSet.Lu2010Orth

theorem conj_ee (x : ℝ) : conj (ee x) = ee (-x) := by
  unfold ee
  rw [← Complex.exp_conj]
  congr 1
  simp [Complex.conj_ofReal, map_ofNat]

/-- **Mean value**: `∫_u^{u+1} |Σ_{n<K} a_n e(nα)|² dα = Σ_{n<K} a_n²` for real `a_n`. -/
theorem meanValue (a : ℕ → ℝ) (K : ℕ) (u : ℝ) :
    ∫ α in u..(u + 1), ‖∑ n ∈ range K, (a n : ℂ) * ee (n * α)‖ ^ 2 = ∑ n ∈ range K, a n ^ 2 := by
  have key : ∀ α : ℝ, ((‖∑ n ∈ range K, (a n : ℂ) * ee (n * α)‖ ^ 2 : ℝ) : ℂ) =
      ∑ n ∈ range K, ∑ m ∈ range K, ((a n * a m : ℝ) : ℂ) * ee (((n : ℤ) - (m : ℤ) : ℤ) * α) := by
    intro α
    rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
    apply Finset.sum_congr rfl; intro n _
    apply Finset.sum_congr rfl; intro m _
    rw [map_mul, Complex.conj_ofReal, conj_ee]
    have : ee (n * α) * ee (-(m * α)) = ee (((n : ℤ) - (m : ℤ) : ℤ) * α) := by
      rw [← ee_add]; congr 1; push_cast; ring
    rw [← this]; push_cast; ring
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  simp_rw [key]
  rw [intervalIntegral.integral_finset_sum
    (f := fun n α => ∑ m ∈ range K, ((a n * a m : ℝ) : ℂ) * ee (((n : ℤ) - (m : ℤ) : ℤ) * α))
    (fun n _ => Continuous.intervalIntegrable
    (continuous_finset_sum _ (fun (m : ℕ) _ =>
      continuous_const.mul (ee_continuous (((n : ℤ) - (m : ℤ) : ℤ) : ℝ)))) _ _)]
  rw [Complex.ofReal_sum]
  apply Finset.sum_congr rfl; intro n hn
  rw [intervalIntegral.integral_finset_sum
    (f := fun m α => ((a n * a m : ℝ) : ℂ) * ee (((n : ℤ) - (m : ℤ) : ℤ) * α))
    (fun (m : ℕ) _ => Continuous.intervalIntegrable
    (continuous_const.mul (ee_continuous (((n : ℤ) - (m : ℤ) : ℤ) : ℝ))) _ _)]
  simp_rw [intervalIntegral.integral_const_mul]
  have hc : ∀ m ∈ range K, ((a n : ℂ) * (a m : ℂ)) *
      (∫ α in u..(u + 1), ee ((((n : ℤ) - (m : ℤ) : ℤ) : ℝ) * α)) =
      if m = n then (a n : ℂ) ^ 2 else 0 := by
    intro m _
    rw [integral_ee]
    split_ifs with h1 h2 h2
    · subst h2; ring
    · exfalso; apply h2; omega
    · exfalso; apply h1; rw [h2]; ring
    · ring
  push_cast at hc ⊢
  rw [Finset.sum_congr rfl hc, Finset.sum_ite_eq' (range K) n, if_pos hn]

/-- The mean value for `S(x, y, α)`: `∫ |S|² = Σ_{y<n≤x} Λ(n)²`. -/
theorem meanValue_S (x y u : ℝ) :
    ∫ α in u..(u + 1), ‖Ssum x y α‖ ^ 2 =
      ∑ n ∈ range (⌊x⌋₊ + 1), (if y < n ∧ (n : ℝ) ≤ x then Λ n else 0) ^ 2 := by
  rw [← meanValue (fun n => if y < n ∧ (n : ℝ) ≤ x then Λ n else 0) (⌊x⌋₊ + 1) u]
  congr 1; funext α; congr 2
  unfold Ssum
  apply Finset.sum_congr rfl; intro n _
  split_ifs <;> simp

/-- `∫ |S|² ≤ (x - y + 1) log² x` for `0 ≤ y ≤ x`. -/
theorem meanValue_S_le {x y : ℝ} (hy : 0 ≤ y) (hxy : y ≤ x) (u : ℝ) :
    ∫ α in u..(u + 1), ‖Ssum x y α‖ ^ 2 ≤ (x - y + 1) * Real.log x ^ 2 := by
  rw [meanValue_S]
  have hsub : ∀ n ∈ range (⌊x⌋₊ + 1), (if y < n ∧ (n : ℝ) ≤ x then Λ n else 0) ^ 2 ≤
      if n ∈ Ioc ⌊y⌋₊ ⌊x⌋₊ then Real.log x ^ 2 else 0 := by
    intro n _
    split_ifs with h1 h2 h2
    · have hn1 : (1 : ℝ) ≤ n := by
        have : 0 < n := by
          rcases Nat.eq_zero_or_pos n with h | h
          · subst h; simp at h1; linarith [h1.1]
          · exact h
        exact_mod_cast this
      have hL : Λ n ≤ Real.log x := vonMangoldt_le_log.trans
        (Real.log_le_log (by linarith) h1.2)
      exact pow_le_pow_left₀ vonMangoldt_nonneg hL 2
    · exfalso; apply h2
      simp only [Finset.mem_Ioc]
      constructor
      · exact Nat.floor_lt hy |>.mpr h1.1
      · exact Nat.le_floor h1.2
    · nlinarith [sq_nonneg (Real.log x)]
    · simp
  refine (Finset.sum_le_sum hsub).trans ?_
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  have hfil : (range (⌊x⌋₊ + 1)).filter (fun n => n ∈ Ioc ⌊y⌋₊ ⌊x⌋₊) = Ioc ⌊y⌋₊ ⌊x⌋₊ := by
    ext n; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]; omega
  rw [hfil]
  have hc := Lu2010Lemma1.card_Ioc_floor_le hy hxy
  exact mul_le_mul_of_nonneg_right hc (sq_nonneg _)

/-- Cauchy-Schwarz on a set of finite measure: `(∫_s f)² ≤ |s| ∫_s f²`. -/
theorem sq_setIntegral_le {s : Set ℝ} (hs : volume s ≠ ⊤) {f : ℝ → ℝ}
    (hf : IntegrableOn f s) (hf2 : IntegrableOn (fun x => f x ^ 2) s) :
    (∫ x in s, f x) ^ 2 ≤ (volume s).toReal * ∫ x in s, f x ^ 2 := by
  set L := (volume s).toReal
  set I := ∫ x in s, f x
  set J := ∫ x in s, f x ^ 2
  have hL : 0 ≤ L := ENNReal.toReal_nonneg
  -- 0 ≤ ∫ (L f - I)² = L² J - 2 L I² + I² L = L (L J - I²)
  have h0 : 0 ≤ ∫ x in s, (L * f x - I) ^ 2 := setIntegral_nonneg_of_ae_restrict
    (Filter.Eventually.of_forall fun x => sq_nonneg _)
  have hexp : ∫ x in s, (L * f x - I) ^ 2 = L ^ 2 * J - 2 * L * I * I + I ^ 2 * L := by
    have e : ∀ x, (L * f x - I) ^ 2 = L ^ 2 * f x ^ 2 - 2 * L * I * f x + I ^ 2 := fun x => by ring
    simp_rw [e]
    have hc : IntegrableOn (fun _ : ℝ => I ^ 2) s := integrableOn_const hs
    have hA : IntegrableOn (fun x => L ^ 2 * f x ^ 2) s := hf2.const_mul _
    have hB : IntegrableOn (fun x => 2 * L * I * f x) s := hf.const_mul _
    have i1 : ∫ x in s, (L ^ 2 * f x ^ 2 - 2 * L * I * f x + I ^ 2) =
        (∫ x in s, (L ^ 2 * f x ^ 2 - 2 * L * I * f x)) + (∫ x in s, I ^ 2) :=
      integral_add (hA.sub hB) hc
    have i2 : ∫ x in s, (L ^ 2 * f x ^ 2 - 2 * L * I * f x) =
        (∫ x in s, L ^ 2 * f x ^ 2) - (∫ x in s, 2 * L * I * f x) := integral_sub hA hB
    have i3 : ∫ x in s, L ^ 2 * f x ^ 2 = L ^ 2 * J := integral_const_mul _ _
    have i4 : ∫ x in s, 2 * L * I * f x = 2 * L * I * I := integral_const_mul _ _
    have i5 : ∫ x in s, I ^ 2 = L * I ^ 2 := by
      rw [setIntegral_const, smul_eq_mul]; rfl
    rw [i1, i2, i3, i4, i5]; ring
  rw [hexp] at h0
  rcases hL.eq_or_lt with hL0 | hLpos
  · -- measure zero: both integrals vanish
    have hz : volume s = 0 := by
      rcases (ENNReal.toReal_eq_zero_iff _).mp hL0.symm with h | h
      · exact h
      · exact absurd h hs
    have : I = 0 := by simp [I, Measure.restrict_eq_zero.mpr hz]
    rw [this, ← hL0]; simp
  · nlinarith

end LeanLab.ExceptionalSet.Lu2010MeanValue

#print axioms LeanLab.ExceptionalSet.Lu2010MeanValue.conj_ee
#print axioms LeanLab.ExceptionalSet.Lu2010MeanValue.meanValue
#print axioms LeanLab.ExceptionalSet.Lu2010MeanValue.meanValue_S
#print axioms LeanLab.ExceptionalSet.Lu2010MeanValue.meanValue_S_le
#print axioms LeanLab.ExceptionalSet.Lu2010MeanValue.sq_setIntegral_le
