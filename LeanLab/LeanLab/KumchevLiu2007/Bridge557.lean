/-
Elementary conversion from a discrete maximal prime bound to page 17.
Source https://arxiv.org/abs/0801.0130 page 17 between displays 57 and 58.
AI wrote the Lean code. Goldbach is open.
-/
import Mathlib
open scoped BigOperators
open MeasureTheory

namespace LeanLab.KumchevLiu2007.Task557c

/-- Page 17, a uniform bound for independently selected errors bounds the
sum of their real suprema. The zero witnesses make every set nonempty. -/
theorem sum_csSup_le {α : Type*} (s : Finset α) (E : α → Set ℝ) (C : ℝ)
    (h0 : ∀ i ∈ s, 0 ∈ E i)
    (h : ∀ f : α → ℝ, (∀ i ∈ s, f i ∈ E i) → (∑ i ∈ s, f i) ≤ C) :
    (∑ i ∈ s, sSup (E i)) ≤ C := by
  classical
  induction s using Finset.induction_on generalizing C with
  | empty => simpa using h (fun _ => 0) (by simp)
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi]
    have hs : sSup (E i) ≤ C - ∑ j ∈ s, sSup (E j) := by
      apply csSup_le ⟨0, h0 i (Finset.mem_insert_self i s)⟩
      intro v hv
      have hh : (∑ j ∈ s, sSup (E j)) ≤ C - v := by
        apply ih (C - v) (fun j hj => h0 j (Finset.mem_insert_of_mem hj))
        intro f hf
        have hupdate : ∀ j ∈ insert i s, Function.update f i v j ∈ E j := by
          intro j hj
          rcases Finset.mem_insert.mp hj with rfl | hj
          · simpa using hv
          · rw [Function.update_of_ne (by intro he; subst j; exact hi hj)]
            exact hf j hj
        have hh := h (Function.update f i v) hupdate
        rw [Finset.sum_insert hi, Function.update_self] at hh
        have heq : (∑ j ∈ s, Function.update f i v j) = ∑ j ∈ s, f j := by
          apply Finset.sum_congr rfl
          intro j hj
          exact Function.update_of_ne (a := j) (a' := i) (by intro he; subst j; exact hi hj) v f
        rw [heq] at hh
        linarith
      linarith
    linarith

/-- Page 17, the reciprocal logarithm decreases on the integral domain. -/
theorem reciprocal_log_antitone : AntitoneOn (fun t : ℝ => 1 / Real.log t) (Set.Ici 2) := by
  intro x hx y hy hxy
  change 2 ≤ x at hx
  apply one_div_le_one_div_of_le (Real.log_pos (by linarith : (1 : ℝ) < x))
  exact Real.log_le_log (by linarith) hxy

/-- Page 17, the endpoint reciprocal logarithm is at most two. -/
theorem reciprocal_log_two_le : (1 : ℝ) / Real.log 2 ≤ 2 := by
  have hh := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
  have hp : 0 < Real.log 2 := Real.log_pos (by norm_num)
  apply (div_le_iff₀ hp).mpr
  norm_num at hh
  linarith

/-- Page 17, the discrete logarithmic integral differs from its continuous
version by a bounded amount at an integer endpoint. -/
theorem discrete_li_integer (N : ℕ) (hN : 2 ≤ N) :
    0 ≤ (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / Real.log n) -
      (∫ t in (2 : ℝ)..(N : ℝ), 1 / Real.log t) ∧
    (∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / Real.log n) -
      (∫ t in (2 : ℝ)..(N : ℝ), 1 / Real.log t) ≤ 2 := by
  let f : ℝ → ℝ := fun t => 1 / Real.log t
  have hanti : AntitoneOn f (Set.Icc (2 : ℝ) N) :=
    reciprocal_log_antitone.mono (fun _ hx => hx.1)
  have hlo := AntitoneOn.integral_le_sum_Ico hN hanti
  have hhi := AntitoneOn.sum_le_integral_Ico hN hanti
  have hsplit : (∑ n ∈ Finset.Icc 1 N, f n) =
      (∑ n ∈ Finset.Ico 2 N, f n) + f N := by
    have hh := Finset.sum_Ico_consecutive (fun n : ℕ => f n)
      (by omega : 1 ≤ 2) (by omega : 2 ≤ N + 1)
    have hsmall : (∑ n ∈ Finset.Ico (1 : ℕ) 2, f n) = 0 := by norm_num [f]
    rw [hsmall, zero_add] at hh
    calc
      _ = ∑ n ∈ Finset.Ico 1 (N + 1), f n := by rw [Finset.Ico_add_one_right_eq_Icc]
      _ = ∑ n ∈ Finset.Ico 2 (N + 1), f n := hh.symm
      _ = _ := Finset.sum_Ico_succ_top hN _
  have hshift : (∑ n ∈ Finset.Ico 2 N, f (n + 1 : ℕ)) =
      (∑ n ∈ Finset.Icc 1 N, f n) - f 2 := by
    have hh := Finset.sum_Ico_add' (fun n : ℕ => f n) 2 N 1
    have hs := Finset.sum_Ico_consecutive (fun n : ℕ => f n)
      (by omega : 1 ≤ 3) (by omega : 3 ≤ N + 1)
    have hsmall : (∑ n ∈ Finset.Ico (1 : ℕ) 3, f n) = f 2 := by norm_num [f, Finset.sum_Ico_succ_top]
    rw [hsmall] at hs
    simp only [Finset.Ico_add_one_right_eq_Icc] at hs hh
    norm_num only at hh
    linarith
  have hnpos : 0 ≤ f N := by dsimp [f]; positivity
  norm_num only [Nat.cast_ofNat] at hlo hhi
  dsimp [f] at hsplit hshift hnpos hlo hhi
  rw [hshift] at hhi
  constructor
  · linarith
  · linarith [reciprocal_log_two_le]

/-- Page 17, integrability of the reciprocal logarithm on the positive domain. -/
theorem reciprocal_log_integrable (a b : ℝ) (ha : 2 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable (fun t : ℝ => 1 / Real.log t) volume a b := by
  apply ContinuousOn.intervalIntegrable
  apply continuousOn_of_forall_continuousAt
  intro x hx
  rw [Set.uIcc_of_le hab] at hx
  have hx2 : 2 ≤ x := ha.trans hx.1
  exact continuousAt_const.div (Real.continuousAt_log (by linarith))
    (Real.log_pos (by linarith)).ne'

/-- Page 17, passing from a discrete logarithmic sum to the printed real
integral costs at most two at every real endpoint at least two. -/
theorem discrete_li_real (x : ℝ) (hx : 2 ≤ x) :
    |(∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) / Real.log n) -
      (∫ t in (2 : ℝ)..x, 1 / Real.log t)| ≤ 2 := by
  let N := ⌊x⌋₊
  have hN : 2 ≤ N := Nat.le_floor hx
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have htail : 0 ≤ ∫ t in (N : ℝ)..x, 1 / Real.log t := by
    apply intervalIntegral.integral_nonneg hNx
    intro t ht
    exact div_nonneg zero_le_one (Real.log_nonneg (by linarith [ht.1]))
  have hnorm := intervalIntegral.norm_integral_le_of_norm_le_const
    (a := (N : ℝ)) (b := x) (C := (2 : ℝ)) (f := fun t => 1 / Real.log t) (by
      intro t ht
      rw [Set.uIoc_of_le hNx] at ht
      have ht2 : 2 ≤ t := hN2.trans ht.1.le
      have hlog : 0 < Real.log t := Real.log_pos (by linarith)
      rw [Real.norm_eq_abs, abs_of_pos (by positivity : 0 < 1 / Real.log t)]
      exact (reciprocal_log_antitone (by simp) ht2 ht2).trans reciprocal_log_two_le)
  rw [Real.norm_eq_abs, abs_of_nonneg htail,
    abs_of_nonneg (sub_nonneg.mpr hNx)] at hnorm
  have hshort : x - (N : ℝ) < 1 := by
    have hh := Nat.lt_floor_add_one x
    change x < (N : ℝ) + 1 at hh
    linarith
  have hbase := discrete_li_integer N hN
  have hadd := intervalIntegral.integral_add_adjacent_intervals
    (reciprocal_log_integrable 2 N (by norm_num) hN2)
    (reciprocal_log_integrable N x hN2 hNx)
  rw [← hadd]
  apply abs_le.mpr
  constructor <;> dsimp [N] at * <;> linarith

/-- Page 17, an upstream copy of the prime progression count. -/
noncomputable def primeAP (x : ℝ) (d a : ℕ) : ℝ :=
  (((Finset.Icc 1 ⌊x⌋₊).filter (fun p : ℕ => p.Prime ∧ p % d = a % d)).card : ℝ)

/-- Page 17, an upstream copy of the maximal prime discrepancy. -/
noncomputable def primeError (T : ℝ) (d : ℕ) : ℝ :=
  sSup (insert 0 {v : ℝ | ∃ a : ℕ, ∃ x : ℝ,
    a < d ∧ Nat.Coprime a d ∧ 2 ≤ x ∧ x ≤ T ∧
      v = |primeAP x d a - (∫ t in (2 : ℝ)..x, 1 / Real.log t) / Nat.totient d|})

/-- Page 17, the discrete logarithmic sum before its integral correction. -/
noncomputable def discreteLi (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 1 ⌊x⌋₊, (1 : ℝ) / Real.log n

/-- Page 17, the correction to one residue class is at most two. -/
theorem prime_error_integral_correction (x : ℝ) (d a : ℕ) (hx : 2 ≤ x) (hd : 1 ≤ d) :
    |primeAP x d a - (∫ t in (2 : ℝ)..x, 1 / Real.log t) / Nat.totient d| ≤
      |primeAP x d a - discreteLi x / Nat.totient d| + 2 := by
  have hφ1 : (1 : ℝ) ≤ Nat.totient d := by exact_mod_cast Nat.totient_pos.mpr hd
  have hφ : (0 : ℝ) < Nat.totient d := by linarith
  have hli : |discreteLi x - (∫ t in (2 : ℝ)..x, 1 / Real.log t)| ≤ 2 :=
    discrete_li_real x hx
  have herr : |discreteLi x / Nat.totient d -
      (∫ t in (2 : ℝ)..x, 1 / Real.log t) / Nat.totient d| ≤ 2 := by
    rw [← sub_div, abs_div, abs_of_pos hφ]
    exact (div_le_iff₀ hφ).mpr (by linarith)
  exact (abs_sub_le (primeAP x d a) (discreteLi x / Nat.totient d)
    ((∫ t in (2 : ℝ)..x, 1 / Real.log t) / Nat.totient d)).trans
      (add_le_add le_rfl herr)

/-- Page 17, a discrete maximal prime distribution bound supplies the exact
continuous integral and supremum form. CONDITIONAL ON the explicit discrete
prime distribution bound. The proof uses no analytic distribution theorem. -/
theorem maximal_prime_of_discrete
    (hPi : ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ,
      ∀ T : ℝ, 2 ≤ T → ∀ a : ℕ → ℕ, (∀ q, Nat.Coprime (a q) q) →
      ∀ y : ℕ → ℝ, (∀ q, 0 ≤ y q ∧ y q ≤ T) →
      (∑ q ∈ Finset.Icc 1 ⌊Real.sqrt T / Real.log T ^ B⌋₊,
        |primeAP (y q) q (a q) - discreteLi (y q) / q.totient|) ≤
        K * T / Real.log T ^ A)
    (A : ℝ) (hA : 0 < A) :
    ∃ b C T0 : ℝ, 0 < b ∧ 0 < C ∧ 2 ≤ T0 ∧
      ∀ T : ℝ, T0 ≤ T → ∀ D : ℕ,
        (D : ℝ) ≤ Real.sqrt T * Real.log T ^ (-b) →
        (∑ d ∈ Finset.Icc 1 D, primeError T d) ≤
          C * T * Real.log T ^ (-A) := by
  classical
  obtain ⟨B, hB, K, hK⟩ := hPi A hA
  let b := B + A
  let C := max K 0 + 3
  refine ⟨b, C, max 2 (Real.exp 1), by dsimp [b]; linarith,
    by dsimp [C]; have := le_max_right K 0; linarith, le_max_left _ _, ?_⟩
  intro T hT D hD
  have hT2 : 2 ≤ T := (le_max_left _ _).trans hT
  have hT0 : 0 < T := by linarith
  have hL1 : 1 ≤ Real.log T := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hT)
  have hL0 : 0 < Real.log T := by linarith
  have hpow : Real.log T ^ (-b) ≤ (Real.log T ^ B)⁻¹ := by
    rw [← Real.rpow_neg hL0.le]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by dsimp [b]; linarith)
  have hDold : D ≤ ⌊Real.sqrt T / Real.log T ^ B⌋₊ := by
    apply Nat.le_floor
    exact hD.trans (by simpa only [div_eq_mul_inv] using
      mul_le_mul_of_nonneg_left hpow (Real.sqrt_nonneg T))
  have hsqrt : Real.sqrt T ≤ T := by
    apply (Real.sqrt_le_left hT0.le).mpr
    nlinarith
  have hscale : (D : ℝ) ≤ T * Real.log T ^ (-A) := by
    apply hD.trans
    apply mul_le_mul hsqrt
      (Real.rpow_le_rpow_of_exponent_le hL1 (by dsimp [b]; linarith))
      (Real.rpow_nonneg hL0.le _) hT0.le
  have hchoices (a : ℕ → ℕ) (ha : ∀ q, Nat.Coprime (a q) q)
      (y : ℕ → ℝ) (hy : ∀ q, 0 ≤ y q ∧ y q ≤ T) :
      (∑ q ∈ Finset.Icc 1 D,
        |primeAP (y q) q (a q) - discreteLi (y q) / q.totient|) ≤
        K * T * Real.log T ^ (-A) := by
    have hh := hK T hT2 a ha y hy
    have heq : K * T / Real.log T ^ A = K * T * Real.log T ^ (-A) := by
      rw [Real.rpow_neg hL0.le, div_eq_mul_inv]
    rw [heq] at hh
    exact (Finset.sum_le_sum_of_subset_of_nonneg
      (Finset.Icc_subset_Icc_right hDold) (fun _ _ _ => abs_nonneg _)).trans hh
  unfold primeError
  apply sum_csSup_le (Finset.Icc 1 D)
    (fun d => insert 0 {v : ℝ | ∃ a : ℕ, ∃ x : ℝ,
      a < d ∧ Nat.Coprime a d ∧ 2 ≤ x ∧ x ≤ T ∧
        v = |primeAP x d a - (∫ t in (2 : ℝ)..x, 1 / Real.log t) / Nat.totient d|})
    (C * T * Real.log T ^ (-A)) (fun _ _ => Set.mem_insert _ _)
  intro f hf
  have hex : ∀ q : ℕ, ∃ a : ℕ, ∃ x : ℝ,
      Nat.Coprime a q ∧ 0 ≤ x ∧ x ≤ T ∧
      (q ∈ Finset.Icc 1 D → f q ≤ |primeAP x q a - discreteLi x / q.totient| + 2) := by
    intro q
    by_cases hq : q ∈ Finset.Icc 1 D
    · rcases Set.mem_insert_iff.mp (hf q hq) with hz | hz
      · refine ⟨1, 0, Nat.coprime_one_left q, le_rfl, hT0.le, ?_⟩
        intro _
        rw [hz]
        positivity
      · obtain ⟨a, x, ha, hcop, hx, hxT, heq⟩ := hz
        exact ⟨a, x, hcop, by linarith, hxT, fun _ =>
          by rw [heq]; exact prime_error_integral_correction x q a hx (Finset.mem_Icc.mp hq).1⟩
    · exact ⟨1, 0, Nat.coprime_one_left q, le_rfl, hT0.le, by simp [hq]⟩
  choose a y ha hy0 hyT hfy using hex
  have hsum : (∑ q ∈ Finset.Icc 1 D, f q) ≤
      (∑ q ∈ Finset.Icc 1 D,
        |primeAP (y q) q (a q) - discreteLi (y q) / q.totient|) + 2 * D := by
    simpa [Finset.sum_add_distrib, nsmul_eq_mul, mul_comm] using
      Finset.sum_le_sum (fun q hq => hfy q hq)
  have hh := hchoices a ha y (fun q => ⟨hy0 q, hyT q⟩)
  have hC : K + 2 ≤ C := by dsimp [C]; linarith [le_max_left K 0]
  have hS : 0 ≤ T * Real.log T ^ (-A) := by positivity
  have hmul := mul_le_mul_of_nonneg_right hC hS
  dsimp [C] at *
  nlinarith

#print axioms sum_csSup_le
#print axioms reciprocal_log_antitone
#print axioms reciprocal_log_two_le
#print axioms discrete_li_integer
#print axioms reciprocal_log_integrable
#print axioms discrete_li_real
#print axioms primeAP
#print axioms primeError
#print axioms discreteLi
#print axioms prime_error_integral_correction
#print axioms maximal_prime_of_discrete

end LeanLab.KumchevLiu2007.Task557c
