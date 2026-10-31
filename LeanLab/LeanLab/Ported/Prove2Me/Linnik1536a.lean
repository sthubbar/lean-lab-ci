/-
Port of six accepted Prove2Me proofs by fizzyinc3, Apache 2.0.
Source: https://beta.prove2.me . Mission 4b504f07.
Original environment: Lean 4.33.1. Lab environment: Lean 4.35.
LL_Linnik1536a.markov, id af70bad1-6531-468f-a760-34d4e6d5453c
Submission 225efe92-08ff-4fdc-a4ff-f3814815f056.
LL_Linnik1536a.exp_le_even_partial, id cf8c8c4e-45e1-4a4a-8ccd-82a276a14ace
Submission 20961a8d-cda9-438a-ba45-607b19cf1c2f.
LL_Linnik1536a.moment_binom, id 99dae314-4aa5-43d7-972b-a29d637f10ce
Submission 36ceb626-4aad-41d8-94b4-621417946e86.
LL_Linnik1536a.four_pow_le, id f83aca82-d836-43a6-bc4b-0323f8cf44ad
Submission 4c5b1181-5dad-40b4-8655-384fa4da4c98.
LL_Linnik1536a.moment_SL_nonneg, id bb1c3ab3-5cf6-48ff-b3be-8c3daecd710d
Submission 635ddfc4-a406-471a-9484-aec9c7ec281a.
LL_Linnik1536a.even_partial_le_int_exp, id e0a774e7-d153-4475-9125-6a9164651f2e
Submission 301aacc3-5247-429a-8ff9-5dce088a1667.
AI adapted this Lean code. Goldbach is open.
The lab definitions below are moved verbatim to avoid a circular import.
-/
import Mathlib

namespace LeanLab.Linnik.Decomp1536a

open Real MeasureTheory Finset

/-- `G_L(x) = Σ_{j=0}^{L-1} e(2^j x)`, Section 4, p. 172, with `g = 2`. -/
noncomputable def Gpow (L : ℕ) (x : ℝ) : ℂ :=
  ∑ j ∈ range L, Complex.exp (2 * π * Complex.I * ((2 : ℂ) ^ j * x))

/-- `S_L(x) = Re G_L(x) = Σ_{j=0}^{L-1} cos(2π 2^j x)`, Section 4, p. 172. -/
noncomputable def Spow (L : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range L, Real.cos (2 * π * ((2 : ℝ) ^ j * x))

/-- `E_L = ∫_0^1 e^{λ S_L(x)} dx`, proof of Theorem 2, p. 173. -/
noncomputable def EL (L : ℕ) (lam : ℝ) : ℝ :=
  ∫ x in (0 : ℝ)..1, Real.exp (lam * Spow L x)

/-- The large deviation set `{x ∈ [0,1] : |G_L(x)| > dL}` of Section 7, p. 184. -/
def devSet (L : ℕ) (d : ℝ) : Set ℝ :=
  {x | x ∈ Set.Icc (0 : ℝ) 1 ∧ d * L < ‖Gpow L x‖}

end LeanLab.Linnik.Decomp1536a

namespace LeanLab.Ported.Prove2Me.Linnik1536a

open Real MeasureTheory Finset
open LeanLab.Linnik.Decomp1536a

theorem four_pow_le (j : ℕ) : (4 : ℝ) ^ j ≤ (2 * j + 1) * Nat.centralBinom j := by
  exact_mod_cast Nat.four_pow_le_two_mul_add_one_mul_centralBinom j


theorem markov {L : ℕ} {d lam : ℝ} (hlam : 0 ≤ lam) :
    volume (LeanLab.Linnik.Decomp1536a.devSet L d) ≤
      ENNReal.ofReal (Real.exp (-(lam * d * L)) *
        ∫ x in (0 : ℝ)..1, Real.exp (lam * ‖LeanLab.Linnik.Decomp1536a.Gpow L x‖)) := by
  set f : ℝ → ℝ := fun x => Real.exp (lam * ‖LeanLab.Linnik.Decomp1536a.Gpow L x‖) with hf
  have hcont : Continuous f := by
    rw [hf]; unfold LeanLab.Linnik.Decomp1536a.Gpow; fun_prop
  set c := Real.exp (lam * d * L) with hcdef
  have hc : 0 < c := Real.exp_pos _
  have hsub : LeanLab.Linnik.Decomp1536a.devSet L d ⊆ {0} ∪ ({x | c ≤ f x} ∩ Set.Ioc 0 1) := by
    rintro x ⟨⟨h0, h1⟩, hx⟩
    rcases h0.eq_or_lt with h | h
    · left; exact h.symm
    · right
      refine ⟨?_, h, h1⟩
      show Real.exp (lam * d * L) ≤ Real.exp (lam * ‖LeanLab.Linnik.Decomp1536a.Gpow L x‖)
      apply Real.exp_le_exp.mpr
      have := mul_le_mul_of_nonneg_left hx.le hlam
      linarith [this]
  have hmeas : MeasurableSet {x | c ≤ f x} := measurableSet_le measurable_const hcont.measurable
  have hint : IntegrableOn f (Set.Ioc 0 1) :=
    (hcont.continuousOn.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  have hm := mul_meas_ge_le_integral_of_nonneg (μ := volume.restrict (Set.Ioc (0:ℝ) 1))
    (Filter.Eventually.of_forall fun x => (Real.exp_pos _).le) hint c
  have hfin : (volume.restrict (Set.Ioc (0:ℝ) 1)) {x | c ≤ f x} ≠ ⊤ := by
    rw [Measure.restrict_apply hmeas]
    exact ne_top_of_le_ne_top (by simp) (measure_mono Set.inter_subset_right)
  calc volume (LeanLab.Linnik.Decomp1536a.devSet L d)
      ≤ volume ({0} ∪ ({x | c ≤ f x} ∩ Set.Ioc 0 1)) := measure_mono hsub
    _ ≤ volume ({0} : Set ℝ) + volume ({x | c ≤ f x} ∩ Set.Ioc 0 1) := measure_union_le _ _
    _ = (volume.restrict (Set.Ioc (0:ℝ) 1)) {x | c ≤ f x} := by
        rw [Real.volume_singleton, zero_add, Measure.restrict_apply hmeas]
    _ ≤ ENNReal.ofReal (c⁻¹ * ∫ x in Set.Ioc (0:ℝ) 1, f x) := by
        rw [← ENNReal.ofReal_toReal hfin]
        apply ENNReal.ofReal_le_ofReal
        rw [le_inv_mul_iff₀ hc]
        exact hm
    _ = _ := by
        rw [intervalIntegral.integral_of_le zero_le_one, Real.exp_neg]


namespace TaylorTail

lemma term_le {r : ℝ} {n : ℕ} (hr : 0 ≤ r) (hrn : r ≤ n) (i : ℕ) :
    r ^ (2 * n + i) / ((2 * n + i).factorial : ℝ) ≤ Real.exp r * (1 / 2) ^ i := by
  induction i with
  | zero => simpa using Real.pow_div_factorial_le_exp (x := r) hr (2 * n)
  | succ i ih =>
    have hk : r ^ (2 * n + (i + 1)) / ((2 * n + (i + 1)).factorial : ℝ)
        = r ^ (2 * n + i) / ((2 * n + i).factorial : ℝ) * (r / ((2 * n + i : ℕ) + 1 : ℝ)) := by
      rw [show 2 * n + (i + 1) = (2 * n + i) + 1 by ring, Nat.factorial_succ, pow_succ]
      push_cast
      field_simp
    rw [hk]
    have hpos : (0 : ℝ) < ((2 * n + i : ℕ) : ℝ) + 1 := by positivity
    have h1 : r / ((2 * n + i : ℕ) + 1 : ℝ) ≤ 1 / 2 := by
      rw [div_le_iff₀ hpos]
      push_cast
      have : (0:ℝ) ≤ i := by positivity
      nlinarith
    have h0 : 0 ≤ r / ((2 * n + i : ℕ) + 1 : ℝ) := by positivity
    have ht : 0 ≤ r ^ (2 * n + i) / ((2 * n + i).factorial : ℝ) := by positivity
    calc _ ≤ Real.exp r * (1 / 2) ^ i * (1 / 2) := mul_le_mul ih h1 h0 (by positivity)
      _ = _ := by rw [pow_succ]; ring

end TaylorTail

theorem exp_le_even_partial {A r : ℝ} (hr : 0 ≤ r) (hrA : r ≤ A) :
    Real.exp r ≤
      2 * ∑ j ∈ range (2 * ⌈A⌉₊ + 1), r ^ (2 * j) / ((2 * j).factorial : ℝ) + 1 := by
  set n := ⌈A⌉₊ with hn
  have hrn : r ≤ n := hrA.trans (Nat.le_ceil A)
  set f : ℕ → ℝ := fun j => r ^ (2 * j) / ((2 * j).factorial : ℝ) with hf
  have hs := Real.hasSum_cosh r
  have hsum : Summable f := hs.summable
  have hsplit := hsum.sum_add_tsum_nat_add (2 * n + 1)
  rw [hs.tsum_eq] at hsplit
  -- tail bound
  have hen : Real.exp r ≤ 4 ^ n := by
    calc Real.exp r ≤ Real.exp n := Real.exp_le_exp.mpr hrn
      _ = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul, mul_one]
      _ ≤ 4 ^ n := by
        gcongr
        linarith [Real.exp_one_lt_d9]
  have hbound : ∀ j, f (j + (2 * n + 1)) ≤ (1 / 4) * (1 / 2) ^ j := by
    intro j
    have := TaylorTail.term_le hr hrn (2 * j + 2 * n + 2)
    simp only [hf]
    rw [show 2 * (j + (2 * n + 1)) = 2 * n + (2 * j + 2 * n + 2) by ring]
    refine this.trans ?_
    have h4 : (4:ℝ) ^ n * (1 / 2) ^ (2 * n) = 1 := by
      rw [pow_mul, ← mul_pow]; norm_num
    calc Real.exp r * (1 / 2) ^ (2 * j + 2 * n + 2)
        ≤ 4 ^ n * (1 / 2) ^ (2 * j + 2 * n + 2) := by gcongr
      _ = (4 ^ n * (1 / 2) ^ (2 * n)) * (1 / 4) * (1 / 2) ^ (2 * j) := by
        rw [pow_add, pow_add]; ring
      _ ≤ (1 / 4) * (1 / 2) ^ j := by
        rw [h4, one_mul]
        exact mul_le_mul_of_nonneg_left
          (pow_le_pow_of_le_one (by norm_num) (by norm_num) (by omega)) (by norm_num)
  have hgeo : Summable (fun j : ℕ => (1 / 4 : ℝ) * (1 / 2) ^ j) :=
    (summable_geometric_two).mul_left _
  have htail : ∑' j, f (j + (2 * n + 1)) ≤ 1 / 2 := by
    calc ∑' j, f (j + (2 * n + 1)) ≤ ∑' j : ℕ, (1 / 4 : ℝ) * (1 / 2) ^ j :=
          Summable.tsum_le_tsum hbound ((summable_nat_add_iff _).mpr hsum) hgeo
      _ = 1 / 2 := by rw [tsum_mul_left, tsum_geometric_two]; norm_num
  have hc := Real.cosh_eq r
  have hneg := Real.exp_pos (-r)
  have : Real.exp r ≤ 2 * Real.cosh r := by rw [hc]; linarith
  linarith


namespace FiniteFourier

noncomputable def E (n : ℤ) (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * ((n : ℂ) * x))

lemma E_cont (n : ℤ) : Continuous (E n) := by
  unfold E; fun_prop

lemma E_zero (x : ℝ) : E 0 x = 1 := by simp [E]

lemma E_add (n m : ℤ) (x : ℝ) : E n x * E m x = E (n + m) x := by
  unfold E; rw [← Complex.exp_add]; congr 1; push_cast; ring

lemma E_conj (n : ℤ) (x : ℝ) : (starRingEnd ℂ) (E n x) = E (-n) x := by
  unfold E; rw [← Complex.exp_conj]; congr 1
  simp [map_mul, Complex.conj_ofReal, map_ofNat]

lemma E_int (n : ℤ) : ∫ x in (0 : ℝ)..1, E n x = if n = 0 then 1 else 0 := by
  split_ifs with h
  · subst h; simp [E_zero]
  · have hc : (2 * π * Complex.I * n) ≠ 0 := by
      have := Real.pi_pos
      simp [h, Real.pi_ne_zero, Complex.I_ne_zero]
    have : (fun x : ℝ => E n x) = fun x : ℝ => Complex.exp ((2 * π * Complex.I * n) * x) := by
      funext x; unfold E; congr 1; ring
    rw [this, integral_exp_mul_complex hc]
    have h1 : Complex.exp (2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = 1 := by
      rw [show (2 * π * Complex.I * n * ((1 : ℝ) : ℂ)) = n * (2 * π * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I n
    rw [h1]; simp



lemma good_one : (fun f : ℝ → ℂ => ∃ s : Multiset ℤ, ∀ x, f x = (s.map fun n => E n x).sum) (fun _ => 1) := ⟨{0}, fun x => by simp [E_zero]⟩

lemma msum_mul (s t : Multiset ℤ) (x : ℝ) :
    (s.map fun n => E n x).sum * (t.map fun n => E n x).sum =
      ((s.bind fun a => t.map fun b => a + b).map fun n => E n x).sum := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    rw [Multiset.map_cons, Multiset.sum_cons, add_mul, ih, Multiset.cons_bind,
      Multiset.map_add, Multiset.sum_add, Multiset.map_map]
    congr 1
    rw [← Multiset.sum_map_mul_left]
    congr 1
    apply Multiset.map_congr rfl
    intro b _
    simp [E_add]

lemma good_mul {f g : ℝ → ℂ} (hf : (fun f : ℝ → ℂ => ∃ s : Multiset ℤ, ∀ x, f x = (s.map fun n => E n x).sum) f) (hg : (fun f : ℝ → ℂ => ∃ s : Multiset ℤ, ∀ x, f x = (s.map fun n => E n x).sum) g) : (fun f : ℝ → ℂ => ∃ s : Multiset ℤ, ∀ x, f x = (s.map fun n => E n x).sum) (fun x => f x * g x) := by
  obtain ⟨s, hs⟩ := hf
  obtain ⟨t, ht⟩ := hg
  exact ⟨_, fun x => by show f x * g x = _; rw [hs, ht, msum_mul]⟩

lemma good_pow {f : ℝ → ℂ} (hf : (fun f : ℝ → ℂ => ∃ s : Multiset ℤ, ∀ x, f x = (s.map fun n => E n x).sum) f) (p : ℕ) : (fun f : ℝ → ℂ => ∃ s : Multiset ℤ, ∀ x, f x = (s.map fun n => E n x).sum) (fun x => f x ^ p) := by
  induction p with
  | zero => simpa using good_one
  | succ p ih =>
    simpa [pow_succ] using good_mul ih hf

lemma msum_int (s : Multiset ℤ) :
    ∫ x in (0 : ℝ)..1, (s.map fun n => E n x).sum = ((s.count 0 : ℕ) : ℂ) := by
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    simp only [Multiset.map_cons, Multiset.sum_cons]
    have hc : Continuous fun x => (s.map fun n => E n x).sum := by
      apply continuous_multiset_sum; intro i _; exact E_cont i
    rw [intervalIntegral.integral_add ((E_cont a).intervalIntegrable _ _)
      (hc.intervalIntegrable _ _), ih, E_int, Multiset.count_cons]
    by_cases h : a = 0
    · subst h; simp; ring
    · simp [h, Ne.symm h]

lemma good_int {f : ℝ → ℂ} (hf : (fun f : ℝ → ℂ => ∃ s : Multiset ℤ, ∀ x, f x = (s.map fun n => E n x).sum) f) : ∃ N : ℕ, ∫ x in (0 : ℝ)..1, f x = N := by
  obtain ⟨s, hs⟩ := hf
  exact ⟨_, by simp_rw [hs]; exact msum_int s⟩

lemma G_eq (L : ℕ) (x : ℝ) :
    LeanLab.Linnik.Decomp1536a.Gpow L x = ∑ k ∈ range L, E (2 ^ k) x := by
  unfold LeanLab.Linnik.Decomp1536a.Gpow E; push_cast; rfl

lemma good_G (L : ℕ) : (fun f : ℝ → ℂ => ∃ s : Multiset ℤ, ∀ x, f x = (s.map fun n => E n x).sum) (LeanLab.Linnik.Decomp1536a.Gpow L) := by
  refine ⟨(range L).val.map fun k => (2 : ℤ) ^ k, fun x => ?_⟩
  rw [G_eq, Multiset.map_map, Finset.sum_eq_multiset_sum]; rfl

lemma good_Gc (L : ℕ) : (fun f : ℝ → ℂ => ∃ s : Multiset ℤ, ∀ x, f x = (s.map fun n => E n x).sum) (fun x => (starRingEnd ℂ) (LeanLab.Linnik.Decomp1536a.Gpow L x)) := by
  refine ⟨(range L).val.map fun k => -(2 : ℤ) ^ k, fun x => ?_⟩
  show (starRingEnd ℂ) (LeanLab.Linnik.Decomp1536a.Gpow L x) = _
  rw [G_eq, map_sum, Multiset.map_map, Finset.sum_eq_multiset_sum]
  simp only [E_conj]; rfl

lemma G_cont (L : ℕ) : Continuous (LeanLab.Linnik.Decomp1536a.Gpow L) := by
  unfold LeanLab.Linnik.Decomp1536a.Gpow; fun_prop

lemma S_re (L : ℕ) (x : ℝ) : LeanLab.Linnik.Decomp1536a.Spow L x = (LeanLab.Linnik.Decomp1536a.Gpow L x).re := by
  unfold LeanLab.Linnik.Decomp1536a.Spow LeanLab.Linnik.Decomp1536a.Gpow
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [show (2 * π * Complex.I * ((2 : ℂ) ^ k * x)) = ((2 * π * ((2 : ℝ) ^ k * x) : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  rw [Complex.exp_ofReal_mul_I_re]

lemma twoS (L : ℕ) (x : ℝ) : ((2 * LeanLab.Linnik.Decomp1536a.Spow L x : ℝ) : ℂ) =
    LeanLab.Linnik.Decomp1536a.Gpow L x + (starRingEnd ℂ) (LeanLab.Linnik.Decomp1536a.Gpow L x) := by
  rw [Complex.add_conj, S_re]

lemma normpow (z : ℂ) (j : ℕ) : ((‖z‖ ^ (2 * j) : ℝ) : ℂ) = z ^ j * (starRingEnd ℂ z) ^ j := by
  rw [← mul_pow, Complex.mul_conj, pow_mul, Complex.sq_norm]; push_cast; rfl

lemma Ipq (L p q : ℕ) : ∃ N : ℕ, ∫ x in (0 : ℝ)..1,
    LeanLab.Linnik.Decomp1536a.Gpow L x ^ p * (starRingEnd ℂ) (LeanLab.Linnik.Decomp1536a.Gpow L x) ^ q = N :=
  good_int (good_mul (good_pow (good_G L) p) (good_pow (good_Gc L) q))

end FiniteFourier

open FiniteFourier in
theorem moment_binom (L j : ℕ) :
    (Nat.centralBinom j : ℝ) / 4 ^ j * ∫ x in (0 : ℝ)..1, ‖LeanLab.Linnik.Decomp1536a.Gpow L x‖ ^ (2 * j) ≤
      ∫ x in (0 : ℝ)..1, LeanLab.Linnik.Decomp1536a.Spow L x ^ (2 * j) := by
  choose N hN using Ipq L
  set G := LeanLab.Linnik.Decomp1536a.Gpow L
  have hGc : Continuous G := G_cont L
  have hGcc : Continuous fun x => (starRingEnd ℂ) (G x) := by fun_prop
  -- integral of |G|^{2j}
  have h1 : ∫ x in (0 : ℝ)..1, ‖G x‖ ^ (2 * j) = (N j j : ℝ) := by
    apply Complex.ofReal_injective
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [normpow]
    rw [hN]; simp
  -- integral of (2S)^{2j}
  have h2 : ∫ x in (0 : ℝ)..1, (2 * LeanLab.Linnik.Decomp1536a.Spow L x) ^ (2 * j) =
      ∑ k ∈ range (2 * j + 1), (N k (2 * j - k) : ℝ) * ((2 * j).choose k : ℝ) := by
    apply Complex.ofReal_injective
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [Complex.ofReal_pow, twoS, add_pow]
    rw [intervalIntegral.integral_finsetSum]
    · push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [intervalIntegral.integral_mul_const, hN]
    · intro k _
      apply Continuous.intervalIntegrable
      exact ((hGc.pow _).mul (hGcc.pow _)).mul continuous_const
  have h3 : ∫ x in (0 : ℝ)..1, (2 * LeanLab.Linnik.Decomp1536a.Spow L x) ^ (2 * j) =
      4 ^ j * ∫ x in (0 : ℝ)..1, LeanLab.Linnik.Decomp1536a.Spow L x ^ (2 * j) := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x
    rw [mul_pow, pow_mul]; norm_num
  have h4 : (N j j : ℝ) * ((2 * j).choose j : ℝ) ≤
      ∑ k ∈ range (2 * j + 1), (N k (2 * j - k) : ℝ) * ((2 * j).choose k : ℝ) := by
    have := Finset.single_le_sum (f := fun k => (N k (2 * j - k) : ℝ) * ((2 * j).choose k : ℝ))
      (fun k _ => by positivity) (show j ∈ range (2 * j + 1) by simp; omega)
    simpa [show 2 * j - j = j by omega] using this
  rw [h1]
  have h4' : (0 : ℝ) < 4 ^ j := by positivity
  rw [div_mul_eq_mul_div, div_le_iff₀ h4', mul_comm _ ((4 : ℝ) ^ j), ← h3, h2,
    Nat.centralBinom_eq_two_mul_choose, mul_comm]
  exact h4


open FiniteFourier in
theorem moment_SL_nonneg (L n : ℕ) : 0 ≤ ∫ x in (0 : ℝ)..1, LeanLab.Linnik.Decomp1536a.Spow L x ^ n := by
  choose N hN using Ipq L
  set G := LeanLab.Linnik.Decomp1536a.Gpow L
  have hGc : Continuous G := G_cont L
  have hGcc : Continuous fun x => (starRingEnd ℂ) (G x) := by fun_prop
  have h2 : ∫ x in (0 : ℝ)..1, (2 * LeanLab.Linnik.Decomp1536a.Spow L x) ^ n =
      ∑ k ∈ range (n + 1), (N k (n - k) : ℝ) * (n.choose k : ℝ) := by
    apply Complex.ofReal_injective
    rw [← intervalIntegral.integral_ofReal]
    simp_rw [Complex.ofReal_pow, twoS, add_pow]
    rw [intervalIntegral.integral_finsetSum]
    · push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [intervalIntegral.integral_mul_const, hN]
    · intro k _
      apply Continuous.intervalIntegrable
      exact ((hGc.pow _).mul (hGcc.pow _)).mul continuous_const
  have h3 : ∫ x in (0 : ℝ)..1, (2 * LeanLab.Linnik.Decomp1536a.Spow L x) ^ n =
      2 ^ n * ∫ x in (0 : ℝ)..1, LeanLab.Linnik.Decomp1536a.Spow L x ^ n := by
    rw [← intervalIntegral.integral_const_mul]
    congr 1; funext x
    rw [mul_pow]
  have h4 : (0 : ℝ) ≤ ∑ k ∈ range (n + 1), (N k (n - k) : ℝ) * (n.choose k : ℝ) := by
    positivity
  rw [← h2, h3] at h4
  exact nonneg_of_mul_nonneg_right (by linarith) (by positivity : (0 : ℝ) < 2 ^ n) |> fun h => h


namespace Taylor

noncomputable def T (N : ℕ) (y : ℝ) : ℝ := ∑ n ∈ range N, y ^ n / (n.factorial : ℝ)

lemma hasDerivAt_T (N : ℕ) (y : ℝ) : HasDerivAt (T (N + 1)) (T N y) y := by
  induction N with
  | zero =>
    have : T 1 = fun _ => 1 := by funext z; simp [T]
    rw [this]; simpa [T] using hasDerivAt_const y (1 : ℝ)
  | succ N ih =>
    have h1 : T (N + 2) = fun z => T (N + 1) z + z ^ (N + 1) / ((N + 1).factorial : ℝ) := by
      funext z; simp only [T]; rw [sum_range_succ]
    have hp : HasDerivAt (fun z : ℝ => z ^ (N + 1) / ((N + 1).factorial : ℝ))
        (((N + 1 : ℕ) : ℝ) * y ^ N / ((N + 1).factorial : ℝ)) y := by
      have := (hasDerivAt_pow (N + 1) y).div_const ((N + 1).factorial : ℝ)
      simpa using this
    rw [h1]
    refine (ih.add hp).congr_deriv ?_
    unfold T; rw [sum_range_succ (n := N)]
    congr 1
    rw [Nat.factorial_succ]; push_cast
    have : (N.factorial : ℝ) ≠ 0 := by positivity
    field_simp

lemma T_zero (N : ℕ) : T (N + 1) 0 = 1 := by
  simp only [T]
  rw [sum_range_succ']
  simp

lemma neg_case (N : ℕ) : ∀ y ≤ 0, 0 ≤ (-1 : ℝ) ^ N * (exp y - T N y) := by
  induction N with
  | zero => intro y _; simp [T]; positivity
  | succ N ih =>
    intro y hy
    set g : ℝ → ℝ := fun z => (-1 : ℝ) ^ (N + 1) * (exp z - T (N + 1) z) with hg
    have hd : ∀ z, HasDerivAt g ((-1 : ℝ) ^ (N + 1) * (exp z - T N z)) z := fun z =>
      ((Real.hasDerivAt_exp z).sub (hasDerivAt_T N z)).const_mul _
    have hanti : AntitoneOn g (Set.Iic 0) := by
      apply antitoneOn_of_deriv_nonpos (convex_Iic 0)
      · exact (continuous_iff_continuousAt.2 fun z => (hd z).continuousAt).continuousOn
      · exact fun z _ => (hd z).differentiableAt.differentiableWithinAt
      · intro z hz
        rw [(hd z).deriv]
        rw [interior_Iic] at hz
        have := ih z (le_of_lt hz)
        rw [pow_succ]; nlinarith
    have h0 : g 0 = 0 := by simp [hg, T_zero]
    have := hanti (Set.mem_Iic.2 hy) (Set.mem_Iic.2 le_rfl) hy
    rw [h0] at this; exact this

lemma T_le_exp (m : ℕ) (y : ℝ) : T (2 * m) y ≤ exp y := by
  rcases le_total 0 y with h | h
  · exact Real.sum_le_exp_of_nonneg h _
  · have := neg_case (2 * m) y h
    rw [pow_mul] at this; norm_num at this; linarith

lemma split_sum (a : ℕ → ℝ) (ha : ∀ j, 0 ≤ a (2 * j + 1)) (K : ℕ) :
    ∑ j ∈ range K, a (2 * j) ≤ ∑ n ∈ range (2 * K), a n := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, show 2 * (K + 1) = 2 * K + 1 + 1 by ring, sum_range_succ,
      sum_range_succ]
    linarith [ha K]

end Taylor

theorem even_partial_le_int_exp {f : ℝ → ℝ} (hf : Continuous f)
    (hmom : ∀ n : ℕ, 0 ≤ ∫ x in (0 : ℝ)..1, f x ^ n) {lam : ℝ} (hlam : 0 ≤ lam) (K : ℕ) :
    ∑ j ∈ range K, lam ^ (2 * j) / ((2 * j).factorial : ℝ) * ∫ x in (0 : ℝ)..1, f x ^ (2 * j) ≤
      ∫ x in (0 : ℝ)..1, Real.exp (lam * f x) := by
  set a : ℕ → ℝ := fun n => lam ^ n / (n.factorial : ℝ) * ∫ x in (0 : ℝ)..1, f x ^ n with ha
  have h1 : ∑ j ∈ range K, a (2 * j) ≤ ∑ n ∈ range (2 * K), a n :=
    Taylor.split_sum a (fun j => mul_nonneg (by positivity) (hmom _)) K
  have h2 : ∑ n ∈ range (2 * K), a n = ∫ x in (0 : ℝ)..1, Taylor.T (2 * K) (lam * f x) := by
    simp only [Taylor.T]
    rw [intervalIntegral.integral_finsetSum]
    · refine sum_congr rfl fun n _ => ?_
      simp only [ha]
      rw [← intervalIntegral.integral_const_mul]
      congr 1; funext x; rw [mul_pow]; ring
    · intro n _
      exact ((hf.const_mul lam).pow n |>.div_const _).intervalIntegrable _ _
  have h3 : ∫ x in (0 : ℝ)..1, Taylor.T (2 * K) (lam * f x) ≤ ∫ x in (0 : ℝ)..1, exp (lam * f x) := by
    apply intervalIntegral.integral_mono_on zero_le_one
    · simp only [Taylor.T]
      exact (continuous_finsetSum _ fun n _ =>
        ((hf.const_mul lam).pow n).div_const _).intervalIntegrable _ _
    · exact (Real.continuous_exp.comp (hf.const_mul lam)).intervalIntegrable _ _
    · intro x _; exact Taylor.T_le_exp K _
  have : ∑ j ∈ range K, lam ^ (2 * j) / ((2 * j).factorial : ℝ) *
      ∫ x in (0 : ℝ)..1, f x ^ (2 * j) = ∑ j ∈ range K, a (2 * j) := rfl
  rw [this]; linarith

end LeanLab.Ported.Prove2Me.Linnik1536a
