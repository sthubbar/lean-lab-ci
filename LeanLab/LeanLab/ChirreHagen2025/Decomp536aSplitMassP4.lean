import LeanLab.ChirreHagen2025.Decomp536aSplitMassP2

/-!
Split of the LEAF `Decomp536aSplitMassP2.high_inverse_square_mass`, burst-20261122,
session S132. Ramare 2013 page 118 Lemma 4.2.
The tail of the sum of 1/gamma ^ 2 above T0 = 2.44 * 10 ^ 12 is cut into dyadic shells
2 ^ k T0 < |gamma| <= 2 ^ (k + 1) T0. The cited input is a zero count on one shell,
at most T log T zeros with T < |gamma| <= 2 T, counted with multiplicity and both signs of
gamma, a weak consequence of the Riemann von Mangoldt formula N(T) = T/(2 pi) log(T/(2 pi e))
plus O(log T). The shell k then contributes at most log X/X with X = 2 ^ k T0, and these are
summed by induction on the number of shells against the telescoping bound
0.0008 - 0.0008 (3/4) ^ K.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp536aSplitMassP4

open Real

/-- LEAF: Ramare 2013 page 118 Lemma 4.2 input, the Riemann von Mangoldt zero count on a
dyadic shell: for T >= 2.44 * 10 ^ 12, the nontrivial zeros with T < |gamma| <= 2 T, counted
with multiplicity, number at most T log T. The true count is about (T/pi) log T, from
N(2T) - N(T) for both signs of gamma. Needs an explicit Riemann von Mangoldt bound,
Trudgian 2014 or Rosser 1941, not in Mathlib. Class HARD. -/
theorem shell_zero_count (T : ℝ) (hT : 2.44 * 10 ^ 12 ≤ T) (s : Finset ℂ)
    (hs : ∀ z ∈ s, riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ T < |z.im| ∧ |z.im| ≤ 2 * T) :
    (∑ z ∈ s, (analyticOrderNatAt riemannZeta z : ℝ)) ≤ T * Real.log T := by
  sorry

/-- Proved: log (2.44 * 10 ^ 12) <= 29. -/
theorem log_T0_le : Real.log (2.44 * 10 ^ 12) ≤ 29 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : (2.7 : ℝ) ≤ exp 1 := by linarith [exp_one_gt_d9]
  have h2 : (2.7 : ℝ) ^ 29 ≤ exp 1 ^ 29 := pow_le_pow_left₀ (by norm_num) h1 29
  rw [← Real.exp_nat_mul] at h2
  norm_num at h2 ⊢
  linarith

/-- Proved: the shell bound log X/X <= 0.0002 (3/4) ^ K for X = 2 ^ K * 2.44 * 10 ^ 12. -/
theorem shell_term_le (K : ℕ) :
    Real.log (2 ^ K * (2.44 * 10 ^ 12)) / (2 ^ K * (2.44 * 10 ^ 12)) ≤
      0.0002 * (3 / 4 : ℝ) ^ K := by
  have hX : (0 : ℝ) < 2 ^ K * (2.44 * 10 ^ 12) := by positivity
  rw [div_le_iff₀ hX]
  have hlog : Real.log (2 ^ K * (2.44 * 10 ^ 12)) ≤ K + 29 := by
    rw [Real.log_mul (by positivity) (by norm_num), Real.log_pow]
    have := log_T0_le
    have h2 : Real.log 2 ≤ 1 := by linarith [Real.log_two_lt_d9]
    have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
    nlinarith
  have hpow : (3 / 4 : ℝ) ^ K * 2 ^ K = (3 / 2) ^ K := by
    rw [← mul_pow]; norm_num
  have hb : 1 + (K : ℝ) * (1 / 2) ≤ (3 / 2 : ℝ) ^ K := by
    have := one_add_mul_le_pow (a := (1 / 2 : ℝ)) (by norm_num) K
    norm_num at this ⊢
    linarith
  have : 0.0002 * (3 / 4 : ℝ) ^ K * (2 ^ K * (2.44 * 10 ^ 12)) =
      0.0002 * (2.44 * 10 ^ 12) * (3 / 2) ^ K := by
    rw [← hpow]; ring
  rw [this]
  have hK : (0 : ℝ) ≤ K := Nat.cast_nonneg K
  nlinarith

/-- Proved from the LEAF: the mass of zeros with T0 < |gamma| <= 2 ^ K T0 is at most
0.0008 - 0.0008 (3/4) ^ K, by induction on K. CONDITIONAL ON `shell_zero_count`. -/
theorem mass_le_of_bounded (K : ℕ) (s : Finset ℂ)
    (hs : ∀ z ∈ s, riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ 2.44 * 10 ^ 12 < |z.im| ∧
      |z.im| ≤ 2 ^ K * (2.44 * 10 ^ 12)) :
    (∑ z ∈ s, (analyticOrderNatAt riemannZeta z : ℝ) / z.im ^ 2) ≤
      0.0008 - 0.0008 * (3 / 4 : ℝ) ^ K := by
  induction K generalizing s with
  | zero =>
    have hs0 : s = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro z hz
      have h := hs z hz
      simp at h
      linarith [h.2.2.2.1, h.2.2.2.2]
    subst hs0
    norm_num
  | succ K ih =>
    set X : ℝ := 2 ^ K * (2.44 * 10 ^ 12) with hXdef
    have hX0 : 2.44 * 10 ^ 12 ≤ X := by
      have : (1 : ℝ) ≤ 2 ^ K := one_le_pow₀ (by norm_num)
      rw [hXdef]; nlinarith
    rw [← Finset.sum_filter_add_sum_filter_not s (fun z : ℂ => |z.im| ≤ X)]
    have h1 := ih (s.filter (fun z : ℂ => |z.im| ≤ X)) (fun z hz => by
      rw [Finset.mem_filter] at hz
      exact ⟨(hs z hz.1).1, (hs z hz.1).2.1, (hs z hz.1).2.2.1, (hs z hz.1).2.2.2.1, hz.2⟩)
    set r := s.filter (fun z : ℂ => ¬ |z.im| ≤ X) with hr
    have hrmem : ∀ z ∈ r, riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ X < |z.im| ∧
        |z.im| ≤ 2 * X := by
      intro z hz
      rw [hr, Finset.mem_filter] at hz
      have h := hs z hz.1
      refine ⟨h.1, h.2.1, h.2.2.1, lt_of_not_ge hz.2, ?_⟩
      have := h.2.2.2.2
      rw [hXdef, pow_succ] at *
      linarith
    have hcount := shell_zero_count X hX0 r hrmem
    have hXpos : 0 < X := by linarith
    have h2 : (∑ z ∈ r, (analyticOrderNatAt riemannZeta z : ℝ) / z.im ^ 2) ≤
        (∑ z ∈ r, (analyticOrderNatAt riemannZeta z : ℝ)) / X ^ 2 := by
      rw [Finset.sum_div]
      apply Finset.sum_le_sum
      intro z hz
      have hlt := (hrmem z hz).2.2.2.1
      have hsq : X ^ 2 ≤ z.im ^ 2 := by
        rw [← sq_abs z.im]
        exact pow_le_pow_left₀ hXpos.le hlt.le 2
      exact div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) hsq
    have h3 : (∑ z ∈ r, (analyticOrderNatAt riemannZeta z : ℝ)) / X ^ 2 ≤
        Real.log X / X := by
      rw [div_le_div_iff₀ (by positivity) hXpos]
      have : X * Real.log X * X = Real.log X * X ^ 2 := by ring
      nlinarith
    have h4 := shell_term_le K
    rw [← hXdef] at h4
    have h5 : 0.0008 - 0.0008 * (3 / 4 : ℝ) ^ (K + 1) =
        (0.0008 - 0.0008 * (3 / 4 : ℝ) ^ K) + 0.0002 * (3 / 4 : ℝ) ^ K := by
      rw [pow_succ]; ring
    rw [h5]
    linarith

/-- Exact statement of `Decomp536aSplitMassP2.high_inverse_square_mass`.
CONDITIONAL ON `shell_zero_count`. -/
theorem high_inverse_square_mass_of_leaves (s : Finset ℂ)
    (hs : ∀ z ∈ s, riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1 ∧ 2.44 * 10 ^ 12 < |z.im|) :
    (∑ z ∈ s, (analyticOrderNatAt riemannZeta z : ℝ) / z.im ^ 2) ≤ 0.0008 := by
  obtain ⟨K, hK⟩ := pow_unbounded_of_one_lt
    ((∑ z ∈ s, |z.im|) / (2.44 * 10 ^ 12)) (by norm_num : (1 : ℝ) < 2)
  have hb : ∀ z ∈ s, |z.im| ≤ 2 ^ K * (2.44 * 10 ^ 12) := by
    intro z hz
    have h1 : |z.im| ≤ ∑ w ∈ s, |w.im| :=
      Finset.single_le_sum (f := fun w : ℂ => |w.im|) (fun w _ => abs_nonneg _) hz
    rw [div_lt_iff₀ (by norm_num)] at hK
    linarith
  have := mass_le_of_bounded K s (fun z hz => ⟨(hs z hz).1, (hs z hz).2.1, (hs z hz).2.2.1,
    (hs z hz).2.2.2, hb z hz⟩)
  have hp : (0 : ℝ) ≤ 0.0008 * (3 / 4 : ℝ) ^ K := by positivity
  linarith

end LeanLab.ChirreHagen2025.Decomp536aSplitMassP4

#print axioms LeanLab.ChirreHagen2025.Decomp536aSplitMassP4.log_T0_le
#print axioms LeanLab.ChirreHagen2025.Decomp536aSplitMassP4.shell_term_le
#print axioms LeanLab.ChirreHagen2025.Decomp536aSplitMassP4.mass_le_of_bounded
#print axioms LeanLab.ChirreHagen2025.Decomp536aSplitMassP4.high_inverse_square_mass_of_leaves
