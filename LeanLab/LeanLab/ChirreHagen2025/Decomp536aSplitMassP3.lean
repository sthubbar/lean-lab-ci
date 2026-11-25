import LeanLab.ChirreHagen2025.Decomp536aSplitMassP2
import LeanLab.ChenExplicit.GammaBounds

/-!
Third split, of the LEAF `Decomp536aSplitMassP2.critical_line_mass`, burst-20261122,
session S132. Ramare 2013 page 118 Lemma 4.3.
The Lemma 4.3 identity, the sum over all nontrivial zeros of 1/(rho (1 - rho)), equivalently
of 2 Re(1/rho) by the symmetry rho to 1 - conj rho, equals 2 + gamma - log 4 pi, with every
term positive. It is kept as one cited LEAF in the form: every finite multiset of nontrivial
zeros has weighted mass of 2 Re(1/rho) at most 2 + gamma - log 4 pi.
Proved here: on the critical line 2 Re(1/rho) = 1/(1/4 + gamma ^ 2), and the numerical bound
2 + gamma - log 4 pi < 0.0462, from the lab bound gamma < 0.57722, log 2 > 0.6931471803 and
log pi > 1.144729.
AI wrote this Lean code. Goldbach is open.
-/
namespace LeanLab.ChirreHagen2025.Decomp536aSplitMassP3

open Real

/-- LEAF: Ramare 2013 page 118 Lemma 4.3: the sum over all nontrivial zeros rho of
zeta, counted with multiplicity, of 1/(rho (1 - rho)) = 2 Re(1/rho) equals
2 + gamma - log 4 pi, and every term is positive since Re(1/rho) = Re rho/|rho| ^ 2 > 0;
hence every finite set of nontrivial zeros has weighted mass of 2 Re(1/rho) at most
2 + gamma - log 4 pi. Needs the Hadamard product of the completed zeta function,
not in Mathlib. Class HARD. -/
theorem lemma43_zero_mass (s : Finset ℂ)
    (hs : ∀ z ∈ s, riemannZeta z = 0 ∧ 0 < z.re ∧ z.re < 1) :
    (∑ z ∈ s, (analyticOrderNatAt riemannZeta z : ℝ) * (2 * (1 / z).re)) ≤
      2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) := by
  sorry

/-- Proved: on the critical line 2 Re(1/rho) = 1/(1/4 + gamma ^ 2). -/
theorem two_re_inv_of_re_half (z : ℂ) (h : z.re = 1 / 2) :
    2 * (1 / z).re = 1 / (1 / 4 + z.im ^ 2) := by
  rw [one_div, Complex.inv_re, Complex.normSq_apply, h]
  have hp : (0 : ℝ) < 1 / 4 + z.im ^ 2 := by positivity
  field_simp
  ring

/-- Proved: log pi > 1.144729. -/
theorem log_pi_gt' : (1.144729 : ℝ) < Real.log Real.pi := by
  rw [Real.lt_log_iff_exp_lt pi_pos]
  have e : exp (1.144729 : ℝ) = exp 1 * exp 0.144729 := by rw [← exp_add]; norm_num
  have h1 := exp_one_lt_d9
  have h2 := Real.exp_bound' (x := (0.144729 : ℝ)) (by norm_num) (by norm_num) (n := 7)
    (by norm_num)
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h2
  norm_num at h2
  have := pi_gt_d6
  rw [e]; nlinarith [exp_pos (0.144729 : ℝ), exp_pos 1]

/-- Proved: 2 + gamma - log 4 pi < 0.0462; true value 0.0461914. -/
theorem lemma43_constant_lt : 2 + Real.eulerMascheroniConstant - Real.log (4 * Real.pi) <
    0.0462 := by
  have hg := LeanLab.ChenExplicit.Gamma.gamma_lt
  have hl2 := Real.log_two_gt_d9
  have hlp := log_pi_gt'
  have h4 : Real.log (4 * Real.pi) = 2 * Real.log 2 + Real.log Real.pi := by
    rw [Real.log_mul (by norm_num) pi_ne_zero,
      show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    push_cast; ring
  rw [h4]
  linarith

/-- Exact statement of `Decomp536aSplitMassP2.critical_line_mass`.
CONDITIONAL ON `lemma43_zero_mass`. -/
theorem critical_line_mass_of_leaves (s : Finset ℂ)
    (hs : ∀ z ∈ s, riemannZeta z = 0 ∧ z.re = 1 / 2) :
    (∑ z ∈ s, (analyticOrderNatAt riemannZeta z : ℝ) / (1 / 4 + z.im ^ 2)) ≤ 0.0462 := by
  have heq : (∑ z ∈ s, (analyticOrderNatAt riemannZeta z : ℝ) / (1 / 4 + z.im ^ 2)) =
      ∑ z ∈ s, (analyticOrderNatAt riemannZeta z : ℝ) * (2 * (1 / z).re) := by
    apply Finset.sum_congr rfl
    intro z hz
    rw [two_re_inv_of_re_half z (hs z hz).2, div_eq_mul_one_div]
  rw [heq]
  have hm := lemma43_zero_mass s (fun z hz => by
    refine ⟨(hs z hz).1, ?_, ?_⟩ <;> rw [(hs z hz).2] <;> norm_num)
  linarith [lemma43_constant_lt]

end LeanLab.ChirreHagen2025.Decomp536aSplitMassP3

#print axioms LeanLab.ChirreHagen2025.Decomp536aSplitMassP3.two_re_inv_of_re_half
#print axioms LeanLab.ChirreHagen2025.Decomp536aSplitMassP3.log_pi_gt'
#print axioms LeanLab.ChirreHagen2025.Decomp536aSplitMassP3.lemma43_constant_lt
#print axioms LeanLab.ChirreHagen2025.Decomp536aSplitMassP3.critical_line_mass_of_leaves
