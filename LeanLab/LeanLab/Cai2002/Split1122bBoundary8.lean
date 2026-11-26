/-
Split of the LEAFs leaf8_F3 and leaf8_f2 of Split1122bSeries8.lean: the boundary values
F(3) = 2 e ^ γ / 3 and f(2) = 0 of the series solution of Nathanson Theorem 9.4, as quoted
by Bordignon, Johnston and Starichkova, arXiv 2207.09452v6, papers/P0009.pdf, page 6,
displays 8 and 13 to 18.

Write O(s) for the sum of f_n(s) over odd n, the series 13, and E(s) for the sum over even
n, the series 14, so F = 1 + O and f = 1 - E. Nathanson's argument, Theorem 9.4 with the
adjoint function method of the linear sieve, splits into:
* f(2) = 0. Q = F - f = O + E solves (s Q(s))' = - Q(s - 1) for s > 3, whose adjoint
  function is s - 1, so I(s) = s (s - 1) Q(s) - the integral of t Q(t) over [s - 1, s]
  is constant for s ≥ 3; it tends to 0 since Q decays like h(s) by display 18; and
  I(3) = 2 E(2) - 2 by display 17 and display 16 on [2, 3]. Hence E(2) = 1.
* F(3) = 2 e ^ γ / 3. P = F + f = 2 + O - E solves (s P(s))' = P(s - 1) for s > 3. With
  an adjoint function q, s q'(s) = - q(s + 1) and s q(s) → 1, the quantity
  J(s) = s q(s) P(s) + the integral of P(t) q(t + 1) over [s - 1, s] is constant for
  s ≥ 3 and tends to 2. On [2, 3], with f(2) = 0, P(t) = A (1 + log (t - 1)) / t with
  A = 3 (1 + O(3)), so J(3) = A K(q). The Mertens type constant enters through
  K(q) = e ^ -γ for q(s) = the integral over x > 0 of exp (- s x - Ein x).
The final algebra is proved here; the analytic pieces are LEAFs.
Numerical check, AI written Python, grid step 0.001, 90 terms: the odd sum at 3 is
0.1873818 against 2 e ^ γ / 3 - 1 = 0.1873816, the even sum at 2 is 1.0000004,
f_2(2) = 0.647919, and K(q) = 0.5614595 against e ^ -γ = 0.5614595.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Cai2002.Prove1122bDerivEven8

open Finset Real

noncomputable section

namespace LeanLab.Cai2002

/-- O(s), the sum of the series 13 of BJS page 6 over odd n: F(s) = 1 + O(s). -/
def oSumB8 (s : ℝ) : ℝ := ∑' n : ℕ, if Odd n then bjsF306 n s else 0

/-- E(s), the sum of the series 14 of BJS page 6 over even n: f(s) = 1 - E(s). -/
def eSumB8 (s : ℝ) : ℝ := ∑' n : ℕ, if Even n then bjsF306 n s else 0

/-- The invariant of Q = F - f = O + E with adjoint function s - 1:
I(s) = s (s - 1) Q(s) - the integral of t Q(t) over [s - 1, s]. -/
def qInvB8 (s : ℝ) : ℝ :=
  s * (s - 1) * (oSumB8 s + eSumB8 s) - ∫ t in (s - 1)..s, t * (oSumB8 t + eSumB8 t)

/-- P = F + f = 2 + O - E. -/
def pSumB8 (s : ℝ) : ℝ := 2 + oSumB8 s - eSumB8 s

/-- The adjoint system of (s P(s))' = P(s - 1): s q'(s) = - q(s + 1) for s > 0, normalized by
s q(s) → 1 as s → ∞. -/
def IsAdjB8 (q : ℝ → ℝ) : Prop :=
  (∀ s : ℝ, 0 < s → HasDerivAt q (-q (s + 1) / s) s) ∧
    Filter.Tendsto (fun s => s * q s) Filter.atTop (nhds 1)

/-- The invariant of P with adjoint q: J(s) = s q(s) P(s) + the integral of P(t) q(t + 1)
over [s - 1, s]. -/
def jInvB8 (q : ℝ → ℝ) (s : ℝ) : ℝ :=
  s * q s * pSumB8 s + ∫ t in (s - 1)..s, pSumB8 t * q (t + 1)

/-- The constant K(q) = q(3) (1 + log 2) + the integral over [2, 3] of
(1 + log (t - 1)) q(t + 1) / t, which J(3) equals divided by A = F(3) 3. -/
def kConstB8 (q : ℝ → ℝ) : ℝ :=
  q 3 * (1 + log 2) + ∫ t in (2 : ℝ)..3, (1 + log (t - 1)) * q (t + 1) / t

/-- The entire exponential integral used in the adjoint construction. -/
def einB8 (x : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..x, (1 - exp (-u)) / u

/-- The Laplace transform of `exp (-einB8 x)`. -/
def adjB8 (s : ℝ) : ℝ :=
  ∫ x in Set.Ioi 0, exp (-s * x - einB8 x)

/-- LEAF: Nathanson Theorem 9.4, adjoint function method for Q = F - f, BJS page 6 displays
8, 13 and 14: by display 16 for even n and displays 16, 17 for odd n, summed as in
leaf8_deriv_even and leaf8_deriv_odd, (s Q(s))' = - Q(s - 1) for s > 3, so with the adjoint
function s - 1 the derivative of I vanishes on (3, ∞) and I is constant on [3, ∞) by
continuity of the sums. Class MEDIUM: FTC for the parameter integral plus the termwise
derivatives already proved or split. -/
theorem leafB8_IQ_const (s : ℝ) (hs : 3 ≤ s) : qInvB8 s = qInvB8 3 := by
  sorry

/-- LEAF: Nathanson Theorem 9.4, F(s), f(s) → 1 at infinity, BJS display 18 with Lemma 8:
0 ≤ O(s) + E(s) ≤ C h(s) with h(s) = 3 e ^ -s / s for s > 3, so s ^ 2 Q(s) and the integral
of t Q(t) over [s - 1, s] tend to 0. Class MEDIUM: the bound key_l8306 summed, then
exponential decay beats s ^ 2. -/
theorem leafB8_IQ_tendsto : Filter.Tendsto qInvB8 Filter.atTop (nhds 0) := by
  sorry

/-- LEAF: Nathanson Theorem 9.4 on [2, 3], BJS displays 16 and 17: O(t) = A / t - 1 on
[1, 3] with A = 3 (1 + O(3)) by display 17, and s E(s) = 2 E(2) - A log (s - 1) + s - 2 on
[2, 3] by display 16 summed, leaf8_deriv_even, with continuity at 2; then
I(3) = 2 E(2) - 2, the A terms cancelling. Class MEDIUM: FTC on [2, 3] and the integral of
log. -/
theorem leafB8_IQ3 : qInvB8 3 = 2 * eSumB8 2 - 2 := by
  sorry

/-- f(2) = 0 for the series 14: E(2) = 1. Proved from the three LEAFs above: I is constant
on [3, ∞) and tends to 0, so I(3) = 0 = 2 E(2) - 2. -/
theorem eSumB8_two : eSumB8 2 = 1 := by
  have hev : qInvB8 =ᶠ[Filter.atTop] fun _ => qInvB8 3 :=
    Filter.eventually_atTop.2 ⟨3, fun s hs => leafB8_IQ_const s hs⟩
  have h1 : Filter.Tendsto qInvB8 Filter.atTop (nhds (qInvB8 3)) :=
    tendsto_const_nhds.congr' hev.symm
  have h0 : qInvB8 3 = 0 := tendsto_nhds_unique h1 leafB8_IQ_tendsto
  have h3 := leafB8_IQ3
  linarith

/-- The series 13 and 14 converge where used, from the PROVED bound 18 with Lemma 8,
key_l8306 with c_n = 0.9607, and leaf306_fn_nonneg; a geometric comparison. -/
theorem parity_summableB8 (P : ℕ → Prop) [DecidablePred P] (s : ℝ)
    (hP : ∀ n, P n → (Odd n ∧ 1 ≤ s) ∨ (Even n ∧ 2 ≤ s)) (hs : 0 ≤ s) :
    Summable (fun n : ℕ => if P n then bjsF306 n s else 0) := by
  rw [← summable_nat_add_iff 1]
  have hh := hSieve_nonneg306 s hs
  set C := 2 * exp 2 * LeanLab.ChenExplicit.hSieve s with hC
  refine Summable.of_nonneg_of_le (fun k => ?_) (fun k => ?_)
    ((summable_geometric_of_lt_one (by norm_num : (0 : ℝ) ≤ 0.9607) (by norm_num)).mul_left C)
  · split_ifs with h
    · exact leaf306_fn_nonneg _ s (hP _ h)
    · exact le_rfl
  · split_ifs with h
    · have := key_l8306 (k + 1) (by omega) s (hP _ h)
      rw [show k + 1 - 1 = k by omega] at this
      rw [hC]
      linarith
    · positivity

/-- Twin of leaf8_f2 of Split1122bSeries8.lean, statement copied verbatim. -/
theorem leaf8_f2_twin :
    HasSum (fun n : ℕ => if Even n then bjsF306 n 2 else 0) 1 := by
  convert (parity_summableB8 Even 2 (fun _ h => Or.inr ⟨h, le_rfl⟩) (by norm_num)).hasSum using 1
  exact eSumB8_two.symm

/-- LEAF: the adjoint function of the linear sieve, Nathanson Theorem 9.4 and the Mertens
type constant: q(s) = the integral over x > 0 of exp (- s x - Ein x), with
Ein x = the integral over [0, x] of (1 - e ^ -u) / u, satisfies s q'(s) = - q(s + 1) by
parts, s q(s) → 1 by Laplace, and K(q) = e ^ -γ through the integral of e ^ -t / t, that is
Ein x = log x + γ + E_1(x). Numerically K(q) = 0.5614595. Class HARD: Laplace transform
identities and γ as a limit of the exponential integral. -/
theorem leafB8_adjoint :
    ∃ q : ℝ → ℝ, IsAdjB8 q ∧ kConstB8 q = exp (-eulerMascheroniConstant) := by
  refine ⟨adjB8, ⟨?_, ?_⟩, ?_⟩
  · intro s hs
    refine ?_
  · filter_upwards [] with s hs
    exact ?_
  · refine ?_

/-- LEAF: Nathanson Theorem 9.4, adjoint method for P = F + f: (s P(s))' = P(s - 1) for
s > 3 from leaf8_deriv_even and leaf8_deriv_odd, so with s q' = - q(s + 1) the derivative of
J vanishes on (3, ∞) and J is constant on [3, ∞). Class MEDIUM. -/
theorem leafB8_J_const (q : ℝ → ℝ) (hq : IsAdjB8 q) (s : ℝ) (hs : 3 ≤ s) :
    jInvB8 q s = jInvB8 q 3 := by
  sorry

/-- LEAF: Nathanson Theorem 9.4, F, f → 1 at infinity: P(s) → 2 by display 18, s q(s) → 1,
and q(t + 1) → 0 uniformly on [s - 1, s], so J(s) → 2. Class MEDIUM. -/
theorem leafB8_J_tendsto (q : ℝ → ℝ) (hq : IsAdjB8 q) :
    Filter.Tendsto (jInvB8 q) Filter.atTop (nhds 2) := by
  sorry

/-- LEAF: Nathanson Theorem 9.4 on [2, 3], BJS displays 16 and 17: with f(2) = 0, that is
E(2) = 1, O(t) = A / t - 1 and t E(t) = 2 - A log (t - 1) + t - 2, so
P(t) = A (1 + log (t - 1)) / t on [2, 3] and J(3) = A K(q), A = 3 (1 + O(3)).
Class MEDIUM: FTC on [2, 3] as in leafB8_IQ3. -/
theorem leafB8_J3 (q : ℝ → ℝ) (hq : IsAdjB8 q) (he : eSumB8 2 = 1) :
    jInvB8 q 3 = 3 * (1 + oSumB8 3) * kConstB8 q := by
  sorry

/-- F(3) = 2 e ^ γ / 3: O(3) = 2 e ^ γ / 3 - 1. Proved from the LEAFs: J(3) = 2 since J is
constant and tends to 2, J(3) = A K(q) and K(q) = e ^ -γ. -/
theorem oSumB8_three : oSumB8 3 = 2 * exp eulerMascheroniConstant / 3 - 1 := by
  obtain ⟨q, hq, hK⟩ := leafB8_adjoint
  have hev : jInvB8 q =ᶠ[Filter.atTop] fun _ => jInvB8 q 3 :=
    Filter.eventually_atTop.2 ⟨3, fun s hs => leafB8_J_const q hq s hs⟩
  have h1 : Filter.Tendsto (jInvB8 q) Filter.atTop (nhds (jInvB8 q 3)) :=
    tendsto_const_nhds.congr' hev.symm
  have h2 : jInvB8 q 3 = 2 := tendsto_nhds_unique h1 (leafB8_J_tendsto q hq)
  rw [leafB8_J3 q hq eSumB8_two, hK] at h2
  have hE : exp (-eulerMascheroniConstant) * exp eulerMascheroniConstant = 1 := by
    rw [← exp_add]; simp
  have h3 : 3 * (1 + oSumB8 3) = 2 * exp eulerMascheroniConstant := by
    calc 3 * (1 + oSumB8 3)
        = 3 * (1 + oSumB8 3) * (exp (-eulerMascheroniConstant) *
            exp eulerMascheroniConstant) := by rw [hE, mul_one]
      _ = 2 * exp eulerMascheroniConstant := by rw [← mul_assoc, h2]
  linarith

/-- Twin of leaf8_F3 of Split1122bSeries8.lean, statement copied verbatim. -/
theorem leaf8_F3_twin :
    HasSum (fun n : ℕ => if Odd n then bjsF306 n 3 else 0)
      (2 * exp eulerMascheroniConstant / 3 - 1) := by
  convert (parity_summableB8 Odd 3 (fun _ h => Or.inl ⟨h, by norm_num⟩) (by norm_num)).hasSum using 1
  exact oSumB8_three.symm

end LeanLab.Cai2002

#print axioms LeanLab.Cai2002.parity_summableB8
#print axioms LeanLab.Cai2002.leaf8_F3_twin
#print axioms LeanLab.Cai2002.leaf8_f2_twin
