/-
AI wrote this Lean code, Claude, ROUTE BURST S70, burst-20261122, unit ep2022_split.
Split of the LEAF `ProgressionS63.ep2022_theorem1`, Ernvall-Hytonen and Palojarvi,
arXiv 2003.01925v4, Theorem 1 p. 2, along the paper's own proof in Section 4, pp. 40 to 46:
* `thm3`, LEAF HARD: Theorem 3 p. 3, the GRH bound for psi of x, q, a; the analytic core.
* `lemma31`, LEAF MEDIUM: Lemma 31 pp. 40 to 41, the integral estimate of S from the
  Theorem 3 bound, a real analysis step.
* `display_50_53`, LEAF MEDIUM: the partial summation identities (50) and (53) p. 44.
* `display_51`, `display_52`, LEAF MEDIUM: the bounds (51) and (52) p. 44 from
  Rosser-Schoenfeld 1962 Theorem 13, psi minus theta below 1.42620 sqrt x.
* `final_combination`, LEAF MEDIUM: the simplification on pp. 45 to 46 with Lemmas 11
  and 32, a pure inequality between explicit functions of x and q.
* `ep2022_theorem1_of_leaves`, PROVED: the triangle inequality assembling them into the
  exact statement of `ProgressionS63.ep2022_theorem1`.
The constants were read on the rendered pages 3, 40, 41 and 44 of the arXiv PDF. Note the
term `x^(1/4) log log √x` of Lemma 31, which the text extraction drops to `log log x`.
A Python check of `final_combination` over q from 3 to 10^40 and x/q from 1 to 10^80 found
slack at least 154.
Binary Goldbach is open.
-/
import LeanLab.BS2022GRH.ChenThresholdGRH

namespace LeanLab.BS2022GRH.ProgressionEPS70
open Real Finset Classical ChenThresholdGRH
noncomputable section

/-- psi of x, q, a of EP2022 p. 44: the sum of the von Mangoldt function over
`n ≤ x` with `n ≡ a mod q`. -/
def psiAP (q a : ℕ) (x : ℝ) : ℝ :=
  ∑ n ∈ (Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q), (ArithmeticFunction.vonMangoldt n : ℝ)

/-- theta of x, q, a of EP2022 p. 44: the sum of `log p` over primes `p ≤ x`,
`p ≡ a mod q`. -/
def thetaAP (q a : ℕ) (x : ℝ) : ℝ :=
  ∑ p ∈ (range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % q = a % q), log p

/-- `R₁(q)` of EP2022 Theorem 3 p. 3, three cases of q. -/
def R1 (q : ℕ) : ℝ :=
  if (q : ℝ) < 4 * 10 ^ 5 then
    0.014 * √(q : ℝ) * log q + 0.034 * √(q : ℝ) + 3.679 * log q + 263.886
  else if (q : ℝ) < 10 ^ 29 then 1.858 * log q ^ 2 + 3.679 * log q + 104.626
  else (0.297 * log (log q) + 0.603) * log q ^ 2 + 3.679 * log q + 104.626

/-- The right side of EP2022 Theorem 3 p. 3. -/
def thm3RHS (q : ℕ) (x : ℝ) : ℝ :=
  (1 / (8 * π * (q.totient : ℝ)) + 1 / (6 * π)) * √x * log x ^ 2
  + (0.184 * log q + 8.250) * √x * log x
  + (5.314 * log q + 124.318) * √x
  + (5.048 * log q ^ 2 + 109.573 * log q + 725.316) * √x / log x
  + (2.015 * log q + 0.5) * log x + R1 q

/-- The right side of EP2022 Lemma 31 pp. 40 to 41. -/
def lemma31RHS (q : ℕ) (x : ℝ) : ℝ :=
  (1 / (8 * π * (q.totient : ℝ)) + 1 / (6 * π)) * √x * log x
  + (0.184 * log q + 8.396) * √x
  + (6.05 * log q + 157.318) * √x / log x
  + (5.048 * log q ^ 2 + 152.085 * log q + 1719.86) * √x / log x ^ 2
  + (0.184 * log q + 8.250) * x ^ ((1 : ℝ) / 4) * log (log √x)
  + (5.254 * log q ^ 2 + 121.765 * log q + 937.202) * x ^ ((1 : ℝ) / 4)
  - (11.364 * log q + 281.636) * x ^ ((1 : ℝ) / 4) / log x
  - (10.096 * log q ^ 2 + 261.658 * log q + 2445.176) * x ^ ((1 : ℝ) / 4) / log x ^ 2
  + (80.768 * log q ^ 2 + 1753.168 * log q + 11605.056) * x ^ ((1 : ℝ) / 4) / log x ^ 3
      * (x ^ ((1 : ℝ) / 4) - 1)
  + (2.015 * log q + 0.5) * log (log x) + 2.754 * log q + 0.534 + R1 q / log 2

/-- The right side of EP2022 display (52) p. 44. -/
def display52RHS (x : ℝ) : ℝ :=
  11.4096 * √x / log x ^ 2 + 1.4262 * x ^ ((1 : ℝ) / 4) / log 2
  - 2.8524 * x ^ ((1 : ℝ) / 4) / log x - 11.4096 * x ^ ((1 : ℝ) / 4) / log x ^ 2

/-- LEAF: EP2022 Theorem 3 p. 3, GRH bound for psi of x, q, a. HARD, the analytic core of
the paper, Section 3, from the explicit formula for psi of x and chi. -/
theorem thm3 (hG : GRH) (q a : ℕ) (x : ℝ) (ha : Nat.Coprime a q) (hq : 3 ≤ q) (hx : 2 ≤ x) :
    |psiAP q a x - x / (q.totient : ℝ)| < thm3RHS q x := by
  sorry

/-- LEAF: EP2022 Lemma 31 pp. 40 to 41. MEDIUM, real analysis: integrate the Theorem 3
bound for `S(t) = psi(t; q, a) - t / phi(q)`, displays (40) to (49). The paper states the
one sided form; its proof bounds `|S|` from (40), which gives the absolute form here. -/
theorem lemma31 (q a : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : (q : ℝ) ≤ x)
    (hS : ∀ t : ℝ, 2 ≤ t → t ≤ x → |psiAP q a t - t / (q.totient : ℝ)| < thm3RHS q t) :
    |(psiAP q a x - x / (q.totient : ℝ)) / log x
      + ∫ t in (2 : ℝ)..x, (psiAP q a t - t / (q.totient : ℝ)) / (t * log t ^ 2)|
      < lemma31RHS q x := by
  sorry

/-- LEAF: EP2022 displays (50) and (53) p. 44, partial summation for pi of x, q, a via
theta of x, q, a, then psi of x, q, a, with `∫₂ˣ dt / log² t = li x - x / log x - li 2
+ 2 / log 2`. MEDIUM. -/
theorem display_50_53 (q a : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : 2 ≤ x) :
    ((((range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℕ) : ℝ)
        - liPV x / (q.totient : ℝ)
      = ((psiAP q a x - x / (q.totient : ℝ)) / log x
          + ∫ t in (2 : ℝ)..x, (psiAP q a t - t / (q.totient : ℝ)) / (t * log t ^ 2))
        + (thetaAP q a x - psiAP q a x) / log x
        + (∫ t in (2 : ℝ)..x, (thetaAP q a t - psiAP q a t) / (t * log t ^ 2))
        + (-liPV 2 + 2 / log 2) / (q.totient : ℝ) := by
  sorry

/-- LEAF: Rosser-Schoenfeld 1962 Theorem 13, display (3.36) p. 71, cited by EP2022 p. 44 as
[11] Theorem 13: `ψ(x) - θ(x) < 1.42620 x^{1/2}` for `0 < x`. A classical cited input,
checked on the rendered page. EASY to state, its proof in the source is a tabulation for
`x < 50653` and an analytic argument above. -/
theorem rs62_thm13 (x : ℝ) (hx : 0 < x) :
    Chebyshev.psi x - Chebyshev.theta x < 1.4262 * √x := by
  sorry

/-- PROVED: `θ(x; q, a)` is the prime part of the sum defining `ψ(x; q, a)`. -/
theorem thetaAP_eq (q a : ℕ) (x : ℝ) : thetaAP q a x =
    ∑ n ∈ ((Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q)).filter (fun n => n.Prime),
      (ArithmeticFunction.vonMangoldt n : ℝ) := by
  unfold thetaAP
  have hs : (range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % q = a % q)
      = ((Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q)).filter (fun n => n.Prime) := by
    ext n
    simp only [mem_filter, mem_range, mem_Icc]
    constructor
    · rintro ⟨h1, h2, h3⟩; exact ⟨⟨⟨h2.one_lt.le, by omega⟩, h3⟩, h2⟩
    · rintro ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩; exact ⟨by omega, h4, h3⟩
  rw [hs]
  refine sum_congr rfl fun n hn => ?_
  rw [ArithmeticFunction.vonMangoldt_apply_prime (mem_filter.1 hn).2]

/-- PROVED: EP2022 p. 44 before (51), `0 ≤ ψ(x; q, a) - θ(x; q, a) ≤ ψ(x) - θ(x)`. -/
theorem psiAP_sub_thetaAP_bounds (q a : ℕ) (x : ℝ) :
    0 ≤ psiAP q a x - thetaAP q a x ∧
      psiAP q a x - thetaAP q a x ≤ Chebyshev.psi x - Chebyshev.theta x := by
  have hsplit := sum_filter_add_sum_filter_not ((Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q))
    (fun n => n.Prime) (fun n => (ArithmeticFunction.vonMangoldt n : ℝ))
  have hd : psiAP q a x - thetaAP q a x =
      ∑ n ∈ ((Icc 1 ⌊x⌋₊).filter (fun n => n % q = a % q)).filter (fun n => ¬ n.Prime),
        (ArithmeticFunction.vonMangoldt n : ℝ) := by
    rw [thetaAP_eq]; unfold psiAP; linarith
  rw [hd, Chebyshev.psi_sub_theta_eq_sum_not_prime]
  constructor
  · exact sum_nonneg fun n _ => ArithmeticFunction.vonMangoldt_nonneg
  · apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      simp only [mem_filter, mem_Icc, mem_Ioc] at hn ⊢
      exact ⟨⟨by omega, hn.1.1.2⟩, hn.2⟩
    · intro n _ _; exact ArithmeticFunction.vonMangoldt_nonneg

/-- EP2022 display (51) p. 44. Was a LEAF; PROVED by S70 from `rs62_thm13` and
`psiAP_sub_thetaAP_bounds`, so it is CONDITIONAL ON the cited Rosser-Schoenfeld 1962
Theorem 13 only. -/
theorem display_51 (q a : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : 2 ≤ x) :
    |(thetaAP q a x - psiAP q a x) / log x| < 1.4262 * √x / log x := by
  have hl : 0 < log x := log_pos (by linarith)
  obtain ⟨h0, h1⟩ := psiAP_sub_thetaAP_bounds q a x
  have h2 := rs62_thm13 x (by linarith)
  rw [abs_div, abs_of_pos hl, abs_sub_comm, abs_of_nonneg h0]
  exact div_lt_div_of_pos_right (by linarith) hl

/-- LEAF: EP2022 display (52) p. 44, the integral of the (51) bound split at `√x`.
MEDIUM. -/
theorem display_52 (q a : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : 2 ≤ x) :
    |∫ t in (2 : ℝ)..x, (thetaAP q a t - psiAP q a t) / (t * log t ^ 2)|
      ≤ display52RHS x := by
  sorry

/-- LEAF: EP2022 pp. 45 to 46, the simplification of the assembled bound to the form of
Theorem 1, with Lemmas 11 and 32 and the value of `li 2`. MEDIUM, an inequality between
explicit functions of `x ≥ q ≥ 3`. -/
theorem final_combination (q : ℕ) (x : ℝ) (hq : 3 ≤ q) (hx : (q : ℝ) ≤ x) :
    lemma31RHS q x + 1.4262 * √x / log x + display52RHS x
        + |-liPV 2 + 2 / log 2| / (q.totient : ℝ) ≤
      (1 / (8 * π * (q.totient : ℝ)) + 1 / (6 * π)) * √x * log x
      + (0.184 * log q + 8.396) * √x
      + (6.05 * log q + 158.745) * √x / log x
      + (5.048 * log q ^ 2 + 152.085 * log q + 1731.270) * √x / log x ^ 2
      + (0.184 * log q + 8.250) * x ^ ((1 : ℝ) / 4) * log (log x)
      + (5.254 * log q ^ 2 + 121.765 * log q + 939.260) * x ^ ((1 : ℝ) / 4)
      + (80.768 * log q ^ 2 + 1753.168 * log q + 11605.056) * √x / log x ^ 3
      - 237.934 := by
  sorry

/-- PROVED from the LEAFs above: EP2022 Theorem 1 p. 2, in the exact form of
`ProgressionS63.ep2022_theorem1`. -/
theorem ep2022_theorem1_of_leaves (hG : GRH) (q a : ℕ) (x : ℝ)
    (ha : Nat.Coprime a q) (hq : 3 ≤ q) (hx : (q : ℝ) ≤ x) :
    |((((range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p % q = a % q)).card : ℕ) : ℝ)
        - liPV x / (q.totient : ℝ)| <
      (1 / (8 * π * (q.totient : ℝ)) + 1 / (6 * π)) * √x * log x
      + (0.184 * log q + 8.396) * √x
      + (6.05 * log q + 158.745) * √x / log x
      + (5.048 * log q ^ 2 + 152.085 * log q + 1731.270) * √x / log x ^ 2
      + (0.184 * log q + 8.250) * x ^ ((1 : ℝ) / 4) * log (log x)
      + (5.254 * log q ^ 2 + 121.765 * log q + 939.260) * x ^ ((1 : ℝ) / 4)
      + (80.768 * log q ^ 2 + 1753.168 * log q + 11605.056) * √x / log x ^ 3
      - 237.934 := by
  have hq3 : (3 : ℝ) ≤ q := by exact_mod_cast hq
  have hx2 : (2 : ℝ) ≤ x := by linarith
  have hphi : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.2 (by omega)
  rw [display_50_53 q a x hq hx2]
  have hA := lemma31 q a x hq hx (fun t ht1 _ => thm3 hG q a t ha hq ht1)
  have hB := display_51 q a x hq hx2
  have hC := display_52 q a x hq hx2
  have hD : |(-liPV 2 + 2 / log 2) / (q.totient : ℝ)| = |-liPV 2 + 2 / log 2| / (q.totient : ℝ) := by
    rw [abs_div, abs_of_pos hphi]
  have hF := final_combination q x hq hx
  calc _ ≤ |(psiAP q a x - x / (q.totient : ℝ)) / log x
          + ∫ t in (2 : ℝ)..x, (psiAP q a t - t / (q.totient : ℝ)) / (t * log t ^ 2)|
        + |(thetaAP q a x - psiAP q a x) / log x|
        + |∫ t in (2 : ℝ)..x, (thetaAP q a t - psiAP q a t) / (t * log t ^ 2)|
        + |(-liPV 2 + 2 / log 2) / (q.totient : ℝ)| := by
          refine le_trans (abs_add_le _ _) ?_
          gcongr
          refine le_trans (abs_add_le _ _) ?_
          gcongr
          exact abs_add_le _ _
    _ < _ := by rw [hD]; linarith

end

end LeanLab.BS2022GRH.ProgressionEPS70

#print axioms LeanLab.BS2022GRH.ProgressionEPS70.ep2022_theorem1_of_leaves
#print axioms LeanLab.BS2022GRH.ProgressionEPS70.thetaAP_eq
#print axioms LeanLab.BS2022GRH.ProgressionEPS70.psiAP_sub_thetaAP_bounds
#print axioms LeanLab.BS2022GRH.ProgressionEPS70.display_51
