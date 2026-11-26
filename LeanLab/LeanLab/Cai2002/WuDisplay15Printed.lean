/-
Wu 1993, Theoreme 1, display 1.5, page 111, is FALSE as printed: a misprint of z/l for h/l.
J. Wu, Theoremes generalises de Bombieri-Vinogradov dans les petits intervalles,
Quart. J. Math. Oxford 44 (1993), 109 to 128, papers/Wu1993.pdf, page 111.
Cai 2002 quotes the companion Theoreme 2, display 1.7, as its Lemma 4 on page 599.

Wu prints, for an arithmetic function g with hypothesis 1.4,
  H(z, h, q, a, l) = psi(z + h; q, a, l) - psi(z; q, a, l) - (z/l) / phi(q),
where psi(z; q, a, l) is the sum of Lambda(n) over l n at most z with l n = a mod q, and
display 1.5 asserts that the sum over q at most Q = x^(theta - 1/2) L^(-B) of the max over
a coprime to q, h at most y = x^theta and x/2 < z at most x of the absolute value of the sum
over l at most x^((5 theta - 3)/2 - epsilon) coprime to q of g(l) H(z, h, q, a, l) is
at most a constant times y L^(-A), L = log x, for 3/5 + epsilon at most theta at most 1.
The main term z/l is of the size of the whole count up to z, not of the interval of length h.
Take g the indicator of l = 1, which satisfies 1.4 with lambda = 1, theta = 1, a = 1, h = 0
and z = x: the term q = 1 alone is x, while the right side is K x / log x.
The same z/l is printed in relation 3.1 on page 116, while E(z, h, l, chi_0) there subtracts
h/l, and Theoreme 2 integrates 1/log t from z/l to (z + h)/l. So h/l is meant; the lab's
`WuTheorem2Stmt`, display 1.7, is not affected.

The max over a, h and z is written, as in `WuTheorem2Stmt`, as a bound for every choice
of a, h and z at each q; the constants B, K and x0 may depend on g here, so the refuted
statement is the weakest reading of the printed display.
No definition is added and no sorry is used. AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.Complex.ExponentialBounds

open Filter Finset Real

namespace LeanLab.Cai2002

/-- The indicator of l = 1 satisfies Wu's hypothesis 1.4, page 111, with lambda = 1, C = 3. -/
theorem wu15_indicator_hyp (u : ℝ) (hu : 2 ≤ u) :
    ∑ l ∈ Icc 1 ⌊u⌋₊, |(if l = 1 then (1 : ℝ) else 0)| ^ 2 / (l : ℝ) ≤ 3 * log u ^ (1 : ℝ) := by
  have h1 : (1 : ℕ) ∈ Icc 1 ⌊u⌋₊ := by
    simp only [mem_Icc, le_refl, true_and]
    exact Nat.le_floor (by push_cast; linarith)
  rw [Finset.sum_eq_single 1 (fun l _ hl => by simp [hl]) (fun h => absurd h1 h)]
  have hl2 : log 2 ≤ log u := log_le_log (by norm_num) hu
  have := Real.log_two_gt_d9
  rw [rpow_one]
  norm_num
  linarith

/-- FALSE AS PRINTED. Wu 1993, Theoreme 1, display 1.5, page 111, with the printed main
term (z/l)/phi(q) of H, read with constants allowed to depend on g. Refuted at theta = 1,
epsilon = 1/10, lambda = 1, A = 1 and g the indicator of l = 1. -/
theorem not_wu_display15_printed :
    ¬ (∀ θ ε lam A : ℝ, 0 < ε → 3 / 5 + ε ≤ θ → θ ≤ 1 → 0 < lam → 0 < A →
      ∀ g : ℕ → ℝ,
        (∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, 2 ≤ u →
          ∑ l ∈ Icc 1 ⌊u⌋₊, |g l| ^ 2 / (l : ℝ) ≤ C * log u ^ lam) →
      ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧ ∃ x0 : ℝ, ∀ x : ℝ, x0 ≤ x →
      ∀ (a : ℕ → ℕ) (h z : ℕ → ℝ), (∀ q, (a q).Coprime q) →
        (∀ q, 0 ≤ h q ∧ h q ≤ x ^ θ) → (∀ q, x / 2 < z q ∧ z q ≤ x) →
        ∑ q ∈ Icc 1 ⌊x ^ (θ - 1 / 2) / log x ^ B⌋₊,
          |∑ l ∈ (Icc 1 ⌊x ^ ((5 * θ - 3) / 2 - ε)⌋₊).filter (fun l => l.Coprime q),
            g l * ((∑ n ∈ (range (⌊z q + h q⌋₊ + 1)).filter
                  (fun n => ((l * n : ℕ) : ℝ) ≤ z q + h q ∧ l * n ≡ a q [MOD q]),
                  (ArithmeticFunction.vonMangoldt n : ℝ)) -
              (∑ n ∈ (range (⌊z q⌋₊ + 1)).filter
                  (fun n => ((l * n : ℕ) : ℝ) ≤ z q ∧ l * n ≡ a q [MOD q]),
                  (ArithmeticFunction.vonMangoldt n : ℝ)) -
              (z q / l) / (q.totient : ℝ))| ≤ K * x ^ θ / log x ^ A) := by
  intro H
  obtain ⟨B, -, K, hK, x0, hx⟩ := H 1 (1 / 10) 1 1 (by norm_num) (by norm_num) le_rfl
    one_pos one_pos (fun l => if l = 1 then 1 else 0) ⟨3, by norm_num, wu15_indicator_hyp⟩
  have ev : ∀ᶠ x : ℝ in atTop, x0 ≤ x ∧ 2 ≤ x ∧ K < log x ∧
      ‖log x ^ B‖ ≤ 1 * ‖x ^ (1 / 2 : ℝ)‖ :=
    (eventually_ge_atTop x0).and ((eventually_ge_atTop 2).and
      ((tendsto_log_atTop.eventually_gt_atTop K).and
        ((isLittleO_log_rpow_rpow_atTop B (by norm_num : (0 : ℝ) < 1 / 2)).bound one_pos)))
  obtain ⟨x, hx0, hx2, hKx, hQ⟩ := ev.exists
  have hxpos : 0 < x := by linarith
  have hlog : 0 < log x := log_pos (by linarith)
  have hS := hx x hx0 (fun _ => 1) (fun _ => 0) (fun _ => x) (fun q => Nat.coprime_one_left q)
    (fun _ => ⟨le_rfl, by positivity⟩) (fun _ => ⟨by linarith, le_rfl⟩)
  -- the sieve range for q contains q = 1
  have hQ1 : (1 : ℕ) ∈ Icc 1 ⌊x ^ ((1 : ℝ) - 1 / 2) / log x ^ B⌋₊ := by
    simp only [mem_Icc, le_refl, true_and]
    apply Nat.le_floor
    have hLB : 0 < log x ^ B := rpow_pos_of_pos hlog B
    rw [norm_of_nonneg hLB.le, norm_of_nonneg (rpow_nonneg hxpos.le _), one_mul] at hQ
    push_cast
    rw [le_div_iff₀ hLB, one_mul]
    norm_num
    exact hQ
  have hL1 : (1 : ℕ) ∈ (Icc 1 ⌊x ^ ((5 * (1 : ℝ) - 3) / 2 - 1 / 10)⌋₊).filter
      (fun l => l.Coprime 1) := by
    simp only [mem_filter, mem_Icc, le_refl, true_and, Nat.coprime_one_right_eq_true, and_true]
    exact Nat.le_floor (by push_cast; exact one_le_rpow (by linarith) (by norm_num))
  have hterm := Finset.single_le_sum (f := fun q : ℕ =>
      |∑ l ∈ (Icc 1 ⌊x ^ ((5 * (1 : ℝ) - 3) / 2 - 1 / 10)⌋₊).filter (fun l => l.Coprime q),
        (if l = 1 then (1 : ℝ) else 0) *
          ((∑ n ∈ (range (⌊x + 0⌋₊ + 1)).filter
                (fun n => ((l * n : ℕ) : ℝ) ≤ x + 0 ∧ l * n ≡ 1 [MOD q]),
                (ArithmeticFunction.vonMangoldt n : ℝ)) -
            (∑ n ∈ (range (⌊x⌋₊ + 1)).filter
                (fun n => ((l * n : ℕ) : ℝ) ≤ x ∧ l * n ≡ 1 [MOD q]),
                (ArithmeticFunction.vonMangoldt n : ℝ)) -
            (x / l) / (q.totient : ℝ))|) (fun q _ => abs_nonneg _) hQ1
  have h1 : |∑ l ∈ (Icc 1 ⌊x ^ ((5 * (1 : ℝ) - 3) / 2 - 1 / 10)⌋₊).filter (fun l => l.Coprime 1),
        (if l = 1 then (1 : ℝ) else 0) *
          ((∑ n ∈ (range (⌊x + 0⌋₊ + 1)).filter
                (fun n => ((l * n : ℕ) : ℝ) ≤ x + 0 ∧ l * n ≡ 1 [MOD 1]),
                (ArithmeticFunction.vonMangoldt n : ℝ)) -
            (∑ n ∈ (range (⌊x⌋₊ + 1)).filter
                (fun n => ((l * n : ℕ) : ℝ) ≤ x ∧ l * n ≡ 1 [MOD 1]),
                (ArithmeticFunction.vonMangoldt n : ℝ)) -
            (x / l) / ((1 : ℕ).totient : ℝ))| = x := by
    rw [Finset.sum_eq_single 1 (fun l _ hl => by simp [hl]) (fun h => absurd hL1 h)]
    simp only [ite_true, add_zero, sub_self, Nat.cast_one, div_one, Nat.totient_one, one_mul,
      zero_sub, abs_neg]
    exact abs_of_pos hxpos
  have hfin : x ≤ K * x ^ (1 : ℝ) / log x ^ (1 : ℝ) := by
    exact (h1.symm.le.trans hterm).trans hS
  rw [rpow_one, rpow_one, le_div_iff₀ hlog] at hfin
  nlinarith

#print axioms wu15_indicator_hyp
#print axioms not_wu_display15_printed

end LeanLab.Cai2002
