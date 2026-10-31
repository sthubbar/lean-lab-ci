/-
Unit U-1535, run 20261026T0004Z-24325, STATE job for P0033.
J. R. Chen and T. Z. Wang 1996, "On odd Goldbach problem", Acta Math. Sinica Chin. Ser.
39:2 (1996) 169-174, doi 10.12386/A1996sxxb0030, MR1411958.

The paper itself was NOT FOUND in the repo papers folder, nor in the PC copies folder, nor
at the journal or doi pages, which refused the PDF. What was read: the journal's abstract
metadata, which says every odd integer N ≥ exp(exp(9.715)) is a sum of three primes, proved
from a study of the zero-free region of Dirichlet L-functions and a mean-value estimate for
the distribution of primes; and the t5k.org reference entry. So the abstract settles the
earlier QUESTION in favour of ≥, the form `chenWang` in Ternary/Statements.lean already uses.

Since the paper's own lemmas could not be read, this file states the main theorem in the
weighted form that the circle method actually proves, plus the qualitative zero-free region
input the abstract names, in the classical textbook form of Davenport, chapter 14.
The leaves in Decomp1535a and Decomp1535b follow the standard circle method route, with page
references to Liu-Wang 2002, Acta Arith. 105, which uses the same route and is in the lab.

AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Ternary.Statements

namespace LeanLab.Ternary.U1535

open MeasureTheory LeanLab.Ternary

/-- The weighted count of ordered prime triples: the sum over primes `p + q + r = N`
of `log p · log q · log r`. -/
noncomputable def R3 (N : ℕ) : ℝ :=
  ∑ p ∈ Finset.range (N + 1), ∑ q ∈ Finset.range (N + 1), ∑ r ∈ Finset.range (N + 1),
    if p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = N then
      Real.log p * Real.log q * Real.log r else 0

/-- The exponential sum over primes `S(α) = Σ_{p ≤ N} log p · e(pα)`. -/
noncomputable def S (N : ℕ) (α : ℝ) : ℂ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime,
    (Real.log p : ℂ) * Complex.exp (2 * Real.pi * Complex.I * α * p)

/-- The circle method integrand `S(α)^3 e(-Nα)`. -/
noncomputable def F (N : ℕ) (α : ℝ) : ℂ :=
  S N α ^ 3 * Complex.exp (-(2 * Real.pi * Complex.I * α * N))

/-- Chebyshev's `θ(N) = Σ_{p ≤ N} log p`. -/
noncomputable def theta (N : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (N + 1)).filter Nat.Prime, Real.log p

/-- The weighted ternary statement above `C`: every odd `N ≥ C` has `R3 N > 0`. -/
def ChenWangWeighted (C : ℝ) : Prop := ∀ N : ℕ, Odd N → C ≤ N → 0 < R3 N

/-- A zero-free region away from the real axis: for every modulus `q ≥ 1`, every Dirichlet
character `χ` mod `q`, and `s = σ + it` with `|t| ≥ 1` and
`σ ≥ 1 - 1 / (c log (q (|t| + 2)))`, `L(s, χ) ≠ 0`. -/
def ZeroFreeHigh (c : ℝ) : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t : ℝ), 1 ≤ |t| →
    1 - 1 / (c * Real.log (q * (|t| + 2))) ≤ σ →
      DirichletCharacter.LFunction χ (σ + t * Complex.I) ≠ 0

/-! ### Sealed statements -/

/-- P0033 Chen-Wang 1996, main theorem, abstract: every odd integer `N ≥ exp(exp(9.715))`
is a sum of three primes, here in the weighted circle method form `R3 N > 0`. Cited, the
paper was not read; the threshold and the ≥ sign are from the journal's abstract. -/
theorem chenWang_weighted : ChenWangWeighted (Real.exp (Real.exp 9.715)) := by sorry

/-- The zero-free region input named in the P0033 abstract, in its classical qualitative
form, Davenport, Multiplicative Number Theory, chapter 14: some `c > 0` works. Away from
the real axis no exceptional zero occurs. Cited as a textbook theorem. -/
theorem zeroFreeHigh_exists : ∃ c : ℝ, 0 < c ∧ ZeroFreeHigh c := by sorry

/-! ### Vacuity instances and links, zero sorry -/

theorem term_nonneg (N p q r : ℕ) :
    0 ≤ (if p.Prime ∧ q.Prime ∧ r.Prime ∧ p + q + r = N then
      Real.log p * Real.log q * Real.log r else (0 : ℝ)) := by
  split_ifs
  · exact mul_nonneg (mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _))
      (Real.log_natCast_nonneg _)
  · exact le_rfl

/-- A sum of three primes has positive weighted count. -/
theorem r3_pos_of_isTernarySum {N : ℕ} (h : IsTernarySum N) : 0 < R3 N := by
  obtain ⟨p, q, r, hp, hq, hr, hs⟩ := h
  have hpN : p ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  have hqN : q ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  have hrN : r ∈ Finset.range (N + 1) := Finset.mem_range.mpr (by omega)
  unfold R3
  refine Finset.sum_pos' (fun i _ => Finset.sum_nonneg fun j _ =>
    Finset.sum_nonneg fun k _ => term_nonneg N i j k) ⟨p, hpN, ?_⟩
  refine Finset.sum_pos' (fun j _ => Finset.sum_nonneg fun k _ =>
    term_nonneg N p j k) ⟨q, hqN, ?_⟩
  refine Finset.sum_pos' (fun k _ => term_nonneg N p q k) ⟨r, hrN, ?_⟩
  rw [if_pos ⟨hp, hq, hr, hs⟩]
  have h1 := Real.log_pos (show (1 : ℝ) < p by exact_mod_cast hp.one_lt)
  have h2 := Real.log_pos (show (1 : ℝ) < q by exact_mod_cast hq.one_lt)
  have h3 := Real.log_pos (show (1 : ℝ) < r by exact_mod_cast hr.one_lt)
  exact mul_pos (mul_pos h1 h2) h3

/-- Vacuity instance for `ChenWangWeighted`: its body holds at `N = 7 = 2 + 2 + 3`. -/
theorem r3_seven_pos : 0 < R3 7 :=
  r3_pos_of_isTernarySum ⟨2, 2, 3, Nat.prime_two, Nat.prime_two, Nat.prime_three, rfl⟩

/-- `ChenWangWeighted C` follows from `TernaryAbove C`, so it holds whenever the ternary
statement does, for example from Helfgott's theorem. -/
theorem chenWangWeighted_of_ternaryAbove {C : ℝ} (h : TernaryAbove C) :
    ChenWangWeighted C := fun N ho hN => r3_pos_of_isTernarySum (h N ho hN)

/-- Vacuity instance for `ZeroFreeHigh`: with `c = -1` the region lies in `Re s > 1`,
where Mathlib proves `L(s, χ) ≠ 0`. -/
theorem zeroFreeHigh_neg_one : ZeroFreeHigh (-1) := by
  intro q _ χ σ t ht hσ
  have hq : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hx : (1 : ℝ) < q * (|t| + 2) := by nlinarith [abs_nonneg t]
  have hlog : 0 < Real.log (q * (|t| + 2)) := Real.log_pos hx
  have hσ1 : 1 ≤ σ := by
    have : 1 - 1 / ((-1) * Real.log (q * (|t| + 2))) = 1 + 1 / Real.log (q * (|t| + 2)) := by
      rw [neg_one_mul, one_div_neg_eq_neg_one_div]; ring
    rw [this] at hσ
    have : 0 < 1 / Real.log (q * (|t| + 2)) := by positivity
    linarith
  apply DirichletCharacter.LFunction_ne_zero_of_one_le_re
  · right
    intro h
    have him := congrArg Complex.im h
    simp at him
    rw [him] at ht
    norm_num at ht
  · simpa using hσ1

end LeanLab.Ternary.U1535
