/-
T1, unit U-1094, PC run 20261019T1803Z-6290. P0043 J. Wu, Chen's double sieve, Goldbach's conjecture
and the twin prime problem, 2, Acta Arith. 131, 2008, arXiv 0709.3764v1, Lemma 2.2, p. 4, and its
proof, pp. 4 to 6, read from the rendered pages in Claude in Chrome.

The proof ends on p. 6 with
  Δ₂ ≥ − Σ_{p₁<p₂<p₃<N^κ₂} {…} − Σ_{N^κ₁ ≤ p₁ < p₂ < N^κ₂ ≤ p₃ < N^{1/2−2κ₁}/p₂} {…} + Σ … ≥ −Υ₁₀ − Υ₁₁,
but the second triple sum of Δ₁, p. 5, from Buchstab on S₁(κ₂, 1/2 − 3κ₁), runs over
p₃ < N^{1/2−3κ₁}, and N^{1/2−2κ₁}/p₂ < N^{1/2−3κ₁} whenever p₂ > N^κ₁, `range_strict`. So part of a
nonnegative subtracted sum is dropped without a reason, and Υ₁₁'s range p₄ < N^{1/2−2κ₁}/p₃ is too short.

This file checks the consequence in the exponent model, where a prime q is recorded by
e = log q / log N, stored as the natural number e·D with D = 3 · 100 · 1327 · 824 = 328034400 so that
every threshold is exact and the kernel can decide each count and every condition of Lemma 2.2 is a linear condition on exponents: for the
squarefree a with exponents 0.08, 0.09, 0.12, 0.25, four primes, so 4[Ω(a) ≤ 2] = 0, the right side
of Lemma 2.2 is 1 with the printed Υ₁₁ and 0 with p₄ < N^{1/2−3κ₁}, `printed_fails`,
`corrected_holds`. The sieve sets are read as intended, Υ₉ with P(Np₁p₂), Υ₁₀ and Υ₁₁ with P(Np₁),
as in numerics/wu08_lemma22.py of the cloud's U-5411; with the printed P(N) Υ₁₀ = Υ₁₁ = 0 and the
failure only grows. A real instance at N = 10^60 with an actual prime p = N − a was checked by
the falsifier subagent in Python, not here.

Plain math twin: with κ₁ = 1/13.27, κ₂ = 1/8.24, for a = q₁q₂q₃q₄ with q_i ≈ N^{0.08}, N^{0.09},
N^{0.12}, N^{0.25}: Υ₁ = 1, Υ₂ = 0, Υ₃ = Υ₄ = 4, Υ₅ = Υ₆ = 3, Υ₇ to Υ₁₁ = 0, so
3 + 0 − 4 − 4 + 3 + 3 = 1 > 0 = 4[Ω(a) ≤ 2]; with the longer range Υ₁₁ = 1 and the right side is 0.
Vacuity: the exponents are distinct, at least κ₁ and sum to 0.54 < 1, `config_ok`.
KNOWN mathematics; the gap is in the published proof. Chen's theorem itself is not in doubt.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel.
-/
import Mathlib

namespace LeanLab.ChenDoubleSieve.Wu08Gap

/-- Exponents are stored in units of `1/D`. -/
def D : ℕ := 328034400
def k1 : ℕ := 24720000   -- D / 13.27
def k2 : ℕ := 39810000   -- D / 8.24
def e13 : ℕ := 109344800 -- D / 3
def em : ℕ := 89857200   -- D (1/2 − 3κ₁)
def e2m : ℕ := 114577200 -- D (1/2 − 2κ₁)

theorem units : (k1 : ℚ) / D = 1 / 13.27 ∧ (k2 : ℚ) / D = 1 / 8.24 ∧ (e13 : ℚ) / D = 1 / 3 ∧
    (em : ℚ) / D = 1 / 2 - 3 / 13.27 ∧ (e2m : ℚ) / D = 1 / 2 - 2 / 13.27 := by
  norm_num [k1, k2, e13, em, e2m, D]

/-- `a` has no prime `q` with `yd · q < yn` except those in `X`; the level is `yn / yd`. -/
def sift (d X : List ℕ) (yn yd : ℕ) : Bool := d.all fun q => decide (yn ≤ yd * q) || X.contains q

def prs (d : List ℕ) : List (ℕ × ℕ) := (d.product d).filter fun p => decide (p.1 < p.2)

def U2 (d : List ℕ) : ℤ := if sift d [] k2 1 then 1 else 0
def U3 (d : List ℕ) : ℤ := (d.countP fun q => decide (q < e13) : ℕ)
def U4 (d : List ℕ) : ℤ := (d.countP fun q => decide (q < em) : ℕ)
def U5 (d : List ℕ) : ℤ := ((prs d).countP fun p => decide (p.2 < k2) : ℕ)
def U6 (d : List ℕ) : ℤ :=
  ((d.product d).countP fun p => decide (k1 ≤ p.1 ∧ p.1 < k2 ∧ k2 ≤ p.2 ∧ p.2 < em) : ℕ)
def U7 (d : List ℕ) : ℤ :=
  ((prs d).countP fun p => decide (em ≤ p.1 ∧ p.1 + 2 * p.2 < D) && sift d [p.1] p.2 1 : ℕ)
def U8 (d : List ℕ) : ℤ :=
  ((prs d).countP fun p => decide (p.1 < e13 ∧ e13 ≤ p.2 ∧ p.1 + 2 * p.2 < D) &&
    sift d [p.1] p.2 1 : ℕ)
/-- Υ₉, sifting level `(N/p₁p₂)^{1/2}`, exponent `(1 − e₁ − e₂)/2`. -/
def U9 (d : List ℕ) : ℤ :=
  ((prs d).countP fun p => decide (k2 ≤ p.1 ∧ p.1 < em ∧ em ≤ p.2 ∧ p.1 + 2 * p.2 < D) &&
    sift d [p.1, p.2] (D - p.1 - p.2) 2 : ℕ)
def trs (d : List ℕ) : List (ℕ × ℕ × ℕ) :=
  (d.product (d.product d)).filter fun t => decide (t.1 < t.2.1 ∧ t.2.1 < t.2.2)
def U10 (d : List ℕ) : ℤ :=
  (((trs d).product d).countP fun s => decide (s.1.2.2 < s.2 ∧ s.2 < k2) &&
    sift d [s.1.1] s.1.2.1 1 : ℕ)
/-- Υ₁₁ with the upper limit for `p₄` given as a function of `p₃`. -/
def U11 (top : ℕ → ℕ) (d : List ℕ) : ℤ :=
  (((trs d).product d).countP fun s => decide (s.1.2.2 < k2 ∧ k2 ≤ s.2 ∧ s.2 < top s.1.2.2) &&
    sift d [s.1.1] s.1.2.1 1 : ℕ)

/-- The right side of Lemma 2.2 for one squarefree `a`, Υ₁ = 1. -/
def rhs (top : ℕ → ℕ) (d : List ℕ) : ℤ :=
  3 + U2 d - U3 d - U4 d + U5 d + U6 d - 2 * U7 d - U8 d - U9 d - U10 d - U11 top d
def lhs (d : List ℕ) : ℤ := if d.length ≤ 2 then 4 else 0

def printedTop (t3 : ℕ) : ℕ := e2m - t3
def fullTop (_ : ℕ) : ℕ := em

/-- Exponents 0.08, 0.09, 0.12, 0.25 in units of `1/D`. -/
def cfg : List ℕ := [26242752, 29523096, 39364128, 82008600]

theorem cfg_units : cfg.map (fun e => (e : ℚ) / D) = [0.08, 0.09, 0.12, 0.25] := by
  norm_num [cfg, D]

theorem config_ok : cfg.Nodup ∧ (∀ e ∈ cfg, k1 ≤ e) ∧ cfg.sum < D := by decide

theorem printed_fails : lhs cfg = 0 ∧ rhs printedTop cfg = 1 := by decide

theorem corrected_holds : rhs fullTop cfg = 0 := by decide

/-- The p. 6 range is strictly shorter than the Δ₁ range on p. 5 for every `p₂ > N^κ₁`,
in exponents: `1/2 − 2κ₁ − t₂ < 1/2 − 3κ₁` when `t₂ > κ₁`. -/
theorem range_strict (t2 : ℚ) (h : 1 / 13.27 < t2) : 1 / 2 - 2 / 13.27 - t2 < 1 / 2 - 3 / 13.27 := by
  linarith

end LeanLab.ChenDoubleSieve.Wu08Gap

#print axioms LeanLab.ChenDoubleSieve.Wu08Gap.units
#print axioms LeanLab.ChenDoubleSieve.Wu08Gap.cfg_units
#print axioms LeanLab.ChenDoubleSieve.Wu08Gap.config_ok
#print axioms LeanLab.ChenDoubleSieve.Wu08Gap.printed_fails
#print axioms LeanLab.ChenDoubleSieve.Wu08Gap.corrected_holds
#print axioms LeanLab.ChenDoubleSieve.Wu08Gap.range_strict
