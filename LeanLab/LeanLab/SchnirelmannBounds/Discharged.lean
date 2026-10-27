/-
Audit U-1069, PC run 20261019T1503Z-1562. P0022 Kaniecki 1995's Theorem, both halves, kept
until now as the `sorry` theorems `kaniecki_odd` and `kaniecki_even` in Statements.lean, are
now the Props `kaniecki_odd_stmt` and `kaniecki_even_stmt` there and are PROVED here
CONDITIONAL ON the three cited inputs of `ChirreHagen2025.goldbach_10`, the J_ψ bound under
RH, even Goldbach to 4 · 10^18 and Schoenfeld's θ bound under RH, plus Liu-Wang 2002's
ternary threshold e^3100. The proofs are `KanieckiGap/AssemblyEven.lean`, units U-1064 and
U-1065, VERIFY MATCH in the same run. This is NOT Kaniecki's own proof: his Lemmas 4 to 7 are
not used. RH stays the hypothesis of the statement itself, as Kaniecki states it.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.SchnirelmannBounds.Statements
import LeanLab.KanieckiGap.AssemblyEven
import LeanLab.Kaniecki1995.Statements

namespace LeanLab.SchnirelmannBounds
open LeanLab.SchnirelmannConstant

/-- The three cited inputs of `goldbach_10` and Liu-Wang 2002, bundled. Each field is a
published result the lab does not prove: Chirre-Hagen's J_ψ bound and Schoenfeld's θ bound,
both under RH; the Oliveira e Silva, Herzog, Pardi check; Liu-Wang's e^3100. -/
structure KanieckiInputs : Prop where
  h2 : RiemannHypothesis → ∀ x δ : ℝ, 10 ^ 13 ≤ x → 0 < δ → δ ≤ 1 / 10 ^ 13 →
    LeanLab.ChirreHagen2025.Jpsi x δ ≤ 2.2258 * δ * Real.log (2.0001 / δ) ^ 2 * x ^ 2
  hE : EvenGoldbachUpTo (4 * 10 ^ 18)
  hS : RiemannHypothesis → LeanLab.ChirreHagen2025.SchoenfeldTheta
  hLW : LeanLab.Ternary.TernaryAbove (Real.exp 3100)

/-- **P0022 Kaniecki, odd half**, CONDITIONAL ON `KanieckiInputs`. -/
theorem kaniecki_odd (h : KanieckiInputs) : kaniecki_odd_stmt :=
  LeanLab.KanieckiGap.kaniecki_odd_of_inputs' h.h2 h.hE h.hS h.hLW

/-- **P0022 Kaniecki, even half as printed, with the G2 hypothesis**, CONDITIONAL ON
`KanieckiInputs`. The G2 hypothesis is not needed: the inputs already carry the 4 · 10^18
check. -/
theorem kaniecki_even (h : KanieckiInputs) : kaniecki_even_stmt := fun hRH _ =>
  LeanLab.KanieckiGap.kaniecki_even_of_inputs h.h2 h.hE h.hS h.hLW hRH

/-- The RH form used by `kaniecki_even_RH_of` follows. -/
theorem kaniecki_even_RH (h : KanieckiInputs) :
    RiemannHypothesis → ∀ n : ℕ, Even n → AtMostPrimes 4 n :=
  kaniecki_even_RH_of (kaniecki_even h) h.hE

/-- Faithfulness: the two Props are exactly the paper's Theorem as `Kaniecki1995` states it. -/
example : kaniecki_odd_stmt = LeanLab.Kaniecki1995.TheoremOdd := rfl
example : kaniecki_even_stmt = LeanLab.Kaniecki1995.TheoremEven := rfl

/-- P0022's own Theorem, both halves, in the `Kaniecki1995` namespace's statements. -/
theorem kaniecki1995_theorem (h : KanieckiInputs) :
    LeanLab.Kaniecki1995.TheoremOdd ∧ LeanLab.Kaniecki1995.TheoremEven :=
  ⟨kaniecki_odd h, kaniecki_even h⟩

/-- Vacuity: the conclusions are not empty, `9 = 2 + 7` is at most four primes and
`7 = 2 + 2 + 3` at most five. -/
example : AtMostPrimes 4 9 ∧ AtMostPrimes 5 7 :=
  ⟨((AtMostPrimes.prime Nat.prime_two).add (AtMostPrimes.prime (p := 7) (by norm_num))).mono
      (by norm_num),
    ((AtMostPrimes.prime Nat.prime_two).add ((AtMostPrimes.prime Nat.prime_two).add
      (AtMostPrimes.prime Nat.prime_three))).mono (by norm_num)⟩

end LeanLab.SchnirelmannBounds
