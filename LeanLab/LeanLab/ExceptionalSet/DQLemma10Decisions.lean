/-
Cited wall decision for `U1539.lemma10` of State1539, run CLOUD-cited-lemma10, 2026-11-20.

Target. `Lemma10` of State1539Data264 is Lemma 10 of J. Brudern and A. Perelli, Goldbach
numbers in sparse sequences, Ann. Inst. Fourier 48 (1998) 353-378, p. 370-371, lab copy
`papers/P0082.pdf`, PDF pages 19 and 20, read from the page images. Brudern-Perelli give no
proof: "This is Theorem 1 of Karacuba [K], with a change of notation (our k is Karacuba's
n + 1, c0 = δ, c1 = Θ0 etc.)".

Source. A. A. Karacuba, Estimates of trigonometric sums by the method of I. M. Vinogradov
and their applications, Trudy Mat. Inst. Steklov 112 (1971) 241-255, English translation
Proc. Steklov Inst. Math. 112 (1973) 251-265. Lab copy `papers/Karacuba1971-TrudyMIAN112.pdf`,
PDF page 4, journal page 244, chapter I section 2, Theorem 1, read from the page image.

Decision. NAMED HYPOTHESIS for the cited source, `KaracubaThm1Named`, which is exactly the
lab's earlier faithful transcription `KaracubaSplit.KaracubaTheorem1`, see the `Iff.rfl`
twin below.

MISCUT, recorded as a QUESTION, not a change. Brudern-Perelli's Lemma 10 is NOT a pure
change of notation of Karacuba's Theorem 1: their set `S ⊆ {1, ..., k-1}` may contain
`s = 1`, while Karacuba asks `s_j ≥ 2`, p. 244. When `S` has an element `s ≥ 2` the proved
bridge `KaracubaSplit.lemma10_of_thm1` reaches Theorem 1 with `c0 = δ/2`; the one case left is
`S = {1}`, which forces `δ k ≤ 1`. That case is `KaracubaSplit.LeafS1Case`; it is not in
Karacuba and not cited anywhere, so it cannot be a named hypothesis of this kind. It is
believed TRUE, by a short argument in the notes file: Taylor blocks of length `N^(Θ0 - ε)`
and the Kusmin-Landau first derivative test give `|Σ| ≪ k N^(1 - (Θ0 - θ)/2)`. Brudern and
Perelli never meet it: their `k` tends to infinity with `N`, p. 377.

So `lemma10_of_named` below is CONDITIONAL ON the cited `KaracubaThm1Named` and on the
uncited open leaf `LeafS1Case`; it is not conditional on named hypotheses only.

AI wrote the Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.KaracubaSplit

namespace LeanLab.ExceptionalSet.U1539.DQLemma10

open LeanLab.ExceptionalSet.U1539
open LeanLab.ExceptionalSet.U1539.KaracubaSplit

/-- NAMED HYPOTHESIS, CITED. Theorem 1 of Karacuba, Trudy Mat. Inst. Steklov 112 (1971),
chapter I section 2, p. 244, English Proc. Steklov Inst. Math. 112 (1973) 251-265:
let `N, P` be integers, `P > 0`, `n ≥ 2`, and let `f` have a continuous `(n+1)`th derivative
on `N ≤ x ≤ N + P`; let `c0, ..., c4` be positive constants with `c0 < 1`, `c1 < 1`,
`c2 + c4 < c1`, `r` an integer with `c0 n ≤ r ≤ n`, and `s_j ≥ 2`, `j = 1, ..., r`, not
exceeding `n`, such that on `N ≤ x ≤ N + P`
a) `|f^{(n+1)}(x)/(n+1)!| ≤ P^{-c1 (n+1)}`, and
b) `P^{-c2 s_j} ≤ |f^{(s_j)}(x)/s_j!| ≤ P^{-c3 s_j}`.
Then for every integer `0 < P₁ ≤ P` the sum `S = Σ_{x=N}^{N+P₁-1} e^{2πi f(x)}` has
`|S| ≤ A P^{1 - γ/n²}` with `A, γ > 0` absolute, that is depending on the `c`'s only.
Lean reading, all choices weaken the statement, so the source implies it: the derivative is
asked `C^{n+1}` on an open set around the interval; the `s_j` form a `Finset`, hence are
distinct, which Karacuba's proof uses on p. 245; `r ≤ n` follows from `T ⊆ [2, n]`. -/
def KaracubaThm1Named : Prop :=
  ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
    c0 < 1 → c1 < 1 → c2 + c4 < c1 →
    ∃ A γ : ℝ, 0 < A ∧ 0 < γ ∧ ∀ N P n : ℕ, 0 < P → 2 ≤ n → ∀ (f : ℝ → ℝ) (T : Finset ℕ),
      KarHyp c0 c1 c2 c3 N P n f T → ∀ P₁ : ℕ, 0 < P₁ → P₁ ≤ P →
        ‖∑ x ∈ Finset.Ico N (N + P₁), eC (f x)‖ ≤ A * (P : ℝ) ^ (1 - γ / (n : ℝ) ^ 2)

/-- Twin check: the named hypothesis is the lab's transcription `KaracubaTheorem1`. -/
theorem karacubaThm1Named_iff : KaracubaThm1Named ↔ KaracubaTheorem1 := Iff.rfl

/-- CONDITIONAL ASSEMBLY of the sealed target. The type is exactly `Lemma10`, the type of
`U1539.lemma10`. CONDITIONAL ON the CITED `KaracubaThm1Named` and on the uncited QUESTION
leaf `LeafS1Case`, the case `S = {1}` that Brudern-Perelli add to Karacuba's class. -/
theorem lemma10_of_named (hK : KaracubaThm1Named) (hS1 : LeafS1Case) : Lemma10 :=
  lemma10_of_thm1 hK hS1

/-- CONDITIONAL ASSEMBLY of the route target Theorem 2 of Brudern-Perelli, p. 354, through
Lemma 10 and the proved section 8 leaves of Decomp1539a. Same two conditions as above. -/
theorem theorem2_of_named (hK : KaracubaThm1Named) (hS1 : LeafS1Case) : Theorem2 :=
  theorem2_of_all_leaves (lemma10_of_named hK hS1)

end LeanLab.ExceptionalSet.U1539.DQLemma10

#print axioms LeanLab.ExceptionalSet.U1539.DQLemma10.karacubaThm1Named_iff
#print axioms LeanLab.ExceptionalSet.U1539.DQLemma10.lemma10_of_named
#print axioms LeanLab.ExceptionalSet.U1539.DQLemma10.theorem2_of_named
