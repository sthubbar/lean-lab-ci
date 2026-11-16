/-
Kumchev and Liu, arXiv 0801.0130, paper P0088. Branch repair of Task129,
2026-11-13.

The branch claude/KumchevLiu2007-residual_input-p3 added three sorries to the
existing file `Decomp129`, which the lab rule forbids for an existing file. They
live here instead, each on a theorem whose doc comment starts with LEAF, and
`Decomp129` proves its own three steps by applying them, so the statements of
those steps are unchanged.

This file declares nothing: no def, abbrev, structure, instance, notation or
axiom. The four definitions of `Decomp129` that the leaves mention (the window
Y, the window pair set, the sieve level and the sifted pair count, the partial
product and the sieve product, the main term and the residual) are written out
in full in each statement. `Decomp129` imports this file and so cannot supply
them, and a copy would be a new definition. Writing them out keeps the two
statements definitionally equal, which is what `Decomp129` uses.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp1534a
import LeanLab.KumchevLiu2007.Decomp1534c

namespace LeanLab.KumchevLiu2007.Task129L

open Real Complex LeanLab.KumchevLiu2007
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: Page 16 display 57 and page 17 display 58. Lemma 3.7, the Rosser
Iwaniec upper bound sieve cited from Iwaniec Theorem 1, applied with D = Y to
the 1/9 and z = exp of L to the 1 - delta/2 to the sequence A of page 16, with N
of display 57 at most a constant times Y to the 1/2 L to the -2 log L by the
prime number theorem and the remainder sum bounded through Bombieri Vinogradov
and Cauchy's inequality. The left side is the sifted pair count, which is at
most the sum of Phi(m, z) over A for large X. A can be taken arbitrarily large.
Here windowY, sieveLevel, sieveV and siftedPairs are written out.
CITED: the upper bound sieve of Lemma 3.7 is not in Mathlib and not in the
imports of Decomp129. -/
theorem sifted_sieve_input (A B δ ε : ℝ) (hA : 0 < A) (hB : 0 < B) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ K X1 : ℝ, 0 < K ∧ ∀ X : ℝ, X1 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + (X ^ (7 / 12 + ε / 2)) ^ (1 - ε) →
      (((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => (∀ p : ℕ, p.Prime → p ∣ v.1 → (Real.exp (Real.log X ^ (1 - δ / 2))) ≤ (p : ℝ)) ∧
      ¬ v.2.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ v.2 → ((X ^ (7 / 12 + ε / 2))) ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤ (p : ℝ))).card : ℝ) ≤
        K * ((X ^ (7 / 12 + ε / 2)) ^ (1 / 2 : ℝ) * Real.log X ^ (-2 : ℝ) *
            Real.log (Real.log X) * ∏ p ∈ (Finset.range (⌊(Real.exp (Real.log X ^ (1 - δ / 2)))⌋₊ + 1)).filter Nat.Prime,
      (1 - if p ∣ n then 0 else
      (((Finset.range p).filter (fun x => x ^ 2 % p = n % p)).card : ℝ) / (Nat.totient p : ℝ)) +
          (X ^ (7 / 12 + ε / 2)) ^ (1 / 2 : ℝ) * Real.log X ^ (-A)) := by
  sorry

/-- LEAF: Lemma 3.8 on page 14, display 49, for j = 2, a local twin of
Task129b.lemma38_two with the partial product of page 13 display 45 in place of
the identical Task129b.product2 and the interval numbers unfolded. The proof
chain of Task342e.lemma38_two_proved imports Decomp129, so neither Decomp129 nor
this file can import it: it would close the cycle from Decomp129 to this file to
Task342e to Decomp129. The clean downstream supply is
Supply129r.lemma38_two_local_supply. Here series2 and partialProduct2 are
written out. CITED. -/
theorem lemma38_two_local (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧
    ∀ x y P Q : ℝ, x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, ‖(∑ q ∈ Finset.Icc 1 ⌊(P)⌋₊, U1534.A2 n q) - ∏ p ∈ (Finset.range (⌊(Q)⌋₊ + 1)).filter Nat.Prime, (1 + U1534.A2 n p)‖ ^ 2) ≤
        C * (y / P * Real.log x + y / Real.log x ^ A) := by
  sorry

/-- LEAF: Proposition 2 on page 16 is stated only for H at most Y to the
1 - epsilon, while Theorem 1 on page 2 allows H up to X. This is the remaining
range X + Y to the 1 - epsilon < n at most X + H, with the windows of page 2
displays 4 to 6 still anchored at X. The written paper has no proof of this
range; PROGRESS.md records it as BLOCKED NO WRITTEN PROOF. Here windowY, main2
and residualCount are written out. -/
theorem residual_full_range_extension (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ δ ε : ℝ, 0 < δ → 0 < ε →
      ∃ C K X0 : ℝ, 0 < C ∧ 0 < K ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => X + (X ^ (7 / 12 + ε / 2)) ^ (1 - ε) < (n : ℝ) ∧ InH2 n ∧
          K * ‖((((∑ v ∈ ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n),
          1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ))) : ℝ) : ℂ) * (∑ q ∈ Finset.Icc 1 ⌊(Real.log X ^ B)⌋₊, U1534.A2 n q))‖ * Real.log X ^ (-1 + δ) <
          |((((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => v.1.Prime ∧
        ∀ p : ℕ, p.Prime → p ∣ v.2 → ((X ^ (7 / 12 + ε / 2))) ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤ (p : ℝ))).card : ℝ) - (((((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt ((X ^ (7 / 12 + ε / 2)))⌋₊ + 1))).filter
        (fun v => X - ((X ^ (7 / 12 + ε / 2))) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt ((X ^ (7 / 12 + ε / 2))) / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt ((X ^ (7 / 12 + ε / 2))) ∧ v.1 + v.2 ^ 2 = n)).filter (fun v => v.1.Prime ∧ v.2.Prime)).card : ℝ))|) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  sorry

end LeanLab.KumchevLiu2007.Task129L
