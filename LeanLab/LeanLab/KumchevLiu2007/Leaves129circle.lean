/-
Kumchev and Liu, arXiv 0801.0130, paper P0088. Branch repair of Task129, 2026-11-13.

The branch `claude/KumchevLiu2007-circle_input-p2` added four theorems with a
`sorry` to the existing file `Decomp129`, which the lab rule forbids for an
existing file. They are stated here instead, each on a theorem whose doc comment
starts with LEAF, and `Decomp129` proves its own four steps by applying them, so
the statements of those steps are unchanged.

This file declares nothing: no def, abbrev, structure, instance, notation or
axiom. The definitions of `Decomp129` that the four statements mention (the
window Y, the window pair set, the integer main term, the weight f2, the
singular integral, the truncated singular series, the sifted count, the error of
display 53, the summation range and the Euler product P2) are bound by `let` in
front of each statement, with the body of the definition written out. `Decomp129`
imports this file and so cannot supply them, and a copy of one would be a new
definition. A `let` is definitionally transparent, so each statement here is the
same proposition as the step `Decomp129` proves from it.

The four steps are CITED leaves: the paper derives them from Proposition 1
display 33 on page 7 with hypotheses A1.2, A2.2 and A2.3 of page 15, from Lemma
3.8 display 49 on page 14, and in two cases from ranges that the paper does not
write out. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp1534a
import LeanLab.KumchevLiu2007.Decomp1534c

namespace LeanLab.KumchevLiu2007.Task129K

open Real Complex LeanLab.KumchevLiu2007
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: Proposition 1 display 33 on page 7, applied on pages 15 and 16 to R of
n, varpi, lambda0 with varpi the prime indicator and lambda0 of display 34: the
sum over X less than n at most X plus H of the square of R minus S2 of n, P times
I of n is at most a constant times H Y L to the minus A, for H from X to the
7/18 plus epsilon up to X to the 1 minus epsilon. CITED: needs hypotheses A1.2,
A2.2 and A2.3 verified on page 15, which rest on the short interval Siegel
Walfisz theorem and Lemma 3.4. -/
theorem prop1_meansq :
    let windowY : ℝ → ℝ → ℝ := fun X ε => X ^ (7 / 12 + ε / 2)
    let windowPairs : ℝ → ℝ → ℕ → Finset (ℕ × ℕ) := fun X Y n =>
      ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
        (fun v => X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt Y ∧ v.1 + v.2 ^ 2 = n)
    let integerMain : ℝ → ℝ → ℕ → ℝ := fun X Y n =>
      ∑ v ∈ windowPairs X Y n, 1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ))
    let f2Weight : ℝ → ℝ → ℝ := fun z0 u =>
      1 / Real.log u + ∫ t in z0..Real.sqrt u, 1 / (t * Real.log t * Real.log (u / t))
    let singInt : ℝ → ℝ → ℝ → ℕ → ℝ := fun X Y P n =>
      ∑ v ∈ windowPairs X Y n,
        (1 / Real.log (v.1 : ℝ)) * f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (v.2 : ℝ)
    let series2 : ℕ → ℝ → ℂ := fun n P => ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, U1534.A2 n q
    let roughCount : ℝ → ℝ → ℝ → ℕ → ℕ := fun X Y P n =>
      ((windowPairs X Y n).filter (fun v => v.1.Prime ∧
        ∀ p : ℕ, p.Prime → p ∣ v.2 → Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p : ℝ))).card
    let err53 : ℝ → ℝ → ℝ → ℕ → ℝ := fun X ε B n =>
      ‖(roughCount X (windowY X ε) (Real.log X ^ B) n : ℂ) -
        series2 n (Real.log X ^ B) * (singInt X (windowY X ε) (Real.log X ^ B) n : ℂ)‖
    let iocNat : ℝ → ℝ → Finset ℕ := fun X H =>
      (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ))
    ∀ A : ℝ, 0 < A →
      ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
        ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
          X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
          ∑ n ∈ iocNat X H, err53 X ε B n ^ 2 ≤
            C * H * windowY X ε * Real.log X ^ (-A) := by
  sorry

/-- LEAF: Display 53 of page 16 when epsilon exceeds 5 over 18 and H exceeds X to
the 1 minus epsilon, with the lower bound X to the 7/18 plus epsilon on H of
Theorem 1. The paper treats epsilon as a small fixed number and does not write
this case; PROGRESS.md records it as BLOCKED NO WRITTEN PROOF. SUPERSEDED: this
statement omits the lower bound X to the 7/18 plus epsilon on H, so for epsilon
above 11/36 it reaches below the range of Theorem 1, and `Decomp129` no longer
uses it: `eq53_large_eps_range` states the range with the lower bound kept. It is
kept here unchanged because it was in the branch. -/
theorem eq53_large_eps :
    let windowY : ℝ → ℝ → ℝ := fun X ε => X ^ (7 / 12 + ε / 2)
    let windowPairs : ℝ → ℝ → ℕ → Finset (ℕ × ℕ) := fun X Y n =>
      ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
        (fun v => X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt Y ∧ v.1 + v.2 ^ 2 = n)
    let integerMain : ℝ → ℝ → ℕ → ℝ := fun X Y n =>
      ∑ v ∈ windowPairs X Y n, 1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ))
    let f2Weight : ℝ → ℝ → ℝ := fun z0 u =>
      1 / Real.log u + ∫ t in z0..Real.sqrt u, 1 / (t * Real.log t * Real.log (u / t))
    let singInt : ℝ → ℝ → ℝ → ℕ → ℝ := fun X Y P n =>
      ∑ v ∈ windowPairs X Y n,
        (1 / Real.log (v.1 : ℝ)) * f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (v.2 : ℝ)
    let series2 : ℕ → ℝ → ℂ := fun n P => ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, U1534.A2 n q
    let roughCount : ℝ → ℝ → ℝ → ℕ → ℕ := fun X Y P n =>
      ((windowPairs X Y n).filter (fun v => v.1.Prime ∧
        ∀ p : ℕ, p.Prime → p ∣ v.2 → Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p : ℝ))).card
    let err53 : ℝ → ℝ → ℝ → ℕ → ℝ := fun X ε B n =>
      ‖(roughCount X (windowY X ε) (Real.log X ^ B) n : ℂ) -
        series2 n (Real.log X ^ B) * (singInt X (windowY X ε) (Real.log X ^ B) n : ℂ)‖
    let iocNat : ℝ → ℝ → Finset ℕ := fun X H =>
      (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ))
    ∀ A : ℝ, 0 < A →
      ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
        ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
          X0 ≤ X → 5 / 18 < ε → X ^ (1 - ε) < H → H ≤ X →
          (cntIoc (fun n => InH2 n ∧
            Real.sqrt (windowY X ε) * Real.log X ^ (-A) < err53 X ε B n) X H : ℝ) ≤
            C * H / Real.log X ^ A := by
  sorry

/-- LEAF: Lemma 3.8, display 49 on page 14, for j equal to 2. The statement
matches `lemma38_two` of `Decomp129b` term for term, which reduces it to the
leaves `truncation_input` and `tail_mean_square_input`; the bridge is
`eq49_lemma38_of_lemma38_two` in `Decomp129c`. CITED. -/
theorem eq49_lemma38 :
    let series2 : ℕ → ℝ → ℂ := fun n P => ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, U1534.A2 n q
    let eulerP2 : ℕ → ℝ → ℂ := fun n Q =>
      ∏ p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime, (1 + U1534.A2 n p)
    ∀ A ε : ℝ, 2 ≤ A → 0 < ε →
      ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧ ∀ x y P Q : ℝ, x0 ≤ x → x ^ ε ≤ y → y ≤ x →
        0 < P → P ≤ Q → Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
        (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, ‖series2 n P - eulerP2 n Q‖ ^ 2) ≤
          C * (y / P * Real.log x + y / Real.log x ^ A) := by
  sorry

/-- LEAF: The mean square bound display 33 of Proposition 1, page 7, for R of n,
varpi, lambda0 when epsilon lies in 5/18, 11/18 and X to the 1 minus epsilon is
less than H, with H at most Y and H at least the smaller of X to the 7/18 plus
epsilon and Y. Here H is Y to the theta2 with theta2 at least 2/3 and at most 1,
so the verification of hypothesis A2.3 on page 15 by Lemma 3.4 with x equal to Y
and y equal to H is the same argument as on the written range. The paper does not
write it: page 16 states display 55 only for H at most X to the 1 minus epsilon.
CITED. -/
theorem prop1_meansq_large :
    let windowY : ℝ → ℝ → ℝ := fun X ε => X ^ (7 / 12 + ε / 2)
    let windowPairs : ℝ → ℝ → ℕ → Finset (ℕ × ℕ) := fun X Y n =>
      ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
        (fun v => X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
          Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt Y ∧ v.1 + v.2 ^ 2 = n)
    let integerMain : ℝ → ℝ → ℕ → ℝ := fun X Y n =>
      ∑ v ∈ windowPairs X Y n, 1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ))
    let f2Weight : ℝ → ℝ → ℝ := fun z0 u =>
      1 / Real.log u + ∫ t in z0..Real.sqrt u, 1 / (t * Real.log t * Real.log (u / t))
    let singInt : ℝ → ℝ → ℝ → ℕ → ℝ := fun X Y P n =>
      ∑ v ∈ windowPairs X Y n,
        (1 / Real.log (v.1 : ℝ)) * f2Weight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) (v.2 : ℝ)
    let series2 : ℕ → ℝ → ℂ := fun n P => ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, U1534.A2 n q
    let roughCount : ℝ → ℝ → ℝ → ℕ → ℕ := fun X Y P n =>
      ((windowPairs X Y n).filter (fun v => v.1.Prime ∧
        ∀ p : ℕ, p.Prime → p ∣ v.2 → Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p : ℝ))).card
    let err53 : ℝ → ℝ → ℝ → ℕ → ℝ := fun X ε B n =>
      ‖(roughCount X (windowY X ε) (Real.log X ^ B) n : ℂ) -
        series2 n (Real.log X ^ B) * (singInt X (windowY X ε) (Real.log X ^ B) n : ℂ)‖
    let iocNat : ℝ → ℝ → Finset ℕ := fun X H =>
      (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ))
    ∀ A : ℝ, 0 < A →
      ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
        ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
          X0 ≤ X → 5 / 18 < ε → ε ≤ 11 / 18 →
          min (X ^ (7 / 18 + ε)) (windowY X ε) ≤ H → X ^ (1 - ε) < H →
          H ≤ windowY X ε →
          ∑ n ∈ iocNat X H, err53 X ε B n ^ 2 ≤
            C * H * windowY X ε * Real.log X ^ (-A) := by
  sorry

end LeanLab.KumchevLiu2007.Task129K
