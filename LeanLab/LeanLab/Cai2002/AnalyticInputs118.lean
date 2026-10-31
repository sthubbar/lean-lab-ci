/-
P0044, Cai 2002, page 599, Lemmas 3 and 4.
These are cited paper propositions, not proofs.
Nonnegative envelopes express the maxima in the printed mean value bounds.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib

open Finset Filter Asymptotics
noncomputable section
namespace LeanLab.Cai2002

/-- The logarithmic integral Li x in Lemma 3, page 599, with lower endpoint two. -/
def li118 (x : ℝ) : ℝ := ∫ t in (2 : ℝ)..x, 1 / Real.log t

/-- The prime count pi of y in residue l modulo d in Lemma 3, page 599.
Only y at least two and d positive are used in the cited statement. -/
def apCount118 (y : ℝ) (d l : ℕ) : ℕ :=
  ((range (⌊y⌋₊ + 1)).filter (fun p => p.Prime ∧ p % d = l % d)).card

/-- CITED. Lemma 3, page 599, attributed to Pan and Pan, Goldbach Conjecture,
1992, pages 175 to 176. Nonnegative envelopes replace the residue and endpoint maxima.
The implicit Vinogradov constant and sufficiently large threshold are explicit existentials. -/
def BombieriVinogradov118 : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧ ∃ K : ℝ, 0 < K ∧
    ∃ x0 : ℝ, 2 ≤ x0 ∧ ∀ x : ℝ, x0 ≤ x →
      ∃ R : ℕ → ℝ,
        (∀ d ∈ Icc 1 ⌊x ^ (1 / 2 : ℝ) / Real.log x ^ B⌋₊,
          0 ≤ R d ∧ ∀ l : ℕ, l < d → Nat.Coprime l d →
            ∀ y : ℝ, 2 ≤ y → y ≤ x →
              |(apCount118 y d l : ℝ) - li118 y / (Nat.totient d : ℝ)| ≤ R d) ∧
        (∑ d ∈ Icc 1 ⌊x ^ (1 / 2 : ℝ) / Real.log x ^ B⌋₊, R d) ≤
          K * x / Real.log x ^ A


/-- The interval prime count inside H in Lemma 4, page 599.
The cited sum uses positive a and q. -/
def shortCount118 (z h : ℝ) (a q l : ℕ) : ℕ :=
  ((range (⌊z + h⌋₊ + 1)).filter (fun p => p.Prime ∧
    z ≤ (a * p : ℕ) ∧ ((a * p : ℕ) : ℝ) < z + h ∧
    (a * p) % q = l % q)).card

/-- H of Lemma 4, page 599. The lower interval endpoint is included and the upper excluded. -/
def shortError118 (z h : ℝ) (a q l : ℕ) : ℝ :=
  (shortCount118 z h a q l : ℝ) -
    (li118 ((z + h) / (a : ℝ)) - li118 (z / (a : ℝ))) / (Nat.totient q : ℝ)

/-- CITED. Lemma 4, page 599, Wu 1993, Quart. J. Math. 44, pages 109 to 128.
B depends on A and c, as printed. The other constants may depend on the coefficient
sequence and the fixed theta and beta. Nonnegative envelopes express all three maxima. -/
def WuMeanValue118 : Prop :=
  ∀ c : ℝ, 0 < c → ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧
    ∀ g : ℕ → ℝ,
      ((fun x : ℝ => ∑ n ∈ Icc 1 ⌊x⌋₊, g n ^ 2 / (n : ℝ)) =O[atTop]
        (fun x : ℝ => Real.log x ^ c)) →
      ∀ theta beta : ℝ, 3 / 5 < theta → theta ≤ 1 →
        0 ≤ beta → beta < (5 * theta - 3) / 2 →
        ∃ K : ℝ, 0 < K ∧ ∃ x0 : ℝ, 2 ≤ x0 ∧
          ∀ x : ℝ, x0 ≤ x → ∃ R : ℕ → ℝ,
            (∀ d ∈ Icc 1 ⌊x ^ (theta - 1 / 2) / Real.log x ^ B⌋₊,
              0 ≤ R d ∧ ∀ l : ℕ, l < d → Nat.Coprime l d →
                ∀ h : ℝ, 0 ≤ h → h ≤ x ^ theta →
                  ∀ z : ℝ, x / 2 ≤ z → z ≤ x →
                    |∑ a ∈ (Icc 1 ⌊x ^ beta⌋₊).filter (fun a => Nat.Coprime a d),
                      g a * shortError118 z h a d l| ≤ R d) ∧
            (∑ d ∈ Icc 1 ⌊x ^ (theta - 1 / 2) / Real.log x ^ B⌋₊, R d) ≤
              K * x ^ theta / Real.log x ^ A

end LeanLab.Cai2002
