/- AI wrote the Lean code for CODEX task164.
Journal Theorem 7, pp. 1234 to 1241. Goldbach is open. -/
import LeanLab.BS2022GRH.Decomp148d
namespace LeanLab.BS2022GRH.DecompC164c
open Real Finset Classical ChenThresholdGRH
noncomputable section
/-- The main part of the sealed bracket, pp. 1235 and 1237, display 29. -/
def mainBracket (α ε C₁ X₂ ε₁ : ℝ) : ℝ :=
(1 + 0.06 * log X₂ / X₂ ^ (1 / 6 : ℝ)) *
      (2 / (1 / 2 - α) * exp eulerMascheroniConstant + 3 * ε * C₁) * (1 + ε₁) *
      (log (X₂ ^ (1 / 3 : ℝ)) * (liPV (X₂ ^ (1 / 3 : ℝ))
        + X₂ ^ (1 / 6 : ℝ) * log (X₂ ^ (1 / 3 : ℝ)) / (8 * π)) / X₂ ^ (1 / 3 : ℝ)) *
      (LeanLab.ChenExplicit.BJS.cbar + 36 / log X₂ ^ 2 + (log (8 / 3) + 64 / log X₂ ^ 2) *
        (log √(1 + ε₁) / (log (X₂ ^ (1 / 3 : ℝ)) ^ 2 - log √(1 + ε₁) ^ 2) + 27 / log X₂ ^ 2))
/-- The bilinear error part, p. 1241 display 33. -/
def errorBracket (A X₂ ε₁ : ℝ) : ℝ :=
  invTw * (1 + ε₁) / (log (1 + ε₁) * log X₂ ^ (A - 4)) *
      (0.053 * mbarJ X₂ A (X₂ ^ (1 / 8 : ℝ)) * (1 + ε₁) ^ (-(1 / 2) : ℝ)
        + 0.08 * X₂ ^ (-(1 / 8) : ℝ) * log X₂ ^ (A + 1))
/-- Multiplicative slices of p1, pp. 1235 and 1236 display 26. -/
def w (n : ℕ) (ε₁ : ℝ) (j : ℕ) : ℝ := U7153.zz n * (1 + ε₁) ^ j
/-- The number of slices, p. 1236 display 26. -/
def slices (n : ℕ) (ε₁ : ℝ) : Finset ℕ :=
  range ⌈log (U7153.yy n / U7153.zz n) / log (1 + ε₁)⌉₊
/-- Triples in one relaxed slice, p. 1235 before display 26.
We count triples so no uniqueness of representations is assumed. -/
def slice (n : ℕ) (ε₁ : ℝ) (j : ℕ) : Finset ((ℕ × ℕ) × ℕ) :=
  let K := ⌈(1 + ε₁) * n⌉₊ + 1
  ((range K ×ˢ range K) ×ˢ range K).filter (fun t =>
    t.1.1.Prime ∧ t.1.2.Prime ∧ t.2.Prime ∧
    U7153.zz n ≤ t.1.1 ∧ (t.1.1 : ℝ) < U7153.yy n ∧
    U7153.yy n ≤ t.1.2 ∧ t.1.2 ≤ t.2 ∧
    Nat.Coprime (t.1.2 * t.2) n ∧
    w n ε₁ j * t.1.2 * t.2 < n ∧
    w n ε₁ j ≤ t.1.1 ∧ (t.1.1 : ℝ) < w n ε₁ j * (1 + ε₁))
/-- Sum of the slice cardinalities, p. 1237 display 30. -/
def mass (n : ℕ) (ε₁ : ℝ) : ℝ :=
  ∑ j ∈ slices n ε₁, ((slice n ε₁ j).card : ℝ)
/-- Squarefree sifting divisors below D star, pp. 1236 and 1239. -/
def divisors (n : ℕ) (A : ℝ) : Finset ℕ :=
  (((range ⌈U7153.yy n⌉₊).filter (fun p => p.Prime ∧ ¬ p ∣ n)).powerset.image
    (fun T => ∏ p ∈ T, p)).filter
    (fun d => (d : ℝ) < √(n : ℝ) / log (n : ℝ) ^ (A + 1))
/-- The residue error in a slice, pp. 1236 and 1239 display 32. -/
def residueError (n : ℕ) (ε₁ : ℝ) (j d : ℕ) : ℝ :=
  (((slice n ε₁ j).filter
    (fun t => (t.1.1 * t.1.2 * t.2) % d = n % d)).card : ℝ) -
    ((slice n ε₁ j).card : ℝ) / (d.totient : ℝ)
/-- Total remainder with DQ enlarged to D star, p. 1241 display 33. -/
def remainder (n : ℕ) (A ε₁ : ℝ) : ℝ :=
  ∑ j ∈ slices n ε₁, ∑ d ∈ divisors n A, |residueError n ε₁ j d|
/-- The sieve coefficient of the total slice mass, p. 1237 display 29. -/
def sieveCoefficient (n : ℕ) (α ε C₁ : ℝ) : ℝ :=
  UNfull n / log n * (1 + 0.06 * log n / (n : ℝ) ^ (1 / 6 : ℝ)) *
    (2 / (1 / 2 - α) * exp eulerMascheroniConstant + 3 * ε * C₁)
/-- Cardinality coefficient from Lemma 14, p. 1237. -/
def massBound (n : ℕ) (ε₁ : ℝ) : ℝ :=
  (1 + ε₁) *
    (log (U7153.yy n) * (liPV (U7153.yy n) +
      √(U7153.yy n) * log (U7153.yy n) / (8 * π)) / U7153.yy n) * n *
    (LeanLab.ChenExplicit.BJS.cbar / log n + 36 / log n ^ 3 +
      (log (8 / 3) + 64 / log n ^ 2) *
        (log √(1 + ε₁) / (log (U7153.yy n) ^ 2 - log √(1 + ε₁) ^ 2) +
          27 / log n ^ 3))
/-- LEAF. Sieve the disjoint slices and sum, pp. 1236 and 1237 displays 27 to 29.
Use Theorem 4, Lemma 7 and Lemma 10. The expanded divisor range increases the error. -/
theorem sieve_slices (α A u ε C₁ C₂ X₂ ε₁ : ℝ) (n : ℕ)
    (hG : GRH) (hT : LinearSieveT4 ε C₁ C₂) (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (heps : epsJ u ≤ ε) (he0 : 0 < ε) (he1 : ε < 1 / 63)
    (hε₁ : 0 < ε₁) (hε₁1 : ε₁ < 1) (hα : 0 < α) (hα1 : α < 1 / 16)
    (hA : 0 < A) (hc : Cond25 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) :
    (U7153.SB n : ℝ) ≤ mass n ε₁ * sieveCoefficient n α ε C₁ + remainder n A ε₁ := by
  sorry
/-- LEAF. Bound the relaxed triple count by Lemma 14, pp. 1237 to 1239.
Use Schoenfeld Corollary 1 and partial summation for both prime variables. -/
theorem mass_bound (n : ℕ) (ε₁ : ℝ) (hG : GRH)
    (hε₁ : 0 < ε₁) (hε₁1 : ε₁ < 1) (hn : exp (exp 10) ≤ (n : ℝ)) :
    mass n ε₁ ≤ massBound n ε₁ := by
  sorry
/-- LEAF. Replace the running endpoint in the main term by X2.
Theorem 7 conclusion, pp. 1235 and 1241 after display 33.
The printed Lemma 14 bracket contains a short interval term whose normalization
introduces an extra log N. AuditC164 records this scalar mismatch as a QUESTION.
This leaf needs a stronger count bound or a justified compensation, not just algebra. -/
theorem main_at_threshold (α A u ε C₁ X₂ ε₁ : ℝ) (n : ℕ)
    (hC₁ : 0 ≤ C₁) (he0 : 0 < ε) (hε₁ : 0 < ε₁) (hε₁1 : ε₁ < 1)
    (hα : 0 < α) (hα1 : α < 1 / 16) (hA : 0 < A)
    (hc : Cond25 α A u X₂) (hX : exp (exp 10) ≤ X₂) (hn : X₂ ≤ (n : ℝ))
    (hm : mass n ε₁ ≤ massBound n ε₁) :
    mass n ε₁ * sieveCoefficient n α ε C₁ ≤
      UNfull n * n / log n ^ 2 * mainBracket α ε C₁ X₂ ε₁ := by
  sorry
/-- LEAF. Sum the bilinear remainder, pp. 1239 to 1241 displays 31 to 33.
Use Lemma 8 for each slice and Lemmas 4 and 5 for the coprimality correction. -/
theorem remainder_bound (α A u X₂ ε₁ : ℝ) (n : ℕ) (hG : GRH)
    (hε₁ : 0 < ε₁) (hε₁1 : ε₁ < 1) (hα : 0 < α) (hα1 : α < 1 / 16)
    (hA : 0 < A) (hc : Cond25 α A u X₂) (hX : exp (exp 10) ≤ X₂)
    (hn : X₂ ≤ (n : ℝ)) (hev : Even n) :
    remainder n A ε₁ ≤ UNfull n * n / log n ^ 2 * errorBracket A X₂ ε₁ := by
  sorry
/-- The sealed bracket is the sum of its main and error parts. -/
theorem bracket_split (α A ε C₁ X₂ ε₁ : ℝ) :
    B7J α A ε C₁ X₂ ε₁ = mainBracket α ε C₁ X₂ ε₁ + errorBracket A X₂ ε₁ := by
  rfl
/-- Exact sealed Thm7J, OPEN through four named leaves. No direct sorry. -/
theorem thm7J : Thm7J := by
  intro α A u ε C₁ C₂ X₂ ε₁ n hG hT hC₁ hC₂ heps he0 he1 hε₁ hε₁1 hα hα1 hA hc hX hn hev
  have hs := sieve_slices α A u ε C₁ C₂ X₂ ε₁ n hG hT hC₁ hC₂ heps he0 he1
    hε₁ hε₁1 hα hα1 hA hc hX hn hev
  have hm := main_at_threshold α A u ε C₁ X₂ ε₁ n hC₁ he0 hε₁ hε₁1 hα hα1 hA hc hX hn
    (mass_bound n ε₁ hG hε₁ hε₁1 (hX.trans hn))
  have hr := remainder_bound α A u X₂ ε₁ n hG hε₁ hε₁1 hα hα1 hA hc hX hn hev
  calc (U7153.SB n : ℝ)
      ≤ mass n ε₁ * sieveCoefficient n α ε C₁ + remainder n A ε₁ := hs
    _ ≤ UNfull n * n / log n ^ 2 * mainBracket α ε C₁ X₂ ε₁ +
        UNfull n * n / log n ^ 2 * errorBracket A X₂ ε₁ := add_le_add hm hr
    _ = UNfull n * n / log n ^ 2 * B7J α A ε C₁ X₂ ε₁ := by
      rw [bracket_split, mul_add]
end
end LeanLab.BS2022GRH.DecompC164c
#print axioms LeanLab.BS2022GRH.DecompC164c.sieve_slices
#print axioms LeanLab.BS2022GRH.DecompC164c.mass_bound
#print axioms LeanLab.BS2022GRH.DecompC164c.main_at_threshold
#print axioms LeanLab.BS2022GRH.DecompC164c.remainder_bound
#print axioms LeanLab.BS2022GRH.DecompC164c.bracket_split
#print axioms LeanLab.BS2022GRH.DecompC164c.thm7J
