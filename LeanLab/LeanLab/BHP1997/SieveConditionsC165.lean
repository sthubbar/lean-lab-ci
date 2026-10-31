/-
P0069, pages 1 to 3. The explicit Theorem 2 weight conditions.
These definitions are shared by the weight leaves and correlation transfer.
The two Prop definitions require Claude review before merge.
AI wrote the Lean code. CODEX task165. Goldbach is open.
-/
import LeanLab.BHP1997.Thm2Statement

namespace LeanLab.BHP1997.DecompC165b
open Classical Complex

/-- Pages 1 and 2, the interval I for the long weight. -/
noncomputable def leftInterval (ε x : ℝ) : Finset ℕ :=
  Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊

/-- Pages 1 and 2, the interval J for the short weight. -/
noncomputable def rightInterval (ε x : ℝ) : Finset ℕ :=
  Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊

/-- Page 3, Q is the integer part of one half of the square root of H. -/
noncomputable def sieveQ (ε x : ℝ) : ℕ :=
  ⌊((x ^ (11 / 20 + ε)) ^ ((2 : ℝ) * (1 / 16 - 1 / 10 ^ 5))) ^ (1 / 2 : ℝ) / 2⌋₊

/-- Page 3, Theorem 2 conditions i and ii for one real long weight.
This is a paper statement and requires Claude review before merge. -/
def LeftConditions (ε B u : ℝ) (a : ℝ → ℕ → ℝ) : Prop :=
  (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
    1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
    ∀ t : ℝ, t ≤ x →
      ‖∑ k ∈ (leftInterval ε x).filter (fun k : ℕ => (k : ℝ) ≤ t),
        ((a x k : ℂ) * χ (k : ZMod q) - Thm2.delta χ * u / Real.log x)‖ ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
  (∃ C : ℝ, ∀ x k, |a x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
  (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
    Nat.gcd k (Thm2.primorialBelow (Real.log x ^ A)) ≠ 1 → a x k = 0)

/-- Page 3, Theorem 2 conditions ii, iii and iv for one real short weight.
The exceptional character sets depend on A and x as in Thm2.Theorem2.
This is a paper statement and requires Claude review before merge. -/
def RightConditions (ε B v : ℝ) (b : ℝ → ℕ → ℝ) : Prop :=
  (∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B) ∧
  (∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
    1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
    ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
      ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        ((b x m : ℂ) * χ (m : ZMod q) -
          Thm2.delta χ * v / Real.log (x ^ (11 / 20 + ε)))‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ∧
  (∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → q ≤ sieveQ ε x →
      ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
      ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
            ‖∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              ((b x m : ℂ) * χ (m : ZMod q) -
                Thm2.delta χ * v / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                  C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                    x ^ (11 / 20 + ε) * Real.log x ^ (-A))

end LeanLab.BHP1997.DecompC165b
