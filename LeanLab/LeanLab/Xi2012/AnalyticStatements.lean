import LeanLab.Xi2012.NatSiegelWalfisz
import LeanLab.Xi2012.ElementaryPaper
import LeanLab.Xi2012.Ramanujan

/-!
Remaining named analytic targets in Xi 2012, arXiv 1206.2148v1.
These are proposition definitions. They assert no bound of the withdrawn paper.
The paper chooses c large. The targets keep c explicit and require it positive.
An eventual natural cutoff records the asymptotic meaning of the printed bounds.
The sequence bounds in Lemma 6 are normalized to 1.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Xi2012.NatEncoding

open Finset Real MeasureTheory

/-- The common family hypotheses on pages 2 and 3. -/
def FamilyContext (A : ℕ → Finset ℕ) (δ : ℕ → ℝ) (c₀ : ℝ) : Prop :=
  0 < c₀ ∧ IsPrimeFamily A ∧ DensityFloor δ c₀ ∧ SiegelWalfiszNat A δ

/-- Page 3 equation 4, P. -/
noncomputable def majorDenominator (x : ℕ) (c : ℝ) : ℝ := Real.log x ^ (6 * c + 24)

/-- Page 3 equation 4, Q. -/
noncomputable def minorScale (x : ℕ) (c : ℝ) : ℝ :=
  (x : ℝ) * Real.log x ^ (-7 * c - 30)

/-- Page 4 Lemma 2 part 3 uses 6c plus 12, distinct from the major-arc cutoff. -/
noncomputable def ramanujanCutoff (x : ℕ) (c : ℝ) : ℝ := Real.log x ^ (6 * c + 12)

/-- Page 3 equation 5, the union of the closed major arcs. -/
def majorArc (x : ℕ) (c α : ℝ) : Prop :=
  ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ majorDenominator x c ∧
    ∃ a : ℕ, 1 ≤ a ∧ a ≤ q ∧ Nat.Coprime a q ∧
      |α - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * minorScale x c)

/-- Page 3 equation 5, the complement inside the printed integration interval. -/
def minorArc (x : ℕ) (c α : ℝ) : Prop :=
  α ∈ Set.Icc (1 / minorScale x c) (1 + 1 / minorScale x c) ∧ ¬ majorArc x c α

/-- Page 2 unweighted exponential sum. -/
noncomputable def unweightedSum (X : Finset ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ X, fourierPhase α n

/-- Page 3 equation 6, major contribution for the selected prime set. -/
noncomputable def majorContribution (A : Finset ℕ) (x : ℕ) (c : ℝ) : ℂ := by
  classical
  exact ∫ α in {α : ℝ | majorArc x c α},
    primeWeightedSum A (fourierPhase α) ^ 2 * unweightedSum (excSet A x) (-α)

/-- Page 3 equation 6, minor contribution. -/
noncomputable def minorContribution (A : Finset ℕ) (x : ℕ) (c : ℝ) : ℂ := by
  classical
  exact ∫ α in {α : ℝ | minorArc x c α},
    primeWeightedSum A (fourierPhase α) ^ 2 * unweightedSum (excSet A x) (-α)

/-- Page 4 Lemma 1. Target at the chosen positive c, not asserted. -/
def Lemma1At (c : ℝ) : Prop :=
  0 < c → ∀ (A : ℕ → Finset ℕ) (δ : ℕ → ℝ) (c₀ : ℝ), FamilyContext A δ c₀ →
    ∃ C : ℝ, 0 ≤ C ∧ ∃ x₀ : ℕ, 3 ≤ x₀ ∧ ∀ x : ℕ, x₀ ≤ x →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ majorDenominator x c →
      ∀ a : ℕ, 1 ≤ a → a ≤ q → Nat.Coprime a q →
      ∀ β : ℝ, |β| ≤ 1 / ((q : ℝ) * minorScale x c) →
        ‖primeWeightedSum (A x) (fourierPhase ((a : ℝ) / q + β)) -
          (((ArithmeticFunction.moebius q : ℝ) / (q.totient : ℝ) * δ x : ℝ) : ℂ) *
            unweightedSum (Icc 1 x) β‖ ≤
          C * (δ x / (q : ℝ) * (1 + |β| * x) * Real.log q +
            (1 + (q : ℝ) * |β|) * x / Real.log x ^ (2 * c))

/-- Page 4 Lemma 2 part 3. Target with its printed x squared error. -/
def Lemma2Part3At (c : ℝ) : Prop :=
  0 < c → ∀ A : ℕ → Finset ℕ, IsPrimeFamily A →
    ∃ C : ℝ, 0 ≤ C ∧ ∃ x₀ : ℕ, 3 ≤ x₀ ∧ ∀ x : ℕ, x₀ ≤ x →
      ‖(∑ n ∈ excSet (A x) x, ∑ q ∈ Icc 1 ⌊ramanujanCutoff x c⌋₊,
          ((((ArithmeticFunction.moebius q : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) : ℝ) : ℂ) *
            ramanujanSum q n) -
        ((2 * LeanLab.ChenExplicit.twinC *
          (∑ n ∈ excSet (A x) x, oddPrimeProduct n) : ℝ) : ℂ)‖ ≤
        C * (x : ℝ) ^ 2 / Real.log x ^ c

/-- Page 5 Proposition 1, not asserted. -/
def Proposition1At (c : ℝ) : Prop :=
  0 < c → ∀ (A : ℕ → Finset ℕ) (δ : ℕ → ℝ) (c₀ : ℝ), FamilyContext A δ c₀ →
    ∃ C : ℝ, 0 ≤ C ∧ ∃ x₀ : ℕ, 3 ≤ x₀ ∧ ∀ x : ℕ, x₀ ≤ x →
      ‖majorContribution (A x) x c -
        ((2 * LeanLab.ChenExplicit.twinC * δ x ^ 2 * (x : ℝ) *
          (∑ n ∈ excSet (A x) x, oddPrimeProduct n) : ℝ) : ℂ)‖ ≤
        C * (δ x * (x : ℝ) ^ ((3 : ℝ) / 2) * Real.sqrt ((excSet (A x) x).card : ℝ) /
          Real.log x ^ c + (x : ℝ) ^ 2 / Real.log x ^ c)

/-- Page 5 Lemma 3 equation 10, not asserted. -/
def Lemma3At (c : ℝ) : Prop :=
  0 < c → ∀ (A : ℕ → Finset ℕ) (δ : ℕ → ℝ) (c₀ : ℝ), FamilyContext A δ c₀ →
    ∃ C : ℝ, 0 ≤ C ∧ ∃ x₀ : ℕ, 3 ≤ x₀ ∧ ∀ x : ℕ, x₀ ≤ x →
      ∀ q : ℕ, 1 ≤ q → ∀ a : ℕ, Nat.Coprime a q →
      ∀ β : ℝ, |β| ≤ 1 / ((q : ℝ) * minorScale x c) →
        ‖primeWeightedSum (A x) (fourierPhase ((a : ℝ) / q + β))‖ ≤
          C * ((x : ℝ) * (q : ℝ) ^ (-(1 : ℝ) / 6) +
            (x : ℝ) ^ ((1 : ℝ) / 2) * (q : ℝ) ^ ((5 : ℝ) / 6) + (q : ℝ)) *
              Real.log x ^ (3 : ℕ)

/-- Page 5 Lemma 3 minor-arc consequence, kept separate from equation 10. -/
def Lemma3MinorAt (c : ℝ) : Prop :=
  0 < c → ∀ (A : ℕ → Finset ℕ) (δ : ℕ → ℝ) (c₀ : ℝ), FamilyContext A δ c₀ →
    ∃ C : ℝ, 0 ≤ C ∧ ∃ x₀ : ℕ, 3 ≤ x₀ ∧ ∀ x : ℕ, x₀ ≤ x →
      ∀ α : ℝ, minorArc x c α →
        ‖primeWeightedSum (A x) (fourierPhase α)‖ ≤ C * x / Real.log x ^ (c + 1)

/-- Page 5 Proposition 2, not asserted. -/
def Proposition2At (c : ℝ) : Prop :=
  0 < c → ∀ (A : ℕ → Finset ℕ) (δ : ℕ → ℝ) (c₀ : ℝ), FamilyContext A δ c₀ →
    ∃ C : ℝ, 0 ≤ C ∧ ∃ x₀ : ℕ, 3 ≤ x₀ ∧ ∀ x : ℕ, x₀ ≤ x →
      ‖minorContribution (A x) x c‖ ≤
        C * Real.sqrt (δ x) * (x : ℝ) ^ ((3 : ℝ) / 2) *
          Real.sqrt ((excSet (A x) x).card : ℝ) / Real.log x ^ c

/-- The clipped reciprocal equals U at an integer phase, rather than using inverse zero. -/
noncomputable def clippedReciprocal (U t : ℝ) : ℝ :=
  if LeanLab.PNTPort.LargeSieve.dist0 t = 0 then U
  else min U (1 / LeanLab.PNTPort.LargeSieve.dist0 t)

/-- The approximation hypothesis printed in Section 4. No extra denominator range is added. -/
def PrintedApproximation (x : ℕ) (c α : ℝ) (a q : ℕ) : Prop :=
  1 ≤ q ∧ Nat.Coprime a q ∧
    |α - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * minorScale x c)

/-- Page 7 Lemma 5 equation 15 with the printed positive U and N domain. -/
def Lemma5FirstAt (c : ℝ) : Prop :=
  0 < c → ∃ C : ℝ, 0 ≤ C ∧ ∃ x₀ : ℕ, 3 ≤ x₀ ∧ ∀ x : ℕ, x₀ ≤ x →
    ∀ (α : ℝ) (a q : ℕ), PrintedApproximation x c α a q →
    ∀ U N : ℝ, 0 < U → 0 < N → ∀ θ : ℝ, θ ∈ Set.Icc 0 1 →
      (∑ n ∈ Icc 1 ⌊N⌋₊, clippedReciprocal U (α * n + θ)) ≤
        C * (1 + N / q) * (U + q * Real.log q)

/-- Page 7 Lemma 5 equation 16. The printed positive U domain is retained. -/
def Lemma5SecondAt (c : ℝ) : Prop :=
  0 < c → ∃ C : ℝ, 0 ≤ C ∧ ∃ x₀ : ℕ, 3 ≤ x₀ ∧ ∀ x : ℕ, x₀ ≤ x →
    ∀ (α : ℝ) (a q : ℕ), PrintedApproximation x c α a q →
    ∀ U N : ℝ, 0 < U → 0 < N → ∀ θ : ℝ, θ ∈ Set.Icc 0 1 →
      (∑ n ∈ Icc 1 ⌊N⌋₊, clippedReciprocal (U / n) (α * n + θ)) ≤
        C * (N + U / q + q) * Real.log (2 * q * U)

/-- Page 7 Lemma 6, the positive-index bilinear sum. -/
noncomputable def bilinearSum (x : ℕ) (M N : ℝ) (a b : ℕ → ℂ) (α : ℝ) : ℂ := by
  classical
  exact ∑ m ∈ (Icc 1 x).filter (fun m : ℕ => M < (m : ℝ)),
    ∑ n ∈ (Icc 1 (x / m)).filter (fun n : ℕ => N < (n : ℝ)),
      a m * b n * fourierPhase α (m * n)

/-- Page 7 Lemma 6 for coefficients of norm at most 1, not asserted. -/
def Lemma6At (c : ℝ) : Prop :=
  0 < c → ∃ C : ℝ, 0 ≤ C ∧ ∃ x₀ : ℕ, 3 ≤ x₀ ∧ ∀ x : ℕ, x₀ ≤ x →
    ∀ (α : ℝ) (r q : ℕ), PrintedApproximation x c α r q →
    ∀ M N : ℝ, 0 < M → 0 < N → ∀ a b : ℕ → ℂ,
      (∀ m, ‖a m‖ ≤ 1) → (∀ n, ‖b n‖ ≤ 1) →
        ‖bilinearSum x M N a b α‖ ≤
          C * Real.sqrt ((x : ℝ) / M + (x : ℝ) / N + (x : ℝ) / q + q) *
            Real.sqrt x * Real.log x ^ (2 : ℕ)

/-- The common analytic hypotheses have a proved prime-family instance. -/
theorem familyContext_primes {c₀ : ℝ} (hc₀ : 0 < c₀) :
    FamilyContext primesUpTo (fun _ => 1) c₀ :=
  ⟨hc₀, primes_admissible hc₀⟩

/-- The printed positive-U domain includes a zero logarithm with positive left side. -/
theorem not_Lemma5SecondAt {c : ℝ} (hc : 0 < c) : ¬ Lemma5SecondAt c := by
  intro h
  obtain ⟨C, _hC, x₀, hx₀, hbound⟩ := h hc
  have hx : (1 : ℝ) < x₀ := by exact_mod_cast (show 1 < x₀ by omega)
  have hlog : 0 < Real.log x₀ := Real.log_pos hx
  have hQ : 0 < minorScale x₀ c := by
    unfold minorScale
    positivity
  have happ : PrintedApproximation x₀ c 1 1 1 := by
    refine ⟨by norm_num, by norm_num, ?_⟩
    simp only [Nat.cast_one, div_one, sub_self, abs_zero, one_mul]
    positivity
  have hb := hbound x₀ le_rfl 1 1 1 happ (1 / 2) 1
    (by norm_num) (by norm_num) 0 (by norm_num)
  norm_num [clippedReciprocal, LeanLab.PNTPort.LargeSieve.dist0] at hb

end LeanLab.Xi2012.NatEncoding
