import LeanLab.ChenDoubleSieve.Decomp275a
import LeanLab.ChenDoubleSieve.Decomp275d
import LeanLab.ChenDoubleSieve.FunctionalStatements
import LeanLab.ChenDoubleSieve.Wu2008Lemma22Sum

/-!
Wu 2004 Section 10 at its printed parameter choice.
The open leaves separate weights, sieve estimates, and numerical integration.
Source: https://arxiv.org/pdf/0705.1652, pages 34 to 42.
AI wrote the Lean code. Binary Goldbach is open.
-/

noncomputable section
open Real Finset MeasureTheory
open scoped Classical
namespace LeanLab.ChenDoubleSieve.Task275
open Wu41 (S PS)
open Wu08Sum (P2 P4)
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- The prime difference sequence used in Sections 9 and 10. -/
def primeSequence (N : ℕ) : Finset ℕ :=
  ((range (N + 1)).filter Nat.Prime).image (fun p => N - p)

/-- Section 10's fixed kappa one. -/
def kappa1 : ℝ := 1 / 12
/-- Section 10's fixed kappa two. -/
def kappa2 : ℝ := 29 / 250
/-- Section 10's fixed sigma one. -/
def sigma1 : ℝ := 41 / 125
/-- Section 10's fixed sigma two. -/
def sigma2 : ℝ := 141 / 500

/-- The printed parameters satisfy equation 10.1 and the Lemma 9.2 constraint. -/
theorem parameters_admissible :
    kappa1 < kappa2 ∧ kappa2 ≤ 1 / 8 ∧ (1 / 4 : ℝ) < sigma2 ∧
      sigma2 < sigma1 ∧ sigma1 < 1 / 3 ∧ 1 < 3 * sigma1 + kappa1 ∧
      1 < 2 * sigma1 + sigma2 + kappa2 ∧ 3 * kappa1 + 1 / 4 = 1 / 2 := by
  norm_num [kappa1, kappa2, sigma1, sigma2]

/-- Every Buchstab argument in the F13 integral exceeds three and a half. -/
theorem fourfold13_argument (t1 t2 t3 t4 : ℝ) (ht2 : 0 < t2)
    (h1 : t1 ≤ kappa2) (h2 : t2 ≤ kappa2) (h3 : t3 ≤ kappa2)
    (h4 : t4 ≤ kappa2) :
    (3.5 : ℝ) ≤ (1 - t1 - t2 - t3 - t4) / t2 := by
  rw [le_div_iff₀ ht2]
  norm_num [kappa2] at *
  linarith

/-- Every Buchstab argument in the F14 integral exceeds three and a half. -/
theorem fourfold14_argument (t1 t2 t3 t4 : ℝ) (ht2 : 0 < t2)
    (h1 : t1 ≤ kappa2) (h2 : t2 ≤ kappa2)
    (h4 : t4 ≤ 1 / 2 - 2 * kappa1 - t3) :
    (3.5 : ℝ) ≤ (1 - t1 - t2 - t3 - t4) / t2 := by
  rw [le_div_iff₀ ht2]
  norm_num [kappa1, kappa2] at *
  linarith

/-- The twelve coefficients in the final display on page 42.
The order is 0, 1, 2, 3, 4, 5, 7, 8, 9, 10, 13, 14. -/
def weighted (v : Fin 12 → ℝ) : ℝ :=
  4 * v 0 - v 1 - v 2 - v 3 + v 4 + v 5 -
    2 * v 6 - 2 * v 7 - v 8 - v 9 - v 10 - v 11

/-- The twelve actual sieve counts retained from Lemma 9.2.
For Upsilon 13 and 14 the modulus excludes p one as in the intended reading
already used for the analogous sums elsewhere in this folder. -/
def sieveTerms (N : ℕ) : Fin 12 → ℝ :=
  let A := primeSequence N
  let y := fun k : ℝ => (N : ℝ) ^ k
  ![(S A 1 N (y kappa1) : ℝ),
    (∑ p ∈ PS N (y kappa1) (y kappa2), S A p N p : ℕ),
    (∑ p ∈ PS N (y kappa1) (y sigma1), S A p N (y kappa1) : ℕ),
    (∑ p ∈ PS N (y kappa1) (y sigma2), S A p N (y kappa1) : ℕ),
    (∑ q ∈ P2 N (fun p q => y kappa1 ≤ p ∧ p < q ∧ (q : ℝ) < y kappa2),
      S A (q.1 * q.2) N (y kappa1) : ℕ),
    (∑ q ∈ P2 N (fun p q => y kappa1 ≤ p ∧ (p : ℝ) < y kappa2 ∧
      y kappa2 ≤ q ∧ (q : ℝ) < y (1 / 2 - 2 * kappa1) / p),
      S A (q.1 * q.2) N (y kappa1) : ℕ),
    (∑ q ∈ P2 N (fun p q => y sigma1 ≤ p ∧ p < q ∧
      (q : ℝ) < Real.sqrt ((N : ℝ) / p)), S A (q.1 * q.2) (N * q.1) q.2 : ℕ),
    (∑ q ∈ P2 N (fun p q => y sigma2 ≤ p ∧ p < q ∧
      (q : ℝ) < Real.sqrt ((N : ℝ) / p)), S A (q.1 * q.2) (N * q.1) q.2 : ℕ),
    (∑ q ∈ P2 N (fun p q => y kappa1 ≤ p ∧ (p : ℝ) < y sigma1 ∧
      y sigma1 ≤ q ∧ (q : ℝ) < Real.sqrt ((N : ℝ) / p)),
      S A (q.1 * q.2) (N * q.1) q.2 : ℕ),
    (∑ q ∈ P2 N (fun p q => y kappa2 ≤ p ∧ (p : ℝ) < y sigma2 ∧
      y sigma2 ≤ q ∧ (q : ℝ) < Real.sqrt ((N : ℝ) / p)),
      S A (q.1 * q.2) (N * q.1) (y sigma1) : ℕ),
    (∑ q ∈ P4 N (fun p q r s => y kappa1 ≤ p ∧ p < q ∧ q < r ∧ r < s ∧
      (s : ℝ) < y kappa2),
      S A (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1 : ℕ),
    (∑ q ∈ P4 N (fun p q r s => y kappa1 ≤ p ∧ p < q ∧ q < r ∧
      (r : ℝ) < y kappa2 ∧ y kappa2 ≤ s ∧
      (s : ℝ) < y (1 / 2 - 2 * kappa1) / r),
      S A (q.1 * q.2.1 * q.2.2.1 * q.2.2.2) (N * q.1) q.2.1 : ℕ)]

/-- The fourfold Buchstab integral common to F13 and F14 in equation 10.12.
The upper endpoint for t four distinguishes the two terms. -/
def fourfold (ω : ℝ → ℝ) (last : ℝ → ℝ) (a b : ℝ) (lower weight : ℝ → ℝ) : ℝ :=
  ∫ t1 in a..b,
    (∫ t2 in t1..kappa2,
      (∫ t3 in t2..kappa2,
        (∫ t4 in lower t3..last t3,
          ω ((1 - t1 - t2 - t3 - t4) / t2) / t4) / t3) / t2 ^ 2) /
      weight t1

/-- F0 to F14 from equations 10.2 to 10.12, in the order used by sieveTerms. -/
def integralTerms (F f ω : ℝ → ℝ) : Fin 12 → ℝ :=
  let eg := exp eulerMascheroniConstant
  ![2 * f (1 / (2 * kappa1)) / (kappa1 * eg),
    4 / eg * ∫ t in (1 / (2 * kappa2) - 1)..(1 / (2 * kappa1) - 1), F t,
    4 / eg * ∫ t in ((1 / 2 - sigma1) / kappa1)..((1 / 2 - kappa1) / kappa1),
      F t / (1 - 2 * kappa1 * t),
    4 / eg * ∫ t in ((1 / 2 - sigma2) / kappa1)..((1 / 2 - kappa1) / kappa1),
      F t / (1 - 2 * kappa1 * t),
    2 / (kappa1 * eg) * ∫ t in kappa1..kappa2,
      (∫ u in t..kappa2, f ((1 / 2 - t - u) / kappa1) / u) / t,
    2 / (kappa1 * eg) * ∫ t in kappa1..kappa2,
      (∫ u in kappa2..(1 / 2 - 2 * kappa1 - t),
        f ((1 / 2 - t - u) / kappa1) / u) / t,
    8 * ∫ t in (2 : ℝ)..(1 / sigma1 - 1), log (t - 1) / t,
    8 * ∫ t in (2 : ℝ)..(1 / sigma2 - 1), log (t - 1) / t,
    36 / 5 * (∫ t in kappa1..(1 / 10 : ℝ),
      log (1 / sigma1 - 1 - t / sigma1) / (t * (1 - t) ^ 2)) +
      8 * ∫ t in (1 / 10 : ℝ)..sigma1,
        log (1 / sigma1 - 1 - t / sigma1) / (t * (1 - t)),
    8 * ∫ t in kappa2..sigma2,
      log (1 / sigma2 - 1 - t / sigma2) / (t * (1 - t)),
    36 / 5 * fourfold ω (fun _ => kappa2) kappa1 (1 / 10) id (fun t => t * (1 - t)) +
      8 * fourfold ω (fun _ => kappa2) (1 / 10) kappa2 id id,
    36 / 5 * fourfold ω (fun t => 1 / 2 - 2 * kappa1 - t) kappa1 (1 / 10) (fun _ => kappa2) (fun t => t * (1 - t)) +
      8 * fourfold ω (fun t => 1 / 2 - 2 * kappa1 - t) (1 / 10) kappa2 (fun _ => kappa2) id]

/-- LEAF. Wu 2004 page 6 equation 2.6 and page 9 Lemma 2.10.
The standard linear sieve pair and Buchstab function exist. -/
theorem standard_functions : ∃ F f ω : ℝ → ℝ, IsLinearSieve F f ∧ IsBuchstab ω := by
  sorry

/-- LEAF. Wu 2004 pages 34 to 37 equation 9.4, specialized to page 42's parameters.
Drop the four nonnegative terms and retain the stated power remainder. -/
theorem weighted_sieve_power : ∃ C : ℝ, 0 ≤ C ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      weighted (sieveTerms N) ≤ 4 * (D12 N : ℝ) + C * (N : ℝ) ^ (11 / 12 : ℝ) := by
  sorry

/-- Absorb the remainder with the proved elementary normalization theorem.
CONDITIONAL ON weighted_sieve_power only. -/
theorem weighted_sieve : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      weighted (sieveTerms N) - ε * Θ N ≤ 4 * (D12 N : ℝ) := by
  intro ε hε
  obtain ⟨C, hC, M, hM⟩ := weighted_sieve_power
  obtain ⟨K, hK⟩ := power_remainder_absorbed C ε hC hε
  refine ⟨max M K, ?_⟩
  intro N hEven hN
  have hw := hM N hEven ((le_max_left M K).trans hN)
  have he := hK N ((le_max_right M K).trans hN)
  linarith

/-- LEAF. Wu 2004 pages 38 and 39 equations 10.2 and 10.5.
The three positively weighted terms have their printed lower estimates. -/
theorem positive_estimates (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      (integralTerms F f ω 0 - ε) * Θ N ≤ sieveTerms N 0 ∧
      (integralTerms F f ω 4 - ε) * Θ N ≤ sieveTerms N 4 ∧
      (integralTerms F f ω 5 - ε) * Θ N ≤ sieveTerms N 5 := by
  sorry

/-- LEAF. Wu 2004 pages 39 to 41 equations 10.3, 10.4, 10.10 to 10.12.
The nine negatively weighted terms have their printed upper estimates. -/
theorem negative_estimates (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({1, 2, 3, 6, 7, 8, 9, 10, 11} : Finset (Fin 12)) →
        sieveTerms N i ≤ (integralTerms F f ω i + ε) * Θ N := by
  sorry

/-- LEAF. Wu 2004 page 42 final display of Section 10.
This bounds actual integrals, rather than comparing equal rational constants. -/
theorem integral_evaluation (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) :
    (3344307 : ℝ) / 4000000 ≤ weighted (integralTerms F f ω) / 4 := by
  sorry

/-- Componentwise bounds lose seventeen epsilon units in the weighted sum. -/
theorem weighted_comparison (v w : Fin 12 → ℝ) (t ε : ℝ)
    (hp : ∀ i : Fin 12, i ∈ ({0, 4, 5} : Finset (Fin 12)) → (v i - ε) * t ≤ w i)
    (hn : ∀ i : Fin 12, i ∈ ({1, 2, 3, 6, 7, 8, 9, 10, 11} : Finset (Fin 12)) →
      w i ≤ (v i + ε) * t) :
    weighted v * t - 17 * ε * t ≤ weighted w := by
  have h0 := hp 0 (by decide)
  have h4 := hp 4 (by decide)
  have h5 := hp 5 (by decide)
  have h1 := hn 1 (by decide)
  have h2 := hn 2 (by decide)
  have h3 := hn 3 (by decide)
  have h6 := hn 6 (by decide)
  have h7 := hn 7 (by decide)
  have h8 := hn 8 (by decide)
  have h9 := hn 9 (by decide)
  have h10 := hn 10 (by decide)
  have h11 := hn 11 (by decide)
  dsimp only [weighted]
  linarith

/-- The exact statement of thm2_analytic_link follows from the five open leaves.
Its rational hypothesis carries no information about the integrals. -/
theorem thm2_analytic_link_checked (h : (83607 : ℝ) / 100000 ≤ 0.83607) :
    ChenLower 0.836 := by
  obtain ⟨F, f, ω, hF, hω⟩ := standard_functions
  obtain ⟨Nw, hw⟩ := weighted_sieve (1 / 1000000) (by norm_num)
  obtain ⟨Np, hp⟩ := positive_estimates F f ω hF hω (1 / 1000000) (by norm_num)
  obtain ⟨Nn, hn⟩ := negative_estimates F f ω hF hω (1 / 1000000) (by norm_num)
  have heval := integral_evaluation F f ω hF hω
  refine ⟨max Nw (max Np Nn), ?_⟩
  intro N hEven hN
  have hwN := hw N hEven (by omega)
  have hpN := hp N hEven (by omega)
  have hnN := hn N hEven (by omega)
  have hpositive : ∀ i : Fin 12, i ∈ ({0, 4, 5} : Finset (Fin 12)) →
      (integralTerms F f ω i - 1 / 1000000) * Θ N ≤ sieveTerms N i := by
    intro i hi
    simp only [mem_insert, mem_singleton] at hi
    rcases hi with rfl | rfl | rfl
    · exact hpN.1
    · exact hpN.2.1
    · exact hpN.2.2
  have hcomb := weighted_comparison (integralTerms F f ω) (sieveTerms N)
    (Θ N) (1 / 1000000) hpositive hnN
  have hscaled := mul_le_mul_of_nonneg_right heval (Θ_nonneg N)
  have ht := Θ_nonneg N
  nlinarith only [hwN, hcomb, hscaled, ht]

end LeanLab.ChenDoubleSieve.Task275
