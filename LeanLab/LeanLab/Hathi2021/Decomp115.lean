/-
P0101 Liqun Hu, Acta Arithmetica 191, 2019, pages 191 to 200.
DOI https://doi.org/10.4064/aa190121-10-4
Fallback decomposition of Theorem 1.1, printed page 192, closing proof page 199.
AI wrote this Lean code. Binary Goldbach is OPEN.
The analytic lower bound remains CONDITIONAL ON the cited circle method inputs.
-/
import LeanLab.Hathi2021.PairLinnik

open Finset Real

namespace LeanLab.Hathi2021.Decomp115

/-- Display 1.1 on page 192, with shared powers and positive exponents. -/
def PairWitness (n₁ n₂ : ℕ) (p : Fin 6 → ℕ) (ν : Fin 82 → ℕ) : Prop :=
  (∀ i, (p i).Prime) ∧ (∀ i, 1 ≤ ν i) ∧
    n₁ = p 0 + p 1 ^ 2 + p 2 ^ 2 + ∑ i, 2 ^ ν i ∧
    n₂ = p 3 + p 4 ^ 2 + p 5 ^ 2 + ∑ i, 2 ^ ν i

/-- CITED. Theorem 1.1 on page 192. The threshold depends on the fixed ratio bound. -/
def HuTheorem11 : Prop :=
  ∀ C : ℝ, 1 < C → ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
    Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
    ∃ p ν, PairWitness n₁ n₂ p ν

/-- Page 193 weighted count, enlarged to all solutions bounded by n₁.
The paper's restricted prime and exponent ranges form a subset. -/
noncomputable def weightedCount (n₁ n₂ : ℕ) : ℝ := by
  classical
  exact ∑ x : (Fin 6 → Fin (n₁ + 1)) × (Fin 82 → Fin (n₁ + 1)),
    if PairWitness n₁ n₂ (fun i => (x.1 i).val) (fun i => (x.2 i).val)
    then ∏ i : Fin 6, Real.log ((x.1 i).val : ℝ) else 0

/-- Page 192, the logarithmic scale used in the arc estimates. -/
noncomputable def logScale (n : ℕ) : ℝ := Real.log (n / Real.log n) / Real.log 2

/-- LEAF. Page 199, Lemmas 2.2, 2.4 and 2.5 combined, with the vanishing
error absorbed into any positive ε. The enlarged weighted count is at least
this lower bound. This leaf needs Hu and Liu, reference 2, Kong and Liu,
reference 5, Platt and Trudgian, reference 16, Rieger, reference 17, and Zhao, reference 18.
The numerical and local factor questions in PROGRESS.md remain open inputs. -/
theorem analytic_lower_bound (C ε : ℝ) (hC : 1 < C) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ n₁ n₂ : ℕ,
      Odd n₁ → Odd n₂ → N₀ ≤ n₂ → n₂ < n₁ → (n₁ : ℝ) ≤ C * n₂ →
      (PairLinnik.margin101 (108238 / 10) 82 - ε) *
        ((n₁ : ℝ) * n₂ * logScale n₁ ^ 82) ≤ weightedCount n₁ n₂ := by
  sorry

/-- LEAF. Page 199, the closing numerical inequality at k = 82. -/
theorem margin_pos : 0 < PairLinnik.margin101 (108238 / 10) 82 := by
  exact PairLinnik.p0101_reproduced.1

/-- LEAF. Page 192, the scale L is positive for n at least 16. -/
theorem logScale_pos (n : ℕ) (hn : 16 ≤ n) : 0 < logScale n := by
  have h1 : (1 : ℝ) < n := by exact_mod_cast (show 1 < n by omega)
  have hp : (0 : ℝ) < n := lt_trans zero_lt_one h1
  have hlog : 0 < Real.log n := by exact?
  have hlt : Real.log (n : ℝ) < n := by
    linarith [Real.log_le_sub_one_of_pos hp]
  unfold logScale
  apply div_pos
  · apply Real.log_pos
    exact (one_lt_div hlog).mpr hlt
  · exact Real.log_pos (by norm_num)

/-- LEAF. Page 193, a positive weighted number of solutions gives a solution
of display 1.1. The finite enlargement keeps exactly the shared exponents. -/
theorem solution_of_weightedCount_pos (n₁ n₂ : ℕ) (h : 0 < weightedCount n₁ n₂) :
    ∃ p ν, PairWitness n₁ n₂ p ν := by
  classical
  unfold weightedCount at h
  obtain ⟨x, _, hx⟩ := Finset.exists_ne_zero_of_sum_ne_zero (ne_of_gt h)
  by_cases hw : PairWitness n₁ n₂ (fun i => (x.1 i).val) (fun i => (x.2 i).val)
  · exact ⟨_, _, hw⟩
  · simp only [if_neg hw] at hx
    exact (hx rfl).elim

/-- Theorem 1.1 assembled from the leaves. CONDITIONAL ON analytic_lower_bound. -/
theorem hu_theorem_1_1 : HuTheorem11 := by
  intro C hC
  obtain ⟨N₀, hN₀⟩ := analytic_lower_bound C
    (PairLinnik.margin101 (108238 / 10) 82 / 2) hC (half_pos margin_pos)
  refine ⟨max N₀ 16, ?_⟩
  intro n₁ n₂ ho₁ ho₂ hn₂ hlt hratio
  have h16 : 16 ≤ n₂ := (le_max_right _ _).trans hn₂
  have hn₁ : 16 ≤ n₁ := by omega
  have hbound := hN₀ n₁ n₂ ho₁ ho₂ ((le_max_left _ _).trans hn₂) hlt hratio
  apply solution_of_weightedCount_pos
  have hscale := logScale_pos n₁ hn₁
  have hp₁ : (0 : ℝ) < n₁ := by exact_mod_cast (show 0 < n₁ by omega)
  have hp₂ : (0 : ℝ) < n₂ := by exact_mod_cast (show 0 < n₂ by omega)
  have hcoef : 0 < PairLinnik.margin101 (108238 / 10) 82 -
      PairLinnik.margin101 (108238 / 10) 82 / 2 := by linarith [margin_pos]
  exact lt_of_lt_of_le (mul_pos hcoef (by positivity)) hbound

/-- Display 1.1, page 192. A concrete unequal odd pair satisfies the witness predicate. -/
theorem pairWitness_example :
    PairWitness 187 185 ![5, 3, 3, 3, 3, 3] (fun _ => 1) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i
    fin_cases i <;> norm_num
  · intro i
    exact le_rfl
  · norm_num
  · norm_num

/-- Page 193, every prime solution carries a positive logarithmic weight. -/
theorem prime_weight_pos (p : Fin 6 → ℕ) (hp : ∀ i, (p i).Prime) :
    0 < ∏ i, Real.log (p i : ℝ) := by
  apply Finset.prod_pos
  intro i _
  apply Real.log_pos
  exact_mod_cast (hp i).one_lt

/-- Page 193, a concrete positive count certifies the extraction leaf is nonvacuous. -/
theorem weightedCount_example : 0 < weightedCount 187 185 := by
  classical
  let T := (Fin 6 → Fin 188) × (Fin 82 → Fin 188)
  let x : T := (![5, 3, 3, 3, 3, 3], fun _ => 1)
  have hp : (fun i => (x.1 i).val) = ![5, 3, 3, 3, 3, 3] := by
    funext i
    fin_cases i <;> rfl
  have hν : (fun i => (x.2 i).val) = (fun _ => 1) := rfl
  have hx : PairWitness 187 185 (fun i => (x.1 i).val) (fun i => (x.2 i).val) := by
    rw [hp, hν]
    exact pairWitness_example
  let w (y : T) : ℝ :=
    if PairWitness 187 185 (fun i => (y.1 i).val) (fun i => (y.2 i).val)
    then ∏ i : Fin 6, Real.log ((y.1 i).val : ℝ) else 0
  have hw : 0 < w x := by
    dsimp only [w]
    rw [if_pos hx]
    exact prime_weight_pos _ hx.1
  have hsum : w x ≤ ∑ y : T, w y := by
    apply Finset.single_le_sum _ (Finset.mem_univ x)
    intro y _
    dsimp only [w]
    split_ifs with hy
    · exact (prime_weight_pos _ hy.1).le
    · exact le_rfl
  change w x ≤ weightedCount 187 185 at hsum
  exact hw.trans_le hsum

end LeanLab.Hathi2021.Decomp115
