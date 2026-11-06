/-
P0069, pages 12 to 15. Theorem 4 split along its four dominance cases.
The three distinct analytic cases are OPEN. The fourth is symmetry.
The exact dyadic_mean_value assembly is CONDITIONAL on the OPEN cases.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165c

namespace LeanLab.BHP1997.Decomp414a
open Classical Complex Thm4 MeanSquareC165 DecompC165c

/-- Page 13, the dominance test immediately above Case 1.
For a nonzero value z, sigma is one half plus log norm z divided by log F.
At zero the tag is harmless because the product summand is zero. -/
noncomputable def dominanceFlag (Q F : ℝ) (z : ℂ) : Bool :=
  decide (Q ≤ F ^ Thm4.c (1 / 2 + Real.log ‖z‖ / Real.log F))

/-- Pages 13 to 15, the part of a finite set with two prescribed dominance tags. -/
noncomputable def casePart {α : Type*} (S : Finset α) (f g : α → Bool)
    (u v : Bool) : Finset α := S.filter (fun p => f p = u ∧ g p = v)

/-- Pages 13 to 15, finite sum partition into the four dominance cases.
LeanSearch and Loogle find Finset.sum_filter_add_sum_filter_not.
The Boolean normal form below is its twice-refined partition. -/
theorem sum_four_parts {α : Type*} (S : Finset α) (f g : α → Bool) (w : α → ℝ) :
    ∑ p ∈ S, w p =
      (∑ p ∈ casePart S f g true true, w p) +
      (∑ p ∈ casePart S f g false false, w p) +
      (∑ p ∈ casePart S f g true false, w p) +
      (∑ p ∈ casePart S f g false true, w p) := by
  simp only [casePart, Finset.sum_filter]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  cases hf : f p <;> cases hg : g p <;> simp [hf, hg]

/-- Page 15, Case 4 interchanges the two dominance coordinates. -/
theorem casePart_swap {α : Type*} (S : Finset α) (f g : α → Bool) (u v : Bool) :
    casePart S f g u v = casePart S g f v u := by
  ext p
  simp [casePart, and_comm]

/-- Page 13, local consistency of the two sides of the dominance test.
The nonzero values 1 and 4 give opposite tags at Q equal to 8 and F equal to 4. -/
theorem dominance_flag_instances :
    dominanceFlag 8 4 1 = false ∧ dominanceFlag 8 4 4 = true := by
  have hl : Real.log (4 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  norm_num [dominanceFlag, Thm4.c, hl]

/-- LEAF. Page 13, Case 1, displays 3.11 and 3.12, followed by 3.2.
Dyadically sum only the part where both first terms dominate.
This uses the logarithmic energy bound, not a positive power substitute.
OPEN. CONDITIONAL on the three explicit analytic inputs. -/
theorem both_dominant (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) :
    ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
    ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a b e : ℕ → ℂ,
    1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
    2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
    1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
    2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
    2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    CoeffBound a B → CoeffBound b B → CoeffBound e B →
    (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
      ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
    ∑ p ∈ casePart S
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) true true, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- LEAF. Page 13, Case 2 i and ii, displays 3.10 to 3.13.
Dyadically sum only the part where neither first term dominates.
The three branches of gamma provide the power savings.
OPEN. CONDITIONAL on the three explicit analytic inputs. -/
theorem neither_dominant (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) :
    ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
    ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a b e : ℕ → ℂ,
    1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
    2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
    1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
    2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
    2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    CoeffBound a B → CoeffBound b B → CoeffBound e B →
    (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
      ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
    ∑ p ∈ casePart S
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) false false, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- LEAF. Page 14, Case 3 i and ii, displays 3.14 to 3.16.
Dyadically sum only the part where the first polynomial dominates.
Use the repaired g equal to one branch already proved in DecompC165c.
The bounded power selection and the remaining summation are retained here.
OPEN. CONDITIONAL on the three explicit analytic inputs. -/
theorem first_dominant (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) :
    ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
    ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a b e : ℕ → ℂ,
    1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
    2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
    1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
    2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
    2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    CoeffBound a B → CoeffBound b B → CoeffBound e B →
    (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
      ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
    ∑ p ∈ casePart S
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) true false, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- Page 15, Case 4 follows from Case 3 by interchanging M and N.
CONDITIONAL on first_dominant and its three explicit analytic inputs. -/
theorem second_dominant (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) :
    ∀ B : ℝ, ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
    ∀ c₁ c₂ : ℝ, 0 < c₁ → c₁ < c₂ → ∀ K : ℝ → ℝ, ∀ A : ℝ, 0 < A → ∃ C : ℝ,
    ∀ θ α₁ α₂ x X T : ℝ, ∀ q : ℕ, ∀ S : Finset (ℝ × DirichletCharacter ℂ q),
    ∀ a b e : ℕ → ℂ,
    1 / 2 + ε < θ → θ < 7 / 12 → |α₁ - α₂| < 2 * θ - 1 - ε → 1 - (α₁ + α₂) < gam θ - ε →
    2 ≤ x → (X = x ∨ X = (x ^ (11 / 20 + ε)) ^ 2) →
    1 ≤ q → (q : ℝ) ≤ x → 2 < T → T ≤ x / 4 → (q : ℝ) * T = X ^ (1 - θ) →
    2 ≤ X ^ α₁ → X ^ α₁ ≤ x → 2 ≤ X ^ α₂ → X ^ α₂ ≤ x →
    2 ≤ X ^ (1 - α₁ - α₂) → X ^ (1 - α₁ - α₂) ≤ x →
    WellSpaced S → (∀ p ∈ S, |p.1| ≤ T) →
    CoeffBound a B → CoeffBound b B → CoeffBound e B →
    (∀ A' : ℝ, 0 < A' → ∀ p ∈ S,
      ‖dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
        K A' * (X ^ (1 - α₁ - α₂)) ^ (1 / 2 : ℝ) * Real.log x ^ (-A')) →
    ∑ p ∈ casePart S
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) false true, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  intro B
  obtain ⟨η, hη, hcase⟩ := first_dominant hmean hlarge henergy B
  refine ⟨η, hη, ?_⟩
  intro ε hε hεη c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C, hC⟩ := hcase ε hε hεη c₁ c₂ hc₁ hc₂ K A hA
  refine ⟨C, ?_⟩
  intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have h := hC θ α₂ α₁ x X T q S b a e hθ hθu
    (by simpa only [abs_sub_comm] using hab) (by convert hgam using 1 <;> ring)
    hx hX hq hqx hT hTx hqT hN hNx hM hMx
    (by convert hL using 1 <;> congr 1 <;> ring)
    (by convert hLx using 1 <;> congr 1 <;> ring)
    hspace htimes hb ha he (by convert hsmall using 1 <;> congr 1 <;> ring)
  convert h using 1
  · rw [casePart_swap]
    apply Finset.sum_congr rfl
    intro p hp
    congr 1
    congr 1
    · ring
    · congr 2
      ring

/-- Pages 12 to 15, exact original dyadic_mean_value statement assembled
from the four smaller dominance parts. No direct sorry.
CONDITIONAL on the three OPEN cases and the original analytic inputs. -/
theorem dyadic_mean_value (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
    (henergy : EnergyLogBound) : Thm4.Theorem4Paper := by
  intro B
  obtain ⟨η0, hη0, h0⟩ := both_dominant hmean hlarge henergy B
  obtain ⟨η1, hη1, h1⟩ := neither_dominant hmean hlarge henergy B
  obtain ⟨η2, hη2, h2⟩ := first_dominant hmean hlarge henergy B
  obtain ⟨η3, hη3, h3⟩ := second_dominant hmean hlarge henergy B
  refine ⟨min η0 (min η1 (min η2 η3)), by positivity, ?_⟩
  intro ε hε hεη
  have he0 : ε < η0 := lt_of_lt_of_le hεη (min_le_left _ _)
  have he1 : ε < η1 := lt_of_lt_of_le hεη ((min_le_right _ _).trans (min_le_left _ _))
  have he2 : ε < η2 := lt_of_lt_of_le hεη
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have he3 : ε < η3 := lt_of_lt_of_le hεη
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  intro c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C0, hc0⟩ := h0 ε hε he0 c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C1, hc1⟩ := h1 ε hε he1 c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C2, hc2⟩ := h2 ε hε he2 c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C3, hc3⟩ := h3 ε hε he3 c₁ c₂ hc₁ hc₂ K A hA
  refine ⟨C0 + C1 + C2 + C3, ?_⟩
  intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have hb0 := hc0 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have hb1 := hc1 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have hb2 := hc2 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have hb3 := hc3 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  rw [sum_four_parts S
    (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
    (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1)))]
  calc
    _ ≤ C0 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) +
        C1 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) +
        C2 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) +
        C3 * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) :=
      add_le_add (add_le_add (add_le_add hb0 hb1) hb2) hb3
    _ = _ := by ring

end LeanLab.BHP1997.Decomp414a
