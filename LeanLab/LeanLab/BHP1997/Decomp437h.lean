/-
P0069, page 14, the two third-factor branches of mixed Case 3.
The small branch uses the completed dominant square moment and a mean square.
The large branch retains the bounded-power interpolation work.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp437f

namespace LeanLab.BHP1997.Decomp437h
open Classical Complex Thm4 MeanSquareC165 DecompC165c Decomp414a Decomp437c Decomp437d Decomp437f
open scoped BigOperators

/-- LEAF. Page 14, Case 3 i, display 3.14.
The third factor has norm at most its length to one quarter.
CONDITIONAL on the original three inputs. -/
theorem first_small_third (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
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
    ∑ p ∈ thirdNormPart (casePart S
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) true false)
      (fun p => dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1))
      (X ^ (1 - α₁ - α₂)) true, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  intro B
  refine ⟨1, by norm_num, ?_⟩
  intro ε hε hεη c₁ c₂ hc₁ hc₂ Kfun A hA
  obtain ⟨Cm, hCm, hm⟩ := hmean B c₁ c₂ hc₁ hc₂
  obtain ⟨Ce, K0, hCe, hK0, he⟩ := energy_log_uniform henergy B c₁ c₂ hc₁ hc₂
  obtain ⟨Cd, Dd, hCd, hDd, hd⟩ := Decomp437e.dominant_square_moment hmean hlarge henergy B c₁ c₂ hc₁ hc₂
  let D0 := max Dd (K0 + 1)
  have hD0 : 0 ≤ D0 := hDd.trans (le_max_left _ _)
  let H := Cd + 2 * Cm * Ce
  let R := ((ε / 4) / (A + D0)) ^ (-(A + D0))
  have hH : 0 < H := by dsimp [H]; positivity
  have hR : 0 ≤ R := by dsimp [R]; positivity
  refine ⟨H * R, ?_⟩
  intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb hecoeff hsmall
  let M := X ^ α₁
  let N := X ^ α₂
  let L := X ^ (1 - α₁ - α₂)
  let Q : ℝ := (q : ℝ) * T
  let P := thirdNormPart (casePart S
    (fun p => dominanceFlag Q M (dirPoly a c₁ c₂ M p.2 (half p.1)))
    (fun p => dominanceFlag Q N (dirPoly b c₁ c₂ N p.2 (half p.1))) true false)
    (fun p => dirPoly e c₁ c₂ L p.2 (half p.1)) L true
  have hsub : P ⊆ S := (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  have hx3 : 3 ≤ x := by linarith
  have hlx : 1 ≤ Real.log x := by
    have hh := Real.log_le_log (by norm_num : (0 : ℝ) < 3) hx3
    linarith [Real.log_three_gt_d9]
  have hlx0 : 0 < Real.log x := by linarith
  have hXge : x ≤ X := by
    rcases hX with rfl | rfl
    · exact le_rfl
    · rw [← Real.rpow_mul_natCast (by linarith : 0 ≤ x)]
      calc
        x = x ^ (1 : ℝ) := (Real.rpow_one x).symm
        _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num; linarith)
  have hX0 : 0 < X := by linarith
  have hX1 : 1 ≤ X := by linarith
  have hQ0 : 0 ≤ Q := by dsimp [Q]; positivity
  have hlog0 : 0 ≤ Real.log x ^ D0 := Real.rpow_nonneg hlx0.le _
  by_cases hEmpty : P = ∅
  · change (∑ p ∈ P, _) ≤ _
    rw [hEmpty, Finset.sum_empty]
    positivity
  obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hEmpty
  have hcase := (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2
  have hNQ : N < Q := nondominant_scale_lt (by dsimp [N]; linarith) hcase.2
  have hsp : WellSpaced P := by
    intro p hp p' hp' hne heq
    exact hspace p (hsub hp) p' (hsub hp') hne heq
  have htime : ∀ p ∈ P, |p.1| ≤ T := fun p hp => htimes p (hsub hp)
  have hHc : Cd ≤ H := by
    dsimp [H]
    have hh : 0 ≤ 2 * Cm * Ce := by positivity
    linarith
  have hHm : 2 * Cm * Ce ≤ H := by dsimp [H]; linarith
  have hlogd : Real.log x ^ Dd ≤ Real.log x ^ D0 :=
    Real.rpow_le_rpow_of_exponent_le hlx (le_max_left _ _)
  have hlogk : Real.log x ^ (K0 + 1) ≤ Real.log x ^ D0 :=
    Real.rpow_le_rpow_of_exponent_le hlx (le_max_right _ _)
  have hmomentM : (∑ p ∈ P, ‖dirPoly a c₁ c₂ M p.2 (half p.1)‖ ^ 2) ≤
      H * M * Real.log x ^ D0 := by
    have hh := hd x M T q P a ha hx hM hMx hT hTx hq hqx hsp htime
      (by intro p hp; exact (Finset.mem_filter.mp (Finset.mem_filter.mp hp).1).2.1)
    exact hh.trans (mul_le_mul (mul_le_mul_of_nonneg_right hHc (by dsimp [M]; positivity))
      hlogd (by positivity) (by dsimp [M]; positivity))
  have hmomentN : (∑ p ∈ P, ‖dirPoly b c₁ c₂ N p.2 (half p.1)‖ ^ 2) ≤
      H * Q * Real.log x ^ D0 := by
    have hmF := hm x N T q P b hb hx hN hNx hT hTx hq hqx hsp htime
    have heF := he b hb x N hlx hN hNx
    have hEnonneg : 0 ≤ energy b c₁ c₂ N := Finset.sum_nonneg (fun n hn => by positivity)
    calc
      _ ≤ Cm * Real.log x * (Q + N) * energy b c₁ c₂ N := hmF
      _ ≤ Cm * Real.log x * (2 * Q) * (Ce * Real.log x ^ K0) := by gcongr <;> linarith
      _ = (2 * Cm * Ce) * Q * (Real.log x ^ K0 * Real.log x) := by ring
      _ = (2 * Cm * Ce) * Q * Real.log x ^ (K0 + 1) := by rw [Real.rpow_add hlx0, Real.rpow_one]
      _ ≤ H * Q * Real.log x ^ D0 := mul_le_mul
        (mul_le_mul_of_nonneg_right hHm hQ0) hlogk (by positivity) (by positivity)
  have hpair' := Decomp437a.pair_of_square_bounds P
    (fun p => dirPoly a c₁ c₂ M p.2 (half p.1))
    (fun p => dirPoly b c₁ c₂ N p.2 (half p.1)) hH.le
    (by dsimp [M]; positivity) hQ0 (Real.rpow_nonneg hlx0.le D0) hmomentM hmomentN
  have htriple := Decomp437a.triple_of_pair_bound P
    (fun p => dirPoly a c₁ c₂ M p.2 (half p.1))
    (fun p => dirPoly b c₁ c₂ N p.2 (half p.1))
    (fun p => dirPoly e c₁ c₂ L p.2 (half p.1))
    (by dsimp [L]; positivity : 0 ≤ L ^ (1 / 4 : ℝ)) hpair'
    (by intro p hp; exact of_decide_eq_true (Finset.mem_filter.mp hp).2)
  have hpow : Real.sqrt M * Real.sqrt Q * L ^ (1 / 4 : ℝ) ≤ X ^ (1 / 2 - ε / 4) := by
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, show Q = X ^ (1 - θ) from hqT]
    dsimp [M, L]
    rw [← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le, ← Real.rpow_mul hX0.le,
      ← Real.rpow_add hX0, ← Real.rpow_add hX0]
    apply Real.rpow_le_rpow_of_exponent_le hX1
    have hab' := (abs_lt.mp hab).2
    linarith
  have hsave := power_saving_with_log (by linarith : 1 < x) hXge hA
    (by linarith : 0 < ε / 4) hD0
  calc
    _ ≤ (H * Real.sqrt M * Real.sqrt Q * Real.log x ^ D0) * L ^ (1 / 4 : ℝ) := htriple
    _ = H * (Real.sqrt M * Real.sqrt Q * L ^ (1 / 4 : ℝ)) * Real.log x ^ D0 := by ring
    _ ≤ H * X ^ (1 / 2 - ε / 4) * Real.log x ^ D0 :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hH.le) hlog0
    _ = H * (X ^ (1 / 2 - ε / 4) * Real.log x ^ D0) := by ring
    _ ≤ H * (R * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) := mul_le_mul_of_nonneg_left hsave hH.le
    _ = _ := by ring

/-- LEAF. Page 14, Case 3 ii, displays 3.15 and 3.16.
Only the part above the third norm threshold remains. The bounded choice
of polynomial power and its level-set summation remain OPEN.
Retain the existing proved repair for the g equal to one branch.
CONDITIONAL on the original three inputs. -/
theorem first_large_third (hmean : Lemma1MeanSquare) (hlarge : Lemma1LargeValues)
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
    ∑ p ∈ thirdNormPart (casePart S
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₁) (dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1)))
      (fun p => dominanceFlag ((q : ℝ) * T) (X ^ α₂) (dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1))) true false)
      (fun p => dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1))
      (X ^ (1 - α₁ - α₂)) false, ‖dirPoly a c₁ c₂ (X ^ α₁) p.2 (half p.1) * dirPoly b c₁ c₂ (X ^ α₂) p.2 (half p.1) *
      dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1)‖ ≤
      C * X ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- Page 14, exact original mixed-case target from its two written branches.
CONDITIONAL on the large-third-factor leaf and original inputs. -/
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
  intro B
  obtain ⟨η0, hη0, h0⟩ := first_small_third hmean hlarge henergy B
  obtain ⟨η1, hη1, h1⟩ := first_large_third hmean hlarge henergy B
  refine ⟨min η0 η1, lt_min hη0 hη1, ?_⟩
  intro ε hε hεη c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C0, hc0⟩ := h0 ε hε (lt_of_lt_of_le hεη (min_le_left _ _)) c₁ c₂ hc₁ hc₂ K A hA
  obtain ⟨C1, hc1⟩ := h1 ε hε (lt_of_lt_of_le hεη (min_le_right _ _)) c₁ c₂ hc₁ hc₂ K A hA
  refine ⟨C0 + C1, ?_⟩
  intro θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have hs0 := hc0 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  have hs1 := hc1 θ α₁ α₂ x X T q S a b e hθ hθu hab hgam hx hX hq hqx hT hTx hqT
    hM hMx hN hNx hL hLx hspace htimes ha hb he hsmall
  rw [sum_third_parts _ (fun p => dirPoly e c₁ c₂ (X ^ (1 - α₁ - α₂)) p.2 (half p.1))
    (X ^ (1 - α₁ - α₂))]
  exact (add_le_add hs0 hs1).trans_eq (by ring)

/-- Page 15, Case 4 follows from the new exact Case 3 supply by symmetry.
CONDITIONAL on the same explicit inputs and the OPEN mixed large-third-factor leaf. -/
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

end LeanLab.BHP1997.Decomp437h
