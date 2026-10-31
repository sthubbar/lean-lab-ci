import LeanLab.Pintz2021.Lemma2Task99

/-!
P0054 page 14, the bounded family of suspicious conductors before Lemma 2.
Nonnegative singular series weights allow repeated bad exponents to be removed.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.ConductorFamilyTask99

open Finset DivisorSumTask53 Lemma2Task99

attribute [local instance] Classical.propDecidable

/-- Count the singular series weight of a union of conductor conditions once. -/
theorem weighted_union_le (m K : ℕ) (R : Finset ℕ) :
    ∑ ν ∈ ((Icc 1 K).filter (fun ν => 2 ^ ν < m ∧
      ∃ q ∈ R, q ∣ m - 2 ^ ν)), Sing (m - 2 ^ ν) ≤
      ∑ q ∈ R, ∑ ν ∈ eligibleExponents m q K, Sing (m - 2 ^ ν) := by
  have himage : ((R.sigma (fun q => eligibleExponents m q K)).image
      (fun p => p.2)) =
      (Icc 1 K).filter (fun ν => 2 ^ ν < m ∧ ∃ q ∈ R, q ∣ m - 2 ^ ν) := by
    ext ν
    simp only [mem_image, mem_sigma, eligibleExponents, mem_filter]
    constructor
    · rintro ⟨⟨q, t⟩, ⟨hq, ht, htm, hdiv⟩, heq⟩
      change t = ν at heq
      subst t
      exact ⟨ht, htm, q, hq, hdiv⟩
    · rintro ⟨ht, htm, q, hq, hdiv⟩
      exact ⟨⟨q, ν⟩, ⟨hq, ht, htm, hdiv⟩, rfl⟩
  rw [← himage]
  calc
    _ ≤ ∑ p ∈ R.sigma (fun q => eligibleExponents m q K), Sing (m - 2 ^ p.2) :=
      sum_image_le_of_nonneg (s := R.sigma (fun q => eligibleExponents m q K))
        (g := fun p : Σ _q : ℕ, ℕ => p.2)
        (f := fun ν => Sing (m - 2 ^ ν)) (fun _ _ => (Applications.Sing_pos _).le)
    _ = _ := by rw [sum_sigma]

/-- A bounded number of sufficiently large conductors has small total weight. -/
theorem bounded_family {η : ℝ} (hη : 0 < η) (B : ℕ) :
    ∃ Cη : ℝ, ∀ (X : ℝ) (m : ℕ) (R : Finset ℕ), (m : ℝ) ≤ X →
      Cη < X → R.card ≤ B →
      (∀ q ∈ R, Odd q ∧ Squarefree q ∧ Cη < (q : ℝ)) →
      ∑ ν ∈ ((Icc 1 ⌊Lnu X⌋₊).filter (fun ν => 2 ^ ν < m ∧
        ∃ q ∈ R, q ∣ m - 2 ^ ν)), Sing (m - 2 ^ ν) ≤ η * Lnu X := by
  let δ := η / ((B : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C, hC⟩ := lemma2_proved δ hδ
  refine ⟨max C 16, fun X m R hm hX hR hq => ?_⟩
  have hX16 : 16 ≤ X := ((le_max_right C 16).trans_lt hX).le
  have hL : 0 ≤ Lnu X := by
    have := (CutoffTask53.Lnu_bounds hX16).1
    have := Real.logb_nonneg (by norm_num : (1 : ℝ) < 2) (by linarith : 1 ≤ X)
    linarith
  have hterm : ∀ q ∈ R, ∑ ν ∈ eligibleExponents m q ⌊Lnu X⌋₊,
      Sing (m - 2 ^ ν) ≤ δ * Lnu X := by
    intro q hqr
    obtain ⟨hodd, hsq, hqC⟩ := hq q hqr
    exact hC X m q hm hodd hsq (lt_min
      ((le_max_left C 16).trans_lt hqC) ((le_max_left C 16).trans_lt hX))
  have hBδ : (B : ℝ) * δ ≤ η := by
    calc
      _ ≤ ((B : ℝ) + 1) * δ :=
        mul_le_mul_of_nonneg_right (by linarith) hδ.le
      _ = η := by dsimp [δ]; field_simp
  calc
    _ ≤ ∑ q ∈ R, ∑ ν ∈ eligibleExponents m q ⌊Lnu X⌋₊, Sing (m - 2 ^ ν) :=
      weighted_union_le m ⌊Lnu X⌋₊ R
    _ ≤ ∑ _q ∈ R, δ * Lnu X := sum_le_sum hterm
    _ = (R.card : ℝ) * (δ * Lnu X) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ (B : ℝ) * (δ * Lnu X) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast hR) (mul_nonneg hδ.le hL)
    _ = ((B : ℝ) * δ) * Lnu X := by ring
    _ ≤ η * Lnu X := mul_le_mul_of_nonneg_right hBδ hL

end LeanLab.Pintz2021.ConductorFamilyTask99

#print axioms LeanLab.Pintz2021.ConductorFamilyTask99.weighted_union_le

#print axioms LeanLab.Pintz2021.ConductorFamilyTask99.bounded_family
