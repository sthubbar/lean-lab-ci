import LeanLab.HelfgottMajor.BookZeroHonest1123
import Mathlib

/-!
# Split of `BookZeroSplit1122.book_395_nontrivial`, FREE-nv-glm3 task3476

The source is Helfgott, The ternary Goldbach problem, Part I, section 3.7.3.3,
page 86, display 3.95 and footnote 5.  The argument separates characters into
the real case and the non-real case.

For a real character, the one-sided count for the character and its inverse is
twice the one-sided book count.  The pair estimate from Bennett, Martin,
O'Bryant and Rechnitzer then gives the desired bound after division by two.

For a non-real character, the argument in footnote 5 of the book adapts the
two-sided argument of Trudgian, section 2, to give the one-sided bound directly.
That adaptation is the remaining analytic leaf.

AI wrote this Lean code.  Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.BookZeroSplit1122
open LeanLab.HelfgottMajor.ZeroCount1623
open LeanLab.HelfgottMajor.BookZeroHonest1123
open Complex Set Filter Topology

variable {q : ℕ} [NeZero q]

/-- LEAF: Pair estimate step.  For a primitive character of modulus greater than one,
the sum of the one-sided book counts of the character and its inverse differs from
twice the book main term by at most `0.298 log (qT) + 4.358`.  This is the corrected
two-sided zero count of Bennett, Martin, O'Bryant and Rechnitzer, with the endpoint
weights of the book convention.  It is strictly easier than the one-sided target. -/
theorem book_395_pair_F3476 (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hq : 1 < q) {T : ℝ} (hT : 5 / 7 ≤ T) :
    |bookCount χ T + bookCount χ⁻¹ T - 2 * bookMain q T| ≤
      0.298 * Real.log ((q : ℝ) * T) + 4.358 := by
  have hT0 : 0 < T := by linarith
  have hq0 : (q : ℝ) ≠ 0 := by exact_mod_cast NeZero.ne q
  rw [pair_weight_sum χ hT0, two_bookMain]
  set F := (stripZeros_finite χ T).toFinset with hF
  set S := ∑ ρ ∈ F, (if |ρ.im| = T then (1 / 2 : ℝ) else 1) * (mult χ ρ : ℝ) with hS
  set N := ∑ ρ ∈ F, (mult χ ρ : ℝ) with hN
  set M := ∑ ρ ∈ F.filter (fun ρ => |ρ.im| < T), (mult χ ρ : ℝ) with hM
  have hSN : S ≤ N := by
    apply Finset.sum_le_sum
    intro ρ _
    have hm : (0 : ℝ) ≤ mult χ ρ := Nat.cast_nonneg _
    split_ifs <;> linarith
  have hMS : M ≤ S := by
    rw [hM, Finset.sum_filter]
    apply Finset.sum_le_sum
    intro ρ _
    have hm : (0 : ℝ) ≤ mult χ ρ := Nat.cast_nonneg _
    split_ifs with h1 h2
    · linarith
    · linarith
    · linarith
    · linarith
  have hup := (abs_le.mp (bmor_two_sided χ hχ hq hT)).2
  obtain ⟨ε, hε, hgap⟩ := left_gap χ T
  set g : ℝ → ℝ := fun t ↦ t / Real.pi * Real.log ((q : ℝ) * t / (2 * Real.pi * Real.exp 1)) -
    (0.298 * Real.log ((q : ℝ) * t) + 4.358) with hg
  have hev : ∀ᶠ t in 𝓝[<] T, g t ≤ M := by
    have hlt : max (T - ε) (5 / 7) < T := max_lt (by linarith) (by linarith)
    filter_upwards [Ioo_mem_nhdsLT hlt] with t ht
    have h57 : (5 / 7 : ℝ) ≤ t := (lt_of_le_of_lt (le_max_right _ _) ht.1).le
    have hTe : T - ε < t := lt_of_le_of_lt (le_max_left _ _) ht.1
    have he := hgap t hTe ht.2
    have hb := (abs_le.mp (bmor_two_sided χ hχ hq h57)).1
    rw [he] at hb
    simp only [hg]
    linarith
  have hcont : ContinuousAt g T :=
    (continuousAt_main2 hq0 hT0).sub
      ((continuousAt_const.mul (continuousAt_logqT hq0 hT0)).add continuousAt_const)
  have hlim : Tendsto g (𝓝[<] T) (𝓝 (g T)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hlow : g T ≤ M := le_of_tendsto hlim hev
  simp only [hg] at hlow
  rw [abs_le]
  constructor <;> linarith

/-- LEAF: Non-real character step.  For a primitive character whose inverse differs
from the character, the one-sided book count differs from the book main term by at most
`0.15 log (qT) + 3.389`.  This is the one-sided adaptation in footnote 5 of the book,
based on the argument of Trudgian, section 2.  The additional inverse condition excludes
the real character case and makes this leaf strictly easier than the target. -/
theorem book_395_nonreal_F3476 (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hc : χ⁻¹ ≠ χ) {T : ℝ} (hT : 1 ≤ T) :
    |bookCount χ T - bookMain q T| ≤ bookError q T := by
  sorry

/-- ASSEMBLY.  The statement of `book_395_nontrivial`, copied character for character.
The real case is obtained from the pair estimate.  The non-real case is the non-real
leaf.  The proof contains no gap of its own. -/
theorem book_395_nontrivial_F3476 (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive)
    (hne : χ ≠ 1) {T : ℝ} (hT : 1 ≤ T) :
    |bookCount χ T - bookMain q T| ≤ bookError q T := by
  by_cases hr : χ⁻¹ = χ
  · have hq : 1 < q := by
      have h0 := NeZero.pos q
      by_contra h
      obtain rfl : q = 1 := by omega
      exact hne (DirichletCharacter.level_one χ)
    have hpair := book_395_pair_F3476 χ hχ hq
      ((by norm_num : (5 / 7 : ℝ) ≤ 1).trans hT)
    rw [hr] at hpair
    have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq.le
    have hL : 0 ≤ Real.log ((q : ℝ) * T) := Real.log_nonneg (by nlinarith)
    unfold bookError
    rw [abs_le] at hpair ⊢
    constructor <;> linarith [hpair.1, hpair.2]
  · exact book_395_nonreal_F3476 χ hχ hr hT

example : type_of% @book_395_nontrivial_F3476 = type_of% @book_395_nontrivial := rfl

end LeanLab.HelfgottMajor.BookZeroSplit1122

#print axioms LeanLab.HelfgottMajor.BookZeroSplit1122.book_395_nontrivial_F3476
