import LeanLab.LanguascoPintzZaccagnini2007.DecompJ218

/-!
Split of `cor42_window_extension131` of `DecompJ218`. The target extends Corollary 4.2 of the
source from `evenJ131 X` = J(X) = [2X/3, X] to `evenWindow131 X` = [X/2, X], at the same scale X,
with one major arc parameter `P` and one exceptional set `E` serving the whole window.

Nothing on J(X) itself is new: `evenJ131 X ⊆ evenWindow131 X`, so on J(X) the first conjunct of the
conclusion is the hypothesis applied at the same X, and the second conjunct follows from the first
by the triangle inequality and `Sing_nonneg131`.

What is new is the strip `X/2 ≤ n < 2X/3`. `binaryMajor131 X n P` depends on X through
`primeSum131 X` and through the arcs `majorArcs131 X P`, so the strip is a statement at the fixed
scale X for n below 2X/3, and it has to hold for the parameter and the exceptional set that the
J(X) estimate already uses: one parameter and one set serve both parts of the window. That is why
`leaf_strip_extension131` takes the J(X) estimate as a hypothesis at the same X, same `P`, same
`E`, and same `Cstar`, instead of choosing its own.

The second conjunct has no `Nonexceptional131` guard, so it must also cover the n that the
exceptional set really does cover. Those n are the content of `leaf_exceptional_absolute131`; for
the remaining n the second conjunct follows from the first with a constant 2.

`cor42_window_extension131_split` below is proved from the two leaves with no `sorry`, and does not
use `cor42_window_extension131`.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real Filter MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- LEAF. The strip step `X/2 ≤ n < 2X/3` at a fixed scale X: when the relative estimate for the
binary major arc integral already holds on J(X) with the major arc parameter `P`, the exceptional
set `E` and the constant `Cstar`, then it holds with the same tolerance for the even n of
[X/2, 2X/3) as well, for the same `P`, `E`, `Cstar`. This is the estimate the J(X) form does not
give, since the integral and the arcs are those of the scale X. -/
theorem leaf_strip_extension131 (η : ℝ) (hη : 0 < η) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∀ (P : ℝ) (E : Finset ℕ) (Cstar : ℕ),
        AdmissibleP131 X P →
        (∀ n ∈ evenJ131 X, Nonexceptional131 Cstar E n →
          |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) →
        ∀ n ∈ evenWindow131 X, 2 * (X : ℝ) / 3 > n → Nonexceptional131 Cstar E n →
          |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n := by
  sorry

/-- LEAF. The crude bound on the n the exceptional set covers: if some modulus of the exceptional
set divides `Cstar * n`, then the binary major arc integral is at most a constant times n times the
singular series, with the constant independent of the scale, of the major arc parameter, of the
exceptional set and of its two parameters. Only these n need it: for the other n of the window the
bound follows from the relative estimate. -/
theorem leaf_exceptional_absolute131 :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (X : ℕ) (Cstar K₁ : ℕ) (c P : ℝ) (E : Finset ℕ),
      0 < c → AdmissibleP131 X P → ExceptionalModuli131 K₁ c X E →
      ∀ n ∈ evenWindow131 X, ¬ Nonexceptional131 Cstar E n →
        |binaryMajor131 X n P| ≤ A * n * Sing n := by
  sorry

/-- The split target: the same statement as `cor42_window_extension131`, proved from the two
leaves above and not from the target. -/
theorem cor42_window_extension131_split :
    Cor42OnWindow131 evenJ131 → Cor42OnWindow131 evenWindow131 := by
  intro h η hη
  have hmin : 0 < min η 1 := lt_min hη one_pos
  have hle : min η 1 ≤ η := min_le_left _ _
  have hle1 : min η 1 ≤ 1 := min_le_right _ _
  obtain ⟨X₁, hX₁⟩ := leaf_strip_extension131 (min η 1) hmin
  obtain ⟨Aabs, hAabs0, hAabs⟩ := leaf_exceptional_absolute131
  unfold Cor42OnWindow131 at h
  obtain ⟨K₁, Cstar, c, A₀, hCstar, hc, -, X₀, hX₀⟩ := h (min η 1) hmin
  refine ⟨K₁, Cstar, c, max 2 Aabs, hCstar, hc, le_trans zero_le_two (le_max_left _ _),
    max X₀ X₁, ?_⟩
  intro X hX
  obtain ⟨P, E, hAdm, hExc, hrel, -⟩ := hX₀ X (le_trans (le_max_left _ _) hX)
  have hwin : ∀ n ∈ evenWindow131 X, Nonexceptional131 Cstar E n →
      |binaryMajor131 X n P - n * Sing n| ≤ min η 1 * n * Sing n := by
    intro n hn hnone
    by_cases hge : 2 * (X : ℝ) / 3 ≤ n
    · exact hrel n (mem_filter.mpr ⟨(mem_filter.mp hn).1, (mem_filter.mp hn).2.1, hge⟩) hnone
    · exact hX₁ X (le_trans (le_max_right _ _) hX) P E Cstar hAdm
        (fun m hm hm' => hrel m hm hm') n hn (not_le.mp hge) hnone
  refine ⟨P, E, hAdm, hExc, ?_, ?_⟩
  · intro n hn hnone
    have hb : (0 : ℝ) ≤ n * Sing n := mul_nonneg (Nat.cast_nonneg n) (Sing_nonneg131 n)
    have h1 := hwin n hn hnone
    have h2 : min η 1 * n * Sing n ≤ η * n * Sing n :=
      mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hle (Nat.cast_nonneg n)) (Sing_nonneg131 n)
    linarith
  · intro n hn
    have hb : (0 : ℝ) ≤ n * Sing n := mul_nonneg (Nat.cast_nonneg n) (Sing_nonneg131 n)
    by_cases hnone : Nonexceptional131 Cstar E n
    · have h1 := hwin n hn hnone
      have h2 : |binaryMajor131 X n P| ≤
          |binaryMajor131 X n P - n * Sing n| + n * Sing n := by
        have hrw : binaryMajor131 X n P =
            (binaryMajor131 X n P - n * Sing n) + n * Sing n := by ring
        calc |binaryMajor131 X n P|
            = |(binaryMajor131 X n P - n * Sing n) + n * Sing n| := congrArg abs hrw
          _ ≤ |binaryMajor131 X n P - n * Sing n| + |n * Sing n| := abs_add_le _ _
          _ = |binaryMajor131 X n P - n * Sing n| + n * Sing n := by
              rw [abs_of_nonneg hb]
      have h3 : min η 1 * n * Sing n ≤ n * Sing n :=
        mul_le_mul_of_nonneg_right
          (by simpa using mul_le_mul_of_nonneg_right hle1 (Nat.cast_nonneg n))
          (Sing_nonneg131 n)
      have h4 : (2 : ℝ) * n * Sing n ≤ max 2 Aabs * n * Sing n :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_left (2 : ℝ) Aabs) (Nat.cast_nonneg n))
          (Sing_nonneg131 n)
      linarith
    · have h5 := hAabs X Cstar K₁ c P E hc hAdm hExc n hn hnone
      have h6 : Aabs * n * Sing n ≤ max 2 Aabs * n * Sing n :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_right (le_max_right (2 : ℝ) Aabs) (Nat.cast_nonneg n))
          (Sing_nonneg131 n)
      linarith

#print axioms LeanLab.LPZ2007.cor42_window_extension131_split

end

end LeanLab.LPZ2007
