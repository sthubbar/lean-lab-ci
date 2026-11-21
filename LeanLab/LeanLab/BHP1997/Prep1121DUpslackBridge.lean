/-
P0069 Baker Harman Pintz 1997, pages 43, 49 and 53. Deepening pass on the four piece leaves of
Prep1121UpslackLemma29. The page 53 sentence "We use Lemma 34 to obtain (5.1) and (5.2) for
g_m, h_m and j_m" is cut here into the general Lemma 34 of page 49, two LEAFs, one for 5.1 and
one for 5.2, and a PROVED bridge: Lemma 29 on page 43, the existing open leaf
`DQLeaf518Split.leaf_lemma29` of main, turns 5.1 and 5.2 into the window mean square, and on the
characters of F the `delta chi` term vanishes, so the bound over `E_q^c` minus the principal
character follows by dropping the principal term.
New file, no new definition, no existing statement changed.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prep1121UpslackLemma29
import LeanLab.BHP1997.DQLeaf518Split

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open MeasureTheory

/-- P0069 page 43, Lemma 29 read for the characters of F: from 5.1 over `E^c` minus the
principal character with the size of E, 5.2, and the coefficient bound 3.1, the window mean
square over `E^c` minus the principal character, where `delta chi = 0`. PROVED from the
existing leaf `DQLeaf518Split.leaf_lemma29` of main. -/
theorem upD_np_of_lemma29 (b : ℝ → ℕ → ℝ) {ε B : ℝ} (hε : 0 < ε)
    (hb : ∃ C : ℝ, ∀ x k, |b x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    (h51 : ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
          ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
            ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
                (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
              ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
          C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
            Real.log x ^ (-A'))
    (h52 : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A)) :
    ∃ E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q),
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).erase 1,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((b x m : ℝ) : ℂ) * χ (m : ZMod q)‖ ^ 2 ≤
              C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  obtain ⟨E, hE⟩ := h51
  have h51' : ∀ A : ℝ, 0 < A → ∀ A' : ℝ, 0 < A' → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → q ≤ sieveQ ε x →
      ∑ χ ∈ ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q).filter (· ≠ 1),
        ∫ t in (-x ^ (11 / 20 + ε))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) * χ (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A') := by
    intro A hA A' hA'
    obtain ⟨C, hC⟩ := hE A hA A' hA'
    exact ⟨C, fun x hx q hq hqQ => (hC x hx q hq hqQ).2⟩
  have L := DQLeaf518Split.leaf_lemma29 b hε hb E h51' h52
  refine ⟨E, fun A hA => ?_⟩
  obtain ⟨C1, h1⟩ := L A hA
  obtain ⟨C2, h2⟩ := hE A hA A hA
  refine ⟨max (max C1 C2) 1, fun x hx q hq hqQ => ?_⟩
  have hx1 : C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : C2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx0 : 1 ≤ x := le_trans (le_max_right _ _) hx
  have hL : 0 ≤ Real.log x := Real.log_nonneg hx0
  have hM1 : C1 ≤ max (max C1 C2) 1 := le_trans (le_max_left _ _) (le_max_left _ _)
  have hM2 : C2 ≤ max (max C1 C2) 1 := le_trans (le_max_right _ _) (le_max_left _ _)
  have hY : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg (by linarith) _
  refine ⟨?_, fun z hz1 hz2 => ?_⟩
  · have hP : 0 ≤ (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) :=
      mul_nonneg (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Real.rpow_nonneg hL _)
    refine le_trans (h2 x hx2 q hq hqQ).1 ?_
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hM2 hP
  have k0 := h1 x hx1 q hq hqQ z hz1 hz2
  have hR : 0 ≤ ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_nonneg (mul_nonneg (sq_nonneg _) hY) (Real.rpow_nonneg hL _)
  have k := le_trans k0 (by
    have := mul_le_mul_of_nonneg_right hM1 hR
    calc C1 * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)
        = C1 * (((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by ring
      _ ≤ max (max C1 C2) 1 * (((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) *
          Real.log x ^ (-A)) := this
      _ = max (max C1 C2) 1 * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) *
          Real.log x ^ (-A) := by ring)
  have hab : x ^ (11 / 20 + ε) / 2 ≤ 3 * x ^ (11 / 20 + ε) := by linarith
  refine le_trans ?_ k
  refine le_trans (le_of_eq ?_)
    (Finset.sum_le_sum_of_subset_of_nonneg (Finset.erase_subset 1 _) ?_)
  · refine Finset.sum_congr rfl fun χ hχ => ?_
    have hχ1 : χ ≠ 1 := (Finset.mem_erase.mp hχ).1
    have hd : Thm2.delta χ = 0 := by simp [Thm2.delta, hχ1]
    simp only [hd, zero_mul, sub_zero]
  · intro χ _ _
    exact intervalIntegral.integral_nonneg hab fun y _ => sq_nonneg _

end LeanLab.BHP1997.DecompC165d
