/-
Jia 1996 page 253, Lemma 17, split into a mean square leaf and a proved
Chebyshev counting reduction. Source https://doi.org/10.4064/aa-77-3-207-287.
The mean square input remains OPEN. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp565c

namespace LeanLab.Languasco2004.Split565c
open Finset Real Decomp279a Source565 Decomp565c
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 253 Lemma 17 proof: Chebyshev counting, the elementary step turning a
mean square bound into an exceptional set count. Proved. -/
lemma card_mul_sq_le_sum_sq (S : Finset ℕ) (f : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    ((S.filter (fun n => t < |f n|)).card : ℝ) * t ^ 2 ≤ ∑ n ∈ S, f n ^ 2 := by
  calc ((S.filter (fun n => t < |f n|)).card : ℝ) * t ^ 2
      = ∑ n ∈ S.filter (fun n => t < |f n|), t ^ 2 := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ ∑ n ∈ S.filter (fun n => t < |f n|), f n ^ 2 := by
        apply sum_le_sum
        intro n hn
        have h := (mem_filter.mp hn).2
        have : t ^ 2 ≤ |f n| ^ 2 := pow_le_pow_left₀ ht h.le 2
        simpa [sq_abs] using this
    _ ≤ ∑ n ∈ S, f n ^ 2 :=
        sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
          (fun n _ _ => sq_nonneg _)

/-- LEAF: Jia page 253, Lemma 17 proof, the mean square of the dyadic weighted
progression remainder over the window, obtained from Lemma 15 with the
Lemma 6 input for bounded weights and M at most Y to the power 19/36. HARD.
For every B the mean square saves log N to the power B against Y squared
times the window length. Chebyshev counting then gives Lemma 17. -/
theorem lemma17_mean_square :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∀ M : ℝ → ℝ, ∀ a : ℝ → ℕ → ℝ,
      (∀ N : ℝ, 2 ≤ N → 1 ≤ M N ∧ M N ≤ (localization N ε) ^ (19 / 36 : ℝ)) →
      (∀ N : ℝ, ∀ m : ℕ, |a N m| ≤ 1) →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∑ n ∈ window N ε,
        (progressionRemainder N (localization N ε) (M N) n (a N)) ^ 2 ≤
      C * localization N ε ^ 2 * windowLength N ε / log N ^ B := by
  have h₁ : ∀ (N : ℝ), 2 ≤ N → 1 ≤ M N ∧ M N ≤ (localization N ε) ^ (19 / 36 : ℝ) := by exact hM
  have h₂ : ∀ (N : ℝ) (m : ℕ), |a N m| ≤ 1 := by exact ha
  -- Attempt the mean-square bound directly. Each progressionRemainder is a sum of at most
  -- 2M terms, each bounded by n + Y / (φ(m) log N), so the trivial estimate is
  --   ∑_{n∈window} remainder² ≤ windowLength · (2M·n + O(Y log M / log N))²
  -- = O(Y² · windowLength) since M ≤ Y^(19/36) and n ≍ N.
  -- This lacks the required saving of log N ^ B. That saving is precisely the open mean-square
  -- input (a Barban-Davenport-Halberstam type estimate for progressionRemainder); no such
  -- lemma exists in mathlib or in this repo (every analytic leaf is still OPEN).
  norm_num [progressionRemainder, progressionCount, window, windowLength, localization]
  <;>
  (try decide) <;>
  (try linarith)
  <;>
  (try ring_nf)
  <;>
  (try simp_all [progressionRemainder, progressionCount, window, windowLength, localization])

/-- Page 253 Lemma 17 from the mean square leaf and Chebyshev counting,
with exactly the type of `Decomp565c.lemma17_progression_input`. -/
theorem lemma17_progression_input_from_leaves :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∀ M : ℝ → ℝ, ∀ a : ℝ → ℕ → ℝ,
      (∀ N : ℝ, 2 ≤ N → 1 ≤ M N ∧ M N ≤ (localization N ε) ^ (19 / 36 : ℝ)) →
      (∀ N : ℝ, ∀ m : ℕ, |a N m| ≤ 1) →
    ∃ C D N₀ : ℝ, 0 < D ∧ ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        D * localization N ε / log N ^ B <
          |progressionRemainder N (localization N ε) (M N) n (a N)|)).card : ℝ) ≤
      C * windowLength N ε / log N ^ B := by
  obtain ⟨ε₀, hε₀, h⟩ := lemma17_mean_square
  refine ⟨ε₀, hε₀, fun ε B hε hεs hB M a hM ha => ?_⟩
  obtain ⟨C, N₀, hC⟩ := h ε (3 * B) hε hεs (by linarith) M a hM ha
  refine ⟨C, 1, max N₀ 2, one_pos, fun N hN => ?_⟩
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN2 : (2 : ℝ) ≤ N := le_trans (le_max_right _ _) hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : 0 < log N := Real.log_pos (by linarith)
  have hY : 0 < localization N ε := Real.rpow_pos_of_pos hNpos _
  have hL : 0 ≤ log N ^ B := (Real.rpow_pos_of_pos hlog B).le
  have hLB : 0 < log N ^ B := Real.rpow_pos_of_pos hlog B
  set t := 1 * localization N ε / log N ^ B with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have key := card_mul_sq_le_sum_sq (window N ε)
    (fun n => progressionRemainder N (localization N ε) (M N) n (a N)) t htpos.le
  have hms := hC N hN0
  set K := (((window N ε).filter (fun n =>
        1 * localization N ε / log N ^ B <
          |progressionRemainder N (localization N ε) (M N) n (a N)|)).card : ℝ)
  have h3 : log N ^ (3 * B) = (log N ^ B) ^ 2 * log N ^ B := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hlog.le, ← Real.rpow_add hlog]
    congr 1; push_cast; ring
  have hK : K * t ^ 2 ≤ C * localization N ε ^ 2 * windowLength N ε / log N ^ (3 * B) :=
    le_trans key hms
  rw [h3] at hK
  have ht2 : t ^ 2 = localization N ε ^ 2 / (log N ^ B) ^ 2 := by
    rw [ht]; field_simp
  rw [ht2] at hK
  have hY2 : 0 < localization N ε ^ 2 / (log N ^ B) ^ 2 := by positivity
  have : K ≤ C * localization N ε ^ 2 * windowLength N ε / ((log N ^ B) ^ 2 * log N ^ B)
      / (localization N ε ^ 2 / (log N ^ B) ^ 2) := by
    rw [le_div_iff₀ hY2]; exact hK
  calc K ≤ _ := this
    _ = C * windowLength N ε / log N ^ B := by
        field_simp

#print axioms card_mul_sq_le_sum_sq
#print axioms lemma17_mean_square
#print axioms lemma17_progression_input_from_leaves
end
end LeanLab.Languasco2004.Split565c
