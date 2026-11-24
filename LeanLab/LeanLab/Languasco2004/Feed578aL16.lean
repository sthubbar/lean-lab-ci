/-
Jia 1996 pages 252 and 253, Lemma 16 and its proof from Lemmas 14 and 15.
Source https://doi.org/10.4064/aa-77-3-207-287.
Split of Decomp578a.lemma16_progression_input into a mean square LEAF and a
proved Chebyshev counting step. The mean square estimate remains OPEN.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.Decomp578a

namespace LeanLab.Languasco2004.Feed578aL16
open Finset Real Decomp279a Decomp316a Source565 Decomp578a
noncomputable section
attribute [local instance] Classical.propDecidable

/-- LEAF: Jia page 253, the mean square form of the Lemma 16 remainder over the basic interval, HARD.
This is the estimate supplied by Lemmas 14 and 15 in the proof of Lemma 16 on page 253:
on region i, the square of the trilinear progression remainder summed over the even n of the
basic interval is at most a constant times the interval length times Y squared divided by an
arbitrary power B of log N. The constant may depend on epsilon, B and the block data. -/
theorem lemma16_mean_square :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∀ P Q R : ℝ → ℝ, ∀ a b c : ℝ → ℕ → ℝ,
      (∀ N : ℝ, 2 ≤ N →
        (localization N ε) ^ (16 / 135 : ℝ) ≤ R N ∧ R N ≤ Q N ∧
        (localization N ε) ^ (16 / 135 : ℝ) ≤ P N ∧
        P N ≤ (localization N ε) ^ (89 / 462 : ℝ) ∧
        (localization N ε) ^ (16 / 135 : ℝ) ≤ Q N ∧ Q N ≤ P N) →
      (∀ N : ℝ, ∀ m : ℕ, |a N m| ≤ 1 ∧ |b N m| ≤ 1 ∧ |c N m| ≤ 1) →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∑ n ∈ window N ε,
        |trilinearRemainder N (localization N ε) (P N) (Q N) (R N) n (a N) (b N) (c N)| ^ 2 ≤
      C * windowLength N ε * (localization N ε) ^ 2 / log N ^ B := by sorry

/-- Page 253 support: the Chebyshev counting inequality for a finite exceptional set. -/
theorem chebyshev_count (s : Finset ℕ) (f : ℕ → ℝ) (t : ℝ) (ht : 0 ≤ t) :
    ((s.filter (fun n => t < |f n|)).card : ℝ) * t ^ 2 ≤ ∑ n ∈ s, |f n| ^ 2 := by
  have h1 : ((s.filter (fun n => t < |f n|)).card : ℝ) * t ^ 2 ≤
      ∑ n ∈ s.filter (fun n => t < |f n|), |f n| ^ 2 := by
    have := Finset.card_nsmul_le_sum (s.filter (fun n => t < |f n|)) (fun n => |f n| ^ 2) (t ^ 2)
      (by
        intro n hn
        have hlt := (mem_filter.mp hn).2
        exact pow_le_pow_left₀ ht hlt.le 2)
    simpa [nsmul_eq_mul] using this
  have h2 : ∑ n ∈ s.filter (fun n => t < |f n|), |f n| ^ 2 ≤ ∑ n ∈ s, |f n| ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun n _ _ => sq_nonneg _)
  exact h1.trans h2

/-- Jia page 253: exact type of Decomp578a.lemma16_progression_input.
CONDITIONAL ON the mean square LEAF lemma16_mean_square. -/
theorem lemma16_progression_input_from_leaves :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε B : ℝ, 0 < ε → ε < ε₀ → 0 < B →
    ∀ P Q R : ℝ → ℝ, ∀ a b c : ℝ → ℕ → ℝ,
      (∀ N : ℝ, 2 ≤ N →
        (localization N ε) ^ (16 / 135 : ℝ) ≤ R N ∧ R N ≤ Q N ∧
        (localization N ε) ^ (16 / 135 : ℝ) ≤ P N ∧
        P N ≤ (localization N ε) ^ (89 / 462 : ℝ) ∧
        (localization N ε) ^ (16 / 135 : ℝ) ≤ Q N ∧ Q N ≤ P N) →
      (∀ N : ℝ, ∀ m : ℕ, |a N m| ≤ 1 ∧ |b N m| ≤ 1 ∧ |c N m| ≤ 1) →
    ∃ C D N₀ : ℝ, 0 < D ∧ ∀ N : ℝ, N₀ ≤ N →
      (((window N ε).filter (fun n =>
        D * localization N ε / log N ^ B <
          |trilinearRemainder N (localization N ε) (P N) (Q N) (R N) n (a N) (b N) (c N)|)).card : ℝ) ≤
      C * windowLength N ε / log N ^ B := by
  obtain ⟨e, he, hms⟩ := lemma16_mean_square
  refine ⟨e, he, ?_⟩
  intro ε B hε hεe hB P Q R a b c hPQR habc
  obtain ⟨C, N₀, hC⟩ := hms ε (3 * B) hε hεe (by linarith) P Q R a b c hPQR habc
  refine ⟨C, 1, max N₀ 3, one_pos, ?_⟩
  intro N hN
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hlog : 0 < log N := Real.log_pos (by linarith)
  have hY : 0 < localization N ε := Real.rpow_pos_of_pos hNpos _
  have hLB : 0 < log N ^ B := Real.rpow_pos_of_pos hlog _
  set t := 1 * localization N ε / log N ^ B with ht
  have htpos : 0 < t := by rw [ht]; positivity
  have hcheb := chebyshev_count (window N ε)
    (fun n => trilinearRemainder N (localization N ε) (P N) (Q N) (R N) n (a N) (b N) (c N))
    t htpos.le
  have hms' := hC N ((le_max_left _ _).trans hN)
  have h3 : log N ^ (3 * B) = (log N ^ B) ^ 3 := by
    rw [mul_comm, Real.rpow_mul hlog.le]
    exact Real.rpow_natCast _ 3
  rw [h3] at hms'
  have hkey : (((window N ε).filter (fun n => t <
      |trilinearRemainder N (localization N ε) (P N) (Q N) (R N) n (a N) (b N) (c N)|)).card : ℝ) * t ^ 2 ≤
      (C * windowLength N ε / log N ^ B) * t ^ 2 := by
    refine hcheb.trans (hms'.trans (le_of_eq ?_))
    rw [ht]
    field_simp
  exact le_of_mul_le_mul_right hkey (by positivity)

#print axioms lemma16_mean_square
#print axioms chebyshev_count
#print axioms lemma16_progression_input_from_leaves
end
end LeanLab.Languasco2004.Feed578aL16
