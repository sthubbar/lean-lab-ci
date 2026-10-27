import LeanLab.LanguascoPintzZaccagnini2007.Truncation131

namespace LeanLab.LPZ2007

open Finset Real Filter MeasureTheory

noncomputable section

/-- LEAF. Display 3 on page 3. The tuples removed by replacing L with L-sqrt L
have weighted count o(N L^k), uniformly on J(X).
Source: the standard sieve upper bound R(n) << n S(n) invoked after display 3.
The exact Fourier inversion and the arc split are proved in Convolution131. -/
theorem truncation_tail131 (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ N ∈ evenJ131 X,
      |Rpp k X N - truncatedCount131 k X N| ≤ ε * N * Lg X ^ k := by
  exact truncation_tail_proved131 k hk ε hε

/-- LEAF. Displays 3 to 6 on pages 3 and 4. Truncating the powers of two
and Fourier inversion leave an error o(N L^k), uniformly on J(X).
The bound for the prime pair sum used after display 3 is an outside sieve input.
Source: the standard upper bound R(n) << n S(n) invoked on page 3. -/
theorem truncation131 (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ P : ℝ, AdmissibleP131 X P →
      ∀ N ∈ evenJ131 X,
        |Rpp k X N - majorContribution131 k X N P - minorContribution131 k X N P| ≤
          ε * N * Lg X ^ k := by
  obtain ⟨X₁, hX₁⟩ := truncation_tail131 k hk ε hε
  obtain ⟨X₂, hX₂⟩ := admissible_gap_eventually131
  refine ⟨max X₁ X₂, fun X hX P hP N hN => ?_⟩
  obtain ⟨hX2, hpar⟩ := hX₂ X (by omega)
  obtain ⟨hP1, _, hQ⟩ := hpar P hP
  have he := arc_split131 k X N P (by omega) (by linarith) hQ
  rw [show Rpp k X N - majorContribution131 k X N P - minorContribution131 k X N P =
      Rpp k X N - (majorContribution131 k X N P + minorContribution131 k X N P) by ring,
    he]
  exact hX₁ X (by omega) N hN

/-- LEAF. Page 4 before display 7. The Bessel and prime number theorem argument
with Lemma 6.3 gives the minor arc mean square bound.
Source outside P0045: Vaughan Theorem 3.1 cited as Lemma 6.3 on page 10,
and the prime number theorem invoked on page 4. -/
theorem minor_mean_square131 (k : ℕ) (hk : 1 ≤ k) :
    ∃ K : ℝ, 0 ≤ K ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∀ P : ℝ, AdmissibleP131 X P →
        ∑ N ∈ evenJ131 X, minorContribution131 k X N P ^ 2 ≤
          K * (X : ℝ) ^ ((13 : ℝ) / 5) * Lg X ^ (2 * k + 9) := by
  exact minor_mean_square_proved131 k

/-- LEAF. Display 25 on page 8, with the factor 2c0 restored from display 2.
The major arc averaging proof gives a uniform additive error o(N L^k).
Source outside P0045: Pintz Theorem 10 cited as Lemma 4.1, and the Iwaniec
zero free region and primitive real character facts in Corollary 4.2 on page 6.
The arithmetic Lemmas 6.1 and 6.2 are already proved in this folder. -/
theorem major_asymptotic131 (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∃ P : ℝ, AdmissibleP131 X P ∧
      ∀ N ∈ evenJ131 X,
        |majorContribution131 k X N P - coefficient131 k N * N * Lg X ^ k| ≤
          ε * N * Lg X ^ k := by
  sorry

/-- LEAF. Page 9 conclusion: three error contributions combine by the triangle inequality.
This elementary statement is independent of the cited analytic inputs. -/
theorem combine_errors131 {R A B C t : ℝ}
    (h₁ : |R - A - B| ≤ t / 3) (h₂ : |A - C| ≤ t / 3) (h₃ : |B| ≤ t / 3) :
    |R - C| ≤ t := by
  have h := abs_add_three (R - A - B) (A - C) B
  have he : R - A - B + (A - C) + B = R - C := by ring
  rw [he] at h
  linarith

/-- LEAF. Display 7 on page 4. The already proved mean square counting lemma
bounds the exceptional set with an explicit factor 9/4. -/
theorem minor_count131 {k X : ℕ} {P K : ℝ} (hX : 0 < X) (hL : 0 < Lg X)
    (hsum : ∑ N ∈ evenJ131 X, minorContribution131 k X N P ^ 2 ≤
      K * (X : ℝ) ^ ((13 : ℝ) / 5) * Lg X ^ (2 * k + 9)) :
    (((evenJ131 X).filter (fun N : ℕ =>
      (N : ℝ) * Lg X ^ ((k : ℝ) - 1 / 2) ≤ |minorContribution131 k X N P|)).card : ℝ) ≤
        9 / 4 * K / Real.log 2 ^ 10 * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10 := by
  classical
  have hc := count_le_of_sq_sum (S := (evenJ131 X).filter (fun N : ℕ =>
      (N : ℝ) * Lg X ^ ((k : ℝ) - 1 / 2) ≤ |minorContribution131 k X N P|))
    (a := fun N => minorContribution131 k X N P) (K := K) (k := k) (X := (X : ℝ))
    (by exact_mod_cast hX) hL
  have he : 9 / 4 * K * (X : ℝ) ^ ((3 : ℝ) / 5) * Lg X ^ 10 =
      9 / 4 * K / Real.log 2 ^ 10 * (X : ℝ) ^ ((3 : ℝ) / 5) * Real.log X ^ 10 := by
    simp only [Lg, Real.logb, div_pow]
    ring
  rw [← he]
  apply hc
  · intro N hN
    exact (mem_filter.mp (mem_filter.mp hN).1).2.2
  · intro N hN
    exact (mem_filter.mp hN).2
  · refine le_trans ?_ hsum
    exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)

/-- LEAF. Page 9: the minor arc cutoff N L^(k-1/2) is eventually at most
any fixed positive multiple of N L^k. -/
theorem cutoff_small131 (k : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      Lg X ^ ((k : ℝ) - 1 / 2) ≤ ε * Lg X ^ k := by
  have ht : Tendsto (fun X : ℕ => Lg X) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  obtain ⟨X₀, hX₀⟩ := (ht.eventually_ge_atTop (max 1 ((1 / ε) ^ 2))).exists_forall_of_atTop
  refine ⟨X₀, fun X hX => ?_⟩
  have hL := hX₀ X hX
  have hL1 : 1 ≤ Lg X := (le_max_left _ _).trans hL
  have hL0 : 0 < Lg X := by linarith
  have hs : 1 / ε ≤ Real.sqrt (Lg X) := by
    calc 1 / ε = Real.sqrt ((1 / ε) ^ 2) := (Real.sqrt_sq (by positivity)).symm
      _ ≤ Real.sqrt (Lg X) := Real.sqrt_le_sqrt ((le_max_right _ _).trans hL)
  rw [Real.rpow_sub hL0, Real.rpow_natCast, ← Real.sqrt_eq_rpow]
  apply (div_le_iff₀ (Real.sqrt_pos.2 hL0)).2
  have he : 1 ≤ ε * Real.sqrt (Lg X) := by
    have := (div_le_iff₀ hε).1 hs
    linarith
  nlinarith [mul_le_mul_of_nonneg_left he (pow_nonneg hL0.le k)]

/-- Assembly of the repaired cited conclusion from the six leaves.
CONDITIONAL on major_asymptotic131 only.
The discarded tuple bound, minor mean square and Fourier assembly are proved.
There is no sorry in this assembly. -/
theorem repaired_mainJ131 : RepairedMainJ131 := by
  classical
  intro k hk
  obtain ⟨K, hK, X₁, hX₁⟩ := minor_mean_square131 k hk
  refine ⟨9 / 4 * K / Real.log 2 ^ 10, by positivity, fun η hη => ?_⟩
  have hη3 : 0 < η / 3 := by positivity
  obtain ⟨X₂, hX₂⟩ := truncation131 k hk (η / 3) hη3
  obtain ⟨X₃, hX₃⟩ := major_asymptotic131 k hk (η / 3) hη3
  obtain ⟨X₄, hX₄⟩ := cutoff_small131 k (η / 3) hη3
  refine ⟨max 2 (max X₁ (max X₂ (max X₃ X₄))), fun X hX => ?_⟩
  have h2 : 2 ≤ X := le_trans (le_max_left _ _) hX
  have hx1 : X₁ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hx2 : X₂ ≤ X := by omega
  have hx3 : X₃ ≤ X := by omega
  have hx4 : X₄ ≤ X := by omega
  have hL : 0 < Lg X := Real.logb_pos (by norm_num) (by exact_mod_cast h2)
  obtain ⟨P, hP, hmajor⟩ := hX₃ X hx3
  have hcount := minor_count131 (by omega : 0 < X) hL (hX₁ X hx1 P hP)
  refine le_trans ?_ (by simpa [mul_assoc] using hcount)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro N hN
  obtain ⟨hN, hbad⟩ := mem_filter.mp hN
  refine mem_filter.mpr ⟨hN, ?_⟩
  by_contra hminor
  have hminor' : |minorContribution131 k X N P| ≤
      η * N * Lg X ^ k / 3 := by
    have hcut := mul_le_mul_of_nonneg_left (hX₄ X hx4) (Nat.cast_nonneg N : (0 : ℝ) ≤ N)
    have hm : |minorContribution131 k X N P| < (N : ℝ) * Lg X ^ ((k : ℝ) - 1 / 2) := by
      simpa only [one_div] using (not_le.mp hminor)
    have := hm.le.trans hcut
    nlinarith
  have htrunc : |Rpp k X N - majorContribution131 k X N P - minorContribution131 k X N P| ≤
      η * N * Lg X ^ k / 3 := by
    have := hX₂ X hx2 P hP N hN
    nlinarith
  have hmajor' : |majorContribution131 k X N P - coefficient131 k N * N * Lg X ^ k| ≤
      η * N * Lg X ^ k / 3 := by
    have := hmajor N hN
    nlinarith
  exact (not_lt_of_ge (combine_errors131 htrunc hmajor' hminor')) hbad

end

end LeanLab.LPZ2007
