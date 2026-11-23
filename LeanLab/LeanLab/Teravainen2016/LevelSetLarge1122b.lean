/-
P0076, Proposition 4.2, pages 13 to 14, the large delta level set estimate.
Split of paper_level_set_large_delta from LevelSetSplit.lean along Green and Tao,
Restriction theory of the Selberg sieve, arXiv math/0405581, proof of Proposition 4.1,
pages 9 to 12 of the arXiv version: display 4.2, the bound
E_n |sum over B of f(b) e_N(bn)|^2 beta(n) at most |B|^(1+eps) for |f| at most 1,
split into a large set B, proved here by the crude bound plus Parseval exactly as on page 9,
and a small set B, the LEAF that uses the Fourier expansion 3.3, Poisson summation and
divisor moments, pages 10 to 12. The duality step, TT* in the form of Cauchy Schwarz in
L2 of beta, and the final arithmetic that turns display 4.2 into the level set count are
proved here. burst-20261122 S69. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.LevelSetSplit

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016.LevelSet1122b

open LeanLab.Teravainen2016

/-- LEAF: Green and Tao, Restriction theory of the Selberg sieve, arXiv math/0405581, proof of
Proposition 4.1, display 4.2 in the case of a small set B, pages 10 to 12: the smooth cutoff,
the expansion 3.3, Poisson summation, the separation of fractions with denominator at most R^2,
and the moment bound for the restricted divisor function. Class HARD. Here for the capped weight,
which is dominated by the uncapped sieve whose expansion EnvelopingFourierBounds supplies; the
threshold exponent c plays the role of the cut |B| at most R^(eps^2) on page 9. -/
theorem gt42_small_set (A D : ℝ → ℝ)
    (hAD : ∀ ε : ℝ, 0 < ε → 0 < A ε ∧ 0 < D ε) :
    ∀ ε : ℝ, 0 < ε → ∃ c : ℝ, 0 < c ∧ ∃ K : ℝ, 0 < K ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          EnvelopingFourierBounds w (WW J w) b M A D →
          ∀ B : Finset ℕ, B ⊆ range M → (B.card : ℝ) < (M : ℝ) ^ c →
          ∀ f : ℕ → ℂ, (∀ x, ‖f x‖ ≤ 1) →
            (M : ℝ)⁻¹ * ∑ n ∈ range M, restrictionBeta w (WW J w) b M n *
              ‖∑ x ∈ B, f x * eC (-((x : ℝ) * n / M))‖ ^ 2 ≤ K * (B.card : ℝ) ^ (1 + ε) := by
  sorry

/-- Dual Parseval on Z_M: for B inside 0 through M minus 1, the squared exponential sums over
all n below M add up to M times the squared coefficients. Green and Tao page 9. -/
theorem dual_parseval (M : ℕ) (hM : 1 ≤ M) (B : Finset ℕ) (hB : B ⊆ range M) (f : ℕ → ℂ) :
    ∑ n ∈ range M, ‖∑ x ∈ B, f x * eC (-((x : ℝ) * n / M))‖ ^ 2 =
      (M : ℝ) * ∑ x ∈ B, ‖f x‖ ^ 2 := by
  have hM0 : M ≠ 0 := by omega
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  set g : ℕ → ℂ := fun x => if x ∈ B then f x else 0 with hg
  have hP := parseval_complexFhat M hM0 g
  have hInter : range M ∩ B = B := inter_eq_right.mpr hB
  have hF : ∀ n, complexFhat M g n =
      (M : ℂ)⁻¹ * ∑ x ∈ B, f x * eC (-((x : ℝ) * n / M)) := by
    intro n
    unfold complexFhat
    congr 1
    have : ∀ x ∈ range M, g x * eC (-((n : ℝ) * x / M)) =
        if x ∈ B then f x * eC (-((x : ℝ) * n / M)) else 0 := by
      intro x _
      simp only [hg]
      split_ifs
      · congr 3; ring
      · simp
    rw [sum_congr rfl this, sum_ite_mem, hInter]
  have hG : ∑ x ∈ range M, ‖g x‖ ^ 2 = ∑ x ∈ B, ‖f x‖ ^ 2 := by
    have : ∀ x ∈ range M, ‖g x‖ ^ 2 = if x ∈ B then ‖f x‖ ^ 2 else 0 := by
      intro x _
      simp only [hg]
      split_ifs <;> simp
    rw [sum_congr rfl this, sum_ite_mem, hInter]
  simp only [hF, norm_mul, norm_inv, Complex.norm_natCast, mul_pow] at hP
  rw [← mul_sum, hG] at hP
  have hMinv : ((M : ℝ)⁻¹) ^ 2 ≠ 0 := by positivity
  field_simp at hP
  linarith

/-- Green and Tao, proof of Proposition 4.1, page 9: display 4.2 for a large set B, at least
M^c, from the crude subpower bound of the weight and Parseval. Proved. -/
theorem gt42_large_set (A D : ℝ → ℝ)
    (hAD : ∀ ε : ℝ, 0 < ε → 0 < A ε ∧ 0 < D ε) :
    ∀ ε : ℝ, 0 < ε → ∀ c : ℝ, 0 < c →
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          EnvelopingFourierBounds w (WW J w) b M A D →
          ∀ B : Finset ℕ, B ⊆ range M → (M : ℝ) ^ c ≤ (B.card : ℝ) →
          ∀ f : ℕ → ℂ, (∀ x, ‖f x‖ ≤ 1) →
            (M : ℝ)⁻¹ * ∑ n ∈ range M, restrictionBeta w (WW J w) b M n *
              ‖∑ x ∈ B, f x * eC (-((x : ℝ) * n / M))‖ ^ 2 ≤
                A (ε * c) * (B.card : ℝ) ^ (1 + ε) := by
  intro ε hε c hc J w _ _ b _ _ _ M hM hEB B hB hcard f hf
  have hεc : 0 < ε * c := mul_pos hε hc
  have hMr : (0 : ℝ) < M := by exact_mod_cast (by omega : 0 < M)
  have hA := (hAD (ε * c) hεc).1
  set G : ℕ → ℝ := fun n => ‖∑ x ∈ B, f x * eC (-((x : ℝ) * n / M))‖ ^ 2 with hGdef
  have hN1 : (1 : ℝ) ≤ B.card := (Real.one_le_rpow (by exact_mod_cast hM) hc.le).trans hcard
  have hNpos : (0 : ℝ) < B.card := by linarith
  have hpow : (M : ℝ) ^ (ε * c) ≤ (B.card : ℝ) ^ ε := by
    rw [mul_comm, Real.rpow_mul hMr.le]
    exact Real.rpow_le_rpow (Real.rpow_nonneg hMr.le _) hcard hε.le
  have hsum : ∑ n ∈ range M, restrictionBeta w (WW J w) b M n * G n ≤
      A (ε * c) * (M : ℝ) ^ (ε * c) * ∑ n ∈ range M, G n := by
    rw [mul_sum]
    apply sum_le_sum
    intro n hn
    apply mul_le_mul_of_nonneg_right (hEB.1 (ε * c) hεc n (mem_range.mp hn)) (by positivity)
  have hpars : ∑ n ∈ range M, G n = (M : ℝ) * ∑ x ∈ B, ‖f x‖ ^ 2 :=
    dual_parseval M hM B hB f
  have hfB : ∑ x ∈ B, ‖f x‖ ^ 2 ≤ (B.card : ℝ) := by
    calc ∑ x ∈ B, ‖f x‖ ^ 2 ≤ ∑ x ∈ B, (1 : ℝ) := by
          apply sum_le_sum
          intro x _
          have h0 := norm_nonneg (f x)
          have h1 := hf x
          nlinarith
      _ = B.card := by simp
  have hsplit : (B.card : ℝ) ^ (1 + ε) = (B.card : ℝ) * (B.card : ℝ) ^ ε := by
    rw [Real.rpow_add hNpos, Real.rpow_one]
  rw [hsplit]
  calc (M : ℝ)⁻¹ * ∑ n ∈ range M, restrictionBeta w (WW J w) b M n * G n
      ≤ (M : ℝ)⁻¹ * (A (ε * c) * (M : ℝ) ^ (ε * c) * ((M : ℝ) * ∑ x ∈ B, ‖f x‖ ^ 2)) := by
        rw [← hpars]
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = A (ε * c) * (M : ℝ) ^ (ε * c) * ∑ x ∈ B, ‖f x‖ ^ 2 := by
        field_simp
    _ ≤ A (ε * c) * (B.card : ℝ) ^ ε * (B.card : ℝ) := by
        apply mul_le_mul (mul_le_mul_of_nonneg_left hpow hA.le) hfB
          (sum_nonneg (fun _ _ => by positivity))
        exact mul_nonneg hA.le (Real.rpow_nonneg hNpos.le _)
    _ = A (ε * c) * ((B.card : ℝ) * (B.card : ℝ) ^ ε) := by ring

/-- Green and Tao, display 4.2 for every set B, assembled from the large set case and the
small set LEAF. CONDITIONAL ON gt42_small_set. -/
theorem gt42_all (A D : ℝ → ℝ)
    (hAD : ∀ ε : ℝ, 0 < ε → 0 < A ε ∧ 0 < D ε) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          EnvelopingFourierBounds w (WW J w) b M A D →
          ∀ B : Finset ℕ, B ⊆ range M →
          ∀ f : ℕ → ℂ, (∀ x, ‖f x‖ ≤ 1) →
            (M : ℝ)⁻¹ * ∑ n ∈ range M, restrictionBeta w (WW J w) b M n *
              ‖∑ x ∈ B, f x * eC (-((x : ℝ) * n / M))‖ ^ 2 ≤ K * (B.card : ℝ) ^ (1 + ε) := by
  intro ε hε
  obtain ⟨c, hc, K1, hK1, H⟩ := gt42_small_set A D hAD ε hε
  have hA := (hAD (ε * c) (mul_pos hε hc)).1
  refine ⟨K1 + A (ε * c), by linarith, ?_⟩
  intro J w hJ hw b hb hbW ham M hM hEB B hB f hf
  have hp : 0 ≤ (B.card : ℝ) ^ (1 + ε) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  rcases lt_or_ge (B.card : ℝ) ((M : ℝ) ^ c) with hs | hl
  · refine (H J w hJ hw b hb hbW ham M hM hEB B hB hs f hf).trans ?_
    nlinarith
  · refine (gt42_large_set A D hAD ε hε c hc J w hJ hw b hb hbW ham M hM hEB B hB hl f hf).trans ?_
    nlinarith

end LeanLab.Teravainen2016.LevelSet1122b
