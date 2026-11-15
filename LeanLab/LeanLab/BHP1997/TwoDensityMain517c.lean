/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character, the
E2 sum of display 5.15, page 50: the prime number theorem with partial summation for one outer
prime.

The outer primes of display 5.15 carry the weight `1 / p` times a function of bounded
variation. This file proves the form of the prime number theorem that such a weight needs:
partial summation with the prefix error growing like the endpoint, so that the weight `1 / n`
cancels it and only one factor `log X` is lost.

No new definition, nothing left open in this file. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.PrimeWeighted517

namespace LeanLab.BHP1997.LowerShortC165
open Decomp132
open scoped BigOperators

/-- P0069 page 51 display 5.17, partial summation on an integer interval `(L, U]`, real
form: the weighted sum is the endpoint weight times the full sum minus the increments of the
weight against the prefix sums. -/
theorem two_pair_abel (a F : ℕ → ℝ) (L : ℕ) {U : ℕ} (hLU : L ≤ U) :
    ∑ n ∈ Finset.Ioc L U, a n * F n =
      F U * ∑ n ∈ Finset.Ioc L U, a n -
        ∑ i ∈ Finset.Ico L U, (F (i + 1) - F i) * ∑ n ∈ Finset.Ioc L i, a n := by
  induction U, hLU using Nat.le_induction with
  | base => simp
  | succ U hLU ih =>
    rw [Finset.sum_Ioc_succ_top hLU, Finset.sum_Ioc_succ_top hLU,
      Finset.sum_Ico_succ_top hLU, ih]
    ring

/-- P0069 page 51, display 5.17, the prime number theorem with partial summation for one outer
prime of display 5.15. For every positive `A` and `c` there is `C` such that for `X ≥ C` and
an integer interval `(L, U]` with `X ^ c ≤ L` and `U ≤ X`, a function `G` bounded by `M` with
total variation at most `V` on the interval satisfies: the sum of `G n / n` over the primes
of the interval differs from the sum over all integers with density `1 / log n` by at most
`C (M (1 + log X) + V) / log^A X`. -/
theorem two_pair_pnt_harmonic (A : ℝ) (hA : 0 < A) (c : ℝ) (hc : 0 < c) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ X : ℝ, C ≤ X → ∀ L U : ℕ, L ≤ U → X ^ c ≤ (L : ℝ) → (U : ℝ) ≤ X →
      ∀ (G : ℕ → ℝ) (M V : ℝ), 0 ≤ M → (∀ n ∈ Finset.Ioc L U, |G n| ≤ M) →
        ∑ i ∈ Finset.Ico (L + 1) U, |G (i + 1) - G i| ≤ V →
        |∑ n ∈ Finset.Ioc L U, (primeWeight n - 1 / Real.log (n : ℝ)) * (G n / (n : ℝ))| ≤
          C * (M * (1 + Real.log X) + V) * Real.log X ^ (-A) := by
  obtain ⟨C0, hC01, h0⟩ := pnt_interval_nat A hA
  have hC00 : 0 ≤ C0 := by linarith
  have hcA : 0 < c ^ (-A) := Real.rpow_pos_of_pos hc _
  have hCnn : (0 : ℝ) ≤ max (max (C0 ^ (1 / c)) (2 * (C0 * c ^ (-A)))) 2 :=
    le_trans (by norm_num) (le_max_right _ _)
  refine ⟨max (max (C0 ^ (1 / c)) (2 * (C0 * c ^ (-A)))) 2, hCnn, ?_⟩
  intro X hX L U hLU hXL hUX G M V hM0 hG hV
  have hCa : C0 ^ (1 / c) ≤ X := (le_max_left _ _).trans ((le_max_left _ _).trans hX)
  have hCb : 2 * (C0 * c ^ (-A)) ≤ max (max (C0 ^ (1 / c)) (2 * (C0 * c ^ (-A)))) 2 :=
    (le_max_right _ _).trans (le_max_left _ _)
  have hX2 : 2 ≤ X := (le_max_right _ _).trans hX
  have hX0 : 0 < X := by linarith
  have hlogX : 0 < Real.log X := Real.log_pos (by linarith)
  have hlX : 0 ≤ Real.log X ^ (-A) := Real.rpow_nonneg hlogX.le _
  have hV0 : 0 ≤ V := (Finset.sum_nonneg fun i _ => abs_nonneg _).trans hV
  have hMV : 0 ≤ M * (1 + Real.log X) + V :=
    add_nonneg (mul_nonneg hM0 (by linarith)) hV0
  have hC0L : C0 ≤ (L : ℝ) := by
    have h1 : (C0 ^ (1 / c)) ^ c ≤ X ^ c :=
      Real.rpow_le_rpow (Real.rpow_nonneg hC00 _) hCa hc.le
    rw [← Real.rpow_mul hC00, one_div_mul_cancel hc.ne', Real.rpow_one] at h1
    exact h1.trans hXL
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := hC01.trans hC0L
  have hcl : 0 < c * Real.log X := mul_pos hc hlogX
  obtain ⟨Kl, hKl0, hKl⟩ : ∃ Kl : ℝ, 0 ≤ Kl ∧ Kl = C0 * c ^ (-A) * Real.log X ^ (-A) :=
    ⟨_, mul_nonneg (mul_nonneg hC00 hcA.le) hlX, rfl⟩
  have hpre : ∀ i : ℕ, L ≤ i → i ≤ U →
      |∑ n ∈ Finset.Ioc L i, (primeWeight n - 1 / Real.log (n : ℝ))| ≤ Kl * (i : ℝ) := by
    intro i hLi hiU
    have hiL : (L : ℝ) ≤ (i : ℝ) := Nat.cast_le.mpr hLi
    have hi0 : 0 < (i : ℝ) := by linarith
    have hlogi : c * Real.log X ≤ Real.log (i : ℝ) := by
      rw [← Real.log_rpow hX0]
      exact Real.log_le_log (Real.rpow_pos_of_pos hX0 _) (hXL.trans hiL)
    have hpow : Real.log (i : ℝ) ^ (-A) ≤ c ^ (-A) * Real.log X ^ (-A) := by
      rw [← Real.mul_rpow hc.le hlogX.le, Real.rpow_neg (hcl.le.trans hlogi),
        Real.rpow_neg hcl.le]
      exact inv_anti₀ (Real.rpow_pos_of_pos hcl _) (Real.rpow_le_rpow hcl.le hlogi hA.le)
    have h := h0 (i : ℝ) (hC0L.trans hiL) L i hLi le_rfl
    calc |∑ n ∈ Finset.Ioc L i, (primeWeight n - 1 / Real.log (n : ℝ))|
        ≤ C0 * (i : ℝ) * Real.log (i : ℝ) ^ (-A) := h
      _ ≤ C0 * (i : ℝ) * (c ^ (-A) * Real.log X ^ (-A)) :=
          mul_le_mul_of_nonneg_left hpow (mul_nonneg hC00 hi0.le)
      _ = Kl * (i : ℝ) := by rw [hKl]; ring
  rcases hLU.eq_or_lt with rfl | hlt
  · rw [Finset.Ioc_self, Finset.sum_empty, abs_zero]
    exact mul_nonneg (mul_nonneg hCnn hMV) hlX
  have hU0 : (0 : ℝ) < (U : ℝ) := by
    have : (L : ℝ) < (U : ℝ) := Nat.cast_lt.mpr hlt
    linarith
  have hab := two_pair_abel (fun n => primeWeight n - 1 / Real.log (n : ℝ))
    (fun n => G n / (n : ℝ)) L hLU
  beta_reduce at hab
  rw [hab, Finset.sum_eq_sum_Ico_succ_bot hlt, Finset.Ioc_self, Finset.sum_empty, mul_zero,
    zero_add]
  have hend : |G U / (U : ℝ) * ∑ n ∈ Finset.Ioc L U, (primeWeight n - 1 / Real.log (n : ℝ))| ≤
      M * Kl := by
    rw [abs_mul, abs_div, abs_of_pos hU0]
    have h1 : |G U| / (U : ℝ) ≤ M / (U : ℝ) :=
      div_le_div_of_nonneg_right (hG U (Finset.mem_Ioc.mpr ⟨hlt, le_rfl⟩)) hU0.le
    calc |G U| / (U : ℝ) * |∑ n ∈ Finset.Ioc L U, (primeWeight n - 1 / Real.log (n : ℝ))|
        ≤ M / (U : ℝ) * (Kl * (U : ℝ)) :=
          mul_le_mul h1 (hpre U hLU le_rfl) (abs_nonneg _) (div_nonneg hM0 hU0.le)
      _ = M * Kl := by field_simp
  have hmid : ∀ i ∈ Finset.Ico (L + 1) U,
      |(G (i + 1) / ((i + 1 : ℕ) : ℝ) - G i / (i : ℝ)) *
        ∑ n ∈ Finset.Ioc L i, (primeWeight n - 1 / Real.log (n : ℝ))| ≤
        Kl * (|G (i + 1) - G i| + M * (1 / (i : ℝ))) := by
    intro i hi
    have hi' := Finset.mem_Ico.mp hi
    have hi0 : 0 < (i : ℝ) := by
      have : 0 < i := by omega
      exact_mod_cast this
    have hGi := hG i (Finset.mem_Ioc.mpr ⟨by omega, by omega⟩)
    have hD : G (i + 1) / ((i + 1 : ℕ) : ℝ) - G i / (i : ℝ) =
        (G (i + 1) - G i) / ((i : ℝ) + 1) - G i / ((i : ℝ) * ((i : ℝ) + 1)) := by
      push_cast
      field_simp
      ring
    have hDabs : |G (i + 1) / ((i + 1 : ℕ) : ℝ) - G i / (i : ℝ)| ≤
        (|G (i + 1) - G i| + M * (1 / (i : ℝ))) / (i : ℝ) := by
      rw [hD]
      have h1 : |(G (i + 1) - G i) / ((i : ℝ) + 1)| ≤ |G (i + 1) - G i| / (i : ℝ) := by
        rw [abs_div, abs_of_pos (by linarith : (0 : ℝ) < (i : ℝ) + 1)]
        exact div_le_div_of_nonneg_left (abs_nonneg _) hi0 (by linarith)
      have h2 : |G i / ((i : ℝ) * ((i : ℝ) + 1))| ≤ M * (1 / (i : ℝ)) / (i : ℝ) := by
        rw [abs_div, abs_of_pos (mul_pos hi0 (by linarith : (0 : ℝ) < (i : ℝ) + 1))]
        have h3 : |G i| / ((i : ℝ) * ((i : ℝ) + 1)) ≤ M / ((i : ℝ) * (i : ℝ)) :=
          div_le_div₀ hM0 hGi (mul_pos hi0 hi0)
            (mul_le_mul_of_nonneg_left (by linarith) hi0.le)
        have h4 : M / ((i : ℝ) * (i : ℝ)) = M * (1 / (i : ℝ)) / (i : ℝ) := by
          field_simp
        linarith
      have h5 := abs_sub (( G (i + 1) - G i) / ((i : ℝ) + 1)) (G i / ((i : ℝ) * ((i : ℝ) + 1)))
      have h6 : (|G (i + 1) - G i| + M * (1 / (i : ℝ))) / (i : ℝ) =
          |G (i + 1) - G i| / (i : ℝ) + M * (1 / (i : ℝ)) / (i : ℝ) := by ring
      linarith
    have hnum : 0 ≤ |G (i + 1) - G i| + M * (1 / (i : ℝ)) :=
      add_nonneg (abs_nonneg _) (mul_nonneg hM0 (by positivity))
    rw [abs_mul]
    calc |G (i + 1) / ((i + 1 : ℕ) : ℝ) - G i / (i : ℝ)| *
          |∑ n ∈ Finset.Ioc L i, (primeWeight n - 1 / Real.log (n : ℝ))|
        ≤ (|G (i + 1) - G i| + M * (1 / (i : ℝ))) / (i : ℝ) * (Kl * (i : ℝ)) :=
          mul_le_mul hDabs (hpre i (by omega) (by omega)) (abs_nonneg _)
            (div_nonneg hnum hi0.le)
      _ = Kl * (|G (i + 1) - G i| + M * (1 / (i : ℝ))) := by field_simp
  have hharm : ∑ i ∈ Finset.Ico (L + 1) U, (1 : ℝ) / (i : ℝ) ≤ 1 + Real.log X := by
    have hh : ∑ n ∈ Finset.Icc 1 U, (1 : ℝ) / (n : ℝ) ≤ 1 + Real.log (U : ℝ) := by
      have h1 := harmonic_le_one_add_log U
      rw [harmonic_eq_sum_Icc] at h1
      push_cast at h1
      simpa [one_div] using h1
    have hsub : Finset.Ico (L + 1) U ⊆ Finset.Icc 1 U := by
      intro n hn
      rw [Finset.mem_Ico] at hn
      rw [Finset.mem_Icc]
      omega
    have h2 := Finset.sum_le_sum_of_subset_of_nonneg hsub
      (f := fun n : ℕ => (1 : ℝ) / (n : ℝ)) (fun _ _ _ => by positivity)
    have h3 : Real.log (U : ℝ) ≤ Real.log X := Real.log_le_log hU0 hUX
    linarith
  have hsum : |∑ i ∈ Finset.Ico (L + 1) U,
      (G (i + 1) / ((i + 1 : ℕ) : ℝ) - G i / (i : ℝ)) *
        ∑ n ∈ Finset.Ioc L i, (primeWeight n - 1 / Real.log (n : ℝ))| ≤
      Kl * (V + M * (1 + Real.log X)) :=
    calc _ ≤ ∑ i ∈ Finset.Ico (L + 1) U,
          |(G (i + 1) / ((i + 1 : ℕ) : ℝ) - G i / (i : ℝ)) *
            ∑ n ∈ Finset.Ioc L i, (primeWeight n - 1 / Real.log (n : ℝ))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.Ico (L + 1) U, Kl * (|G (i + 1) - G i| + M * (1 / (i : ℝ))) :=
          Finset.sum_le_sum hmid
      _ = Kl * (∑ i ∈ Finset.Ico (L + 1) U, |G (i + 1) - G i| +
            M * ∑ i ∈ Finset.Ico (L + 1) U, (1 : ℝ) / (i : ℝ)) := by
          rw [← Finset.mul_sum, Finset.sum_add_distrib, ← Finset.mul_sum]
      _ ≤ Kl * (V + M * (1 + Real.log X)) :=
          mul_le_mul_of_nonneg_left
            (add_le_add hV (mul_le_mul_of_nonneg_left hharm hM0)) hKl0
  have e1 := abs_le.mp hend
  have e2 := abs_le.mp hsum
  have hMl : M ≤ M * (1 + Real.log X) := by
    have := mul_nonneg hM0 hlogX.le
    linarith
  have hfin : M * Kl + Kl * (V + M * (1 + Real.log X)) ≤
      max (max (C0 ^ (1 / c)) (2 * (C0 * c ^ (-A)))) 2 * (M * (1 + Real.log X) + V) *
        Real.log X ^ (-A) := by
    have h1 : M * Kl + Kl * (V + M * (1 + Real.log X)) ≤
        2 * Kl * (M * (1 + Real.log X) + V) := by
      have h2 := mul_le_mul_of_nonneg_left hMl hKl0
      have h3 := mul_nonneg hKl0 hV0
      nlinarith
    have h4 : 2 * Kl * (M * (1 + Real.log X) + V) =
        2 * (C0 * c ^ (-A)) * ((M * (1 + Real.log X) + V) * Real.log X ^ (-A)) := by
      rw [hKl]; ring
    have h5 := mul_le_mul_of_nonneg_right hCb (mul_nonneg hMV hlX)
    linarith
  rw [abs_le]
  constructor <;> linarith [e1.1, e1.2, e2.1, e2.2]

end LeanLab.BHP1997.LowerShortC165
