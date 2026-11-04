/-
AI wrote this Lean code. Codex task286.
Binary Goldbach is open.
Source: Tolev 2009 page 4 display 12.
Written proof: Tolev 1999 pages 71 and 82 to 87, Lemmas 4 and 12.
The fixed residue and full prime interval adaptations remain OPEN.
No L2 assumption is added.
-/
import LeanLab.Tolev2009.Decomp83

open Finset Real

namespace LeanLab.Tolev2009.Decomp286b

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.Displays14to16
open LeanLab.Tolev2009.Dyadic

/-- The number of ordered factorizations into five positive integers, tau5 in display 53. -/
noncomputable def tau5 (n : ℕ) : ℕ := (ArithmeticFunction.zeta ^ 5) n

/-- The weighted bilinear block of Tolev 1999 pages 82 to 83 displays 53 and 54.
The phase is alpha times m times l and the congruence is ml equal to l3 modulo k.
The coprime divisor weight is exactly the already defined weight in L2Bound. -/
noncomputable def bilinear (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (a b : ℕ → ℂ) : ℂ :=
  ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊,
    if x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N then
      a m * b l * ee (α * (m * l : ℕ)) * (L2Bound.weight lam l₃ K (m * l) : ℂ)
    else 0

/-- LEAF. Tolev 1999 displays 53 and 54, the divisor coefficient at one is nonzero. -/
theorem tau5_one : tau5 1 = 1 := by
  norm_num [tau5, pow_succ, ArithmeticFunction.mul_apply_one]

/-- LEAF. Tolev 1999 displays 53 and 54, a nonzero instance of the adapted block.
This checks the block definition and does not witness either uniform estimate. -/
theorem bilinear_nonzero :
    bilinear (fun k => if k = 1 then 1 else 0) 1 1 6 0 3 (1 / 2) 1 3 6
      (fun m => if m = 1 then 1 else 0) (fun _ => 1) = 3 := by
  norm_num [bilinear, L2Bound.weight, ee_zero, Finset.sum_Ioc_succ_top]

/-- LEAF. Tolev 1999 page 86 displays 64 to 66, the two Type I estimates.
Adapted to Tolev 2009 display 12 with a fixed residue and the smaller modulus cutoff.
The shell x is at least N times log N to minus 4A. The first coefficient is normalised.
Both b equal to one and b equal to log l are included. OPEN. -/
theorem typeI_estimate :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((249 : ℝ) / 500) ≤ H →
          ∀ a b : ℕ → ℂ,
            (∀ m, ‖a m‖ ≤ (tau5 m : ℝ) * Real.log N) →
            (b = (fun _ => 1) ∨ b = (fun l : ℕ => (Real.log l : ℂ))) →
            ‖bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ a b‖ ≤
              C * N * Real.log N ^ (330 - 4 * A) := by
  sorry

/-- LEAF. Tolev 1999 pages 83 to 86 displays 55 to 63, the Type II estimate.
The same fixed residue and shell adaptation is required as in typeI_estimate.
Only bilinear sums with both coefficients normalised by tau5 times log N occur. OPEN. -/
theorem typeII_estimate :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((1 : ℝ) / 1000) ≤ H → H ≤ 2 ^ 30 * x ^ ((1 : ℝ) / 3) →
          ∀ a b : ℕ → ℂ,
            (∀ m, ‖a m‖ ≤ (tau5 m : ℝ) * Real.log N) →
            (∀ l, ‖b l‖ ≤ (tau5 l : ℝ) * Real.log N) →
            ‖bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ a b‖ ≤
              C * N * Real.log N ^ (330 - 4 * A) := by
  sorry

/-- LEAF. Tolev 1999 page 71 Lemma 4 and page 82 display 52 followed by 53 and 54.
Apply Heath Brown's identity on dyadic shells, omitting the initial short segment.
The remainder includes that segment and the prime power conversion.
There are at most C log N to seven blocks after shell subdivision.
The source's tau5 coefficient constants are moved into the bounded scalars c. OPEN. -/
theorem prime_decomposition :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) → ∀ α : ℝ,
          ∃ J : ℕ, (J : ℝ) ≤ C * Real.log N ^ (7 : ℕ) ∧
          ∃ r : ℂ, ‖r‖ ≤ C * N * Real.log N ^ (330 - 4 * A) ∧
          ∃ x M M₁ H H₁ : Fin J → ℝ, ∃ a b : Fin J → ℕ → ℂ, ∃ c : Fin J → ℂ,
            Kfun lam l₃ (cutoff3 (10 ^ 4 * A) N) N α = r +
              ∑ j : Fin J, c j * bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
                (x j) (M j) (M₁ j) (H j) (H₁ j) (a j) (b j) ∧
            ∀ j : Fin J,
              ‖c j‖ ≤ C ∧
              (N : ℝ) * Real.log N ^ (-4 * A) ≤ x j ∧ x j ≤ N ∧ 2 < x j ∧
              0 < M j ∧ M j ≤ M₁ j ∧ M₁ j ≤ 2 * M j ∧
              0 < H j ∧ H j ≤ H₁ j ∧ H₁ j ≤ 2 * H j ∧
              x j / 4 ≤ M j * H j ∧ M j * H j ≤ 2 * x j ∧
              (∀ m, ‖a j m‖ ≤ (tau5 m : ℝ) * Real.log N) ∧
              ((x j ^ ((249 : ℝ) / 500) ≤ H j ∧
                  (b j = (fun _ => 1) ∨ b j = (fun l : ℕ => (Real.log l : ℂ)))) ∨
                (x j ^ ((1 : ℝ) / 1000) ≤ H j ∧ H j ≤ 2 ^ 30 * x j ^ ((1 : ℝ) / 3) ∧
                  ∀ l, ‖b j l‖ ≤ (tau5 l : ℝ) * Real.log N)) := by
  sorry

/-- The exact statement of Decomp83.minor_arc_sup_leaf from smaller bilinear leaves.
CONDITIONAL ON the Type I, Type II and prime decomposition leaves.
The L2 half of display 12 is already proved in L2Bound.display12_L2_cutoff. -/
theorem minor_arc_sup_leaf : Sup12Uniform := by
  intro A hA l₃ hl₃
  obtain ⟨Cᵢ, Nᵢ, hCᵢ, hI⟩ := typeI_estimate A hA l₃ hl₃
  obtain ⟨Cᵢᵢ, Nᵢᵢ, hCᵢᵢ, hII⟩ := typeII_estimate A hA l₃ hl₃
  obtain ⟨D, ND, hD, hdec⟩ := prime_decomposition A hA l₃ hl₃
  refine ⟨D + D ^ 2 * (Cᵢ + Cᵢᵢ), max (max Nᵢ Nᵢᵢ) (max ND 3), by positivity, ?_⟩
  intro lam hlam N hodd hN α hα hminor
  have hNᵢ : Nᵢ ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNᵢᵢ : Nᵢᵢ ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hND : ND ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hN3 : (3 : ℝ) ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hL0 : 0 < Real.log N := by linarith
  obtain ⟨J, hJ, r, hr, x, M, M₁, H, H₁, a, b, c, he, hb⟩ :=
    hdec N hodd hND lam hlam α
  have hterm : ∀ j : Fin J,
      ‖bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
        (x j) (M j) (M₁ j) (H j) (H₁ j) (a j) (b j)‖ ≤
        (Cᵢ + Cᵢᵢ) * N * Real.log N ^ (330 - 4 * A) := by
    intro j
    rcases hb j with ⟨hc, hxlo, hxhi, hx, hM, hMM₁, hM₁, hH, hHH₁, hH₁,
      hprodlo, hprodhi, ha, htype⟩
    rcases htype with ⟨hsize, hbI⟩ | ⟨hlo, hhi, hbII⟩
    · have hi := hI N hodd hNᵢ lam hlam α hα hminor
        (x j) (M j) (M₁ j) (H j) (H₁ j)
        hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize (a j) (b j) ha hbI
      exact hi.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hCᵢᵢ) (Nat.cast_nonneg N))
        (Real.rpow_nonneg (Real.log_natCast_nonneg N) _))
    · have hi := hII N hodd hNᵢᵢ lam hlam α hα hminor
        (x j) (M j) (M₁ j) (H j) (H₁ j)
        hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hlo hhi (a j) (b j) ha hbII
      exact hi.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hCᵢ) (Nat.cast_nonneg N))
        (Real.rpow_nonneg (Real.log_natCast_nonneg N) _))
  have hsum : ‖∑ j : Fin J, c j * bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
      (x j) (M j) (M₁ j) (H j) (H₁ j) (a j) (b j)‖ ≤
      (J : ℝ) * (D * ((Cᵢ + Cᵢᵢ) * N * Real.log N ^ (330 - 4 * A))) := by
    refine (norm_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ j : Fin J, D * ((Cᵢ + Cᵢᵢ) * N * Real.log N ^ (330 - 4 * A)) := by
        apply sum_le_sum
        intro j _
        rw [norm_mul]
        exact mul_le_mul (hb j).1 (hterm j) (norm_nonneg _) hD
      _ = _ := by simp
  have hpow : Real.log N ^ (7 : ℕ) * Real.log N ^ (330 - 4 * A) ≤
      Real.log N ^ (350 - 4 * A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_add hL0]
    exact Real.rpow_le_rpow_of_exponent_le hL (by norm_num; linarith)
  have hpow0 : Real.log N ^ (330 - 4 * A) ≤ Real.log N ^ (350 - 4 * A) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hsum' : ‖∑ j : Fin J, c j * bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
      (x j) (M j) (M₁ j) (H j) (H₁ j) (a j) (b j)‖ ≤
      D ^ 2 * (Cᵢ + Cᵢᵢ) * N * Real.log N ^ (350 - 4 * A) := by
    calc
      _ ≤ (J : ℝ) * (D * ((Cᵢ + Cᵢᵢ) * N * Real.log N ^ (330 - 4 * A))) := hsum
      _ ≤ (D * Real.log N ^ (7 : ℕ)) *
          (D * ((Cᵢ + Cᵢᵢ) * N * Real.log N ^ (330 - 4 * A))) :=
        mul_le_mul_of_nonneg_right hJ (by positivity)
      _ = D ^ 2 * (Cᵢ + Cᵢᵢ) * N *
          (Real.log N ^ (7 : ℕ) * Real.log N ^ (330 - 4 * A)) := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left hpow (by positivity)
  have hr' := hr.trans (mul_le_mul_of_nonneg_left hpow0
    (show 0 ≤ D * (N : ℝ) by positivity))
  rw [he]
  calc
    _ ≤ ‖r‖ + ‖∑ j : Fin J, c j * bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α
        (x j) (M j) (M₁ j) (H j) (H₁ j) (a j) (b j)‖ := norm_add_le _ _
    _ ≤ D * N * Real.log N ^ (350 - 4 * A) +
        D ^ 2 * (Cᵢ + Cᵢᵢ) * N * Real.log N ^ (350 - 4 * A) := add_le_add hr' hsum'
    _ = _ := by ring

end LeanLab.Tolev2009.Decomp286b
