/-
P0093 page 159 equation 5.1. Audit of unordered tsum in the Mellin split.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Supply473
import LeanLab.Linnik1951.SPLIT1622_mellin

namespace LeanLab.Linnik1951

/-- The principal undamped prime power series on the line at N sixteen has
unordered tsum value zero. This audits the annotation of page 159 equation 5.1. -/
theorem principal_undamped_zero473 (t : ℝ) :
    (∑' p : Nat.Primes, ∑' m : ℕ,
      ((m : ℂ) + 1)⁻¹ * (1 : DirichletCharacter ℂ 1) ((p : ℕ) ^ (m + 1)) *
        (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-(mellinLine1622 16 t))) = 0 := by
  simp only [MulChar.one_apply (isUnit_of_subsingleton _), mul_one]
  apply prime_power_undamped_tsum_zero473
  all_goals
    have hlog : 2 < Real.log (16 : ℝ) := by
      have h : Real.log (16 : ℝ) = 4 * Real.log 2 := by
        rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
        norm_num
      rw [h]
      linarith [Real.log_two_gt_d9]
    simp only [mellinLine1622, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
      sub_zero, add_zero]
  · positivity
  · have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hlog.le
    norm_num at h ⊢
    linarith

/-- The Mellin integral in the principal counterexample is zero at every phase.
This is an annotation audit of page 159 equation 5.1. -/
theorem principal_mellin_zero473 (α : ℝ) :
    mellinU1622 16
      (fun t : ℝ => ∑' p : Nat.Primes, ∑' m : ℕ,
        ((m : ℂ) + 1)⁻¹ * (1 : DirichletCharacter ℂ 1) ((p : ℕ) ^ (m + 1)) *
          (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-(mellinLine1622 16 t))) α = 0 := by
  simp only [mellinU1622, principal_undamped_zero473, mul_zero,
    MeasureTheory.integral_zero]

/-- The damped side at the principal character and phase zero has positive real
part. This is an annotation audit of page 159 equation 5.1. -/
theorem principal_damped_pos473 (N : ℕ) (hN : 2 ≤ N) :
    0 < (∑' p : Nat.Primes, ∑' m : ℕ,
      ((m : ℂ) + 1)⁻¹ * (1 : DirichletCharacter ℂ 1) ((p : ℕ) ^ (m + 1)) *
        (Real.exp (-(((p : ℕ) : ℝ) ^ (m + 1) / (N : ℝ))) : ℂ) *
          Complex.exp
            ((-(2 * Real.pi * (0 : ℝ) * (((p : ℕ) : ℝ) ^ (m + 1))) : ℝ) * Complex.I)).re := by
  let g : Nat.Primes × ℕ → ℝ := fun x =>
    ((x.2 : ℝ) + 1)⁻¹ * Real.exp (-(((x.1 : ℕ) : ℝ) ^ (x.2 + 1) / (N : ℝ)))
  have hgn : ∀ x, 0 ≤ g x := by intro x; dsimp [g]; positivity
  have hgs : Summable g := by
    apply Summable.of_nonneg_of_le hgn _
      (prime_power_damping_summable473 N (by omega))
    intro x
    dsimp [g]
    apply mul_le_of_le_one_left (Real.exp_pos _).le
    apply (inv_le_one₀ (by positivity)).mpr
    linarith [Nat.cast_nonneg (α := ℝ) x.2]
  have hpos : 0 < ∑' x, g x := by
    apply hgs.tsum_pos hgn (⟨⟨2, Nat.prime_two⟩, 0⟩ : Nat.Primes × ℕ)
    dsimp [g]
    positivity
  have heq : (∑' p : Nat.Primes, ∑' m : ℕ,
      ((m : ℂ) + 1)⁻¹ * (1 : DirichletCharacter ℂ 1) ((p : ℕ) ^ (m + 1)) *
        (Real.exp (-(((p : ℕ) : ℝ) ^ (m + 1) / (N : ℝ))) : ℂ) *
          Complex.exp
            ((-(2 * Real.pi * (0 : ℝ) * (((p : ℕ) : ℝ) ^ (m + 1))) : ℝ) * Complex.I))
        = ((∑' x, g x : ℝ) : ℂ) := by
    rw [hgs.tsum_prod, Complex.ofReal_tsum]
    apply tsum_congr
    intro p
    rw [Complex.ofReal_tsum]
    apply tsum_congr
    intro m
    simp [g, MulChar.one_apply (isUnit_of_subsingleton _)]
  rw [heq, Complex.ofReal_re]
  exact hpos

/-- The exact universally quantified Mellin series leaf is false. The witness is
N sixteen, modulus one, the principal character and phase zero. This audits the
Lean annotation and does not assert a paper error. -/
theorem not_mellin_prime_power_series1622 :
    ¬ (∀ N : ℕ, 2 ≤ N → ∀ (q : ℕ) [NeZero q], ∀ χ : DirichletCharacter ℂ q, ∀ α : ℝ,
      mellinU1622 N
          (fun t : ℝ => ∑' p : Nat.Primes, ∑' m : ℕ,
            ((m : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (m + 1)) *
              (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-(mellinLine1622 N t))) α
        = ∑' p : Nat.Primes, ∑' m : ℕ,
            ((m : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (m + 1)) *
              (Real.exp (-(((p : ℕ) : ℝ) ^ (m + 1) / (N : ℝ))) : ℂ) *
                Complex.exp
                  ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (m + 1))) : ℝ) * Complex.I)) := by
  intro h
  have heq := h 16 (by norm_num) 1 (1 : DirichletCharacter ℂ 1) 0
  rw [principal_mellin_zero473] at heq
  have hp := principal_damped_pos473 16 (by norm_num)
  rw [← heq] at hp
  simp at hp

/-- The Euler leaf conclusion fails at N sixteen for every nonprincipal
character. This audits the unordered series in page 159 equation 5.1. -/
theorem log_prime_power_failure473 (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ ≠ 1) :
    ∃ t : ℝ, Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 16 t)) ≠
      ∑' p : Nat.Primes, ∑' m : ℕ,
        ((m : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (m + 1)) *
          (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-(mellinLine1622 16 t)) := by
  obtain ⟨t, ht⟩ := log_L_nonzero_on_vertical473 q χ hχ
    (1 / 2 + 1 / Real.log (16 : ℝ))
  refine ⟨t, ?_⟩
  have hline : 0 < (mellinLine1622 16 t).re ∧ (mellinLine1622 16 t).re ≤ 1 := by
    constructor
    all_goals
      have hlog : 2 < Real.log (16 : ℝ) := by
        have h : Real.log (16 : ℝ) = 4 * Real.log 2 := by
          rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, Real.log_pow]
          norm_num
        rw [h]
        linarith [Real.log_two_gt_d9]
      simp only [mellinLine1622, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul,
        sub_zero, add_zero]
    · positivity
    · have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 2) hlog.le
      norm_num at h ⊢
      linarith
  rw [character_prime_power_undamped_zero473 q χ _ hline.1 hline.2]
  exact ht

/-- The universally quantified conclusion of the Euler leaf is false. This
statement has no GRH hypothesis and makes no assertion about the truth of GRH. -/
theorem not_log_L_prime_power_series1622_conclusion :
    ¬ (∀ N : ℕ, 2 ≤ N → ∀ (q : ℕ) [NeZero q], ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
      ∀ t : ℝ, Complex.log (DirichletCharacter.LFunction χ (mellinLine1622 N t))
        = ∑' p : Nat.Primes, ∑' m : ℕ,
            ((m : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (m + 1)) *
              (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-(mellinLine1622 N t))) := by
  intro h
  obtain ⟨χ, hχ⟩ := DirichletCharacter.exists_apply_ne_one_of_hasEnoughRootsOfUnity
    ℂ (a := (2 : ZMod 3)) (by decide)
  have hn : χ ≠ 1 := by
    intro he
    subst χ
    exact hχ (MulChar.one_apply (by decide))
  obtain ⟨t, ht⟩ := log_prime_power_failure473 3 χ hn
  exact ht (h 16 (by norm_num) 3 χ hn t)

end LeanLab.Linnik1951
