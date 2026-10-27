import LeanLab.Ricci1937.TheoremsCD

/-!
Ricci 1937, page 83: the powers used for the part 2 sieve thresholds.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937
noncomputable section

/-- The next integer above the stated factor bound reaches the degree ratio. -/
lemma c2_next_bound_mul {g s : ℕ} (hg : 1 ≤ g) (hsg : g < s) :
    2 * s * g ≤ ((2 * s * g - 1) / (s - g) + 1) * (s - g) := by
  have hden : 0 < s - g := by omega
  have hdiv := Nat.mod_lt (2 * s * g - 1) hden
  have heq := Nat.mod_add_div (2 * s * g - 1) (s - g)
  have hspos : 0 < s := by omega
  have hpos : 0 < 2 * s * g := by positivity
  have hnum : 2 * s * g - 1 + 1 = 2 * s * g := by omega
  nlinarith

/-- The selected prime threshold power is large enough to dominate xi to degree g. -/
lemma c2_next_bound_exponent {g s : ℕ} (hg : 1 ≤ g) (hsg : g < s) :
    (g : ℝ) ≤ (((s : ℝ) - g) / (2 * s)) *
      (((2 * s * g - 1) / (s - g) + 1 : ℕ) : ℝ) := by
  have hspos : (0 : ℝ) < s := by exact_mod_cast (by omega : 0 < s)
  have hmul := c2_next_bound_mul hg hsg
  have hsub : ((s - g : ℕ) : ℝ) = (s : ℝ) - g := Nat.cast_sub (by omega)
  have hmulR0 : 2 * (s : ℝ) * g ≤
      (((2 * s * g - 1) / (s - g) + 1 : ℕ) : ℝ) * ((s - g : ℕ) : ℝ) := by
    exact_mod_cast hmul
  rw [hsub] at hmulR0
  rw [div_mul_eq_mul_div]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 * s)).mpr
  nlinarith

/-- A coefficient C at least one absorbs the polynomial size constant. -/
lemma scaled_threshold_power {C ξ α : ℝ} {g k : ℕ}
    (hC : 1 ≤ C) (hξ : 1 ≤ ξ) (hk : 1 ≤ k) (hexp : (g : ℝ) ≤ α * k) :
    C * ξ ^ g ≤ (C * ξ ^ α) ^ k := by
  have hξ0 : 0 ≤ ξ := by linarith
  rw [mul_pow, ← Real.rpow_mul_natCast hξ0]
  have hCp : C ≤ C ^ k := le_self_pow₀ hC (by omega)
  have hξp : ξ ^ g ≤ ξ ^ (α * k) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le hξ hexp
  exact mul_le_mul hCp hξp (pow_nonneg hξ0 _) (by positivity)

/-- Page 83: the prime threshold forces the stated total factor bound. -/
lemma c2_prime_threshold_power {g s : ℕ} (hg : 1 ≤ g) (hsg : g < s)
    {C ξ : ℝ} (hC : 1 ≤ C) (hξ : 1 ≤ ξ) :
    C * ξ ^ g ≤ (C * ξ ^ (((s : ℝ) - g) / (2 * s))) ^
      (((2 * s * g - 1) / (s - g) + 1) : ℕ) :=
  scaled_threshold_power (g := g) (k := (2 * s * g - 1) / (s - g) + 1)
    hC hξ (Nat.succ_le_succ (Nat.zero_le _)) (c2_next_bound_exponent hg hsg)

/-- Page 83: the square threshold forces all prime multiplicities below s. -/
lemma c2_square_threshold_power {g s : ℕ} (hsg : g < s)
    {C ξ : ℝ} (hC : 1 ≤ C) (hξ : 1 ≤ ξ) :
    C * ξ ^ g ≤ (C * ξ ^ ((g : ℝ) / s)) ^ s := by
  apply scaled_threshold_power hC hξ (by omega)
  have hs0 : (s : ℝ) ≠ 0 := by exact_mod_cast (by omega : s ≠ 0)
  rw [div_mul_cancel₀ _ hs0]

example : (2 : ℕ) * 3 * 1 ≤ ((2 * 3 * 1 - 1) / (3 - 1) + 1) * (3 - 1) := by
  norm_num

example : (2 : ℝ) * 8 ^ (1 : ℕ) ≤
    (2 * (8 : ℝ) ^ (((3 : ℝ) - 1) / (2 * 3))) ^ (3 : ℕ) := by
  simpa using c2_prime_threshold_power (g := 1) (s := 3) (C := 2) (ξ := 8) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num)

example : (2 : ℝ) * 8 ^ (1 : ℕ) ≤
    (2 * (8 : ℝ) ^ ((1 : ℝ) / 3)) ^ (3 : ℕ) := by
  simpa using c2_square_threshold_power (g := 1) (s := 3) (C := 2) (ξ := 8) (by norm_num) (by norm_num) (by norm_num)

end
end LeanLab.Ricci1937
