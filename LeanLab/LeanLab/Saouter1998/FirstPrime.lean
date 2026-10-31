/-
Saouter 1998, page 864: 138412033 is the least prime of the required form.
The first three candidates are composite. This closes the earlier Python-only check.
AI wrote this Lean code for CODEX task73. Binary Goldbach is open.
-/
import LeanLab.Saouter1998.Theorem2

namespace LeanLab.Saouter1998.FirstPrime

open LeanLab.Saouter1998.Paper

/-- All odd cofactors with the required last digit have R = 10 k + 3. -/
theorem cofactor_form {R : ℕ} (hR : R % 2 = 1) (h : (2 ^ 22 * R + 1) % 10 = 3) :
    ∃ k : ℕ, R = 10 * k + 3 := by
  have hm : (4 * (R % 10) + 1) % 10 = 3 := by
    norm_num [Nat.add_mod, Nat.mul_mod] at h ⊢
    exact h
  clear h
  refine ⟨R / 10, ?_⟩
  omega

/-- The first three candidates are composite, with small explicit divisors. -/
theorem small_candidates : ¬ (N 0).Prime ∧ ¬ (N 1).Prime ∧ ¬ (N 2).Prime := by
  have h0 : N 0 = 7 * 1797559 := by norm_num [N]
  have h1 : N 1 = 17 * 3207409 := by norm_num [N]
  have h2 : N 2 = 3 * 32156331 := by norm_num [N]
  rw [h0, h1, h2]
  exact ⟨Nat.not_prime_mul (by decide) (by decide),
    Nat.not_prime_mul (by decide) (by decide), Nat.not_prime_mul (by decide) (by decide)⟩

/-- Any prime of the two required forms is at least the paper's first prime. -/
theorem first_le {R : ℕ} (hR : R % 2 = 1) (hp : (2 ^ 22 * R + 1).Prime)
    (hmod : (2 ^ 22 * R + 1) % 10 = 3) : 138412033 ≤ 2 ^ 22 * R + 1 := by
  obtain ⟨k, rfl⟩ := cofactor_form hR hmod
  have hp' : (N k).Prime := by simpa only [N_form] using hp
  have hk : 3 ≤ k := by
    by_contra h
    have hcases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
    rcases hcases with hk0 | hk1 | hk2
    · exact small_candidates.1 (hk0 ▸ hp')
    · exact small_candidates.2.1 (hk1 ▸ hp')
    · exact small_candidates.2.2 (hk2 ▸ hp')
  omega

/-- The least prime assertion on page 864, with primality and minimality together. -/
theorem least_prime : (138412033 : ℕ).Prime ∧
    ∀ R : ℕ, R % 2 = 1 → (2 ^ 22 * R + 1) % 10 = 3 →
      (2 ^ 22 * R + 1).Prime → 138412033 ≤ 2 ^ 22 * R + 1 := by
  exact ⟨Thm2.first_prime, fun _ hR hm hp => first_le hR hp hm⟩

end LeanLab.Saouter1998.FirstPrime
