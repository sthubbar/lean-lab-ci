import LeanLab.LiuWang2002.Checkpoint368

/-!
Sparse endpoint reductions for the finite primorial certificates.
Source Schoenfeld page 356, display 5.1 star, derived interpolation.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LiuWang2002.Task551
/-- A right endpoint product with the exponent of the first integer
bounds every integer in the interval. Derived interpolation for
Schoenfeld page 356, display 5.1 star. -/
theorem primorial_interval_of_endpoint (a b n : ℕ) (ha : a < n) (hb : n ≤ b)
    (hc : primorial b * 25 ^ (a + 1) < 68 ^ (a + 1)) :
    primorial n * 25 ^ n < 68 ^ n := by
  have hn : primorial n * 25 ^ (a + 1) < 68 ^ (a + 1) :=
    (Nat.mul_le_mul_right _ (primorial_mono hb)).trans_lt hc
  obtain ⟨t, rfl⟩ := Nat.exists_eq_add_of_le (show a + 1 ≤ n by omega)
  exact Task368.certificate_exponent _ _ _ hn

/-- Sparse endpoint inequalities imply every integer certificate in
a bounded interval. Only intervals whose left endpoint is below B
are requested. Derived reduction for Schoenfeld page 356, display 5.1 star. -/
theorem primorial_interval_of_mesh (A B step : ℕ) (hstep : 0 < step)
    (hc : ∀ i : ℕ, A + step * i < B →
      primorial (min B (A + step * (i + 1))) * 25 ^ (A + step * i + 1) <
        68 ^ (A + step * i + 1))
    (n : ℕ) (hn : A < n) (hn' : n ≤ B) :
    primorial n * 25 ^ n < 68 ^ n := by
  let i := (n - A - 1) / step
  have hlo : step * i ≤ n - A - 1 := by
    dsimp [i]
    simpa only [Nat.mul_comm] using Nat.div_mul_le_self (n - A - 1) step
  have hmod := Nat.mod_lt (n - A - 1) hstep
  have heq := Nat.mod_add_div (n - A - 1) step
  have hleft : A + step * i < n := by omega
  have hright : n ≤ A + step * (i + 1) := by
    rw [Nat.mul_add, Nat.mul_one]
    dsimp [i]
    omega
  exact primorial_interval_of_endpoint (A + step * i)
    (min B (A + step * (i + 1))) n hleft (le_min hn' hright)
    (hc i (hleft.trans_le hn'))
/-- A positive width mesh with two actual prime endpoints has
consistent certificate hypotheses. Derived instance for Schoenfeld
page 356, display 5.1 star. -/
theorem mesh_instance :
    (∀ i : ℕ, 1 + 1 * i < 3 →
      primorial (min 3 (1 + 1 * (i + 1))) * 25 ^ (1 + 1 * i + 1) <
        68 ^ (1 + 1 * i + 1)) ∧
    (∀ n : ℕ, 1 < n → n ≤ 3 → primorial n * 25 ^ n < 68 ^ n) := by
  have hc : ∀ i : ℕ, 1 + 1 * i < 3 →
      primorial (min 3 (1 + 1 * (i + 1))) * 25 ^ (1 + 1 * i + 1) <
        68 ^ (1 + 1 * i + 1) := by
    intro i hi
    have hi' : i ≤ 1 := by omega
    interval_cases i <;> decide +kernel
  exact ⟨hc, primorial_interval_of_mesh 1 3 1 (by decide) hc⟩
end LeanLab.LiuWang2002.Task551
#print axioms LeanLab.LiuWang2002.Task551.primorial_interval_of_endpoint
#print axioms LeanLab.LiuWang2002.Task551.primorial_interval_of_mesh
#print axioms LeanLab.LiuWang2002.Task551.mesh_instance
