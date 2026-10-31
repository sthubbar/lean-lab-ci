import LeanLab.RieselVaughan1983.Lemma2Local

/-!
An absolute majorant for the g of equations 2.5 and 2.6 on page 46.
This supports H at minus one third and equation 3.7 on page 50.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RieselVaughan1983.Lemma2

open Real

noncomputable section

def mass (n : ℕ) : ℝ := |g n| * (n : ℝ) ^ (1 / 3 : ℝ)

def localMass (p : ℕ) : ℝ := mass p + mass (p ^ 2) + mass (p ^ 3)

lemma mass_nonneg (n : ℕ) : 0 ≤ mass n := by unfold mass; positivity

lemma mass_zero : mass 0 = 0 := by simp [mass]

lemma mass_one : mass 1 = 1 := by simp [mass, g_multiplicative.map_one]

lemma mass_mul {m n : ℕ} (h : m.Coprime n) : mass (m * n) = mass m * mass n := by
  simp only [mass, g_multiplicative.map_mul_of_coprime h, Nat.cast_mul, abs_mul,
    Real.mul_rpow (Nat.cast_nonneg m) (Nat.cast_nonneg n)]
  ring

lemma root_pow (p k : ℕ) :
    ((p ^ k : ℕ) : ℝ) ^ (1 / 3 : ℝ) = ((p : ℝ) ^ (1 / 3 : ℝ)) ^ k := by
  rw [Nat.cast_pow, ← Real.rpow_natCast_mul (Nat.cast_nonneg p),
    mul_comm (k : ℝ) (1 / 3 : ℝ), Real.rpow_mul_natCast (Nat.cast_nonneg p)]

lemma root_ge_one (p : ℕ) (hp : 1 ≤ p) : 1 ≤ (p : ℝ) ^ (1 / 3 : ℝ) :=
  Real.one_le_rpow (by exact_mod_cast hp) (by norm_num)

lemma root_cube (p : ℕ) : ((p : ℝ) ^ (1 / 3 : ℝ)) ^ 3 = p := by
  rw [← Real.rpow_mul_natCast (Nat.cast_nonneg p)]
  norm_num

lemma root_sq_div_sq (p : ℕ) (hp : (0 : ℝ) < p) :
    ((p : ℝ) ^ (1 / 3 : ℝ)) ^ 2 / (p : ℝ) ^ 2 = (p : ℝ) ^ (-(4 / 3 : ℝ)) := by
  rw [← Real.rpow_mul_natCast hp.le, ← Real.rpow_natCast, ← Real.rpow_sub hp]
  norm_num

lemma abs_g_prime_le (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    |g p| ≤ 12 / (p : ℝ) ^ 2 := by
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < p := by linarith
  have hpm2 : 0 < (p : ℝ) - 2 := by linarith
  rw [g_odd_prime p hp hp2, abs_of_pos (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg hp0.le (show 0 ≤ (p : ℝ) - 3 by linarith)]

lemma abs_g_prime_sq_le (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    |g (p ^ 2)| ≤ 11 / (p : ℝ) ^ 2 := by
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < p := by linarith
  have hpm2 : 0 < (p : ℝ) - 2 := by linarith
  rw [g_odd_prime_sq p hp hp2, abs_div, abs_of_nonpos (by linarith),
    abs_of_pos (by positivity), div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sq_nonneg (p : ℝ)) (show 0 ≤ (p : ℝ) - 3 by linarith)]

lemma abs_g_prime_cube_le (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    |g (p ^ 3)| ≤ 6 / (p : ℝ) ^ 3 := by
  have hp3 : (3 : ℝ) ≤ p := by exact_mod_cast hp2
  have hp0 : (0 : ℝ) < p := by linarith
  have hpm2 : 0 < (p : ℝ) - 2 := by linarith
  rw [g_odd_prime_cube p hp hp2, abs_of_pos (by positivity),
    div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sq_nonneg (p : ℝ)) (show 0 ≤ (p : ℝ) - 3 by linarith)]

lemma localMass_nonneg (p : ℕ) : 0 ≤ localMass p := by
  unfold localMass
  linarith [mass_nonneg p, mass_nonneg (p ^ 2), mass_nonneg (p ^ 3)]

/-- The comparison with a convergent p-series. -/
theorem localMass_le (p : ℕ) (hp : p.Prime) (hp2 : 2 < p) :
    localMass p ≤ 29 * (p : ℝ) ^ (-(4 / 3 : ℝ)) := by
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  let c : ℝ := (p : ℝ) ^ (1 / 3 : ℝ)
  have hc1 : 1 ≤ c := root_ge_one p hp.one_lt.le
  have hc0 : 0 ≤ c := by linarith
  have hc2 : c ≤ c ^ 2 := by nlinarith [mul_nonneg hc0 (sub_nonneg.mpr hc1)]
  have hcSq : 1 ≤ c ^ 2 := by nlinarith
  have hc3 : c ^ 3 = (p : ℝ) := root_cube p
  have h1 : mass p ≤ 12 * (c ^ 2 / (p : ℝ) ^ 2) := by
    change |g p| * c ≤ _
    calc |g p| * c ≤ (12 / (p : ℝ) ^ 2) * c :=
          mul_le_mul_of_nonneg_right (abs_g_prime_le p hp hp2) hc0
      _ ≤ (12 / (p : ℝ) ^ 2) * c ^ 2 :=
          mul_le_mul_of_nonneg_left hc2 (by positivity)
      _ = _ := by ring
  have h2 : mass (p ^ 2) ≤ 11 * (c ^ 2 / (p : ℝ) ^ 2) := by
    rw [mass, root_pow]
    change |g (p ^ 2)| * c ^ 2 ≤ _
    calc |g (p ^ 2)| * c ^ 2 ≤ (11 / (p : ℝ) ^ 2) * c ^ 2 :=
          mul_le_mul_of_nonneg_right (abs_g_prime_sq_le p hp hp2) (sq_nonneg c)
      _ = _ := by ring
  have h3 : mass (p ^ 3) ≤ 6 * (c ^ 2 / (p : ℝ) ^ 2) := by
    rw [mass, root_pow]
    change |g (p ^ 3)| * c ^ 3 ≤ _
    rw [hc3]
    calc |g (p ^ 3)| * (p : ℝ) ≤ (6 / (p : ℝ) ^ 3) * p :=
          mul_le_mul_of_nonneg_right (abs_g_prime_cube_le p hp hp2) hp0.le
      _ = 6 / (p : ℝ) ^ 2 := by field_simp [hp0.ne'] <;> ring
      _ ≤ 6 * (c ^ 2 / (p : ℝ) ^ 2) := by
        simpa only [mul_div_assoc] using div_le_div_of_nonneg_right
          (show (6 : ℝ) ≤ 6 * c ^ 2 by nlinarith) (sq_nonneg (p : ℝ))
  have hr : c ^ 2 / (p : ℝ) ^ 2 = (p : ℝ) ^ (-(4 / 3 : ℝ)) := root_sq_div_sq p hp0
  calc localMass p ≤ 29 * (c ^ 2 / (p : ℝ) ^ 2) := by
        unfold localMass; linarith
    _ = _ := by rw [hr]

end
end LeanLab.RieselVaughan1983.Lemma2

#print axioms LeanLab.RieselVaughan1983.Lemma2.mass_nonneg
#print axioms LeanLab.RieselVaughan1983.Lemma2.mass_zero
#print axioms LeanLab.RieselVaughan1983.Lemma2.mass_one
#print axioms LeanLab.RieselVaughan1983.Lemma2.mass_mul
#print axioms LeanLab.RieselVaughan1983.Lemma2.root_pow
#print axioms LeanLab.RieselVaughan1983.Lemma2.root_ge_one
#print axioms LeanLab.RieselVaughan1983.Lemma2.root_cube
#print axioms LeanLab.RieselVaughan1983.Lemma2.root_sq_div_sq
#print axioms LeanLab.RieselVaughan1983.Lemma2.abs_g_prime_le
#print axioms LeanLab.RieselVaughan1983.Lemma2.abs_g_prime_sq_le
#print axioms LeanLab.RieselVaughan1983.Lemma2.abs_g_prime_cube_le
#print axioms LeanLab.RieselVaughan1983.Lemma2.localMass_nonneg
#print axioms LeanLab.RieselVaughan1983.Lemma2.localMass_le
