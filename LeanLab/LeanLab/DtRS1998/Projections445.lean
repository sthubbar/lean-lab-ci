/-
AI wrote this Lean code for CODEX task445.
Cohen and H. W. Lenstra 1984 page 306, proof of Theorem 6.3.
This is the finite exponent recombination step with t equal to 5040.
The character and p-adic inputs are not proved here.
Binary Goldbach is open.
-/
import Mathlib.Algebra.Group.Basic
import Mathlib.Data.ZMod.Basic

namespace LeanLab.DtRS1998.Projections445

/-- Cohen and H. W. Lenstra 1984 page 306, the choice of l(r) in the
proof of Theorem 6.3. The four complementary exponents have positive
coefficients whose sum is one modulo 5040. This is finite CRT arithmetic. -/
theorem reconstruction_coefficients :
    5040 = 16 * 9 * 5 * 7 ∧
    315 * 3 + 560 * 5 + 1008 * 2 + 720 * 6 = 2 * 5040 + 1 := by
  decide

/-- Cohen and H. W. Lenstra 1984 page 306, proof of Theorem 6.3.
CONDITIONAL ON the four supplied primary component equalities and
periodicity of y. Four separate witnesses recombine into one exponent.
This algebraic lemma asserts no character test has passed. -/
theorem orbit_of_primary_components {G : Type*} [Monoid G] {x y : G}
    (hy : y ^ 5040 = 1)
    (h2 : ∃ i : ℕ, i < 16 ∧ x ^ 315 = y ^ (315 * i))
    (h3 : ∃ i : ℕ, i < 9 ∧ x ^ 560 = y ^ (560 * i))
    (h5 : ∃ i : ℕ, i < 5 ∧ x ^ 1008 = y ^ (1008 * i))
    (h7 : ∃ i : ℕ, i < 7 ∧ x ^ 720 = y ^ (720 * i)) :
    ∃ i : ℕ, i < 5040 ∧ x = y ^ i := by
  obtain ⟨i2, _, h2⟩ := h2
  obtain ⟨i3, _, h3⟩ := h3
  obtain ⟨i5, _, h5⟩ := h5
  obtain ⟨i7, _, h7⟩ := h7
  have hx : x ^ 5040 = 1 := by
    calc
      x ^ 5040 = (x ^ 315) ^ 16 := by rw [← pow_mul]
      _ = (y ^ (315 * i2)) ^ 16 := by rw [h2]
      _ = (y ^ 5040) ^ i2 := by
        simp only [← pow_mul]
        congr 1
        omega
      _ = 1 := by simp [hy]
  have hxprod : x = (x ^ 315) ^ 3 * (x ^ 560) ^ 5 *
      (x ^ 1008) ^ 2 * (x ^ 720) ^ 6 := by
    calc
      x = (x ^ 5040) ^ 2 * x := by simp [hx]
      _ = x ^ 10081 := by simp only [← pow_mul, ← pow_succ]
      _ = _ := by simp only [← pow_mul, ← pow_add]
  let k := 315 * i2 * 3 + 560 * i3 * 5 + 1008 * i5 * 2 + 720 * i7 * 6
  refine ⟨k % 5040, Nat.mod_lt _ (by decide), ?_⟩
  calc
    x = y ^ k := by
      rw [hxprod, h2, h3, h5, h7]
      simp only [← pow_mul, ← pow_add]
      rfl
    _ = y ^ (k % 5040) := pow_eq_pow_mod k hy

#print axioms reconstruction_coefficients
#print axioms orbit_of_primary_components

end LeanLab.DtRS1998.Projections445

namespace LeanLab.DtRS1998.Projections445

/-- Cohen and H. W. Lenstra 1984 page 306, exponent reduction at the
end of the proof of Theorem 6.3. CONDITIONAL ON the four supplied
primary residue congruences and the periodicity check. -/
theorem residue_orbit_of_primary_components {n r s : ℕ}
    (hn : Nat.powMod n 5040 s = 1)
    (h2 : ∃ i : ℕ, i < 16 ∧ r ^ 315 % s = n ^ (315 * i) % s)
    (h3 : ∃ i : ℕ, i < 9 ∧ r ^ 560 % s = n ^ (560 * i) % s)
    (h5 : ∃ i : ℕ, i < 5 ∧ r ^ 1008 % s = n ^ (1008 * i) % s)
    (h7 : ∃ i : ℕ, i < 7 ∧ r ^ 720 % s = n ^ (720 * i) % s) :
    ∃ i : ℕ, i < 5040 ∧ r % s = n ^ i % s := by
  have hy : (n : ZMod s) ^ 5040 = 1 := by
    rw [Nat.powMod_def] at hn
    have h := congrArg (fun a : ℕ => (a : ZMod s)) hn
    simpa only [ZMod.natCast_mod, Nat.cast_pow, Nat.cast_one] using h
  have cast_component (e b : ℕ)
      (h : ∃ i : ℕ, i < b ∧ r ^ e % s = n ^ (e * i) % s) :
      ∃ i : ℕ, i < b ∧ (r : ZMod s) ^ e = (n : ZMod s) ^ (e * i) := by
    obtain ⟨i, hi, heq⟩ := h
    refine ⟨i, hi, ?_⟩
    simpa only [Nat.cast_pow] using
      (ZMod.natCast_eq_natCast_iff' _ _ s).mpr heq
  obtain ⟨i, hi, heq⟩ := orbit_of_primary_components hy
    (cast_component 315 16 h2) (cast_component 560 9 h3)
    (cast_component 1008 5 h5) (cast_component 720 7 h7)
  refine ⟨i, hi, ?_⟩
  apply (ZMod.natCast_eq_natCast_iff' _ _ s).mp
  simpa only [Nat.cast_pow] using heq

#print axioms residue_orbit_of_primary_components

end LeanLab.DtRS1998.Projections445

namespace LeanLab.DtRS1998.Projections445

/-- Cohen and H. W. Lenstra 1984 page 306, primary exponent selection
in the proof of Theorem 6.3. A full orbit witness always supplies each
smaller complementary power witness. This is the reverse soundness audit
for the four OPEN component obligations, not a character test. -/
theorem component_of_orbit {G : Type*} [Monoid G] {x y : G}
    {e b t : ℕ} (hb : 0 < b) (het : e * b = t) (hy : y ^ t = 1)
    (horbit : ∃ i : ℕ, x = y ^ i) :
    ∃ i : ℕ, i < b ∧ x ^ e = y ^ (e * i) := by
  obtain ⟨i, rfl⟩ := horbit
  have he : (y ^ e) ^ b = 1 := by rw [← pow_mul, het, hy]
  refine ⟨i % b, Nat.mod_lt _ hb, ?_⟩
  calc
    (y ^ i) ^ e = (y ^ e) ^ i := by
      rw [← pow_mul, ← pow_mul, Nat.mul_comm i e]
    _ = (y ^ e) ^ (i % b) := pow_eq_pow_mod i he
    _ = y ^ (e * (i % b)) := (pow_mul _ _ _).symm

/-- Cohen and H. W. Lenstra 1984 page 306, primary exponent
recombination and reduction modulo t. CONDITIONAL ON periodicity of y.
The four component obligations are together equivalent to the full orbit
obligation. The decomposition neither strengthens nor weakens the target. -/
theorem orbit_iff_primary_components {G : Type*} [Monoid G] {x y : G}
    (hy : y ^ 5040 = 1) :
    (∃ i : ℕ, i < 5040 ∧ x = y ^ i) ↔
      (∃ i : ℕ, i < 16 ∧ x ^ 315 = y ^ (315 * i)) ∧
      (∃ i : ℕ, i < 9 ∧ x ^ 560 = y ^ (560 * i)) ∧
      (∃ i : ℕ, i < 5 ∧ x ^ 1008 = y ^ (1008 * i)) ∧
      (∃ i : ℕ, i < 7 ∧ x ^ 720 = y ^ (720 * i)) := by
  constructor
  · rintro ⟨i, _, hi⟩
    exact ⟨component_of_orbit (by decide) (by decide) hy ⟨i, hi⟩,
      component_of_orbit (by decide) (by decide) hy ⟨i, hi⟩,
      component_of_orbit (by decide) (by decide) hy ⟨i, hi⟩,
      component_of_orbit (by decide) (by decide) hy ⟨i, hi⟩⟩
  · rintro ⟨h2, h3, h5, h7⟩
    exact orbit_of_primary_components hy h2 h3 h5 h7

#print axioms component_of_orbit
#print axioms orbit_iff_primary_components

end LeanLab.DtRS1998.Projections445
