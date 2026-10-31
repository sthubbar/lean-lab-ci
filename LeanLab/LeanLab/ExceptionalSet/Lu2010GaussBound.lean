/-
P0095 Lu 2010, page 2379 equation 63, general induced Gauss factor bound.
CODEX task47, unit U-8101. AI wrote this Lean code. Binary Goldbach is open.
The CRT factorization is the existing RieselVaughan1983 GaussImprim theorem.
The nonsquarefree and shared-prime zero cases are supplied by Lu2010Induced.
-/
import LeanLab.ExceptionalSet.Lu2010Induced
import LeanLab.RieselVaughan1983.GaussImprim

namespace LeanLab.ExceptionalSet.Lu2010GaussBound
open Finset ZMod DirichletCharacter
open LeanLab.ExceptionalSet.Lu2010Induced
open LeanLab.RieselVaughan1983.GaussImprim
open scoped ArithmeticFunction.Moebius

/-- The Ramanujan sum at 1 has norm at most 1, including nonsquarefree moduli. -/
theorem ram_norm_le_one (m : ℕ) [NeZero m] : ‖ram m‖ ≤ 1 := by
  by_cases hs : Squarefree m
  · rw [ram_squarefree m hs, Complex.norm_intCast]
    exact_mod_cast (ArithmeticFunction.abs_moebius_le_one (n := m))
  · rw [ram_eq, principal_gauss_zero_of_not_squarefree hs]
    norm_num

/-- At any multiple of the primitive level, the squared induced Gauss norm is at most that level. -/
theorem induced_gauss_norm_sq_le {r q : ℕ} [NeZero r] [NeZero q]
    (χ : DirichletCharacter ℂ r) (hχ : χ.IsPrimitive) (hrq : r ∣ q) :
    ‖gaussSum (changeLevel hrq χ) stdAddChar‖ ^ 2 ≤ (r : ℝ) := by
  obtain ⟨m, rfl⟩ := hrq
  have hm0 : m ≠ 0 := by
    intro hm
    have h := NeZero.ne (r * m)
    simp [hm] at h
  letI : NeZero m := ⟨hm0⟩
  by_cases hcop : r.Coprime m
  · rw [gaussSum_changeLevel_mul hcop, norm_mul, norm_mul, mul_pow, mul_pow,
      norm_sq_gaussSum_of_isPrimitive hχ]
    have h1 : ‖χ (m : ZMod r)‖ ^ 2 ≤ 1 := by
      have h := χ.norm_le_one (m : ZMod r)
      nlinarith [norm_nonneg (χ (m : ZMod r))]
    have h2 : ‖gaussSum (1 : DirichletCharacter ℂ m) stdAddChar‖ ^ 2 ≤ 1 := by
      have h := ram_norm_le_one m
      rw [ram_eq] at h
      nlinarith [norm_nonneg (gaussSum (1 : DirichletCharacter ℂ m) stdAddChar)]
    calc ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) *
        ‖gaussSum (1 : DirichletCharacter ℂ m) stdAddChar‖ ^ 2
        ≤ 1 * (r : ℝ) * 1 := by gcongr
      _ = _ := by ring
  · have hc : ¬ r.Coprime ((r * m) / r) := by
      simpa [Nat.mul_div_cancel_left _ (NeZero.pos r)] using hcop
    rw [induced_gauss_zero_of_not_coprime _ χ hc, norm_zero, zero_pow (by decide)]
    positivity

/-- The product of two induced Gauss factors is at most the lcm of the primitive levels. -/
theorem induced_pair_bound {r1 r2 q : ℕ} [NeZero r1] [NeZero r2] [NeZero q]
    (χ1 : DirichletCharacter ℂ r1) (χ2 : DirichletCharacter ℂ r2)
    (hχ1 : χ1.IsPrimitive) (hχ2 : χ2.IsPrimitive) (h1 : r1 ∣ q) (h2 : r2 ∣ q) :
    ‖gaussSum (changeLevel h1 χ1) stdAddChar * gaussSum (changeLevel h2 χ2) stdAddChar‖ ≤
      (Nat.lcm r1 r2 : ℝ) := by
  have hb1 := induced_gauss_norm_sq_le χ1 hχ1 h1
  have hb2 := induced_gauss_norm_sq_le χ2 hχ2 h2
  have hl0 : 0 < Nat.lcm r1 r2 := Nat.lcm_pos (NeZero.pos r1) (NeZero.pos r2)
  have hl1 : (r1 : ℝ) ≤ Nat.lcm r1 r2 := by
    exact_mod_cast Nat.le_of_dvd hl0 (Nat.dvd_lcm_left r1 r2)
  have hl2 : (r2 : ℝ) ≤ Nat.lcm r1 r2 := by
    exact_mod_cast Nat.le_of_dvd hl0 (Nat.dvd_lcm_right r1 r2)
  have hsq : ‖gaussSum (changeLevel h1 χ1) stdAddChar * gaussSum (changeLevel h2 χ2) stdAddChar‖ ^ 2
      ≤ (Nat.lcm r1 r2 : ℝ) ^ 2 := by
    rw [norm_mul, mul_pow]
    calc _ ≤ (r1 : ℝ) * r2 := mul_le_mul hb1 hb2 (sq_nonneg _) (by positivity)
      _ ≤ (Nat.lcm r1 r2 : ℝ) ^ 2 := by nlinarith
  have hn := norm_nonneg
    (gaussSum (changeLevel h1 χ1) stdAddChar * gaussSum (changeLevel h2 χ2) stdAddChar)
  have hl : (0 : ℝ) ≤ Nat.lcm r1 r2 := by positivity
  nlinarith

end LeanLab.ExceptionalSet.Lu2010GaussBound

#print axioms LeanLab.ExceptionalSet.Lu2010GaussBound.ram_norm_le_one
#print axioms LeanLab.ExceptionalSet.Lu2010GaussBound.induced_gauss_norm_sq_le
#print axioms LeanLab.ExceptionalSet.Lu2010GaussBound.induced_pair_bound
