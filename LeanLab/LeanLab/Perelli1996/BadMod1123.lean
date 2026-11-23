/-
P0083 Perelli 1996, page 484, displays 19 and 20.
ROUTE BURST S110 burst-20261122 split of Bad1122.leaf_bad_modulus_large.
The zero free region 19, from Prachar Chapter 8 with Siegel's theorem, is the new LEAF;
the step from 19 to 20, that a bad character has modulus q ≫ L^P for every P > 0, is proved here.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Char1122

namespace LeanLab.Perelli1996.BadMod1123
open Real
open LeanLab.Perelli1996.Char1122
noncomputable section

/-- LEAF: Page 484 display 19, by the zero free region of Prachar Chapter 8 and Siegel's
theorem: for every ε' > 0 there is c(ε') > 0 such that L(s,χ) ≠ 0 for every character χ
modulo q and every s ≠ 1 with σ > 1 - c(ε')/max{q^ε', log^(4/5)(|t|+1)}.
Class HARD. Cited inputs: Prachar, Primzahlverteilung, Chapter 8, and Siegel's theorem. -/
theorem leaf_zero_free_region_19 (ε' : ℝ) (hε' : 0 < ε') :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ), s ≠ 1 →
      1 - c / max ((q : ℝ) ^ ε') (Real.log (|s.im| + 1) ^ ((4 : ℝ) / 5)) < s.re →
      DirichletCharacter.LFunction χ s ≠ 0 := by
  sorry

/-- Page 484 display 20 from display 19: a bad character modulo q, for the rectangle 18
with L = log N, forces q ≫_P L^P for every P > 0. The exact statement of
Bad1122.leaf_bad_modulus_large. CONDITIONAL ON the LEAF leaf_zero_free_region_19,
used with ε' = 1/(2P). -/
theorem leaf_bad_modulus_large_of_split1123 (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) (P : ℝ)
    (hP : 0 < P) :
    ∃ c' N₀ : ℝ, 0 < c' ∧ 3 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N →
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), ¬ goodCharacter B ε N χ →
        c' * Real.log N ^ P ≤ q := by
  set A : ℝ := 10 * (B / ε) with hAdef
  have hA : 0 < A := by positivity
  obtain ⟨c, hc, h19⟩ := leaf_zero_free_region_19 (1 / (2 * P)) (by positivity)
  set K : ℝ := 20 * A / c with hKdef
  have hK : 0 < K := by positivity
  refine ⟨(c / (10 * A)) ^ (2 * P), max 3 (Real.exp (K ^ (10 : ℝ) + 1)), by positivity,
    le_max_left _ _, ?_⟩
  intro N hN q _ χ hbad
  have hN3 : (3 : ℝ) ≤ N := (le_max_left _ _).trans hN
  have hNe : Real.exp (K ^ (10 : ℝ) + 1) ≤ N := (le_max_right _ _).trans hN
  have hN0 : 0 < N := by linarith
  set L := Real.log N with hLdef
  have hLK : K ^ (10 : ℝ) + 1 ≤ L := by
    rw [hLdef, ← Real.log_exp (K ^ (10 : ℝ) + 1)]
    exact Real.log_le_log (Real.exp_pos _) hNe
  have hK10 : 0 ≤ K ^ (10 : ℝ) := by positivity
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  -- the zero in the rectangle 18
  unfold goodCharacter at hbad
  push Not at hbad
  obtain ⟨s, hs1, hlow, _hup, him, hzero⟩ := hbad
  set M := max ((q : ℝ) ^ (1 / (2 * P))) (Real.log (|s.im| + 1) ^ ((4 : ℝ) / 5)) with hMdef
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hqa : 1 ≤ (q : ℝ) ^ (1 / (2 * P)) := Real.one_le_rpow hq1 (by positivity)
  have hM1 : 1 ≤ M := hqa.trans (le_max_left _ _)
  have hM0 : 0 < M := by linarith
  have hre : s.re ≤ 1 - c / M := by
    by_contra hcon
    exact h19 q χ s hs1 (lt_of_not_ge hcon) hzero
  -- c / M ≤ A log L / L ≤ 10 A L^(1/10) / L
  have hlogL : Real.log L ≤ L ^ ((1 : ℝ) / 10) / (1 / 10) :=
    Real.log_le_rpow_div hL0.le (by norm_num)
  have hcM : c / M ≤ A * Real.log L / L := by
    have : 1 - A * Real.log L / L ≤ s.re := by
      simpa [hAdef, hLdef, mul_assoc] using hlow
    linarith
  have hsplit : L = L ^ ((1 : ℝ) / 10) * L ^ ((9 : ℝ) / 10) := by
    rw [← Real.rpow_add hL0]; norm_num
  have hL110 : 0 < L ^ ((1 : ℝ) / 10) := Real.rpow_pos_of_pos hL0 _
  have hL910 : 0 < L ^ ((9 : ℝ) / 10) := Real.rpow_pos_of_pos hL0 _
  -- key: c L^(9/10) ≤ 10 A M
  have hkey : c * L ^ ((9 : ℝ) / 10) ≤ 10 * A * M := by
    have h1 : c / M ≤ A * (10 * L ^ ((1 : ℝ) / 10)) / L := by
      refine hcM.trans ?_
      apply div_le_div_of_nonneg_right _ hL0.le
      apply mul_le_mul_of_nonneg_left _ hA.le
      linarith [show L ^ ((1 : ℝ) / 10) / (1 / 10) = 10 * L ^ ((1 : ℝ) / 10) by ring]
    have h2 : A * (10 * L ^ ((1 : ℝ) / 10)) / L = 10 * A / L ^ ((9 : ℝ) / 10) := by
      calc A * (10 * L ^ ((1 : ℝ) / 10)) / L
          = A * (10 * L ^ ((1 : ℝ) / 10)) / (L ^ ((1 : ℝ) / 10) * L ^ ((9 : ℝ) / 10)) := by
            rw [← hsplit]
        _ = 10 * A / L ^ ((9 : ℝ) / 10) := by field_simp
    rw [h2, div_le_div_iff₀ hM0 hL910] at h1
    linarith
  rcases le_total (Real.log (|s.im| + 1) ^ ((4 : ℝ) / 5)) ((q : ℝ) ^ (1 / (2 * P))) with hab | hab
  · -- M = q^(1/(2P)): the Siegel case
    have hMq : M = (q : ℝ) ^ (1 / (2 * P)) := max_eq_left hab
    have hqlow : c / (10 * A) * L ^ ((9 : ℝ) / 10) ≤ (q : ℝ) ^ (1 / (2 * P)) := by
      rw [← hMq, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]; linarith
    have hpow := Real.rpow_le_rpow (by positivity) hqlow (show (0 : ℝ) ≤ 2 * P by positivity)
    rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ (by positivity),
      Real.rpow_one, Real.mul_rpow (by positivity) hL910.le, ← Real.rpow_mul hL0.le] at hpow
    refine le_trans ?_ hpow
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Real.rpow_le_rpow_of_exponent_le hL1
    nlinarith
  · -- M = log^(4/5)(|t|+1) ≤ 2 L^(4/5): impossible for large N
    exfalso
    have hMt : M = Real.log (|s.im| + 1) ^ ((4 : ℝ) / 5) := max_eq_right hab
    have ht0 : 0 ≤ Real.log (|s.im| + 1) := Real.log_nonneg (by linarith [abs_nonneg s.im])
    have hlt : Real.log (|s.im| + 1) ≤ 2 * L := by
      have : |s.im| + 1 ≤ N ^ 2 := by nlinarith
      calc Real.log (|s.im| + 1) ≤ Real.log (N ^ 2) :=
            Real.log_le_log (by positivity) this
        _ = 2 * L := by rw [Real.log_pow, hLdef]; norm_num
    have hMle : M ≤ 2 * L ^ ((4 : ℝ) / 5) := by
      rw [hMt]
      calc Real.log (|s.im| + 1) ^ ((4 : ℝ) / 5) ≤ (2 * L) ^ ((4 : ℝ) / 5) :=
            Real.rpow_le_rpow ht0 hlt (by norm_num)
        _ = 2 ^ ((4 : ℝ) / 5) * L ^ ((4 : ℝ) / 5) := Real.mul_rpow (by norm_num) hL0.le
        _ ≤ 2 * L ^ ((4 : ℝ) / 5) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            calc (2 : ℝ) ^ ((4 : ℝ) / 5) ≤ 2 ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
    have hsplit2 : L ^ ((9 : ℝ) / 10) = L ^ ((1 : ℝ) / 10) * L ^ ((4 : ℝ) / 5) := by
      rw [← Real.rpow_add hL0]; norm_num
    have hL45 : 0 < L ^ ((4 : ℝ) / 5) := Real.rpow_pos_of_pos hL0 _
    have hsmall : L ^ ((1 : ℝ) / 10) ≤ K := by
      have : c * (L ^ ((1 : ℝ) / 10) * L ^ ((4 : ℝ) / 5)) ≤ 20 * A * L ^ ((4 : ℝ) / 5) := by
        rw [← hsplit2]; nlinarith
      have h3 : c * L ^ ((1 : ℝ) / 10) ≤ 20 * A := by
        have := le_of_mul_le_mul_right (a := L ^ ((4 : ℝ) / 5))
          (by linarith : c * L ^ ((1 : ℝ) / 10) * L ^ ((4 : ℝ) / 5) ≤
            20 * A * L ^ ((4 : ℝ) / 5)) hL45
        exact this
      rw [hKdef, le_div_iff₀ hc]; linarith
    have hbig := Real.rpow_le_rpow hL110.le hsmall (show (0 : ℝ) ≤ 10 by norm_num)
    rw [← Real.rpow_mul hL0.le] at hbig
    have e : (1 / 10 : ℝ) * 10 = 1 := by norm_num
    rw [e, Real.rpow_one] at hbig
    linarith

end
end LeanLab.Perelli1996.BadMod1123
