import LeanLab.Zhan1991.SPLIT_major_1122

/-!
P0068 Zhan 1991, page 270, the major arcs `I(q, a)` with `q ≤ Q₁ = L^d` and half width
`Q⁻¹ = L⁴/U` are pairwise separated for large `N`: distinct fractions differ by at least
`1/(qq') ≥ L^{-2d}`, which exceeds `2 L⁴/U` once `U = N^{5/8} L^c` is large. PROVED. This is the
disjointness ingredient of step 2 of SPLIT_major_1122, `majorAssembly_of_approx`; that LEAF stays
open. burst-20261122, session S80.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991
open Real Filter Asymptotics

/-- Page 270, the major arcs are separated: two distinct centres `a/q ≠ a'/q'` with
`q, q' ≤ L^d` are more than twice the half width `L⁴/U` apart, for large `N`. PROVED. -/
theorem majorArcs_separated (d c : ℝ) (hd : 0 < d) (hc : 0 ≤ c) :
    ∃ N₀ : ℝ, ∀ N : ℕ, N₀ ≤ N → ∀ (q q' : ℕ) (a a' : ℤ), 1 ≤ q →
      (q : ℝ) ≤ Real.log N ^ d → 1 ≤ q' → (q' : ℝ) ≤ Real.log N ^ d →
      (a : ℝ) / q ≠ (a' : ℝ) / q' →
      2 * (Real.log N ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c)) <
        |(a : ℝ) / q - (a' : ℝ) / q'| := by
  have h := (isLittleO_log_rpow_rpow_atTop (4 + 2 * d) (by norm_num : (0 : ℝ) < 5 / 8)).bound
    (by norm_num : (0 : ℝ) < 1 / 4)
  obtain ⟨X0, hX0⟩ := eventually_atTop.mp (h.and (eventually_ge_atTop (Real.exp 1)))
  refine ⟨X0, fun N hN q q' a a' hq hqL hq' hqL' hne => ?_⟩
  obtain ⟨hb, he⟩ := hX0 N hN
  have hN0 : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos 1) he
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) he
  set L := Real.log N with hLdef
  have hLpos : 0 < L := by linarith
  have hP : 0 < (N : ℝ) ^ (5 / 8 : ℝ) := Real.rpow_pos_of_pos hN0 _
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hLpos.le _),
    abs_of_nonneg hP.le] at hb
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hq0' : (0 : ℝ) < q' := by exact_mod_cast hq'
  -- separation of distinct fractions
  have hsep : 1 / ((q : ℝ) * q') ≤ |(a : ℝ) / q - (a' : ℝ) / q'| := by
    have hz : (a * q' - a' * q : ℤ) ≠ 0 := by
      intro h0
      apply hne
      have : (a : ℝ) * q' = (a' : ℝ) * q := by exact_mod_cast sub_eq_zero.mp h0
      field_simp
      linarith
    have h1 : (1 : ℝ) ≤ |((a * q' - a' * q : ℤ) : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast Int.one_le_abs hz
    have e : (a : ℝ) / q - (a' : ℝ) / q' = ((a * q' - a' * q : ℤ) : ℝ) / (q * q') := by
      push_cast; field_simp
    rw [e, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * q')]
    exact div_le_div_of_nonneg_right h1 (by positivity)
  have hqq : (q : ℝ) * q' ≤ L ^ (2 * d) := by
    rw [show 2 * d = d + d by ring, Real.rpow_add hLpos]
    exact mul_le_mul hqL hqL' hq0'.le (Real.rpow_nonneg hLpos.le _)
  have hLc : 1 ≤ L ^ c := Real.one_le_rpow hL1 hc
  have hL2d : 0 < L ^ (2 * d) := Real.rpow_pos_of_pos hLpos _
  have hsum : L ^ (4 : ℝ) * L ^ (2 * d) = L ^ (4 + 2 * d) := by rw [← Real.rpow_add hLpos]
  have key : 2 * (L ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * L ^ c)) < 1 / L ^ (2 * d) := by
    rw [← mul_div_assoc, div_lt_div_iff₀ (by positivity) hL2d]
    have hc1 : (N : ℝ) ^ (5 / 8 : ℝ) ≤ (N : ℝ) ^ (5 / 8 : ℝ) * L ^ c :=
      le_mul_of_one_le_right hP.le hLc
    nlinarith
  calc 2 * (L ^ (4 : ℝ) / ((N : ℝ) ^ (5 / 8 : ℝ) * L ^ c)) < 1 / L ^ (2 * d) := key
    _ ≤ 1 / ((q : ℝ) * q') := one_div_le_one_div_of_le (by positivity) hqq
    _ ≤ _ := hsep

end LeanLab.Zhan1991
