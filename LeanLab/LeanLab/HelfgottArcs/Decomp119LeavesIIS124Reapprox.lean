/-
P0013 page 70, the re-approximation step for the second choice of parameters.
The leaf Decomp119LeavesII.reapprox is FALSE as stated: at x = 2.16e20, with the
original approximation a/q = 1/q, q = 2.7e13 = (3/4) x^{2/3} and δ/x = -1/(q (3/4) x^{2/3}),
the only fraction a'/q' with q' ≤ Q = x^{2/3}/(500 √6) and |2α - a'/q'| ≤ 1/(q'Q) is 0/1,
and then δ' = 2αx = 8y (1 - 1/q) < 8y, so neither (a) q' > y/4 nor (b2) |δ'| q' > 8y holds.
The paper's sentence "since otherwise a/q would already be a valid approximation under
the first choice of parameters" gives only |δ'| q' ≥ 8y after excluding q' ≤ y, and
even that needs uniqueness of the first approximation, which fails when q is close to
x/(8y). The parent typeII_bound and typeI₂_bound are not shown false by this.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.HelfgottArcs.Decomp119LeavesII

namespace LeanLab.HelfgottArcs.Decomp119LeavesIIS124Reapprox
open LeanLab.HelfgottArcs.Decomp119

theorem cbrt_x0 : (2.16e20 : ℝ) ^ ((1 : ℝ) / 3) = 6000000 := by
  have h : (2.16e20 : ℝ) = (6000000 : ℝ) ^ (3 : ℕ) := by norm_num
  rw [h, show (1 : ℝ) / 3 = ((3 : ℕ) : ℝ)⁻¹ by norm_num]
  exact Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)

theorem x0_two_thirds : (2.16e20 : ℝ) ^ ((2 : ℝ) / 3) = 36000000000000 := by
  rw [show (2 : ℝ) / 3 = (1 / 3) * 2 by norm_num, Real.rpow_mul (by norm_num), cbrt_x0,
    Real.rpow_two]
  norm_num

/-- FALSE: the leaf Decomp119LeavesII.reapprox fails at x = 2.16e20, a = 1,
q = 27000000000000, δ = -x/(q · (3/4) x^{2/3}). P0013 page 70. -/
theorem reapprox_false : ¬ ∀ (x α : ℝ) (a : ℤ) (q : ℕ) (δ : ℝ),
    MinorHyp x α a q δ → x ^ ((1 : ℝ) / 3) / 6 < q →
    ∃ a' : ℤ, ∃ q' : ℕ, ∃ δ' : ℝ, 1 ≤ q' ∧ 2 * α = a' / q' + δ' / x ∧ Int.gcd a' q' = 1 ∧
      (q' : ℝ) ≤ x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6) ∧
      |δ' / x| ≤ 1 / (q' * (x ^ ((2 : ℝ) / 3) / (500 * Real.sqrt 6))) ∧
      (x ^ ((1 : ℝ) / 3) / 6 / 4 < q' ∨
        (8 < |δ'| ∧ 8 * (x ^ ((1 : ℝ) / 3) / 6) < |δ'| * q')) := by
  intro H
  set δ0 : ℝ := -((2.16e20 : ℝ) / (27000000000000 * 27000000000000)) with hδ0
  set α0 : ℝ := (1 / 27000000000000 + δ0 / 2.16e20) / 2 with hα0
  have hM : MinorHyp 2.16e20 α0 1 27000000000000 δ0 := by
    unfold MinorHyp
    rw [x0_two_thirds]
    refine ⟨le_refl _, by norm_num, ?_, by norm_num, by norm_num, ?_⟩
    · rw [hα0]; push_cast; ring
    · rw [hδ0]; norm_num [abs_div]
  have hq : (2.16e20 : ℝ) ^ ((1 : ℝ) / 3) / 6 < ((27000000000000 : ℕ) : ℝ) := by
    rw [cbrt_x0]; norm_num
  obtain ⟨a', q', δ', hq1, h2α, hg, hqQ, hδ, hc⟩ := H _ _ _ _ _ hM hq
  rw [x0_two_thirds] at hqQ hδ
  rw [cbrt_x0] at hc
  have hs1 : Real.sqrt 6 < 2.45 := by
    rw [Real.sqrt_lt' (by norm_num)]; norm_num
  have hs2 : 2.44 < Real.sqrt 6 := by
    rw [Real.lt_sqrt (by norm_num)]; norm_num
  set Q : ℝ := 36000000000000 / (500 * Real.sqrt 6) with hQ
  have hQlo : 29000000000 < Q := by
    rw [hQ, lt_div_iff₀ (by positivity)]; nlinarith
  have hQhi : Q < 30000000000 := by
    rw [hQ, div_lt_iff₀ (by positivity)]; nlinarith
  have hq'pos : (0 : ℝ) < q' := by exact_mod_cast hq1
  set c : ℝ := 2 * α0 with hc_def
  have hcval : c = 1 / 27000000000000 - 1 / (27000000000000 * 27000000000000) := by
    rw [hc_def, hα0, hδ0]; ring
  have hkey : δ' / 2.16e20 = c - a' / q' := by linarith
  clear_value c Q
  -- |c q' - a'| * Q ≤ 1
  have hδ2 : |δ' / 2.16e20| * (q' * Q) ≤ 1 := by
    rw [← le_div_iff₀ (by positivity)]; exact hδ
  have habs : |c * q' - a'| * Q ≤ 1 := by
    have : c * q' - a' = (δ' / 2.16e20) * q' := by
      rw [hkey]; field_simp
    rw [this, abs_mul, abs_of_pos hq'pos]
    nlinarith
  have hcpos : 0 < c := by rw [hcval]; norm_num
  have hcq : c * q' < 1 / 500 := by
    have : c * q' ≤ c * Q := mul_le_mul_of_nonneg_left hqQ hcpos.le
    have : c * Q < 1 / 500 := by rw [hcval]; nlinarith
    linarith
  have hsmall : |c * q' - a'| < 1 / 1000 := by
    have h0 : 0 ≤ |c * q' - a'| := abs_nonneg _
    by_contra hh
    push_neg at hh
    have := mul_le_mul_of_nonneg_right hh (le_of_lt (lt_trans (by norm_num) hQlo))
    linarith
  have ha0 : a' = 0 := by
    have h1 : |(a' : ℝ)| < 1 := by
      have := abs_sub_abs_le_abs_sub (c * q') (a' : ℝ)
      have h3 := abs_sub_comm (c * q') (a' : ℝ)
      have h4 : |(a' : ℝ)| ≤ |c * q'| + |c * q' - a'| := by
        have := abs_add_le (c * q') ((a' : ℝ) - c * q')
        rw [show c * q' + ((a' : ℝ) - c * q') = a' by ring] at this
        rw [abs_sub_comm] at this
        linarith
      have h5 : |c * q'| = c * q' := abs_of_pos (by positivity)
      linarith
    have h2 : |a'| < 1 := by exact_mod_cast h1
    exact Int.abs_lt_one_iff.mp h2
  subst ha0
  have hq'1 : q' = 1 := by
    simpa [Int.gcd_zero_left] using hg
  subst hq'1
  have hδ'v : δ' = c * 2.16e20 := by
    have : δ' / 2.16e20 = c := by rw [hkey]; simp
    field_simp at this; linarith
  rcases hc with h | ⟨_, h⟩
  · norm_num at h
  · rw [hδ'v, hcval] at h
    norm_num [abs_of_pos] at h
