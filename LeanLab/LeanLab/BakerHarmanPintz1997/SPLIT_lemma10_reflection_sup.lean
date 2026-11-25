/-
Split of `lemma10_reflection_sup` in LeanLab.BakerHarmanPintz1997.DecompJ381 into leaves.
P0069 page 24, the reflection step in the case L > qT, reference 24 eq. (21), with the polar
term of the principal character that the print omits. The sealed statement is unchanged and
is restated verbatim in `lemma10_reflection_sup_split`.

The split follows the two mechanisms of the bound.
Leaf 1, nonprincipal characters: partial summation from the cited Fujii, Gallagher and
Montgomery bound `DecompJ883.fgm_bound` over the block c1 F to c2 F, with qT below F, gives
O(log F) and no main term. HARD.
Leaf 2, the principal character: the same partial summation leaves the main term
phi(q)/q times the integral of y^(-1/2-it) over c1 F to c2 F, with an error O(log F). HARD.
Leaf 3, the size of that main term: at most K F^(1/2)/(1 + |t|), by the explicit
antiderivative y^(1/2-it)/(1/2-it) and the trivial bound. MEDIUM.
The assembly is a triangle inequality. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.DecompJ381

namespace LeanLab.BakerHarmanPintz1997
open Finset
open scoped Real

/-- LEAF: page 24, nonprincipal case of the reflection step, partial summation from the cited
FGM bound reference 6 Theorem 1, `DecompJ883.fgm_bound`, on the block c1 F to c2 F. HARD.
For qT below F the FGM error q^(1/2) T^(1/2) log(qT) times F^(-1/2) is O(log F).
Non-vacuity: any modulus q at least 2 with a nonprincipal character, T = 3 and F large. -/
theorem leaf_reflection_nonprincipal :
  ∀ c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ K : ℝ, 0 ≤ K ∧
  ∀ (F : ℝ) (c : Cfg), 2 ≤ F → 1 ≤ c.q → 2 < c.T → (c.q : ℝ) * c.T < F →
    ∀ e ∈ c.S, |e.1| ≤ c.T →
      e.2 ≠ 1 → ‖(longDP c1 c2 F).eval e.2 (half e.1)‖ ≤ K * Real.log F := by
  sorry

/-- LEAF: page 24, principal case of the reflection step: the long sum minus its polar main
term phi(q)/q times the integral of y^(-1/2-it) over c1 F to c2 F is O(log F), by partial
summation from `DecompJ883.fgm_bound` at the principal character. HARD.
Non-vacuity: q = 1, the trivial character, T = 3 and F large. -/
theorem leaf_reflection_principal_error :
  ∀ c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ K : ℝ, 0 ≤ K ∧
  ∀ (F : ℝ) (c : Cfg), 2 ≤ F → 1 ≤ c.q → 2 < c.T → (c.q : ℝ) * c.T < F →
    ∀ e ∈ c.S, |e.1| ≤ c.T →
      e.2 = 1 → ‖(longDP c1 c2 F).eval e.2 (half e.1) -
        ((Nat.totient c.q : ℂ) / (c.q : ℂ)) *
          ∫ y in (c1 * F)..(c2 * F), ((y : ℂ) ^ (-(half e.1)))‖ ≤ K * Real.log F := by
  sorry

/-- LEAF: page 24, the polar main term is at most K F^(1/2)/(1 + |t|). MEDIUM.
The integral equals the difference of y^(1/2-it)/(1/2-it) at the two ends, of size at most
2 (c2 F)^(1/2)/|1/2 - it|, and |1/2 - it| is at least (1 + |t|)/3; phi(q)/q is at most 1.
Non-vacuity: an explicit bound for every real t and every F at least 2. -/
theorem leaf_reflection_polar_size :
  ∀ c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ K : ℝ, 0 ≤ K ∧
  ∀ (F : ℝ) (q : ℕ), 2 ≤ F → 1 ≤ q → ∀ t : ℝ,
    ‖((Nat.totient q : ℂ) / (q : ℂ)) *
        ∫ y in (c1 * F)..(c2 * F), ((y : ℂ) ^ (-(half t)))‖ ≤
      K * (F ^ (1 / 2 : ℝ) / (1 + |t|)) := by
  intro c1 c2 hc1 hc2
  refine ⟨3 * (c2 ^ (1 / 2 : ℝ) + c1 ^ (1 / 2 : ℝ)), ?_, ?_⟩
  · have := Real.rpow_nonneg hc1.le (1 / 2 : ℝ)
    have := Real.rpow_nonneg (hc1.trans hc2).le (1 / 2 : ℝ)
    linarith
  intro F q hF hq t
  have hF0 : 0 < F := by linarith
  have hc20 : 0 < c2 := hc1.trans hc2
  set r : ℂ := -(half t) with hr
  have hr1 : r + 1 = 1 / 2 - t * Complex.I := by rw [hr, half]; ring
  have hre : (r + 1).re = 1 / 2 := by rw [hr1]; simp
  have him : (r + 1).im = -t := by rw [hr1]; simp
  have hrre : -1 < r.re := by
    have : r.re = (r + 1).re - 1 := by simp
    rw [this, hre]; norm_num
  have hn1 : (1 / 2 : ℝ) ≤ ‖r + 1‖ := by
    have := Complex.abs_re_le_norm (r + 1); rw [hre] at this
    linarith [le_abs_self (1 / 2 : ℝ)]
  have hn2 : |t| ≤ ‖r + 1‖ := by
    have := Complex.abs_im_le_norm (r + 1); rwa [him, abs_neg] at this
  have hnpos : 0 < ‖r + 1‖ := by linarith
  have hnorm : (1 + |t|) / 3 ≤ ‖r + 1‖ := by linarith
  -- phi(q)/q has norm at most 1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hphi : ‖((Nat.totient q : ℂ) / (q : ℂ))‖ ≤ 1 := by
    rw [norm_div, Complex.norm_natCast, Complex.norm_natCast, div_le_one hq0]
    exact_mod_cast Nat.totient_le q
  rw [integral_cpow (Or.inl hrre), norm_mul]
  have hb : ‖((c2 * F : ℝ) : ℂ) ^ (r + 1)‖ = c2 ^ (1 / 2 : ℝ) * F ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), hre,
      Real.mul_rpow hc20.le hF0.le]
  have ha : ‖((c1 * F : ℝ) : ℂ) ^ (r + 1)‖ = c1 ^ (1 / 2 : ℝ) * F ^ (1 / 2 : ℝ) := by
    rw [Complex.norm_cpow_eq_rpow_re_of_pos (by positivity), hre,
      Real.mul_rpow hc1.le hF0.le]
  have hdiff : ‖((((c2 * F : ℝ) : ℂ) ^ (r + 1) - ((c1 * F : ℝ) : ℂ) ^ (r + 1)) / (r + 1))‖ ≤
      (c2 ^ (1 / 2 : ℝ) + c1 ^ (1 / 2 : ℝ)) * F ^ (1 / 2 : ℝ) / ((1 + |t|) / 3) := by
    rw [norm_div]
    have hnum := norm_sub_le (((c2 * F : ℝ) : ℂ) ^ (r + 1)) (((c1 * F : ℝ) : ℂ) ^ (r + 1))
    rw [hb, ha] at hnum
    have h0 : 0 < (1 + |t|) / 3 := by positivity
    calc _ ≤ (c2 ^ (1 / 2 : ℝ) * F ^ (1 / 2 : ℝ) + c1 ^ (1 / 2 : ℝ) * F ^ (1 / 2 : ℝ)) /
          ‖r + 1‖ := div_le_div_of_nonneg_right hnum hnpos.le
      _ ≤ (c2 ^ (1 / 2 : ℝ) * F ^ (1 / 2 : ℝ) + c1 ^ (1 / 2 : ℝ) * F ^ (1 / 2 : ℝ)) /
          ((1 + |t|) / 3) := div_le_div_of_nonneg_left (by positivity) h0 hnorm
      _ = _ := by ring
  calc _ ≤ 1 * ((c2 ^ (1 / 2 : ℝ) + c1 ^ (1 / 2 : ℝ)) * F ^ (1 / 2 : ℝ) / ((1 + |t|) / 3)) :=
        mul_le_mul hphi hdiff (norm_nonneg _) zero_le_one
    _ = 3 * (c2 ^ (1 / 2 : ℝ) + c1 ^ (1 / 2 : ℝ)) * (F ^ (1 / 2 : ℝ) / (1 + |t|)) := by
        have : 0 < 1 + |t| := by positivity
        field_simp

/-- `lemma10_reflection_sup`, verbatim. CONDITIONAL ON `leaf_reflection_nonprincipal`,
`leaf_reflection_principal_error` and `leaf_reflection_polar_size`. -/
theorem lemma10_reflection_sup_split :
  ∀ c1 c2 : ℝ, 0 < c1 → c1 < c2 → ∃ K : ℝ, 0 ≤ K ∧
  ∀ (F : ℝ) (c : Cfg), 2 ≤ F → 1 ≤ c.q → 2 < c.T → (c.q : ℝ) * c.T < F →
    ∀ e ∈ c.S, |e.1| ≤ c.T →
      (e.2 ≠ 1 → ‖(longDP c1 c2 F).eval e.2 (half e.1)‖ ≤ K * Real.log F) ∧
      (e.2 = 1 → ‖(longDP c1 c2 F).eval e.2 (half e.1)‖ ≤
        K * (Real.log F + F ^ (1 / 2 : ℝ) / (1 + |e.1|))) := by
  intro c1 c2 hc1 hc2
  obtain ⟨K1, hK1, h1⟩ := leaf_reflection_nonprincipal c1 c2 hc1 hc2
  obtain ⟨K2, hK2, h2⟩ := leaf_reflection_principal_error c1 c2 hc1 hc2
  obtain ⟨K3, hK3, h3⟩ := leaf_reflection_polar_size c1 c2 hc1 hc2
  refine ⟨K1 + K2 + K3, by positivity, ?_⟩
  intro F c hF hq hT hqT e he het
  have hlog : 0 ≤ Real.log F := Real.log_nonneg (by linarith)
  have hP : 0 ≤ F ^ (1 / 2 : ℝ) / (1 + |e.1|) := by positivity
  refine ⟨fun hne => ?_, fun heq => ?_⟩
  · have := h1 F c hF hq hT hqT e he het hne
    nlinarith
  · have hE := h2 F c hF hq hT hqT e he het heq
    have hM := h3 F c.q hF hq e.1
    set I : ℂ := ((Nat.totient c.q : ℂ) / (c.q : ℂ)) *
      ∫ y in (c1 * F)..(c2 * F), ((y : ℂ) ^ (-(half e.1)))
    have htri : ‖(longDP c1 c2 F).eval e.2 (half e.1)‖ ≤
        ‖(longDP c1 c2 F).eval e.2 (half e.1) - I‖ + ‖I‖ := by
      have := norm_add_le ((longDP c1 c2 F).eval e.2 (half e.1) - I) I
      rwa [sub_add_cancel] at this
    nlinarith

#print axioms leaf_reflection_polar_size
#print axioms lemma10_reflection_sup_split

end LeanLab.BakerHarmanPintz1997
