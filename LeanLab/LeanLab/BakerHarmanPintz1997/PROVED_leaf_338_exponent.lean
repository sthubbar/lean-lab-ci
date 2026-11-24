/-
PROVED leaf `leaf_338_exponent` of the split `SPLIT_lemma10_small_L_338`, P0069 page 24, the
exponent count under (3.38). The statement is restated verbatim as `leaf_338_exponent_proof`.
Route: with P = abs A0, q <= L^P, qT <= L^P x^(0.45 - 2 eps/3), a = max(M, x^0.45),
b = max(N, x^0.225), qT + M <= 2 L^P a and qT + N^2 <= 2 L^P b^2, so the product of the three
factors is L^(B1+B2+B3) times the fourth root of a quantity at most 8 L^(4P) (ab)^2 x^(0.45 - 2 eps/3)
<= 8 L^(4P) x^(2 - 5 eps/12), and L^(B1+B2+B3+P+A) <= x^(5 eps/48) for large x.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.SPLIT_lemma10_small_L_338

namespace LeanLab.BakerHarmanPintz1997
open Finset
open scoped Real

/-- Powers of the logarithm are eventually below any positive power of x. -/
theorem leaf338exp_log_rpow_le (p δ : ℝ) (hδ : 0 < δ) :
    ∃ X0 : ℝ, ∀ x, X0 ≤ x → Real.log x ^ p ≤ x ^ δ := by
  have h := (isLittleO_log_rpow_rpow_atTop p hδ).bound (show (0:ℝ) < 1 by norm_num)
  obtain ⟨X0, hX⟩ := Filter.eventually_atTop.1 (h.and (Filter.eventually_ge_atTop (1:ℝ)))
  refine ⟨X0, fun x hx => ?_⟩
  obtain ⟨h1, h2⟩ := hX x hx
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs] at h1
  exact (le_abs_self _).trans (h1.trans (abs_of_nonneg (Real.rpow_nonneg (by linarith) _)).le)

/-- For nonnegative u, v, w: u^(1/2) v^(1/4) w^(1/4) = (u^2 v w)^(1/4). -/
theorem leaf338exp_root_combine (u v w : ℝ) (hu : 0 ≤ u) (hv : 0 ≤ v) (hw : 0 ≤ w) :
    u ^ (1 / 2 : ℝ) * v ^ (1 / 4 : ℝ) * w ^ (1 / 4 : ℝ) = (u ^ 2 * v * w) ^ (1 / 4 : ℝ) := by
  rw [Real.mul_rpow (by positivity) hw, Real.mul_rpow (by positivity) hv]
  congr 2
  rw [← Real.rpow_natCast, ← Real.rpow_mul hu]
  norm_num

/-- PROVED: `leaf_338_exponent` of `SPLIT_lemma10_small_L_338`, statement verbatim, P0069 page 24,
the exponent count under (3.38) and T <= T1, with C = 8^(1/4). -/
theorem leaf_338_exponent_proof :
  ∀ ε : ℝ, 0 < ε → ε < 1 / 100 →
  ∀ (A0 : ℝ) (Ml Nl : ℝ → ℝ) (𝒮 : ℝ → Set Cfg),
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ c.T ≤ T1 ε x) →
    (∀ x, ∀ c ∈ 𝒮 x, max (Ml x) (x ^ (0.45 : ℝ)) * max (Nl x) (x ^ (0.225 : ℝ)) ≤ x ^ (0.775 + ε / 8)) →
    ∀ B1 B2 B3 A : ℝ, 0 < A → ∃ C X0 : ℝ, 0 ≤ C ∧ ∀ x, X0 ≤ x → ∀ c ∈ 𝒮 x,
      (L x ^ B1 * (c.q * c.T + max (Ml x) 0) ^ (1 / 2 : ℝ)) *
        (L x ^ B2 * (c.q * c.T + max (Nl x) 0 ^ 2) ^ (1 / 4 : ℝ)) *
        (L x ^ B3 * (c.q * c.T) ^ (1 / 4 : ℝ)) ≤ C * x ^ (1 / 2 : ℝ) / L x ^ A := by
  intro ε hε _hε1 A0 Ml Nl 𝒮 hcase h338 B1 B2 B3 A _hA
  set P : ℝ := |A0| with hP
  obtain ⟨X1, hX1⟩ := leaf338exp_log_rpow_le (B1 + B2 + B3 + P + A) (5 * ε / 48) (by positivity)
  refine ⟨(8 : ℝ) ^ (1 / 4 : ℝ), max X1 (Real.exp 1), by positivity, ?_⟩
  intro x hx c hc
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hx0 : 0 < x := lt_of_lt_of_le (Real.exp_pos 1) hxe
  have hL1 : 1 ≤ L x := by
    show 1 ≤ Real.log x
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos 1) hxe
  have hL0 : 0 < L x := by linarith
  obtain ⟨hstd, hq, hT⟩ := hcase x c hc
  obtain ⟨_, hq1, _, hT2, _⟩ := hstd
  have hq0 : (0 : ℝ) ≤ c.q := by positivity
  have hT0 : 0 ≤ c.T := by linarith
  have hqP : (c.q : ℝ) ≤ L x ^ P :=
    hq.trans (Real.rpow_le_rpow_of_exponent_le hL1 (le_abs_self A0))
  have hLP1 : 1 ≤ L x ^ P := Real.one_le_rpow hL1 (abs_nonneg _)
  set y : ℝ := x ^ (0.45 - 2 * ε / 3 : ℝ) with hy
  have hyx : y ≤ x ^ (0.45 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith [Real.add_one_le_exp (1:ℝ)]) (by linarith)
  have hqT : (c.q : ℝ) * c.T ≤ L x ^ P * y :=
    mul_le_mul hqP hT hT0 (by positivity)
  have hqT0 : 0 ≤ (c.q : ℝ) * c.T := mul_nonneg hq0 hT0
  set a := max (Ml x) (x ^ (0.45 : ℝ)) with ha
  set b := max (Nl x) (x ^ (0.225 : ℝ)) with hb
  have ha1 : x ^ (0.45 : ℝ) ≤ a := le_max_right _ _
  have hb1 : x ^ (0.225 : ℝ) ≤ b := le_max_right _ _
  have hx45 : 0 < x ^ (0.45 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hx225 : 0 < x ^ (0.225 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have ha0 : 0 ≤ a := by linarith
  have hb0 : 0 ≤ b := by linarith
  have hMa : max (Ml x) 0 ≤ a := max_le (le_max_left _ _) ha0
  have hNb : max (Nl x) 0 ≤ b := max_le (le_max_left _ _) hb0
  have hb2 : x ^ (0.45 : ℝ) ≤ b ^ 2 := by
    have : x ^ (0.45 : ℝ) = (x ^ (0.225 : ℝ)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]; norm_num
    rw [this]; exact pow_le_pow_left₀ hx225.le hb1 2
  have hU : (c.q : ℝ) * c.T + max (Ml x) 0 ≤ 2 * L x ^ P * a := by
    have h1 : L x ^ P * y ≤ L x ^ P * a :=
      mul_le_mul_of_nonneg_left (hyx.trans ha1) (by positivity)
    have h2 : a ≤ L x ^ P * a := le_mul_of_one_le_left ha0 hLP1
    linarith
  have hV : (c.q : ℝ) * c.T + max (Nl x) 0 ^ 2 ≤ 2 * L x ^ P * b ^ 2 := by
    have h1 : L x ^ P * y ≤ L x ^ P * b ^ 2 :=
      mul_le_mul_of_nonneg_left (hyx.trans hb2) (by positivity)
    have h2 : b ^ 2 ≤ L x ^ P * b ^ 2 := le_mul_of_one_le_left (by positivity) hLP1
    have h3 : max (Nl x) 0 ^ 2 ≤ b ^ 2 := pow_le_pow_left₀ (le_max_right _ _) hNb 2
    linarith
  have hU0 : 0 ≤ (c.q : ℝ) * c.T + max (Ml x) 0 := by positivity
  have hV0 : 0 ≤ (c.q : ℝ) * c.T + max (Nl x) 0 ^ 2 := by positivity
  have hab : a * b ≤ x ^ (0.775 + ε / 8) := h338 x c hc
  -- the fourth power quantity
  have hprod : ((c.q : ℝ) * c.T + max (Ml x) 0) ^ 2 * ((c.q : ℝ) * c.T + max (Nl x) 0 ^ 2) *
      ((c.q : ℝ) * c.T) ≤ 8 * (L x ^ P) ^ 4 * x ^ (2 - 5 * ε / 12 : ℝ) := by
    have e1 : ((c.q : ℝ) * c.T + max (Ml x) 0) ^ 2 * ((c.q : ℝ) * c.T + max (Nl x) 0 ^ 2) *
        ((c.q : ℝ) * c.T) ≤ (2 * L x ^ P * a) ^ 2 * (2 * L x ^ P * b ^ 2) * (L x ^ P * y) := by
      gcongr
    have e2 : (2 * L x ^ P * a) ^ 2 * (2 * L x ^ P * b ^ 2) * (L x ^ P * y)
        = 8 * (L x ^ P) ^ 4 * ((a * b) ^ 2 * y) := by ring
    have e3 : (a * b) ^ 2 * y ≤ (x ^ (0.775 + ε / 8)) ^ 2 * y := by
      gcongr
    have e4 : (x ^ (0.775 + ε / 8)) ^ 2 * y = x ^ (2 - 5 * ε / 12 : ℝ) := by
      rw [hy, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, ← Real.rpow_add hx0]
      congr 1; push_cast; ring
    rw [e2] at e1
    calc _ ≤ _ := e1
      _ ≤ 8 * (L x ^ P) ^ 4 * x ^ (2 - 5 * ε / 12 : ℝ) := by
        rw [← e4]; gcongr
  have hroot : (8 * (L x ^ P) ^ 4 * x ^ (2 - 5 * ε / 12 : ℝ)) ^ (1 / 4 : ℝ)
      = (8 : ℝ) ^ (1 / 4 : ℝ) * L x ^ P * x ^ (1 / 2 - 5 * ε / 48 : ℝ) := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.mul_rpow (by positivity) (by positivity),
      ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul hx0.le]
    congr 2
    · push_cast; ring_nf
    · ring
  have hlog : L x ^ (B1 + B2 + B3 + P + A) ≤ x ^ (5 * ε / 48) := hX1 x (le_trans (le_max_left _ _) hx)
  have hLHS : (L x ^ B1 * ((c.q : ℝ) * c.T + max (Ml x) 0) ^ (1 / 2 : ℝ)) *
        (L x ^ B2 * ((c.q : ℝ) * c.T + max (Nl x) 0 ^ 2) ^ (1 / 4 : ℝ)) *
        (L x ^ B3 * ((c.q : ℝ) * c.T) ^ (1 / 4 : ℝ))
      = L x ^ (B1 + B2 + B3) * (((c.q : ℝ) * c.T + max (Ml x) 0) ^ 2 *
          ((c.q : ℝ) * c.T + max (Nl x) 0 ^ 2) * ((c.q : ℝ) * c.T)) ^ (1 / 4 : ℝ) := by
    rw [← leaf338exp_root_combine _ _ _ hU0 hV0 hqT0, Real.rpow_add hL0, Real.rpow_add hL0]
    ring
  rw [hLHS, le_div_iff₀ (Real.rpow_pos_of_pos hL0 A)]
  calc L x ^ (B1 + B2 + B3) * (((c.q : ℝ) * c.T + max (Ml x) 0) ^ 2 *
          ((c.q : ℝ) * c.T + max (Nl x) 0 ^ 2) * ((c.q : ℝ) * c.T)) ^ (1 / 4 : ℝ) * L x ^ A
      ≤ L x ^ (B1 + B2 + B3) * (8 * (L x ^ P) ^ 4 * x ^ (2 - 5 * ε / 12 : ℝ)) ^ (1 / 4 : ℝ)
          * L x ^ A := by
        gcongr
    _ = (8 : ℝ) ^ (1 / 4 : ℝ) * L x ^ (B1 + B2 + B3 + P + A) * x ^ (1 / 2 - 5 * ε / 48 : ℝ) := by
        rw [hroot]; simp only [Real.rpow_add hL0]
        ring
    _ ≤ (8 : ℝ) ^ (1 / 4 : ℝ) * x ^ (5 * ε / 48) * x ^ (1 / 2 - 5 * ε / 48 : ℝ) := by
        gcongr
    _ = (8 : ℝ) ^ (1 / 4 : ℝ) * x ^ (1 / 2 : ℝ) := by
        rw [mul_assoc, ← Real.rpow_add hx0]; congr 2; ring

end LeanLab.BakerHarmanPintz1997
