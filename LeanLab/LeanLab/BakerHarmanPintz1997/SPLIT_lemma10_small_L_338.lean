/-
Split of `lemma10_small_L_338` in LeanLab.BakerHarmanPintz1997.DecompJ381 into leaves.
P0069 page 24, proof of Lemma 10, the case L <= qT under (3.38). The sealed statement is
unchanged and is restated verbatim in `lemma10_small_L_338_split`.

The paper writes ||MNL||_1 <= ||M||_2 ||N||_4 ||L||_4, bounds ||L||_4 by Lemma 9 and the other two
norms by Lemma 1, the second applied to N^2, then counts exponents with (3.37) and (3.38).
Step 1, Hoelder with exponents 2, 4, 4 on the finite set S, PROVED here as `leaf_338_holder`.
Leaf 2, ||M||_2 << L^B (qT + M)^(1/2), Lemma 1 with (3.1). HARD.
Leaf 3, ||N||_4 << L^B (qT + N^2)^(1/4), Lemma 1 for N^2 with (3.1). HARD.
Leaf 4, ||L||_4 << L^B (qT)^(1/4) for L <= qT, from Lemma 9 through the proved
`Reflection425.interval_fourth_moment_of_lemma9` and `Reflection425.principal_polar_fourth_sum_le`,
and the count |S| << qT of a well spaced set. MEDIUM, CONDITIONAL ON the cited Lemma 9.
Leaf 5, the exponent count from T <= T1 and (3.38). MEDIUM.
Leaf 4 is reused by the split of `lemma10_small_L_339`.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.DecompJ381
import LeanLab.BakerHarmanPintz1997.SPLIT_leaf_long_fourth_moment_p3

namespace LeanLab.BakerHarmanPintz1997
open Finset
open scoped Real

/-- A sampled norm is nonnegative. Proved, used by the assembly below. -/
theorem split338_pnorm_nonneg (P : DP) (c : Cfg) (p : ℝ) : 0 ≤ pnorm P c p :=
  Real.rpow_nonneg (sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _

/-- PROVED, formerly planned as a leaf: page 24, the Hoelder step
||MNL||_1 <= ||M||_2 ||N||_4 ||L||_4 on the finite set S, exponents 1/2 + 1/4 + 1/4 = 1,
by Cauchy Schwarz twice.
Non-vacuity: holds for every triple of Dirichlet polynomials and every configuration. -/
theorem leaf_338_holder :
  ∀ (M N P : DP) (c : Cfg), norm1prod [M, N, P] c ≤ pnorm M c 2 * pnorm N c 4 * pnorm P c 4 := by
  intro M N P c
  set a : ℝ × DirichletCharacter ℂ c.q → ℝ := fun e => ‖M.eval e.2 (half e.1)‖ with ha
  set b : ℝ × DirichletCharacter ℂ c.q → ℝ := fun e => ‖N.eval e.2 (half e.1)‖ with hb
  set d : ℝ × DirichletCharacter ℂ c.q → ℝ := fun e => ‖P.eval e.2 (half e.1)‖ with hd
  have hnorm : norm1prod [M, N, P] c = ∑ e ∈ c.S, a e * (b e * d e) := by
    simp [norm1prod, ha, hb, hd]
  have hq4 : ∀ X : ℝ, 0 ≤ X → X ^ (1 / 4 : ℝ) = Real.sqrt (Real.sqrt X) := by
    intro X hX
    rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hX]
    norm_num
  have hpM : pnorm M c 2 = Real.sqrt (∑ e ∈ c.S, a e ^ 2) := by
    simp only [pnorm, Real.sqrt_eq_rpow, ha]
    norm_num only [Real.rpow_ofNat]
  have hpN : pnorm N c 4 = Real.sqrt (Real.sqrt (∑ e ∈ c.S, b e ^ 4)) := by
    rw [← hq4 _ (sum_nonneg fun _ _ => by positivity)]
    simp only [pnorm, hb]
    norm_num only [Real.rpow_ofNat]
  have hpP : pnorm P c 4 = Real.sqrt (Real.sqrt (∑ e ∈ c.S, d e ^ 4)) := by
    rw [← hq4 _ (sum_nonneg fun _ _ => by positivity)]
    simp only [pnorm, hd]
    norm_num only [Real.rpow_ofNat]
  have h1 := Real.sum_mul_le_sqrt_mul_sqrt c.S a (fun e => b e * d e)
  have h2 := Real.sum_mul_le_sqrt_mul_sqrt c.S (fun e => b e ^ 2) (fun e => d e ^ 2)
  have h2' : ∑ e ∈ c.S, (b e * d e) ^ 2 ≤
      Real.sqrt (∑ e ∈ c.S, b e ^ 4) * Real.sqrt (∑ e ∈ c.S, d e ^ 4) := by
    have hh : ∀ e, (b e * d e) ^ 2 = b e ^ 2 * d e ^ 2 := fun e => by ring
    have hh2 : ∀ e, (b e ^ 2) ^ 2 = b e ^ 4 := fun e => by ring
    have hh3 : ∀ e, (d e ^ 2) ^ 2 = d e ^ 4 := fun e => by ring
    simp only [hh, hh2, hh3] at h2 ⊢
    exact h2
  have h3 : Real.sqrt (∑ e ∈ c.S, (b e * d e) ^ 2) ≤
      Real.sqrt (Real.sqrt (∑ e ∈ c.S, b e ^ 4)) * Real.sqrt (Real.sqrt (∑ e ∈ c.S, d e ^ 4)) := by
    rw [← Real.sqrt_mul (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt h2'
  rw [hnorm, hpM, hpN, hpP, mul_assoc]
  exact h1.trans (mul_le_mul_of_nonneg_left h3 (Real.sqrt_nonneg _))

/-- LEAF: page 24, ||M||_2 << L^B' (qT + M)^(1/2), by Lemma 1, (3.3), with (3.1) giving
G(M) << L^B''. HARD, it rests on the cited Lemma 1 and a divisor sum bound. Under (3.38)
M <= x^(0.55 + eps/8), so log M << L. If M <= 0 the support is empty and the norm is 0.
Non-vacuity: M of length x^(0.5), N of length x^(0.2), q = 1, T = x^(0.1). -/
theorem leaf_338_mean_M :
  ∀ ε : ℝ, 0 < ε → ε < 1 / 100 →
  ∀ (A0 B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0) →
    (∀ x, ∀ c ∈ 𝒮 x, max (Ml x) (x ^ (0.45 : ℝ)) * max (Nl x) (x ^ (0.225 : ℝ)) ≤ x ^ (0.775 + ε / 8)) →
    ∃ B' K X0 : ℝ, 0 ≤ K ∧ ∀ x, X0 ≤ x → ∀ c ∈ 𝒮 x,
      pnorm (M x) c 2 ≤ K * (L x ^ B' * (c.q * c.T + max (Ml x) 0) ^ (1 / 2 : ℝ)) := by
  sorry

/-- LEAF: page 24, ||N||_4 = ||N^2||_2^(1/2) << L^B' (qT + N^2)^(1/4), by Lemma 1, (3.3), for the
polynomial N^2 of length N^2, whose coefficients satisfy (3.1) with a larger B. HARD. Under (3.38)
N <= x^(0.325 + eps/8). If N <= 0 the support is empty and the norm is 0.
Non-vacuity: as for `leaf_338_mean_M`. -/
theorem leaf_338_fourth_N :
  ∀ ε : ℝ, 0 < ε → ε < 1 / 100 →
  ∀ (A0 B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0) →
    (∀ x, ∀ c ∈ 𝒮 x, max (Ml x) (x ^ (0.45 : ℝ)) * max (Nl x) (x ^ (0.225 : ℝ)) ≤ x ^ (0.775 + ε / 8)) →
    ∃ B' K X0 : ℝ, 0 ≤ K ∧ ∀ x, X0 ≤ x → ∀ c ∈ 𝒮 x,
      pnorm (N x) c 4 ≤ K * (L x ^ B' * (c.q * c.T + max (Nl x) 0 ^ 2) ^ (1 / 4 : ℝ)) := by
  sorry

/-- LEAF: page 24, ||L||_4^4 << L^B' qT when L <= qT, the paper's ||L||_4^4 << L^(3A) qT, from
Lemma 9 for the interval L, the principal height condition |t| >= T/2 and |S| << qT. MEDIUM,
CONDITIONAL ON the cited Lemma 9, through `Reflection425.interval_fourth_moment_of_lemma9` and
`Reflection425.principal_polar_fourth_sum_le`. The bound c2 qT <= x needed by Lemma 9 holds
eventually from q <= L^A0 and T <= T1.
Non-vacuity: q = 1, T = x^(0.1), L = x^(0.05) and S the principal points t = T/2 + k. -/
theorem leaf_long_fourth_moment :
  ∀ ε : ℝ, 0 < ε → ε < 1 / 100 →
  ∀ (A0 c1 c2 : ℝ) (Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) →
    (∀ x, ∀ c ∈ 𝒮 x, Ll x ≤ (c.q : ℝ) * c.T) →
    ∃ B' K X0 : ℝ, 0 ≤ K ∧ ∀ x, X0 ≤ x → ∀ c ∈ 𝒮 x,
      pnorm (longDP c1 c2 (Ll x)) c 4 ≤ K * (L x ^ B' * (c.q * c.T) ^ (1 / 4 : ℝ)) := by
  sorry

/-- LEAF: page 24, the exponent count under (3.38). MEDIUM.
(qT + M)^(1/2) (qT + N^2)^(1/4) << L^c max(M, x^0.45)^(1/2) max(N, x^0.225)^(1/2)
<= L^c x^(0.3875 + eps/16) by (3.38), and (qT)^(1/4) <= L^c x^(0.1125 - eps/6) by T <= T1, so
the product is at most L^c x^(1/2 - 5 eps/48), which beats x^(1/2) / L^A.
Non-vacuity: Ml = x^(0.5), Nl = x^(0.2), q = 1, T = x^(0.1) satisfy (3.38) and T <= T1. -/
theorem leaf_338_exponent :
  ∀ ε : ℝ, 0 < ε → ε < 1 / 100 →
  ∀ (A0 : ℝ) (Ml Nl : ℝ → ℝ) (𝒮 : ℝ → Set Cfg),
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ c.T ≤ T1 ε x) →
    (∀ x, ∀ c ∈ 𝒮 x, max (Ml x) (x ^ (0.45 : ℝ)) * max (Nl x) (x ^ (0.225 : ℝ)) ≤ x ^ (0.775 + ε / 8)) →
    ∀ B1 B2 B3 A : ℝ, 0 < A → ∃ C X0 : ℝ, 0 ≤ C ∧ ∀ x, X0 ≤ x → ∀ c ∈ 𝒮 x,
      (L x ^ B1 * (c.q * c.T + max (Ml x) 0) ^ (1 / 2 : ℝ)) *
        (L x ^ B2 * (c.q * c.T + max (Nl x) 0 ^ 2) ^ (1 / 4 : ℝ)) *
        (L x ^ B3 * (c.q * c.T) ^ (1 / 4 : ℝ)) ≤ C * x ^ (1 / 2 : ℝ) / L x ^ A := by
  intro ε hε _ A0 Ml Nl 𝒮 hcase h338 B1 B2 B3 A _
  obtain ⟨X, hX⟩ := exp338_log_pow_le_rpow (B1 + B2 + B3 + |A0| + A) (5 * ε / 48) (by positivity)
  refine ⟨2, max X (Real.exp 1), by norm_num, ?_⟩
  intro x hx c hc
  have hxe : Real.exp 1 ≤ x := (le_max_right _ _).trans hx
  have hx1 : 1 ≤ x := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hℓ1 : 1 ≤ L x := (Real.le_log_iff_exp_le (by linarith)).mpr hxe
  obtain ⟨hstd, hqA, hT1⟩ := hcase x c hc
  have hT : 0 ≤ c.T := by linarith [hstd.2.2.2.1]
  exact exp338_core ε A0 B1 B2 B3 A x c.q c.T (Ml x) (Nl x) hε hx1 hℓ1 (Nat.cast_nonneg _) hT
    hqA hT1 (h338 x c hc) (hX x ((le_max_left _ _).trans hx))

/-- `lemma10_small_L_338`, verbatim. CONDITIONAL ON `leaf_338_mean_M`, `leaf_338_fourth_N`,
`leaf_long_fourth_moment` and `leaf_338_exponent`; `leaf_338_holder` is proved. -/
theorem lemma10_small_L_338_split :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (A0 B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) →
    (∀ x, ∀ c ∈ 𝒮 x, max (Ml x) (x ^ (0.45 : ℝ)) * max (Nl x) (x ^ (0.225 : ℝ)) ≤ x ^ (0.775 + ε / 8)) →
    (∀ x, ∀ c ∈ 𝒮 x, Ll x ≤ (c.q : ℝ) * c.T) →
    Concl39 (fun x => [M x, N x, (⟨fun _ => 1, Finset.Ioo ⌊c1 * Ll x⌋₊ ⌈c2 * Ll x⌉₊⟩ : DP)]) 𝒮 := by
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro ε hε hε0 A0 B c1 c2 M N Ml Nl Ll 𝒮 hc1 hc2 hfam hprod hcase h338 hsmall A hA
  have hcase2 : ∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 :=
    fun x c hc => ⟨(hcase x c hc).1, (hcase x c hc).2.1⟩
  obtain ⟨B1, K1, X1, hK1, hM⟩ :=
    leaf_338_mean_M ε hε hε0 A0 B c1 c2 M N Ml Nl 𝒮 hc1 hc2 hfam hcase2 h338
  obtain ⟨B2, K2, X2, hK2, hN⟩ :=
    leaf_338_fourth_N ε hε hε0 A0 B c1 c2 M N Ml Nl 𝒮 hc1 hc2 hfam hcase2 h338
  obtain ⟨B3, K3, X3, hK3, hP⟩ :=
    leaf_long_fourth_moment ε hε hε0 A0 c1 c2 Ll 𝒮 hc1 hc2 hcase hsmall
  obtain ⟨C, X4, hC, hexp⟩ := leaf_338_exponent ε hε hε0 A0 Ml Nl 𝒮
    (fun x c hc => ⟨(hcase x c hc).1, (hcase x c hc).2.1, (hcase x c hc).2.2.2.1⟩) h338
    B1 B2 B3 A hA
  refine ⟨K1 * K2 * K3 * C, max (max X1 X2) (max X3 X4), ?_⟩
  intro x hx c hc
  have hx1 : X1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : X2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : X3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hx4 : X4 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have h1 := hM x hx1 c hc
  have h2 := hN x hx2 c hc
  have h3 := hP x hx3 c hc
  have h4 := hexp x hx4 c hc
  have hpM := split338_pnorm_nonneg (M x) c 2
  have hpN := split338_pnorm_nonneg (N x) c 4
  have hpP := split338_pnorm_nonneg (longDP c1 c2 (Ll x)) c 4
  have hb1 : 0 ≤ K1 * (L x ^ B1 * (c.q * c.T + max (Ml x) 0) ^ (1 / 2 : ℝ)) := hpM.trans h1
  have hb2 : 0 ≤ K2 * (L x ^ B2 * (c.q * c.T + max (Nl x) 0 ^ 2) ^ (1 / 4 : ℝ)) := hpN.trans h2
  show norm1prod [M x, N x, longDP c1 c2 (Ll x)] c ≤ K1 * K2 * K3 * C * x ^ (1 / 2 : ℝ) / L x ^ A
  calc norm1prod [M x, N x, longDP c1 c2 (Ll x)] c
      ≤ pnorm (M x) c 2 * pnorm (N x) c 4 * pnorm (longDP c1 c2 (Ll x)) c 4 :=
        leaf_338_holder _ _ _ c
    _ ≤ K1 * (L x ^ B1 * (c.q * c.T + max (Ml x) 0) ^ (1 / 2 : ℝ)) *
          (K2 * (L x ^ B2 * (c.q * c.T + max (Nl x) 0 ^ 2) ^ (1 / 4 : ℝ))) *
          (K3 * (L x ^ B3 * (c.q * c.T) ^ (1 / 4 : ℝ))) :=
        mul_le_mul (mul_le_mul h1 h2 hpN hb1) h3 hpP (mul_nonneg hb1 hb2)
    _ = K1 * K2 * K3 * ((L x ^ B1 * (c.q * c.T + max (Ml x) 0) ^ (1 / 2 : ℝ)) *
          (L x ^ B2 * (c.q * c.T + max (Nl x) 0 ^ 2) ^ (1 / 4 : ℝ)) *
          (L x ^ B3 * (c.q * c.T) ^ (1 / 4 : ℝ))) := by ring
    _ ≤ K1 * K2 * K3 * (C * x ^ (1 / 2 : ℝ) / L x ^ A) :=
        mul_le_mul_of_nonneg_left h4 (mul_nonneg (mul_nonneg hK1 hK2) hK3)
    _ = K1 * K2 * K3 * C * x ^ (1 / 2 : ℝ) / L x ^ A := by ring

#print axioms split338_pnorm_nonneg
#print axioms leaf_338_holder
#print axioms leaf_338_exponent
#print axioms lemma10_small_L_338_split

end LeanLab.BakerHarmanPintz1997
