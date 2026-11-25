/-
Split of `lemma10_large_L` in LeanLab.BakerHarmanPintz1997.DecompJ381 into leaves.
P0069 page 24, proof of Lemma 10, the case L > qT. The sealed statement is unchanged and is
restated verbatim in `lemma10_large_L_split`.

The paper bounds ||MNL||_1 by sup |L| times ||M||_2 ||N||_2, then uses Lemma 1 for the two mean
squares and the size conditions (3.37) with (3.38) or (3.39) for the exponents.
Step 0, already proved in DecompJ381: `Reflection425.longSup_product_bound`, the Cauchy Schwarz
step from `LongSup` and the principal height condition.
Step 1, degenerate lengths, PROVED here as `leaf_large_degenerate`: if c2 M < 1 or c2 N < 1
the polynomial has only the term n = 0, which vanishes, so the product norm is 0.
Leaf 2, the mean squares: Lemma 1 with the coefficient bound (3.1) gives
||M||_2 ||N||_2 << L^B' (qT + M)^(1/2) (qT + N)^(1/2). HARD.
Leaf 3, the exponent count: (L^B + 2 L^(1/2)/T) times that bound is << x^(1/2) / L^A, from
T0 <= T <= T1, LMN = x, qT < L and (3.38) or (3.39). MEDIUM.
The assembly multiplies the three bounds. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.SPLIT_lemma10_large_L_p2_meansq

namespace LeanLab.BakerHarmanPintz1997
open Finset
open scoped Real

/-- Proved helper: a polynomial supported on n < 1, that is on n = 0 only, vanishes at
1/2 + it, since 0^(-1/2-it) = 0. -/
theorem split_large_eval_zero (P : DP) {q : ℕ} (χ : DirichletCharacter ℂ q) (t : ℝ)
    (h : ∀ n ∈ P.supp, (n : ℝ) < 1) : P.eval χ (half t) = 0 := by
  unfold DP.eval
  apply sum_eq_zero
  intro n hn
  have hn0 : n = 0 := by
    have := h n hn
    have : n < 1 := by exact_mod_cast this
    omega
  subst hn0
  have hne : -(half t) ≠ 0 := by
    intro h0
    have := congrArg Complex.re h0
    simp [half] at this
  simp [Complex.zero_cpow hne]

/-- PROVED, formerly planned as a leaf: page 24, the implicit convention M, N >> 1 of Lemma 10.
If c2 M < 1 or c2 N < 1 then by the length condition every n in the support is 0, the term
n^(-1/2-it) vanishes, so ||MNP||_1 = 0.
Non-vacuity: Ml = 1/(2 c2) with a nonempty support {0} is allowed by `FamOK`. -/
theorem leaf_large_degenerate :
  ∀ (B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl : ℝ → ℝ),
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    ∀ (x : ℝ) (c : Cfg) (P : DP), (c2 * Ml x < 1 ∨ c2 * Nl x < 1) →
      norm1prod [M x, N x, P] c = 0 := by
  intro B c1 c2 M N Ml Nl hfam x c P hdeg
  obtain ⟨-, hget⟩ := hfam x
  have hM : (M x).HasLen (Ml x) c1 c2 := (hget 0 (by simp) (by simp)).1
  have hN : (N x).HasLen (Nl x) c1 c2 := (hget 1 (by simp) (by simp)).1
  unfold norm1prod
  apply sum_eq_zero
  intro e he
  rcases hdeg with h | h
  · have h0 := split_large_eval_zero (M x) e.2 e.1 (fun n hn => (hM n hn).2.trans h)
    simp [h0]
  · have h0 := split_large_eval_zero (N x) e.2 e.1 (fun n hn => (hN n hn).2.trans h)
    simp [h0]

/-- LEAF: page 24, the two mean squares in the case L > qT: Lemma 1, (3.3), with (3.1) giving
G(F) << L^B'' for F at most a constant times x. HARD, it rests on the cited Lemma 1 and a
divisor sum bound. M <= c2 x / 2 follows from LMN = x, qT < L and c2 N >= 1.
Non-vacuity: any family with M, N of length about x^(1/3) and q = 1. -/
theorem leaf_large_mean_square :
  ∀ (B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x) →
    (∀ x, ∀ c ∈ 𝒮 x, (c.q : ℝ) * c.T < Ll x) →
    ∃ B' K X0 : ℝ, 0 ≤ K ∧ ∀ x, X0 ≤ x → ∀ c ∈ 𝒮 x, 1 ≤ c2 * Ml x → 1 ≤ c2 * Nl x →
      pnorm (M x) c 2 * pnorm (N x) c 2 ≤
        K * (L x ^ B' * ((c.q * c.T + Ml x) ^ (1 / 2 : ℝ) * (c.q * c.T + Nl x) ^ (1 / 2 : ℝ))) := by
  -- PROVED in burst-20261122 from `meanSquare_of_lemma1_P2`, CONDITIONAL ON the cited `lemma1`.
  intro B c1 c2 M N Ml Nl Ll 𝒮 hc1 hc2 hfam hprod hstd hlarge
  have hc2p : 0 < c2 := by linarith
  obtain ⟨E, K, X0, hK, hb⟩ :=
    meanSquare_of_lemma1_P2 lemma1 B c1 c2 (c2 + 1) hc1 hc2 (by linarith)
  refine ⟨E + E, K * K, max X0 3, mul_nonneg hK hK, ?_⟩
  intro x hx c hc hm hn
  have hX0 : X0 ≤ x := (le_max_left _ _).trans hx
  have hx3 : 3 ≤ x := (le_max_right _ _).trans hx
  have hLpos : 0 < L x := Real.log_pos (by linarith)
  obtain ⟨-, hget⟩ := hfam x
  have hM := hget 0 (by simp) (by simp)
  have hN := hget 1 (by simp) (by simp)
  have hst := hstd x c hc
  obtain ⟨-, hq1, -, hT2, -⟩ := hst
  have hq1' : (1 : ℝ) ≤ c.q := by exact_mod_cast hq1
  have hqT : 2 < (c.q : ℝ) * c.T := by nlinarith
  have hLl : 2 < Ll x := lt_trans hqT (hlarge x c hc)
  have hMpos : 0 < Ml x := pos_of_mul_pos_right (by linarith : 0 < c2 * Ml x) hc2p.le
  have hNpos : 0 < Nl x := pos_of_mul_pos_right (by linarith : 0 < c2 * Nl x) hc2p.le
  have hxe : (c2 + 1) * x = c2 * x + x := by ring
  have hMl : Ml x ≤ (c2 + 1) * x := by
    have h1 : 1 ≤ (c2 * Nl x) * Ll x := one_le_mul_of_one_le_of_one_le hn (by linarith)
    have h2 : Ml x * ((c2 * Nl x) * Ll x) = c2 * x := by linear_combination c2 * hprod x
    have h3 : Ml x ≤ Ml x * ((c2 * Nl x) * Ll x) := le_mul_of_one_le_right hMpos.le h1
    linarith
  have hNl : Nl x ≤ (c2 + 1) * x := by
    have h1 : 1 ≤ (c2 * Ml x) * Ll x := one_le_mul_of_one_le_of_one_le hm (by linarith)
    have h2 : Nl x * ((c2 * Ml x) * Ll x) = c2 * x := by linear_combination c2 * hprod x
    have h3 : Nl x ≤ Nl x * ((c2 * Ml x) * Ll x) := le_mul_of_one_le_right hNpos.le h1
    linarith
  have h1 := hb x hX0 (Ml x) (M x) c hM.1 hM.2 (hstd x c hc) hMl
  have h2 := hb x hX0 (Nl x) (N x) c hN.1 hN.2 (hstd x c hc) hNl
  rw [max_eq_left hMpos.le] at h1
  rw [max_eq_left hNpos.le] at h2
  have hp0 : ∀ P : DP, 0 ≤ pnorm P c 2 := fun P =>
    Real.rpow_nonneg (sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _
  calc pnorm (M x) c 2 * pnorm (N x) c 2
      ≤ (K * (L x ^ E * (c.q * c.T + Ml x) ^ (1 / 2 : ℝ))) *
          (K * (L x ^ E * (c.q * c.T + Nl x) ^ (1 / 2 : ℝ))) :=
        mul_le_mul h1 h2 (hp0 _) ((hp0 _).trans h1)
    _ = K * K * (L x ^ (E + E) * ((c.q * c.T + Ml x) ^ (1 / 2 : ℝ) *
          (c.q * c.T + Nl x) ^ (1 / 2 : ℝ))) := by
        rw [Real.rpow_add hLpos]
        ring

/-- LEAF: page 24, the exponent count of the case L > qT. MEDIUM.
With MN = x/L, T0 <= T <= T1 = x^(0.45 - 2 eps/3), q <= L^A0, qT < L, M N >= T0 eventually and
(3.38) or (3.39): each of (qT)^2, qT M, qT N is at most L^c x^(1 - eps/2), MN < x/T0, and the
polar terms are at most x^(1/2) times L^c / T0^(1/2); T0 = exp(L^(1/3)) beats every power of L.
Non-vacuity: Ml = Nl = x^(0.4), Ll = x^(0.2), q = 1, T = x^(0.1) satisfy every hypothesis. -/
theorem leaf_large_exponent :
  ∀ ε : ℝ, 0 < ε → ε < 1 / 100 →
  ∀ (A0 c2 : ℝ) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x) →
    (∀ x, ∀ c ∈ 𝒮 x, (c.q : ℝ) * c.T < Ll x) →
    (∀ x, max (Ml x) (x ^ (0.45 : ℝ)) * max (Nl x) (x ^ (0.225 : ℝ)) ≤ x ^ (0.775 + ε / 8) ∨
      max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 8)) →
    (∃ X1 : ℝ, ∀ x, X1 ≤ x → T0 x ≤ Ml x * Nl x) →
    ∀ B B' A : ℝ, 0 < A → ∃ C X0 : ℝ, 0 ≤ C ∧ ∀ x, X0 ≤ x → ∀ c ∈ 𝒮 x,
      1 ≤ c2 * Ml x → 1 ≤ c2 * Nl x →
      (L x ^ B + 2 * Ll x ^ (1 / 2 : ℝ) / c.T) *
        (L x ^ B' * ((c.q * c.T + Ml x) ^ (1 / 2 : ℝ) * (c.q * c.T + Nl x) ^ (1 / 2 : ℝ))) ≤
        C * x ^ (1 / 2 : ℝ) / L x ^ A := by
  sorry

/-- `lemma10_large_L`, verbatim. CONDITIONAL ON `leaf_large_mean_square` and `leaf_large_exponent`, and on the proved
`leaf_large_degenerate` and `Reflection425.longSup_product_bound`. -/
theorem lemma10_large_L_split :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (A0 B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) →
    (∀ x, ∀ c ∈ 𝒮 x, (c.q : ℝ) * c.T < Ll x) →
    (∀ x, max (Ml x) (x ^ (0.45 : ℝ)) * max (Nl x) (x ^ (0.225 : ℝ)) ≤ x ^ (0.775 + ε / 8) ∨
      max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 8)) →
    (∃ X1 : ℝ, ∀ x, X1 ≤ x → T0 x ≤ Ml x * Nl x) →
    LongSup c1 c2 Ll 𝒮 →
    Concl39 (fun x => [M x, N x, (⟨fun _ => 1, Finset.Ioo ⌊c1 * Ll x⌋₊ ⌈c2 * Ll x⌉₊⟩ : DP)]) 𝒮 := by
  refine ⟨1 / 100, by norm_num, ?_⟩
  intro ε hε hε0 A0 B c1 c2 M N Ml Nl Ll 𝒮 hc1 hc2 hfam hprod hcase hlarge hor hMN hsup A hA
  have hstd : ∀ x, ∀ c ∈ 𝒮 x, c.Std x := fun x c hc => (hcase x c hc).1
  have hLl : ∀ x, ∀ c ∈ 𝒮 x, 0 ≤ Ll x := by
    intro x c hc
    have h := hlarge x c hc
    obtain ⟨-, hq, -, hT, -⟩ := hstd x c hc
    have hq' : (1 : ℝ) ≤ c.q := by exact_mod_cast hq
    nlinarith
  have hheight : ∀ x, ∀ c ∈ 𝒮 x, ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| :=
    fun x c hc e he h1 => ((hcase x c hc).2.2.2.2 e he h1).1
  obtain ⟨B1, K1, X1, hK1, hpb⟩ :=
    Reflection425.longSup_product_bound c1 c2 M N Ll 𝒮 hsup hstd hLl hheight
  obtain ⟨B2, K2, X2, hK2, hms⟩ :=
    leaf_large_mean_square B c1 c2 M N Ml Nl Ll 𝒮 hc1 hc2 hfam hprod hstd hlarge
  obtain ⟨C, X3, hC, hexp⟩ := leaf_large_exponent ε hε hε0 A0 c2 Ml Nl Ll 𝒮 (by linarith)
    hprod (fun x c hc => ⟨(hcase x c hc).1, (hcase x c hc).2.1, (hcase x c hc).2.2.1,
      (hcase x c hc).2.2.2.1⟩) hlarge hor hMN B1 B2 A hA
  refine ⟨K1 * K2 * C, max (max X1 X2) (max X3 1), ?_⟩
  intro x hx c hc
  have hx1 : X1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : X2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx3 : X3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxone : 1 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hLx : 0 ≤ L x := Real.log_nonneg hxone
  have hrhs : 0 ≤ K1 * K2 * C * x ^ (1 / 2 : ℝ) / L x ^ A :=
    div_nonneg (mul_nonneg (mul_nonneg (mul_nonneg hK1 hK2) hC)
      (Real.rpow_nonneg (by linarith) _)) (Real.rpow_nonneg hLx _)
  show norm1prod [M x, N x, longDP c1 c2 (Ll x)] c ≤ K1 * K2 * C * x ^ (1 / 2 : ℝ) / L x ^ A
  by_cases hdeg : c2 * Ml x < 1 ∨ c2 * Nl x < 1
  · rw [leaf_large_degenerate B c1 c2 M N Ml Nl hfam x c _ hdeg]
    exact hrhs
  · rw [not_or, not_lt, not_lt] at hdeg
    obtain ⟨hm, hn⟩ := hdeg
    have h1 := hpb x hx1 c hc
    have h2 := hms x hx2 c hc hm hn
    have h3 := hexp x hx3 c hc hm hn
    have hT : 0 < c.T := by
      have := (hstd x c hc).2.2.2.1
      linarith
    have hS : 0 ≤ L x ^ B1 + 2 * Ll x ^ (1 / 2 : ℝ) / c.T := by
      have := Real.rpow_nonneg hLx B1
      have := Real.rpow_nonneg (hLl x c hc) (1 / 2 : ℝ)
      positivity
    calc norm1prod [M x, N x, longDP c1 c2 (Ll x)] c
        ≤ K1 * (L x ^ B1 + 2 * Ll x ^ (1 / 2 : ℝ) / c.T) * pnorm (M x) c 2 *
            pnorm (N x) c 2 := h1
      _ = K1 * ((L x ^ B1 + 2 * Ll x ^ (1 / 2 : ℝ) / c.T) *
            (pnorm (M x) c 2 * pnorm (N x) c 2)) := by ring
      _ ≤ K1 * ((L x ^ B1 + 2 * Ll x ^ (1 / 2 : ℝ) / c.T) *
            (K2 * (L x ^ B2 * ((c.q * c.T + Ml x) ^ (1 / 2 : ℝ) *
              (c.q * c.T + Nl x) ^ (1 / 2 : ℝ))))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left h2 hS) hK1
      _ = K1 * K2 * ((L x ^ B1 + 2 * Ll x ^ (1 / 2 : ℝ) / c.T) *
            (L x ^ B2 * ((c.q * c.T + Ml x) ^ (1 / 2 : ℝ) *
              (c.q * c.T + Nl x) ^ (1 / 2 : ℝ)))) := by ring
      _ ≤ K1 * K2 * (C * x ^ (1 / 2 : ℝ) / L x ^ A) :=
          mul_le_mul_of_nonneg_left h3 (mul_nonneg hK1 hK2)
      _ = K1 * K2 * C * x ^ (1 / 2 : ℝ) / L x ^ A := by ring

#print axioms split_large_eval_zero
#print axioms leaf_large_degenerate
#print axioms leaf_large_mean_square
#print axioms lemma10_large_L_split

end LeanLab.BakerHarmanPintz1997
