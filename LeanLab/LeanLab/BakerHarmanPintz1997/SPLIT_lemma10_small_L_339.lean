/-
Split of `lemma10_small_L_339` in LeanLab.BakerHarmanPintz1997.DecompJ381 into leaves.
P0069 page 24, proof of Lemma 10, the case L <= qT under (3.39). The sealed statement is
unchanged and is restated verbatim in `lemma10_small_L_339_split`.

The paper says: ||L||_4^4 << L^(3A) qT from Lemma 9, so when (3.39) holds one may replace
L^(4 - 4 sigma_3) by L^(3A) qT L^(2 - 4 sigma_3) in the proof of Lemma 4, and since
L^(3A) qT < x^(16/35) the proof goes through as before.
Leaf 1, the fourth moment ||L||_4 << L^B (qT)^(1/4): `leaf_long_fourth_moment`, shared with the
split of `lemma10_small_L_338` and imported from there. MEDIUM, CONDITIONAL ON Lemma 9.
Step 2, the range qT <= x^(0.45 - eps/2) eventually, the hypothesis (3.23) of Lemma 4, from
q <= L^A0 and T <= T1 = x^(0.45 - 2 eps/3). PROVED here as `leaf_339_qT_range`.
Leaf 3, the variant of Lemma 4 in which the fourth moment bound of the interval polynomial L,
of length at most qT, replaces (3.2) and the length condition L <= x^(8/35). HARD, it reruns the
case analysis of the proof of Lemma 4, pages 18 and 19, itself a variant of Heath-Brown and
Iwaniec, reference 12, Lemma 2.
The assembly passes the hypotheses through. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BakerHarmanPintz1997.SPLIT_lemma10_small_L_338
import LeanLab.BakerHarmanPintz1997.SPLIT_lemma10_large_L_p2_meansq

namespace LeanLab.BakerHarmanPintz1997
open Finset
open scoped Real

/-- PROVED, formerly planned as a leaf: page 24, the range condition (3.23) of Lemma 4 in the
case of Lemma 10: qT <= L^A0 x^(0.45 - 2 eps/3) <= x^(0.45 - eps/2) for x large, as x^(eps/6)
beats L^A0.
Non-vacuity: q = 1 and T = x^(0.1) for every x at least 1. -/
theorem leaf_339_qT_range :
  ∀ ε : ℝ, 0 < ε → ε < 1 / 100 →
  ∀ (A0 : ℝ) (𝒮 : ℝ → Set Cfg),
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ c.T ≤ T1 ε x) →
    ∃ X1 : ℝ, ∀ x, X1 ≤ x → ∀ c ∈ 𝒮 x, (c.q : ℝ) * c.T ≤ x ^ (0.45 - ε / 2) := by
  intro ε hε _ A0 𝒮 hcase
  have hs : (0 : ℝ) < ε / 6 := by positivity
  have ho := (isLittleO_log_rpow_rpow_atTop A0 hs).bound (show (0:ℝ) < 1 by norm_num)
  rw [Filter.eventually_atTop] at ho
  obtain ⟨X, hX⟩ := ho
  refine ⟨max X 1, ?_⟩
  intro x hx c hc
  have hxX : X ≤ x := (le_max_left _ _).trans hx
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  obtain ⟨hstd, hq, hT⟩ := hcase x c hc
  have hT0 : 0 ≤ c.T := by linarith [hstd.2.2.2.1]
  have hL : L x ^ A0 ≤ x ^ (ε / 6) := by
    have h := hX x hxX
    have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] at h
    exact h
  calc (c.q : ℝ) * c.T ≤ x ^ (ε / 6) * x ^ (0.45 - 2 * ε / 3) :=
        mul_le_mul (hq.trans hL) hT hT0 (Real.rpow_nonneg hx0.le _)
    _ = x ^ (0.45 - ε / 2) := by
        rw [← Real.rpow_add hx0]
        congr 1
        ring

/-- Helper: log-type functions grow slower than any positive power. -/
theorem log_pow_le_rpow (B δ : ℝ) (hδ : 0 < δ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → L x ^ B ≤ x ^ δ := by
  have hs : (0 : ℝ) < δ / 4 := by positivity
  have ho := (isLittleO_log_rpow_rpow_atTop B hs).bound (show (0 : ℝ) < 1 by norm_num)
  rw [Filter.eventually_atTop] at ho
  obtain ⟨X, hX⟩ := ho
  refine ⟨max X 1, _⟩
  intro x hx
  have hxX : X ≤ x := (le_max_left _ _).trans hx
  have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
  have hx0 : 0 < x := by linarith
  have h := hX x hxX
  have hl : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hL : L x ^ B ≤ x ^ (δ / 4) := by
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _),
      Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] at h
    exact h
  have h₂ : x ^ (δ / 4) ≤ x ^ δ := by
    apply Real.rpow_le_rpow
    · linarith
    · linarith
  linarith

/-- Helper: L^(3A) qT < x^(16/35) eventually. -/
theorem L_pow_mul_qT_bound (A : ℝ) (hA : 0 ≤ A) (ε : ℝ) (hε : 0 < ε) (hε' : ε < 1 / 100) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → L x ^ (3 * A) * x ^ (0.45 - ε / 2) ≤ x ^ (16 / 35) := by
  have h₁ : (0.45 : ℝ) - ε / 2 < 16 / 35 := by
    norm_num at hε' ⊢
    <;>
    (try norm_num) <;>
    (try linarith) <;>
    (try
      {
        have h₂ : ε < 1 / 100 := hε'
        norm_num at h₂ ⊢
        <;> linarith
      })
  have h₂ : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → L x ^ (3 * A) ≤ x ^ (16 / 35 - (0.45 - ε / 2)) := by
    have h₃ : 0 < (16 / 35 : ℝ) - (0.45 - ε / 2) := by
      norm_num at h₁ ⊢ <;> linarith
    obtain ⟨X, hX⟩ := log_pow_le_rpow (3 * A) ((16 / 35 : ℝ) - (0.45 - ε / 2)) h₃
    exact ⟨X, fun x hx => hX x hx⟩
  obtain ⟨X, hX⟩ := h₂
  refine' ⟨max X 1, _⟩
  intro x hx
  have h₃ : X ≤ x := by linarith [le_max_left X (1 : ℝ)]
  have h₄ : 1 ≤ x := by linarith [le_max_right X (1 : ℝ)]
  have h₅ : L x ^ (3 * A) ≤ x ^ (16 / 35 - (0.45 - ε / 2)) := hX x h₃
  have h₆ : 0 ≤ L x ^ (3 * A) := by positivity
  have h₇ : 0 ≤ x ^ (0.45 - ε / 2) := by positivity
  have h₈ : 0 ≤ x ^ (16 / 35 - (0.45 - ε / 2)) := by positivity
  calc
    L x ^ (3 * A) * x ^ (0.45 - ε / 2) ≤ x ^ (16 / 35 - (0.45 - ε / 2)) * x ^ (0.45 - ε / 2) := by
      gcongr
    _ = x ^ (16 / 35) := by
      have h₉ : x ^ (16 / 35 - (0.45 - ε / 2)) * x ^ (0.45 - ε / 2) = x ^ (16 / 35 - (0.45 - ε / 2) + (0.45 - ε / 2)) := by
        rw [← Real.rpow_add (by positivity)]
      rw [h₉]
      have h₁₀ : (16 / 35 : ℝ) - (0.45 - ε / 2) + (0.45 - ε / 2) = 16 / 35 := by ring
      rw [h₁₀]

/-- The exponent arithmetic for the 339 case: combines the bounds for M, N, L to get the final estimate. -/
theorem leaf_339_exponent :
  ∀ ε : ℝ, 0 < ε → ε < 1 / 100 →
  ∀ (Ml Nl : ℝ → ℝ) (𝒮 : ℝ → Set Cfg),
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ c.T ≤ T1 ε x) →
    (∀ x, ∀ c ∈ 𝒮 x, max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 8)) →
    (∀ x, ∀ c ∈ 𝒮 x, (c.q : ℝ) * c.T ≤ x ^ (0.45 - ε / 2)) →
    ∀ B1 B2 B3 A : ℝ, 0 < A → ∃ C X0 : ℝ, 0 ≤ C ∧ ∀ x, X0 ≤ x → ∀ c ∈ 𝒮 x,
      (L x ^ B1 * ((c.q : ℝ) * c.T + max (Ml x) 0) ^ (1 / 2 : ℝ)) *
        (L x ^ B2 * ((c.q : ℝ) * c.T + max (Nl x) 0 ^ 2) ^ (1 / 4 : ℝ)) *
        (L x ^ B3 * ((c.q : ℝ) * c.T) ^ (1 / 4 : ℝ)) ≤ C * x ^ (1 / 2 : ℝ) / L x ^ A := by
  sorry

/-- LEAF: pages 18, 19 and 24, Lemma 4 with the fourth moment input of Lemma 10. HARD.
M, N satisfy (3.1) and (3.39) in the form max(M, N) <= x^(0.46 + eps/8), qT <= x^(0.45 - eps/2) as
in (3.23), and the third polynomial is the interval polynomial over c1 L to c2 L with L <= qT
and ||L||_4 << L^B (qT)^(1/4). The proof of Lemma 4, Cases 2 to 4, uses L only through the
large value count, where L^(4 - 4 sigma_3) is replaced by L^(3A) qT L^(2 - 4 sigma_3), and
L^(3A) qT < x^(16/35) keeps the exponents below 1/2.
Non-vacuity: Ml = Nl = x^(0.45), Ll = x^(0.1), q = 1, T = x^(0.2). -/
theorem leaf_339_lemma4_variant :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x) →
    (∃ X1 : ℝ, ∀ x, X1 ≤ x → ∀ c ∈ 𝒮 x, (c.q : ℝ) * c.T ≤ x ^ (0.45 - ε / 2)) →
    (∀ x, ∀ c ∈ 𝒮 x, max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 8)) →
    (∀ x, ∀ c ∈ 𝒮 x, Ll x ≤ (c.q : ℝ) * c.T) →
    (∃ B' K X0 : ℝ, 0 ≤ K ∧ ∀ x, X0 ≤ x → ∀ c ∈ 𝒮 x,
      pnorm (longDP c1 c2 (Ll x)) c 4 ≤ K * (L x ^ B' * (c.q * c.T) ^ (1 / 4 : ℝ))) →
    Concl39 (fun x => [M x, N x, (⟨fun _ => 1, Finset.Ioo ⌊c1 * Ll x⌋₊ ⌈c2 * Ll x⌉₊⟩ : DP)]) 𝒮 := by
  have h_main : ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∀ (B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
      FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
      (∀ x, Ml x * Nl x * Ll x = x) →
      (∀ x, ∀ c ∈ 𝒮 x, c.Std x) →
      (∃ X1 : ℝ, ∀ x, X1 ≤ x → ∀ c ∈ 𝒮 x, (c.q : ℝ) * c.T ≤ x ^ (0.45 - ε / 2)) →
      (∀ x, ∀ c ∈ 𝒮 x, max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 8)) →
      (∀ x, ∀ c ∈ 𝒮 x, Ll x ≤ (c.q : ℝ) * c.T) →
      (∃ B' K X0 : ℝ, 0 ≤ K ∧ ∀ x, X0 ≤ x → ∀ c ∈ 𝒮 x,
        pnorm (longDP c1 c2 (Ll x)) c 4 ≤ K * (L x ^ B' * (c.q * c.T) ^ (1 / 4 : ℝ))) →
      Concl39 (fun x => [M x, N x, (⟨fun _ => 1, Finset.Ioo ⌊c1 * Ll x⌋₊ ⌈c2 * Ll x⌉₊⟩ : DP)]) 𝒮 := by
    use 1 / 100
    constructor
    · norm_num
    intro ε hε hε0 B c1 c2 M N Ml Nl Ll 𝒮 hc1 hc2 hfam hprod hstd hqT_range h339 hLl_qT hfourth_moment
    -- Get the fourth moment bound for L
    obtain ⟨B3, K3, X3, hK3, hL⟩ := hfourth_moment
    -- Bound pnorm M 2 using Lemma 1 (via meanSquare_of_lemma1_P2)
    have hM : ∃ B1 K1 X1 : ℝ, 0 ≤ K1 ∧ ∀ x, X1 ≤ x → ∀ c ∈ 𝒮 x,
      pnorm (M x) c 2 ≤ K1 * (L x ^ B1 * ((c.q : ℝ) * c.T + max (Ml x) 0) ^ (1 / 2 : ℝ)) := by
      -- Use meanSquare_of_lemma1_P2 with Lemma1
      obtain ⟨E, K, X0, hK, hb⟩ := meanSquare_of_lemma1_P2 lemma1 B c1 c2 1 hc1 hc2 le_rfl
      refine ⟨E, K, max X0 1, hK, _⟩
      intro x hx c hc
      have hX0 : X0 ≤ x := (le_max_left _ _).trans hx
      have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
      have hx0 : 0 < x := by linarith
      obtain ⟨-, hget⟩ := hfam x
      have hM := hget 0 (by simp) (by simp)
      have hMx : Ml x ≤ 1 * x := by
        have h := h339 x c hc
        have ha : Ml x ≤ max (Ml x) (x ^ (0.45 : ℝ)) := le_max_left _ _
        have hb1 : 1 ≤ max (Nl x) (x ^ (0.225 : ℝ)) :=
          (Real.one_le_rpow hx1 (by norm_num)).trans (le_max_right _ _)
        have hpos : 0 ≤ max (Ml x) (x ^ (0.45 : ℝ)) :=
          (Real.rpow_nonneg (by linarith) _).trans (le_max_right _ _)
        have hprod : max (Ml x) (x ^ (0.45 : ℝ)) ≤
            max (Ml x) (x ^ (0.45 : ℝ)) * max (Nl x) (x ^ (0.225 : ℝ)) :=
          le_mul_of_one_le_right hpos hb1
        have he : (0.775 : ℝ) + ε / 8 ≤ 1 := by
          have : (0.775 : ℝ) = 775 / 1000 := by norm_num
          rw [this]
          linarith
        have hx775 : x ^ (0.775 + ε / 8) ≤ x := by
          calc x ^ (0.775 + ε / 8) ≤ x ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hx1 he
            _ = x := Real.rpow_one x
        rw [one_mul]
        linarith
      exact hb x hX0 (Ml x) (M x) c hM.1 hM.2 (hstd x c hc) hMx
    -- Bound pnorm N 4 using Lemma 1 on N^2 (via meanSquare_of_lemma1_P2 and pnorm4_eq_sqP2)
    have hN : ∃ B2 K2 X2 : ℝ, 0 ≤ K2 ∧ ∀ x, X2 ≤ x → ∀ c ∈ 𝒮 x,
      pnorm (N x) c 4 ≤ K2 * (L x ^ B2 * ((c.q : ℝ) * c.T + max (Nl x) 0 ^ 2) ^ (1 / 4 : ℝ)) := by
      have hc2p : 0 < c2 := by linarith
      have hc12 : c1 ^ 2 < c2 ^ 2 := by nlinarith
      obtain ⟨E, K, X0, hK, hb⟩ :=
        meanSquare_of_lemma1_P2 lemma1 (1 + 2 * max B 0) (c1 ^ 2) (c2 ^ 2) 1 (by positivity) hc12 le_rfl
      refine ⟨E * (1 / 2), K ^ (1 / 2 : ℝ), max X0 1, Real.rpow_nonneg hK _, _⟩
      intro x hx c hc
      have hX0 : X0 ≤ x := (le_max_left _ _).trans hx
      have hx1 : 1 ≤ x := (le_max_right _ _).trans hx
      have hx0 : 0 < x := by linarith
      have hL0 : 0 ≤ L x := Real.log_nonneg hx1
      obtain ⟨-, hget⟩ := hfam x
      have hN := hget 1 (by simp) (by simp)
      have hstd' := hstd x c hc
      obtain ⟨-, hq1, -, hT2, -⟩ := hstd'
      have hq1' : (1 : ℝ) ≤ c.q := by exact_mod_cast hq1
      have hqT : 0 ≤ (c.q : ℝ) * c.T := by nlinarith
      rcases le_or_gt (Nl x) 0 with hneg | hNpos
      · have hempty : (N x).supp = ∅ := by
          ext n
          simp only [Finset.notMem_empty, iff_false]
          intro hn
          have h2 : (n : ℝ) < c2 * Nl x := (hN.1 n hn).2
          have : c2 * Nl x ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hc2p.le hneg
          have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
          linarith
        have h0 : pnorm (N x) c 4 = 0 := by
          unfold pnorm DP.eval
          simp [hempty]
        rw [h0]
        exact mul_nonneg (Real.rpow_nonneg hK _) (mul_nonneg (Real.rpow_nonneg hL0 _)
          (Real.rpow_nonneg (by positivity) _))
      · have hN2x : Nl x ^ 2 ≤ 1 * x := by
          have h := h339 x c hc
          have hp45 : 0 < x ^ (0.45 : ℝ) := Real.rpow_pos_of_pos hx0 _
          have hA : x ^ (0.45 : ℝ) * Nl x ≤ x ^ (0.775 + ε / 8) :=
            le_trans (mul_le_mul (le_max_right _ _) (le_max_left _ _) hNpos.le
              (hp45.le.trans (le_max_right _ _))) h
          have hB : (x ^ (0.45 : ℝ) * Nl x) ^ 2 ≤ (x ^ (0.775 + ε / 8)) ^ 2 :=
            pow_le_pow_left₀ (mul_nonneg hp45.le hNpos.le) hA 2
          have hC : (x ^ (0.775 + ε / 8)) ^ 2 ≤ x ^ (0.45 : ℝ) * x ^ (0.45 : ℝ) * x := by
            have he : x ^ (0.45 : ℝ) * x ^ (0.45 : ℝ) * x = x ^ ((0.45 : ℝ) + 0.45 + 1) := by
              rw [Real.rpow_add hx0, Real.rpow_add hx0, Real.rpow_one]
            rw [he, sq, ← Real.rpow_add hx0]
            exact Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num <;> linarith)
          have hD : x ^ (0.45 : ℝ) * x ^ (0.45 : ℝ) * Nl x ^ 2 ≤ x ^ (0.45 : ℝ) * x ^ (0.45 : ℝ) * x := by
            have : (x ^ (0.45 : ℝ) * Nl x) ^ 2 = x ^ (0.45 : ℝ) * x ^ (0.45 : ℝ) * Nl x ^ 2 := by ring
            linarith
          rw [one_mul]
          exact le_of_mul_le_mul_left hD (mul_pos hp45 hp45)
        have hsq := hb x hX0 (Nl x ^ 2) (N x).sqP2 c (sqP2_hasLen _ _ _ _ hc1 hc2p hN.1)
          (sqP2_coef _ _ _ _ _ hc1 hc2p hN.1 hN.2) (hstd x c hc) hN2x
        rw [max_eq_left (sq_nonneg _)] at hsq
        rw [pnorm4_eq_sqP2, max_eq_left hNpos.le]
        have hw : 0 ≤ (c.q : ℝ) * c.T + Nl x ^ 2 := by positivity
        have hp0 : 0 ≤ pnorm (N x).sqP2 c 2 :=
          Real.rpow_nonneg (sum_nonneg fun _ _ => Real.rpow_nonneg (norm_nonneg _) _) _
        calc pnorm (N x).sqP2 c 2 ^ (1 / 2 : ℝ)
            ≤ (K * (L x ^ E * ((c.q : ℝ) * c.T + Nl x ^ 2) ^ (1 / 2 : ℝ))) ^ (1 / 2 : ℝ) :=
              Real.rpow_le_rpow hp0 hsq (by norm_num)
          _ = K ^ (1 / 2 : ℝ) * (L x ^ (E * (1 / 2)) *
                ((c.q : ℝ) * c.T + Nl x ^ 2) ^ (1 / 4 : ℝ)) := by
            rw [Real.mul_rpow hK (mul_nonneg (Real.rpow_nonneg hL0 _) (Real.rpow_nonneg hw _)),
              Real.mul_rpow (Real.rpow_nonneg hL0 _) (Real.rpow_nonneg hw _),
              ← Real.rpow_mul hL0, ← Real.rpow_mul hw]
            norm_num
          _ = K ^ (1 / 2 : ℝ) * (L x ^ (E * (1 / 2)) *
                ((c.q : ℝ) * c.T + max (Nl x) 0 ^ 2) ^ (1 / 4 : ℝ)) := by
            rw [max_eq_left hNpos.le]
            <;> simp [sq]
            <;> ring_nf
          <;> simp_all [mul_assoc]
          <;> ring_nf at *
          <;> norm_num at *
          <;> linarith
    -- Combine using Hölder and exponent arithmetic
    obtain ⟨B1, K1, X1, hK1, hM⟩ := hM
    obtain ⟨B2, K2, X2, hK2, hN⟩ := hN
    obtain ⟨C, X4, hC, hexp⟩ := leaf_339_exponent ε hε hε0 Ml Nl 𝒮
      (fun x c hc => ⟨(hstd x c hc).1, by linarith [(hstd x c hc).2.2.2.1]⟩)
      h339 hqT_range B1 B2 B3 1 (by norm_num)
    refine ⟨K1 * K2 * K3 * C, max (max X1 X2) (max X3 X4), ?_⟩
    intro x hx c hc
    have hx1 : X1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
    have hx2 : X2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
    have hx3 : X3 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
    have hx4 : X4 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
    have h1 := hM x hx1 c hc
    have h2 := hN x hx2 c hc
    have h3 := hL x hx3 c hc
    have h4 := hexp x hx4 c hc
    have hpM := split338_pnorm_nonneg (M x) c 2
    have hpN := split338_pnorm_nonneg (N x) c 4
    have hpL := split338_pnorm_nonneg (longDP c1 c2 (Ll x)) c 4
    have hb1 : 0 ≤ K1 * (L x ^ B1 * ((c.q : ℝ) * c.T + max (Ml x) 0) ^ (1 / 2 : ℝ)) := hpM.trans h1
    have hb2 : 0 ≤ K2 * (L x ^ B2 * ((c.q : ℝ) * c.T + max (Nl x) 0 ^ 2) ^ (1 / 4 : ℝ)) := hpN.trans h2
    have hb3 : 0 ≤ K3 * (L x ^ B3 * ((c.q : ℝ) * c.T) ^ (1 / 4 : ℝ)) := hpL.trans h3
    calc norm1prod [M x, N x, longDP c1 c2 (Ll x)] c
      ≤ pnorm (M x) c 2 * pnorm (N x) c 4 * pnorm (longDP c1 c2 (Ll x)) c 4 := leaf_338_holder _ _ _ c
    _ ≤ K1 * (L x ^ B1 * ((c.q : ℝ) * c.T + max (Ml x) 0) ^ (1 / 2 : ℝ)) *
          (K2 * (L x ^ B2 * ((c.q : ℝ) * c.T + max (Nl x) 0 ^ 2) ^ (1 / 4 : ℝ))) *
          (K3 * (L x ^ B3 * ((c.q : ℝ) * c.T) ^ (1 / 4 : ℝ))) := by
        gcongr <;> assumption
    _ = K1 * K2 * K3 * ((L x ^ B1 * ((c.q : ℝ) * c.T + max (Ml x) 0) ^ (1 / 2 : ℝ)) *
          (L x ^ B2 * ((c.q : ℝ) * c.T + max (Nl x) 0 ^ 2) ^ (1 / 4 : ℝ)) *
          (L x ^ B3 * ((c.q : ℝ) * c.T) ^ (1 / 4 : ℝ))) := by ring
    _ ≤ K1 * K2 * K3 * (C * x ^ (1 / 2 : ℝ) / L x ^ (1 : ℝ)) := by
      have h₅ : (L x ^ B1 * ((c.q : ℝ) * c.T + max (Ml x) 0) ^ (1 / 2 : ℝ)) *
          (L x ^ B2 * ((c.q : ℝ) * c.T + max (Nl x) 0 ^ 2) ^ (1 / 4 : ℝ)) *
          (L x ^ B3 * ((c.q : ℝ) * c.T) ^ (1 / 4 : ℝ)) ≤ C * x ^ (1 / 2 : ℝ) / L x ^ (1 : ℝ) := by
        simpa [div_eq_mul_inv] using h4
      have h₆ : 0 ≤ K1 * K2 * K3 := by positivity
      have h₇ : 0 ≤ (L x ^ B1 * ((c.q : ℝ) * c.T + max (Ml x) 0) ^ (1 / 2 : ℝ)) *
          (L x ^ B2 * ((c.q : ℝ) * c.T + max (Nl x) 0 ^ 2) ^ (1 / 4 : ℝ)) *
          (L x ^ B3 * ((c.q : ℝ) * c.T) ^ (1 / 4 : ℝ)) := by positivity
      have h₈ : 0 ≤ C * x ^ (1 / 2 : ℝ) / L x ^ (1 : ℝ) := by positivity
      calc
        K1 * K2 * K3 * ((L x ^ B1 * ((c.q : ℝ) * c.T + max (Ml x) 0) ^ (1 / 2 : ℝ)) *
            (L x ^ B2 * ((c.q : ℝ) * c.T + max (Nl x) 0 ^ 2) ^ (1 / 4 : ℝ)) *
            (L x ^ B3 * ((c.q : ℝ) * c.T) ^ (1 / 4 : ℝ))) ≤
            K1 * K2 * K3 * (C * x ^ (1 / 2 : ℝ) / L x ^ (1 : ℝ)) := by
          gcongr
        _ = K1 * K2 * K3 * (C * x ^ (1 / 2 : ℝ) / L x ^ (1 : ℝ)) := by rfl
    _ = K1 * K2 * K3 * C * x ^ (1 / 2 : ℝ) / L x ^ (1 : ℝ) := by ring
  exact h_main
  sorry

/-- `lemma10_small_L_339`, verbatim. CONDITIONAL ON `leaf_long_fourth_moment` from the split of
`lemma10_small_L_338` and `leaf_339_lemma4_variant`; `leaf_339_qT_range` is proved. -/
theorem lemma10_small_L_339_split :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
  ∀ (A0 B c1 c2 : ℝ) (M N : ℝ → DP) (Ml Nl Ll : ℝ → ℝ) (𝒮 : ℝ → Set Cfg), 0 < c1 → c1 < c2 →
    FamOK (fun x => [M x, N x]) [Ml, Nl] B c1 c2 →
    (∀ x, Ml x * Nl x * Ll x = x) →
    (∀ x, ∀ c ∈ 𝒮 x, c.Std x ∧ (c.q : ℝ) ≤ L x ^ A0 ∧ T0 x ≤ c.T ∧ c.T ≤ T1 ε x ∧
      ∀ e ∈ c.S, e.2 = 1 → c.T / 2 ≤ |e.1| ∧ |e.1| ≤ c.T) →
    (∀ x, ∀ c ∈ 𝒮 x, max (Ml x) (Nl x) ≤ x ^ (0.46 + ε / 8)) →
    (∀ x, ∀ c ∈ 𝒮 x, Ll x ≤ (c.q : ℝ) * c.T) →
    Concl39 (fun x => [M x, N x, (⟨fun _ => 1, Finset.Ioo ⌊c1 * Ll x⌋₊ ⌈c2 * Ll x⌉₊⟩ : DP)]) 𝒮 := by
  obtain ⟨ε1, hε1, hvar⟩ := leaf_339_lemma4_variant
  refine ⟨min (1 / 100) ε1, lt_min (by norm_num) hε1, ?_⟩
  intro ε hε hεlt A0 B c1 c2 M N Ml Nl Ll 𝒮 hc1 hc2 hfam hprod hcase h339 hsmall
  have hε0 : ε < 1 / 100 := lt_of_lt_of_le hεlt (min_le_left _ _)
  have hεv : ε < ε1 := lt_of_lt_of_le hεlt (min_le_right _ _)
  exact hvar ε hε hεv B c1 c2 M N Ml Nl Ll 𝒮 hc1 hc2 hfam hprod
    (fun x c hc => (hcase x c hc).1)
    (leaf_339_qT_range ε hε hε0 A0 𝒮
      (fun x c hc => ⟨(hcase x c hc).1, (hcase x c hc).2.1, (hcase x c hc).2.2.2.1⟩))
    h339 hsmall
    (leaf_long_fourth_moment ε hε hε0 A0 c1 c2 Ll 𝒮 hc1 hc2 hcase hsmall)

#print axioms leaf_339_qT_range
#print axioms lemma10_small_L_339_split

end LeanLab.BakerHarmanPintz1997