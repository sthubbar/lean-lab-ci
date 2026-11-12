import LeanLab.MissingDigit.Burst8Minor

/-!
# Burst 9, Kim's Theorem 1.1 with `5/8`, as a conditional entry candidate

Paper: P0057, J. Kim, Goldbach's problem in short intervals for numbers with a missing digit,
arXiv 2412.19975v1. This file packages `Burst8Minor.kim_thm1_1_58b : D4Bound (5 / 8) 7` as a
theorem with NO sorry in its proof, `kim_thm1_1_58_conditional`, whose two cited inputs appear as
explicit hypotheses:

* `Prop21_58`: exactly the statement of the leaf `Burst8Range58.prop_2_1_58`, which is
  Matomäki, Shao, Tao and Teräväinen, Higher uniformity of arithmetic functions in short
  intervals I, Forum Math. Pi 11 (2023), arXiv 2204.03754, Theorem 1.1 (iii) with `k = 4`,
  `θ = 5/8` and the linear phase `e(nα)`, as printed; it is Kim's Proposition 2.1, page 7, in
  the range `X^{5/8+ε} ≤ H`.
* `MainTermBound`: exactly the statement of the leaf `Burst8P2.main_term_bound`, Kim's
  Section 2.2, displays (2.8) to (2.11), pages 10 and 11.

The proof redoes the assembly of `kim_thm1_1_58b`. The old proof calls the two sorry constants
directly inside `Burst8P23.major_arcs_bound_p4` and `Burst8Range58.prop_2_2_58`, so those two
are re-threaded here as `major_arcs_bound_p4_of` and `prop_2_2_58_of`, with the same proofs and
the hypotheses in place of the sorry constants. No old declaration is changed.

AI wrote this Lean code. Binary Goldbach is OPEN; Kim's Theorem 1.1 is a divisor sum bound over
a missing digit set, not progress on binary Goldbach itself.
-/

namespace LeanLab.MissingDigit.Burst9Entry58

open Finset Real MeasureTheory Filter
open LeanLab.MissingDigit LeanLab.MissingDigit.Burst4Split LeanLab.MissingDigit.Burst8P2
  LeanLab.MissingDigit.Burst8L17 LeanLab.MissingDigit.Burst8Major
  LeanLab.MissingDigit.Burst8P23 LeanLab.MissingDigit.Burst8Range58
  LeanLab.MissingDigit.Burst8Minor

attribute [local instance] Classical.propDecidable

/-! ### The two cited inputs, as Props -/

/-- Cited input 1. MSTT, Forum Math. Pi 11 (2023) e29, arXiv 2204.03754, Theorem 1.1 (iii) as
printed, with `k = 4`, `θ = 5/8` and the phase `e(nα)`: for `X^{5/8+ε} ≤ H ≤ X^{1-ε}`,
`sup_α |∑_{X ≤ n ≤ X+H} (d₄(n) - d♯₄(n)) e(nα)| ≪_ε H X^{-cε}`. This is Kim's Proposition 2.1,
P0057 page 7, in the range `X^{5/8+ε} ≤ H`. The statement is word for word the type of the
leaf `Burst8Range58.prop_2_1_58`. -/
def Prop21_58 : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ c : ℝ, 0 < c ∧
    ∃ C : ℝ, ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ H : ℝ,
      (X : ℝ) ^ ((5 : ℝ) / 8 + ε) ≤ H → H ≤ (X : ℝ) ^ (1 - ε) → ∀ α : ℝ,
        ‖S4 X H α - S4sharp ε X H α‖ ≤ C * H * (X : ℝ) ^ (-(c * ε))

/-- Cited input 2. Kim, P0057, Section 2.2, displays (2.8) to (2.11), pages 10 and 11: the main
term of Proposition 2.4 is `≪ (log X)^7 |[X,X+H]^*|`. The statement is word for word the type
of the leaf `Burst8P2.main_term_bound`, in the range `X^{3/5+ε} ≤ H`, which contains the range
`X^{5/8+ε} ≤ H` used here. -/
def MainTermBound : Prop :=
  ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ, ∀ g b : ℕ,
    g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∃ C : ℝ, ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((3 : ℝ) / 5 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ‖∑ n ∈ starSet g b (g ^ k) H, mainK ε (g ^ k) H n‖ ≤
        C * Real.log ((g ^ k : ℕ) : ℝ) ^ 7 * (starSet g b (g ^ k) H).card

/-- The leaf `prop_2_1_58` inhabits `Prop21_58`. -/
example : Prop21_58 := Burst8Range58.prop_2_1_58

/-- The leaf `main_term_bound` inhabits `MainTermBound`. -/
example : MainTermBound := Burst8P2.main_term_bound

/-- Both Props are definitionally the types of the leaves. -/
example : Prop21_58 = type_of% Burst8Range58.prop_2_1_58 := rfl
example : MainTermBound = type_of% Burst8P2.main_term_bound := rfl

/-! ### Re-threaded intermediate lemmas -/

/-- Kim, Proposition 2.4 with Section 2.2, the major arc leaf, page 9 to 11: the same statement
and the same proof as `Burst8P23.major_arcs_bound_p4`, from the PROVED `prop_2_4_p4` and
`err_small`, with the cited `MainTermBound`, Kim Section 2.2 displays (2.8) to (2.11), as a
hypothesis. CONDITIONAL ON `MainTermBound`. -/
theorem major_arcs_bound_p4_of (hmain : MainTermBound) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ,
    ∀ g b : ℕ, g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∃ C : ℝ, ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((3 : ℝ) / 5 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ‖∑ n ∈ starSet g b (g ^ k) H, majorInt ε (g ^ k) H n‖ ≤
        C * Real.log ((g ^ k : ℕ) : ℝ) ^ 7 * (starSet g b (g ^ k) H).card := by
  obtain ⟨e1, he1, h24⟩ := prop_2_4_p4
  obtain ⟨e2, he2, hmt⟩ := hmain
  refine ⟨min (min e1 e2) (3 / 80), lt_min (lt_min he1 he2) (by norm_num),
    fun ε hε hεε => ?_⟩
  have hε1 : ε < e1 := lt_of_lt_of_le hεε (le_trans (min_le_left _ _) (min_le_left _ _))
  have hε2 : ε < e2 := lt_of_lt_of_le hεε (le_trans (min_le_left _ _) (min_le_right _ _))
  have hε3 : ε < 3 / 80 := lt_of_lt_of_le hεε (min_le_right _ _)
  obtain ⟨g1, hg1⟩ := h24 ε hε hε1
  obtain ⟨g2, hg2⟩ := hmt ε hε hε2
  refine ⟨max (max g1 g2) 3, fun g b hg hb2 hbg => ?_⟩
  have hgg1 : g1 ≤ g := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hg
  have hgg2 : g2 ≤ g := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hg
  have hg3 : 3 ≤ g := le_trans (le_max_right _ _) hg
  obtain ⟨C1, K1, hK1⟩ := hg1 g b hgg1 hb2 hbg
  obtain ⟨C2, K2, hK2⟩ := hg2 g b hgg2 hb2 hbg
  obtain ⟨K3, hK3⟩ := err_small hε hε3 hg3 hb2 hbg C1
  refine ⟨1 + max C2 0, max (max K1 K2) (max K3 1), fun k H hk hlo hhi => ?_⟩
  have hk1 : K1 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hk2 : K2 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hk3 : K3 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk4 : 1 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  obtain ⟨hH1, hHX, -⟩ := range_facts hg3 hk4 hε (by norm_num) hlo hhi
  have b1 := hK1 k H hk1 hlo hhi
  have b2 := hK2 k H hk2 hlo hhi
  have b3 := hK3 k H hk3 hlo hhi
  set X : ℝ := ((g ^ k : ℕ) : ℝ)
  set N : ℝ := ((starSet g b (g ^ k) H).card : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hX3 : (3 : ℝ) ≤ X := by
    have : 3 ≤ g ^ k := le_trans hg3 (Nat.le_self_pow (by omega) g)
    simp only [X]; exact_mod_cast this
  have hL : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact le_trans (le_of_lt (lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num))) hX3
  have hL7 : 1 ≤ Real.log X ^ 7 := one_le_pow₀ hL
  have htri : ‖∑ n ∈ starSet g b (g ^ k) H, majorInt ε (g ^ k) H n‖ ≤
      ‖(∑ n ∈ starSet g b (g ^ k) H, majorInt ε (g ^ k) H n) -
          ∑ n ∈ starSet g b (g ^ k) H, mainK ε (g ^ k) H n‖ +
        ‖∑ n ∈ starSet g b (g ^ k) H, mainK ε (g ^ k) H n‖ := by
    have := norm_add_le ((∑ n ∈ starSet g b (g ^ k) H, majorInt ε (g ^ k) H n) -
          ∑ n ∈ starSet g b (g ^ k) H, mainK ε (g ^ k) H n)
        (∑ n ∈ starSet g b (g ^ k) H, mainK ε (g ^ k) H n)
    rwa [sub_add_cancel] at this
  have hC2 : C2 * Real.log X ^ 7 * N ≤ max C2 0 * Real.log X ^ 7 * N := by
    have : 0 ≤ Real.log X ^ 7 * N := by positivity
    nlinarith [le_max_left C2 0]
  have hC20 : 0 ≤ max C2 0 := le_max_right _ _
  have hN7 : N ≤ Real.log X ^ 7 * N := by nlinarith
  calc ‖∑ n ∈ starSet g b (g ^ k) H, majorInt ε (g ^ k) H n‖
      ≤ N + max C2 0 * Real.log X ^ 7 * N := by linarith
    _ ≤ (1 + max C2 0) * Real.log X ^ 7 * N := by nlinarith

/-- The major arc leaf in the range `X^{5/8+ε} ≤ H`: same statement and proof as
`Burst8Range58.major_arcs_bound_58`, from `major_arcs_bound_p4_of`. CONDITIONAL ON
`MainTermBound`, Kim Section 2.2. -/
theorem major_arcs_bound_58_of (hmain : MainTermBound) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ,
    ∀ g b : ℕ, g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∃ C : ℝ, ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((5 : ℝ) / 8 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ‖∑ n ∈ starSet g b (g ^ k) H, majorInt ε (g ^ k) H n‖ ≤
        C * Real.log ((g ^ k : ℕ) : ℝ) ^ 7 * (starSet g b (g ^ k) H).card := by
  obtain ⟨e, he, h⟩ := major_arcs_bound_p4_of hmain
  refine ⟨e, he, fun ε hε hεe => ?_⟩
  obtain ⟨g₀, hg₀⟩ := h ε hε hεe
  refine ⟨g₀, fun g b hg hb hbg => ?_⟩
  obtain ⟨C, K, hK⟩ := hg₀ g b hg hb hbg
  exact ⟨C, K, fun k H hk hlo hhi => hK k H hk (lo_mono (by omega) hlo) hhi⟩

/-- Kim, Proposition 2.2 in the range `X^{5/8+ε} ≤ H ≤ X^{1-ε}`, display (2.2), page 8: same
statement and proof as `Burst8Range58.prop_2_2_58`, from the PROVED `lemma_1_7_weak` and
`tail_smallS`, with the cited `Prop21_58`, MSTT arXiv 2204.03754 Theorem 1.1 (iii), as a
hypothesis. CONDITIONAL ON `Prop21_58`. -/
theorem prop_2_2_58_of (h21' : Prop21_58) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ, ∀ g b : ℕ,
    g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∀ η : ℝ, 0 < η → ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
      ((g ^ k : ℕ) : ℝ) ^ ((5 : ℝ) / 8 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
      ‖∑ n ∈ starSet g b (g ^ k) H,
          ∫ α in (0 : ℝ)..1, (S4 (g ^ k) H α - S4sharp ε (g ^ k) H α) * eC (-(n * α))‖ ≤
        η * (starSet g b (g ^ k) H).card := by
  obtain ⟨ε₁, hε₁, h21⟩ := h21'
  set g₁ : ℕ := 3
  refine ⟨ε₁, hε₁, fun ε hε hεε => ?_⟩
  obtain ⟨c, hc, C, X₀, hC⟩ := h21 ε hε hεε
  obtain ⟨g₂, hg₂3, htail⟩ := tail_smallS (by norm_num : (1 : ℝ) ≤ 4) (mul_pos hc hε)
  refine ⟨max g₁ g₂, fun g b hg hb2 hbg η hη => ?_⟩
  have hg1 : g₁ ≤ g := le_trans (le_max_left _ _) hg
  have hg2 : g₂ ≤ g := le_trans (le_max_right _ _) hg
  have hg3 : 3 ≤ g := le_trans hg₂3 hg2
  obtain ⟨C₂, hC₂⟩ := lemma_1_7_weak hg3 hb2 hbg
  obtain ⟨K₁, hK₁⟩ := htail g b hg2 hb2 hbg (C * C₂) η hη
  refine ⟨max K₁ (max X₀ 1), fun k H hk hlo hhi => ?_⟩
  have hkK : K₁ ≤ k := le_trans (le_max_left _ _) hk
  have hkX : X₀ ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk1 : 1 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  obtain ⟨hH1, hHX, hkg⟩ := range_facts hg3 hk1 hε (by norm_num) hlo hhi
  have hb := hC (g ^ k) (le_trans hkX hkg) H hlo hhi
  set X : ℝ := ((g ^ k : ℕ) : ℝ)
  set M : ℝ := C * H * X ^ (-(c * ε))
  have hM0 : 0 ≤ M := le_trans (norm_nonneg _) (hb 0)
  have hF : Continuous (fun α => S4 (g ^ k) H α - S4sharp ε (g ^ k) H α) :=
    (S4_continuous _ _).sub (S4sharp_cont _ _ _)
  simp_rw [intervalIntegral.integral_of_le (zero_le_one' ℝ)]
  refine le_trans (norm_sum_setIntegral_le (measurableSet_Ioc) Set.Ioc_subset_Icc_self _ hF _
    (fun α _ => hb α)) ?_
  rw [setIntegral_Ioc01_norm]
  have hL := hC₂ k H hH1 hHX
  have h2 := hK₁ k H hkK hH1 hHX
  calc M * ∫ α in (0 : ℝ)..1, ‖∑ n ∈ starSet g b (g ^ k) H, eC (n * α)‖
      ≤ M * (C₂ * ((starSet g b (g ^ k) H).card : ℝ) ^ thetaS 4 g) :=
        mul_le_mul_of_nonneg_left hL hM0
    _ = C * C₂ * H * X ^ (-(c * ε)) * ((starSet g b (g ^ k) H).card : ℝ) ^ thetaS 4 g := by
        ring
    _ ≤ _ := h2

/-- The assembly of Kim's Theorem 1.1, page 8, display (2.1) split as minor arc error,
major arcs and minor arcs, in the range `X^{5/8+ε} ≤ H`: the same proof as
`Burst8Minor.kim_thm1_1_58b`, with its three leaves taken as hypotheses `h22`, `hmaj`, `h25`.
These are the statements of `Burst8Range58.prop_2_2_58`, `Burst8Range58.major_arcs_bound_58`
and `Burst8Minor.prop_2_5_58b`. -/
theorem assembly_58
    (h22 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ, ∀ g b : ℕ,
      g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∀ η : ℝ, 0 < η → ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
        ((g ^ k : ℕ) : ℝ) ^ ((5 : ℝ) / 8 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
        ‖∑ n ∈ starSet g b (g ^ k) H,
            ∫ α in (0 : ℝ)..1, (S4 (g ^ k) H α - S4sharp ε (g ^ k) H α) * eC (-(n * α))‖ ≤
          η * (starSet g b (g ^ k) H).card)
    (hmaj : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ,
      ∀ g b : ℕ, g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∃ C : ℝ, ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
        ((g ^ k : ℕ) : ℝ) ^ ((5 : ℝ) / 8 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
        ‖∑ n ∈ starSet g b (g ^ k) H, majorInt ε (g ^ k) H n‖ ≤
          C * Real.log ((g ^ k : ℕ) : ℝ) ^ 7 * (starSet g b (g ^ k) H).card)
    (h25 : ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → ∃ g₀ : ℕ, ∀ g b : ℕ,
      g₀ ≤ g → 2 ≤ b → b ≤ g - 1 → ∀ η : ℝ, 0 < η → ∃ K₀ : ℕ, ∀ (k : ℕ) (H : ℝ), K₀ ≤ k →
        ((g ^ k : ℕ) : ℝ) ^ ((5 : ℝ) / 8 + ε) ≤ H → H ≤ ((g ^ k : ℕ) : ℝ) ^ (1 - ε) →
        ‖∑ n ∈ starSet g b (g ^ k) H, minorInt ε (g ^ k) H n‖ ≤
          η * (starSet g b (g ^ k) H).card) :
    D4Bound (5 / 8) 7 := by
  obtain ⟨e1, he1, h1⟩ := h22
  obtain ⟨e2, he2, h2⟩ := hmaj
  obtain ⟨e3, he3, h3⟩ := h25
  intro ε hε
  set ε' : ℝ := min ε (min e1 (min e2 e3)) / 2 with hε'
  have hmin_pos : 0 < min ε (min e1 (min e2 e3)) := lt_min hε (lt_min he1 (lt_min he2 he3))
  have hε'pos : 0 < ε' := by positivity
  have hε'lt : ε' < min ε (min e1 (min e2 e3)) := by rw [hε']; linarith
  have hε'1 : ε' < e1 := lt_of_lt_of_le hε'lt (le_trans (min_le_right _ _) (min_le_left _ _))
  have hε'2 : ε' < e2 := lt_of_lt_of_le hε'lt
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hε'3 : ε' < e3 := lt_of_lt_of_le hε'lt
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_right _ _)))
  have hε'ε : ε' < ε := lt_of_lt_of_le hε'lt (min_le_left _ _)
  obtain ⟨g1, hg1⟩ := h1 ε' hε'pos hε'1
  obtain ⟨g2, hg2⟩ := h2 ε' hε'pos hε'2
  obtain ⟨g3, hg3⟩ := h3 ε' hε'pos hε'3
  refine ⟨max g1 (max g2 g3), fun g b hg hb2 hbg A₁ A₂ hA₁ hA₂ => ?_⟩
  have hgg1 : g1 ≤ g := le_trans (le_max_left _ _) hg
  have hgg2 : g2 ≤ g := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hg
  have hgg3 : g3 ≤ g := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hg
  have hg2' : 2 ≤ g := by omega
  obtain ⟨K1, hK1⟩ := hg1 g b hgg1 hb2 hbg 1 one_pos
  obtain ⟨C, K2, hK2⟩ := hg2 g b hgg2 hb2 hbg
  obtain ⟨K3, hK3⟩ := hg3 g b hgg3 hb2 hbg 1 one_pos
  -- `X = g^k` tends to infinity, so eventually `X^{ε-ε'} ≥ max (1/A₁) A₂` and `X ≥ 3`.
  have hX : Filter.Tendsto (fun k : ℕ => ((g ^ k : ℕ) : ℝ)) Filter.atTop Filter.atTop := by
    have : Filter.Tendsto (fun k : ℕ => (g : ℝ) ^ k) Filter.atTop Filter.atTop :=
      tendsto_pow_atTop_atTop_of_one_lt (by exact_mod_cast (by omega : 1 < g))
    simpa using this
  have hXc := (tendsto_rpow_atTop (by linarith : 0 < ε - ε')).comp hX
  obtain ⟨K4, hK4⟩ := Filter.eventually_atTop.1
    (hXc.eventually_ge_atTop (max (1 / A₁) A₂))
  obtain ⟨K5, hK5⟩ := Filter.eventually_atTop.1 (hX.eventually_ge_atTop 3)
  refine ⟨max C 0 + 2, max K1 (max K2 (max K3 (max K4 K5))), fun k H hk hlo hhi => ?_⟩
  have hk1 : K1 ≤ k := le_trans (le_max_left _ _) hk
  have hk2 : K2 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk3 : K3 ≤ k := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _))) hk
  have hk4 : K4 ≤ k := le_trans (le_trans (le_max_left _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) hk
  have hk5 : K5 ≤ k := le_trans (le_trans (le_max_right _ _) (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_right _ _)))) hk
  set X : ℝ := ((g ^ k : ℕ) : ℝ) with hXdef
  have hX3 : (3 : ℝ) ≤ X := hK5 k hk5
  have hXpos : 0 < X := by linarith
  have hXpow : max (1 / A₁) A₂ ≤ X ^ (ε - ε') := hK4 k hk4
  have hA1 : 1 / A₁ ≤ X ^ (ε - ε') := le_trans (le_max_left _ _) hXpow
  have hA2 : A₂ ≤ X ^ (ε - ε') := le_trans (le_max_right _ _) hXpow
  -- the hypotheses of the leaves at `ε'`
  have hlo' : X ^ ((5 : ℝ) / 8 + ε') ≤ H := by
    refine le_trans ?_ hlo
    have hsplit : X ^ ((5 : ℝ) / 8 + ε) = X ^ ((5 : ℝ) / 8 + ε') * X ^ (ε - ε') := by
      rw [← Real.rpow_add hXpos]; ring_nf
    rw [hsplit]
    have h1 : 1 ≤ A₁ * X ^ (ε - ε') := by
      have := mul_le_mul_of_nonneg_left hA1 hA₁.le
      rwa [mul_one_div_cancel hA₁.ne'] at this
    have hp : 0 ≤ X ^ ((5 : ℝ) / 8 + ε') := (Real.rpow_pos_of_pos hXpos _).le
    nlinarith
  have hhi' : H ≤ X ^ (1 - ε') := by
    refine le_trans hhi ?_
    have hsplit : X ^ (1 - ε') = X ^ (1 - ε) * X ^ (ε - ε') := by
      rw [← Real.rpow_add hXpos]; ring_nf
    rw [hsplit]
    have hp : 0 ≤ X ^ (1 - ε) := (Real.rpow_pos_of_pos hXpos _).le
    nlinarith
  have b1 := hK1 k H hk1 hlo' hhi'
  have b2 := hK2 k H hk2 hlo' hhi'
  have b3 := hK3 k H hk3 hlo' hhi'
  have hdec := sum_decomp ε' (g ^ k) g b H
  set N : ℝ := ((starSet g b (g ^ k) H).card : ℝ)
  have hN : 0 ≤ N := Nat.cast_nonneg _
  have hL : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact le_trans (le_of_lt (lt_of_lt_of_le Real.exp_one_lt_d9 (by norm_num))) hX3
  have hL7 : 1 ≤ Real.log X ^ 7 := one_le_pow₀ hL
  have hS : (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ)) ≤
      1 * N + C * Real.log X ^ 7 * N + 1 * N := by
    have hnn : 0 ≤ ∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ) :=
      Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _
    calc (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ))
        = ‖((∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ) : ℝ) : ℂ)‖ := by
          rw [Complex.norm_real, Real.norm_of_nonneg hnn]
      _ ≤ _ := by
          rw [hdec]
          refine le_trans (norm_add₃_le) ?_
          linarith
  have hC : C * Real.log X ^ 7 * N ≤ max C 0 * Real.log X ^ 7 * N := by
    have : 0 ≤ Real.log X ^ 7 * N := by positivity
    nlinarith [le_max_left C 0]
  have hC0 : 0 ≤ max C 0 := le_max_right _ _
  calc (∑ n ∈ starSet g b (g ^ k) H, (dk 4 n : ℝ))
      ≤ 1 * N + C * Real.log X ^ 7 * N + 1 * N := hS
    _ ≤ (max C 0 + 2) * Real.log X ^ 7 * N := by nlinarith

/-! ### The conditional entry candidate -/

/-- CONDITIONAL ENTRY CANDIDATE. Kim, P0057 arXiv 2412.19975v1, Theorem 1.1 with `5/8` in
place of `3/5`: for every `ε > 0` there is `g₀` such that for `g ≥ g₀`, every missing digit
`b ∈ {2,…,g-1}` and fixed `A₁, A₂ > 0`, `∑_{n ∈ [X,X+H]^*} d₄(n) ≪ (log X)^7 |[X,X+H]^*|` for
`X = g^k` large and `A₁ X^{5/8+ε} ≤ H ≤ A₂ X^{1-ε}`. Proof with no sorry, CONDITIONAL ON
exactly two cited inputs given as hypotheses:

* `h21 : Prop21_58`, MSTT arXiv 2204.03754 Theorem 1.1 (iii) as printed, `k = 4`, `θ = 5/8`;
* `hmain : MainTermBound`, Kim Section 2.2, displays (2.8) to (2.11).

The minor arc input, Proposition 2.5, is the PROVED `Burst8Minor.prop_2_5_58b`. Kim's printed
exponent `3/5` needs the QUESTION on Proposition 2.1 resolved; see the note
research/burst-20261112/MissingDigit-kim_thm1_1_58b.md. -/
theorem kim_thm1_1_58_conditional (h21 : Prop21_58) (hmain : MainTermBound) :
    D4Bound (5 / 8) 7 :=
  assembly_58 (prop_2_2_58_of h21) (major_arcs_bound_58_of hmain) prop_2_5_58b

/-- Instantiating the hypotheses with the cited leaves recovers `kim_thm1_1_58b`'s statement. -/
example : D4Bound (5 / 8) 7 :=
  kim_thm1_1_58_conditional Burst8Range58.prop_2_1_58 Burst8P2.main_term_bound

#check @kim_thm1_1_58_conditional

#print axioms major_arcs_bound_p4_of
#print axioms major_arcs_bound_58_of
#print axioms prop_2_2_58_of
#print axioms assembly_58
#print axioms prop_2_5_58b
#print axioms kim_thm1_1_58_conditional

end LeanLab.MissingDigit.Burst9Entry58
