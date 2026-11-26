/-
DQ5 decisions for ExceptionalSet, design queue item DQ5, run 20261119T0802Z-29270.
Source: P0082, Brüdern and Perelli 1998, Ann. Inst. Fourier 48, pages 359, 362 to 364, 368 to 371.

Part A. Re-split of `U1539.lemma9`, page 370. The old SPLIT_lemma9 leaf
`leaf_height_domination` is FALSE, see HeightDominationFalse52. The new split keeps the bound
on `h` inside the large value leaf, as the paper does: display 41 and the truncation with
Δ equal to ℰ to the minus 1/3 give a shift `h` with `|h| ≤ ℰ^(2/3)` at which the full sum
`PhiDQ5` is large. The second leaf is the Theorem 2 step on shifted frequencies. The size
comparison now runs the true way round: ℰ^(2/3) is below 2 X^δ plus 2 eventually, proved
here, so the shifted frequency stays inside the Theorem 2 range. `lemma9_of_dq5_leaves`
proves `Lemma9` from the two leaves with no other open step.

Part B. `U1539.lemma10`, Karacuba, and
`UpJ200.Decomp527a.leaf_pointwise_major_character`, Lemma 7 pages 362 to 364, are accepted
as NAMED HYPOTHESES `Lemma10DQ5` and `PointwiseMajorCharacterDQ5`, each with a match
theorem. Theorem 2 and the pointwise lower bound of Lemma 7 are proved from them as explicit
arguments. CONDITIONAL, never PROVED. `U1539.lemma4` is accepted as the named hypothesis
`Lemma4DQ5`; it is the input of display 41, so it lives inside leaf A of Part A.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.ExceptionalSet.State1539
import LeanLab.ExceptionalSet.DQLemma9Decisions
import LeanLab.ExceptionalSet.UpJ200.Decomp527a

namespace LeanLab.ExceptionalSet.U1539

open Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-! ## Part A. Re-split of Lemma 9, P0082 page 370 -/

/-- The full sum `Φ(β) = Σ_{N/2 < n ≤ N} e(β F(n))` of display 41, page 370. -/
noncomputable def PhiDQ5 (γ : ℝ) (N : ℕ) (β : ℝ) : ℂ :=
  ∑ n ∈ Finset.Ioc (N / 2) N, eC (β * F γ n)

/-- LEAF A of the DQ5 split of `lemma9`, page 370 displays 40 and 41 with Lemma 4.
Plain math: for small δ and all small κ, eventually, if `|α| ≤ X^δ` and the even sum
`Φ_e(α)` exceeds `N ℰ^(-1/3)`, then some integer `h` with `|h| ≤ ℰ^(2/3)` has
`|Φ(α - h/2)| > N ℰ^(-1)`. The bound on `h` is part of this leaf. DQ5 open statement for
provers, carries sorry on purpose. -/
theorem leaf_large_value_shift_dq5 :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ α : ℝ, |α| ≤ F γ N ^ δ → N * calE γ κ N ^ (-(1 / 3 : ℝ)) < ‖Phie γ N α‖ →
          ∃ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (2 / 3 : ℝ) ∧
            N * calE γ κ N ^ (-(1 : ℝ)) < ‖PhiDQ5 γ N (α - h / 2)‖ := by
  intro γ hγ₁ hγ₂
  obtain ⟨δ₀, hδ₀, hA⟩ := DQLemma9.large_value_shift_of_lemma4 lemma4 γ hγ₁ hγ₂
  refine ⟨δ₀, hδ₀, fun δ hδ hδlt => ?_⟩
  obtain ⟨κ₀, hκ₀, hA⟩ := hA δ hδ hδlt
  refine ⟨κ₀, hκ₀, fun κ hκ hκle => ?_⟩
  obtain ⟨N₀, hN₀⟩ := hA κ hκ hκle
  refine ⟨N₀, fun N hN α hα hlarge => ?_⟩
  obtain ⟨h, hh, hbig⟩ := hN₀ N hN α hα hlarge
  exact ⟨h, hh, hbig⟩

/-- LEAF B of the DQ5 split of `lemma9`, page 370 last paragraph, Theorem 2 on the window.
Plain math: for `0 < δ < γ - 1` and all small κ, eventually, every β with
`X^(δ-1) < |β| ≤ 2 X^δ + 2` has `|Φ(β)| ≤ N ℰ^(-1)`. DQ5 open statement for provers,
carries sorry on purpose. -/
theorem leaf_shift_minor_dq5 :
    ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ δ : ℝ, 0 < δ → δ < γ - 1 →
      ∃ κ₁ : ℝ, 0 < κ₁ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₁ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ β : ℝ, F γ N ^ (δ - 1) < |β| → |β| ≤ 2 * F γ N ^ δ + 2 →
          ‖PhiDQ5 γ N β‖ ≤ N * calE γ κ N ^ (-(1 : ℝ)) := by
  unfold PhiDQ5
  exact DQLemma9.shift_minor_of_theorem2 theorem2

/-- Vacuity instance for the hypotheses of both leaves: `γ = 5/4`, `δ = 1/8 < γ - 1`. -/
theorem vacuity_dq5_leaves : (1 : ℝ) < 5 / 4 ∧ (5 / 4 : ℝ) < 3 / 2 ∧
    (0 : ℝ) < 1 / 8 ∧ (1 / 8 : ℝ) < 5 / 4 - 1 := by norm_num

/-- The true size comparison, page 370: eventually `ℰ^(2/3) < 2 X^δ + 2`. CLEAN. -/
theorem height_below_window_dq5 (γ : ℝ) (hγ₁ : 1 < γ) (δ κ : ℝ) (hδ : 0 < δ) :
    ∃ N₂ : ℕ, ∀ N : ℕ, N₂ ≤ N → calE γ κ N ^ (2 / 3 : ℝ) < 2 * F γ N ^ δ + 2 := by
  have ht : Tendsto (fun N : ℕ => δ * Real.log (N : ℝ) ^ (3 * γ - 3)) atTop atTop :=
    ((tendsto_rpow_atTop (by linarith : 0 < 3 * γ - 3)).comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).const_mul_atTop hδ
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (κ * (2 / 3)))
  refine ⟨max 2 N₀, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hrate := hN₀ N ((le_max_right _ _).trans hN)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have he : (3 - 2 * γ) + (3 * γ - 3) = γ := by ring
  have hexponent : (κ * Real.log (N : ℝ) ^ (3 - 2 * γ)) * (2 / 3) ≤
      Real.log (N : ℝ) ^ γ * δ := by
    calc (κ * Real.log (N : ℝ) ^ (3 - 2 * γ)) * (2 / 3)
        = Real.log (N : ℝ) ^ (3 - 2 * γ) * (κ * (2 / 3)) := by ring
      _ ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) * (δ * Real.log (N : ℝ) ^ (3 * γ - 3)) :=
        mul_le_mul_of_nonneg_left hrate (Real.rpow_nonneg hlog.le _)
      _ = Real.log (N : ℝ) ^ γ * δ := by
        rw [mul_left_comm _ δ, ← Real.rpow_add hlog, he]
        ring
  have hreverse : calE γ κ N ^ (2 / 3 : ℝ) ≤ F γ N ^ δ := by
    rw [calE, F, ← Real.exp_mul, ← Real.exp_mul]
    exact Real.exp_le_exp.mpr hexponent
  have hpos : 0 < F γ N ^ δ := Real.rpow_pos_of_pos (Real.exp_pos _) δ
  linarith

/-- `Lemma9` from LEAF A and LEAF B, given as explicit arguments. CLEAN as an implication. -/
theorem lemma9_of_dq5_leaves
    (hA : ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ α : ℝ, |α| ≤ F γ N ^ δ → N * calE γ κ N ^ (-(1 / 3 : ℝ)) < ‖Phie γ N α‖ →
          ∃ h : ℤ, (|h| : ℝ) ≤ calE γ κ N ^ (2 / 3 : ℝ) ∧
            N * calE γ κ N ^ (-(1 : ℝ)) < ‖PhiDQ5 γ N (α - h / 2)‖)
    (hB : ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∀ δ : ℝ, 0 < δ → δ < γ - 1 →
      ∃ κ₁ : ℝ, 0 < κ₁ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₁ → ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        ∀ β : ℝ, F γ N ^ (δ - 1) < |β| → |β| ≤ 2 * F γ N ^ δ + 2 →
          ‖PhiDQ5 γ N β‖ ≤ N * calE γ κ N ^ (-(1 : ℝ))) :
    Lemma9 := by
  intro γ hγ₁ hγ₂
  obtain ⟨δ₀, hδ₀, hA⟩ := hA γ hγ₁ hγ₂
  refine ⟨min δ₀ (γ - 1), lt_min hδ₀ (by linarith), fun δ hδ hδlt => ?_⟩
  have hδA : δ < δ₀ := lt_of_lt_of_le hδlt (min_le_left _ _)
  have hδB : δ < γ - 1 := lt_of_lt_of_le hδlt (min_le_right _ _)
  obtain ⟨κ₀, hκ₀, hA⟩ := hA δ hδ hδA
  obtain ⟨κ₁, hκ₁, hB⟩ := hB γ hγ₁ hγ₂ δ hδ hδB
  set κ := min κ₀ κ₁
  have hκ : 0 < κ := lt_min hκ₀ hκ₁
  obtain ⟨NA, hNA⟩ := hA κ hκ (min_le_left _ _)
  obtain ⟨NB, hNB⟩ := hB κ hκ (min_le_right _ _)
  obtain ⟨NH, hNH⟩ := height_below_window_dq5 γ hγ₁ δ κ hδ
  refine ⟨κ, hκ, max NA (max NB NH), fun N hN α hα hlarge => ?_⟩
  have hNA' : NA ≤ N := (le_max_left _ _).trans hN
  have hNB' : NB ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNH' : NH ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  obtain ⟨h, hh, hbig⟩ := hNA N hNA' α hα hlarge
  refine ⟨h, hh, ?_⟩
  by_contra hfar
  rw [not_le] at hfar
  have hheight := hNH N hNH'
  have hFpos : 0 < F γ N ^ δ := Real.rpow_pos_of_pos (Real.exp_pos _) δ
  have hhalf : |(h : ℝ) / 2| ≤ F γ N ^ δ + 1 := by
    rw [abs_div, abs_two]
    linarith
  have hwin : |α - h / 2| ≤ 2 * F γ N ^ δ + 2 := by
    calc |α - h / 2| ≤ |α| + |(h : ℝ) / 2| := abs_sub _ _
      _ ≤ 2 * F γ N ^ δ + 2 := by linarith
  have hsmall := hNB N hNB' (α - h / 2) hfar hwin
  linarith

/-! ## Part B. Named hypotheses -/

/-- Named hypothesis, Lemma 10 of P0082 pages 370 to 371, Karacuba 1973 Theorem 1. CITED. -/
def Lemma10DQ5 : Prop :=
  ∀ θ Θ Θ₀ δ : ℝ, 0 < δ → δ < 1 → 0 < Θ → Θ < θ → θ < Θ₀ → Θ₀ < 1 →
    ∃ B c : ℝ, 0 < B ∧ 0 < c ∧ ∀ N : ℕ, 1 ≤ N → ∀ (f : ℝ → ℝ) (k : ℕ),
      KClass N θ Θ Θ₀ δ f k →
      ‖∑ n ∈ Finset.Ioc N (2 * N), eC (f n)‖ ≤ B * (N : ℝ) ^ (1 - c / (k : ℝ) ^ 2)

/-- Named hypothesis, Lemma 4 of P0082 page 359. CITED. -/
def Lemma4DQ5 : Prop :=
  ∀ γ : ℝ, 1 < γ → γ < 3 / 2 → ∃ κ B : ℝ, 0 < κ ∧ ∀ N : ℕ, 1 ≤ N → ∀ α : ℝ,
    F γ N ^ (-(1 / 2 : ℝ)) < |α| → |α| ≤ 1 → ∀ z₁ z₂ : ℝ, 0 ≤ z₂ → z₂ < z₁ → z₁ ≤ 1 →
      |(((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
          z₂ ≤ Int.fract (α * F γ n) ∧ Int.fract (α * F γ n) < z₁)).card : ℝ)
        - (z₁ - z₂) * N / 2| ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ))

/-- Match: the named hypothesis is definitionally the sealed `Lemma10`. CLEAN. -/
theorem lemma10_named_eq_dq5 : Lemma10DQ5 = Lemma10 := rfl

/-- Match: the named hypothesis is definitionally the sealed `Lemma4`. CLEAN. -/
theorem lemma4_named_eq_dq5 : Lemma4DQ5 = Lemma4 := rfl

/-- Match check against the sealed statement `U1539.lemma10`. Uses that CITED leaf. -/
theorem lemma10_named_match_dq5 : Lemma10DQ5 := lemma10

/-- Match check against the sealed statement `U1539.lemma4`. Uses that open leaf. -/
theorem lemma4_named_match_dq5 : Lemma4DQ5 := lemma4

/-- Theorem 2 of P0082 page 354, CONDITIONAL on the named hypothesis `Lemma10DQ5`. -/
theorem theorem2_of_named_dq5 (h10 : Lemma10DQ5) : Theorem2 :=
  theorem2_of_all_leaves h10

end LeanLab.ExceptionalSet.U1539

namespace LeanLab.ExceptionalSet.UpJ200.Decomp527a

open Real Finset
open LeanLab.ExceptionalSet.Supply465
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)

/-- Named hypothesis, the sealed statement of `leaf_pointwise_major_character`,
P0082 pages 362 to 364, Lemma 7 displays 20 and 21, for every `1 < γ < 3/2`. -/
def PointwiseMajorCharacterDQ5 : Prop :=
  ∀ γ : ℝ, 1 < γ → γ < 3 / 2 →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ F γ N ^ (6 * δ) ∧
            (r = 1 ∨ ∃ (_ : NeZero r) (χ : DirichletCharacter ℂ r),
              χ.IsPrimitive ∧ χ ^ 2 = 1 ∧ χ ≠ 1) ∧
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              let Y := (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j)
              (r = 1 → c * F γ N ≤ Y) ∧
              (r ≠ 1 → Int.gcd (nu γ n + j) r = 1 → c * F γ N ≤ Y) ∧
              (1 < Int.gcd (nu γ n + j) r →
                (∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + j) →
                  c * F γ N ≤ Y) ∧
              (1 < Int.gcd (nu γ n + j) r →
                (¬ ∃ p : ℕ, p.Prime ∧ p ∣ r ∧ 3 < p ∧ ¬ (p : ℤ) ∣ nu γ n + j) →
                (r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) →
                  c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤ Y)

/-- Match check: the named hypothesis is exactly the sealed leaf. Uses that leaf. -/
theorem pointwise_named_match_dq5 : PointwiseMajorCharacterDQ5 :=
  fun γ h1 h2 => leaf_pointwise_major_character γ h1 h2

/-- The pointwise lower bound of Lemma 7, P0082 pages 362 to 364, CONDITIONAL on the named
hypothesis `PointwiseMajorCharacterDQ5`. Same proof as `pointwise_lower_from_cases`. -/
theorem pointwise_lower_of_named_dq5 (hP : PointwiseMajorCharacterDQ5)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ F γ N ^ (6 * δ) ∧
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) → ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              ((r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) ∨
                (Int.gcd (nu γ n + j) r : ℝ) < (r : ℝ) / 24) →
              c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                  A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
  obtain ⟨δ₀, hδ₀, h⟩ := hP γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, h⟩ := h δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c, A, hc, hA, N₀, h⟩ := h κ hκ hκsmall
  refine ⟨c, A, hc, hA, max 2 N₀, fun N hN => ?_⟩
  obtain ⟨r, hr, hrP, hcharacter, hcases⟩ := h N (by omega)
  obtain ⟨k, u, hshape⟩ : ∃ k u : ℕ,
      r = 1 ∨ (r = 2 ^ k * u ∧ k ≤ 3 ∧ Odd u ∧ Squarefree u) := by
    rcases hcharacter with habsent | ⟨hrzero, χ, hprimitive, hreal, hnonprincipal⟩
    · exact ⟨0, 1, Or.inl habsent⟩
    · letI := hrzero
      obtain ⟨k, u, h⟩ := real_primitive_conductor r χ hprimitive hreal hnonprincipal
      exact ⟨k, u, Or.inr h⟩
  refine ⟨r, hr, hrP, fun j hj n hn he hm hgood => ?_⟩
  have hE : 1 ≤ calE γ κ N := by
    apply Real.one_le_exp
    exact mul_nonneg hκ.le (Real.rpow_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _)
  obtain ⟨ha, hb, hd, he⟩ := hcases j hj n hn he hm
  exact four_case_lower r k u (nu γ n + j) c (F γ N) (calE γ κ N) _
    hshape hc.le (Real.exp_pos _).le hE hgood ha hb hd he

end LeanLab.ExceptionalSet.UpJ200.Decomp527a
