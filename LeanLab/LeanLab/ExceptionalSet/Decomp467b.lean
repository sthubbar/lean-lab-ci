import LeanLab.ExceptionalSet.Decomp465a
import LeanLab.ExceptionalSet.Assembly446

/-!
P0082 pages 359 to 369, the remaining inputs of the major arc argument.
The discrepancy, character case bound and odd moment are explicit premises.
Every result below is CONDITIONAL ON the named premises in its statement.
No admitted theorem is used to supply one of them.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp467b
open Real Finset MeasureTheory
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F Solvable Theorem1)
open LeanLab.ExceptionalSet.U1539 (R1 nu nuOdd calE Lemma4)
open LeanLab.ExceptionalSet.DecompJ200
open LeanLab.ExceptionalSet.Supply465
open LeanLab.ExceptionalSet.Adjacent446 (evenAdjacent)

/-- P0082 pages360 to362, Lemma5. The two divisor means add.
CONDITIONAL ON the explicit discrepancy input h4. -/
theorem error_mean_raw (h4 : Lemma4) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) →
              ∑ n ∈ window γ N,
                (gammaOne r (F γ N ^ (6 * δ)) (nu γ n + j) +
                  gammaTwo r (F γ N ^ (6 * δ)) (nu γ n + j)) ≤
                    C * N * calE γ κ N ^ (-(1 / 2 : ℝ)) := by
  obtain ⟨δa, hδa, ha⟩ := gammaOne_mean_from_lemma4 h4 γ h1 h2
  obtain ⟨δb, hδb, hb⟩ := gammaTwo_mean_from_lemma4 h4 γ h1 h2
  refine ⟨min δa δb, lt_min hδa hδb, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κa, hκa, ha⟩ := ha δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κb, hκb, hb⟩ := hb δ hδ (hδsmall.trans_le (min_le_right _ _))
  refine ⟨min κa κb, lt_min hκa hκb, fun κ hκ hκsmall => ?_⟩
  obtain ⟨Ca, hCa, Na, ha⟩ := ha κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨Cb, hCb, Nb, hb⟩ := hb κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨Ca + Cb, add_pos hCa hCb, max Na Nb, fun N hN r hr hrP j hj => ?_⟩
  rw [sum_add_distrib]
  have haN := ha N ((le_max_left _ _).trans hN) r hr hrP j hj
  have hbN := hb N ((le_max_right _ _).trans hN) r hr hrP j hj
  calc
    _ ≤ Ca * N * calE γ κ N ^ (-(1 / 2 : ℝ)) +
        Cb * N * calE γ κ N ^ (-(1 / 2 : ℝ)) := add_le_add haN hbN
    _ = _ := by ring

/-- P0082 page362, completion of Lemma5 for the positive error envelope.
CONDITIONAL ON the explicit discrepancy input h4. -/
theorem error_mean (h4 : Lemma4) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ r : ℕ, 1 ≤ r → (r : ℝ) ≤ F γ N ^ (6 * δ) →
            ∀ j : ℤ, (j = 0 ∨ j = 1) →
              ∑ n ∈ window γ N,
                divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) ≤
                  C * N * calE γ κ N ^ (-(1 / 2 : ℝ)) := by
  simpa only [divisorError, gammaOne, gammaTwo] using error_mean_raw h4 γ h1 h2

section CharacterCases

variable (hpoint : ∀ (γ : ℝ), 1 < γ → γ < 3 / 2 →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c A : ℝ, 0 < c ∧ 0 < A ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∃ r : ℕ, 1 ≤ r ∧ (r : ℝ) ≤ F γ N ^ (6 * δ) ∧
            ∀ j : ℤ, (j = 0 ∨ j = 1) → ∀ n ∈ window γ N,
              Even (nu γ n + j) →
              ((nu γ n + j : ℤ) : ℝ) ≤ F γ N →
              ((r : ℝ) ≤ calE γ κ N ^ (1 / 7 : ℝ) ∨
                (Int.gcd (nu γ n + j) r : ℝ) < (r : ℝ) / 24) →
              c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
                (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
                  A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j))
variable (h4 : Lemma4)
include hpoint h4

/-- P0082 pages362 to364, Lemma7. The pointwise character cases, the
divisor mean and the large gcd count control each adjacent shift. CONDITIONAL. -/
theorem adjacent_count_from_inputs (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ j : ℤ, (j = 0 ∨ j = 1) →
            ((((window γ N).filter (fun n => Even (nu γ n + j))).filter (fun n =>
              (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re <
                c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                  B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  classical
  obtain ⟨δp, hδp, hp⟩ := hpoint γ h1 h2
  obtain ⟨δm, hδm, hm⟩ := error_mean h4 γ h1 h2
  obtain ⟨δg, hδg, hg⟩ := large_gcd_from_lemma4 h4 γ h1 h2
  refine ⟨min δp (min δm δg), lt_min hδp (lt_min hδm hδg), fun δ hδ hδsmall => ?_⟩
  obtain ⟨κp, hκp, hp⟩ := hp δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κm, hκm, hm⟩ := hm δ hδ
    (hδsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨κg, hκg, hg⟩ := hg δ hδ
    (hδsmall.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨min 1 (min κp (min κm κg)), lt_min zero_lt_one (lt_min hκp (lt_min hκm hκg)),
    fun κ hκ hκsmall => ?_⟩
  have hκ1 : κ ≤ 1 := hκsmall.trans (min_le_left _ _)
  have hκrest : κ ≤ min κp (min κm κg) := hκsmall.trans (min_le_right _ _)
  obtain ⟨c, A, hc, hA, Np, hp⟩ := hp κ hκ (hκrest.trans (min_le_left _ _))
  obtain ⟨C, hC, Nm, hm⟩ := hm κ hκ
    (hκrest.trans ((min_le_right _ _).trans (min_le_left _ _)))
  obtain ⟨B, hB, Ng, hg⟩ := hg κ hκ
    (hκrest.trans ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨c / 2, B + 1 + 2 * A * C / c, by positivity, by positivity,
    max 16 (max Np (max Nm Ng)), fun N hN j hj => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNp : Np ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNm : Nm ≤ N := (le_max_left _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  have hNg : Ng ≤ N := (le_max_right _ _).trans
    ((le_max_right _ _).trans ((le_max_right _ _).trans hN))
  obtain ⟨r, hr, hrP, hp⟩ := hp N hNp
  let X := F γ N
  let E := calE γ κ N
  let P := X ^ (6 * δ)
  let s := (window γ N).filter (fun n => Even (nu γ n + j))
  let g := fun n => divisorError r P (nu γ n + j)
  let rare := if (r : ℝ) ≤ E ^ (1 / 7 : ℝ) then ∅ else
    (window γ N).filter (fun n => (r : ℝ) / 24 ≤ (Int.gcd (nu γ n + j) r : ℝ))
  let t := rare ∪ {N}
  have hX : 0 < X := Real.exp_pos _
  have hE : 1 ≤ E := by
    apply Real.one_le_exp
    apply mul_nonneg hκ.le
    apply Real.rpow_nonneg
    exact Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hg0 : ∀ n ∈ window γ N, 0 ≤ g n := fun n _ =>
    divisorError_nonneg r P _ (Real.rpow_nonneg hX.le _)
  have hmean : ∑ n ∈ s, g n ≤ C * N * E ^ (-(1 / 2 : ℝ)) :=
    (sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun n hn _ => hg0 n hn)).trans
      (hm N hNm r hr hrP j hj)
  have hrare : (rare.card : ℝ) ≤ B * N * E ^ (-(1 / 12 : ℝ)) := by
    dsimp only [rare]
    split_ifs with hsmall
    · simp only [card_empty, Nat.cast_zero]
      positivity
    · exact hg N hNg r hr hrP (lt_of_not_ge hsmall) j hj
  have ht : (t.card : ℝ) ≤ (B + 1) * N * E ^ (-(1 / 12 : ℝ)) := by
    have hu : (t.card : ℝ) ≤ (rare.card : ℝ) + 1 := by
      exact_mod_cast (card_union_le rare {N}).trans_eq (by simp)
    have hscale := one_le_count_scale γ κ h1 hκ.le hκ1 N (by omega)
    change 1 ≤ (N : ℝ) * E ^ (-(1 / 12 : ℝ)) at hscale
    nlinarith
  apply count_coefficient s t
    (fun n => (R1 P X (nu γ n + j)).re) g c A C (B + 1) X E N
    hc hA hC.le hX hE (fun n hn => hg0 n (mem_filter.mp hn).1) hmean ht
  intro n hn hnt
  obtain ⟨hnw, hne⟩ := mem_filter.mp hn
  have hnnot : n ≠ N := by
    intro heq
    apply hnt
    exact mem_union.mpr (Or.inr (mem_singleton.mpr heq))
  have hnN : n < N := lt_of_le_of_ne (Decomp371a.window_upper γ h1 N (by omega) n hnw) hnnot
  have hrange := adjacent_le_X γ h1 N n hN16 hnw hnN j (by rcases hj with rfl | rfl <;> norm_num)
  apply hp j hj n hnw hne (by exact_mod_cast hrange)
  by_cases hsmall : (r : ℝ) ≤ E ^ (1 / 7 : ℝ)
  · exact Or.inl hsmall
  · apply Or.inr
    have : ¬ (r : ℝ) / 24 ≤ (Int.gcd (nu γ n + j) r : ℝ) := by
      intro hlarge
      apply hnt
      apply mem_union.mpr
      apply Or.inl
      dsimp only [rare]
      rw [if_neg hsmall]
      exact mem_filter.mpr ⟨hnw, hlarge⟩
    exact lt_of_not_ge this

/-- P0082 pages362 to364, Lemma7. One parity specialization of the
adjacent count with its discrepancy and character case inputs explicit. CONDITIONAL. -/
theorem even_index_from_inputs (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ((((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
            (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re <
              c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  obtain ⟨δ₀, hδ₀, h⟩ := adjacent_count_from_inputs hpoint h4 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, h⟩ := h δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c, B, hc, hB, N₀, h⟩ := h κ hκ hκsmall
  refine ⟨c, B, hc, hB, N₀, fun N hN => ?_⟩
  simpa only [add_zero] using h N hN 0 (Or.inl rfl)

/-- P0082 pages362 to364, Lemma7. One parity specialization of the
adjacent count with its discrepancy and character case inputs explicit. CONDITIONAL. -/
theorem odd_index_from_inputs (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ((((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
            (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
              c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  obtain ⟨δ₀, hδ₀, h⟩ := adjacent_count_from_inputs hpoint h4 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, h⟩ := h δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c, B, hc, hB, N₀, h⟩ := h κ hκ hκsmall
  refine ⟨c, B, hc, hB, N₀, fun N hN => ?_⟩
  simpa only [Int.even_add_one, Int.not_even_iff_odd] using h N hN 1 (Or.inr rfl)

/-- P0082 pages362 to364, Lemma7. Combining the disjoint index parities
gives the even coefficient bound. CONDITIONAL ON the explicit inputs. -/
theorem even_coefficient_from_inputs (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (((window γ N).filter (fun n : ℕ =>
            (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
              c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  classical
  obtain ⟨δe, hδe, he⟩ := even_index_from_inputs hpoint h4 γ h1 h2
  obtain ⟨δo, hδo, ho⟩ := odd_index_from_inputs hpoint h4 γ h1 h2
  refine ⟨min δe δo, lt_min hδe hδo, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κe, hκe, he⟩ := he δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κo, hκo, ho⟩ := ho δ hδ (hδsmall.trans_le (min_le_right _ _))
  refine ⟨min κe κo, lt_min hκe hκo, fun κ hκ hκsmall => ?_⟩
  obtain ⟨ce, Be, hce, hBe, Ne, he⟩ := he κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨co, Bo, hco, hBo, No, ho⟩ := ho κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨min ce co, Be + Bo, lt_min hce hco, add_pos hBe hBo, max Ne No, fun N hN => ?_⟩
  have hNe : Ne ≤ N := (le_max_left _ _).trans hN
  have hNo : No ≤ N := (le_max_right _ _).trans hN
  have hF : 0 ≤ F γ N := (Real.exp_pos _).le
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hR : 0 ≤ calE γ κ N ^ (-(1 / 10 : ℝ)) := (Real.rpow_pos_of_pos hE _).le
  have hstepE : min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
      ce * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_left _ _) hF) hR
  have hstepO : min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) ≤
      co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (min_le_right _ _) hF) hR
  have hA : ((((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
      (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
        min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
      Be * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
    have hsub : (((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card ≤
        (((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
          (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)).re <
            ce * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨hwin, hlt⟩ := Finset.mem_filter.mp hn
      have hpar : Even (nu γ n) := (Finset.mem_filter.mp hwin).2
      have hadj : evenAdjacent γ n = nu γ n := by simp [evenAdjacent, hpar]
      rw [hadj] at hlt
      exact Finset.mem_filter.mpr ⟨hwin, lt_of_lt_of_le hlt hstepE⟩
    exact (Nat.cast_le.mpr hsub).trans (he N hNe)
  have hB : ((((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
      (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
        min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
      Bo * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
    have hsub : (((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card ≤
        (((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
          (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
            co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card := by
      apply Finset.card_le_card
      intro n hn
      obtain ⟨hwin, hlt⟩ := Finset.mem_filter.mp hn
      have hpar : ¬ Even (nu γ n) := (Finset.mem_filter.mp hwin).2
      have hadj : evenAdjacent γ n = nu γ n + 1 := by simp [evenAdjacent, hpar]
      rw [hadj] at hlt
      exact Finset.mem_filter.mpr ⟨hwin, lt_of_lt_of_le hlt hstepO⟩
    exact (Nat.cast_le.mpr hsub).trans (ho N hNo)
  have hpart : (window γ N).filter (fun n : ℕ =>
      (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
        min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))) =
      (((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))) ∪
      (((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_union]
    constructor
    · rintro ⟨hnw, hb⟩
      by_cases hpar : Even (nu γ n)
      · exact Or.inl ⟨⟨hnw, hpar⟩, hb⟩
      · exact Or.inr ⟨⟨hnw, hpar⟩, hb⟩
    · rintro (⟨⟨hnw, _⟩, hb⟩ | ⟨⟨hnw, _⟩, hb⟩)
      · exact ⟨hnw, hb⟩
      · exact ⟨hnw, hb⟩
  have hdisj : Disjoint
      (((window γ N).filter (fun n : ℕ => Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))))
      (((window γ N).filter (fun n : ℕ => ¬ Even (nu γ n))).filter (fun n : ℕ =>
        (R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)).re <
          min ce co * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))) := by
    rw [Finset.disjoint_left]
    intro x hx1 hx2
    exact (Finset.mem_filter.mp (Finset.mem_filter.mp hx2).1).2
      (Finset.mem_filter.mp (Finset.mem_filter.mp hx1).1).2
  rw [hpart, Finset.card_union_of_disjoint hdisj]
  push_cast
  refine (add_le_add hA hB).trans_eq ?_
  ring

variable (hodd : ∀ (γ : ℝ), 1 < γ → γ < 3 / 2 →
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ window γ N,
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nuOdd γ n)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)))
include hodd

/-- P0082 page362, first sentence of the proof of Lemma7. The even
coefficient and the odd second moment give the adjacent sum. CONDITIONAL. -/
theorem coefficient_lower_from_inputs (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (((window γ N).filter (fun n : ℕ =>
            (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
              R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
                c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
            B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  classical
  obtain ⟨δe, hδe, he⟩ := even_coefficient_from_inputs hpoint h4 γ h1 h2
  obtain ⟨δo, hδo, ho⟩ := hodd γ h1 h2
  refine ⟨min δe δo, lt_min hδe hδo, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κe, hκe, he⟩ := he δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κo, hκo, ho⟩ := ho δ hδ (hδsmall.trans_le (min_le_right _ _))
  refine ⟨min κe κo, lt_min hκe hκo, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c, Be, hc, hBe, Ne, he⟩ := he κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨Bo, hBo, No, ho⟩ := ho κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨c / 2, Be + 16 * Bo / c ^ 2, by positivity, by positivity,
    max 2 (max Ne No), fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNe : Ne ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNo : No ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hE : 1 ≤ calE γ κ N := by
    apply Real.one_le_exp
    exact mul_nonneg hκ.le (Real.rpow_nonneg (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _)
  let f : ℕ → ℂ := fun n => R1 (F γ N ^ (6 * δ)) (F γ N) (evenAdjacent γ n)
  let g : ℕ → ℂ := fun n => R1 (F γ N ^ (6 * δ)) (F γ N) (nuOdd γ n)
  let T := c / 2 * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))
  have hpair := Adjacent446.bad_pair_count (window γ N) f g T
  have hrewrite (n : ℕ) : f n + g n =
      R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
        R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1) :=
    Adjacent446.adjacent_sum (R1 (F γ N ^ (6 * δ)) (F γ N)) γ n
  have htwo : 2 * T = c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) := by
    dsimp [T]
    ring
  simp_rw [hrewrite, htwo] at hpair
  have hodd := OddMoment446.odd_bad_count (window γ N) g c Bo (F γ N) (calE γ κ N) N
    hc hBo.le (Real.exp_pos _) hE (ho N hNo)
  have hpairR := Nat.cast_le (α := ℝ).mpr hpair
  push_cast at hpairR
  change _ ≤ _ at hodd
  have heN := he N hNe
  change (((window γ N).filter (fun n => (f n).re <
    c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤ _ at heN
  dsimp only [T] at hpairR
  refine hpairR.trans ((add_le_add heN hodd).trans ?_)
  ring_nf
  exact le_rfl

/-- P0082 page365, Lemma8. This is the exact sealed major bound conclusion
from the explicit discrepancy, character case and odd moment inputs. CONDITIONAL. -/
theorem major_bound_from_inputs (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ → ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (Eγ_major_block γ δ κ c₀ N : ℝ) ≤ B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  classical
  obtain ⟨δ₀, hδ₀, hcoeff⟩ := coefficient_lower_from_inputs hpoint h4 hodd γ h1 h2
  obtain ⟨κb, hκb, hboundary⟩ := Decomp404a.boundary_of_lemma4 h4 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κa, hκa, hcoeff⟩ := hcoeff δ hδ hδsmall
  refine ⟨min κa κb, lt_min hκa hκb, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c₀, Ba, hc₀, hBa, Na, ha⟩ :=
    hcoeff κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨Bb, hBb, Nb, hb⟩ :=
    hboundary κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨c₀, Ba + Bb, hc₀, add_pos hBa hBb, max 2 (max Na Nb), fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNa : Na ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNb : Nb ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hE : 1 < calE γ κ N := by
    unfold calE
    exact Real.one_lt_exp_iff.mpr (mul_pos hκ (Real.rpow_pos_of_pos hlog _))
  have hΔ : 0 < calE γ κ N ^ (-(1 / 8 : ℝ)) :=
    Real.rpow_pos_of_pos (lt_trans zero_lt_one hE) _
  have hΔ1 : calE γ κ N ^ (-(1 / 8 : ℝ)) < 1 := by
    rw [Real.rpow_def_of_pos (lt_trans zero_lt_one hE)]
    exact Real.exp_lt_one_iff.mpr (mul_neg_of_pos_of_neg (Real.log_pos hE) (by norm_num))
  let A := (window γ N).filter (fun n : ℕ =>
    (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
      R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)).re <
        c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))
  let B := (window γ N).filter (fun n : ℕ =>
    Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
      1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n))
  have hsubset : (window γ N).filter (fun n : ℕ =>
      (majorInt γ δ κ N n).re < c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))) ⊆ A ∪ B := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnW, hnmajor⟩
    by_cases hnB : n ∈ B
    · exact Finset.mem_union_right _ hnB
    · have hgood : ¬ (Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
          1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n)) := by
        intro hbad
        exact hnB (Finset.mem_filter.mpr ⟨hnW, hbad⟩)
      have hid := Decomp404a.major_identity γ δ κ N n hΔ hΔ1
        (le_of_not_gt (fun h => hgood (Or.inl h)))
        (le_of_not_gt (fun h => hgood (Or.inr h)))
      apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      exact ⟨hnW, by rwa [hid] at hnmajor⟩
  have hcard : (Eγ_major_block γ δ κ c₀ N : ℝ) ≤ (A.card : ℝ) + B.card := by
    exact_mod_cast (Finset.card_le_card hsubset).trans (Finset.card_union_le A B)
  have hpow : calE γ κ N ^ (-(1 / 8 : ℝ)) ≤ calE γ κ N ^ (-(1 / 12 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hE.le (by norm_num)
  calc
    _ ≤ (A.card : ℝ) + B.card := hcard
    _ ≤ Ba * N * calE γ κ N ^ (-(1 / 12 : ℝ)) +
        Bb * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := add_le_add (ha N hNa) (hb N hNb)
    _ ≤ Ba * N * calE γ κ N ^ (-(1 / 12 : ℝ)) +
        Bb * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
      gcongr
    _ = _ := by ring

end CharacterCases

end LeanLab.ExceptionalSet.Decomp467b
