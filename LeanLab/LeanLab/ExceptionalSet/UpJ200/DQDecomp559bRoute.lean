import LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly
import LeanLab.ExceptionalSet.DQ5Decisions

/-!
Next route step after `DQDecomp559bAssembly`, session CLOUD-cited-decomp559b-p2, 2026-11-20.
Source P0082, Brüdern and Perelli 1998, Ann. Inst. Fourier 48, pages 362 to 364, Lemma 7.

`Decomp527a.PointwiseMajorCharacterDQ5` is the DQ5 named hypothesis for the sealed leaf
`Decomp527a.leaf_pointwise_major_character`. Its body is word for word the type of
`Decomp559b.pointwise_major_character_from_selected_cases`, so it now follows from the
named hypotheses of the four case decisions with no admitted step.

The next step, `Decomp527a.pointwise_lower_of_named_dq5`, takes `PointwiseMajorCharacterDQ5`
as its only argument and is otherwise free of admitted steps, its conductor leaves being proved through
`Decomp559a`. So `pointwise_lower_of_hyps`, the statement of
`Decomp527a.pointwise_lower_from_cases`, rests on the six named hypotheses only.

One step further, `adjacent_count_of_hyps` replays `Decomp527a.adjacent_count_from_inputs`
with the Lemma 4 discrepancy input `U1539.Lemma4` as an explicit argument in place of the
admitted theorem `U1539.lemma4`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly

open LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected (Lemma2NoExcBP
  SingularSeriesEvenLowerBP)
open LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected (BPLemma3CoprimeHyp)
open LeanLab.ExceptionalSet.UpJ200.DQLeafPrimeProductSelected (PrimeProductSelectedP0082)
open LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected (CaseIIdMajorLowerHyp
  RealZeroDistanceHyp)

/-- P0082 pages 362 to 364 Lemma 7. The DQ5 named hypothesis
`PointwiseMajorCharacterDQ5` from the six named hypotheses of the four case decisions.
CONDITIONAL ON `Lemma2NoExcBP`, `SingularSeriesEvenLowerBP`, `BPLemma3CoprimeHyp`,
`PrimeProductSelectedP0082`, `CaseIIdMajorLowerHyp` and `RealZeroDistanceHyp`; no admitted step. -/
theorem pointwiseMajorCharacterDQ5_of_hyps
    (hL : Lemma2NoExcBP) (hSa : SingularSeriesEvenLowerBP)
    (hL3 : BPLemma3CoprimeHyp) (H : PrimeProductSelectedP0082)
    (hII : CaseIIdMajorLowerHyp) (hZ : RealZeroDistanceHyp) :
    LeanLab.ExceptionalSet.UpJ200.Decomp527a.PointwiseMajorCharacterDQ5 :=
  fun γ h1 h2 => pointwise_major_character_of_six_hyps hL hSa hL3 H hII hZ γ h1 h2

/-- Twin check: `PointwiseMajorCharacterDQ5` unfolds to the statement of
`Decomp559b.pointwise_major_character_from_selected_cases` for every `1 < γ < 3/2`. PROVED. -/
theorem pointwiseMajorCharacterDQ5_iff :
    LeanLab.ExceptionalSet.UpJ200.Decomp527a.PointwiseMajorCharacterDQ5 ↔
      type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.pointwise_major_character_from_selected_cases :=
  Iff.rfl

open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)

/-- P0082 pages 362 to 364 Lemma 7, the pointwise lower bound with the case split folded
in, `Decomp527a.pointwise_lower_of_named_dq5` fed by the assembly above. CONDITIONAL ON
the six named hypotheses and on whatever `pointwise_lower_of_named_dq5` itself uses,
which `#print axioms` below reports; no admitted step in this file. -/
theorem pointwise_lower_of_hyps
    (hL : Lemma2NoExcBP) (hSa : SingularSeriesEvenLowerBP)
    (hL3 : BPLemma3CoprimeHyp) (H : PrimeProductSelectedP0082)
    (hII : CaseIIdMajorLowerHyp) (hZ : RealZeroDistanceHyp)
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
                  A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) :=
  LeanLab.ExceptionalSet.UpJ200.Decomp527a.pointwise_lower_of_named_dq5
    (pointwiseMajorCharacterDQ5_of_hyps hL hSa hL3 H hII hZ) γ h1 h2

/-- Twin check: same type as `Decomp527a.pointwise_lower_from_cases`. -/
theorem pointwise_lower_twin
    (hL : Lemma2NoExcBP) (hSa : SingularSeriesEvenLowerBP)
    (hL3 : BPLemma3CoprimeHyp) (H : PrimeProductSelectedP0082)
    (hII : CaseIIdMajorLowerHyp) (hZ : RealZeroDistanceHyp) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp527a.pointwise_lower_from_cases :=
  pointwise_lower_of_hyps hL hSa hL3 H hII hZ

section AdjacentCount
open Real Finset
open LeanLab.ExceptionalSet.Supply465
open LeanLab.ExceptionalSet.U1539 (Lemma4)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a

/-- P0082 pages 362 to 364, Lemma 7. The statement of `Decomp527a.adjacent_count_from_inputs`,
by its proof with `pointwise_lower_from_cases` replaced by `pointwise_lower_of_hyps` and the
admitted theorem `U1539.lemma4` replaced by the explicit argument `h4 : Lemma4`, the Lemma 4
discrepancy input, DQ5 named hypothesis `Lemma4DQ5`. CONDITIONAL ON `Lemma4` and the six
named hypotheses; no admitted step. -/
theorem adjacent_count_of_hyps (h4 : Lemma4)
    (hL : Lemma2NoExcBP) (hSa : SingularSeriesEvenLowerBP)
    (hL3 : BPLemma3CoprimeHyp) (H : PrimeProductSelectedP0082)
    (hII : CaseIIdMajorLowerHyp) (hZ : RealZeroDistanceHyp)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ c₀ B : ℝ, 0 < c₀ ∧ 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ j : ℤ, (j = 0 ∨ j = 1) →
            ((((window γ N).filter (fun n => Even (nu γ n + j))).filter (fun n =>
              (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re <
                c₀ * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤
                  B * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by
  classical
  obtain ⟨δp, hδp, hp⟩ := pointwise_lower_of_hyps hL hSa hL3 H hII hZ γ h1 h2
  obtain ⟨δm, hδm, hm⟩ := LeanLab.ExceptionalSet.UpJ200.Decomp527a.error_mean h4 γ h1 h2
  obtain ⟨δg, hδg, hg⟩ := LeanLab.ExceptionalSet.UpJ200.Decomp527a.large_gcd_from_lemma4 h4 γ h1 h2
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
  have hnN : n < N := lt_of_le_of_ne (LeanLab.ExceptionalSet.UpJ200.Decomp371a.window_upper γ h1 N (by omega) n hnw) hnnot
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

/-- Twin check: same type as `Decomp527a.adjacent_count_from_inputs`. -/
theorem adjacent_count_twin (h4 : Lemma4)
    (hL : Lemma2NoExcBP) (hSa : SingularSeriesEvenLowerBP)
    (hL3 : BPLemma3CoprimeHyp) (H : PrimeProductSelectedP0082)
    (hII : CaseIIdMajorLowerHyp) (hZ : RealZeroDistanceHyp) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp527a.adjacent_count_from_inputs :=
  adjacent_count_of_hyps h4 hL hSa hL3 H hII hZ

end AdjacentCount

end LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly

#print axioms LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly.pointwiseMajorCharacterDQ5_of_hyps
#print axioms LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly.pointwiseMajorCharacterDQ5_iff
#print axioms LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly.pointwise_lower_of_hyps
#print axioms LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly.pointwise_lower_twin
#print axioms LeanLab.ExceptionalSet.UpJ200.Decomp527a.pointwise_lower_of_named_dq5
#print axioms LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly.adjacent_count_of_hyps
#print axioms LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly.adjacent_count_twin
