import LeanLab.ExceptionalSet.Prep1122Theorem1FiveWalls
import LeanLab.ExceptionalSet.UpJ200.Prep1122Decomp559bWire
import LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082
import LeanLab.ExceptionalSet.KaracubaThm1Clean1122
import LeanLab.ExceptionalSet.DQLemma10S1

/-!
Integration of burst burst-20261122, branch claude/ExceptionalSet-integrate1122.
Source P0082, J. Brüdern and A. Perelli, Ann. Inst. Fourier 48 (1998), doi 10.5802/aif.1621,
Theorem 1 page 354, assembled through pages 358 to 371.

The sealed route of `DecompJ200.brudernPerelli_assembly` passes through the four case leaves of
Lemma 7 in `Decomp559b`. The wires on main and on today's burst branches each fix one set of
named walls. This file states the assembly once with the four case leaves as explicit
arguments, typed by `type_of%` of the sealed leaves, so that every later proof of a single leaf
plugs in without another copy of the assembly.

* `pointwise_major_character_of_leaves`: the proof of
  `Prep1122Decomp559bWire.pointwise_major_character_wired`, copied, with its four wired leaves
  replaced by the arguments.
* `adjacent_count_of_leaves`: the proof of `DQDecomp559bAssembly.adjacent_count_of_hyps`,
  copied, with `pointwise_lower_of_hyps` replaced by the argument.
* `theorem1_of_karacuba_and_leaves`: the proof of
  `Prep1122Theorem1FiveWalls.theorem1_of_five_citation_walls`, copied, with the adjacent count
  taken from the line above.
* `theorem1_of_vinogradov_walls`: `Theorem1` CONDITIONAL ON `KarLemma1`, `KarLemma2`,
  `Lemma2NoExcBP`, `BPLemma3CoprimeHyp`, `BPLemma3Hyp` and `CaseIIdMajorLowerHyp`.
* `theorem2_of_vinogradov`: P0082 Theorem 2 CONDITIONAL ON `KarLemma1` and `KarLemma2`.

No new definition, no sorry, no statement changed. AI wrote the Lean code. Binary Goldbach is
open.
-/

namespace LeanLab.ExceptionalSet.Integrate1122

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F Solvable Theorem1)
open LeanLab.ExceptionalSet.U1539 (R1 nu calE Lemma4 Lemma9 Lemma10)
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero leaf_selected_real_zero
  selected_shape)

/-- P0082 pages 362 to 364 Lemma 7, the statement of
`Decomp559b.pointwise_major_character_from_selected_cases`, CONDITIONAL ON the four case leaves
given as arguments of the exact types of `Decomp559b.leaf_absent_selected`, case i page 362,
`leaf_coprime_selected`, case ii a page 363, `leaf_prime_product_selected`, case ii b page 363,
and `leaf_near_zero_selected`, case ii d page 364. -/
theorem pointwise_major_character_of_leaves
    (hA : type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_absent_selected)
    (hB : type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_coprime_selected)
    (hD : type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_prime_product_selected)
    (hE : type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_near_zero_selected) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.pointwise_major_character_from_selected_cases := by
  intro γ h1 h2
  obtain ⟨a, hapos, hselect⟩ := leaf_selected_real_zero
  obtain ⟨δa, hδa, ha⟩ := hA γ h1 h2 a hapos
  obtain ⟨δb, hδb, hb⟩ := hB γ h1 h2 a hapos
  obtain ⟨δd, hδd, hd⟩ := hD γ h1 h2 a hapos
  obtain ⟨δe, hδe, he⟩ := hE γ h1 h2 a hapos
  refine ⟨min δa (min δb (min δd δe)), lt_min hδa (lt_min hδb (lt_min hδd hδe)), ?_⟩
  intro δ hδ hδsmall
  have hdeltas := lt_min_iff.mp hδsmall
  have hdeltas' := lt_min_iff.mp hdeltas.2
  have hdeltas'' := lt_min_iff.mp hdeltas'.2
  obtain ⟨κa, hκa, ha⟩ := ha δ hδ hdeltas.1
  obtain ⟨κb, hκb, hb⟩ := hb δ hδ hdeltas'.1
  obtain ⟨κd, hκd, hd⟩ := hd δ hδ hdeltas''.1
  obtain ⟨κe, hκe, he⟩ := he δ hδ hdeltas''.2
  refine ⟨min κa (min κb (min κd κe)), lt_min hκa (lt_min hκb (lt_min hκd hκe)), ?_⟩
  intro κ hκ hκsmall
  have hkappas := le_min_iff.mp hκsmall
  have hkappas' := le_min_iff.mp hkappas.2
  have hkappas'' := le_min_iff.mp hkappas'.2
  obtain ⟨ca, Aa, hca, hAa, Na, ha⟩ := ha κ hκ hkappas.1
  obtain ⟨cb, Ab, hcb, hAb, Nb, hb⟩ := hb κ hκ hkappas'.1
  obtain ⟨cd, Ad, hcd, hAd, Nd, hd⟩ := hd κ hκ hkappas''.1
  obtain ⟨ce, Ae, hce, hAe, Ne, he⟩ := he κ hκ hkappas''.2
  let c := min ca (min cb (min cd ce))
  let A := Aa + Ab + Ad + Ae
  have hc : 0 < c := lt_min hca (lt_min hcb (lt_min hcd hce))
  have hA : 0 < A := by dsimp [A]; positivity
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hF : Tendsto (fun N : ℕ => F γ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith : 0 < γ)).comp hlog)
  have hP : Tendsto (fun N : ℕ => F γ N ^ (6 * δ)) atTop atTop :=
    (tendsto_rpow_atTop (by positivity : 0 < 6 * δ)).comp hF
  obtain ⟨Np, hNp⟩ := eventually_atTop.mp (hP.eventually_ge_atTop 2)
  refine ⟨c, A, hc, hA, max Np (max Na (max Nb (max Nd Ne))), ?_⟩
  intro N hN
  have hNs := max_le_iff.mp hN
  have hNs' := max_le_iff.mp hNs.2
  have hNs'' := max_le_iff.mp hNs'.2
  have hNs''' := max_le_iff.mp hNs''.2
  obtain ⟨r, hr, hrP, hs⟩ := hselect _ (hNp N hNs.1)
  refine ⟨r, hr, hrP, selected_shape a _ r hs, ?_⟩
  intro j hj n hn heven hm
  dsimp only
  have hX : 0 ≤ F γ N := (Real.exp_pos _).le
  have hP0 : 0 ≤ F γ N ^ (6 * δ) := Real.rpow_nonneg hX _
  have hD : 0 ≤ divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
    unfold divisorError
    apply add_nonneg
    · apply mul_nonneg (by positivity)
      exact sum_nonneg (fun q _ => by positivity)
    · apply mul_nonneg (by positivity)
      exact tsum_nonneg (fun q => by split_ifs <;> positivity)
  have hca' : c ≤ ca := min_le_left _ _
  have hcb' : c ≤ cb := (min_le_right _ _).trans (min_le_left _ _)
  have hcd' : c ≤ cd := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hce' : c ≤ ce := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))
  have hAa' : Aa ≤ A := by dsimp [A]; linarith
  have hAb' : Ab ≤ A := by dsimp [A]; linarith
  have hAd' : Ad ≤ A := by dsimp [A]; linarith
  have hAe' : Ae ≤ A := by dsimp [A]; linarith
  have transfer (ci Ai w : ℝ) (hw : 0 ≤ w) (hci : c ≤ ci) (hAi : Ai ≤ A)
      (h : ci * F γ N * w ≤ (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
        Ai * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j)) :
      c * F γ N * w ≤ (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re +
        A * F γ N * divisorError r (F γ N ^ (6 * δ)) (nu γ n + j) := by
    have hleft := mul_le_mul_of_nonneg_right hci (mul_nonneg hX hw)
    have hright := mul_le_mul_of_nonneg_right hAi (mul_nonneg hX hD)
    nlinarith only [hleft, hright, h]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hcase
    have hh := ha N hNs'.1 r hr hrP hs j hj n hn heven hm hcase
    simpa only [mul_one] using transfer ca Aa 1 (by norm_num) hca' hAa' (by simpa using hh)
  · intro hcase hgcd
    have hh := hb N hNs''.1 r hr hrP hs j hj n hn heven hm hcase hgcd
    simpa only [mul_one] using transfer cb Ab 1 (by norm_num) hcb' hAb' (by simpa using hh)
  · intro hgcd hprime
    have hh := hd N hNs'''.1 r hr hrP hs j hj n hn heven hm hgcd hprime
    simpa only [mul_one] using transfer cd Ad 1 (by norm_num) hcd' hAd' (by simpa using hh)
  · intro hgcd hprime hsmall
    exact transfer ce Ae _ (Real.rpow_nonneg (Real.exp_pos _).le _) hce' hAe'
      (he N hNs'''.2 r hr hrP hs j hj n hn heven hm hgcd hprime hsmall)


/-- P0082 pages 362 to 364, the statement of `Decomp527a.pointwise_lower_from_cases`,
through the proved `Decomp527a.pointwise_lower_of_named_dq5`. CONDITIONAL ON the four case
leaves. -/
theorem pointwise_lower_of_leaves
    (hA : type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_absent_selected)
    (hB : type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_coprime_selected)
    (hD : type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_prime_product_selected)
    (hE : type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_near_zero_selected) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp527a.pointwise_lower_from_cases :=
  LeanLab.ExceptionalSet.UpJ200.Decomp527a.pointwise_lower_of_named_dq5
    (fun γ h1 h2 => pointwise_major_character_of_leaves hA hB hD hE γ h1 h2)

section AdjacentCount
open LeanLab.ExceptionalSet.Supply465
open LeanLab.ExceptionalSet.UpJ200.Decomp527a

/-- P0082 pages 362 to 364, Lemma 7, the statement of `Decomp527a.adjacent_count_from_inputs`,
CONDITIONAL ON the Lemma 4 input and the pointwise lower bound. -/
theorem adjacent_count_of_leaves (h4 : Lemma4)
    (hPL : type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp527a.pointwise_lower_from_cases) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp527a.adjacent_count_from_inputs := by
  intro γ h1 h2
  classical
  obtain ⟨δp, hδp, hp⟩ := hPL γ h1 h2
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

end AdjacentCount

open LeanLab.ExceptionalSet.Prep1122MainWire in
/-- P0082 page 354 Theorem 1, CONDITIONAL ON Karacuba 1971 Theorem 1, `KaracubaThm1Named`, and
the four case leaves of Lemma 7. Lemmas 4, 9 and 10 come from `KaracubaThm1Named` as in
`Prep1122Theorem1FiveWalls`; display 11 and display 10 enter only inside the case leaves. -/
theorem theorem1_of_karacuba_and_leaves
    (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named)
    (hA : type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_absent_selected)
    (hB : type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_coprime_selected)
    (hD : type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_prime_product_selected)
    (hE : type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp559b.leaf_near_zero_selected) :
    Theorem1 := by
  have h10 := LeanLab.ExceptionalSet.U1539.DQLemma10.lemma10_of_karacuba_named hK
  have h4 := LeanLab.ExceptionalSet.Prep1121Lemma9Wire.lemma4_of_karacuba hK
  have h9 := LeanLab.ExceptionalSet.Prep1121Lemma9Wire.lemma9_of_karacuba hK
  have hadj := adjacent_count_of_leaves h4 (pointwise_lower_of_leaves hA hB hD hE)
  have hcoeff := coefficient_lower_of_inputs hadj (odd_moment_of_inputs h4 h9 h10)
  have hmajor := major_bound_of_inputs hcoeff h4
  have hminor := minor_bound_of_lemma10 h10
  intro γ h1 h2
  obtain ⟨κ, B, hκ, hB, N₀, hblock⟩ :=
    block_bound_of_arc_inputs hmajor hminor γ h1 h2
  obtain ⟨c, hc, C, hC, M₀, hdyadic⟩ :=
    LeanLab.ExceptionalSet.DecompJ200.leaf_block_dissection γ κ B h1 h2 hκ hB
      (fun n => ¬ Solvable γ n) N₀ hblock
  have heq (M : ℕ) : LeanLab.ExceptionalSet.DecompJ200.Eγ_dyadic γ M =
      LeanLab.ExceptionalSet.DecompJ200.dyadicCount (fun n => ¬ Solvable γ n) M := by
    unfold LeanLab.ExceptionalSet.DecompJ200.Eγ_dyadic
      LeanLab.ExceptionalSet.DecompJ200.dyadicCount
    congr!
  exact LeanLab.ExceptionalSet.DecompJ200.leaf_theorem1_from_sums γ h1 h2
    ⟨c, hc, C, hC, M₀, fun M hM => by rw [heq]; exact hdyadic M hM⟩
    (LeanLab.ExceptionalSet.DecompJ200.leaf_dyadic_trivial γ)
    (LeanLab.ExceptionalSet.DecompJ200.leaf_dyadic_sum γ)
    (LeanLab.ExceptionalSet.DecompJ200.leaf_dyadic_sum_exp γ h1 h2)

/-- P0082 page 354 Theorem 1, CONDITIONAL ON exactly six named citation walls:
`KarLemma1` and `KarLemma2`, Karacuba 1971 pages 243 and 244, Vinogradov's mean value theorem
and Weyl sum estimate; `Lemma2NoExcBP`, P0082 Lemma 2; `BPLemma3CoprimeHyp` and `BPLemma3Hyp`,
two readings of P0082 Lemma 3; `CaseIIdMajorLowerHyp`, the case ii d lower bound of page 364.
The Erdős–Turán wall, display 10 and display 11 are all discharged by proved theorems. -/
theorem theorem1_of_vinogradov_walls
    (hK1 : LeanLab.ExceptionalSet.U1539.KaracubaSplit.KarLemma1)
    (hK2 : LeanLab.ExceptionalSet.U1539.KaracubaSplit.KarLemma2)
    (hL : LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected.Lemma2NoExcBP)
    (hL3c : LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected.BPLemma3CoprimeHyp)
    (hL3 : LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082.BPLemma3Hyp)
    (hII : LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected.CaseIIdMajorLowerHyp) :
    Theorem1 :=
  theorem1_of_karacuba_and_leaves
    (LeanLab.ExceptionalSet.U1539.KaracubaSplit.karacubaThm1Named_of_vinogradov hK1 hK2)
    (LeanLab.ExceptionalSet.UpJ200.Prep1122Decomp559bWire.leaf_absent_selected_wired hL)
    (LeanLab.ExceptionalSet.UpJ200.Prep1122Decomp559bWire.leaf_coprime_selected_wired hL3c)
    (LeanLab.ExceptionalSet.UpJ200.Prep1122Decomp559bWire.leaf_prime_product_selected_wired
      (LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082.prime_product_selected_of_lemma3 hL3))
    (LeanLab.ExceptionalSet.UpJ200.Prep1122Decomp559bWire.leaf_near_zero_selected_wired hII)

/-- P0082 Theorem 2, the minor arc Weyl sum bound in `State1539Data264`, CONDITIONAL ON
`KarLemma1` and `KarLemma2` only, through `DQLemma10.theorem2_of_karacuba_named`. -/
theorem theorem2_of_vinogradov
    (hK1 : LeanLab.ExceptionalSet.U1539.KaracubaSplit.KarLemma1)
    (hK2 : LeanLab.ExceptionalSet.U1539.KaracubaSplit.KarLemma2) :
    LeanLab.ExceptionalSet.U1539.Theorem2 :=
  LeanLab.ExceptionalSet.U1539.DQLemma10.theorem2_of_karacuba_named
    (LeanLab.ExceptionalSet.U1539.KaracubaSplit.karacubaThm1Named_of_vinogradov hK1 hK2)

end LeanLab.ExceptionalSet.Integrate1122

#print axioms LeanLab.ExceptionalSet.Integrate1122.pointwise_major_character_of_leaves
#print axioms LeanLab.ExceptionalSet.Integrate1122.pointwise_lower_of_leaves
#print axioms LeanLab.ExceptionalSet.Integrate1122.adjacent_count_of_leaves
#print axioms LeanLab.ExceptionalSet.Integrate1122.theorem1_of_karacuba_and_leaves
#print axioms LeanLab.ExceptionalSet.Integrate1122.theorem1_of_vinogradov_walls
#print axioms LeanLab.ExceptionalSet.Integrate1122.theorem2_of_vinogradov
