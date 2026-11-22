/-
P0082 J. Brüdern and A. Perelli, Goldbach numbers in sparse sequences, Ann. Inst. Fourier 48
(1998) 353-378. The main result, Theorem 1, wired to the named citation walls of the lane and to
the six case hypotheses of the pointwise character estimate.

Each input of the top assembly is supplied here by a term, and every term has no admitted step
of its own:

  * Lemma 10, pages 370-371, from Karacuba 1971 Theorem 1, p. 244, the named `KaracubaThm1Named`;
  * Lemma 4, page 359, from the Erdős-Turán inequality, the named `ErdosTuranDQ4`, and Lemma 10;
  * Lemma 9, page 368, from those same two walls;
  * the pointwise character cases of pages 362 to 364, from four DQ case hypotheses; the other
    two, the singular series lower bound and the real zero distance, are PROVED in this tree
    (`Task672.singularSeriesEvenLowerBP_proved672`, `Task672.realZeroDistanceHyp_proved672`);
  * the odd coefficient second moment of pages 366 to 369, displays 29 and 30, ported with
    Lemma 4, Lemma 9 and Lemma 10 as arguments in place of the admitted `U1539.lemma4`,
    `U1539.lemma9` and `U1539.lemma10`. That port is the reason Lemma 9 is on the route: the
    page 369 parity gap is `Decomp539a.parity_gap_of_inputs`, which consumes Lemma 9 and
    Lemma 10 directly;
  * the page 354 and page 366 assembly of `Decomp467c`.

Nothing admitted enters the axioms of any statement here: `#print axioms` reports `propext`,
`Classical.choice` and `Quot.sound` for every theorem below. Binary Goldbach is OPEN.

AI wrote the Lean code.
-/
import LeanLab.ExceptionalSet.Decomp467c
import LeanLab.ExceptionalSet.UpJ200.DQDecomp559bRoute
import LeanLab.ExceptionalSet.DQLemma4Decisions
import LeanLab.ExceptionalSet.DQLemma10S1
import LeanLab.ExceptionalSet.DQLemma9Named
import LeanLab.ExceptionalSet.UpJ200.Decomp505a
import LeanLab.ExceptionalSet.UpJ200.Decomp539a
import LeanLab.ExceptionalSet.MinorSup446
import LeanLab.ExceptionalSet.SingularSeriesLower672
import LeanLab.ExceptionalSet.RealZeroLower672

namespace LeanLab.ExceptionalSet.Prep1121Theorem1Wire

open Real Finset MeasureTheory Set Filter Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F Theorem1)
open LeanLab.ExceptionalSet.U1539 (R1 nu nuOdd calE majorArcs Lemma4 Lemma9 Lemma10)
open LeanLab.ExceptionalSet.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp539a

/-- Lemma 10 of P0082, pages 370 and 371, Karacuba's Theorem 1 with the change of notation,
from the cited Karacuba 1971 Theorem 1, p. 244, only. CONDITIONAL ON `KaracubaThm1Named`. -/
theorem lemma10_of_named (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named) :
    Lemma10 :=
  LeanLab.ExceptionalSet.U1539.DQLemma10.lemma10_of_karacuba_named hK

/-- Lemma 4 of P0082, page 359, from the cited Erdős-Turán inequality in the explicit
Kuipers-Niederreiter form `ErdosTuranDQ4` and Lemma 10 through Theorem 2.
CONDITIONAL ON `ErdosTuranDQ4` and `KaracubaThm1Named`. -/
theorem lemma4_of_named (hET : LeanLab.ExceptionalSet.DQLemma4.ErdosTuranDQ4)
    (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named) : Lemma4 :=
  LeanLab.ExceptionalSet.DQLemma4.lemma4_of_erdosTuran_lemma10 hET (lemma10_of_named hK)

/-- Lemma 9 of P0082, page 368, proved on page 370: a large value of the even phase sum
localizes near a half integer with a bounded height. CONDITIONAL ON `ErdosTuranDQ4` and
`KaracubaThm1Named`. -/
theorem lemma9_of_named (hET : LeanLab.ExceptionalSet.DQLemma4.ErdosTuranDQ4)
    (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named) : Lemma9 :=
  LeanLab.ExceptionalSet.DQLemma9Named.lemma9_of_named hET hK

theorem moment_over_complement_of_named (h9 : Lemma9) (h10 : Lemma10)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ j : ℤ, (j = 0 ∨ j = 1) →
            (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + j)),
              ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N ^ (2 / 3 : ℝ))) (calE γ κ N ^ (2 / 3 : ℝ)),
                OddTail467.integrand (F γ N ^ (6 * δ)) (F γ N)
                  (calE γ κ N ^ (-(5 / 12 : ℝ))) (F γ n - j) α‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ))  := by
  classical
  obtain ⟨δg, hδg, hg⟩ := UpJ200.Decomp539a.parity_gap_of_inputs h9 h10 γ h1 h2
  obtain ⟨δm, hδm, hm⟩ := MinorSup446.leaf_minor_sup_supplied γ h1 h2
  refine ⟨min δg (min δm 1), lt_min hδg (lt_min hδm (by norm_num)), fun δ hδ hδsmall => ?_⟩
  have hδg' : δ < δg := hδsmall.trans_le (min_le_left _ _)
  have hδm' : δ < δm := hδsmall.trans_le ((min_le_right _ _).trans (min_le_left _ _))
  have hδ1 : δ ≤ 1 := hδsmall.le.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨κ₀, hκ₀, hg⟩ := hg δ hδ hδg'
  obtain ⟨C, hC, Nm, hm⟩ := hm δ hδ hδm'
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨Ng, hg⟩ := hg κ hκ hκsmall
  obtain ⟨Np, hp⟩ := phase_window_parameters γ δ κ h1 h2 hδ hδ1 hκ
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨49 * Real.log 4 ^ 2 + 42 * C * Real.log 4, by positivity,
    max Ng (max Nm Np), fun N hN j hj => ?_⟩
  have hNg : Ng ≤ N := by omega
  have hNm : Nm ≤ N := by omega
  have hNp : Np ≤ N := by omega
  obtain ⟨hX, hE, hL, hl, hs, hTX, htw, hheight, hr⟩ := hp N hNp
  let X := F γ N
  let E := calE γ κ N
  let P := X ^ (6 * δ)
  let Δ := E ^ (-(5 / 12 : ℝ))
  let A := oddDomain P X E
  let M := ∫ a in A, mass P X Δ a
  let V := (N : ℝ) * E ^ (-(5 / 6 : ℝ))
  let Q := 6 * C * X * E ^ (-(2 / 3 : ℝ))
  have hX0 : 0 < X := Real.exp_pos _
  have hE0 : 0 < E := Real.exp_pos _
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos hE0 _
  have hΔ1 : Δ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hE (by norm_num)
  have hMi := mass_integrable P X Δ hΔ hΔ1
  have hM0 : 0 ≤ M := integral_nonneg (fun a => norm_nonneg _)
  have hMb : M ≤ 7 * (Real.log 4 * X * Real.log X) / Real.sqrt Δ := by
    apply (setIntegral_le_integral hMi (Filter.Eventually.of_forall (fun a => norm_nonneg _))).trans
    exact Decomp483d.shifted_weighted_mass_sqrt P X Δ hX hΔ hΔ1
  have hinner (a : ℝ) (ha : a ∈ A) :
      (∫ b in A ∩ {b | V < ‖parityPhase γ N j (b - a)‖}, mass P X Δ b) ≤ Q := by
    apply prime_strip_inner E X C δ hE.le hX0 hC.le hΔ1 hTX hl hs (hm N hNm) a
    · exact Set.inter_subset_left
    · intro b hb
      have hbt : |b - a| ≤ 2 * E ^ (2 / 3 : ℝ) := by
        apply abs_le.mpr
        constructor <;> linarith [ha.2.1, ha.2.2, hb.1.2.1, hb.1.2.2]
      obtain ⟨h, hgap⟩ := hg N hNg j hj (b - a) (hbt.trans htw) hb.2
      have hh := half_integer_height E (b - a) (X ^ (δ - 1)) h hr hbt hgap hheight
      have hmem := mem_stripIndices E h hh
      apply Set.mem_iUnion.mpr
      refine ⟨h, Set.mem_iUnion.mpr ⟨hmem, ?_⟩⟩
      have hab := abs_le.mp hgap
      exact ⟨by linarith [hab.1], by linarith [hab.2]⟩
  have hmoment := shifted_moment_from_inner γ P X Δ N j A hΔ hΔ1 V Q (by dsimp [V]; positivity) hinner
  have hsmall := small_phase_budget E (Real.log 4 * X * Real.log X) M N hE.le
    (by positivity) hM0 hMb
  have hsmalllog := small_phase_log_budget E X N hE.le hl
  have hlarge := large_phase_budget E X C M N hE.le hX0.le hC.le hL hl hMb
  change _ ≤ (49 * Real.log 4 ^ 2 + 42 * C * Real.log 4) * N * X ^ 2 * E ^ (-(1 / 3 : ℝ))
  change _ ≤ V * M ^ 2 + N * Q * M at hmoment
  calc
    _ ≤ V * M ^ 2 + N * Q * M := hmoment
    _ ≤ (49 * Real.log 4 ^ 2) * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) +
        (42 * C * Real.log 4) * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by
      exact add_le_add (hsmall.trans hsmalllog) hlarge
    _ = _ := by ring


theorem boundary_of_lemma4 (h4 : Lemma4) (γ a : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2)
    (ha : 0 < a) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
          Int.fract (F γ n) < calE γ κ N ^ (-a) ∨
            1 - calE γ κ N ^ (-a) < Int.fract (F γ n))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-a) := by
  classical
  obtain ⟨κa, A, hκa, hdisc⟩ := h4 γ h1 h2
  refine ⟨κa / a, by positivity, fun κ hκ hκsmall => ?_⟩
  let B := 2 * |A| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hE : Tendsto (fun N : ℕ => calE γ κ N) atTop atTop := by
    exact Real.tendsto_exp_atTop.comp
      (((tendsto_rpow_atTop (by linarith : 0 < 3 - 2 * γ)).comp hlog).const_mul_atTop hκ)
  obtain ⟨NE, hNE⟩ := eventually_atTop.mp (hE.eventually_ge_atTop 2)
  refine ⟨B, hB, max 16 NE, fun N hN => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hE1 : 1 < calE γ κ N := lt_of_lt_of_le (by norm_num) (hNE N ((le_max_right _ _).trans hN))
  let Δ := calE γ κ N ^ (-a)
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hΔ1 : Δ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hE1 (by linarith)
  have hF1 : 1 < F γ N := by
    rw [F]
    exact Real.one_lt_exp_iff.mpr (Real.rpow_pos_of_pos hL _)
  have hα : F γ N ^ (-(1 / 2 : ℝ)) < |(1 : ℝ)| := by
    simpa using Real.rpow_lt_one_of_one_lt_of_neg hF1 (by norm_num : -(1 / 2 : ℝ) < 0)
  have hlo := hdisc N hN1 1 hα (by norm_num) Δ 0 (by norm_num) hΔ hΔ1.le
  have hhi := hdisc N hN1 1 hα (by norm_num) 1 (1 - Δ) (by linarith) (by linarith) le_rfl
  simp only [one_mul, sub_zero, sub_sub_cancel] at hlo hhi
  have herr : Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) ≤ Δ := by
    dsimp [Δ, calE]
    rw [← Real.exp_mul]
    apply Real.exp_le_exp.mpr
    have hp : 0 ≤ Real.log N ^ (3 - 2 * γ) := (Real.rpow_pos_of_pos hL _).le
    have hsmall : κ * a ≤ κa := (le_div_iff₀ ha).mp hκsmall
    nlinarith [mul_le_mul_of_nonneg_right hsmall hp]
  let L := (Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
    0 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < Δ)
  let R := (Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
    1 - Δ ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < 1)
  have hsubset : (Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
      Int.fract (F γ n) < Δ ∨ 1 - Δ < Int.fract (F γ n)) ⊆ L ∪ R := by
    intro n hn
    rcases Finset.mem_filter.mp hn with ⟨hnW, hn⟩
    have hnI := hnW
    rcases hn with hn | hn
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnI, Int.fract_nonneg _, hn⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnI, hn.le, Int.fract_lt_one _⟩)
  have hcard : (((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
      Int.fract (F γ n) < Δ ∨ 1 - Δ < Int.fract (F γ n))).card : ℝ) ≤ L.card + R.card := by
    exact_mod_cast (Finset.card_le_card hsubset).trans (Finset.card_union_le L R)
  have hl : (L.card : ℝ) ≤ Δ * N / 2 + |A| * N * Δ := by
    have ha := (abs_le.mp hlo).2
    change (L.card : ℝ) - Δ * N / 2 ≤ _ at ha
    have hbound : A * N * Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) ≤ |A| * N * Δ := by
      calc _ ≤ |A| * N * Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) := by gcongr; exact le_abs_self _
           _ ≤ _ := by gcongr
    linarith
  have hr : (R.card : ℝ) ≤ Δ * N / 2 + |A| * N * Δ := by
    have ha := (abs_le.mp hhi).2
    change (R.card : ℝ) - Δ * N / 2 ≤ _ at ha
    have hbound : A * N * Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) ≤ |A| * N * Δ := by
      calc _ ≤ |A| * N * Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) := by gcongr; exact le_abs_self _
           _ ≤ _ := by gcongr
    linarith
  calc
    _ ≤ (L.card : ℝ) + R.card := hcard
    _ ≤ (Δ * N / 2 + |A| * N * Δ) + (Δ * N / 2 + |A| * N * Δ) := add_le_add hl hr
    _ = _ := by dsimp [B]; ring

theorem parity_moment_from_shifted_of_named (h4 : Lemma4) (h9 : Lemma9) (h10 : Lemma10)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ j : ℤ, (j = 0 ∨ j = 1) →
            (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + j)),
              ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n - j + 1)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨δ₀, hδ₀, hm⟩ := moment_over_complement_of_named h9 h10 γ h1 h2
  obtain ⟨κb, hκb, hb⟩ := boundary_of_lemma4 h4 γ (5 / 12) h1 h2 (by norm_num)
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κm, hκm, hm⟩ := hm δ hδ hδsmall
  refine ⟨min κm κb, lt_min hκm hκb, fun κ hκ hκsmall => ?_⟩
  obtain ⟨Bm, hBm, Nm, hm⟩ := hm κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨Bb, hBb, Nb, hb⟩ := hb κ hκ (hκsmall.trans (min_le_right _ _))
  obtain ⟨Np, hp⟩ := TailParameters385.tail_parameters_eventually γ h1 h2 δ κ hδ hκ
  obtain ⟨Nl, hl⟩ := UpJ200.Decomp467a.log_F_sq_le_calE_twelfth γ κ h1 h2 hκ
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hEtop : Tendsto (fun N : ℕ => calE γ κ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (((tendsto_rpow_atTop (by linarith : 0 < 3 - 2 * γ)).comp hlog).const_mul_atTop hκ)
  obtain ⟨Ne, he⟩ := eventually_atTop.mp (hEtop.eventually_ge_atTop 2)
  obtain ⟨Nt, ht⟩ := eventually_atTop.mp
    (((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 2 / 3)).comp hEtop).eventually_ge_atTop 4)
  refine ⟨2 * Bm + 128 * Real.log 4 ^ 2 / Real.pi ^ 4 + Bb * Real.log 4 ^ 2,
    by positivity, max Nm (max Nb (max Np (max Nl (max Ne Nt)))), fun N hN j hj => ?_⟩
  have hNm : Nm ≤ N := by omega
  have hNb : Nb ≤ N := by omega
  have hNp : Np ≤ N := by omega
  have hNl : Nl ≤ N := by omega
  have hNe : Ne ≤ N := by omega
  have hNt : Nt ≤ N := by omega
  let X := F γ N
  let E := calE γ κ N
  let P := X ^ (6 * δ)
  let Δ := E ^ (-(5 / 12 : ℝ))
  let T := E ^ (2 / 3 : ℝ)
  let s := (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + j))
  have hX : 2 ≤ X := (hp N hNp).1
  have hP : 2 ≤ P := by have := (hp N hNp).2.1; dsimp [P, X]; linarith
  have hE : 1 < E := lt_of_lt_of_le (by norm_num) (he N hNe)
  have hE0 : 0 < E := lt_trans zero_lt_one hE
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos hE0 _
  have hΔ1 : Δ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hE (by norm_num)
  have hT : 4 ≤ T := ht N hNt
  have hodd (n : ℕ) (hn : n ∈ s) : Odd (⌊F γ n - (j : ℝ)⌋ + 1) := by
    rw [Int.floor_sub_intCast]
    change Odd (nu γ n - j + 1)
    obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hn).2
    exact ⟨k - j, by omega⟩
  have htransfer := Decomp483a.odd_upper_truncated_moment P X Δ T hP hX hΔ hΔ1 hT s
    (fun n => F γ n - j) hodd
  simp_rw [Int.floor_sub_intCast, show ∀ n : ℕ, ⌊F γ n⌋ = nu γ n from fun _ => rfl] at htransfer
  have hcard : (s.card : ℝ) ≤ N := by
    exact_mod_cast (Finset.card_filter_le _ _).trans
      (by rw [Nat.card_Ioc]; omega : (Finset.Ioc (N / 2) N).card ≤ N)
  have hsub : s.filter (fun n : ℕ => Int.fract (F γ n - j) < Δ / 2 ∨
      1 - Δ / 2 < Int.fract (F γ n - j)) ⊆
      (Finset.Ioc (N / 2) N).filter (fun n : ℕ => Int.fract (F γ n) < Δ ∨
        1 - Δ < Int.fract (F γ n)) := by
    intro n hn
    obtain ⟨hns, hn⟩ := Finset.mem_filter.mp hn
    apply Finset.mem_filter.mpr
    refine ⟨(Finset.mem_filter.mp hns).1, ?_⟩
    simp only [Int.fract_sub_intCast] at hn
    rcases hn with hn | hn
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hboundary : ((s.filter (fun n : ℕ => Int.fract (F γ n - j) < Δ / 2 ∨
      1 - Δ / 2 < Int.fract (F γ n - j))).card : ℝ) ≤ Bb * N * Δ := by
    exact (Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)).trans (hb N hNb)
  have herrors := UpJ200.Decomp509a.shifted_error_budget X E Bb N hE.le hBb.le (hl N hNl)
  have htail : 2 * (s.card : ℝ) *
      (8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T)) ^ 2 ≤
      2 * N * (8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T)) ^ 2 := by
    gcongr
  have hboundaryTerm := mul_le_mul_of_nonneg_right hboundary
    (sq_nonneg (Real.log 4 * X * Real.log X))
  have hmoment := hm N hNm j hj
  change (∑ n ∈ s, ‖∫ α in (majorArcs P X)ᶜ ∩ Set.Icc (-T) T,
    OddTail467.integrand P X Δ (F γ n - j) α‖ ^ 2) ≤
      Bm * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) at hmoment
  change _ ≤ (2 * Bm + 128 * Real.log 4 ^ 2 / Real.pi ^ 4 + Bb * Real.log 4 ^ 2) *
    N * X ^ 2 * E ^ (-(1 / 3 : ℝ))
  calc
    _ ≤ 2 * (Bm * N * X ^ 2 * E ^ (-(1 / 3 : ℝ))) +
        (128 * Real.log 4 ^ 2 / Real.pi ^ 4 + Bb * Real.log 4 ^ 2) *
          N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by
      dsimp only [P, X, E, Δ, T, s] at htransfer htail hboundaryTerm herrors hmoment ⊢
      linarith only [htransfer, htail, hboundaryTerm, herrors, hmoment]
    _ = _ := by ring



theorem leaf_even_parity_moment_of_named (h4 : Lemma4) (h9 : Lemma9) (h10 : Lemma10)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n : ℕ => Even (nu γ n)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨δ₀, hδ₀, h⟩ := parity_moment_from_shifted_of_named h4 h9 h10 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, h⟩ := h δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨B, hB, N₀, h⟩ := h κ hκ hκsmall
  refine ⟨B, hB, N₀, fun N hN => ?_⟩
  simpa only [add_zero, sub_zero] using h N hN 0 (Or.inl rfl)


theorem leaf_odd_parity_moment_of_named (h4 : Lemma4) (h9 : Lemma9) (h10 : Lemma10)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n : ℕ => ¬ Even (nu γ n)),
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  obtain ⟨δ₀, hδ₀, h⟩ := parity_moment_from_shifted_of_named h4 h9 h10 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, h⟩ := h δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨B, hB, N₀, h⟩ := h κ hκ hκsmall
  refine ⟨B, hB, N₀, fun N hN => ?_⟩
  simpa only [even_add_one, Int.not_even_iff_odd, sub_add_cancel] using
    h N hN 1 (Or.inr rfl)


theorem odd_moment_uniform_of_named (h4 : Lemma4) (h9 : Lemma9) (h10 : Lemma10)
    (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          (∑ n ∈ window γ N,
            ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nuOdd γ n)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨δa, hδa, ha⟩ := leaf_even_parity_moment_of_named h4 h9 h10 γ h1 h2
  obtain ⟨δb, hδb, hb⟩ := leaf_odd_parity_moment_of_named h4 h9 h10 γ h1 h2
  refine ⟨min δa δb, lt_min hδa hδb, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κa, hκa, ha⟩ := ha δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κb, hκb, hb⟩ := hb δ hδ (hδsmall.trans_le (min_le_right _ _))
  refine ⟨min κa κb, lt_min hκa hκb, fun κ hκ hκsmall => ?_⟩
  obtain ⟨Ba, hBa, Na, ha⟩ := ha κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨Bb, hBb, Nb, hb⟩ := hb κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨Ba + Bb, add_pos hBa hBb, max 16 (max Na Nb), fun N hN => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hNa : Na ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNb : Nb ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  let s := Finset.Ioc (N / 2) N
  let f := fun n : ℕ => R1 (F γ N ^ (6 * δ)) (F γ N) (nuOdd γ n)
  have hsub : window γ N ⊆ s :=
    UpJ200.Decomp371a.window_subset_Ioc γ h1 N hN16
  calc
    _ ≤ ∑ n ∈ s, ‖f n‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _)
    _ = (∑ n ∈ s.filter (fun n => Even (nu γ n)), ‖f n‖ ^ 2) +
        ∑ n ∈ s.filter (fun n => ¬ Even (nu γ n)), ‖f n‖ ^ 2 :=
      (Finset.sum_filter_add_sum_filter_not s (fun n => Even (nu γ n)) _).symm
    _ ≤ Ba * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) +
        Bb * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
      apply add_le_add
      · convert ha N hNa using 1
        apply Finset.sum_congr rfl
        intro n hn
        have hnE := (Finset.mem_filter.mp hn).2
        have hnO : ¬ Odd (nu γ n) := Int.not_odd_iff_even.mpr hnE
        simp [f, nuOdd, hnO]
      · convert hb N hNb using 1
        apply Finset.sum_congr rfl
        intro n hn
        have hnO : Odd (nu γ n) := Int.not_even_iff_odd.mp (Finset.mem_filter.mp hn).2
        simp [f, nuOdd, hnO]
    _ = _ := by ring

/-- Theorem 1 of P0082, page 354: for `1 < γ < 3/2` the number of `n ≤ N` whose even neighbour
of `F γ n` is not a sum of two odd primes is at most `C N exp(-c (log N)^{3-2γ})`, with `c` and
`C` effective. The page 366 block bound is fed here by the Lemma 4, Lemma 9 and Lemma 10 wires
above and by the pointwise character cases of the six DQ case hypotheses, and the odd second
moment comes from the section 6 port above. CONDITIONAL ON `ErdosTuranDQ4`, `KaracubaThm1Named`
and those six hypotheses. -/
theorem main_theorem_of_named (hET : LeanLab.ExceptionalSet.DQLemma4.ErdosTuranDQ4)
    (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named)
    (hL : LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected.Lemma2NoExcBP)
    (hL3 : LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected.BPLemma3CoprimeHyp)
    (hH : LeanLab.ExceptionalSet.UpJ200.DQLeafPrimeProductSelected.PrimeProductSelectedP0082)
    (hII : LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected.CaseIIdMajorLowerHyp) :
    Theorem1 :=
  LeanLab.ExceptionalSet.Decomp467c.brudernPerelli_from_inputs
    (fun γ h1 h2 =>
      LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly.pointwise_lower_of_hyps
        hL Task672.singularSeriesEvenLowerBP_proved672 hL3 hH hII
        Task672.realZeroDistanceHyp_proved672 γ h1 h2)
    (lemma4_of_named hET hK)
    (odd_moment_uniform_of_named (lemma4_of_named hET hK) (lemma9_of_named hET hK)
      (lemma10_of_named hK))
    (lemma10_of_named hK)

end LeanLab.ExceptionalSet.Prep1121Theorem1Wire

