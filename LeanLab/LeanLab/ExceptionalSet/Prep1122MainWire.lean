import LeanLab.ExceptionalSet.Prep1121Lemma9Wire
import LeanLab.ExceptionalSet.DecompJ200
import LeanLab.ExceptionalSet.UpJ200.DQDecomp559bRoute
import LeanLab.ExceptionalSet.Prep1121SingSeries
import LeanLab.ExceptionalSet.RealZeroLower672

/-!
P0082, Brudern and Perelli 1998, pages 354 and 362 to 370.
Main result wiring with the named citation walls as explicit hypotheses.
The sealed declarations are unchanged. The moment proofs below replay the
existing proofs with their admitted inputs replaced by explicit arguments.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Prep1122MainWire

open Real Finset Filter MeasureTheory
open scoped Topology
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F Solvable Theorem1)
open LeanLab.ExceptionalSet.U1539 (nu nuOdd calE R1 majorArcs Lemma4 Lemma9 Lemma10)

section Boundary
open LeanLab.ExceptionalSet.UpJ200.Decomp509a

/-- P0082 page 368 display 33. The full half interval boundary estimate,
CONDITIONAL ON the explicit Lemma 4 input. -/
theorem full_boundary_of_lemma4 (h4 : Lemma4) :
    type_of% @full_boundary_at_rate := by
  intro γ a h1 h2 ha
  classical
  obtain ⟨κa, A, hκa, hdisc⟩ := h4 γ h1 h2
  refine ⟨κa / a, by positivity, fun κ hκ hκsmall => ?_⟩
  let B := 2 * |A| + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hE : Tendsto (fun N : ℕ => calE γ κ N) atTop atTop :=
    Real.tendsto_exp_atTop.comp
      (((tendsto_rpow_atTop (by linarith : 0 < 3 - 2 * γ)).comp hlog).const_mul_atTop hκ)
  obtain ⟨NE, hNE⟩ := eventually_atTop.mp (hE.eventually_ge_atTop 2)
  refine ⟨B, hB, max 16 NE, fun N hN => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := by omega
  have hN1 : 1 ≤ N := by omega
  have hL : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hE1 : 1 < calE γ κ N :=
    lt_of_lt_of_le (by norm_num) (hNE N ((le_max_right _ _).trans hN))
  let Δ := calE γ κ N ^ (-a)
  have hΔ : 0 < Δ := Real.rpow_pos_of_pos (Real.exp_pos _) _
  have hΔ1 : Δ < 1 := Real.rpow_lt_one_of_one_lt_of_neg hE1 (by linarith)
  have hF1 : 1 < F γ N := by
    rw [F]
    exact Real.one_lt_exp_iff.mpr (Real.rpow_pos_of_pos hL _)
  have hα : F γ N ^ (-(1 / 2 : ℝ)) < |(1 : ℝ)| := by
    simpa using Real.rpow_lt_one_of_one_lt_of_neg hF1
      (by norm_num : -(1 / 2 : ℝ) < 0)
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
    rcases hn with hn | hn
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hnW, Int.fract_nonneg _, hn⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hnW, hn.le, Int.fract_lt_one _⟩)
  have hcard : (((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
      Int.fract (F γ n) < Δ ∨ 1 - Δ < Int.fract (F γ n))).card : ℝ) ≤ L.card + R.card := by
    exact_mod_cast (Finset.card_le_card hsubset).trans (Finset.card_union_le L R)
  have hl : (L.card : ℝ) ≤ Δ * N / 2 + |A| * N * Δ := by
    have ha := (abs_le.mp hlo).2
    change (L.card : ℝ) - Δ * N / 2 ≤ _ at ha
    have hbound : A * N * Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) ≤ |A| * N * Δ := by
      calc
        _ ≤ |A| * N * Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) := by
          gcongr
          exact le_abs_self _
        _ ≤ _ := by gcongr
    linarith
  have hr : (R.card : ℝ) ≤ Δ * N / 2 + |A| * N * Δ := by
    have ha := (abs_le.mp hhi).2
    change (R.card : ℝ) - Δ * N / 2 ≤ _ at ha
    have hbound : A * N * Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) ≤ |A| * N * Δ := by
      calc
        _ ≤ |A| * N * Real.exp (-κa * Real.log N ^ (3 - 2 * γ)) := by
          gcongr
          exact le_abs_self _
        _ ≤ _ := by gcongr
    linarith
  calc
    _ ≤ (L.card : ℝ) + R.card := hcard
    _ ≤ (Δ * N / 2 + |A| * N * Δ) + (Δ * N / 2 + |A| * N * Δ) := add_le_add hl hr
    _ = _ := by dsimp [B]; ring

end Boundary

section ShiftedMoment
open LeanLab.ExceptionalSet.UpJ200.Decomp539a

/-- P0082 pages 368 to 369 displays 35 to 39. The shifted parity moment,
CONDITIONAL ON Lemma 9 and Lemma 10. -/
theorem shifted_moment_of_inputs (h9 : Lemma9) (h10 : Lemma10) :
    type_of% @parity_moment_from_gap := by
  intro γ h1 h2
  classical
  obtain ⟨δg, hδg, hg⟩ := parity_gap_of_inputs h9 h10 γ h1 h2
  obtain ⟨δm, hδm, hm⟩ :=
    LeanLab.ExceptionalSet.UpJ200.MinorSup446.leaf_minor_sup_supplied γ h1 h2
  refine ⟨min δg (min δm 1), lt_min hδg (lt_min hδm (by norm_num)),
    fun δ hδ hδsmall => ?_⟩
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
    apply (setIntegral_le_integral hMi
      (Filter.Eventually.of_forall (fun a => norm_nonneg _))).trans
    exact LeanLab.ExceptionalSet.Decomp483d.shifted_weighted_mass_sqrt P X Δ hX hΔ hΔ1
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
  have hmoment := shifted_moment_from_inner γ P X Δ N j A hΔ hΔ1 V Q
    (by dsimp [V]; positivity) hinner
  have hsmall := small_phase_budget E (Real.log 4 * X * Real.log X) M N hE.le
    (by positivity) hM0 hMb
  have hsmalllog := small_phase_log_budget E X N hE.le hl
  have hlarge := large_phase_budget E X C M N hE.le hX0.le hC.le hL hl hMb
  change _ ≤ (49 * Real.log 4 ^ 2 + 42 * C * Real.log 4) * N * X ^ 2 *
    E ^ (-(1 / 3 : ℝ))
  change _ ≤ V * M ^ 2 + N * Q * M at hmoment
  calc
    _ ≤ V * M ^ 2 + N * Q * M := hmoment
    _ ≤ (49 * Real.log 4 ^ 2) * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) +
        (42 * C * Real.log 4) * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) :=
      add_le_add (hsmall.trans hsmalllog) hlarge
    _ = _ := by ring

end ShiftedMoment

section OddMoment
open LeanLab.ExceptionalSet.UpJ200.Decomp509a
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)

/-- P0082 page 367 displays 29 and 30. Transfer the shifted moment to
odd major coefficients, CONDITIONAL ON Lemmas 4, 9 and 10. -/
theorem parity_moment_of_inputs (h4 : Lemma4) (h9 : Lemma9) (h10 : Lemma10) :
    type_of% @parity_moment_from_shifted := by
  intro γ h1 h2
  classical
  obtain ⟨δ₀, hδ₀, hm⟩ := shifted_moment_of_inputs h9 h10 γ h1 h2
  obtain ⟨κb, hκb, hb⟩ := full_boundary_of_lemma4 h4 γ (5 / 12) h1 h2 (by norm_num)
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κm, hκm, hm⟩ := hm δ hδ hδsmall
  refine ⟨min κm κb, lt_min hκm hκb, fun κ hκ hκsmall => ?_⟩
  obtain ⟨Bm, hBm, Nm, hm⟩ := hm κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨Bb, hBb, Nb, hb⟩ := hb κ hκ (hκsmall.trans (min_le_right _ _))
  obtain ⟨Np, hp⟩ :=
    LeanLab.ExceptionalSet.UpJ200.TailParameters385.tail_parameters_eventually γ h1 h2 δ κ hδ hκ
  obtain ⟨Nl, hl⟩ :=
    LeanLab.ExceptionalSet.UpJ200.Decomp467a.log_F_sq_le_calE_twelfth γ κ h1 h2 hκ
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
  have hP : 2 ≤ P := by
    have := (hp N hNp).2.1
    dsimp [P, X]
    linarith
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
  have htransfer := LeanLab.ExceptionalSet.Decomp483a.odd_upper_truncated_moment
    P X Δ T hP hX hΔ hΔ1 hT s (fun n => F γ n - j) hodd
  simp_rw [Int.floor_sub_intCast, show ∀ n : ℕ, ⌊F γ n⌋ = nu γ n from fun _ => rfl]
    at htransfer
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
      1 - Δ / 2 < Int.fract (F γ n - j))).card : ℝ) ≤ Bb * N * Δ :=
    (Nat.cast_le (α := ℝ).mpr (Finset.card_le_card hsub)).trans (hb N hNb)
  have herrors := shifted_error_budget X E Bb N hE.le hBb.le (hl N hNl)
  have htail : 2 * (s.card : ℝ) *
      (8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T)) ^ 2 ≤
      2 * N * (8 * (Real.log 4 * X * Real.log X) / (Δ * Real.pi ^ 2 * T)) ^ 2 := by
    gcongr
  have hboundaryTerm := mul_le_mul_of_nonneg_right hboundary
    (sq_nonneg (Real.log 4 * X * Real.log X))
  have hmoment := hm N hNm j hj
  change (∑ n ∈ s, ‖∫ α in (majorArcs P X)ᶜ ∩ Set.Icc (-T) T,
    LeanLab.ExceptionalSet.OddTail467.integrand P X Δ (F γ n - j) α‖ ^ 2) ≤
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

/-- P0082 page 367 displays 29 and 30. Sum both parity moments on the
floor window, CONDITIONAL ON Lemmas 4, 9 and 10. -/
theorem odd_moment_of_inputs (h4 : Lemma4) (h9 : Lemma9) (h10 : Lemma10) :
    type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp505a.odd_moment_uniform := by
  intro γ h1 h2
  classical
  obtain ⟨δ₀, hδ₀, hm⟩ := parity_moment_of_inputs h4 h9 h10 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, hm⟩ := hm δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨B, hB, N₀, hm⟩ := hm κ hκ hκsmall
  refine ⟨2 * B, by positivity, max 16 N₀, fun N hN => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hN₀ : N₀ ≤ N := (le_max_right _ _).trans hN
  let s := Finset.Ioc (N / 2) N
  let f := fun n : ℕ => R1 (F γ N ^ (6 * δ)) (F γ N) (nuOdd γ n)
  have he := hm N hN₀ 0 (Or.inl rfl)
  have ho := hm N hN₀ 1 (Or.inr rfl)
  simp only [add_zero, sub_zero] at he
  simp only [even_add_one, sub_add_cancel] at ho
  calc
    _ ≤ ∑ n ∈ s, ‖f n‖ ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg
        (LeanLab.ExceptionalSet.UpJ200.Decomp371a.window_subset_Ioc γ h1 N hN16)
        (fun _ _ _ => sq_nonneg _)
    _ = (∑ n ∈ s.filter (fun n => Even (nu γ n)), ‖f n‖ ^ 2) +
        ∑ n ∈ s.filter (fun n => ¬ Even (nu γ n)), ‖f n‖ ^ 2 :=
      (Finset.sum_filter_add_sum_filter_not s (fun n => Even (nu γ n)) _).symm
    _ ≤ B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) +
        B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
      apply add_le_add
      · convert he using 1
        apply Finset.sum_congr rfl
        intro n hn
        have hnO : ¬ Odd (nu γ n) :=
          Int.not_odd_iff_even.mpr (Finset.mem_filter.mp hn).2
        simp [f, nuOdd, hnO]
      · convert ho using 1
        apply Finset.sum_congr (by ext n; simp [s, Int.not_even_iff_odd])
        intro n hn
        have hnO : Odd (nu γ n) := (Finset.mem_filter.mp hn).2
        simp [f, nuOdd, hnO]
    _ = _ := by ring

end OddMoment

section Coefficient
open LeanLab.ExceptionalSet.UpJ200.DecompJ200 (window)
open LeanLab.ExceptionalSet.UpJ200.Decomp505a

/-- P0082 pages 362 to 364. Combine the two even member counts.
CONDITIONAL ON the explicit adjacent count input. -/
theorem even_lower_of_adjacent
    (hadj : type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp527a.adjacent_count_from_inputs) :
    type_of% @leaf_even_lower := by
  intro γ h1 h2
  classical
  obtain ⟨δ₀, hδ₀, ha⟩ := hadj γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, ha⟩ := ha δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c, B, hc, hB, N₀, ha⟩ := ha κ hκ hκsmall
  refine ⟨c, 2 * B, hc, by positivity, N₀, fun N hN => ?_⟩
  let T := c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))
  let s (j : ℤ) := ((window γ N).filter (fun n => Even (nu γ n + j))).filter
    (fun n => (R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + j)).re < T)
  have hsub : (window γ N).filter (fun n =>
      (R1 (F γ N ^ (6 * δ)) (F γ N) (evenIndex γ n)).re < T) ⊆ s 0 ∪ s 1 := by
    intro n hn
    obtain ⟨hnw, hnlt⟩ := mem_filter.mp hn
    by_cases he : Even (nu γ n)
    · apply mem_union.mpr
      left
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨hnw, by simpa using he⟩, ?_⟩
      simpa [evenIndex, he] using hnlt
    · apply mem_union.mpr
      right
      apply mem_filter.mpr
      refine ⟨mem_filter.mpr ⟨hnw, by simpa [Int.even_add_one] using he⟩, ?_⟩
      simpa [evenIndex, he] using hnlt
  have hcard : (((window γ N).filter (fun n =>
      (R1 (F γ N ^ (6 * δ)) (F γ N) (evenIndex γ n)).re < T)).card : ℝ) ≤
      (s 0).card + (s 1).card := by
    exact_mod_cast (card_le_card hsub).trans (card_union_le _ _)
  have he := ha N hN 0 (Or.inl rfl)
  have ho := ha N hN 1 (Or.inr rfl)
  change ((s 0).card : ℝ) ≤ _ at he
  change ((s 1).card : ℝ) ≤ _ at ho
  exact hcard.trans ((add_le_add he ho).trans_eq (by ring))

/-- P0082 page 362 Lemma 7. Combine the even lower bound with the
odd second moment, CONDITIONAL ON the explicit two inputs. -/
theorem coefficient_lower_of_inputs
    (hadj : type_of% @LeanLab.ExceptionalSet.UpJ200.Decomp527a.adjacent_count_from_inputs)
    (hodd : type_of% @odd_moment_uniform) :
    type_of% @coefficient_lower_assembly := by
  intro γ h1 h2
  classical
  obtain ⟨δe, hδe, he⟩ := even_lower_of_adjacent hadj γ h1 h2
  obtain ⟨δo, hδo, ho⟩ := hodd γ h1 h2
  refine ⟨min δe δo, lt_min hδe hδo, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κe, hκe, he⟩ := he δ hδ (hδsmall.trans_le (min_le_left _ _))
  obtain ⟨κo, hκo, ho⟩ := ho δ hδ (hδsmall.trans_le (min_le_right _ _))
  refine ⟨min κe κo, lt_min hκe hκo, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c, Be, hc, hBe, Ne, he⟩ := he κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨Bo, hBo, No, ho⟩ := ho κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨c / 2, Be + 4 * Bo / c ^ 2, by positivity, by positivity,
    max 2 (max Ne No), fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNe : Ne ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNo : No ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hE : 1 ≤ calE γ κ N := by
    apply Real.one_le_exp
    exact mul_nonneg hκ.le (Real.rpow_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _)
  let f : ℕ → ℂ := fun n => R1 (F γ N ^ (6 * δ)) (F γ N) (evenIndex γ n)
  let g : ℕ → ℂ := fun n => R1 (F γ N ^ (6 * δ)) (F γ N) (nuOdd γ n)
  let T := c / 2 * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ))
  have hpair := bad_pair_count (window γ N) f g T
  have hrewrite (n : ℕ) : f n + g n =
      R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n) +
        R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n + 1) :=
    adjacent_sum (R1 (F γ N ^ (6 * δ)) (F γ N)) γ n
  have htwo : 2 * T = c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)) := by
    dsimp [T]
    ring
  simp_rw [hrewrite, htwo] at hpair
  have hodd := odd_bad_count (window γ N) g c Bo (F γ N) (calE γ κ N) N
    hc hBo.le (Real.exp_pos _) hE (ho N hNo)
  have hpairR := Nat.cast_le (α := ℝ).mpr hpair
  push_cast at hpairR
  have heN := he N hNe
  change (((window γ N).filter (fun n => (f n).re <
    c * F γ N * calE γ κ N ^ (-(1 / 10 : ℝ)))).card : ℝ) ≤ _ at heN
  dsimp only [T] at hpairR
  refine hpairR.trans ((add_le_add heN hodd).trans ?_)
  ring_nf
  exact le_rfl

end Coefficient

section Arcs
open LeanLab.ExceptionalSet.DecompJ200

/-- P0082 page 365 Lemma 8. The major bound with its coefficient input
and Lemma 4 explicit. CONDITIONAL ON those inputs. -/
theorem major_bound_of_inputs
    (hcoeff : type_of% @leaf_major_coefficient_lower) (h4 : Lemma4) :
    type_of% @leaf_major_bound := by
  intro γ h1 h2
  classical
  obtain ⟨δ₀, hδ₀, hcoeff⟩ := hcoeff γ h1 h2
  obtain ⟨κb, hκb, hboundary⟩ := full_boundary_of_lemma4 h4 γ (1 / 8) h1 h2 (by norm_num)
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κa, hκa, hcoeff⟩ := hcoeff δ hδ hδsmall
  refine ⟨min κa κb, lt_min hκa hκb, fun κ hκ hκsmall => ?_⟩
  obtain ⟨c₀, Ba, hc₀, hBa, Na, ha⟩ :=
    hcoeff κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨Bb, hBb, Nb, hb⟩ := hboundary κ hκ (hκsmall.trans (min_le_right _ _))
  refine ⟨c₀, Ba + Bb, hc₀, add_pos hBa hBb, max 16 (max Na Nb), fun N hN => ?_⟩
  have hN16 : 16 ≤ N := (le_max_left _ _).trans hN
  have hN2 : 2 ≤ N := by omega
  have hNa : Na ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNb : Nb ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hlog : 0 < Real.log (N : ℝ) := Real.log_pos (by exact_mod_cast hN2)
  have hE : 1 < calE γ κ N := by
    unfold calE
    exact Real.one_lt_exp_iff.mpr (mul_pos hκ (Real.rpow_pos_of_pos hlog _))
  have hΔ : 0 < calE γ κ N ^ (-(1 / 8 : ℝ)) :=
    Real.rpow_pos_of_pos (lt_trans zero_lt_one hE) _
  have hΔ1 : calE γ κ N ^ (-(1 / 8 : ℝ)) < 1 :=
    Real.rpow_lt_one_of_one_lt_of_neg hE (by norm_num)
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
      have hid := leaf_major_identity γ δ κ N n hΔ hΔ1
        (le_of_not_gt (fun h => hgood (Or.inl h)))
        (le_of_not_gt (fun h => hgood (Or.inr h)))
      apply Finset.mem_union_left
      apply Finset.mem_filter.mpr
      exact ⟨hnW, by rwa [hid] at hnmajor⟩
  have hcard : (Eγ_major_block γ δ κ c₀ N : ℝ) ≤ (A.card : ℝ) + B.card := by
    unfold Eγ_major_block
    exact_mod_cast (Finset.card_le_card hsubset).trans (Finset.card_union_le A B)
  have hb' : (B.card : ℝ) ≤ Bb * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := by
    have hsub : B ⊆ (Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
        Int.fract (F γ n) < calE γ κ N ^ (-(1 / 8 : ℝ)) ∨
          1 - calE γ κ N ^ (-(1 / 8 : ℝ)) < Int.fract (F γ n)) := by
      intro n hn
      obtain ⟨hnw, hn⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr
        ⟨LeanLab.ExceptionalSet.UpJ200.Decomp371a.window_subset_Ioc γ h1 N hN16 hnw, hn⟩
    exact (Nat.cast_le.mpr (Finset.card_le_card hsub)).trans (hb N hNb)
  have hpow : calE γ κ N ^ (-(1 / 8 : ℝ)) ≤ calE γ κ N ^ (-(1 / 12 : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_le hE.le (by norm_num)
  calc
    _ ≤ (A.card : ℝ) + B.card := hcard
    _ ≤ Ba * N * calE γ κ N ^ (-(1 / 12 : ℝ)) +
        Bb * N * calE γ κ N ^ (-(1 / 8 : ℝ)) := add_le_add (ha N hNa) hb'
    _ ≤ Ba * N * calE γ κ N ^ (-(1 / 12 : ℝ)) +
        Bb * N * calE γ κ N ^ (-(1 / 12 : ℝ)) := by gcongr
    _ = _ := by ring

/-- P0082 page 366. The minor bound from the explicit Karacuba input.
CONDITIONAL ON Lemma 10 only. -/
theorem minor_bound_of_lemma10 (h10 : Lemma10) :
    type_of% @leaf_minor_bound := by
  intro γ h1 h2
  obtain ⟨δ₀, hδ₀, hm⟩ := minor_truncated_moment_of_karacuba h10 γ h1 h2
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κ₀, hκ₀, hm⟩ := hm δ hδ hδsmall
  refine ⟨κ₀, hκ₀, fun κ hκ hκsmall => ?_⟩
  obtain ⟨B, hB, Nm, hm⟩ := hm κ hκ hκsmall
  obtain ⟨Nt, ht⟩ := leaf_minor_tail γ h1 h2 δ κ hδ hκ
  refine ⟨4 * B, by positivity, max 2 (max Nm Nt), fun N hN => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hNm : Nm ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNt : Nt ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hX : 0 < F γ N := Real.exp_pos _
  have hE : 0 < calE γ κ N := Real.exp_pos _
  have hE1 : 1 ≤ calE γ κ N := by
    apply Real.one_le_exp
    exact mul_nonneg hκ.le (Real.rpow_nonneg
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))) _)
  have hm' : (∑ n ∈ window γ N, ‖minorTruncInt γ δ κ N n‖ ^ 2) ≤
      B * N * F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)) :=
    (hm N hNm).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hE1 (by norm_num)) (by positivity))
  have hT : 0 < F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) :=
    mul_pos hX (Real.rpow_pos_of_pos hE _)
  have hc := minor_count_chebyshev (window γ N)
    (minorInt γ δ κ N) (minorTruncInt γ δ κ N)
    (F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)))
    (B * N * F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)))
    hT (fun n _ => ht N hNt n) hm'
  change (Eγ_minor_block γ δ κ N : ℝ) *
    (F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) / 2) ^ 2 ≤ _ at hc
  have hp : calE γ κ N ^ (-(3 / 4 : ℝ)) =
      calE γ κ N ^ (-(1 / 12 : ℝ)) * (calE γ κ N ^ (-(1 / 3 : ℝ))) ^ 2 := by
    rw [← Real.rpow_mul_natCast hE.le, ← Real.rpow_add hE]
    congr 1
    norm_num
  have hfactor : B * (N : ℝ) * F γ N ^ 2 * calE γ κ N ^ (-(3 / 4 : ℝ)) =
      (4 * B * N * calE γ κ N ^ (-(1 / 12 : ℝ))) *
        (F γ N * calE γ κ N ^ (-(1 / 3 : ℝ)) / 2) ^ 2 := by
    rw [hp]
    ring
  rw [hfactor] at hc
  exact (mul_le_mul_iff_left₀ (sq_pos_of_pos (half_pos hT))).mp hc

/-- P0082 page 366. Synchronize the arc parameters and count exceptions.
CONDITIONAL ON the explicit major and minor estimates. -/
theorem block_bound_of_arc_inputs
    (hmajor : type_of% @leaf_major_bound) (hminor : type_of% @leaf_minor_bound) :
    type_of% @block_bound := by
  intro γ h1 h2
  obtain ⟨δ₁, hδ₁, hmin⟩ := hminor γ h1 h2
  obtain ⟨δ₂, hδ₂, hmaj⟩ := hmajor γ h1 h2
  have hδ : 0 < min δ₁ δ₂ / 2 := half_pos (lt_min hδ₁ hδ₂)
  have hδ1 : min δ₁ δ₂ / 2 < δ₁ := by
    have := min_le_left δ₁ δ₂
    have := lt_min hδ₁ hδ₂
    linarith
  have hδ2 : min δ₁ δ₂ / 2 < δ₂ := by
    have := min_le_right δ₁ δ₂
    have := lt_min hδ₁ hδ₂
    linarith
  obtain ⟨κ₁, hκ₁, hmin⟩ := hmin _ hδ hδ1
  obtain ⟨κ₂, hκ₂, hmaj⟩ := hmaj _ hδ hδ2
  have hκ : 0 < min κ₁ κ₂ := lt_min hκ₁ hκ₂
  obtain ⟨B₁, hB₁, N₁, hmin⟩ := hmin _ hκ (min_le_left _ _)
  obtain ⟨c₀, B₂, hc₀, hB₂, N₂, hmaj⟩ := hmaj _ hκ (min_le_right _ _)
  obtain ⟨N₃, hsplit⟩ :=
    leaf_dyadic_split γ (min δ₁ δ₂ / 2) (min κ₁ κ₂) c₀ h1 h2 hδ hκ hc₀
  refine ⟨min κ₁ κ₂, B₁ + B₂, hκ, add_pos hB₁ hB₂,
    max N₁ (max N₂ N₃), fun N hN => ?_⟩
  have h₁ := hmin N (le_trans (le_max_left _ _) hN)
  have h₂ := hmaj N (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN)
  have h₃ := hsplit N (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN)
  have h₃' : (blockCount γ (fun n => ¬ Solvable γ n) N : ℝ) ≤
      Eγ_minor_block γ (min δ₁ δ₂ / 2) (min κ₁ κ₂) N +
        Eγ_major_block γ (min δ₁ δ₂ / 2) (min κ₁ κ₂) c₀ N := by exact_mod_cast h₃
  calc
    _ ≤ _ := h₃'
    _ ≤ _ := add_le_add h₁ h₂
    _ = _ := by ring

end Arcs

/-- P0082 page 354 Theorem 1, assembled through pages 362 to 370.
CONDITIONAL ON exactly six named citation walls: Karacuba, Erdos-Turan,
the nonexceptional major formula, the coprime major formula, the prime
product case and the near-zero major formula. No admitted result is used. -/
theorem theorem1_of_named_citation_walls
    (hK : LeanLab.ExceptionalSet.U1539.DQLemma10.KaracubaThm1Named)
    (hET : LeanLab.ExceptionalSet.DQLemma4.ErdosTuranDQ4)
    (hL : LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected.Lemma2NoExcBP)
    (hL3 : LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected.BPLemma3CoprimeHyp)
    (hP : LeanLab.ExceptionalSet.UpJ200.DQLeafPrimeProductSelected.PrimeProductSelectedP0082)
    (hII : LeanLab.ExceptionalSet.UpJ200.DQLeafNearZeroSelected.CaseIIdMajorLowerHyp) :
    Theorem1 := by
  have hT := LeanLab.ExceptionalSet.U1539.DQLemma10.theorem2_of_karacuba_named hK
  have h10 := LeanLab.ExceptionalSet.U1539.DQLemma10.lemma10_of_karacuba_named hK
  have h4 := LeanLab.ExceptionalSet.DQLemma4.lemma4_of_erdosTuran_theorem2 hET hT
  have h9 := LeanLab.ExceptionalSet.Prep1121Lemma9Wire.lemma9_of_theorem2_lemma4_wired hT h4
  have hadj := LeanLab.ExceptionalSet.UpJ200.DQDecomp559bAssembly.adjacent_count_of_hyps
    h4 hL LeanLab.ExceptionalSet.UpJ200.Prep1121SingSeries.singularSeriesEvenLowerBP_split
    hL3 hP hII LeanLab.ExceptionalSet.Task672.realZeroDistanceHyp_proved672
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

#print axioms full_boundary_of_lemma4
#print axioms shifted_moment_of_inputs
#print axioms parity_moment_of_inputs
#print axioms odd_moment_of_inputs
#print axioms even_lower_of_adjacent
#print axioms coefficient_lower_of_inputs
#print axioms major_bound_of_inputs
#print axioms minor_bound_of_lemma10
#print axioms block_bound_of_arc_inputs
#print axioms theorem1_of_named_citation_walls

end LeanLab.ExceptionalSet.Prep1122MainWire
