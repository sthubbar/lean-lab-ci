import LeanLab.ExceptionalSet.UpJ200.Decomp539a

namespace LeanLab.ExceptionalSet.UpJ200.Decomp509a
open Real Finset Filter Topology MeasureTheory
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)
open LeanLab.ExceptionalSet.U1539 (nu calE R1 majorArcs)

/-- P0082 page368 display33 from page359 Lemma4.
A free boundary width is controlled on the entire half interval.
CONDITIONAL ON the cited discrepancy input U1539.lemma4. -/
theorem full_boundary_at_rate (γ a : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (ha : 0 < a) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
        (((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
          Int.fract (F γ n) < calE γ κ N ^ (-a) ∨
            1 - calE γ κ N ^ (-a) < Int.fract (F γ n))).card : ℝ) ≤
          B * N * calE γ κ N ^ (-a) := by
  classical
  obtain ⟨κa, A, hκa, hdisc⟩ := LeanLab.ExceptionalSet.U1539.lemma4 γ h1 h2
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


/-- P0082 page368 displays33 to35, derived error margin.
The free width E to minus five twelfths and height E to two thirds
leave enough decay for the two logarithms in both error terms. -/
theorem shifted_error_budget (X E B : ℝ) (N : ℕ)
    (hE : 1 ≤ E) (hB : 0 ≤ B)
    (hlog : Real.log X ^ 2 ≤ E ^ (1 / 12 : ℝ)) :
    2 * N * (8 * (Real.log 4 * X * Real.log X) /
      (E ^ (-(5 / 12 : ℝ)) * Real.pi ^ 2 * E ^ (2 / 3 : ℝ))) ^ 2 +
      (B * N * E ^ (-(5 / 12 : ℝ))) * (Real.log 4 * X * Real.log X) ^ 2 ≤
        (128 * Real.log 4 ^ 2 / Real.pi ^ 4 + B * Real.log 4 ^ 2) *
          N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by
  have hE0 : 0 < E := lt_of_lt_of_le zero_lt_one hE
  have ht : (E ^ (-(5 / 12 : ℝ)) * E ^ (2 / 3 : ℝ)) ^ 2 = E ^ (1 / 2 : ℝ) := by
    rw [← Real.rpow_add hE0, ← Real.rpow_mul_natCast hE0.le]
    norm_num
  have htail : (8 * (Real.log 4 * X * Real.log X) /
      (E ^ (-(5 / 12 : ℝ)) * Real.pi ^ 2 * E ^ (2 / 3 : ℝ))) ^ 2 =
      (64 * Real.log 4 ^ 2 / Real.pi ^ 4) * X ^ 2 * Real.log X ^ 2 *
        E ^ (-(1 / 2 : ℝ)) := by
    conv_rhs => rw [Real.rpow_neg hE0.le]
    rw [div_pow]
    have hd : (E ^ (-(5 / 12 : ℝ)) * Real.pi ^ 2 * E ^ (2 / 3 : ℝ)) ^ 2 =
        Real.pi ^ 4 * E ^ (1 / 2 : ℝ) := by
      calc _ = Real.pi ^ 4 * (E ^ (-(5 / 12 : ℝ)) * E ^ (2 / 3 : ℝ)) ^ 2 := by ring
           _ = _ := by rw [ht]
    rw [hd]
    ring
  have hp (a : ℝ) :
      Real.log X ^ 2 * E ^ a ≤ E ^ (a + 1 / 12) := by
    calc _ ≤ E ^ (1 / 12 : ℝ) * E ^ a :=
        mul_le_mul_of_nonneg_right hlog (Real.rpow_pos_of_pos hE0 _).le
         _ = _ := by rw [← Real.rpow_add hE0]; congr 1; ring
  have htlog : Real.log X ^ 2 * E ^ (-(1 / 2 : ℝ)) ≤ E ^ (-(1 / 3 : ℝ)) := by
    refine (hp (-(1 / 2 : ℝ))).trans ?_
    exact Real.rpow_le_rpow_of_exponent_le hE (by norm_num)
  have hblog : Real.log X ^ 2 * E ^ (-(5 / 12 : ℝ)) ≤ E ^ (-(1 / 3 : ℝ)) := by
    convert hp (-(5 / 12 : ℝ)) using 1 <;> norm_num
  rw [htail]
  calc
    _ = (128 * Real.log 4 ^ 2 / Real.pi ^ 4) * N * X ^ 2 *
          (Real.log X ^ 2 * E ^ (-(1 / 2 : ℝ))) +
        (B * Real.log 4 ^ 2) * N * X ^ 2 *
          (Real.log X ^ 2 * E ^ (-(5 / 12 : ℝ))) := by ring
    _ ≤ (128 * Real.log 4 ^ 2 / Real.pi ^ 4) * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) +
        (B * Real.log 4 ^ 2) * N * X ^ 2 * E ^ (-(1 / 3 : ℝ)) := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_left htlog (by positivity)
      · exact mul_le_mul_of_nonneg_left hblog (by positivity)
    _ = _ := by ring


/-- LEAF: P0082 page368 display35 and page369 displays37 to39.
The full parity sets retain cancellation. The free width and height have
extra logarithmic margins. Only this truncated sparse moment remains analytic. -/
theorem leaf_shifted_parity_moment (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ j : ℤ, (j = 0 ∨ j = 1) →
            (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + j)),
              ‖∫ α in (majorArcs (F γ N ^ (6 * δ)) (F γ N))ᶜ ∩
                Set.Icc (-(calE γ κ N ^ (2 / 3 : ℝ))) (calE γ κ N ^ (2 / 3 : ℝ)),
                OddTail467.integrand (F γ N ^ (6 * δ)) (F γ N)
                  (calE γ κ N ^ (-(5 / 12 : ℝ))) (F γ n - j) α‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  exact Decomp539a.parity_moment_from_gap γ h1 h2

/-- P0082 page367 displays29 and30 from page368 display35.
The full interval discrepancy bound and explicit tail budget discharge all
boundary and truncation steps. CONDITIONAL ON the shifted analytic moment
and the cited discrepancy input U1539.lemma4. -/
theorem parity_moment_from_shifted (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
        ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
          ∀ j : ℤ, (j = 0 ∨ j = 1) →
            (∑ n ∈ (Finset.Ioc (N / 2) N).filter (fun n => Even (nu γ n + j)),
              ‖R1 (F γ N ^ (6 * δ)) (F γ N) (nu γ n - j + 1)‖ ^ 2) ≤
              B * N * F γ N ^ 2 * calE γ κ N ^ (-(1 / 3 : ℝ)) := by
  classical
  obtain ⟨δ₀, hδ₀, hm⟩ := leaf_shifted_parity_moment γ h1 h2
  obtain ⟨κb, hκb, hb⟩ := full_boundary_at_rate γ (5 / 12) h1 h2 (by norm_num)
  refine ⟨δ₀, hδ₀, fun δ hδ hδsmall => ?_⟩
  obtain ⟨κm, hκm, hm⟩ := hm δ hδ hδsmall
  refine ⟨min κm κb, lt_min hκm hκb, fun κ hκ hκsmall => ?_⟩
  obtain ⟨Bm, hBm, Nm, hm⟩ := hm κ hκ (hκsmall.trans (min_le_left _ _))
  obtain ⟨Bb, hBb, Nb, hb⟩ := hb κ hκ (hκsmall.trans (min_le_right _ _))
  obtain ⟨Np, hp⟩ := TailParameters385.tail_parameters_eventually γ h1 h2 δ κ hδ hκ
  obtain ⟨Nl, hl⟩ := Decomp467a.log_F_sq_le_calE_twelfth γ κ h1 h2 hκ
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
  have herrors := shifted_error_budget X E Bb N hE.le hBb.le (hl N hNl)
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

end LeanLab.ExceptionalSet.UpJ200.Decomp509a
