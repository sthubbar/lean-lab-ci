/-
Burst 20261122, session S64 group C, wiring for unit
DecompC165d.upper_normalized_raw_conditions_slack. P0069 Baker Harman Pintz 1997, pages 1 to 4
and Section 5, pages 43 to 53. The route of `AssemblyC165.theorem1` reached the slack LEAF through
DecompC165d.upper_short_weight, whose proof is `upper_short_weight_of_slack_leaf`. The verbatim
copy `upper_short_weight_of_upslack_route` of Wire1122UpperShortSlackRoute goes through
`upslack_route` instead. DecompC165d, DecompC165b and AssemblyC165 cannot import that file without
editing existing proofs, so this NEW file gives routed copies with verbatim statements of
DecompC165d.upper_short_weight, DecompC165d.section5_weights, DecompC165b.section5_weights,
DecompC165b.sieve_data and AssemblyC165.theorem1, each proof the original one with the single
input swapped. No new definition, no sorry of its own.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.AssemblyC165
import LeanLab.BHP1997.Wire1122UpperShortSlackRoute

namespace LeanLab.BHP1997.Wire1122S64
open Classical Complex Real Filter Decomp132 DecompC165b

/-- P0069, page 53. Verbatim statement of `DecompC165d.upper_short_weight`, proved through
`DecompC165d.upper_short_weight_of_upslack_route` instead of the slack LEAF. -/
theorem upper_short_weight (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v1 : ℝ) (b1 : ℝ → ℕ → ℝ),
        v1 < 2.2 ∧ RightConditions ε B v1 b1 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x, primeWeight m ≤ b1 x m :=
  DecompC165d.upper_short_weight_of_upslack_route h4 h9

/-- P0069, pages 43 to 53. Verbatim statement of `DecompC165d.section5_weights`, the original
proof with `upper_short_weight` taken from the upslack route. -/
theorem section5_weights_d (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v0 v1 : ℝ) (b0 b1 : ℝ → ℕ → ℝ),
        0.05 < v0 ∧ v0 ≤ v1 ∧ v1 < 2.2 ∧
        RightConditions ε B v0 b0 ∧ RightConditions ε B v1 b1 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x,
            b0 x m ≤ primeWeight m ∧ primeWeight m ≤ b1 x m := by
  obtain ⟨B0, η0, hη0, h0⟩ := DecompC165d.lower_short_weight h4 h9
  obtain ⟨B1, η1, hη1, h1⟩ := Wire1122S64.upper_short_weight h4 h9
  refine ⟨max B0 B1, min η0 η1, lt_min hη0 hη1, ?_⟩
  intro B ε hB hε hεη
  obtain ⟨v0, b0, hv0, hb0, X0, hs0⟩ := h0 B ε
    (le_trans (le_max_left _ _) hB) hε (lt_of_lt_of_le hεη (min_le_left _ _))
  obtain ⟨v1, b1, hv1, hb1, X1, hs1⟩ := h1 B ε
    (le_trans (le_max_right _ _) hB) hε (lt_of_lt_of_le hεη (min_le_right _ _))
  have hsand : ∀ x : ℝ, max X0 X1 ≤ x → ∀ m ∈ rightInterval ε x,
      b0 x m ≤ primeWeight m ∧ primeWeight m ≤ b1 x m := fun x hx m hm =>
    ⟨hs0 x (le_trans (le_max_left _ _) hx) m hm,
      hs1 x (le_trans (le_max_right _ _) hx) m hm⟩
  have hmono : v0 ≤ v1 := DecompC165d.right_density_mono hε hb0 hb1
    ⟨max X0 X1, fun x hx m hm => (hsand x hx m hm).1.trans (hsand x hx m hm).2⟩
  exact ⟨v0, v1, b0, b1, hv0, hmono, hv1, hb0, hb1, max X0 X1, hsand⟩

/-- P0069, Section 5. Verbatim statement of `DecompC165b.section5_weights`. -/
theorem section5_weights (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v0 v1 : ℝ) (b0 b1 : ℝ → ℕ → ℝ),
        0.05 < v0 ∧ v0 ≤ v1 ∧ v1 < 2.2 ∧
        RightConditions ε B v0 b0 ∧ RightConditions ε B v1 b1 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x,
            b0 x m ≤ primeWeight m ∧ primeWeight m ≤ b1 x m := by
  exact section5_weights_d h4 h9

/-- P0069, pages 1 to 4 and Sections 2 to 5. Verbatim statement of `DecompC165b.sieve_data`, the
original proof with `section5_weights` taken from the upslack route. -/
theorem sieve_data :
    ∃ ε u0 u1 v0 v1 : ℝ, 0 < ε ∧ ε < 8.8 / 10 ^ 5 ∧
      0.99 < u0 ∧ u0 ≤ u1 ∧ u1 < 1.01 ∧ 0.05 < v0 ∧ v0 ≤ v1 ∧ v1 < 2.2 ∧
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
        ∃ (I J : Finset ℕ) (a0 a1 b0 b1 : ℕ → ℝ) (E : Finset ℕ),
          (∀ k ∈ I, a0 k ≤ primeWeight k ∧ primeWeight k ≤ a1 k) ∧
          (∀ m ∈ J, b0 m ≤ primeWeight m ∧ primeWeight m ≤ b1 m) ∧
          (E.card : ℝ) < x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) /
            Real.log x ^ A ∧
          ∀ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊,
            Even N → N ∉ E → ∃ r : ℝ, 0 < r ∧
              |convolution I J a0 b1 N - u0 * v1 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 ∧
              |convolution I J a1 b0 N - u1 * v0 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 ∧
              |convolution I J a1 b1 N - u1 * v1 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 := by
  have h4 := section3_mean_values
  obtain ⟨Bl, ηl, hηl, hl⟩ := section4_lower h4
  obtain ⟨Bu, ηu, hηu, hu⟩ := section4_upper h4
  obtain ⟨Br, ηr, hηr, hr⟩ := Wire1122S64.section5_weights h4 DecompC165a.lemma9
  obtain ⟨η2, hη2, h2⟩ := section2_circle_method_pos (max Bl (max Bu Br))
  let η := min η2 (min ηl (min ηu (min ηr (8.8 / 10 ^ 5))))
  have hη : 0 < η := by dsimp [η]; positivity
  let ε := η / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεη : ε < η := by dsimp [ε]; linarith
  have hε2 : ε < η2 := lt_of_lt_of_le hεη (min_le_left _ _)
  have hεl : ε < ηl := lt_of_lt_of_le hεη
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεu : ε < ηu := lt_of_lt_of_le hεη
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hεr : ε < ηr := lt_of_lt_of_le hεη
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hε1 : ε < 8.8 / 10 ^ 5 := lt_of_lt_of_le hεη
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))))
  let B := max Bl (max Bu Br)
  obtain ⟨u0, a0, hu0, hu01, ha0, X0, hs0⟩ := hl B ε (le_max_left _ _) hε hεl
  obtain ⟨u1, a1, hu11, hu1, ha1, X1, hs1⟩ := hu B ε
    (le_trans (le_max_left _ _) (le_max_right _ _)) hε hεu
  obtain ⟨v0, v1, b0, b1, hv0, hv, hv1, hb0, hb1, Xb, hsb⟩ := hr B ε
    (le_trans (le_max_right _ _) (le_max_right _ _)) hε hεr
  have hu0' : 0.99 < u0 := by linarith
  have hu' : u0 ≤ u1 := le_trans hu01 hu11
  have hu1' : u1 < 1.01 := by linarith
  refine ⟨ε, u0, u1, v0, v1, hε, hε1, hu0', hu', hu1', hv0, hv, hv1, ?_⟩
  exact correlation_transfer_pos (h2 ε hε hε2) hε hε1 hu0' hu' hu1' hv0 hv hv1
    ha0 ha1 hb0 hb1 ⟨max X0 (max X1 Xb), fun x hx =>
      ⟨fun k hk => ⟨hs0 x (le_trans (le_max_left _ _) hx) k hk,
        hs1 x (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) k hk⟩,
       hsb x (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx)⟩⟩

/-- P0069, Theorem 1, pages 1 to 4. Verbatim statement of `AssemblyC165.theorem1`, the original
proof with `sieve_data` taken from the upslack route. No direct sorry; CONDITIONAL on the leaves
below it. -/
theorem theorem1 : Theorem1 := by
  obtain ⟨ε, u0, u1, v0, v1, hε, hε1, hu0, hu, hu1, hv0, hv, hv1, hdata⟩ := Wire1122S64.sieve_data
  have hm := constants15 hu0 hu hu1 hv0 hv hv1
  have hδ := theta12 hε hε1
  intro θ hθ
  apply cover_short_intervals
    (by linarith : 0 < (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))
    (by linarith : (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) < 1)
    (lt_of_lt_of_le hδ.1 hθ)
  intro A hA
  obtain ⟨C, hC⟩ := hdata A hA
  refine ⟨C, fun x hx => ?_⟩
  obtain ⟨I, J, a0, a1, b0, b1, E, ha, hb, hE, hcorr⟩ := hC x hx
  have hsub : (Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
      (fun N => Even N ∧ ¬ IsGoldbachSum N) ⊆ E := by
    intro N hN
    obtain ⟨hNI, hEven, hnot⟩ := Finset.mem_filter.mp hN
    by_contra hNE
    obtain ⟨r, hr, h01, h10, h11⟩ := hcorr N hNI hEven hNE
    have hpos := correlation_positive hm hr h01 h10 h11
    have hle := convolution_sandwich ha hb N
    rw [prime_convolution_zero I J hnot] at hle
    linarith
  exact lt_of_le_of_lt (by exact_mod_cast Finset.card_le_card hsub) hE

end LeanLab.BHP1997.Wire1122S64
