import LeanLab.Pintz2021.Decomp393b

/-!
A fixed finite data characterization of the unbounded cutoff estimate.
Source: arXiv:1804.05561v1 page 9 display 2.12.
This is a derived logical audit, not a uniform estimate in the paper parameters.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.Decomp393c

open Filter Topology Finset State1581 DecompJ281 Truncation168 Decomp393a

attribute [local instance] Classical.propDecidable

/-- At fixed finite data, an all U decaying bound exists exactly when lcm discarded terms cancel. -/
theorem all_cutoff_bound_iff_discarded_lcm_sum_eq_zero (E : Finset ExcPair)
    (Sg : ExcPair → ExcPair → ℕ → ℂ) (ε X P : ℝ) (m : ℕ) :
    (∃ A : ℝ, 0 < A ∧ ∀ U : ℝ, 2 ≤ U →
      ‖mainTermPrime (E : Set ExcPair) Sg ε X m -
        mainTermTruncatedPrime (E : Set ExcPair) Sg ε X P U m‖ ≤
          A * (Real.log U / Real.sqrt U)) ↔
    ∑ p ∈ (E ×ˢ E).filter (fun p => P < (Nat.lcm p.1.r p.2.r : ℝ)),
      pairTerm Sg ε X m p = 0 := by
  constructor
  · rintro ⟨A, _, hA⟩
    apply discarded_lcm_sum_eq_zero_of_eventual_bound E Sg ε X P A m
    filter_upwards [eventually_ge_atTop (2 : ℝ)] with U hU using hA U hU
  · intro hzero
    obtain ⟨B0, hB⟩ := (error_eventually_zero_of_discarded_lcm_sum_eq_zero
      E Sg ε X P m hzero).exists_forall_of_atTop
    let B : ℝ := max B0 2
    have hB2 : 2 ≤ B := le_max_right _ _
    have hBpos : 0 < Real.sqrt B := Real.sqrt_pos.mpr (by linarith)
    let M : ℝ := ∑ p ∈ E ×ˢ E, ‖pairTerm Sg ε X m p‖
    have hM : 0 ≤ M := sum_nonneg (fun _ _ => norm_nonneg _)
    have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
    let A : ℝ := M * Real.sqrt B / Real.log 2 + 1
    have hA : 0 < A := by dsimp [A]; positivity
    refine ⟨A, hA, fun U hU => ?_⟩
    by_cases hBU : B ≤ U
    · rw [hB U ((le_max_left B0 2).trans hBU), sub_self, norm_zero]
      exact mul_nonneg hA.le
        (div_nonneg (Real.log_nonneg (by linarith)) (Real.sqrt_nonneg _))
    · have hUB : U ≤ B := (lt_of_not_ge hBU).le
      have hUpos : 0 < Real.sqrt U := Real.sqrt_pos.mpr (by linarith)
      have herr : ‖mainTermPrime (E : Set ExcPair) Sg ε X m -
          mainTermTruncatedPrime (E : Set ExcPair) Sg ε X P U m‖ ≤ M := by
        rw [DecompJ665.truncatedPrime_eq_finite]
        apply (norm_truncation_error_le E Sg ε X P U m).trans
        exact sum_le_sum_of_subset_of_nonneg sdiff_subset (fun _ _ _ => norm_nonneg _)
      have hratio : Real.log 2 / Real.sqrt B ≤ Real.log U / Real.sqrt U := by
        calc
          _ ≤ Real.log 2 / Real.sqrt U :=
            div_le_div_of_nonneg_left hlog2.le hUpos (Real.sqrt_le_sqrt hUB)
          _ ≤ _ := div_le_div_of_nonneg_right
            (Real.log_le_log (by norm_num) hU) (Real.sqrt_nonneg _)
      have hMA : M ≤ A * (Real.log 2 / Real.sqrt B) := by
        have heq : A * (Real.log 2 / Real.sqrt B) = M + Real.log 2 / Real.sqrt B := by
          dsimp [A]
          field_simp [hlog2.ne', hBpos.ne']
        rw [heq]
        exact le_add_of_nonneg_right (div_nonneg hlog2.le hBpos.le)
      exact herr.trans (hMA.trans (mul_le_mul_of_nonneg_left hratio hA.le))

/-- More consecutive disjoint bands than finite thresholds leave an empty band. -/
theorem exists_empty_band (S : Finset ℝ) (f : ℕ → ℝ) (hf : StrictAnti f) :
    ∃ k ∈ range (S.card + 1), ∀ t ∈ S, ¬ (f (k + 1) < t ∧ t ≤ f k) := by
  classical
  by_contra! hn
  let bands : ℕ → Finset ℝ := fun k => S.filter (fun t => f (k + 1) < t ∧ t ≤ f k)
  have hne : ∀ k ∈ range (S.card + 1), (bands k).Nonempty := by
    intro k hk
    obtain ⟨t, ht, hlo, hhi⟩ := hn k hk
    exact ⟨t, mem_filter.mpr ⟨ht, hlo, hhi⟩⟩
  have hd : (range (S.card + 1) : Set ℕ).PairwiseDisjoint bands := by
    intro i _ j _ hij
    apply disjoint_left.mpr
    intro t hti htj
    have hi := (mem_filter.mp hti).2
    have hj := (mem_filter.mp htj).2
    rcases lt_or_gt_of_ne hij with hij | hji
    · have hstep : f j ≤ f (i + 1) := hf.antitone (by omega)
      linarith
    · have hstep : f i ≤ f (j + 1) := hf.antitone (by omega)
      linarith
  have hcard := card_le_card_biUnion hd hne
  have hsub : (range (S.card + 1)).biUnion bands ⊆ S := by
    intro t ht
    obtain ⟨k, _, hkt⟩ := mem_biUnion.mp ht
    exact (mem_filter.mp hkt).1
  have hle := card_le_card hsub
  simp only [card_range] at hcard
  omega

/-- The finite geometric gap selection used to choose the major arc level. -/
theorem exists_geometric_gap (S : Finset ℝ) {P0 a : ℝ}
    (hP0 : 0 < P0) (ha0 : 0 < a) (ha1 : a < 1) :
    ∃ P : ℝ, P0 * a ^ S.card ≤ P ∧ P ≤ P0 ∧
      ∀ t ∈ S, t ≤ P → t ≤ P * a := by
  have hf : StrictAnti (fun k : ℕ => P0 * a ^ k) :=
    fun _ _ hij => mul_lt_mul_of_pos_left (pow_right_strictAnti₀ ha0 ha1 hij) hP0
  obtain ⟨k, hk, hgap⟩ := exists_empty_band S _ hf
  refine ⟨P0 * a ^ k, hf.antitone (by have hk' := mem_range.mp hk; omega), ?_, ?_⟩
  · simpa using hf.antitone (Nat.zero_le k)
  · intro t ht htP
    apply le_of_not_gt
    intro hgt
    apply hgap t ht
    exact ⟨by simpa [pow_succ, mul_assoc] using hgt, htP⟩

/-- The paper scale admits a level with a finite threshold gap inside the prescribed interval. -/
theorem exists_level_with_finite_gap (S : Finset ℝ) {X ε P0 : ℝ}
    (hX : 1 < X) (hε : 0 < ε) (hP0 : 0 < P0) :
    ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
      ∀ t ∈ S, t ≤ P → t ≤ P * X ^ (-(ε / ((S.card : ℝ) + 1))) := by
  let δ : ℝ := ε / ((S.card : ℝ) + 1)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hX0 : 0 < X := zero_lt_one.trans hX
  obtain ⟨P, hlo, hhi, hgap⟩ := exists_geometric_gap S hP0
    (Real.rpow_pos_of_pos hX0 (-δ))
    (Real.rpow_lt_one_of_one_lt_of_neg hX (neg_neg_of_pos hδ))
  have hexp : -ε ≤ -δ * (S.card : ℝ) := by
    have hd : δ * ((S.card : ℝ) + 1) = ε := by
      dsimp [δ]
      exact div_mul_cancel₀ _ (by positivity)
    nlinarith
  have hpow : X ^ (-ε) ≤ (X ^ (-δ)) ^ S.card := by
    rw [← Real.rpow_mul_natCast hX0.le]
    exact Real.rpow_le_rpow_of_exponent_le hX.le hexp
  exact ⟨P, (mul_le_mul_of_nonneg_left hpow hP0.le).trans hlo, hhi, hgap⟩

/-- A supplied cardinal bound gives a uniform exponent in the finite gap selection. -/
theorem exists_level_with_gap_of_card_le (S : Finset ℝ) {N : ℕ}
    (hcard : S.card ≤ N) {X ε P0 : ℝ}
    (hX : 1 < X) (hε : 0 < ε) (hP0 : 0 < P0) :
    ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
      ∀ t ∈ S, t ≤ P → t ≤ P * X ^ (-(ε / ((N : ℝ) + 1))) := by
  obtain ⟨P, hlo, hhi, hgap⟩ := exists_level_with_finite_gap S hX hε hP0
  have hX0 : 0 < X := zero_lt_one.trans hX
  have hP : 0 ≤ P := (mul_pos hP0 (Real.rpow_pos_of_pos hX0 _)).le.trans hlo
  have hden : (S.card : ℝ) + 1 ≤ (N : ℝ) + 1 := by exact_mod_cast Nat.add_le_add_right hcard 1
  have hdiv : ε / ((N : ℝ) + 1) ≤ ε / ((S.card : ℝ) + 1) :=
    div_le_div_of_nonneg_left hε.le (by positivity) hden
  have hpow : X ^ (-(ε / ((S.card : ℝ) + 1))) ≤ X ^ (-(ε / ((N : ℝ) + 1))) :=
    Real.rpow_le_rpow_of_exponent_le hX.le (neg_le_neg hdiv)
  exact ⟨P, hlo, hhi, fun t ht htP =>
    (hgap t ht htP).trans (mul_le_mul_of_nonneg_left hpow hP)⟩

/-- Every finite exceptional family admits the pair lcm gap from display 10.6. -/
theorem exists_level_with_pair_lcm_gap (E : Finset ExcPair) {X ε P0 : ℝ}
    (hX : 1 < X) (hε : 0 < ε) (hP0 : 0 < P0) :
    ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
      ∀ z ∈ E, ∀ w ∈ E, (Nat.lcm z.r w.r : ℝ) ≤ P →
        (Nat.lcm z.r w.r : ℝ) ≤ P * X ^ (-(ε / (((E.card ^ 2 : ℕ) : ℝ) + 1))) := by
  classical
  let S : Finset ℝ := (E ×ˢ E).image (fun p => (Nat.lcm p.1.r p.2.r : ℝ))
  have hcard : S.card ≤ E.card ^ 2 := by
    calc
      _ ≤ (E ×ˢ E).card := card_image_le
      _ = _ := by rw [card_product, pow_two]
  obtain ⟨P, hlo, hhi, hgap⟩ := exists_level_with_gap_of_card_le S hcard hX hε hP0
  refine ⟨P, hlo, hhi, fun z hz w hw hl => ?_⟩
  exact hgap _ (mem_image.mpr ⟨(z, w), mem_product.mpr ⟨hz, hw⟩, rfl⟩) hl

/-- Both lcm and height gaps of display 10.6 follow from a finite family of thresholds. -/
theorem exists_level_with_pair_and_height_gaps (E : Finset ExcPair) {X ε P0 : ℝ}
    (hX : 1 < X) (hε : 0 < ε) (hP0 : 0 < P0) :
    ∃ δ P : ℝ, 0 < δ ∧ P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
      (∀ z ∈ E, ∀ w ∈ E, (Nat.lcm z.r w.r : ℝ) ≤ P →
        (Nat.lcm z.r w.r : ℝ) ≤ P * X ^ (-δ)) ∧
      ∀ z ∈ E, |z.ρ.im| ≤ P / z.r * X ^ δ →
        |z.ρ.im| ≤ P / z.r * X ^ (-4 * δ) := by
  classical
  let N : ℕ := E.card ^ 2 + E.card
  let δ : ℝ := ε / (10 * ((E.card : ℝ) + 1) ^ 2)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hX0 : 0 < X := zero_lt_one.trans hX
  let S1 : Finset ℝ := (E ×ˢ E).image (fun p => (Nat.lcm p.1.r p.2.r : ℝ))
  let S2 : Finset ℝ := E.image (fun z => |z.ρ.im| * z.r * X ^ (-δ))
  let S : Finset ℝ := S1 ∪ S2
  have hcard : S.card ≤ N := by
    calc
      _ ≤ S1.card + S2.card := card_union_le _ _
      _ ≤ (E ×ˢ E).card + E.card := Nat.add_le_add card_image_le card_image_le
      _ = N := by simp [N, card_product, pow_two]
  have hN : (N : ℝ) + 1 ≤ 2 * ((E.card : ℝ) + 1) ^ 2 := by
    dsimp [N]
    push_cast
    nlinarith [Nat.cast_nonneg (α := ℝ) E.card]
  have hden : 0 < (N : ℝ) + 1 := by positivity
  have hδ5 : 5 * δ ≤ ε / ((N : ℝ) + 1) := by
    apply (le_div_iff₀ hden).mpr
    have hd : δ * (10 * ((E.card : ℝ) + 1) ^ 2) = ε := by
      dsimp [δ]
      exact div_mul_cancel₀ _ (by positivity)
    nlinarith [mul_le_mul_of_nonneg_left hN hδ.le]
  obtain ⟨P, hlo, hhi, hgap⟩ := exists_level_with_gap_of_card_le S hcard hX hε hP0
  have hP : 0 ≤ P := (mul_pos hP0 (Real.rpow_pos_of_pos hX0 _)).le.trans hlo
  have hpow5 : X ^ (-(ε / ((N : ℝ) + 1))) ≤ X ^ (-5 * δ) :=
    Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)
  have hsmall : ∀ t ∈ S, t ≤ P → t ≤ P * X ^ (-5 * δ) :=
    fun t ht htP => (hgap t ht htP).trans (mul_le_mul_of_nonneg_left hpow5 hP)
  have hpowcancel : X ^ (-δ) * X ^ δ = 1 := by
    rw [← Real.rpow_add hX0]
    simp
  have hpowshift : X ^ (-5 * δ) * X ^ δ = X ^ (-4 * δ) := by
    rw [← Real.rpow_add hX0]
    congr 1
    ring
  refine ⟨δ, P, hδ, hlo, hhi, ?_, ?_⟩
  · intro z hz w hw hl
    have ht : (Nat.lcm z.r w.r : ℝ) ∈ S :=
      mem_union_left _ (mem_image.mpr ⟨(z, w), mem_product.mpr ⟨hz, hw⟩, rfl⟩)
    apply (hsmall _ ht hl).trans
    apply mul_le_mul_of_nonneg_left _ hP
    exact Real.rpow_le_rpow_of_exponent_le hX.le (by linarith)
  · intro z hz hγ
    haveI : NeZero z.r := z.hr
    have hr : 0 < (z.r : ℝ) := by exact_mod_cast NeZero.pos z.r
    have ht : |z.ρ.im| * z.r * X ^ (-δ) ∈ S :=
      mem_union_right _ (mem_image_of_mem _ hz)
    have htP : |z.ρ.im| * z.r * X ^ (-δ) ≤ P := by
      calc
        _ ≤ (P / z.r * X ^ δ) * z.r * X ^ (-δ) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hγ hr.le)
            (Real.rpow_nonneg hX0.le _)
        _ = P := by
          calc
            _ = P * (X ^ (-δ) * X ^ δ) := by field_simp [hr.ne']
            _ = P := by rw [hpowcancel, mul_one]
    have htbound : |z.ρ.im| * z.r ≤ P * X ^ (-4 * δ) := by
      calc
        _ = (|z.ρ.im| * z.r * X ^ (-δ)) * X ^ δ := by
          rw [mul_assoc, hpowcancel, mul_one]
        _ ≤ (P * X ^ (-5 * δ)) * X ^ δ :=
          mul_le_mul_of_nonneg_right (hsmall _ ht htP) (Real.rpow_nonneg hX0.le _)
        _ = P * X ^ (-4 * δ) := by rw [mul_assoc, hpowshift]
    calc
      _ ≤ (P * X ^ (-4 * δ)) / z.r := (le_div_iff₀ hr).mpr htbound
      _ = _ := by ring

end LeanLab.Pintz2021.Decomp393c

#print axioms LeanLab.Pintz2021.Decomp393c.all_cutoff_bound_iff_discarded_lcm_sum_eq_zero

#print axioms LeanLab.Pintz2021.Decomp393c.exists_empty_band

#print axioms LeanLab.Pintz2021.Decomp393c.exists_geometric_gap

#print axioms LeanLab.Pintz2021.Decomp393c.exists_level_with_finite_gap

#print axioms LeanLab.Pintz2021.Decomp393c.exists_level_with_gap_of_card_le

#print axioms LeanLab.Pintz2021.Decomp393c.exists_level_with_pair_lcm_gap

#print axioms LeanLab.Pintz2021.Decomp393c.exists_level_with_pair_and_height_gaps
