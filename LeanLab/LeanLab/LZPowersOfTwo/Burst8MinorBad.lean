/-
ROUTE BURST session 8, part 2 of the LZPowersOfTwo split: the leaf `minor_bad353`,
P0079 pages 10 to 12, displays (38) to (40) and (43).
Paper: P0079 A. Languasco and A. Zaccagnini, arXiv 0811.3663v2, 2 Apr 2009.
AI wrote this Lean code. Binary Goldbach is OPEN; this file says nothing about it.

`minor_bad_p2` has the exact statement of `minor_bad353` and is proved here with no sorry
of its own from cited inputs; the transcendental case `minor_bad_tr_p2`, the one the main
theorem uses, needs only two of them:
* `lemma5_tr_p2`, `lemma5_alg_p2`: Lemma 5 of the paper (Pintz and Ruzsa) on `(0, 1)` with
  (30) and (29), page 8.
* `cook_harman_tr_p2`: the display after (42), page 11, after Cook and Harman section 8 and
  Harman pages 221 to 223.
* `bcp39_alg_p2`: display (39), page 11, after Bruedern, Cook and Perelli section 4.
PROVED here: the passage from Lemma 5 on `(0, 1)` to `|m2| ≪ s L^2 X^{-c}` of page 10,
by periodicity, scaling and a covering by unit intervals; the Cauchy Schwarz step (38), in
the weighted arithmetic geometric mean form; and the choice of exponents leading to (40)
and (43).
-/
import LeanLab.LZPowersOfTwo.Decomp353c
import LeanLab.LZPowersOfTwo.ArcGeometry353
import LeanLab.LZPowersOfTwo.PrimeMoment353

open Real Finset MeasureTheory Filter Asymptotics
noncomputable section
namespace LeanLab.LZPowersOfTwo.Burst8P2

open LeanLab.LZPowersOfTwo

/-- P0079 page 11, the integrand of (38) and (39): `|S(λ1α) S(λ2α)|^2 K(α, η)`. -/
def twoPrimeMoment (l1 l2 η ε X α : ℝ) : ℝ :=
  ‖primeSum293 ε X (l1 * α) * primeSum293 ε X (l2 * α)‖ ^ 2 * kernel293 η α

/-- The minor arc piece `m2 = m ∩ {|G(μ_i α)| > νL for some i}` of page 10. -/
abbrev m2set (s : ℕ) (ν : ℝ) (μ : ℕ → ℝ) (ε X : ℝ) : Set ℝ :=
  minor293 X (cutoff293 s μ ε X) ∩ badPower353 s ν μ ε X

/-! ### The cited inputs -/

/-- The set where `|G(β)| > νL`, for the powers of two sum `G` of page 4. -/
def badG (L ν : ℝ) : Set ℝ := {β : ℝ | ν * L < ‖powerSum293 L β‖}

/-- CITED, sorry. P0079 page 8, Lemma 5 (Pintz and Ruzsa [21], section 7), with the
authors' computation (30): for `ν = 0.91237810306`,
`|{α ∈ (0, 1) : |G(α)| > νL}| ≪_{M,ε} X^{-4/5-10^{-20}}`. -/
theorem lemma5_tr_p2 (s : ℕ) (μ : ℕ → ℝ) (ε : ℝ) (hs : 2 ≤ s) (hμ : ∀ i, μ i ≠ 0)
    (hε : 0 < ε) (hε' : ε < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℝ in atTop,
      volume.real (Set.Ioo (0 : ℝ) 1 ∩ badG (cutoff293 s μ ε X) nuTr) ≤
        C * X ^ (-(4 / 5 + 1 / 10 ^ 20 : ℝ)) := by
  sorry

/-- CITED, sorry. P0079 page 8, Lemma 5 with (29): for `ν = 0.83372131685`,
`|{α ∈ (0, 1) : |G(α)| > νL}| ≪_{M,ε} X^{-2/3-10^{-20}}`. -/
theorem lemma5_alg_p2 (s : ℕ) (μ : ℕ → ℝ) (ε : ℝ) (hs : 2 ≤ s) (hμ : ∀ i, μ i ≠ 0)
    (hε : 0 < ε) (hε' : ε < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℝ in atTop,
      volume.real (Set.Ioo (0 : ℝ) 1 ∩ badG (cutoff293 s μ ε X) nuAlg) ≤
        C * X ^ (-(2 / 3 + 1 / 10 ^ 20 : ℝ)) := by
  sorry

/-! ### From Lemma 5 on `(0, 1)` to `|m2| ≪ s L^2 X^{-c}`, page 10, PROVED -/

/-- `G` has period one. -/
theorem powerSum_periodic_p2 (L β : ℝ) (k : ℤ) : powerSum293 L (β + k) = powerSum293 L β := by
  unfold powerSum293
  apply sum_congr rfl; intro m _
  rw [show (2 : ℝ) ^ m * (β + k) = 2 ^ m * β + ((2 ^ m * k : ℤ) : ℝ) by push_cast; ring,
    character_add293, character_int353, mul_one]

theorem badG_measurable_p2 (L ν : ℝ) : MeasurableSet (badG L ν) := by
  unfold badG
  apply measurableSet_lt measurable_const
  apply Continuous.measurable
  unfold powerSum293 character293
  fun_prop

/-- Each unit interval carries the same exceptional measure as `(0, 1)`. -/
theorem unit_shift_p2 (L ν : ℝ) (k : ℤ) :
    volume (Set.Ico (k : ℝ) (k + 1) ∩ badG L ν) ≤ volume (Set.Ioo (0 : ℝ) 1 ∩ badG L ν) := by
  have hset : Set.Ico (k : ℝ) (k + 1) ∩ badG L ν =
      (fun β : ℝ => β + (-(k : ℝ))) ⁻¹' (Set.Ico (0 : ℝ) 1 ∩ badG L ν) := by
    ext β
    simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_preimage, badG, Set.mem_setOf_eq]
    have hp : powerSum293 L (β + -(k : ℝ)) = powerSum293 L β := by
      have := powerSum_periodic_p2 L (β + -(k : ℝ)) k
      rw [show β + -(k : ℝ) + k = β by ring] at this
      exact this.symm
    rw [hp]
    constructor <;> rintro ⟨⟨h1, h2⟩, h3⟩ <;> refine ⟨⟨?_, ?_⟩, h3⟩ <;> linarith
  rw [hset, measure_preimage_add_right]
  have hsub : Set.Ico (0 : ℝ) 1 ∩ badG L ν ⊆ (Set.Ioo (0 : ℝ) 1 ∩ badG L ν) ∪ {0} := by
    intro β ⟨⟨h1, h2⟩, h3⟩
    rcases eq_or_lt_of_le h1 with h | h
    · right; exact h.symm
    · left; exact ⟨⟨h, h2⟩, h3⟩
  calc volume (Set.Ico (0 : ℝ) 1 ∩ badG L ν)
      ≤ volume ((Set.Ioo (0 : ℝ) 1 ∩ badG L ν) ∪ {0}) := measure_mono hsub
    _ ≤ volume (Set.Ioo (0 : ℝ) 1 ∩ badG L ν) + volume ({0} : Set ℝ) := measure_union_le _ _
    _ = _ := by rw [Real.volume_singleton, add_zero]

/-- A symmetric interval `[-R, R]` meets at most `2⌈R⌉ + 1` unit intervals. -/
theorem interval_cover_p2 (L ν R : ℝ) (hR : 0 ≤ R) :
    volume ({β : ℝ | |β| ≤ R} ∩ badG L ν) ≤
      ((2 * ⌈R⌉ + 1 : ℤ).toNat : ENNReal) * volume (Set.Ioo (0 : ℝ) 1 ∩ badG L ν) := by
  set N := ⌈R⌉
  have hsub : {β : ℝ | |β| ≤ R} ∩ badG L ν ⊆
      ⋃ k ∈ Finset.Icc (-N) N, Set.Ico (k : ℝ) (k + 1) ∩ badG L ν := by
    intro β ⟨hβ, hb⟩
    simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_Ico, Finset.mem_Icc]
    have hβ' := abs_le.mp (show |β| ≤ R from hβ)
    refine ⟨⌊β⌋, ⟨?_, ?_⟩, ⟨Int.floor_le β, Int.lt_floor_add_one β⟩, hb⟩
    · have : -(N : ℝ) ≤ β := by linarith [Int.le_ceil R]
      have h2 : ((-N : ℤ) : ℝ) ≤ β := by push_cast; exact this
      exact Int.le_floor.mpr h2
    · exact Int.floor_le_floor (hβ'.2.trans (Int.le_ceil R)) |>.trans (by simp [N])
  calc volume ({β : ℝ | |β| ≤ R} ∩ badG L ν)
      ≤ volume (⋃ k ∈ Finset.Icc (-N) N, Set.Ico (k : ℝ) (k + 1) ∩ badG L ν) :=
        measure_mono hsub
    _ ≤ ∑ k ∈ Finset.Icc (-N) N, volume (Set.Ico (k : ℝ) (k + 1) ∩ badG L ν) :=
        measure_biUnion_finset_le _ _
    _ ≤ ∑ _k ∈ Finset.Icc (-N) N, volume (Set.Ioo (0 : ℝ) 1 ∩ badG L ν) :=
        Finset.sum_le_sum (fun k _ => unit_shift_p2 L ν k)
    _ = _ := by
        rw [Finset.sum_const, nsmul_eq_mul, Int.card_Icc]
        congr 2
        omega

/-- P0079 page 10: `|m2| ≤ ∑_i (2 |μ_i| L^2 + 3) / |μ_i| · |E(ν)|`, from the scaling
`β = μ_i α` and the covering of `[-|μ_i| L^2, |μ_i| L^2]` by unit intervals. PROVED. -/
theorem m2_measure_le_p2 (s : ℕ) (ν : ℝ) (μ : ℕ → ℝ) (ε X : ℝ) (hμ : ∀ i, μ i ≠ 0) :
    volume.real (m2set s ν μ ε X) ≤
      (∑ i : Fin s, (2 * (cutoff293 s μ ε X) ^ 2 + 3 / |μ i|)) *
        volume.real (Set.Ioo (0 : ℝ) 1 ∩ badG (cutoff293 s μ ε X) ν) := by
  set L := cutoff293 s μ ε X
  set E0 := Set.Ioo (0 : ℝ) 1 ∩ badG L ν
  have hE0 : volume E0 < ⊤ :=
    (measure_mono Set.inter_subset_left).trans_lt measure_Ioo_lt_top
  let B : Fin s → Set ℝ := fun i => (fun α => μ i * α) ⁻¹' ({β : ℝ | |β| ≤ |μ i| * L ^ 2} ∩ badG L ν)
  have hsub : m2set s ν μ ε X ⊆ ⋃ i, B i := by
    intro α ⟨hmin, hbad⟩
    obtain ⟨i, hi⟩ := hbad
    simp only [Set.mem_iUnion]
    refine ⟨i, ?_, hi⟩
    simp only [Set.mem_setOf_eq, abs_mul]
    exact mul_le_mul_of_nonneg_left hmin.2 (abs_nonneg _)
  have hB : ∀ i, volume (B i) ≤ ENNReal.ofReal (2 * L ^ 2 + 3 / |μ i|) * volume E0 := by
    intro i
    have hμi : 0 < |μ i| := abs_pos.mpr (hμ i)
    have hR : 0 ≤ |μ i| * L ^ 2 := by positivity
    rw [Real.volume_preimage_mul_left (hμ i)]
    have hc := interval_cover_p2 L ν (|μ i| * L ^ 2) hR
    have hN : (((2 * ⌈|μ i| * L ^ 2⌉ + 1 : ℤ).toNat : ℕ) : ℝ) ≤ 2 * (|μ i| * L ^ 2) + 3 := by
      have h1 := Int.ceil_lt_add_one (|μ i| * L ^ 2)
      have h0 : (0 : ℤ) ≤ ⌈|μ i| * L ^ 2⌉ := Int.ceil_nonneg hR
      have : (((2 * ⌈|μ i| * L ^ 2⌉ + 1 : ℤ).toNat : ℕ) : ℝ) =
          ((2 * ⌈|μ i| * L ^ 2⌉ + 1 : ℤ) : ℝ) := by
        rw [← Int.cast_natCast, Int.toNat_of_nonneg (by omega)]
      rw [this]; push_cast; linarith
    calc ENNReal.ofReal |(μ i)⁻¹| * volume ({β : ℝ | |β| ≤ |μ i| * L ^ 2} ∩ badG L ν)
        ≤ ENNReal.ofReal |(μ i)⁻¹| *
            (((2 * ⌈|μ i| * L ^ 2⌉ + 1 : ℤ).toNat : ENNReal) * volume E0) := by gcongr
      _ = ENNReal.ofReal (|(μ i)⁻¹| * (((2 * ⌈|μ i| * L ^ 2⌉ + 1 : ℤ).toNat : ℝ))) *
            volume E0 := by
          rw [← mul_assoc, ENNReal.ofReal_mul (abs_nonneg _), ENNReal.ofReal_natCast]
      _ ≤ ENNReal.ofReal (2 * L ^ 2 + 3 / |μ i|) * volume E0 := by
          gcongr
          rw [abs_inv]
          calc |μ i|⁻¹ * (((2 * ⌈|μ i| * L ^ 2⌉ + 1 : ℤ).toNat : ℕ) : ℝ)
              ≤ |μ i|⁻¹ * (2 * (|μ i| * L ^ 2) + 3) :=
                mul_le_mul_of_nonneg_left hN (by positivity)
            _ = 2 * L ^ 2 + 3 / |μ i| := by field_simp
  have htot : volume (m2set s ν μ ε X) ≤
      ENNReal.ofReal (∑ i : Fin s, (2 * L ^ 2 + 3 / |μ i|)) * volume E0 := by
    calc volume (m2set s ν μ ε X) ≤ volume (⋃ i, B i) := measure_mono hsub
      _ ≤ ∑ i, volume (B i) := measure_iUnion_fintype_le _ _
      _ ≤ ∑ i : Fin s, ENNReal.ofReal (2 * L ^ 2 + 3 / |μ i|) * volume E0 :=
          Finset.sum_le_sum (fun i _ => hB i)
      _ = ENNReal.ofReal (∑ i : Fin s, (2 * L ^ 2 + 3 / |μ i|)) * volume E0 := by
          rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  have hfin : ENNReal.ofReal (∑ i : Fin s, (2 * L ^ 2 + 3 / |μ i|)) * volume E0 ≠ ⊤ :=
    ENNReal.mul_ne_top ENNReal.ofReal_ne_top hE0.ne
  have := ENNReal.toReal_mono hfin htot
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity)] at this
  exact this

/-- P0079 page 10: `|m2| ≪ s L^2 X^{-c}` from Lemma 5 on `(0, 1)`, for `L ≥ 1`. PROVED from
the hypothesis on `(0, 1)`. -/
theorem m2_from_lemma5_p2 (s : ℕ) (ν : ℝ) (μ : ℕ → ℝ) (ε : ℝ) (c C : ℝ) (hC : 0 ≤ C)
    (hμ : ∀ i, μ i ≠ 0) (hM : 0 < ∑ i : Fin s, |μ i|) (hε : 0 < ε)
    (H : ∀ᶠ X : ℝ in atTop,
      volume.real (Set.Ioo (0 : ℝ) 1 ∩ badG (cutoff293 s μ ε X) ν) ≤ C * X ^ (-c)) :
    ∃ C' : ℝ, 0 ≤ C' ∧ ∀ᶠ X : ℝ in atTop,
      volume.real (m2set s ν μ ε X) ≤ C' * s * (cutoff293 s μ ε X) ^ 2 * X ^ (-c) := by
  set K := 2 + 3 * ∑ j : Fin s, 1 / |μ j|
  have hK : 0 ≤ K := by positivity
  refine ⟨C * K, mul_nonneg hC hK, ?_⟩
  filter_upwards [H, (cutoff_tendsto353 s μ ε hM hε).eventually (eventually_ge_atTop 1)]
    with X hX hL
  set L := cutoff293 s μ ε X
  have hm := m2_measure_le_p2 s ν μ ε X hμ
  have hterm : ∀ i : Fin s, 2 * L ^ 2 + 3 / |μ i| ≤ K * L ^ 2 := by
    intro i
    have h1 : 3 / |μ i| ≤ 3 * ∑ j : Fin s, 1 / |μ j| := by
      have := Finset.single_le_sum (f := fun j : Fin s => 1 / |μ j|)
        (fun j _ => by positivity) (Finset.mem_univ i)
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_left this (by norm_num)
    have hL2 : 1 ≤ L ^ 2 := by nlinarith
    have : 3 * ∑ j : Fin s, 1 / |μ j| ≤ 3 * (∑ j : Fin s, 1 / |μ j|) * L ^ 2 := by
      have h0 : 0 ≤ 3 * ∑ j : Fin s, 1 / |μ j| := by positivity
      nlinarith
    rw [show K * L ^ 2 = 2 * L ^ 2 + 3 * (∑ j : Fin s, 1 / |μ j|) * L ^ 2 by ring]
    linarith
  have hsum : (∑ i : Fin s, (2 * L ^ 2 + 3 / |μ i|)) ≤ s * (K * L ^ 2) := by
    calc (∑ i : Fin s, (2 * L ^ 2 + 3 / |μ i|)) ≤ ∑ _i : Fin s, K * L ^ 2 :=
          Finset.sum_le_sum (fun i _ => hterm i)
      _ = s * (K * L ^ 2) := by simp
  have hv0 : 0 ≤ volume.real (Set.Ioo (0 : ℝ) 1 ∩ badG L ν) := measureReal_nonneg
  have hs0 : 0 ≤ (s : ℝ) * (K * L ^ 2) := by positivity
  calc volume.real (m2set s ν μ ε X)
      ≤ (∑ i : Fin s, (2 * L ^ 2 + 3 / |μ i|)) *
          volume.real (Set.Ioo (0 : ℝ) 1 ∩ badG L ν) := hm
    _ ≤ (s * (K * L ^ 2)) * (C * X ^ (-c)) := mul_le_mul hsum hX hv0 hs0
    _ = C * K * s * L ^ 2 * X ^ (-c) := by ring

/-- P0079 page 10: "by Lemma 5, we know that `|m2| ≪_{M,ε} s L^2 X^{-c}`", with
`c = 4/5 + 10^{-20}` and `ν = 0.91237810306` from (30), page 8.
PROVED from `lemma5_tr_p2`, the cited Lemma 5 on `(0, 1)`. -/
theorem pintz_ruzsa_tr_p2 (s : ℕ) (μ : ℕ → ℝ) (ε : ℝ) (hs : 2 ≤ s) (hμ : ∀ i, μ i ≠ 0)
    (hε : 0 < ε) (hε' : ε < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℝ in atTop,
      volume.real (m2set s nuTr μ ε X) ≤
        C * s * (cutoff293 s μ ε X) ^ 2 * X ^ (-(4 / 5 + 1 / 10 ^ 20 : ℝ)) := by
  have hM : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  obtain ⟨C, hC, H⟩ := lemma5_tr_p2 s μ ε hs hμ hε hε'
  exact m2_from_lemma5_p2 s nuTr μ ε _ C hC hμ hM hε H

/-- P0079 page 10, as `pintz_ruzsa_tr_p2`, with `c = 2/3 + 10^{-20}` and
`ν = 0.83372131685` from (29), page 8. PROVED from `lemma5_alg_p2`. -/
theorem pintz_ruzsa_alg_p2 (s : ℕ) (μ : ℕ → ℝ) (ε : ℝ) (hs : 2 ≤ s) (hμ : ∀ i, μ i ≠ 0)
    (hε : 0 < ε) (hε' : ε < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℝ in atTop,
      volume.real (m2set s nuAlg μ ε X) ≤
        C * s * (cutoff293 s μ ε X) ^ 2 * X ^ (-(2 / 3 + 1 / 10 ^ 20 : ℝ)) := by
  have hM : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  obtain ⟨C, hC, H⟩ := lemma5_alg_p2 s μ ε hs hμ hε hε'
  exact m2_from_lemma5_p2 s nuAlg μ ε _ C hC hμ hM hε H

/-- CITED, sorry. P0079 page 11, display (39), arguing as in section 4 of Bruedern, Cook and
Perelli [2]: `∫_{m2} |S(λ1α) S(λ2α)|^2 K(α, η) dα ≪_ε η X^{8/3+ε'}` for `λ1/λ2` algebraic. -/
theorem bcp39_alg_p2 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2)) (ha : IsAlg (l1 / l2)) (hμ : ∀ i, μ i ≠ 0)
    (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) (ε' : ℝ) (hε'' : 0 < ε') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℝ in atTop,
      (∫ α in m2set s nuAlg μ ε X, twoPrimeMoment l1 l2 η ε X α) ≤
        C * η * X ^ (8 / 3 + ε') := by
  sorry

/-- CITED, sorry. P0079 page 11, the display before (43), after section 8 of Cook and
Harman [4] and pages 221 to 223 of Harman [8]:
`∫_{m2} |S(λ1α) S(λ2α)|^2 K(α, η) dα ≪ η^2 X^{14/5+ε'} + η X^{13/5+ε'}` for `λ1/λ2`
transcendental. -/
theorem cook_harman_tr_p2 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2)) (ht : IsTr (l1 / l2)) (hμ : ∀ i, μ i ≠ 0)
    (hη : 0 < η) (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) (ε' : ℝ) (hε'' : 0 < ε') :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ X : ℝ in atTop,
      (∫ α in m2set s nuTr μ ε X, twoPrimeMoment l1 l2 η ε X α) ≤
        C * (η ^ 2 * X ^ (14 / 5 + ε') + η * X ^ (13 / 5 + ε')) := by
  sorry

/-! ### Display (38), PROVED -/

theorem twoPrimeMoment_integrable_p2 (l1 l2 η ε X : ℝ) :
    Integrable (twoPrimeMoment l1 l2 η ε X) := by
  let P := ∑ p ∈ (range (⌊X⌋₊ + 1)).filter (fun p : ℕ => p.Prime ∧ ε * X ≤ (p : ℝ)), |log p|
  have hP : 0 ≤ P := sum_nonneg (fun _ _ => abs_nonneg _)
  have hc : Continuous (fun α : ℝ =>
      ‖primeSum293 ε X (l1 * α) * primeSum293 ε X (l2 * α)‖ ^ 2) := by
    unfold primeSum293 character293
    fun_prop
  apply (kernel_integrable293 η).bdd_mul (c := (P * P) ^ 2) hc.aestronglyMeasurable
  apply Eventually.of_forall
  intro α
  change |‖primeSum293 ε X (l1 * α) * primeSum293 ε X (l2 * α)‖ ^ 2| ≤ (P * P) ^ 2
  rw [abs_of_nonneg (sq_nonneg _)]
  apply pow_le_pow_left₀ (norm_nonneg _) _ 2
  rw [norm_mul]
  exact mul_le_mul (primeSum_norm_le293 ε X (l1 * α))
    (primeSum_norm_le293 ε X (l2 * α)) (norm_nonneg _) hP

theorem m2set_measurable_p2 (s : ℕ) (ν : ℝ) (μ : ℕ → ℝ) (ε X : ℝ) :
    MeasurableSet (m2set s ν μ ε X) := by
  have hbad : MeasurableSet (badPower353 s ν μ ε X) := by
    unfold badPower353
    simp only [Set.setOf_exists]
    apply MeasurableSet.iUnion
    intro i
    apply measurableSet_lt measurable_const
    apply Continuous.measurable
    unfold powerSum293 character293
    fun_prop
  apply MeasurableSet.inter _ hbad
  unfold minor293
  measurability

theorem m2set_finite_p2 (s : ℕ) (ν : ℝ) (μ : ℕ → ℝ) (ε X : ℝ) :
    volume (m2set s ν μ ε X) < ⊤ := by
  set L := cutoff293 s μ ε X
  have hsub : m2set s ν μ ε X ⊆ Set.Icc (-(L ^ 2)) (L ^ 2) := by
    intro α hα
    have h := hα.1.2
    exact abs_le.mp h
  exact (measure_mono hsub).trans_lt measure_Icc_lt_top

/-- P0079 page 11, display (38), pointwise: with `|G| ≤ L` and `2uv ≤ λu^2 + v^2/λ`,
`|integrand| ≤ L^s / 2 (λ |S1 S2|^2 K + K / λ)`. PROVED. -/
theorem integrand_amgm_p2 (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε X α lam : ℝ)
    (hL : 0 ≤ cutoff293 s μ ε X) (hlam : 0 < lam) :
    ‖integrand293 s l1 l2 μ γ η ε X α‖ ≤
      (cutoff293 s μ ε X) ^ s / 2 *
        (lam * twoPrimeMoment l1 l2 η ε X α + kernel293 η α / lam) := by
  have hG : ‖∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)‖ ≤
      (cutoff293 s μ ε X) ^ s := by
    calc
      _ ≤ ∏ i : Fin s, ‖powerSum293 (cutoff293 s μ ε X) (μ i * α)‖ := norm_prod_le _ _
      _ ≤ ∏ _ : Fin s, cutoff293 s μ ε X := by
        apply prod_le_prod₀ (fun _ _ => norm_nonneg _)
        intro i _
        refine (powerSum_norm_le293 _ _).trans ?_
        simpa using Nat.floor_le hL
      _ = _ := by simp
  set u := ‖primeSum293 ε X (l1 * α) * primeSum293 ε X (l2 * α)‖
  set K := kernel293 η α
  have hK : 0 ≤ K := kernel_nonneg293 η α
  have hu : 0 ≤ u := norm_nonneg _
  have hamgm : u * K ≤ (lam * (u ^ 2 * K) + K / lam) / 2 := by
    have h : 0 ≤ K * (lam * u - 1) ^ 2 / lam := by positivity
    have e : (lam * (u ^ 2 * K) + K / lam) / 2 - u * K = K * (lam * u - 1) ^ 2 / lam / 2 := by
      field_simp; ring
    nlinarith
  have hnorm : ‖integrand293 s l1 l2 μ γ η ε X α‖ =
      u * ‖∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)‖ * K := by
    simp only [integrand293, norm_mul, character_norm293, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK, u, K]
  rw [hnorm]
  unfold twoPrimeMoment
  calc u * ‖∏ i : Fin s, powerSum293 (cutoff293 s μ ε X) (μ i * α)‖ * K
      ≤ u * (cutoff293 s μ ε X) ^ s * K := by
        apply mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hG hu) hK
    _ = (cutoff293 s μ ε X) ^ s * (u * K) := by ring
    _ ≤ (cutoff293 s μ ε X) ^ s * ((lam * (u ^ 2 * K) + K / lam) / 2) :=
        mul_le_mul_of_nonneg_left hamgm (pow_nonneg hL _)
    _ = _ := by ring

/-- P0079 page 11, display (38), integrated: for every `λ > 0`,
`|I(X; m2)| ≤ L^s / 2 (λ ∫_{m2} |S1 S2|^2 K + η^2 |m2| / λ)`. PROVED. -/
theorem cauchy38_p2 (s : ℕ) (l1 l2 : ℝ) (ν : ℝ) (μ : ℕ → ℝ) (γ η ε X lam : ℝ)
    (hL : 0 ≤ cutoff293 s μ ε X) (hlam : 0 < lam) :
    ‖∫ α in m2set s ν μ ε X, integrand293 s l1 l2 μ γ η ε X α‖ ≤
      (cutoff293 s μ ε X) ^ s / 2 *
        (lam * (∫ α in m2set s ν μ ε X, twoPrimeMoment l1 l2 η ε X α) +
          η ^ 2 * volume.real (m2set s ν μ ε X) / lam) := by
  set E := m2set s ν μ ε X
  have hE := m2set_measurable_p2 s ν μ ε X
  have hEf := m2set_finite_p2 s ν μ ε X
  have hF := (integrand_integrable293 s l1 l2 μ γ η ε X).norm.integrableOn (s := E)
  have hT := (twoPrimeMoment_integrable_p2 l1 l2 η ε X).integrableOn (s := E)
  have hKi := (kernel_integrable293 η).integrableOn (s := E)
  have hR : IntegrableOn (fun α => (cutoff293 s μ ε X) ^ s / 2 *
      (lam * twoPrimeMoment l1 l2 η ε X α + kernel293 η α / lam)) E :=
    ((hT.const_mul lam).add (hKi.div_const lam)).const_mul _
  have hKE : (∫ α in E, kernel293 η α) ≤ η ^ 2 * volume.real E := by
    have := norm_setIntegral_le_of_norm_le_const (μ := volume) (f := kernel293 η)
      (C := η ^ 2) hEf (fun α _ => by
        rw [Real.norm_of_nonneg (kernel_nonneg293 η α)]; exact kernel_le293 η α)
    exact (le_abs_self _).trans (by simpa using this)
  calc ‖∫ α in E, integrand293 s l1 l2 μ γ η ε X α‖
      ≤ ∫ α in E, ‖integrand293 s l1 l2 μ γ η ε X α‖ := norm_integral_le_integral_norm _
    _ ≤ ∫ α in E, (cutoff293 s μ ε X) ^ s / 2 *
          (lam * twoPrimeMoment l1 l2 η ε X α + kernel293 η α / lam) :=
        setIntegral_mono_on hF hR hE (fun α _ => integrand_amgm_p2 s l1 l2 μ γ η ε X α lam hL hlam)
    _ = (cutoff293 s μ ε X) ^ s / 2 *
          (lam * (∫ α in E, twoPrimeMoment l1 l2 η ε X α) +
            (∫ α in E, kernel293 η α) / lam) := by
        rw [integral_const_mul, integral_add (hT.const_mul lam) (hKi.div_const lam),
          integral_const_mul, integral_div]
    _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have := div_le_div_of_nonneg_right hKE hlam.le
        linarith

/-! ### Displays (40) and (43): the exponent count, PROVED -/

/-- The cutoff is `L = (log X + log(ε/(2M))) / log 2`. -/
theorem cutoff_formula_p2 (s : ℕ) (μ : ℕ → ℝ) (ε X : ℝ) (hM : 0 < ∑ i : Fin s, |μ i|)
    (hε : 0 < ε) (hX : 0 < X) :
    cutoff293 s μ ε X = (log X + log (ε / (2 * ∑ i : Fin s, |μ i|))) / log 2 := by
  unfold cutoff293
  rw [Real.logb, show ε * X / (2 * ∑ i : Fin s, |μ i|) =
    X * (ε / (2 * ∑ i : Fin s, |μ i|)) by ring, Real.log_mul hX.ne' (by positivity)]

/-- P0079 pages 11 to 12, the passage from (38) to (40) and (43): if
`∫_{m2} |S1 S2|^2 K ≤ α0 X^ζ` and `|m2| ≤ β0 L^2 X^{-c}` with `ζ - c < 2`, then the choice
`λ = X^{1 - ζ - ρ}`, `ρ = (2 - ζ + c)/2`, in (38) gives `|I(X; m2)| ≤ δ η X L^s` for every
`δ > 0` and large `X`. PROVED. -/
theorem bad_from_bounds_p2 (s : ℕ) (μ : ℕ → ℝ) (ε η : ℝ) (hM : 0 < ∑ i : Fin s, |μ i|)
    (hε : 0 < ε) (hη : 0 < η) (ζ c : ℝ) (hgap : ζ - c < 2) (A V Inorm : ℝ → ℝ)
    (α0 β0 : ℝ) (hα0 : 0 ≤ α0) (hβ0 : 0 ≤ β0)
    (hA : ∀ᶠ X : ℝ in atTop, A X ≤ α0 * X ^ ζ)
    (hV : ∀ᶠ X : ℝ in atTop, V X ≤ β0 * (cutoff293 s μ ε X) ^ 2 * X ^ (-c))
    (hI : ∀ᶠ X : ℝ in atTop, ∀ lam : ℝ, 0 < lam →
      Inorm X ≤ (cutoff293 s μ ε X) ^ s / 2 * (lam * A X + η ^ 2 * V X / lam)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop, Inorm X ≤ δ * η * X * (cutoff293 s μ ε X) ^ s := by
  intro δ hδ
  obtain ⟨ρ, hρ⟩ : ∃ ρ : ℝ, ρ = (2 - ζ + c) / 2 := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρ]; linarith
  obtain ⟨b0, hb0⟩ : ∃ b0 : ℝ, b0 = log (ε / (2 * ∑ i : Fin s, |μ i|)) := ⟨_, rfl⟩
  have hlog2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  obtain ⟨D, hD⟩ : ∃ D : ℝ, D = η ^ 2 * β0 * 2 / (log 2) ^ 2 := ⟨_, rfl⟩
  have hD0 : 0 ≤ D := by rw [hD]; positivity
  have hlo := (isLittleO_log_rpow_rpow_atTop (2 : ℝ) hρ0).bound
    (c := δ * η / (D + 1)) (by positivity)
  have hT := (tendsto_rpow_atTop hρ0).eventually
    (eventually_ge_atTop ((α0 + D * b0 ^ 2) / (δ * η)))
  filter_upwards [hA, hV, hI, hlo, hT, eventually_ge_atTop (1 : ℝ),
    (cutoff_tendsto353 s μ ε hM hε).eventually (eventually_ge_atTop 0)]
    with X hAX hVX hIX hloX hTX hX1 hL0
  have hX0 : 0 < X := by linarith
  set L := cutoff293 s μ ε X with hLdef
  have hlogX : 0 ≤ log X := log_nonneg hX1
  -- the eventual size bound
  have hLsq : L ^ 2 ≤ 2 * ((log X) ^ 2 + b0 ^ 2) / (log 2) ^ 2 := by
    rw [hLdef, cutoff_formula_p2 s μ ε X hM hε hX0, ← hb0, div_pow,
      div_le_div_iff_of_pos_right (by positivity)]
    nlinarith [sq_nonneg (log X - b0)]
  have hlo' : (log X) ^ 2 ≤ δ * η / (D + 1) * X ^ ρ := by
    have := hloX
    rwa [Real.norm_of_nonneg (by positivity), Real.norm_of_nonneg (by positivity),
      Real.rpow_two] at this
  have hsize : α0 + η ^ 2 * β0 * L ^ 2 ≤ 2 * δ * η * X ^ ρ := by
    have h1 : η ^ 2 * β0 * L ^ 2 ≤ D * ((log X) ^ 2 + b0 ^ 2) := by
      calc η ^ 2 * β0 * L ^ 2 ≤ η ^ 2 * β0 * (2 * ((log X) ^ 2 + b0 ^ 2) / (log 2) ^ 2) :=
            mul_le_mul_of_nonneg_left hLsq (by positivity)
        _ = D * ((log X) ^ 2 + b0 ^ 2) := by rw [hD]; ring
    have h2 : D * (log X) ^ 2 ≤ δ * η * X ^ ρ := by
      calc D * (log X) ^ 2 ≤ (D + 1) * (log X) ^ 2 := by nlinarith
        _ ≤ (D + 1) * (δ * η / (D + 1) * X ^ ρ) := mul_le_mul_of_nonneg_left hlo' (by positivity)
        _ = δ * η * X ^ ρ := by field_simp
    have h3 : α0 + D * b0 ^ 2 ≤ δ * η * X ^ ρ := by
      have := (div_le_iff₀ (by positivity : (0 : ℝ) < δ * η)).mp hTX
      linarith
    nlinarith
  -- the choice of `λ`
  have hlam : 0 < X ^ (1 - ζ - ρ) := Real.rpow_pos_of_pos hX0 _
  have hI1 := hIX (X ^ (1 - ζ - ρ)) hlam
  have e1 : X ^ (1 - ζ - ρ) * X ^ ζ = X ^ (1 - ρ) := by
    rw [← Real.rpow_add hX0]; ring_nf
  have e2 : X ^ (-c) / X ^ (1 - ζ - ρ) = X ^ (1 - ρ) := by
    rw [← Real.rpow_sub hX0]; congr 1; rw [hρ]; ring
  have e3 : X ^ (1 - ρ) * X ^ ρ = X := by
    rw [← Real.rpow_add hX0]; simp
  have hb1 : X ^ (1 - ζ - ρ) * A X ≤ α0 * X ^ (1 - ρ) := by
    calc X ^ (1 - ζ - ρ) * A X ≤ X ^ (1 - ζ - ρ) * (α0 * X ^ ζ) :=
          mul_le_mul_of_nonneg_left hAX hlam.le
      _ = α0 * (X ^ (1 - ζ - ρ) * X ^ ζ) := by ring
      _ = α0 * X ^ (1 - ρ) := by rw [e1]
  have hb2 : η ^ 2 * V X / X ^ (1 - ζ - ρ) ≤ η ^ 2 * β0 * L ^ 2 * X ^ (1 - ρ) := by
    rw [div_le_iff₀ hlam]
    calc η ^ 2 * V X ≤ η ^ 2 * (β0 * L ^ 2 * X ^ (-c)) :=
          mul_le_mul_of_nonneg_left hVX (by positivity)
      _ = η ^ 2 * β0 * L ^ 2 * (X ^ (-c) / X ^ (1 - ζ - ρ)) * X ^ (1 - ζ - ρ) := by
          field_simp
      _ = _ := by rw [e2]
  have hLs : 0 ≤ L ^ s / 2 := by positivity
  have hX1ρ : 0 < X ^ (1 - ρ) := Real.rpow_pos_of_pos hX0 _
  calc Inorm X ≤ L ^ s / 2 * (X ^ (1 - ζ - ρ) * A X + η ^ 2 * V X / X ^ (1 - ζ - ρ)) := hI1
    _ ≤ L ^ s / 2 * (X ^ (1 - ρ) * (α0 + η ^ 2 * β0 * L ^ 2)) := by
        apply mul_le_mul_of_nonneg_left _ hLs
        nlinarith
    _ ≤ L ^ s / 2 * (X ^ (1 - ρ) * (2 * δ * η * X ^ ρ)) := by
        apply mul_le_mul_of_nonneg_left _ hLs
        exact mul_le_mul_of_nonneg_left hsize hX1ρ.le
    _ = δ * η * (X ^ (1 - ρ) * X ^ ρ) * L ^ s := by ring
    _ = δ * η * X * L ^ s := by rw [e3]

/-! ### The leaf `minor_bad353` -/

/-- P0079 pages 11 to 12, displays (38) and (43), the transcendental case of section 7.
CONDITIONAL ON `pintz_ruzsa_tr_p2` and `cook_harman_tr_p2`, used with `ε' = 10^{-21}`;
this proof has no sorry of its own. -/
theorem minor_bad_tr_p2 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2))
    (hc : ν = nuTr ∧ IsTr (l1 / l2))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|)
    (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖∫ α in (minor293 X (cutoff293 s μ ε X) ∩ badPower353 s ν μ ε X),
        integrand293 s l1 l2 μ γ η ε X α‖ ≤
        δ * η * X * (cutoff293 s μ ε X) ^ s := by
  have hM : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  have hε1 : ε < 1 := by
    have H := (lt_div_iff₀ (by positivity : 0 < 8 * l1)).mp hε'
    nlinarith [mul_pos hε (show 0 < l1 by linarith)]
  have hI : ∀ᶠ X : ℝ in atTop, ∀ lam : ℝ, 0 < lam →
      ‖∫ α in m2set s ν μ ε X, integrand293 s l1 l2 μ γ η ε X α‖ ≤
        (cutoff293 s μ ε X) ^ s / 2 *
          (lam * (∫ α in m2set s ν μ ε X, twoPrimeMoment l1 l2 η ε X α) +
            η ^ 2 * volume.real (m2set s ν μ ε X) / lam) := by
    filter_upwards [(cutoff_tendsto353 s μ ε hM hε).eventually (eventually_ge_atTop 0)]
      with X hL lam hlam
    exact cauchy38_p2 s l1 l2 ν μ γ η ε X lam hL hlam
  have he : (0 : ℝ) < 1 / 10 ^ 21 := by norm_num
  obtain ⟨hν, htr⟩ := hc
  subst hν
  obtain ⟨CA, hCA, HA⟩ := cook_harman_tr_p2 s l1 l2 μ η ε hs h1 h2 hr hi htr hμ hη hε hε'
    (1 / 10 ^ 21) he
  obtain ⟨CV, hCV, HV⟩ := pintz_ruzsa_tr_p2 s μ ε hs hμ hε hε1
  have hA' : ∀ᶠ X : ℝ in atTop,
      (∫ α in m2set s nuTr μ ε X, twoPrimeMoment l1 l2 η ε X α) ≤
        CA * (η ^ 2 + η) * X ^ (14 / 5 + 1 / 10 ^ 21 : ℝ) := by
    filter_upwards [HA, eventually_ge_atTop (1 : ℝ)] with X hX hX1
    have hmono : X ^ (13 / 5 + 1 / 10 ^ 21 : ℝ) ≤ X ^ (14 / 5 + 1 / 10 ^ 21 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by norm_num)
    refine hX.trans ?_
    have hp : 0 ≤ X ^ (14 / 5 + 1 / 10 ^ 21 : ℝ) := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hmono hη.le]
  exact bad_from_bounds_p2 s μ ε η hM hε hη (14 / 5 + 1 / 10 ^ 21) (4 / 5 + 1 / 10 ^ 20)
    (by norm_num) _ _ _ (CA * (η ^ 2 + η)) (CV * s) (by positivity) (by positivity)
    hA' HV hI

/-- P0079 pages 11 to 12, displays (38) to (40) and (43): the exact statement of
`minor_bad353`, both cases. CONDITIONAL ON `pintz_ruzsa_tr_p2`, `pintz_ruzsa_alg_p2`,
`bcp39_alg_p2` and `cook_harman_tr_p2`, used with `ε' = 10^{-21}`; this proof has no sorry
of its own. -/
theorem minor_bad_p2 (ν : ℝ) (s : ℕ) (l1 l2 : ℝ) (μ : ℕ → ℝ) (γ η ε : ℝ)
    (hs : 2 ≤ s) (h1 : 1 < l1) (h2 : l2 < -1) (hr : 1 ≤ |l1 / l2|)
    (hi : Irrational (l1 / l2))
    (hc : (ν = nuTr ∧ IsTr (l1 / l2)) ∨ (ν = nuAlg ∧ IsAlg (l1 / l2)))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|)
    (hε : 0 < ε) (hε' : ε < 1 / (8 * l1)) :
    ∀ δ : ℝ, 0 < δ → ∀ᶠ X : ℝ in atTop,
      ‖∫ α in (minor293 X (cutoff293 s μ ε X) ∩ badPower353 s ν μ ε X),
        integrand293 s l1 l2 μ γ η ε X α‖ ≤
        δ * η * X * (cutoff293 s μ ε X) ^ s := by
  rcases hc with htr | ⟨hν, halg⟩
  · exact minor_bad_tr_p2 ν s l1 l2 μ γ η ε hs h1 h2 hr hi htr hμ r1 r2 hr1 hr2 hη hη1 hη2
      hε hε'
  have hM : 0 < ∑ i : Fin s, |μ i| := by
    apply sum_pos' (fun i _ => abs_nonneg _)
    exact ⟨⟨0, by omega⟩, mem_univ _, abs_pos.mpr (hμ 0)⟩
  have hε1 : ε < 1 := by
    have H := (lt_div_iff₀ (by positivity : 0 < 8 * l1)).mp hε'
    nlinarith [mul_pos hε (show 0 < l1 by linarith)]
  have hI : ∀ᶠ X : ℝ in atTop, ∀ lam : ℝ, 0 < lam →
      ‖∫ α in m2set s ν μ ε X, integrand293 s l1 l2 μ γ η ε X α‖ ≤
        (cutoff293 s μ ε X) ^ s / 2 *
          (lam * (∫ α in m2set s ν μ ε X, twoPrimeMoment l1 l2 η ε X α) +
            η ^ 2 * volume.real (m2set s ν μ ε X) / lam) := by
    filter_upwards [(cutoff_tendsto353 s μ ε hM hε).eventually (eventually_ge_atTop 0)]
      with X hL lam hlam
    exact cauchy38_p2 s l1 l2 ν μ γ η ε X lam hL hlam
  have he : (0 : ℝ) < 1 / 10 ^ 21 := by norm_num
  subst hν
  obtain ⟨CA, hCA, HA⟩ := bcp39_alg_p2 s l1 l2 μ η ε hs h1 h2 hr hi halg hμ hη hε hε'
    (1 / 10 ^ 21) he
  obtain ⟨CV, hCV, HV⟩ := pintz_ruzsa_alg_p2 s μ ε hs hμ hε hε1
  have hA' : ∀ᶠ X : ℝ in atTop,
      (∫ α in m2set s nuAlg μ ε X, twoPrimeMoment l1 l2 η ε X α) ≤
        CA * η * X ^ (8 / 3 + 1 / 10 ^ 21 : ℝ) := HA
  exact bad_from_bounds_p2 s μ ε η hM hε hη (8 / 3 + 1 / 10 ^ 21) (2 / 3 + 1 / 10 ^ 20)
    (by norm_num) _ _ _ (CA * η) (CV * s) (by positivity) (by positivity)
    hA' HV hI

end LeanLab.LZPowersOfTwo.Burst8P2
