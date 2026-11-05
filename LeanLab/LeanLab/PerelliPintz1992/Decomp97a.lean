/-
P0070, pages 363 to 366, fine steps behind 27 to 34.
Analytic finiteness uses Mathlib and does not use a density theorem.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.ZeroCountCS97
import LeanLab.PerelliPintz1992.Decomp97
import LeanLab.ExceptionalSet.WindowParseval264
import LeanLab.PerelliPintz1992.ZeroPairSum97
import LeanLab.PerelliPintz1992.InducedZeros
import LeanLab.PNTPort.DirichletZF.U1482Jensen
namespace LeanLab.PerelliPintz1992.Section6
open Real Filter Topology Set Metric MeasureTheory
/-- The actual zeros in any bounded nontrivial region form a finite set.
This justifies finite truncation on page 365 before applying 32 to 34. -/
theorem nontrivial_zero_set_finite {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) (σ T : ℝ) :
    {ρ : ℂ | ρ ∈ zeroRegion σ T ∧ χ.LFunction ρ = 0}.Finite := by
  have finite_zeros (f : ℂ → ℂ) (hf : Differentiable ℂ f) {z : ℂ} (hz : f z ≠ 0) :
      (closedBall (0 : ℂ) (|T| + 2) ∩ f ⁻¹' {0}).Finite := by
    have ha : AnalyticOnNhd ℂ f univ := fun z _ => hf.analyticAt z
    have hd := ha.preimage_zero_mem_codiscrete hz
    have hc : IsClosed (f ⁻¹' {0}) := isClosed_singleton.preimage hf.continuous
    have hi : IsDiscrete (f ⁻¹' {0}) := by
      simpa using (mem_codiscrete'.mp hd).2
    exact ((isCompact_closedBall _ _).inter_right hc).finite (hi.mono inter_subset_right)
  have hball {ρ : ℂ} (hβ : 0 < ρ.re) (hβ' : ρ.re < 1) (hγ : |ρ.im| ≤ T) :
      ρ ∈ closedBall (0 : ℂ) (|T| + 2) := by
    rw [mem_closedBall, dist_zero_right]
    calc
      ‖ρ‖ ≤ |ρ.re| + |ρ.im| := Complex.norm_le_abs_re_add_abs_im ρ
      _ ≤ |T| + 2 := by rw [abs_of_pos hβ]; linarith [le_abs_self T]
  by_cases hχ : χ = 1
  · subst χ
    have hf := finite_zeros (DirichletCharacter.LFunctionTrivChar₁ (q : ℕ))
      (DirichletCharacter.differentiable_LFunctionTrivChar₁ (q : ℕ))
      (DirichletCharacter.LFunctionTrivChar₁_apply_one_ne_zero (q : ℕ))
    apply hf.subset
    rintro ρ ⟨⟨hσ, hβ, hβ', hγ⟩, hz⟩
    refine ⟨hball hβ hβ' hγ, ?_⟩
    have hρ : ρ ≠ 1 := by intro hh; simp [hh] at hβ'
    simp only [mem_preimage, mem_singleton_iff]
    rw [DirichletCharacter.LFunctionTrivChar₁, Function.update_of_ne hρ]
    change (ρ - 1) * (1 : DirichletCharacter ℂ (q : ℕ)).LFunction ρ = 0
    rw [hz, mul_zero]
  · have hf := finite_zeros χ.LFunction (DirichletCharacter.differentiable_LFunction hχ)
      (χ.LFunction_ne_zero_of_one_le_re (s := 2) (by norm_num) (by norm_num))
    apply hf.subset
    rintro ρ ⟨⟨hσ, hβ, hβ', hγ⟩, hz⟩
    exact ⟨hball hβ hβ' hγ, hz⟩
/-- Every analytic order away from the possible pole is finite.
Auxiliary justification of the zero multiplicities in 28 to 34 on pages 365 and 366. -/
theorem LFunction_analyticOrderAt_ne_top {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) {ρ : ℂ} (hρ : ρ ≠ 1) :
    analyticOrderAt χ.LFunction ρ ≠ ⊤ := by
  have ha : AnalyticOnNhd ℂ χ.LFunction ({1} : Set ℂ)ᶜ := by
    apply DifferentiableOn.analyticOnNhd _ isOpen_compl_singleton
    intro z hz
    exact (χ.differentiableAt_LFunction z (Or.inl hz)).differentiableWithinAt
  apply ha.analyticOrderAt_ne_top_of_isPreconnected
    (isConnected_compl_singleton_of_one_lt_rank (by simp) (1 : ℂ)).isPreconnected
    (x := 2) (by norm_num) hρ
  rw [analyticOrderAt_eq_zero.mpr (Or.inr
    (χ.LFunction_ne_zero_of_one_le_re (s := 2) (by norm_num) (by norm_num)))]
  simp

/-- The actual zero multiplicity count is finite without either density input.
This removes the finiteness hypotheses from the use of 34 on page 366. -/
theorem zeroCount_ne_top {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) (σ T : ℝ) :
    zeroCount χ σ T ≠ ⊤ := by
  classical
  let Z := (nontrivial_zero_set_finite χ σ T).toFinset
  have hsum : zeroCount χ σ T = ∑ ρ ∈ Z, (analyticOrderAt χ.LFunction ρ).toENNReal := by
    unfold zeroCount
    rw [tsum_eq_sum (s := Z) ?_]
    · apply Finset.sum_congr rfl
      intro ρ hρ
      rw [ite_eq_left ((nontrivial_zero_set_finite χ σ T).mem_toFinset.mp hρ).1]
    · intro ρ hρ
      by_cases hr : ρ ∈ zeroRegion σ T
      · have hz : χ.LFunction ρ ≠ 0 := by
          intro hz
          exact hρ ((nontrivial_zero_set_finite χ σ T).mem_toFinset.mpr ⟨hr, hz⟩)
        rw [ite_eq_left hr, analyticOrderAt_eq_zero.mpr (Or.inr hz)]
        simp
      · rw [ite_eq_right hr]
  rw [hsum]
  apply ENNReal.sum_ne_top.mpr
  intro ρ hρ
  apply ENat.toENNReal_ne_top.mpr
  apply LFunction_analyticOrderAt_ne_top χ
  have hβ := ((nontrivial_zero_set_finite χ σ T).mem_toFinset.mp hρ).1.2.2.1
  intro heq
  simp [heq] at hβ

/-- The finite family of actual nontrivial zeros, with multiplicities kept in coefficients. -/
noncomputable def zeroTruncation {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) (σ T : ℝ) : Finset ℂ :=
  (nontrivial_zero_set_finite χ σ T).toFinset

/-- Membership retains the real part cutoff, height cutoff and the actual L zero equation. -/
theorem mem_zeroTruncation {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) (σ T : ℝ) (ρ : ℂ) :
    ρ ∈ zeroTruncation χ σ T ↔ ρ ∈ zeroRegion σ T ∧ χ.LFunction ρ = 0 := by
  exact (nontrivial_zero_set_finite χ σ T).mem_toFinset

/-- The zero sum on page 365 is an actual finite sum for every x and finite cutoff T. -/
theorem explicitZeroSum_eq_sum {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) (x T : ℝ) :
    explicitZeroSum χ x T = ∑ ρ ∈ zeroTruncation χ 0 T,
      (analyticOrderNatAt χ.LFunction ρ : ℂ) * (x : ℂ) ^ ρ / ρ := by
  classical
  unfold explicitZeroSum
  rw [tsum_eq_sum (s := zeroTruncation χ 0 T) ?_]
  · apply Finset.sum_congr rfl
    intro ρ hρ
    rw [ite_eq_left ((mem_zeroTruncation χ 0 T ρ).mp hρ).1]
  · intro ρ hρ
    by_cases hr : ρ ∈ zeroRegion 0 T
    · have hz : χ.LFunction ρ ≠ 0 := by
        intro hz
        exact hρ ((mem_zeroTruncation χ 0 T ρ).mpr ⟨hr, hz⟩)
      rw [ite_eq_left hr]
      have ho : analyticOrderNatAt χ.LFunction ρ = 0 := by
        unfold analyticOrderNatAt
        rw [analyticOrderAt_eq_zero.mpr (Or.inr hz)]
        rfl
      rw [ho]
      simp
    · rw [ite_eq_right hr]

/-- The actual ENNReal count equals the finite sum of natural multiplicities. -/
theorem zeroCount_eq_sum_orders {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) (σ T : ℝ) :
    zeroCount χ σ T = ∑ ρ ∈ zeroTruncation χ σ T,
      (analyticOrderNatAt χ.LFunction ρ : ENNReal) := by
  classical
  unfold zeroCount
  rw [tsum_eq_sum (s := zeroTruncation χ σ T) ?_]
  · apply Finset.sum_congr rfl
    intro ρ hρ
    have hr := ((mem_zeroTruncation χ σ T ρ).mp hρ).1
    rw [ite_eq_left hr]
    have hρ1 : ρ ≠ 1 := by intro he; simp [zeroRegion, he] at hr
    rw [← Nat.cast_analyticOrderNatAt (LFunction_analyticOrderAt_ne_top χ hρ1)]
    simp
  · intro ρ hρ
    by_cases hr : ρ ∈ zeroRegion σ T
    · have hz : χ.LFunction ρ ≠ 0 := by
        intro hz
        exact hρ ((mem_zeroTruncation χ σ T ρ).mpr ⟨hr, hz⟩)
      rw [ite_eq_left hr, analyticOrderAt_eq_zero.mpr (Or.inr hz)]
      simp
    · rw [ite_eq_right hr]

/-- The character count minimum in 34 needs no separate finiteness or density hypothesis. -/
theorem character_zero_sqrt_min_finite (q : ℕ+) (σ T : ℝ) :
    (∑ χ : DirichletCharacter ℂ (q : ℕ), sqrt ((zeroCount χ σ T).toReal)) ≤
      min (allCharacterCount q σ T).toReal
        (sqrt ((q : ℝ) * (allCharacterCount q σ T).toReal)) := by
  exact character_zero_sqrt_min q σ T (fun χ => zeroCount_ne_top χ σ T)

/-- Page 363: at most one numerator with fixed positive denominator meets the window.
The explicit sufficient size bounds are Q greater than four and H greater than four q. -/
theorem meeting_numerator_unique {q a b : ℕ} (hq : 0 < q) {Q H ξ x y : ℝ} (hQ : 4 < Q) (hH : 4 * q < H)
    (ha : |x - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * Q)) (hx : |x - ξ| < 1 / H)
    (hb : |y - (b : ℝ) / q| ≤ 1 / ((q : ℝ) * Q)) (hy : |y - ξ| < 1 / H) : a = b := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hQp : 0 < Q := by linarith
  have hHp : 0 < H := by linarith
  have hw : 1 / ((q : ℝ) * Q) < 1 / (4 * q) := by
    apply one_div_lt_one_div_of_lt (by positivity)
    nlinarith
  have hv : 1 / H < 1 / (4 * q) := one_div_lt_one_div_of_lt (by positivity) hH
  have hx' := abs_lt.mp (hx.trans hv)
  have hy' := abs_lt.mp (hy.trans hv)
  have ha' := abs_lt.mp (ha.trans_lt hw)
  have hb' := abs_lt.mp (hb.trans_lt hw)
  have he : (4 : ℝ) * (1 / (4 * q)) = 1 / (q : ℝ) := by field_simp
  have hdiff : |(a : ℝ) / q - (b : ℝ) / q| < 1 / (q : ℝ) := by
    rw [abs_lt]
    constructor <;> linarith
  rw [← sub_div, abs_div, abs_of_pos hqR, div_lt_div_iff_of_pos_right hqR] at hdiff
  have hboth := abs_lt.mp hdiff
  have hab : a < b + 1 := by exact_mod_cast (by linarith [hboth.2] : (a : ℝ) < b + 1)
  have hba : b < a + 1 := by exact_mod_cast (by linarith [hboth.1] : (b : ℝ) < a + 1)
  omega

/-- Page 366, the symmetric pair kernel in 32 is bounded by a single weighted sum
when its multiplicity weighted row sums are bounded by B. -/
theorem weighted_zero_pair_schur {ι : Type*} (Z : Finset ι) (m w : ι → ℝ) (t : ι → ℝ) (B : ℝ)
    (hm : ∀ i ∈ Z, 0 ≤ m i)
    (hrow : ∀ i ∈ Z, ∑ j ∈ Z, m j / max 1 |t i - t j| ≤ B) :
    (∑ i ∈ Z, ∑ j ∈ Z, m i * m j * w i * w j / max 1 |t i - t j|) ≤ B * ∑ i ∈ Z, m i * w i ^ 2 := by
  have hpt (i : ι) (hi : i ∈ Z) (j : ι) (hj : j ∈ Z) : 2 * (m i * m j * w i * w j / max 1 |t i - t j|) ≤
      (m i * m j * w i ^ 2 + m i * m j * w j ^ 2) / max 1 |t i - t j| := by
    rw [← mul_div_assoc]
    apply div_le_div_of_nonneg_right (by nlinarith [mul_nonneg (mul_nonneg (hm i hi) (hm j hj)) (sq_nonneg (w i - w j))]) (by positivity)
  have heq : (∑ i ∈ Z, ∑ j ∈ Z, (m i * m j * w i ^ 2 + m i * m j * w j ^ 2) / max 1 |t i - t j|) =
      2 * ∑ i ∈ Z, (m i * w i ^ 2) * (∑ j ∈ Z, m j / max 1 |t i - t j|) := by
    simp_rw [add_div, Finset.sum_add_distrib]
    rw [Finset.sum_comm (f := fun i j => m i * m j * w j ^ 2 / max 1 |t i - t j|)]
    have hh : (∑ i ∈ Z, ∑ j ∈ Z, m i * m j * w i ^ 2 / max 1 |t i - t j|) =
        ∑ i ∈ Z, (m i * w i ^ 2) * (∑ j ∈ Z, m j / max 1 |t i - t j|) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i hi
      apply Finset.sum_congr rfl
      intro j hj
      ring
    have hh' : (∑ j ∈ Z, ∑ i ∈ Z, m i * m j * w j ^ 2 / max 1 |t i - t j|) =
        ∑ j ∈ Z, (m j * w j ^ 2) * (∑ i ∈ Z, m i / max 1 |t j - t i|) := by
      simp_rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      apply Finset.sum_congr rfl
      intro i hi
      rw [abs_sub_comm]
      ring
    rw [hh, hh']
    ring
  have hp : 2 * (∑ i ∈ Z, ∑ j ∈ Z, m i * m j * w i * w j / max 1 |t i - t j|) ≤
      2 * ∑ i ∈ Z, (m i * w i ^ 2) * (∑ j ∈ Z, m j / max 1 |t i - t j|) := by
    rw [← heq]
    simp_rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i hi => Finset.sum_le_sum fun j hj => hpt i hi j hj
  have hr : (∑ i ∈ Z, (m i * w i ^ 2) * (∑ j ∈ Z, m j / max 1 |t i - t j|)) ≤
      B * ∑ i ∈ Z, m i * w i ^ 2 := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i hi
    simpa only [mul_comm] using mul_le_mul_of_nonneg_left (hrow i hi) (mul_nonneg (hm i hi) (sq_nonneg (w i)))
  linarith

/-- Page 366, the unit height counting step before 33.
An absolute height gap bin lies in two intervals of length one. -/
theorem unit_bin_mass_bound {ι : Type*} [DecidableEq ι] (Z : Finset ι) (m t : ι → ℝ) (ξ B : ℝ) (k : ℕ)
    (hm : ∀ j ∈ Z, 0 ≤ m j)
    (hunit : ∀ τ : ℝ, ∑ j ∈ Z.filter (fun j => |t j - τ| ≤ 1 / 2), m j ≤ B) :
    (∑ j ∈ Z.filter (fun j => ⌊|t j - ξ|⌋₊ = k), m j) ≤ 2 * B := by
  let P := Z.filter (fun j => |t j - (ξ + (k : ℝ) + 1 / 2)| ≤ 1 / 2)
  let M := Z.filter (fun j => |t j - (ξ - (k : ℝ) - 1 / 2)| ≤ 1 / 2)
  have hsub : Z.filter (fun j => ⌊|t j - ξ|⌋₊ = k) ⊆ P ∪ M := by
    intro j hj
    obtain ⟨hjZ, hjk⟩ := Finset.mem_filter.mp hj
    have hl := Nat.floor_le (abs_nonneg (t j - ξ))
    have hu := Nat.lt_floor_add_one |t j - ξ|
    rw [hjk] at hl hu
    rcases le_total ξ (t j) with hp | hp
    · apply Finset.mem_union.mpr
      left
      apply Finset.mem_filter.mpr
      refine ⟨hjZ, ?_⟩
      rw [abs_of_nonneg (sub_nonneg.mpr hp)] at hl hu
      rw [abs_le]
      constructor <;> linarith
    · apply Finset.mem_union.mpr
      right
      apply Finset.mem_filter.mpr
      refine ⟨hjZ, ?_⟩
      rw [abs_of_nonpos (sub_nonpos.mpr hp)] at hl hu
      rw [abs_le]
      constructor <;> linarith
  have hnonneg : ∀ j ∈ P ∪ M, 0 ≤ m j := by
    intro j hj
    rcases Finset.mem_union.mp hj with hj | hj
    · exact hm j (Finset.mem_filter.mp hj).1
    · exact hm j (Finset.mem_filter.mp hj).1
  calc
    _ ≤ ∑ j ∈ P ∪ M, m j := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun j hj _ => hnonneg j hj)
    _ ≤ (∑ j ∈ P, m j) + ∑ j ∈ M, m j := by
      have hh := Finset.sum_union_inter (s₁ := P) (s₂ := M) (f := m)
      have hn : 0 ≤ ∑ j ∈ P ∩ M, m j := Finset.sum_nonneg (fun j hj =>
        hm j (Finset.mem_filter.mp (Finset.mem_inter.mp hj).1).1)
      linarith
    _ ≤ 2 * B := by linarith [hunit (ξ + (k : ℝ) + 1 / 2), hunit (ξ - (k : ℝ) - 1 / 2)]

/-- Page 366, the harmonic summation step before 33 with an explicit constant four.
A bound B on every unit interval gives a row bound four B times one plus log of K plus one. -/
theorem zero_kernel_row_bound {ι : Type*} [DecidableEq ι] (Z : Finset ι) (m t : ι → ℝ) (ξ B : ℝ) (K : ℕ)
    (hm : ∀ j ∈ Z, 0 ≤ m j) (hB : 0 ≤ B)
    (hheight : ∀ j ∈ Z, |t j - ξ| ≤ K)
    (hunit : ∀ τ : ℝ, ∑ j ∈ Z.filter (fun j => |t j - τ| ≤ 1 / 2), m j ≤ B) :
    (∑ j ∈ Z, m j / max 1 |t j - ξ|) ≤ 4 * B * (1 + log (K + 1)) := by
  let J := Finset.range (K + 1)
  have hmap : ∀ j ∈ Z, ⌊|t j - ξ|⌋₊ ∈ J := by
    intro j hj
    apply Finset.mem_range.mpr
    have hf := Nat.floor_mono (hheight j hj)
    rw [Nat.floor_natCast] at hf
    omega
  have hgroup : (∑ j ∈ Z, m j / max 1 |t j - ξ|) =
      ∑ k ∈ J, ∑ j ∈ Z.filter (fun j => ⌊|t j - ξ|⌋₊ = k),
        m j / max 1 |t j - ξ| := by
    exact (Finset.sum_fiberwise_of_maps_to hmap (fun j => m j / max 1 |t j - ξ|)).symm
  have hbin (k : ℕ) : (∑ j ∈ Z.filter (fun j => ⌊|t j - ξ|⌋₊ = k),
      m j / max 1 |t j - ξ|) ≤ (2 * B) / max 1 (k : ℝ) := by
    calc
      _ ≤ ∑ j ∈ Z.filter (fun j => ⌊|t j - ξ|⌋₊ = k), m j / max 1 (k : ℝ) := by
        apply Finset.sum_le_sum
        intro j hj
        obtain ⟨hjZ, hjk⟩ := Finset.mem_filter.mp hj
        have hl := Nat.floor_le (abs_nonneg (t j - ξ))
        rw [hjk] at hl
        exact div_le_div_of_nonneg_left (hm j hjZ) (by positivity) (max_le_max_left 1 hl)
      _ = (∑ j ∈ Z.filter (fun j => ⌊|t j - ξ|⌋₊ = k), m j) / max 1 (k : ℝ) := by
        rw [Finset.sum_div]
      _ ≤ _ := div_le_div_of_nonneg_right (unit_bin_mass_bound Z m t ξ B k hm hunit) (by positivity)
  have hrecip (k : ℕ) : 1 / max 1 (k : ℝ) ≤ 2 / (k + 1 : ℝ) := by
    have hk := Nat.cast_nonneg (α := ℝ) k
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    rcases k with _ | k
    · norm_num
    · have h1 : (1 : ℝ) ≤ (k + 1 : ℕ) := by exact_mod_cast Nat.succ_le_succ (Nat.zero_le k)
      rw [max_eq_right h1]
      push_cast
      linarith [Nat.cast_nonneg (α := ℝ) k]
  calc
    _ = ∑ k ∈ J, ∑ j ∈ Z.filter (fun j => ⌊|t j - ξ|⌋₊ = k), m j / max 1 |t j - ξ| := hgroup
    _ ≤ ∑ k ∈ J, (2 * B) / max 1 (k : ℝ) := Finset.sum_le_sum (fun k hk => hbin k)
    _ ≤ ∑ k ∈ J, (2 * B) * (2 / (k + 1 : ℝ)) := by
      apply Finset.sum_le_sum
      intro k hk
      simpa only [mul_one_div] using mul_le_mul_of_nonneg_left (hrecip k) (by positivity : 0 ≤ 2 * B)
    _ = 4 * B * (harmonic (K + 1) : ℝ) := by
      simp only [harmonic, Rat.cast_sum, Rat.cast_inv, Nat.cast_add, Nat.cast_one]
      dsimp only [J]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      push_cast
      ring
    _ ≤ _ := by
      simpa only [Nat.cast_add, Nat.cast_one] using
        mul_le_mul_of_nonneg_left (harmonic_le_one_add_log (K + 1)) (by positivity : 0 ≤ 4 * B)

/-- Equation 32 for the finite actual zero family and its analytic multiplicities. -/
theorem actual_zero_mean_square_bound {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ))
    (σ T : ℝ) {N : ℝ} (hN : 0 < N) :
    (1 / N) * (∫ x : ℝ in N / 2..3 * N,
      ‖∑ ρ ∈ zeroTruncation χ σ T,
        (analyticOrderNatAt χ.LFunction ρ : ℂ) * (x : ℂ) ^ (ρ - 1)‖ ^ 2) ≤
      10 * ∑ ρ ∈ zeroTruncation χ σ T, ∑ ρ' ∈ zeroTruncation χ σ T,
        (analyticOrderNatAt χ.LFunction ρ : ℝ) * (analyticOrderNatAt χ.LFunction ρ' : ℝ) *
          N ^ (ρ.re + ρ'.re - 2) / max 1 |ρ.im - ρ'.im| := by
  have hh := finite_zero_mean_square_bound (zeroTruncation χ σ T)
    (fun ρ => (analyticOrderNatAt χ.LFunction ρ : ℂ)) hN (fun ρ hρ =>
      ⟨((mem_zeroTruncation χ σ T ρ).mp hρ).1.2.1.le,
        ((mem_zeroTruncation χ σ T ρ).mp hρ).1.2.2.1.le⟩)
  simpa only [Complex.norm_natCast] using hh

/-- Principal character induction preserves the nontrivial zeta zero multiplicity. -/
theorem principal_order_eq_zeta {q : ℕ+} {ρ : ℂ} (hβ : 0 < ρ.re) (hβ' : ρ.re < 1) :
    analyticOrderAt (1 : DirichletCharacter ℂ (q : ℕ)).LFunction ρ =
      analyticOrderAt riemannZeta ρ := by
  have hh := analyticOrderAt_changeLevel (r := 1) (q := q) (Nat.one_dvd (q : ℕ))
    (1 : DirichletCharacter ℂ 1) hβ hβ'
  change analyticOrderAt (DirichletCharacter.changeLevel (Nat.one_dvd (q : ℕ))
    (1 : DirichletCharacter ℂ 1)).LFunction ρ =
    analyticOrderAt (1 : DirichletCharacter ℂ 1).LFunction ρ at hh
  rw [DirichletCharacter.changeLevel_one, DirichletCharacter.LFunction_modOne_eq] at hh
  exact hh

/-- The unit height interval count before 33, with actual analytic multiplicities.
Reuse the lab's proved Jensen estimates for nonprincipal L functions and zeta. -/
theorem zero_window_multiplicity_bound {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ))
    (τ : ℝ) (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, χ.LFunction ρ = 0 ∧ 1 / 2 ≤ ρ.re ∧ ρ.re < 1 ∧ |ρ.im - τ| ≤ 1 / 2) :
    (∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤
      log (24 * LeanLab.PNTPort.DirichletZF.Z * (q : ℝ) * (|τ| + 4) ^ 2) / log (7 / 6) := by
  have hZpos := LeanLab.PNTPort.DirichletZF.Z_pos
  by_cases hχ : χ = 1
  · subst χ
    have hζ : ∀ ρ ∈ Z, ρ ∈ LeanLab.PNTPort.DirichletZF.U1482.RW riemannZeta τ := by
      intro ρ hρ
      have hz := hZ ρ hρ
      have hβ : 0 < ρ.re := by linarith [hz.2.1]
      refine ⟨?_, hz.2⟩
      by_contra hn
      have ho : analyticOrderAt (1 : DirichletCharacter ℂ (q : ℕ)).LFunction ρ = 0 := by
        rw [principal_order_eq_zeta hβ hz.2.2.1]
        exact analyticOrderAt_eq_zero.mpr (Or.inr hn)
      have hρ1 : ρ ≠ 1 := by intro he; simp [he] at hz
      have ha : AnalyticAt ℂ (1 : DirichletCharacter ℂ (q : ℕ)).LFunction ρ := by
        apply DifferentiableOn.analyticAt (s := ({1} : Set ℂ)ᶜ)
        · intro z hz
          exact (DirichletCharacter.differentiableAt_LFunction _ z (Or.inl hz)).differentiableWithinAt
        · exact isOpen_compl_singleton.mem_nhds hρ1
      exact (ha.analyticOrderAt_eq_zero.mp ho) hz.1
    have hs : (∑ ρ ∈ Z, (analyticOrderNatAt (1 : DirichletCharacter ℂ (q : ℕ)).LFunction ρ : ℝ)) =
        ∑ ρ ∈ Z, (analyticOrderNatAt riemannZeta ρ : ℝ) := by
      apply Finset.sum_congr rfl
      intro ρ hρ
      unfold analyticOrderNatAt
      rw [principal_order_eq_zeta (by linarith [(hZ ρ hρ).2.1]) (hZ ρ hρ).2.2.1]
    rw [hs]
    refine ((LeanLab.PNTPort.DirichletZF.U1482.rw_count_zeta τ).2 Z hζ).trans ?_
    apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
    apply Real.log_le_log (by positivity)
    have hq : (1 : ℝ) ≤ q := by exact_mod_cast q.property
    have hh := mul_le_mul_of_nonneg_left hq
      (show 0 ≤ 24 * LeanLab.PNTPort.DirichletZF.Z * (|τ| + 4) ^ 2 by
        positivity)
    nlinarith
  · exact (LeanLab.PNTPort.DirichletZF.U1482.rw_count_L hχ τ).2 Z hZ

/-- The local zero count bound is uniform in the height centre for the actual finite truncation. -/
theorem zeroTruncation_unit_bound {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ))
    {σ T : ℝ} (hσ : 1 / 2 ≤ σ) (hT : 0 ≤ T) (τ : ℝ) :
    (∑ ρ ∈ (zeroTruncation χ σ T).filter (fun ρ => |ρ.im - τ| ≤ 1 / 2),
      (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤
      log (24 * LeanLab.PNTPort.DirichletZF.Z * (q : ℝ) * (T + 5) ^ 2) / log (7 / 6) := by
  classical
  have hZpos := LeanLab.PNTPort.DirichletZF.Z_pos
  have hqpos : (0 : ℝ) < q := by exact_mod_cast q.property
  have hqone : (1 : ℝ) ≤ q := by exact_mod_cast q.property
  let F := (zeroTruncation χ σ T).filter (fun ρ => |ρ.im - τ| ≤ 1 / 2)
  by_cases hF : F.Nonempty
  · obtain ⟨ρ, hρ⟩ := hF
    obtain ⟨hρZ, hρτ⟩ := Finset.mem_filter.mp hρ
    have hr := (mem_zeroTruncation χ σ T ρ).mp hρZ
    have htau : |τ| ≤ T + 1 / 2 := by
      calc
        |τ| = |ρ.im - (ρ.im - τ)| := by congr 1; ring
        _ ≤ |ρ.im| + |ρ.im - τ| := abs_sub _ _
        _ ≤ T + 1 / 2 := add_le_add hr.1.2.2.2 hρτ
    have hh := zero_window_multiplicity_bound χ τ F (by
      intro z hz
      obtain ⟨hzZ, hzτ⟩ := Finset.mem_filter.mp hz
      have hr := (mem_zeroTruncation χ σ T z).mp hzZ
      exact ⟨hr.2, hσ.trans hr.1.1, hr.1.2.2.1, hzτ⟩)
    apply hh.trans
    apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
    apply Real.log_le_log (by positivity)
    have hp : (|τ| + 4) ^ 2 ≤ (T + 5) ^ 2 := by nlinarith [abs_nonneg τ]
    exact mul_le_mul_of_nonneg_left hp (by positivity)
  · have he : F = ∅ := Finset.not_nonempty_iff_eq_empty.mp hF
    change (∑ ρ ∈ F, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤ _
    rw [he, Finset.sum_empty]
    apply div_nonneg _ (Real.log_nonneg (by norm_num))
    apply Real.log_nonneg
    have hZone := LeanLab.PNTPort.DirichletZF.one_le_Z
    calc
      (1 : ℝ) ≤ 24 * 1 * 1 * 1 := by norm_num
      _ ≤ 24 * LeanLab.PNTPort.DirichletZF.Z * (q : ℝ) * (T + 5) ^ 2 := by
        gcongr
        nlinarith

/-- Page 366, reduce the actual zero mean square to its single weighted power sum.
The only extra premise is the displayed unit height multiplicity bound. -/
theorem actual_zero_mean_square_of_unit_bound {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ))
    (σ T : ℝ) {N B : ℝ} (hN : 0 < N) (hB : 0 ≤ B)
    (hunit : ∀ τ : ℝ,
      (∑ ρ ∈ (zeroTruncation χ σ T).filter (fun ρ => |ρ.im - τ| ≤ 1 / 2),
        (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤ B) :
    (1 / N) * (∫ x : ℝ in N / 2..3 * N,
      ‖∑ ρ ∈ zeroTruncation χ σ T,
        (analyticOrderNatAt χ.LFunction ρ : ℂ) * (x : ℂ) ^ (ρ - 1)‖ ^ 2) ≤
      40 * B * (1 + log (⌈2 * |T|⌉₊ + 1 : ℝ)) *
        ∑ ρ ∈ zeroTruncation χ σ T,
          (analyticOrderNatAt χ.LFunction ρ : ℝ) * N ^ (2 * ρ.re - 2) := by
  classical
  let Z := zeroTruncation χ σ T
  let m : ℂ → ℝ := fun ρ => analyticOrderNatAt χ.LFunction ρ
  let w : ℂ → ℝ := fun ρ => N ^ (ρ.re - 1)
  let K : ℕ := ⌈2 * |T|⌉₊
  have hm : ∀ ρ ∈ Z, 0 ≤ m ρ := fun ρ hρ => Nat.cast_nonneg _
  have hrow : ∀ ρ ∈ Z, (∑ ρ' ∈ Z, m ρ' / max 1 |ρ.im - ρ'.im|) ≤
      4 * B * (1 + log (K + 1 : ℝ)) := by
    intro ρ hρ
    have hh := zero_kernel_row_bound Z m (fun z => z.im) ρ.im B K hm hB ?_ hunit
    · simpa only [abs_sub_comm] using hh
    · intro ρ' hρ'
      have hi := ((mem_zeroTruncation χ σ T ρ).mp hρ).1.2.2.2
      have hi' := ((mem_zeroTruncation χ σ T ρ').mp hρ').1.2.2.2
      calc
        |ρ'.im - ρ.im| ≤ |ρ'.im| + |ρ.im| := abs_sub _ _
        _ ≤ 2 * |T| := by linarith [le_abs_self T]
        _ ≤ K := Nat.le_ceil _
  have hpair := weighted_zero_pair_schur Z m w (fun ρ => ρ.im)
    (4 * B * (1 + log (K + 1 : ℝ))) hm hrow
  have hpow (ρ ρ' : ℂ) : N ^ (ρ.re + ρ'.re - 2) = w ρ * w ρ' := by
    dsimp only [w]
    rw [← Real.rpow_add hN]
    congr 1
    ring
  have hw (ρ : ℂ) : w ρ ^ 2 = N ^ (2 * ρ.re - 2) := by
    dsimp only [w]
    rw [pow_two, ← Real.rpow_add hN]
    congr 1
    ring
  have heq : (∑ ρ ∈ Z, ∑ ρ' ∈ Z, m ρ * m ρ' * N ^ (ρ.re + ρ'.re - 2) /
      max 1 |ρ.im - ρ'.im|) =
      ∑ ρ ∈ Z, ∑ ρ' ∈ Z, m ρ * m ρ' * w ρ * w ρ' / max 1 |ρ.im - ρ'.im| := by
    apply Finset.sum_congr rfl
    intro ρ hρ
    apply Finset.sum_congr rfl
    intro ρ' hρ'
    rw [hpow]
    ring
  have hb := (actual_zero_mean_square_bound χ σ T hN).trans
    (mul_le_mul_of_nonneg_left (heq.trans_le hpair) (by norm_num : (0 : ℝ) ≤ 10))
  simp_rw [hw] at hb
  convert hb using 1
  dsimp only [Z, m, K]
  ring

/-- The single weighted zero sum bound behind 33 with all local zero counts discharged. -/
theorem actual_zero_mean_square_log_bound {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ))
    {σ T : ℝ} (hσ : 1 / 2 ≤ σ) (hT : 0 ≤ T) {N : ℝ} (hN : 0 < N) :
    (1 / N) * (∫ x : ℝ in N / 2..3 * N,
      ‖∑ ρ ∈ zeroTruncation χ σ T,
        (analyticOrderNatAt χ.LFunction ρ : ℂ) * (x : ℂ) ^ (ρ - 1)‖ ^ 2) ≤
      40 * (log (24 * LeanLab.PNTPort.DirichletZF.Z * (q : ℝ) * (T + 5) ^ 2) / log (7 / 6)) *
        (1 + log (⌈2 * |T|⌉₊ + 1 : ℝ)) *
        ∑ ρ ∈ zeroTruncation χ σ T,
          (analyticOrderNatAt χ.LFunction ρ : ℝ) * N ^ (2 * ρ.re - 2) := by
  have hunit := zeroTruncation_unit_bound χ hσ hT
  have hB : 0 ≤ log (24 * LeanLab.PNTPort.DirichletZF.Z * (q : ℝ) * (T + 5) ^ 2) / log (7 / 6) :=
    (Finset.sum_nonneg (fun ρ hρ => Nat.cast_nonneg (analyticOrderNatAt χ.LFunction ρ))).trans (hunit 0)
  exact actual_zero_mean_square_of_unit_bound χ σ T hN hB hunit

/-- Page 366, moving an exponent to the upper endpoint of a log sized bin costs exp two. -/
theorem zero_real_bin_power_bound {N δ d : ℝ} (hN : 1 < N) (hd : d ≤ δ + 1 / log N) :
    N ^ (-2 * δ) ≤ exp 2 * N ^ (-2 * d) := by
  have hNp : 0 < N := by linarith
  have hlog : 0 < log N := log_pos hN
  rw [Real.rpow_def_of_pos hNp, Real.rpow_def_of_pos hNp, ← Real.exp_add, Real.exp_le_exp]
  have hh := mul_le_mul_of_nonneg_left hd hlog.le
  have he : log N * (δ + 1 / log N) = log N * δ + 1 := by field_simp
  rw [he] at hh
  nlinarith

/-- Page 366, one actual real part bin is bounded by its actual cutoff zero count. -/
theorem actual_zero_real_bin_bound {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ))
    {N : ℕ} (hN : 2 ≤ N) (T : ℝ) (k : ℕ) :
    (∑ ρ ∈ (zeroTruncation χ (1 / 2) T).filter
      (fun ρ => ⌈(1 - ρ.re) * L N⌉₊ = k),
      (analyticOrderNatAt χ.LFunction ρ : ℝ) * (N : ℝ) ^ (2 * ρ.re - 2)) ≤
      exp 2 * (N : ℝ) ^ (-2 * ((k : ℝ) / L N)) *
        (zeroCount χ (max (1 / 2) (1 - (k : ℝ) / L N)) T).toReal := by
  classical
  have hL := L_pos hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  let Z := (zeroTruncation χ (1 / 2) T).filter (fun ρ => ⌈(1 - ρ.re) * L N⌉₊ = k)
  have hbin (ρ : ℂ) (hρ : ρ ∈ Z) :
      ρ ∈ zeroTruncation χ (max (1 / 2) (1 - (k : ℝ) / L N)) T ∧
      (N : ℝ) ^ (2 * ρ.re - 2) ≤ exp 2 * (N : ℝ) ^ (-2 * ((k : ℝ) / L N)) := by
    obtain ⟨hρZ, hk⟩ := Finset.mem_filter.mp hρ
    have hr := (mem_zeroTruncation χ (1 / 2) T ρ).mp hρZ
    have hp : 0 < (1 - ρ.re) * L N := mul_pos (by linarith [hr.1.2.2.1]) hL
    have hl := Nat.le_ceil ((1 - ρ.re) * L N)
    have hu := Nat.ceil_lt_add_one hp.le
    rw [hk] at hl hu
    have hlow : 1 - (k : ℝ) / L N ≤ ρ.re := by
      have hh : 1 - ρ.re ≤ (k : ℝ) / L N := (le_div_iff₀ hL).mpr (by nlinarith)
      linarith
    have hupper : (k : ℝ) / L N ≤ (1 - ρ.re) + 1 / L N := by
      rw [div_le_iff₀ hL]
      have he : ((1 - ρ.re) + 1 / L N) * L N = (1 - ρ.re) * L N + 1 := by field_simp
      rw [he]
      exact hu.le
    refine ⟨(mem_zeroTruncation χ _ T ρ).mpr ⟨⟨max_le hr.1.1 hlow, hr.1.2⟩, hr.2⟩, ?_⟩
    have hh := zero_real_bin_power_bound hN1 (by simpa only [L] using hupper)
    simpa only [show 2 * ρ.re - 2 = -2 * (1 - ρ.re) by ring, L] using hh
  have hcount : (∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℝ)) ≤
      (zeroCount χ (max (1 / 2) (1 - (k : ℝ) / L N)) T).toReal := by
    rw [zeroCount_eq_sum_orders, ENNReal.toReal_sum (fun _ _ => ENNReal.natCast_ne_top _)]
    simp only [ENNReal.toReal_natCast]
    apply Finset.sum_le_sum_of_subset_of_nonneg (fun ρ hρ => (hbin ρ hρ).1)
    intro ρ hρ hρ'
    exact Nat.cast_nonneg _
  calc
    _ ≤ ∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℝ) *
        (exp 2 * (N : ℝ) ^ (-2 * ((k : ℝ) / L N))) := by
      apply Finset.sum_le_sum
      intro ρ hρ
      exact mul_le_mul_of_nonneg_left (hbin ρ hρ).2 (Nat.cast_nonneg _)
    _ = (exp 2 * (N : ℝ) ^ (-2 * ((k : ℝ) / L N))) *
        ∑ ρ ∈ Z, (analyticOrderNatAt χ.LFunction ρ : ℝ) := by rw [← Finset.sum_mul]; ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hcount (by positivity)

/-- Page 366, sum all actual real part bins with their cumulative zero counts. -/
theorem actual_zero_power_sum_bins {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ))
    {N : ℕ} (hN : 2 ≤ N) (T : ℝ) :
    (∑ ρ ∈ zeroTruncation χ (1 / 2) T,
      (analyticOrderNatAt χ.LFunction ρ : ℝ) * (N : ℝ) ^ (2 * ρ.re - 2)) ≤
      exp 2 * ∑ k ∈ Finset.Icc 1 ⌈L N / 2⌉₊,
        (N : ℝ) ^ (-2 * ((k : ℝ) / L N)) *
          (zeroCount χ (max (1 / 2) (1 - (k : ℝ) / L N)) T).toReal := by
  classical
  let Z := zeroTruncation χ (1 / 2) T
  let J := Finset.Icc 1 ⌈L N / 2⌉₊
  have hL := L_pos hN
  have hmap : ∀ ρ ∈ Z, ⌈(1 - ρ.re) * L N⌉₊ ∈ J := by
    intro ρ hρ
    have hr := (mem_zeroTruncation χ (1 / 2) T ρ).mp hρ
    apply Finset.mem_Icc.mpr
    constructor
    · exact Nat.one_le_ceil_iff.mpr (mul_pos (by linarith [hr.1.2.2.1]) hL)
    · exact Nat.ceil_mono (by nlinarith [hr.1.1])
  have hg := (Finset.sum_fiberwise_of_maps_to hmap
    (fun ρ => (analyticOrderNatAt χ.LFunction ρ : ℝ) * (N : ℝ) ^ (2 * ρ.re - 2))).symm
  change (∑ ρ ∈ Z, _) ≤ _
  rw [hg]
  calc
    _ ≤ ∑ k ∈ J, exp 2 * (N : ℝ) ^ (-2 * ((k : ℝ) / L N)) *
        (zeroCount χ (max (1 / 2) (1 - (k : ℝ) / L N)) T).toReal := by
      apply Finset.sum_le_sum
      intro k hk
      exact actual_zero_real_bin_bound χ hN T k
    _ = _ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      ring

/-- Page 364, the finite weighted L2 triangle inequality before the Gallagher step.
The L2 hypotheses ensure that every displayed real integral has its intended value. -/
theorem weighted_integral_sqrt_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℂ) (c : ι → ℂ) (μ : Measure ℝ)
    (hf : ∀ i ∈ s, MemLp (f i) 2 μ) :
    sqrt (∫ x, ‖∑ i ∈ s, c i * f i x‖ ^ 2 ∂μ) ≤
      ∑ i ∈ s, ‖c i‖ * sqrt (∫ x, ‖f i x‖ ^ 2 ∂μ) := by
  have hnorm (g : ℝ → ℂ) (hg : AEStronglyMeasurable g μ) :
      lpNorm g 2 μ = sqrt (∫ x, ‖g x‖ ^ 2 ∂μ) := by
    rw [lpNorm_eq_integral_norm_rpow_toReal (by norm_num) (by norm_num) hg]
    norm_num [Real.sqrt_eq_rpow, Real.rpow_two]
  have hmem : ∀ i ∈ s, MemLp (fun x => c i * f i x) 2 μ := fun i hi => (hf i hi).const_mul (c i)
  have hh := lpNorm_sum_le hmem (by norm_num : (1 : ENNReal) ≤ 2)
  have hs : MemLp (∑ i ∈ s, fun x => c i * f i x) 2 μ := by
    convert memLp_finsetSum s hmem using 1
    ext x
    simp only [Finset.sum_apply]
  rw [hnorm _ hs.aestronglyMeasurable] at hh
  have he : ∀ i ∈ s, lpNorm (fun x => c i * f i x) 2 μ =
      ‖c i‖ * sqrt (∫ x, ‖f i x‖ ^ 2 ∂μ) := by
    intro i hi
    change lpNorm (c i • f i) 2 μ = _
    rw [lpNorm_const_smul, hnorm _ (hf i hi).aestronglyMeasurable]
    rfl
  simp_rw [Finset.sum_apply] at hh
  exact hh.trans_eq (Finset.sum_congr rfl he)

/-- Page 365, the explicit formula gives the exact moving character interval identity
at natural endpoints. This is algebra with the defined explicit error, not a proof of 28. -/
theorem character_interval_explicit_identity {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) {m n : ℕ} (hmn : m ≤ n) (T : ℝ) :
    (∑ k ∈ Finset.Ioc m n, ((ArithmeticFunction.vonMangoldt k : ℂ) * χ k - if χ = 1 then 1 else 0)) =
      explicitError χ (n : ℝ) T - explicitError χ (m : ℝ) T -
        (explicitZeroSum χ (n : ℝ) T - explicitZeroSum χ (m : ℝ) T) := by
  have hsum (f : ℕ → ℂ) : ∑ k ∈ Finset.Ioc m n, f k =
      (∑ k ∈ Finset.Icc 1 n, f k) - ∑ k ∈ Finset.Icc 1 m, f k := by
    have hh := Finset.sum_Ioc_consecutive f (Nat.zero_le m) hmn
    simpa only [← Finset.Icc_add_one_left_eq_Ioc, Nat.zero_add] using (eq_sub_iff_add_eq.mpr (by
      simpa only [← Finset.Icc_add_one_left_eq_Ioc, Nat.zero_add, add_comm] using hh))
  rw [hsum, Finset.sum_sub_distrib, Finset.sum_sub_distrib]
  unfold explicitError
  simp only [Nat.floor_natCast]
  by_cases hχ : χ = 1
  · simp only [ite_eq_left hχ, Finset.sum_const, Nat.card_Icc, Nat.add_sub_cancel,
      nsmul_eq_mul, mul_one]
    push_cast
    ring
  · simp only [ite_eq_right hχ, Finset.sum_const_zero, sub_zero]
    ring

/-- The actual character polynomial Psi prime on page 364, with inclusive lab endpoints. -/
noncomputable def characterPolynomial (N : ℕ) {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) (η : ℝ) : ℂ := by
  classical
  exact ∑ n ∈ Finset.Icc N (2 * N),
    ((ArithmeticFunction.vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0) *
      LeanLab.PerelliPintz1992.e ((n : ℝ) * η)

/-- LEAF. Page 364, quarter radius Gallagher variant for the actual character polynomial.
P. X. Gallagher, Invent. Math. 11, 1970, pages 329 to 339.
The unspecified logarithmic power printed on page 364 is retained.
The window remains two q Q and the radius is one divided by four q Q.
This auxiliary variant does not give the full Farey radius used in 27. -/
def CharacterGallagherStep : Prop :=
  ∃ C N₀ : ℝ, ∃ c : ℕ, 0 < C ∧ ∀ N : ℕ, N₀ ≤ N → ∀ q : ℕ+,
    (q : ℝ) ≤ LeanLab.PerelliPintz1992.Decomp97.Q N →
    ∀ χ : DirichletCharacter ℂ (q : ℕ),
      (∫ η in Set.Ioc (-1 / (4 * (q : ℝ) * LeanLab.PerelliPintz1992.Decomp97.Q N))
        (1 / (4 * (q : ℝ) * LeanLab.PerelliPintz1992.Decomp97.Q N)),
        ‖characterPolynomial N χ η‖ ^ 2) ≤
        C * L N ^ c * N * LeanLab.PerelliPintz1992.Decomp97.W N χ ^ 2

/-- The untruncated moving character sum on page 365, before 28. -/
noncomputable def movingCharacterSum {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) (x h : ℝ) : ℂ := by
  classical
  exact ∑ n ∈ Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊,
    ((ArithmeticFunction.vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0)

/-- LEAF. Page 365, the unclipped fixed window variant of the comparison before 28.
This does not compare the sealed clipped W with an unclipped relative window.
The universal E formulation avoids assuming existence of a real supremum.
The hypothesis uses every theta in the actual printed range.
This comparison is an open cited input. -/
def MovingWindowStep : Prop :=
  ∃ C N₀ : ℝ, 0 < C ∧ ∀ N : ℕ, N₀ ≤ N → ∀ q : ℕ+,
    (q : ℝ) ≤ LeanLab.PerelliPintz1992.Decomp97.Q N →
    ∀ χ : DirichletCharacter ℂ (q : ℕ), ∀ E : ℝ, 0 ≤ E →
      (∀ θ : ℝ, ((q : ℝ) * LeanLab.PerelliPintz1992.Decomp97.Q N) / (20 * N) ≤ θ →
        θ ≤ (20 * (q : ℝ) * LeanLab.PerelliPintz1992.Decomp97.Q N) / N →
        (∫ x in Set.Ioc ((N : ℝ) / 2) (3 * N : ℝ),
          ‖movingCharacterSum χ x (θ * x)‖ ^ 2) ≤ E) →
      (1 / ((N : ℝ) * ((q : ℝ) * LeanLab.PerelliPintz1992.Decomp97.Q N) ^ 2)) *
        (∫ x in Set.Ioc ((N : ℝ) / 2) (2 * N : ℝ),
          ‖movingCharacterSum χ x (2 * (q : ℝ) * LeanLab.PerelliPintz1992.Decomp97.Q N)‖ ^ 2) ≤
        C * E / ((N : ℝ) * ((q : ℝ) * LeanLab.PerelliPintz1992.Decomp97.Q N) ^ 2)

/-- Page 366, the actual zero mean square is bounded by the finite cumulative count bins.
All local zero counts are discharged. No density or zero free input is used. -/
theorem actual_zero_mean_square_bins {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ))
    {N : ℕ} (hN : 2 ≤ N) {T : ℝ} (hT : 0 ≤ T) :
    (1 / (N : ℝ)) * (∫ x : ℝ in (N : ℝ) / 2..3 * N,
      ‖∑ ρ ∈ zeroTruncation χ (1 / 2) T,
        (analyticOrderNatAt χ.LFunction ρ : ℂ) * (x : ℂ) ^ (ρ - 1)‖ ^ 2) ≤
      (40 * exp 2) *
        (log (24 * LeanLab.PNTPort.DirichletZF.Z * (q : ℝ) * (T + 5) ^ 2) / log (7 / 6)) *
        (1 + log (⌈2 * |T|⌉₊ + 1 : ℝ)) *
        ∑ k ∈ Finset.Icc 1 ⌈L N / 2⌉₊,
          (N : ℝ) ^ (-2 * ((k : ℝ) / L N)) *
            (zeroCount χ (max (1 / 2) (1 - (k : ℝ) / L N)) T).toReal := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hh := actual_zero_mean_square_log_bound χ (σ := 1 / 2) le_rfl hT hNp
  have hB : 0 ≤ log (24 * LeanLab.PNTPort.DirichletZF.Z * (q : ℝ) * (T + 5) ^ 2) / log (7 / 6) :=
    (Finset.sum_nonneg (fun ρ hρ => Nat.cast_nonneg (analyticOrderNatAt χ.LFunction ρ))).trans
      (zeroTruncation_unit_bound χ le_rfl hT 0)
  have hlog : 0 ≤ log (⌈2 * |T|⌉₊ + 1 : ℝ) := log_nonneg (by linarith [Nat.cast_nonneg (α := ℝ) ⌈2 * |T|⌉₊])
  apply hh.trans
  have hb := mul_le_mul_of_nonneg_left (actual_zero_power_sum_bins χ hN T)
    (show 0 ≤ 40 *
      (log (24 * LeanLab.PNTPort.DirichletZF.Z * (q : ℝ) * (T + 5) ^ 2) / log (7 / 6)) *
      (1 + log (⌈2 * |T|⌉₊ + 1 : ℝ)) by positivity)
  convert hb using 1
  ring

/-- Page 364, inclusive and strict left endpoints give equal finite windows almost everywhere. -/
theorem nat_window_left_endpoints_ae (s : Finset ℕ) (a : ℕ → ℂ) (h : ℝ) :
    (fun x : ℝ => ∑ n ∈ s.filter (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + h), a n) =ᵐ[volume]
      (fun x : ℝ => ∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h), a n) := by
  classical
  have hne : ∀ n : ℕ, ∀ᵐ x : ℝ, x ≠ (n : ℝ) := by
    intro n
    rw [ae_iff]
    simp
  filter_upwards [ae_all_iff.mpr hne] with x hx
  have hf : s.filter (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + h) =
      s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h) := by
    apply Finset.filter_congr
    intro n hn
    constructor
    · rintro ⟨hxn, hnx⟩
      exact ⟨lt_of_le_of_ne hxn (hx n), hnx⟩
    · rintro ⟨hxn, hnx⟩
      exact ⟨hxn.le, hnx⟩
  rw [hf]

/-- Page 364, support of the finite short window when its length is at most N divided by two. -/
theorem nat_short_window_integral_restrict (N : ℕ) (a : ℕ → ℂ) (h : ℝ) (hh : h ≤ (N : ℝ) / 2) :
    (∫ x : ℝ, ‖∑ n ∈ (Finset.Icc N (2 * N)).filter
      (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h), a n‖ ^ 2) =
      ∫ x in Set.Ioc ((N : ℝ) / 2) (2 * N : ℝ),
        ‖∑ n ∈ (Finset.Icc N (2 * N)).filter
          (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h), a n‖ ^ 2 := by
  rw [← integral_Icc_eq_integral_Ioc]
  symm
  apply setIntegral_eq_integral_of_forall_compl_eq_zero
  intro x hx
  have hz : ∑ n ∈ (Finset.Icc N (2 * N)).filter
      (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + h), a n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    obtain ⟨hnN, hxn, hnx⟩ := Finset.mem_filter.mp hn
    have hlo : (N : ℝ) ≤ n := by exact_mod_cast (Finset.mem_Icc.mp hnN).1
    have hhi : (n : ℝ) ≤ 2 * N := by exact_mod_cast (Finset.mem_Icc.mp hnN).2
    apply False.elim
    apply hx
    constructor <;> linarith
  rw [hz, norm_zero, zero_pow (by norm_num : 2 ≠ 0)]

/-- Page 364, Gallagher's lemma for finite natural frequencies.
The moving window has exactly length one divided by twice the frequency radius. -/
theorem gallagher_nat_window (s : Finset ℕ) (a : ℕ → ℂ) {T : ℝ} (hT : 0 < T) :
    (∫ t in (-T)..T, ‖∑ n ∈ s, a n * e ((n : ℝ) * t)‖ ^ 2) ≤
      Real.pi ^ 2 * T ^ 2 * ∫ x : ℝ,
        ‖∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + 1 / (2 * T)), a n‖ ^ 2 := by
  let emb : ℕ ↪ ℤ := ⟨Int.ofNat, Int.ofNat_injective⟩
  let s' := s.map emb
  let a' : ℤ → ℂ := fun n => a n.toNat
  have hcast (n : ℕ) : ((Int.ofNat n : ℤ) : ℝ) = (n : ℝ) := Int.cast_natCast n
  have hnat (n : ℕ) : (Int.ofNat n).toNat = n := rfl
  have hpoly (t : ℝ) : (∑ n ∈ s, a n * e ((n : ℝ) * (-t))) =
      ∑ n ∈ s', a' n * Complex.exp ((-2 * Real.pi * t * Complex.I) * (n : ℝ)) := by
    dsimp only [s', a']
    rw [Finset.sum_map]
    apply Finset.sum_congr rfl
    intro n hn
    simp only [emb, Function.Embedding.coeFn_mk, hnat, hcast]
    congr 2
    unfold e
    congr 1
    push_cast
    ring
  have hwindow (x : ℝ) : LeanLab.ExceptionalSet.WindowParseval264.window s' a' (1 / (2 * T)) x =
      ∑ n ∈ s.filter (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + 1 / (2 * T)), a n := by
    rw [LeanLab.ExceptionalSet.WindowParseval264.window_eq_sum_filter]
    dsimp only [s', a']
    simp only [Finset.sum_filter, Finset.sum_map, emb, Function.Embedding.coeFn_mk,
      hcast, hnat]
  have hi : (∫ t in (-T)..T, ‖∑ n ∈ s, a n * e ((n : ℝ) * t)‖ ^ 2) =
      ∫ t in (-T)..T, ‖∑ n ∈ s, a n * e ((n : ℝ) * (-t))‖ ^ 2 := by
    simpa only [neg_neg] using
      (intervalIntegral.integral_comp_neg (fun t : ℝ => ‖∑ n ∈ s, a n * e ((n : ℝ) * t)‖ ^ 2)
        (a := -T) (b := T)).symm
  rw [hi]
  simp_rw [hpoly]
  have hh := LeanLab.ExceptionalSet.WindowParseval264.window_bound s' a' hT
  simpa only [hwindow] using hh

/-- Page 364, the proved Gallagher comparison at one quarter of the Farey radius.
This exactly matches the moving window length in the sealed W. It does not prove
the full Farey radius comparison. -/
theorem character_gallagher_quarter {N : ℕ} (hN : 0 < N) {q : ℕ+}
    (hq : (q : ℝ) ≤ Decomp97.Q N) (χ : DirichletCharacter ℂ (q : ℕ)) :
    (∫ η in Ioc (-1 / (4 * (q : ℝ) * Decomp97.Q N))
      (1 / (4 * (q : ℝ) * Decomp97.Q N)), ‖characterPolynomial N χ η‖ ^ 2) ≤
      (Real.pi ^ 2 / 16) * N * Decomp97.W N χ ^ 2 := by
  classical
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hqp : (0 : ℝ) < q := by exact_mod_cast q.property
  have hQp : 0 < Decomp97.Q N := hqp.trans_le hq
  have hQsq : (Decomp97.Q N) ^ 2 = (N : ℝ) / 4 := by
    unfold Decomp97.Q
    rw [← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg N)]
  have hshort : 2 * (q : ℝ) * Decomp97.Q N ≤ (N : ℝ) / 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hq hQp.le]
  let s := Finset.Icc N (2 * N)
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0
  let T : ℝ := 1 / (4 * (q : ℝ) * Decomp97.Q N)
  have hTp : 0 < T := by dsimp only [T]; positivity
  have hlen : 1 / (2 * T) = 2 * (q : ℝ) * Decomp97.Q N := by
    dsimp only [T]
    field_simp
    ring
  have hgal := gallagher_nat_window s f hTp
  rw [hlen] at hgal
  let J : ℝ := ∫ x in Ioc ((N : ℝ) / 2) (2 * N : ℝ),
    ‖∑ n ∈ s.filter (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + 2 * q * Decomp97.Q N), f n‖ ^ 2
  have hJ : 0 ≤ J := integral_nonneg (fun x => sq_nonneg _)
  have hW : Decomp97.W N χ ^ 2 = (1 / (((q : ℝ) * Decomp97.Q N) ^ 2 * N)) * J := by
    unfold Decomp97.W
    have hn : 0 ≤ (1 / (((q : ℝ) * Decomp97.Q N) ^ 2 * N)) * J := by positivity
    convert Real.sq_sqrt hn using 1
    all_goals simp only [J, s, f, Finset.sum_filter]
    all_goals congr
    funext x
    congr 2
    apply Finset.sum_congr rfl
    intro n hn
    split_ifs <;> rfl
  have hi : (∫ x : ℝ, ‖∑ n ∈ s.filter
      (fun n : ℕ => x < (n : ℝ) ∧ (n : ℝ) ≤ x + 2 * q * Decomp97.Q N), f n‖ ^ 2) = J := by
    rw [nat_short_window_integral_restrict N f _ hshort]
    apply integral_congr_ae
    apply ae_restrict_of_ae
    filter_upwards [nat_window_left_endpoints_ae s f (2 * q * Decomp97.Q N)] with x hx
    rw [hx]
  rw [hi] at hgal
  have hc : Real.pi ^ 2 * T ^ 2 * J = (Real.pi ^ 2 / 16) * N * Decomp97.W N χ ^ 2 := by
    rw [hW]
    dsimp only [T]
    field_simp
    ring
  rw [show (-1 : ℝ) / (4 * (q : ℝ) * Decomp97.Q N) = -T by dsimp only [T]; ring]
  change (∫ η in Ioc (-T) T, ‖characterPolynomial N χ η‖ ^ 2) ≤ _
  rw [← intervalIntegral.integral_of_le (by linarith : -T ≤ T)]
  change (∫ η in (-T)..T, ‖∑ n ∈ s, f n * e ((n : ℝ) * η)‖ ^ 2) ≤ _
  exact hgal.trans_eq hc

/-- The finite sum over all characters of a fixed positive modulus is finite without density inputs. -/
theorem allCharacterCount_ne_top (q : ℕ+) (σ T : ℝ) : allCharacterCount q σ T ≠ ⊤ := by
  unfold allCharacterCount
  rw [tsum_fintype]
  exact ENNReal.sum_ne_top.mpr (fun χ hχ => zeroCount_ne_top χ σ T)

/-- Page 367, the actual cumulative primitive character count is finite at every finite conductor bound. -/
theorem primitiveCount_ne_top (Q σ T : ℝ) : primitiveCount Q σ T ≠ ⊤ := by
  classical
  let b : ℕ+ := ⟨⌊Q⌋₊ + 1, by omega⟩
  have hfin : {q : ℕ+ | (q : ℝ) ≤ Q}.Finite := by
    apply (Set.finite_Iic b).subset
    intro q hq
    have hh : (q : ℕ) ≤ ⌊Q⌋₊ := Nat.le_floor hq
    change (q : ℕ) ≤ ⌊Q⌋₊ + 1
    omega
  unfold primitiveCount
  rw [tsum_eq_sum (s := hfin.toFinset) ?_]
  · apply ENNReal.sum_ne_top.mpr
    intro q hq
    have hqQ : (q : ℝ) ≤ Q := hfin.mem_toFinset.mp hq
    rw [ite_eq_left hqQ, tsum_fintype]
    apply ENNReal.sum_ne_top.mpr
    intro χ hχ
    split_ifs
    · exact zeroCount_ne_top χ σ T
    · exact ENNReal.zero_ne_top
  · intro q hq
    exact ite_eq_right (fun hh => hq (hfin.mem_toFinset.mpr hh))

end LeanLab.PerelliPintz1992.Section6
