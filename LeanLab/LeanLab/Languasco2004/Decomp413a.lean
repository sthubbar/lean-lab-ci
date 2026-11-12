/-
Perelli and Pintz 1993, page 44 displays 3 and 5, pages 46 to 48.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
The cited comparison is PP1992 page 359 display 5.
Source http://www.numdam.org/item/CM_1992__82_3_355_0/.
AI wrote the Lean code. Goldbach is open.
The three smaller inputs stay OPEN. Existing declarations stay sealed.
-/
import LeanLab.Languasco2004.Decomp489e

namespace LeanLab.Languasco2004.Decomp413a
open Finset Real MeasureTheory Decomp279b
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 44 display 3: the capped kernel is nonnegative for nonnegative H. -/
theorem kernel_nonneg {H : ℝ} (hH : 0 ≤ H) (x : ℝ) : 0 ≤ kernel H x := by
  unfold kernel
  split_ifs
  · exact hH
  · exact le_min hH (inv_nonneg.mpr (abs_nonneg _))

/-- Page 44 display 3: the cap also holds at the kernel poles. -/
theorem kernel_le (H x : ℝ) : kernel H x ≤ H := by
  unfold kernel
  split_ifs
  · exact le_rfl
  · exact min_le_left _ _

/-- Page 44 display 5: every local S2 mass is nonnegative. -/
theorem localMass_nonneg (N Y H B ξ : ℝ) : 0 ≤ localMass N Y H B ξ := by
  exact integral_nonneg (fun _ => sq_nonneg _)

/-- Page 44 display 3: every squared kernel mass is nonnegative. -/
theorem kernelMass_nonneg (N Y H B ξ : ℝ) : 0 ≤ kernelMass N Y H B ξ := by
  exact integral_nonneg (fun _ => mul_nonneg (sq_nonneg _) (sq_nonneg _))

/-- Pages 43 and 44: at Y = 1 the S2 sum vanishes since Lambda of one is zero.
This checks the domains of both new integrals without an analytic input. -/
theorem unit_length_instances (N H B ξ : ℝ) :
    localMass N 1 H B ξ = 0 ∧ kernelMass N 1 H B ξ = 0 := by
  have hsum : ∀ α : ℝ, secondSum 1 α = 0 := by
    intro α
    simp [secondSum]
  simp [localMass, kernelMass, hsum]

/-- Page 44 display 3: the value at an integer pole is the cap. -/
theorem kernel_pole_instance (H : ℝ) : kernel H 0 = H := by
  simp [kernel]

/-- LEAF. Page 44 display 5, proved on pages 46 to 48 through display 26.
Only the local S2 integral is estimated. The shifted period and real floors
are the endpoint version of the source's periodic and integer convention. -/
theorem local_mass_bound :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, 0 < C ∧ ∀ N : ℝ, N₀ ≤ N → ∀ ξ : ℝ,
      localMass N (localization N η) (windowLength N η) (arcExponent η A) ξ ≤
        C * localization N η / Real.log N ^ (2 * A + 3) := by
  exact Decomp489e.local_mass_bound_from_leaves

/-! ### Private support lemmas for the local covering step -/

/-- The union of major arcs is measurable. Ported from the (private) argument
of `Decomp279b`, since the covering step integrates over its complement. -/
private lemma measurableSet_majorSet' (N Y B : ℝ) : MeasurableSet (majorSet N Y B) := by
  have h : majorSet N Y B = ⋃ (q : ℕ) (a : ℕ), {α : ℝ |
      1 ≤ q ∧ (q : ℝ) ≤ Real.log N ^ B ∧ 1 ≤ a ∧ a ≤ q ∧ Nat.Coprime a q ∧
        |α - (a : ℝ) / q| < Real.log N ^ (2 * B) / ((q : ℝ) * Y)} := by
    ext α
    simp only [majorSet, Set.mem_setOf_eq, Set.mem_iUnion]
  rw [h]
  apply MeasurableSet.iUnion; intro q
  apply MeasurableSet.iUnion; intro a
  by_cases hq : 1 ≤ q ∧ (q : ℝ) ≤ Real.log N ^ B ∧ 1 ≤ a ∧ a ≤ q ∧ Nat.Coprime a q
  · obtain ⟨h1, h2, h3, h4, h5⟩ := hq
    convert measurableSet_Ioo (a := (a : ℝ) / q - Real.log N ^ (2 * B) / ((q : ℝ) * Y))
      (b := (a : ℝ) / q + Real.log N ^ (2 * B) / ((q : ℝ) * Y)) using 1
    ext α
    simp only [Set.mem_setOf_eq, Set.mem_Ioo]
    constructor
    · rintro ⟨-, -, -, -, -, hlt⟩
      rw [abs_lt] at hlt
      exact ⟨by linarith [hlt.1], by linarith [hlt.2]⟩
    · rintro ⟨ha, hb⟩
      exact ⟨h1, h2, h3, h4, h5, by rw [abs_lt]; exact ⟨by linarith, by linarith⟩⟩
  · have hne : {α : ℝ | 1 ≤ q ∧ (q : ℝ) ≤ Real.log N ^ B ∧ 1 ≤ a ∧ a ≤ q ∧
        Nat.Coprime a q ∧ |α - (a : ℝ) / q| < Real.log N ^ (2 * B) / ((q : ℝ) * Y)} = ∅ := by
      ext α
      simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false]
      constructor
      · rintro ⟨h1, h2, h3, h4, h5, -⟩
        exact hq ⟨h1, h2, h3, h4, h5⟩
      · intro hh
        exact hh.elim
    rw [hne]
    exact MeasurableSet.empty

/-- The phase has norm one. -/
private lemma norm_phase' (x : ℝ) : ‖phase x‖ = 1 := by
  unfold phase
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- The second sum is bounded by its total weight. -/
private lemma secondSum_norm_le' (Y : ℝ) (α : ℝ) :
    ‖secondSum Y α‖ ≤ ∑ k ∈ Finset.Icc 1 ⌊Y⌋₊, ArithmeticFunction.vonMangoldt (k : ℕ) := by
  have hterm : ∀ k ∈ Finset.Icc 1 ⌊Y⌋₊,
      ‖(ArithmeticFunction.vonMangoldt (k : ℕ) : ℂ) * phase ((k : ℝ) * α)‖ =
        ArithmeticFunction.vonMangoldt (k : ℕ) := by
    intro k _
    rw [norm_mul, norm_phase', mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg]
  calc ‖secondSum Y α‖ =
      ‖∑ k ∈ Finset.Icc 1 ⌊Y⌋₊,
        (ArithmeticFunction.vonMangoldt (k : ℕ) : ℂ) * phase ((k : ℝ) * α)‖ := rfl
    _ ≤ ∑ k ∈ Finset.Icc 1 ⌊Y⌋₊,
        ‖(ArithmeticFunction.vonMangoldt (k : ℕ) : ℂ) * phase ((k : ℝ) * α)‖ := norm_sum_le _ _
    _ = ∑ k ∈ Finset.Icc 1 ⌊Y⌋₊, ArithmeticFunction.vonMangoldt (k : ℕ) :=
        Finset.sum_congr rfl hterm

/-- Away from a pole the kernel is at most the reciprocal nearest integer distance. -/
private lemma kernel_le_inverse' (H x : ℝ) (hx : x ≠ (round x : ℤ)) :
    kernel H x ≤ |x - (round x : ℤ)|⁻¹ := by
  unfold kernel
  rw [if_neg hx]
  exact min_le_right _ _

/-- The squared kernel is at most the square of the cap. -/
private lemma kernel_sq_le_cap' {H : ℝ} (hH : 0 ≤ H) (x : ℝ) : kernel H x ^ 2 ≤ H ^ 2 := by
  have h0 : 0 ≤ kernel H x := kernel_nonneg hH x
  have h1 : kernel H x ≤ H := kernel_le H x
  nlinarith

/-- The squared kernel is at most the square of the reciprocal distance off the poles. -/
private lemma kernel_sq_le_inv' {H : ℝ} (hH : 0 ≤ H) {x : ℝ} (hx : x ≠ (round x : ℤ)) :
    kernel H x ^ 2 ≤ |x - (round x : ℤ)|⁻¹ ^ 2 := by
  have h0 : 0 ≤ kernel H x := kernel_nonneg hH x
  have h1 : kernel H x ≤ |x - (round x : ℤ)|⁻¹ := kernel_le_inverse' H x hx
  have h2 : 0 ≤ |x - (round x : ℤ)|⁻¹ := by positivity
  nlinarith

/-- The upper half of the nearest integer distance is strict. -/
private lemma sub_round_lt_half' (x : ℝ) : x - (round x : ℤ) < 1 / 2 := by
  have h := abs_sub_round x
  have h2 := sub_half_lt_round x
  rw [abs_le] at h
  rcases lt_or_eq_of_le h.2 with hlt | heq
  · exact hlt
  · exfalso; linarith

/-- Every real lies in the half-open cell of its nearest half-integer peak. -/
private lemma self_mem_cell' (ξ α : ℝ) :
    α ∈ Set.Ico (ξ + ((round (2 * (α - ξ)) : ℤ) : ℝ) / 2 - 1 / 4)
      (ξ + ((round (2 * (α - ξ)) : ℤ) : ℝ) / 2 + 1 / 4) := by
  rw [Set.mem_Ico]
  constructor
  · linarith [round_le_add_half (2 * (α - ξ))]
  · linarith [sub_half_lt_round (2 * (α - ξ))]

/-- Inside the cell of the peak `m` the nearest integer is `m`. -/
private lemma round_eq_of_mem_cell' {ξ : ℝ} {m : ℤ} {α : ℝ}
    (h : α ∈ Set.Ico (ξ + (m : ℝ) / 2 - 1 / 4) (ξ + (m : ℝ) / 2 + 1 / 4)) :
    round (2 * (α - ξ)) = m := by
  rw [round_eq_iff]
  rw [Set.mem_Ico] at h ⊢
  constructor <;> push_cast <;> linarith [h.1, h.2]

/-- The rounded value dominates the floor of any smaller number. -/
private lemma floor_le_round' {y x : ℝ} (h : y ≤ x) : (⌊y⌋ : ℤ) ≤ round x := by
  by_contra hc
  rw [not_le] at hc
  have h1 : ((round x : ℤ) : ℝ) + 1 ≤ ((⌊y⌋ : ℤ) : ℝ) := by
    exact_mod_cast (Int.lt_iff_add_one_le.mp hc)
  have h2 := abs_sub_round x
  rw [abs_le] at h2
  have h3 : ((⌊y⌋ : ℤ) : ℝ) ≤ y := Int.floor_le y
  linarith [h2.2]

/-- The rounded value is dominated by the ceiling of any larger number. -/
private lemma round_le_ceil' {x z : ℝ} (h : x ≤ z) : round x ≤ ⌈z⌉ := by
  by_contra hc
  rw [not_le] at hc
  have h1 : ((⌈z⌉ : ℤ) : ℝ) + 1 ≤ ((round x : ℤ) : ℝ) := by
    exact_mod_cast (Int.lt_iff_add_one_le.mp hc)
  have h2 := abs_sub_round x
  rw [abs_le] at h2
  have h3 : z ≤ ((⌈z⌉ : ℤ) : ℝ) := Int.le_ceil z
  linarith [h2.1]

/-- The shifted inverse square sum is bounded by one. -/
private lemma sum_shift_le' : ∀ m : ℕ,
    (∑ j ∈ Finset.range m, (1 : ℝ) / ((j : ℝ) + 2) ^ 2) ≤ 1 - 1 / ((m : ℝ) + 1)
  | 0 => by norm_num
  | m + 1 => by
    rw [Finset.sum_range_succ]
    have ih := sum_shift_le' m
    push_cast
    have hc : ((m : ℝ) + 1 + 1) = ((m : ℝ) + 2) := by ring
    rw [hc]
    have key : (1 : ℝ) / ((m : ℝ) + 2) ^ 2 ≤ 1 / ((m : ℝ) + 1) - 1 / ((m : ℝ) + 2) := by
      have h1 : ((m : ℝ) + 1) ≠ 0 := by positivity
      have h2 : ((m : ℝ) + 2) ≠ 0 := by positivity
      field_simp
      nlinarith
    linarith

/-- The annulus weights sum to a bounded constant, uniformly in the cutoff. -/
private lemma sum_inv_sq_le' (n : ℕ) :
    (∑ j ∈ Finset.range n, (1 : ℝ) / ((max 1 j : ℕ) : ℝ) ^ 2) ≤ 3 := by
  match n with
  | 0 => norm_num
  | 1 => norm_num
  | (m + 2) =>
    rw [Finset.sum_range_succ' (fun j => (1 : ℝ) / ((max 1 j : ℕ) : ℝ) ^ 2) (m + 1)]
    rw [Finset.sum_range_succ' (fun j => (1 : ℝ) / ((max 1 (j + 1) : ℕ) : ℝ) ^ 2) m]
    have h1 : (1 : ℝ) / ((max 1 0 : ℕ) : ℝ) ^ 2 = 1 := by norm_num
    have h2 : (1 : ℝ) / ((max 1 1 : ℕ) : ℝ) ^ 2 = 1 := by norm_num
    have h3 : ∀ i : ℕ,
        (1 : ℝ) / ((max 1 (i + 1 + 1) : ℕ) : ℝ) ^ 2 = 1 / ((i : ℝ) + 2) ^ 2 := by
      intro i
      rw [Nat.max_eq_right (by omega : 1 ≤ i + 1 + 1)]
      push_cast
      ring
    rw [h1, h2, Finset.sum_congr rfl (fun i _ => h3 i)]
    have hs := sum_shift_le' m
    have h4 : (0:ℝ) ≤ 1 / ((m : ℝ) + 1) := by positivity
    linarith

/-- Cells of distinct peaks are disjoint. -/
private lemma cell_disjoint' (ξ : ℝ) {m m' : ℤ} (hne : m ≠ m') :
    Disjoint (Set.Ico (ξ + (m : ℝ) / 2 - 1 / 4) (ξ + (m : ℝ) / 2 + 1 / 4))
      (Set.Ico (ξ + (m' : ℝ) / 2 - 1 / 4) (ξ + (m' : ℝ) / 2 + 1 / 4)) := by
  rw [Set.disjoint_left]
  intro x hx hx'
  rw [Set.mem_Ico] at hx hx'
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · have h1 : ((m : ℝ) + 1) ≤ (m' : ℝ) := by
      have : m + 1 ≤ m' := by omega
      exact_mod_cast this
    linarith [hx.2, hx'.1]
  · have h1 : ((m' : ℝ) + 1) ≤ (m : ℝ) := by
      have : m' + 1 ≤ m := by omega
      exact_mod_cast this
    linarith [hx'.2, hx.1]

/-- The half-open pieces of one peak cell are pairwise disjoint. -/
private lemma piece_disjoint' (H p : ℝ) (hH : 0 < H) (q q' : ℕ × Bool) (hne : q ≠ q') :
    Disjoint
      (Set.Ico (p + (if q.2 then 1 else -1) * (((q.1 : ℝ) + 1 / 2) / H) - 1 / (2 * H))
        (p + (if q.2 then 1 else -1) * (((q.1 : ℝ) + 1 / 2) / H) + 1 / (2 * H)))
      (Set.Ico (p + (if q'.2 then 1 else -1) * (((q'.1 : ℝ) + 1 / 2) / H) - 1 / (2 * H))
        (p + (if q'.2 then 1 else -1) * (((q'.1 : ℝ) + 1 / 2) / H) + 1 / (2 * H))) := by
  obtain ⟨j, b⟩ := q
  obtain ⟨j', b'⟩ := q'
  rw [Set.disjoint_left]
  intro x hx hx'
  simp only [Set.mem_Ico] at hx hx'
  have ep : ∀ (i : ℕ), p + 1 * (((i : ℝ) + 1 / 2) / H) - 1 / (2 * H) = p + (i : ℝ) / H := by
    intro i
    field_simp
    ring
  have eq : ∀ (i : ℕ), p + 1 * (((i : ℝ) + 1 / 2) / H) + 1 / (2 * H) = p + ((i : ℝ) + 1) / H := by
    intro i
    field_simp
    ring
  have ep' : ∀ (i : ℕ), p + -1 * (((i : ℝ) + 1 / 2) / H) - 1 / (2 * H) = p - ((i : ℝ) + 1) / H := by
    intro i
    field_simp
    ring
  have eq' : ∀ (i : ℕ), p + -1 * (((i : ℝ) + 1 / 2) / H) + 1 / (2 * H) = p - (i : ℝ) / H := by
    intro i
    field_simp
    ring
  rcases b with _ | _ <;> rcases b' with _ | _ <;>
    simp only [Bool.false_eq_true, if_true, ite_false, reduceIte] at hx hx'
  · -- both left of the peak
    rw [eq' j, ep' j] at hx
    rw [eq' j', ep' j'] at hx'
    have hjj : j ≠ j' := by intro h; exact hne (by rw [h])
    rcases lt_or_gt_of_ne hjj with hlt | hlt
    · have hle : ((j : ℝ) + 1) / H ≤ (j' : ℝ) / H := by
        have h1 : ((j : ℝ) + 1) ≤ (j' : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
        exact div_le_div_of_nonneg_right h1 hH.le
      linarith
    · have hle : ((j' : ℝ) + 1) / H ≤ (j : ℝ) / H := by
        have h1 : ((j' : ℝ) + 1) ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
        exact div_le_div_of_nonneg_right h1 hH.le
      linarith
  · -- left then right
    rw [eq' j, ep' j] at hx
    rw [eq j', ep j'] at hx'
    have h1 : (0:ℝ) ≤ (j' : ℝ) / H := by positivity
    have h2 : (0:ℝ) ≤ (j : ℝ) / H := by positivity
    linarith
  · -- right then left
    rw [eq j, ep j] at hx
    rw [eq' j', ep' j'] at hx'
    have h1 : (0:ℝ) ≤ (j : ℝ) / H := by positivity
    have h2 : (0:ℝ) ≤ (j' : ℝ) / H := by positivity
    linarith
  · -- both right of the peak
    rw [eq j, ep j] at hx
    rw [eq j', ep j'] at hx'
    have hjj : j ≠ j' := by intro h; exact hne (by rw [h])
    rcases lt_or_gt_of_ne hjj with hlt | hlt
    · have hle : ((j : ℝ) + 1) / H ≤ (j' : ℝ) / H := by
        have h1 : ((j : ℝ) + 1) ≤ (j' : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
        exact div_le_div_of_nonneg_right h1 hH.le
      linarith
    · have hle : ((j' : ℝ) + 1) / H ≤ (j : ℝ) / H := by
        have h1 : ((j' : ℝ) + 1) ≤ (j : ℝ) := by exact_mod_cast Nat.succ_le_of_lt hlt
        exact div_le_div_of_nonneg_right h1 hH.le
      linarith

/-- The pieces to the right of the peak tile `[p, p + N/H)`. -/
private lemma right_cover' (H p : ℝ) (hH : 0 < H) (Nc : ℕ) :
    ∀ x ∈ Set.Ico p (p + (Nc : ℝ) / H),
      ∃ j ∈ Finset.range Nc,
        x ∈ Set.Ico (p + 1 * (((j : ℝ) + 1 / 2) / H) - 1 / (2 * H))
          (p + 1 * (((j : ℝ) + 1 / 2) / H) + 1 / (2 * H)) := by
  intro x hx
  rw [Set.mem_Ico] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hnn : (0:ℝ) ≤ H * (x - p) := by nlinarith
  have hlt : H * (x - p) < (Nc : ℝ) := by
    have h1 : x - p < (Nc : ℝ) / H := by linarith
    have h2 := mul_lt_mul_of_pos_left h1 hH
    rwa [mul_div_cancel₀ _ hH.ne'] at h2
  refine ⟨⌊H * (x - p)⌋₊, ?_, ?_⟩
  · rw [Finset.mem_range]
    exact (Nat.floor_lt hnn).mpr hlt
  · rw [Set.mem_Ico]
    have hle := Nat.floor_le hnn
    have hlt2 := Nat.lt_floor_add_one (H * (x - p))
    have e1 : p + 1 * ((((⌊H * (x - p)⌋₊ : ℕ) : ℝ) + 1 / 2) / H) - 1 / (2 * H) =
        p + ((⌊H * (x - p)⌋₊ : ℕ) : ℝ) / H := by
      field_simp
      ring
    have e2 : p + 1 * ((((⌊H * (x - p)⌋₊ : ℕ) : ℝ) + 1 / 2) / H) + 1 / (2 * H) =
        p + (((⌊H * (x - p)⌋₊ : ℕ) : ℝ) + 1) / H := by
      field_simp
      ring
    rw [e1, e2]
    constructor
    · have key : ((⌊H * (x - p)⌋₊ : ℕ) : ℝ) / H ≤ x - p := by
        rw [div_le_iff₀ hH]; linarith
      linarith
    · have key : x - p < (((⌊H * (x - p)⌋₊ : ℕ) : ℝ) + 1) / H := by
        rw [lt_div_iff₀ hH]; linarith
      linarith

/-- The pieces to the left of the peak tile `(p - N/H, p)`. -/
private lemma left_cover' (H p : ℝ) (hH : 0 < H) (Nc : ℕ) :
    ∀ x ∈ Set.Ico (p - (Nc : ℝ) / H) p, x ≠ p →
      ∃ j ∈ Finset.range Nc,
        x ∈ Set.Ico (p + -1 * (((j : ℝ) + 1 / 2) / H) - 1 / (2 * H))
          (p + -1 * (((j : ℝ) + 1 / 2) / H) + 1 / (2 * H)) := by
  intro x hx hne
  rw [Set.mem_Ico] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hpos : (0:ℝ) < H * (p - x) := by nlinarith
  have hcle := Nat.le_ceil (H * (p - x))
  have hclt := Nat.ceil_lt_add_one hpos.le
  have hceilpos : 0 < ⌈H * (p - x)⌉₊ := Nat.ceil_pos.mpr hpos
  have hleNc : H * (p - x) ≤ (Nc : ℝ) := by
    have h1 : p - x ≤ (Nc : ℝ) / H := by linarith
    have h2 := mul_le_mul_of_nonneg_left h1 hH.le
    rwa [mul_div_cancel₀ _ hH.ne'] at h2
  set m := ⌈H * (p - x)⌉₊ with hm
  have hm1 : 1 ≤ m := hceilpos
  have hmcast : (((m - 1 : ℕ)) : ℝ) = (m : ℝ) - 1 := by push_cast [hm1]; ring
  have hjNc : m - 1 < Nc := by
    have h1 : ((m - 1 : ℕ) : ℝ) < (Nc : ℝ) := by rw [hmcast]; linarith
    exact_mod_cast h1
  refine ⟨m - 1, by rw [Finset.mem_range]; exact hjNc, ?_⟩
  · rw [Set.mem_Ico]
    have e1 : p + -1 * (((((m - 1 : ℕ)) : ℝ) + 1 / 2) / H) - 1 / (2 * H) = p - (m : ℝ) / H := by
      rw [hmcast]; field_simp; ring
    have e2 : p + -1 * (((((m - 1 : ℕ)) : ℝ) + 1 / 2) / H) + 1 / (2 * H) =
        p - (((m - 1 : ℕ)) : ℝ) / H := by
      field_simp
      ring
    rw [e1, e2]
    constructor
    · have key : p - x ≤ (m : ℝ) / H := by
        rw [le_div_iff₀ hH]; linarith
      linarith
    · have key : (((m - 1 : ℕ)) : ℝ) / H < p - x := by
        rw [div_lt_iff₀ hH, hmcast]
        linarith
      linarith

/-- A piece sits inside the interval of radius `1 / H` about its centre. -/
private lemma piece_subset' (H p : ℝ) (hH : 0 < H) (q : ℕ × Bool) :
    Set.Ico (p + (if q.2 then 1 else -1) * (((q.1 : ℝ) + 1 / 2) / H) - 1 / (2 * H))
        (p + (if q.2 then 1 else -1) * (((q.1 : ℝ) + 1 / 2) / H) + 1 / (2 * H)) ⊆
      Set.Ioo (p + (if q.2 then 1 else -1) * (((q.1 : ℝ) + 1 / 2) / H) - 1 / H)
        (p + (if q.2 then 1 else -1) * (((q.1 : ℝ) + 1 / 2) / H) + 1 / H) := by
  intro x hx
  rw [Set.mem_Ico] at hx
  rw [Set.mem_Ioo]
  have hc : 1 / (2 * H) < 1 / H := by
    have : 0 < 1 / H := by positivity
    have h2 : 1 / (2 * H) = (1 / H) / 2 := by field_simp
    rw [h2]; linarith
  constructor <;> linarith [hx.1, hx.2]

/-- The annulus weight dominates the reciprocal square bound. -/
private lemma weight_max' {H d : ℝ} (hH : 0 < H) (hd : 0 < d) {j : ℕ} (hj1 : 1 ≤ j)
    (hj : (j : ℝ) ≤ d * H) : (1 / 4) * d⁻¹ ^ 2 ≤ H^2 / ((j : ℕ) : ℝ)^2 := by
  have hj0 : (0:ℝ) < (j : ℝ) := by exact_mod_cast (by omega : 0 < j)
  have hconv : (1 / 4) * d⁻¹ ^ 2 = (1:ℝ) / (4 * d^2) := by
    have hd0 : d ≠ 0 := ne_of_gt hd
    field_simp
  rw [hconv]
  have h1 : (4 * d^2) ≠ 0 := by positivity
  have h2 : ((j : ℝ)^2) ≠ 0 := by positivity
  field_simp
  nlinarith [hj, hd, hH, hj0]

/-- The squared kernel is measurable as a function of the integration variable. -/
private lemma measurable_kernel' (H ξ : ℝ) :
    Measurable fun α : ℝ => kernel H (2 * (α - ξ)) := by
  have hfract : Measurable fun α : ℝ => Int.fract (2 * (α - ξ)) :=
    measurable_fract.comp (by fun_prop)
  have habs : Measurable fun α : ℝ => |2 * (α - ξ) - (round (2 * (α - ξ)) : ℤ)| := by
    have heq : (fun α : ℝ => |2 * (α - ξ) - (round (2 * (α - ξ)) : ℤ)|) =
        fun α : ℝ => min (Int.fract (2 * (α - ξ))) (1 - Int.fract (2 * (α - ξ))) := by
      funext α
      exact abs_sub_round_eq_min _
    rw [heq]
    exact hfract.min (measurable_const.sub hfract)
  have hset : MeasurableSet {α : ℝ | 2 * (α - ξ) = (round (2 * (α - ξ)) : ℤ)} := by
    have hh : {α : ℝ | 2 * (α - ξ) = (round (2 * (α - ξ)) : ℤ)} =
        {α : ℝ | |2 * (α - ξ) - (round (2 * (α - ξ)) : ℤ)| = 0} := by
      ext α
      simp [abs_eq_zero, sub_eq_zero]
    rw [hh]
    exact habs (measurableSet_singleton 0)
  unfold kernel
  exact Measurable.ite hset measurable_const (measurable_const.min habs.inv)

/-- The period has finite volume. -/
private lemma volume_period_ne_top' (H : ℝ) : volume (period H) ≠ ⊤ := by
  rw [show period H = Set.Icc (2 / Real.sqrt H) (1 + 2 / Real.sqrt H) from rfl,
    Real.volume_Icc]
  exact ENNReal.ofReal_ne_top

/-- The squared second sum is integrable on the period. -/
private lemma integrable_second' (Y H : ℝ) :
    IntegrableOn (fun α : ℝ => ‖secondSum Y α‖ ^ 2) (period H) volume := by
  have hc : Continuous (fun α : ℝ => ‖secondSum Y α‖ ^ 2) := by
    unfold secondSum phase
    fun_prop
  exact hc.integrableOn_Icc

/-- The squared kernel mass integrand is integrable on the period. -/
private lemma integrable_kernelMass' (Y H ξ : ℝ) (hH : 0 ≤ H) :
    IntegrableOn (fun α : ℝ => ‖secondSum Y α‖ ^ 2 * kernel H (2 * (α - ξ)) ^ 2)
      (period H) volume := by
  have hmeas : AEStronglyMeasurable
      (fun α : ℝ => ‖secondSum Y α‖ ^ 2 * kernel H (2 * (α - ξ)) ^ 2)
      (volume.restrict (period H)) := by
    have h1 : Measurable fun α : ℝ => ‖secondSum Y α‖ ^ 2 := by
      have hc : Continuous (fun α : ℝ => ‖secondSum Y α‖ ^ 2) := by
        unfold secondSum phase
        fun_prop
      exact hc.measurable
    exact (h1.mul ((measurable_kernel' H ξ).pow_const 2)).aestronglyMeasurable
  refine IntegrableOn.of_bound (lt_top_iff_ne_top.mpr (volume_period_ne_top' H)) hmeas
    ((∑ k ∈ Finset.Icc 1 ⌊Y⌋₊, ArithmeticFunction.vonMangoldt (k : ℕ)) ^ 2 * H ^ 2) ?_
  filter_upwards with α
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have h1 : ‖secondSum Y α‖ ^ 2 ≤
      (∑ k ∈ Finset.Icc 1 ⌊Y⌋₊, ArithmeticFunction.vonMangoldt (k : ℕ)) ^ 2 := by
    have h0 : (0:ℝ) ≤ ∑ k ∈ Finset.Icc 1 ⌊Y⌋₊, ArithmeticFunction.vonMangoldt (k : ℕ) :=
      Finset.sum_nonneg (fun _ _ => ArithmeticFunction.vonMangoldt_nonneg)
    nlinarith [secondSum_norm_le' Y α, norm_nonneg (secondSum Y α), h0]
  have h2 : kernel H (2 * (α - ξ)) ^ 2 ≤ H ^ 2 := kernel_sq_le_cap' hH _
  nlinarith [sq_nonneg (∑ k ∈ Finset.Icc 1 ⌊Y⌋₊, ArithmeticFunction.vonMangoldt (k : ℕ)), h1, h2]

/-- On a piece of the peak cell, the squared kernel is bounded by the piece weight. -/
private lemma weight_on_piece' (H ξ p : ℝ) (m : ℤ) (hp : p = ξ + (m : ℝ) / 2) (hH : 1 ≤ H)
    {α : ℝ} (hα : α ∈ Set.Ico (p - 1 / 4) (p + 1 / 4)) (j : ℕ) (σ : Bool)
    (hx : α ∈ Set.Ico (p + (if σ then 1 else -1) * (((j : ℝ) + 1 / 2) / H) - 1 / (2 * H))
        (p + (if σ then 1 else -1) * (((j : ℝ) + 1 / 2) / H) + 1 / (2 * H))) :
    kernel H (2 * (α - ξ)) ^ 2 ≤ H ^ 2 / ((max 1 j : ℕ) : ℝ) ^ 2 := by
  have hH0 : (0:ℝ) < H := by linarith
  have hcell : α ∈ Set.Ico (ξ + (m : ℝ) / 2 - 1 / 4) (ξ + (m : ℝ) / 2 + 1 / 4) := by
    rw [← hp]; exact hα
  have hround : round (2 * (α - ξ)) = m := round_eq_of_mem_cell' hcell
  rw [Set.mem_Ico] at hx
  obtain ⟨hx1, hx2⟩ := hx
  have hright : ∀ (i : ℕ), p + 1 * (((i : ℝ) + 1 / 2) / H) - 1 / (2 * H) = p + (i : ℝ) / H := by
    intro i; field_simp; ring
  have hright' : ∀ (i : ℕ), p + 1 * (((i : ℝ) + 1 / 2) / H) + 1 / (2 * H) =
      p + ((i : ℝ) + 1) / H := by
    intro i; field_simp; ring
  have hleft : ∀ (i : ℕ), p + -1 * (((i : ℝ) + 1 / 2) / H) - 1 / (2 * H) =
      p - ((i : ℝ) + 1) / H := by
    intro i; field_simp; ring
  have hleft' : ∀ (i : ℕ), p + -1 * (((i : ℝ) + 1 / 2) / H) + 1 / (2 * H) = p - (i : ℝ) / H := by
    intro i; field_simp; ring
  rcases Nat.eq_zero_or_pos j with hj | hj
  · subst hj
    have hb := kernel_sq_le_cap' (le_of_lt hH0) (2 * (α - ξ))
    have hone : ((max 1 0 : ℕ) : ℝ) ^ 2 = 1 := by norm_num
    rw [hone, div_one]
    exact hb
  · have main : α ≠ p ∧ (j : ℝ) ≤ |α - p| * H := by
      rcases σ with _ | _
      · have hif : (if (false = true) then (1:ℝ) else -1) = -1 := by simp
        rw [hif] at hx1 hx2
        have h1 : p - ((j : ℝ) + 1) / H ≤ α := by rw [← hleft j]; exact hx1
        have h2 : α < p - (j : ℝ) / H := by rw [← hleft' j]; exact hx2
        constructor
        · intro hcontra
          have hjp : (0:ℝ) < (j : ℝ) / H := by positivity
          rw [hcontra] at h2
          linarith
        · have h2' : (j : ℝ) / H < p - α := by linarith
          have h4 : (j : ℝ) / H * H < (p - α) * H :=
            mul_lt_mul_of_pos_right h2' hH0
          rw [div_mul_cancel₀ _ hH0.ne'] at h4
          have h5 : p - α ≤ |α - p| := by rw [abs_sub_comm]; exact le_abs_self _
          nlinarith
      · have hif : (if (true = true) then (1:ℝ) else -1) = 1 := by simp
        rw [hif] at hx1 hx2
        have h1 : p + (j : ℝ) / H ≤ α := by rw [← hright j]; exact hx1
        have h2 : α < p + ((j : ℝ) + 1) / H := by rw [← hright' j]; exact hx2
        constructor
        · intro hcontra
          have hjp : (0:ℝ) < (j : ℝ) / H := by positivity
          rw [hcontra] at h1
          linarith
        · have h2' : (j : ℝ) / H ≤ α - p := by linarith
          have h4 : (j : ℝ) / H * H ≤ (α - p) * H :=
            mul_le_mul_of_nonneg_right h2' hH0.le
          rw [div_mul_cancel₀ _ hH0.ne'] at h4
          have h5 : α - p ≤ |α - p| := le_abs_self _
          nlinarith
    obtain ⟨hne, hdist⟩ := main
    have hxne : 2 * (α - ξ) ≠ (round (2 * (α - ξ)) : ℤ) := by
      rw [hround]
      intro hcontra
      apply hne
      rw [hp]
      push_cast at hcontra
      linarith
    have hb := kernel_sq_le_inv' (le_of_lt hH0) hxne
    have hdiff : 2 * (α - ξ) - (round (2 * (α - ξ)) : ℤ) = 2 * (α - p) := by
      rw [hround, hp]; push_cast; ring
    rw [hdiff] at hb
    have hdpos : (0:ℝ) < |α - p| := abs_pos.mpr (sub_ne_zero.mpr hne)
    have hdne : |α - p| ≠ 0 := ne_of_gt hdpos
    have hhalf : |2 * (α - p)|⁻¹ ^ 2 = (1 / 4) * |α - p|⁻¹ ^ 2 := by
      have h2 : |2 * (α - p)| = 2 * |α - p| := by
        rw [abs_mul]; norm_num
      rw [h2, mul_inv]
      field_simp
      ring
    rw [hhalf] at hb
    rw [Nat.max_eq_right hj]
    exact le_trans hb (weight_max' hH0 hdpos hj hdist)


/-- The minor domain sits inside the period. -/
private lemma minorDomain_subset_period (N Y H B : ℝ) : minorDomain N Y H B ⊆ period H :=
  Set.sdiff_subset

/-- One peak cell contributes at most a constant times `H ^ 2 * V`. -/
private lemma cell_bound' (N Y H B V ξ : ℝ) (m : ℤ) (hH : 1 ≤ H) (hV : 0 ≤ V)
    (hloc : ∀ c : ℝ, localMass N Y H B c ≤ V) :
    ∫ α in (minorDomain N Y H B ∩
        Set.Ico (ξ + (m : ℝ) / 2 - 1 / 4) (ξ + (m : ℝ) / 2 + 1 / 4)),
        ‖secondSum Y α‖ ^ 2 * kernel H (2 * (α - ξ)) ^ 2 ≤ 6 * H ^ 2 * V := by
  have hH0 : (0:ℝ) < H := by linarith
  set p : ℝ := ξ + (m : ℝ) / 2 with hp
  set Nc : ℕ := ⌈H⌉₊ + 1 with hNc
  set S : ℕ × Bool → Set ℝ := fun q =>
    Set.Ico (p + (if q.2 then 1 else -1) * (((q.1 : ℝ) + 1 / 2) / H) - 1 / (2 * H))
      (p + (if q.2 then 1 else -1) * (((q.1 : ℝ) + 1 / 2) / H) + 1 / (2 * H)) with hS
  rw [show Set.Ico (ξ + (m : ℝ) / 2 - 1 / 4) (ξ + (m : ℝ) / 2 + 1 / 4)
      = Set.Ico (p - 1 / 4) (p + 1 / 4) from by rw [hp]]
  have hquarter : H / 4 < (Nc : ℝ) := by
    have hNcH : H ≤ (Nc : ℝ) := by
      rw [hNc]; push_cast
      linarith [Nat.le_ceil H]
    linarith
  have hDm : MeasurableSet (minorDomain N Y H B) :=
    measurableSet_Icc.diff (measurableSet_majorSet' N Y B)
  set t : Finset (ℕ × Bool) := Finset.range Nc ×ˢ Finset.univ with ht
  have hcover : minorDomain N Y H B ∩ Set.Ico (p - 1 / 4) (p + 1 / 4)
      ⊆ ⋃ q ∈ t, (minorDomain N Y H B ∩ Set.Ico (p - 1 / 4) (p + 1 / 4) ∩ S q) := by
    intro α hα
    obtain ⟨hαD, hαc⟩ := hα
    rw [Set.mem_Ico] at hαc
    obtain ⟨hα1, hα2⟩ := hαc
    have hq1 : (1:ℝ) / 4 < (Nc : ℝ) / H := by
      rw [lt_div_iff₀ hH0]
      linarith
    rcases le_or_gt p α with hle | hlt
    · obtain ⟨j, hjt, hjs⟩ := right_cover' H p hH0 Nc α ⟨hle, by linarith⟩
      refine Set.mem_iUnion.mpr ⟨(j, true), Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · rw [ht, Finset.mem_product]; exact ⟨hjt, Finset.mem_univ _⟩
      · exact ⟨⟨hαD, hα1, hα2⟩, by simpa [hS] using hjs⟩
    · obtain ⟨j, hjt, hjs⟩ := left_cover' H p hH0 Nc α ⟨by linarith, hlt⟩
        (ne_of_lt hlt)
      refine Set.mem_iUnion.mpr ⟨(j, false), Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
      · rw [ht, Finset.mem_product]; exact ⟨hjt, Finset.mem_univ _⟩
      · exact ⟨⟨hαD, hα1, hα2⟩, by simpa [hS] using hjs⟩
  have hdisj : Set.Pairwise (↑t)
      (fun q q' => Disjoint (minorDomain N Y H B ∩ Set.Ico (p - 1 / 4) (p + 1 / 4) ∩ S q)
        (minorDomain N Y H B ∩ Set.Ico (p - 1 / 4) (p + 1 / 4) ∩ S q')) := by
    intro q _ q' _ hne
    have h1 : Disjoint (S q) (S q') := by
      simpa only [hS] using piece_disjoint' H p hH0 q q' hne
    exact h1.mono Set.inter_subset_right Set.inter_subset_right
  have hInt : ∀ q ∈ t,
      IntegrableOn (fun α : ℝ => ‖secondSum Y α‖ ^ 2 * kernel H (2 * (α - ξ)) ^ 2)
        (minorDomain N Y H B ∩ Set.Ico (p - 1 / 4) (p + 1 / 4) ∩ S q) volume := by
    intro q _
    refine (integrable_kernelMass' Y H ξ hH0.le).mono_set ?_
    intro x hx
    exact minorDomain_subset_period N Y H B hx.1.1
  have hmeas : ∀ q ∈ t,
      MeasurableSet (minorDomain N Y H B ∩ Set.Ico (p - 1 / 4) (p + 1 / 4) ∩ S q) := by
    intro q _
    have hSq : MeasurableSet (S q) := by
      simp only [hS]
      exact measurableSet_Ico
    exact (hDm.inter (measurableSet_Ico (a := p - 1 / 4) (b := p + 1 / 4))).inter hSq
  have hunion : (⋃ q ∈ t, (minorDomain N Y H B ∩ Set.Ico (p - 1 / 4) (p + 1 / 4) ∩ S q))
      = minorDomain N Y H B ∩ Set.Ico (p - 1 / 4) (p + 1 / 4) := by
    refine Set.Subset.antisymm ?_ hcover
    refine Set.iUnion_subset fun q => Set.iUnion_subset fun _ => ?_
    exact Set.inter_subset_left
  have hpart := integral_biUnion_finset (μ := volume)
    (f := fun α : ℝ => ‖secondSum Y α‖ ^ 2 * kernel H (2 * (α - ξ)) ^ 2)
    t (s := fun q => minorDomain N Y H B ∩ Set.Ico (p - 1 / 4) (p + 1 / 4) ∩ S q)
    hmeas hdisj hInt
  rw [hunion] at hpart
  have hterm : ∀ q ∈ t,
      ∫ α in (minorDomain N Y H B ∩ Set.Ico (p - 1 / 4) (p + 1 / 4) ∩ S q),
        ‖secondSum Y α‖ ^ 2 * kernel H (2 * (α - ξ)) ^ 2 ≤
        H ^ 2 / ((max 1 q.1 : ℕ) : ℝ) ^ 2 * V := by
    intro q hq
    have hmass : ∫ α in (minorDomain N Y H B ∩ Set.Ico (p - 1 / 4) (p + 1 / 4) ∩ S q),
        ‖secondSum Y α‖ ^ 2 ≤ V := by
      have hsub : (minorDomain N Y H B ∩ Set.Ico (p - 1 / 4) (p + 1 / 4) ∩ S q)
          ⊆ minorDomain N Y H B ∩
            Set.Ioo (p + (if q.2 then 1 else -1) * (((q.1 : ℝ) + 1 / 2) / H) - 1 / H)
              (p + (if q.2 then 1 else -1) * (((q.1 : ℝ) + 1 / 2) / H) + 1 / H) := by
        intro x hx
        exact ⟨hx.1.1, piece_subset' H p hH0 q (by simpa only [hS] using hx.2)⟩
      have hmono := setIntegral_mono_set (μ := volume)
        (f := fun α : ℝ => ‖secondSum Y α‖ ^ 2)
        (s := minorDomain N Y H B ∩ Set.Ico (p - 1 / 4) (p + 1 / 4) ∩ S q)
        (t := minorDomain N Y H B ∩
            Set.Ioo (p + (if q.2 then 1 else -1) * (((q.1 : ℝ) + 1 / 2) / H) - 1 / H)
              (p + (if q.2 then 1 else -1) * (((q.1 : ℝ) + 1 / 2) / H) + 1 / H))
        ((integrable_second' Y H).mono_set (by
          intro x hx; exact minorDomain_subset_period N Y H B hx.1))
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)
        (Filter.Eventually.of_forall fun x hx => hsub hx)
      exact le_trans hmono (hloc _)
    have hw : ∫ α in (minorDomain N Y H B ∩ Set.Ico (p - 1 / 4) (p + 1 / 4) ∩ S q),
        ‖secondSum Y α‖ ^ 2 * kernel H (2 * (α - ξ)) ^ 2 ≤
        (H ^ 2 / ((max 1 q.1 : ℕ) : ℝ) ^ 2) *
          ∫ α in (minorDomain N Y H B ∩ Set.Ico (p - 1 / 4) (p + 1 / 4) ∩ S q),
            ‖secondSum Y α‖ ^ 2 := by
      rw [← integral_const_mul]
      refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun _ =>
        mul_nonneg (sq_nonneg _) (sq_nonneg _)) ?_ ?_
      · refine ((integrable_second' Y H).mono_set (by
          intro x hx; exact minorDomain_subset_period N Y H B hx.1.1)).const_mul _
      · filter_upwards [ae_restrict_mem (hmeas q hq)] with x hx
        have hb := weight_on_piece' H ξ p m hp hH hx.1.2 q.1 q.2
          (by simpa only [hS] using hx.2)
        have hf0 : (0:ℝ) ≤ ‖secondSum Y x‖ ^ 2 := sq_nonneg _
        nlinarith [hb, hf0]
    refine le_trans hw ?_
    exact mul_le_mul_of_nonneg_left hmass (by positivity)
  calc ∫ α in minorDomain N Y H B ∩ Set.Ico (p - 1 / 4) (p + 1 / 4),
        ‖secondSum Y α‖ ^ 2 * kernel H (2 * (α - ξ)) ^ 2
      = ∑ q ∈ t, ∫ α in (minorDomain N Y H B ∩ Set.Ico (p - 1 / 4) (p + 1 / 4) ∩ S q),
          ‖secondSum Y α‖ ^ 2 * kernel H (2 * (α - ξ)) ^ 2 := hpart
    _ ≤ ∑ q ∈ t, H ^ 2 / ((max 1 q.1 : ℕ) : ℝ) ^ 2 * V := Finset.sum_le_sum hterm
    _ = H ^ 2 * V * ∑ q ∈ t, (1 : ℝ) / ((max 1 q.1 : ℕ) : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun q _ => ?_
        field_simp
    _ ≤ H ^ 2 * V * 6 := by
        have h6 : ∑ q ∈ t, (1 : ℝ) / ((max 1 q.1 : ℕ) : ℝ) ^ 2 ≤ 6 := by
          rw [ht, Finset.sum_product]
          have hb : ∀ j : ℕ,
              (∑ _b ∈ (Finset.univ : Finset Bool), (1 : ℝ) / ((max 1 j : ℕ) : ℝ) ^ 2) =
              2 * (1 / ((max 1 j : ℕ) : ℝ) ^ 2) := by
            intro j
            rw [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
            norm_num
          rw [Finset.sum_congr rfl fun j _ => hb j, ← Finset.mul_sum]
          linarith [sum_inv_sq_le' Nc]
        have hHV : (0:ℝ) ≤ H ^ 2 * V := by positivity
        nlinarith
    _ = 6 * H ^ 2 * V := by ring

/-- LEAF. Page 44 between displays 3 and 5, with the covering argument
also used in PP1992 page 359 display 5. Local mass in intervals of radius
1/H bounds the squared kernel integral by a constant times H squared.
This is a covering lemma. It has no zero density or coefficient estimate. -/
theorem kernel_from_local :
    ∃ D : ℝ, 0 < D ∧ ∀ N Y H B V : ℝ, 1 ≤ H → 0 ≤ V →
      (∀ ξ : ℝ, localMass N Y H B ξ ≤ V) →
      ∀ ξ : ℝ, kernelMass N Y H B ξ ≤ D * H ^ 2 * V := by
  refine ⟨25, by norm_num, ?_⟩
  intro N Y H B V hH hV hloc ξ
  have hH0 : (0:ℝ) < H := by linarith
  rw [kernelMass]
  set lo : ℝ := 2 / Real.sqrt H with hlo
  set hi : ℝ := 1 + 2 / Real.sqrt H with hhi
  set mL : ℤ := ⌊2 * (lo - ξ)⌋ with hmL
  set mU : ℤ := ⌈2 * (hi - ξ)⌉ with hmU
  set s : Finset ℤ := Finset.Icc mL mU with hs
  have hcover : minorDomain N Y H B ⊆ ⋃ m ∈ s,
      (minorDomain N Y H B ∩ Set.Ico (ξ + (m : ℝ) / 2 - 1 / 4) (ξ + (m : ℝ) / 2 + 1 / 4)) := by
    intro α hα
    have hper : α ∈ period H := minorDomain_subset_period N Y H B hα
    rw [show period H = Set.Icc lo hi from rfl, Set.mem_Icc] at hper
    refine Set.mem_iUnion.mpr ⟨round (2 * (α - ξ)), Set.mem_iUnion.mpr ⟨?_, ?_⟩⟩
    · rw [hs, Finset.mem_Icc, hmL, hmU]
      exact ⟨floor_le_round' (by linarith [hper.1]), round_le_ceil' (by linarith [hper.2])⟩
    · exact ⟨hα, self_mem_cell' ξ α⟩
  have hdisj : Set.Pairwise (↑s)
      (fun (m m' : ℤ) => Disjoint
        (minorDomain N Y H B ∩ Set.Ico (ξ + (m : ℝ) / 2 - 1 / 4) (ξ + (m : ℝ) / 2 + 1 / 4))
        (minorDomain N Y H B ∩ Set.Ico (ξ + (m' : ℝ) / 2 - 1 / 4) (ξ + (m' : ℝ) / 2 + 1 / 4))) := by
    intro m _ m' _ hne
    exact (cell_disjoint' ξ hne).mono Set.inter_subset_right Set.inter_subset_right
  have hInt : ∀ m ∈ s, IntegrableOn
      (fun α : ℝ => ‖secondSum Y α‖ ^ 2 * kernel H (2 * (α - ξ)) ^ 2)
      (minorDomain N Y H B ∩ Set.Ico (ξ + (m : ℝ) / 2 - 1 / 4) (ξ + (m : ℝ) / 2 + 1 / 4))
      volume := by
    intro m _
    refine (integrable_kernelMass' Y H ξ hH0.le).mono_set ?_
    intro x hx
    exact minorDomain_subset_period N Y H B hx.1
  have hmeas : ∀ m ∈ s, MeasurableSet
      (minorDomain N Y H B ∩ Set.Ico (ξ + (m : ℝ) / 2 - 1 / 4) (ξ + (m : ℝ) / 2 + 1 / 4)) := by
    intro m _
    exact (measurableSet_Icc.diff (measurableSet_majorSet' N Y B)).inter
      (measurableSet_Ico (a := ξ + (m : ℝ) / 2 - 1 / 4) (b := ξ + (m : ℝ) / 2 + 1 / 4))
  have hunion : (⋃ m ∈ s,
      (minorDomain N Y H B ∩ Set.Ico (ξ + (m : ℝ) / 2 - 1 / 4) (ξ + (m : ℝ) / 2 + 1 / 4)))
      = minorDomain N Y H B := by
    refine Set.Subset.antisymm ?_ hcover
    refine Set.iUnion_subset fun m => Set.iUnion_subset fun _ => ?_
    exact Set.inter_subset_left
  have hpart := integral_biUnion_finset (μ := volume)
    (f := fun α : ℝ => ‖secondSum Y α‖ ^ 2 * kernel H (2 * (α - ξ)) ^ 2)
    s (s := fun m => minorDomain N Y H B ∩
      Set.Ico (ξ + (m : ℝ) / 2 - 1 / 4) (ξ + (m : ℝ) / 2 + 1 / 4)) hmeas hdisj hInt
  rw [hunion] at hpart
  have hcard : (s.card : ℝ) ≤ 4 := by
    have h3 : (hi : ℝ) - lo = 1 := by rw [hhi, hlo]; ring
    have h1 : 2 * (lo - ξ) - 1 < (mL : ℝ) := by
      rw [hmL]; linarith [Int.lt_floor_add_one (2 * (lo - ξ))]
    have h2 : (mU : ℝ) < 2 * (hi - ξ) + 1 := by
      rw [hmU]; linarith [Int.ceil_lt_add_one (2 * (hi - ξ))]
    have hb : mU - mL ≤ 3 := by
      have h4 : ((mU - mL : ℤ) : ℝ) < 4 := by push_cast; linarith
      have h5 : (mU - mL : ℤ) < 4 := by exact_mod_cast h4
      omega
    have h6 : (0:ℤ) ≤ mU - mL := by
      have h7 : (mL : ℝ) ≤ 2 * (lo - ξ) := Int.floor_le _
      have h8 : 2 * (lo - ξ) + 2 ≤ (mU : ℝ) := by
        rw [hmU]
        linarith [Int.le_ceil (2 * (hi - ξ))]
      have h10 : (0:ℝ) ≤ (mU : ℝ) - (mL : ℝ) := by linarith
      have h11 : ((mU - mL : ℤ) : ℝ) = (mU : ℝ) - (mL : ℝ) := by push_cast; ring
      have h12 : (0:ℝ) ≤ ((mU - mL : ℤ) : ℝ) := by rw [h11]; exact h10
      exact_mod_cast h12
    have hx : (s.card : ℤ) = mU + 1 - mL := by
      rw [hs]
      exact Int.card_Icc_of_le (a := mL) (b := mU) (by omega)
    have hx2 : (s.card : ℤ) ≤ 4 := by
      rw [hx]; omega
    exact_mod_cast hx2
  calc ∫ α in minorDomain N Y H B, ‖secondSum Y α‖ ^ 2 * kernel H (2 * (α - ξ)) ^ 2
      = ∑ m ∈ s, ∫ α in (minorDomain N Y H B ∩
          Set.Ico (ξ + (m : ℝ) / 2 - 1 / 4) (ξ + (m : ℝ) / 2 + 1 / 4)),
          ‖secondSum Y α‖ ^ 2 * kernel H (2 * (α - ξ)) ^ 2 := hpart
    _ ≤ ∑ _m ∈ s, 6 * H ^ 2 * V :=
        Finset.sum_le_sum fun m _ => cell_bound' N Y H B V ξ m hH hV hloc
    _ = (s.card : ℝ) * (6 * H ^ 2 * V) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ 4 * (6 * H ^ 2 * V) := by
        refine mul_le_mul_of_nonneg_right hcard (by positivity)
    _ ≤ 25 * H ^ 2 * V := by
        have h0 : (0:ℝ) ≤ H ^ 2 * V := by positivity
        nlinarith

/-- LEAF. Page 44 display 3, after Cauchy Schwarz, Parseval and
Brun Titchmarsh. Squaring removes the square root and supremum.
Only the Fourier coefficient to kernel comparison is asserted.
The constant is uniform in the chosen bound K for the kernel integral. -/
theorem coefficient_energy :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ D N₀ : ℝ, 0 < D ∧ ∀ N : ℝ, N₀ ≤ N → ∀ K : ℝ, 0 ≤ K →
      (∀ ξ : ℝ, kernelMass N (localization N η) (windowLength N η) (arcExponent η A) ξ ≤ K) →
      (∑ m ∈ window N η,
        ‖minorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m‖ ^ 2) ^ 2 ≤
        D * (localization N η * Real.log N) ^ 3 * K := by
  exact Decomp489e.coefficient_energy_from_leaves

/-- Page 44 displays 3 and 5 give the exact sealed minor_bound statement.
CONDITIONAL ON local_mass_bound, kernel_from_local and coefficient_energy. -/
theorem minor_bound_from_parts :
    ∃ η₀ : ℝ, 0 < η₀ ∧ ∀ η A : ℝ, 0 < η → η < η₀ → 0 < A →
    ∃ C N₀ : ℝ, ∀ N : ℝ, N₀ ≤ N →
      ∑ m ∈ window N η,
        ‖minorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m‖ ^ 2 ≤
        C * windowLength N η * localization N η ^ 2 / Real.log N ^ A := by
  obtain ⟨e₁, he₁, hlocal⟩ := local_mass_bound
  obtain ⟨e₂, he₂, hcoeff⟩ := coefficient_energy
  obtain ⟨D, hD, hkernel⟩ := kernel_from_local
  refine ⟨min e₁ e₂, lt_min he₁ he₂, ?_⟩
  intro η A hη he hA
  obtain ⟨C, N₁, hC, hmass⟩ := hlocal η A hη (he.trans_le (min_le_left _ _)) hA
  obtain ⟨E, N₂, hE, henergy⟩ := hcoeff η A hη (he.trans_le (min_le_right _ _)) hA
  refine ⟨E * D * C + 1, max 3 (max N₁ N₂), ?_⟩
  intro N hN
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN1 : N₁ ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hN2 : N₂ ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hNp : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hY : 0 < localization N η := Real.rpow_pos_of_pos hNp _
  have hH : 1 ≤ windowLength N η :=
    Real.one_le_rpow (by linarith) (by unfold lengthExponent; positivity)
  have hV : 0 ≤ C * localization N η / Real.log N ^ (2 * A + 3) := by positivity
  have hk := hkernel N (localization N η) (windowLength N η) (arcExponent η A)
    (C * localization N η / Real.log N ^ (2 * A + 3)) hH hV (hmass N hN1)
  have hK : 0 ≤ D * windowLength N η ^ 2 *
      (C * localization N η / Real.log N ^ (2 * A + 3)) := by positivity
  have hb := henergy N hN2 _ hK hk
  have hpow : Real.log N ^ (2 * A + 3) = (Real.log N ^ A) ^ 2 * Real.log N ^ (3 : ℕ) := by
    rw [Real.rpow_add hL, show 2 * A = A * 2 by ring, Real.rpow_mul hL.le]
    norm_num
  have hLp : Real.log N ^ A ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos hL A)
  have hrewrite : E * (localization N η * Real.log N) ^ 3 *
      (D * windowLength N η ^ 2 * (C * localization N η / Real.log N ^ (2 * A + 3))) =
      E * D * C * (windowLength N η * localization N η ^ 2 / Real.log N ^ A) ^ 2 := by
    rw [hpow]
    field_simp [hLp, hL.ne']
    <;> ring
  rw [hrewrite] at hb
  have hscale : 0 ≤ windowLength N η * localization N η ^ 2 / Real.log N ^ A := by positivity
  have hconstant : 0 ≤ E * D * C := by positivity
  have hsq : E * D * C ≤ (E * D * C + 1) ^ 2 := by nlinarith [sq_nonneg (E * D * C)]
  have hsum : 0 ≤ ∑ m ∈ window N η,
      ‖minorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m‖ ^ 2 :=
    Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have hbig := mul_le_mul_of_nonneg_right hsq (sq_nonneg
    (windowLength N η * localization N η ^ 2 / Real.log N ^ A))
  have hfinal : (∑ m ∈ window N η,
      ‖minorCoefficient N (localization N η) (windowLength N η) (arcExponent η A) m‖ ^ 2) ≤
      (E * D * C + 1) * (windowLength N η * localization N η ^ 2 / Real.log N ^ A) := by
    nlinarith [mul_nonneg (by linarith : 0 ≤ E * D * C + 1) hscale]
  convert hfinal using 1 <;> ring

#print axioms kernel_nonneg
#print axioms kernel_le
#print axioms localMass_nonneg
#print axioms kernelMass_nonneg
#print axioms unit_length_instances
#print axioms kernel_pole_instance
#print axioms local_mass_bound
#print axioms kernel_from_local
#print axioms coefficient_energy
#print axioms minor_bound_from_parts
end
end LeanLab.Languasco2004.Decomp413a
