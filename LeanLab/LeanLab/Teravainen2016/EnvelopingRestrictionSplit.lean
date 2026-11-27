/-
P0076, Section 4, Proposition 4.2, pages 13 to 14.
Split of paper_enveloping_restriction_input into the Green Tao large spectrum
level set estimate, cited as a LEAF, and the dyadic summation, proved here.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.MainInputsRestriction

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016

/-- Green Tao, proof of Proposition 4.2: one dyadic scale index serves every positive value. -/
theorem exists_uniform_pow_lt {ι : Type*} (s : Finset ι) (g : ι → ℝ) {T ρ : ℝ}
    (hT : 0 < T) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    ∃ J : ℕ, ∀ i ∈ s, 0 < g i → T * ρ ^ J < g i := by
  induction s using Finset.induction_on with
  | empty => exact ⟨0, by simp⟩
  | insert a s ha ih =>
    obtain ⟨J1, hJ1⟩ := ih
    have h2 : ∃ J2 : ℕ, 0 < g a → T * ρ ^ J2 < g a := by
      by_cases hga : 0 < g a
      · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (div_pos hga hT) hρ1
        exact ⟨n, fun _ => (lt_div_iff₀' hT).mp hn⟩
      · exact ⟨0, fun h => absurd h hga⟩
    obtain ⟨J2, hJ2⟩ := h2
    refine ⟨max J1 J2, ?_⟩
    intro i hi hgi
    rcases mem_insert.mp hi with rfl | hi
    · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hρ0 hρ1.le (le_max_right _ _)) hT.le) (hJ2 hgi)
    · exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left
        (pow_le_pow_of_le_one hρ0 hρ1.le (le_max_left _ _)) hT.le) (hJ1 i hi hgi)

/-- Green Tao, proof of Proposition 4.2: a positive value below the top scale is
bounded by the dyadic shell sum. -/
theorem rpow_le_dyadic_sum {gi T ρ r : ℝ} {J : ℕ} (hr : 0 ≤ r) (hT : 0 ≤ T) (hρ : 0 ≤ ρ)
    (hg0 : 0 < gi) (hgT : gi ≤ T) (hJ : T * ρ ^ J < gi) :
    gi ^ r ≤ ∑ j ∈ range J, if T * ρ ^ (j + 1) < gi then (T * ρ ^ j) ^ r else 0 := by
  have hJ1 : J ≠ 0 := by
    rintro rfl
    simp only [pow_zero, mul_one] at hJ
    linarith
  have hJs : J - 1 + 1 = J := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hJ1)
  have hex : ∃ j, T * ρ ^ (j + 1) < gi := ⟨J - 1, by rwa [hJs]⟩
  have hj0spec : T * ρ ^ (Nat.find hex + 1) < gi := Nat.find_spec hex
  have hj0le : Nat.find hex ≤ J - 1 := Nat.find_min' hex (by rwa [hJs])
  have hupper : gi ≤ T * ρ ^ (Nat.find hex) := by
    rcases Nat.eq_zero_or_pos (Nat.find hex) with h0 | hpos
    · rw [h0, pow_zero, mul_one]; exact hgT
    · have hmin := Nat.find_min hex (show Nat.find hex - 1 < Nat.find hex by omega)
      push_neg at hmin
      rwa [Nat.sub_add_cancel hpos] at hmin
  have hmem : Nat.find hex ∈ range J := mem_range.mpr (by omega)
  have hterm : gi ^ r ≤ if T * ρ ^ (Nat.find hex + 1) < gi then (T * ρ ^ (Nat.find hex)) ^ r
      else 0 := by
    rw [if_pos hj0spec]
    exact Real.rpow_le_rpow hg0.le hupper hr
  refine hterm.trans (single_le_sum
    (f := fun j => if T * ρ ^ (j + 1) < gi then (T * ρ ^ j) ^ r else 0) ?_ hmem)
  intro j _
  split_ifs
  · exact Real.rpow_nonneg (mul_nonneg hT (pow_nonneg hρ j)) r
  · exact le_rfl

/-- Green Tao, proof of Proposition 4.2: the normalized dyadic summation.
A level set bound with exponent q below r gives a uniform r th moment. -/
theorem dyadic_unit_moment {ι : Type*} (s : Finset ι) (g : ι → ℝ) (hg : ∀ i, 0 ≤ g i)
    {K q r : ℝ} (hK : 0 < K) (hq : 0 < q) (hqr : q < r)
    (h : ∀ δ : ℝ, 0 < δ → ((s.filter (fun i => δ < g i)).card : ℝ) ≤ K * δ ^ (-q)) :
    ∑ i ∈ s, g i ^ r ≤ K * ((2 * K) ^ (1 / q)) ^ r * ((2 * K) ^ (1 / q)) ^ (-q) *
      (1 / 2 : ℝ) ^ (-q) * (1 - (1 / 2 : ℝ) ^ r * (1 / 2 : ℝ) ^ (-q))⁻¹ := by
  set T : ℝ := (2 * K) ^ (1 / q) with hTdef
  set ρ : ℝ := 1 / 2 with hρ
  set x : ℝ := ρ ^ r * ρ ^ (-q) with hx
  have hρ0 : 0 < ρ := by norm_num [hρ]
  have hρ1 : ρ < 1 := by norm_num [hρ]
  have hT : 0 < T := Real.rpow_pos_of_pos (by positivity) _
  have hTq : T ^ (-q) = (2 * K)⁻¹ := by
    rw [hTdef, ← Real.rpow_mul (by positivity)]
    rw [show 1 / q * -q = -1 by field_simp]
    exact Real.rpow_neg_one _
  have hr : 0 < r := hq.trans hqr
  have hbound : ∀ i ∈ s, g i ≤ T := by
    intro i hi
    by_contra hlt
    push_neg at hlt
    have hcard := h T hT
    have hmem : i ∈ s.filter (fun j => T < g j) := mem_filter.mpr ⟨hi, hlt⟩
    have h1 : (1 : ℝ) ≤ (s.filter (fun j => T < g j)).card := by
      exact_mod_cast card_pos.mpr ⟨i, hmem⟩
    rw [hTq] at hcard
    have : K * (2 * K)⁻¹ = 1 / 2 := by field_simp
    linarith
  obtain ⟨J, hJ⟩ := exists_uniform_pow_lt s g hT hρ0.le hρ1
  have hstep : ∑ i ∈ s, g i ^ r ≤ ∑ i ∈ s, ∑ j ∈ range J,
      (if T * ρ ^ (j + 1) < g i then (T * ρ ^ j) ^ r else 0) := by
    apply sum_le_sum
    intro i hi
    rcases (hg i).eq_or_lt with h0 | hpos
    · rw [← h0, Real.zero_rpow hr.ne']
      apply sum_nonneg
      intro j _
      split_ifs
      · exact Real.rpow_nonneg (mul_nonneg hT.le (pow_nonneg hρ0.le j)) r
      · exact le_rfl
    · exact rpow_le_dyadic_sum hr.le hT.le hρ0.le hpos (hbound i hi) (hJ i hi hpos)
  rw [sum_comm] at hstep
  have hswap : ∀ j ∈ range J, ∑ i ∈ s,
      (if T * ρ ^ (j + 1) < g i then (T * ρ ^ j) ^ r else 0) =
      ((s.filter (fun i => T * ρ ^ (j + 1) < g i)).card : ℝ) * (T * ρ ^ j) ^ r := by
    intro j _
    rw [← sum_filter, sum_const, nsmul_eq_mul]
  rw [sum_congr rfl hswap] at hstep
  have hterm : ∀ j ∈ range J,
      ((s.filter (fun i => T * ρ ^ (j + 1) < g i)).card : ℝ) * (T * ρ ^ j) ^ r ≤
        (K * T ^ r * T ^ (-q) * ρ ^ (-q)) * x ^ j := by
    intro j _
    have hδ : 0 < T * ρ ^ (j + 1) := by positivity
    have e1 : (ρ ^ (j + 1)) ^ (-q) = ρ ^ (((j : ℝ) + 1) * -q) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0.le]
      push_cast
      ring_nf
    have e2 : (ρ ^ j) ^ r = ρ ^ ((j : ℝ) * r) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hρ0.le]
    have e3 : x ^ j = ρ ^ ((r + -q) * (j : ℝ)) := by
      rw [hx, ← Real.rpow_add hρ0, ← Real.rpow_natCast, ← Real.rpow_mul hρ0.le]
    have key : ρ ^ (((j : ℝ) + 1) * -q) * ρ ^ ((j : ℝ) * r) =
        ρ ^ (-q) * ρ ^ ((r + -q) * (j : ℝ)) := by
      rw [← Real.rpow_add hρ0, ← Real.rpow_add hρ0]
      congr 1
      ring
    calc _ ≤ K * (T * ρ ^ (j + 1)) ^ (-q) * (T * ρ ^ j) ^ r :=
          mul_le_mul_of_nonneg_right (h _ hδ)
            (Real.rpow_nonneg (mul_nonneg hT.le (pow_nonneg hρ0.le j)) r)
      _ = (K * T ^ r * T ^ (-q) * ρ ^ (-q)) * x ^ j := by
          rw [Real.mul_rpow hT.le (pow_nonneg hρ0.le _),
            Real.mul_rpow hT.le (pow_nonneg hρ0.le _), e1, e2, e3]
          linear_combination (K * T ^ r * T ^ (-q)) * key
  have hx0 : 0 < x := by positivity
  have hx1 : x < 1 := by
    rw [hx, ← Real.rpow_add hρ0]
    exact Real.rpow_lt_one hρ0.le hρ1 (by linarith)
  have hC0 : 0 ≤ K * T ^ r * T ^ (-q) * ρ ^ (-q) := by positivity
  calc ∑ i ∈ s, g i ^ r ≤ ∑ j ∈ range J, (K * T ^ r * T ^ (-q) * ρ ^ (-q)) * x ^ j :=
        hstep.trans (sum_le_sum hterm)
    _ = (K * T ^ r * T ^ (-q) * ρ ^ (-q)) * ∑ j ∈ range J, x ^ j := (mul_sum _ _ _).symm
    _ ≤ (K * T ^ r * T ^ (-q) * ρ ^ (-q)) * (1 - x)⁻¹ :=
        mul_le_mul_of_nonneg_left (by
          have hg := geom_sum_Ico_le_of_lt_one (m := 0) (n := J) hx0.le hx1
          rwa [← range_eq_Ico, pow_zero, one_div] at hg) hC0

/-- Green Tao, proof of Proposition 4.2: the dyadic summation with an energy scale E.
A level set bound with exponent q gives the r th moment for every r above q. -/
theorem dyadic_level_moment {ι : Type*} (s : Finset ι) (f : ι → ℝ) (hf : ∀ i, 0 ≤ f i)
    {E K q r : ℝ} (hE : 0 ≤ E) (hK : 0 < K) (hq : 0 < q) (hqr : q < r)
    (h : ∀ δ : ℝ, 0 < δ → ((s.filter (fun i => δ * E < f i)).card : ℝ) ≤ K * δ ^ (-q)) :
    ∑ i ∈ s, f i ^ r ≤ (K * ((2 * K) ^ (1 / q)) ^ r * ((2 * K) ^ (1 / q)) ^ (-q) *
      (1 / 2 : ℝ) ^ (-q) * (1 - (1 / 2 : ℝ) ^ r * (1 / 2 : ℝ) ^ (-q))⁻¹) * E ^ r := by
  have hr : 0 < r := hq.trans hqr
  rcases hE.eq_or_lt with h0 | hEpos
  · subst h0
    set T : ℝ := (2 * K) ^ (1 / q) with hTdef
    have hT : 0 < T := Real.rpow_pos_of_pos (by positivity) _
    have hTq : T ^ (-q) = (2 * K)⁻¹ := by
      rw [hTdef, ← Real.rpow_mul (by positivity)]
      rw [show 1 / q * -q = -1 by field_simp]
      exact Real.rpow_neg_one _
    have hzero : ∀ i ∈ s, f i = 0 := by
      intro i hi
      by_contra hne
      have hpos : 0 < f i := lt_of_le_of_ne (hf i) (Ne.symm hne)
      have hcard := h T hT
      have hmem : i ∈ s.filter (fun j => T * 0 < f j) :=
        mem_filter.mpr ⟨hi, by rw [mul_zero]; exact hpos⟩
      have h1 : (1 : ℝ) ≤ (s.filter (fun j => T * 0 < f j)).card := by
        exact_mod_cast card_pos.mpr ⟨i, hmem⟩
      rw [hTq] at hcard
      have : K * (2 * K)⁻¹ = 1 / 2 := by field_simp
      linarith
    rw [sum_eq_zero (fun i hi => by rw [hzero i hi, Real.zero_rpow hr.ne']),
      Real.zero_rpow hr.ne', mul_zero]
  · have hunit := dyadic_unit_moment s (fun i => f i / E) (fun i => div_nonneg (hf i) hE)
      hK hq hqr (by
        intro δ hδ
        have hset : s.filter (fun i => δ < f i / E) = s.filter (fun i => δ * E < f i) := by
          apply filter_congr
          intro i _
          exact lt_div_iff₀ hEpos
        rw [hset]
        exact h δ hδ)
    have hsplit : ∑ i ∈ s, f i ^ r = (∑ i ∈ s, (f i / E) ^ r) * E ^ r := by
      rw [sum_mul]
      apply sum_congr rfl
      intro i _
      rw [← Real.mul_rpow (div_nonneg (hf i) hE) hE, div_mul_cancel₀ _ hEpos.ne']
    rw [hsplit]
    exact mul_le_mul_of_nonneg_right hunit (Real.rpow_nonneg hE r)

/-- A filtered subset of `range M` has at most `M` elements. This is the elementary
cardinality bound used in the large spectrum estimate. -/
theorem level_set_card_le_M (M : ℕ) (p : ℕ → Prop) [DecidablePred p] :
    ((range M).filter p).card ≤ M := by
  calc
    ((range M).filter p).card ≤ (range M).card := card_filter_le _ _
    _ = M := card_range M

/-- LEAF: Proposition 4.2, pages 13 to 14, the large spectrum level set estimate in the
proof of Green and Tao, Restriction theory of the Selberg sieve, Proposition 4.2,
arXiv math/0405581. Class HARD. For every positive epsilon the frequencies where the
transform of a times the capped weight exceeds delta times the weighted L2 norm of a
number at most K delta to the power minus two minus epsilon, uniformly in all parameters.
Green Tao prove this from Parseval with the pointwise growth bound for small delta and
from the rational Fourier expansion with its decay bound for large delta. It is the
same reconstructed bounded shift adaptation as the target: the cap for the growth
bound and the uncapped majorant for the Fourier expansion. -/
theorem paper_enveloping_level_set_input (A D : ℝ → ℝ)
    (hAD : ∀ ε : ℝ, 0 < ε → 0 < A ε ∧ 0 < D ε) :
    ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, 0 < K ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          EnvelopingFourierBounds w (WW J w) b M A D →
          ∀ a : ℕ → ℂ, ∀ δ : ℝ, 0 < δ →
            (((range M).filter (fun ξ =>
              δ * ((M : ℝ)⁻¹ * ∑ n ∈ range M,
                ‖a n‖ ^ 2 * restrictionBeta w (WW J w) b M n) ^ ((1 : ℝ) / 2) <
              ‖complexFhat M (fun n => a n * (restrictionBeta w (WW J w) b M n : ℂ)) ξ‖)).card
                : ℝ) ≤ K * δ ^ (-(2 + ε)) := by
  sorry

/-- Proposition 4.2, pages 13 to 14, assembled from the level set LEAF and the proved
dyadic summation. CONDITIONAL ON paper_enveloping_level_set_input. -/
theorem paper_enveloping_restriction_input_of_leaves (A D : ℝ → ℝ)
    (hAD : ∀ ε : ℝ, 0 < ε → 0 < A ε ∧ 0 < D ε) :
    ∀ r : ℝ, 2 < r → ∃ C : ℝ, 0 < C ∧
      ∀ J w : ℕ, 5 ≤ J → wBig ≤ w → ∀ b : ℤ,
        0 ≤ b → b < WW J w → Amenable (WW J w) b → ∀ M : ℕ, 1 ≤ M →
          EnvelopingFourierBounds w (WW J w) b M A D →
          Restriction42 M (restrictionBeta w (WW J w) b M) r C := by
  intro r hr
  have hε : 0 < (r - 2) / 2 := by linarith
  obtain ⟨K, hK, H⟩ := paper_enveloping_level_set_input A D hAD ((r - 2) / 2) hε
  have hq : 0 < 2 + (r - 2) / 2 := by linarith
  have hqr : 2 + (r - 2) / 2 < r := by linarith
  have hr0 : 0 < r := by linarith
  set q : ℝ := 2 + (r - 2) / 2 with hqdef
  set Cst : ℝ := K * ((2 * K) ^ (1 / q)) ^ r * ((2 * K) ^ (1 / q)) ^ (-q) *
      (1 / 2 : ℝ) ^ (-q) * (1 - (1 / 2 : ℝ) ^ r * (1 / 2 : ℝ) ^ (-q))⁻¹ with hCst
  have hx1 : (1 / 2 : ℝ) ^ r * (1 / 2 : ℝ) ^ (-q) < 1 := by
    rw [← Real.rpow_add (by norm_num)]
    exact Real.rpow_lt_one (by norm_num) (by norm_num) (by linarith)
  have hCpos : 0 < Cst := by
    have : 0 < (1 - (1 / 2 : ℝ) ^ r * (1 / 2 : ℝ) ^ (-q))⁻¹ := inv_pos.mpr (by linarith)
    positivity
  refine ⟨Cst ^ (1 / r), Real.rpow_pos_of_pos hCpos _, ?_⟩
  intro J w hJ hw b hb hbW hamen M hM hB a
  set E : ℝ := ((M : ℝ)⁻¹ * ∑ n ∈ range M,
      ‖a n‖ ^ 2 * restrictionBeta w (WW J w) b M n) ^ ((1 : ℝ) / 2) with hEdef
  have hE : 0 ≤ E := by
    apply Real.rpow_nonneg
    apply mul_nonneg (by positivity)
    exact sum_nonneg (fun n _ => mul_nonneg (by positivity)
      (restrictionBeta_nonneg w (WW J w) b M n))
  have hmom := dyadic_level_moment (range M)
    (fun ξ => ‖complexFhat M (fun n => a n * (restrictionBeta w (WW J w) b M n : ℂ)) ξ‖)
    (fun _ => norm_nonneg _) hE hK hq hqr (H J w hJ hw b hb hbW hamen M hM hB a)
  have hsum : 0 ≤ ∑ ξ ∈ range M,
      ‖complexFhat M (fun n => a n * (restrictionBeta w (WW J w) b M n : ℂ)) ξ‖ ^ r :=
    sum_nonneg (fun ξ _ => Real.rpow_nonneg (norm_nonneg _) r)
  have hroot := Real.rpow_le_rpow hsum hmom (by positivity : (0 : ℝ) ≤ 1 / r)
  rw [Real.mul_rpow hCpos.le (Real.rpow_nonneg hE r), ← Real.rpow_mul hE,
    mul_one_div_cancel hr0.ne', Real.rpow_one] at hroot
  exact hroot

end LeanLab.Teravainen2016
