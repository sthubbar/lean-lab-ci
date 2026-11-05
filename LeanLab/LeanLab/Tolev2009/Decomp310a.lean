/-
AI wrote this Lean code. Codex task310.
Binary Goldbach is open.
Source: https://doi.org/10.4064/aa-88-1-67-98.
Adapted to https://arxiv.org/abs/0902.2669 page 4 display 12.
All analytic leaves remain OPEN. Assemblies are CONDITIONAL.
-/
import LeanLab.Tolev2009.Decomp286b
import LeanLab.Tolev2009.Decomp310aScalar

open Finset Real

namespace LeanLab.Tolev2009.Decomp310a

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful
open LeanLab.Tolev2009.FinalReduction LeanLab.Tolev2009.Displays14to16
open LeanLab.Tolev2009.Dyadic LeanLab.Tolev2009.Decomp286b

/-- The inner row after removing a m, Tolev 1999 page 86 display 64.
The product truncation and fixed residue are those of the sealed bilinear block. -/
noncomputable def row (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x H H₁ : ℝ)
    (b : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊,
    if x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N then
      b l * ee (α * (m * l : ℕ)) * (L2Bound.weight lam l₃ K (m * l) : ℂ)
    else 0

/-- Removing the first coefficient gives the row form of display 64. -/
theorem bilinear_eq_rows (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (a b : ℕ → ℂ) :
    bilinear lam l₃ K N α x M M₁ H H₁ a b =
      ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, a m * row lam l₃ K N α x H H₁ b m := by
  unfold bilinear row
  apply sum_congr rfl
  intro m hm
  rw [mul_sum]
  apply sum_congr rfl
  intro l hl
  split_ifs <;> ring

/-- The coefficient free majorant in display 64. No minor arc input is used. -/
theorem bilinear_norm_le_rows (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x M M₁ H H₁ : ℝ)
    (a b : ℕ → ℂ) (ha : ∀ m, ‖a m‖ ≤ (tau5 m : ℝ) * Real.log N) :
    ‖bilinear lam l₃ K N α x M M₁ H H₁ a b‖ ≤
      ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
        ((tau5 m : ℝ) * Real.log N) * ‖row lam l₃ K N α x H H₁ b m‖ := by
  rw [bilinear_eq_rows]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro m hm
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_right (ha m) (norm_nonneg _)

/-- The exact discrete Abel identity behind Tolev 1999 page 86 display 66.
It reduces each logarithmic row to constant rows with truncated upper endpoints.
No minor arc assumption or analytic row bound is used. -/
theorem logarithmic_row_by_parts (lam : ℕ → ℝ) (l₃ K N : ℕ) (α x H H₁ : ℝ) (m : ℕ)
    (hHH : ⌊H⌋₊ < ⌊H₁⌋₊) :
    row lam l₃ K N α x H H₁ (fun l : ℕ => (Real.log l : ℂ)) m =
      (Real.log ⌊H₁⌋₊ : ℂ) * row lam l₃ K N α x H H₁ (fun _ => 1) m -
      ∑ l ∈ Ioc ⌊H⌋₊ (⌊H₁⌋₊ - 1),
        ((Real.log (l + 1 : ℕ) : ℂ) - (Real.log l : ℂ)) *
          row lam l₃ K N α x H (l : ℝ) (fun _ => 1) m := by
  let c : ℕ → ℂ := fun l =>
    if ⌊H⌋₊ < l then
      if x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N then
        ee (α * (m * l : ℕ)) * (L2Bound.weight lam l₃ K (m * l) : ℂ)
      else 0
    else 0
  have hG : ∀ t : ℕ, ∑ l ∈ range (t + 1), c l =
      row lam l₃ K N α x H (t : ℝ) (fun _ => 1) m := by
    intro t
    have hs : (range (t + 1)).filter (fun l => ⌊H⌋₊ < l) = Ioc ⌊H⌋₊ t := by
      ext l
      simp only [mem_filter, mem_range, mem_Ioc]
      omega
    simp only [c]
    rw [← sum_filter, hs]
    simp only [row, Nat.floor_natCast, one_mul]
  have hG0 : ∑ l ∈ range (⌊H⌋₊ + 1), c l = 0 := by
    rw [hG]
    simp only [row, Nat.floor_natCast, Ioc_self, sum_empty]
  have hh := sum_Ioc_by_parts (fun l : ℕ => (Real.log l : ℂ)) c hHH
  rw [hG0, smul_zero, sub_zero] at hh
  simp only [smul_eq_mul] at hh
  have hlhs : (∑ l ∈ Ioc ⌊H⌋₊ ⌊H₁⌋₊, (Real.log l : ℂ) * c l) =
      row lam l₃ K N α x H H₁ (fun l : ℕ => (Real.log l : ℂ)) m := by
    unfold row
    apply sum_congr rfl
    intro l hl
    simp only [c, ite_eq_left (mem_Ioc.mp hl).1]
    split_ifs <;> ring
  rw [hlhs] at hh
  simp_rw [hG] at hh
  simpa only [row, Nat.floor_natCast] using hh

/-- The geometric progression step of Tolev 1999 page 86 display 64 and page 72 Lemma 6.
The denominator is kept as the exact complex distance from one.
No torus distance comparison or averaged Diophantine estimate is asserted. -/
theorem progression_phase_bound (β θ : ℝ) (J : ℕ) (hθ : ee θ ≠ 1) :
    ‖∑ j ∈ range J, ee (β + (j : ℝ) * θ)‖ ≤
      min (J : ℝ) (2 / ‖ee θ - 1‖) := by
  have he : ∀ j : ℕ, ee (β + (j : ℝ) * θ) = ee β * ee θ ^ j := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Nat.cast_add, Nat.cast_one, add_mul, one_mul]
      rw [show β + ((j : ℝ) * θ + θ) = (β + (j : ℝ) * θ) + θ by ring, ee_add, ih, pow_succ]
      ring
  apply le_min
  · apply (norm_sum_le _ _).trans_eq
    simp only [norm_ee, sum_const, card_range, nsmul_eq_mul, mul_one]
  · have hs : (∑ j ∈ range J, ee (β + (j : ℝ) * θ)) = ee β * ∑ j ∈ range J, ee θ ^ j := by
      rw [mul_sum]
      exact sum_congr rfl (fun j hj => he j)
    rw [hs, norm_mul, norm_ee, one_mul, geom_sum_eq hθ J, norm_div]
    have hn : ‖ee θ ^ J - 1‖ ≤ 2 := by
      simpa only [norm_pow, norm_ee, one_pow, norm_one, one_add_one_eq_two] using
        norm_sub_le (ee θ ^ J) 1
    exact div_le_div_of_nonneg_right hn (norm_nonneg _)

open LeanLab.HeathBrown1985

/-- The reciprocal divisor moment used in Tolev 1999 page 72 Lemma 8 part iii.
At r equal to twelve it supplies the Cauchy factor in page 86 display 65. -/
theorem divisor_power_reciprocal (r N : ℕ) :
    ∑ n ∈ Icc 1 N, (n.divisors.card : ℝ) ^ r / n ≤ Hn N ^ (2 ^ r) := by
  induction r generalizing N with
  | zero => simp [Hn]
  | succ r ih =>
    have hh := LeanLab.Tolev2009.DivisorMoment.reciprocal_step N r (2 ^ r) (fun M hM => ih M)
    simpa only [pow_succ, Nat.mul_comm] using hh

/-- Expanding the divisor weight gives the exact progression decomposition.
This is the adapted identity before Tolev 1999 display 64. -/
theorem t144_row_eq_progressions (lam : ℕ → ℝ) (l₃ K N m : ℕ) (α x H H₁ : ℝ) :
    row lam l₃ K N α x H H₁ (fun _ => 1) m =
      ∑ k ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃),
        (lam k : ℂ) * LeanLab.Tolev2009.Decomp310aScalar.progression l₃ k N m α x H H₁ := by
  classical
  unfold row LeanLab.Tolev2009.Decomp310aScalar.progression
  simp only [mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro l hl
  simp only [L2Bound.weight, sum_filter, Complex.ofReal_sum, apply_ite,
    Complex.ofReal_zero, one_mul, mul_sum]
  by_cases hc : x < (m * l : ℕ) ∧ (m * l : ℕ) ≤ 2 * x ∧ m * l ≤ N
  · simp only [hc, ite_true, true_and]
    apply sum_congr rfl
    intro k hk
    split_ifs <;> simp_all <;> ring
  · simp only [hc, ite_false, false_and, mul_zero, ite_self, sum_const_zero]


/-- The triangle step in display 64 removes all bounded real weights. -/
theorem t144_row_norm_le_progressions (lam : ℕ → ℝ) (l₃ K N m : ℕ) (α x H H₁ : ℝ)
    (hlam : ∀ k, |lam k| ≤ 1) :
    ‖row lam l₃ K N α x H H₁ (fun _ => 1) m‖ ≤
      ∑ k ∈ (Icc 1 K).filter (fun k => Nat.Coprime k l₃),
        ‖LeanLab.Tolev2009.Decomp310aScalar.progression l₃ k N m α x H H₁‖ := by
  rw [t144_row_eq_progressions]
  apply (norm_sum_le _ _).trans
  apply sum_le_sum
  intro k hk
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  exact (mul_le_mul_of_nonneg_right (hlam k) (norm_nonneg _)).trans_eq (one_mul _)


/-- Every row is bounded by the same scalar phase sum, uniformly in its upper endpoint.
This is the elementary triangle reduction in display 64. -/
theorem t144_row_norm_le_phase (lam : ℕ → ℝ) (l₃ K N m : ℕ) (α x H H₁ : ℝ)
    (hlam : ∀ k, |lam k| ≤ 1) (hm : 1 ≤ m) (hx : 0 < x)
    (hp : ∀ k ∈ Icc 1 K, Nat.Coprime k l₃ →
      ‖LeanLab.Tolev2009.Decomp310aScalar.progression l₃ k N m α x H H₁‖ ≤ LeanLab.Tolev2009.Decomp310aScalar.phaseCap α x (m * k)) :
    ‖row lam l₃ K N α x H H₁ (fun _ => 1) m‖ ≤
      ∑ k ∈ Icc 1 K, LeanLab.Tolev2009.Decomp310aScalar.phaseCap α x (m * k) := by
  apply (t144_row_norm_le_progressions lam l₃ K N m α x H H₁ hlam).trans
  apply (sum_le_sum (fun k hk => hp k (mem_filter.mp hk).1 (mem_filter.mp hk).2)).trans
  exact sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun k hk hnot =>
    LeanLab.Tolev2009.Decomp310aScalar.phaseCap_nonneg α x (m * k) hx.le)


/-- A uniform prefix estimate transfers to the logarithmic row by Abel summation.
This is the norm step in Tolev 1999 page 86 display 66.
Every prefix keeps the original product cutoffs. -/
theorem t144_logarithmic_row_norm_le_prefix (lam : ℕ → ℝ) (l₃ K N m : ℕ)
    (α x H H₁ B : ℝ) (hB : 0 ≤ B) (hHH : ⌊H⌋₊ < ⌊H₁⌋₊)
    (hp : ∀ t : ℕ, ⌊H⌋₊ < t → t ≤ ⌊H₁⌋₊ →
      ‖row lam l₃ K N α x H (t : ℝ) (fun _ => 1) m‖ ≤ B) :
    ‖row lam l₃ K N α x H H₁ (fun l : ℕ => (Real.log l : ℂ)) m‖ ≤
      2 * Real.log ⌊H₁⌋₊ * B := by
  let U := ⌊H₁⌋₊
  let L := ⌊H⌋₊
  have hLU : L < U := hHH
  have hU : 1 ≤ U := by omega
  have htop : ‖row lam l₃ K N α x H H₁ (fun _ => 1) m‖ ≤ B := by
    simpa only [row, Nat.floor_natCast] using hp U hLU le_rfl
  have hd : ∀ l ∈ Ioc L (U - 1),
      0 ≤ Real.log (l + 1 : ℕ) - Real.log l := by
    intro l hl
    have hl0 : 0 < (l : ℝ) := by exact_mod_cast (show 0 < l by have := (mem_Ioc.mp hl).1; omega)
    exact sub_nonneg.mpr (Real.log_le_log hl0 (by exact_mod_cast Nat.le_succ l))
  have hs : (∑ l ∈ Ioc L (U - 1),
      (Real.log (l + 1 : ℕ) - Real.log l)) ≤ Real.log U := by
    have he : Ioc L (U - 1) = Ico (L + 1) U := by
      ext l
      simp only [mem_Ioc, mem_Ico]
      omega
    rw [he, sum_Ico_sub (fun l : ℕ => Real.log l) (show L + 1 ≤ U by omega)]
    exact sub_le_self _ (Real.log_natCast_nonneg _)
  rw [logarithmic_row_by_parts lam l₃ K N α x H H₁ m hHH]
  apply (norm_sub_le _ _).trans
  have hfirst : ‖(Real.log ⌊H₁⌋₊ : ℂ) * row lam l₃ K N α x H H₁ (fun _ => 1) m‖ ≤
      Real.log U * B := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.log_natCast_nonneg _)]
    exact mul_le_mul_of_nonneg_left htop (Real.log_natCast_nonneg _)
  have hsecond : ‖∑ l ∈ Ioc ⌊H⌋₊ (⌊H₁⌋₊ - 1),
        ((Real.log (l + 1 : ℕ) : ℂ) - (Real.log l : ℂ)) *
          row lam l₃ K N α x H (l : ℝ) (fun _ => 1) m‖ ≤ Real.log U * B := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ l ∈ Ioc L (U - 1), (Real.log (l + 1 : ℕ) - Real.log l) * B := by
        apply sum_le_sum
        intro l hl
        rw [norm_mul, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hd l hl)]
        exact mul_le_mul_of_nonneg_left (hp l (mem_Ioc.mp hl).1 (by have := (mem_Ioc.mp hl).2; omega)) (hd l hl)
      _ = (∑ l ∈ Ioc L (U - 1), (Real.log (l + 1 : ℕ) - Real.log l)) * B := by rw [sum_mul]
      _ ≤ Real.log U * B := mul_le_mul_of_nonneg_right hs hB
  nlinarith


/-- LEAF. Tolev 1999 page 86 display 64 and its geometric estimate before 65.
This is one finite progression with no divisor coefficient or minor arc premise.
The resonance and endpoint cases are explicit. -/
theorem t144_progression_bound (l₃ k N m : ℕ) (α x H H₁ : ℝ)
    (hk : 1 ≤ k) (hm : 1 ≤ m) (hcop : Nat.Coprime k l₃) (hx : 0 < x) :
    ‖LeanLab.Tolev2009.Decomp310aScalar.progression l₃ k N m α x H H₁‖ ≤ LeanLab.Tolev2009.Decomp310aScalar.phaseCap α x (m * k) := by
  obtain ⟨β, J, he, hJ⟩ := LeanLab.Tolev2009.Decomp310aScalar.progression_affine l₃ k N m α x H H₁ hk hm hcop hx
  rw [he]
  unfold LeanLab.Tolev2009.Decomp310aScalar.phaseCap
  split_ifs with hθ
  · apply le_trans (norm_sum_le _ _)
    simpa only [norm_ee, sum_const, card_range, nsmul_eq_mul, mul_one] using hJ
  · exact (progression_phase_bound β (α * (m * k : ℕ)) J hθ).trans
      (min_le_min hJ le_rfl)


/-- Abel summation bounds the logarithmic row by eight log N times the phase sum.
The upper dyadic endpoint is controlled explicitly. No product cutoff is dropped.
No minor arc input is used. -/
theorem t144_logarithmic_row_norm_le_phase (lam : ℕ → ℝ) (l₃ K N m : ℕ)
    (α x M M₁ H H₁ : ℝ) (hlam : ∀ k, |lam k| ≤ 1)
    (hN : (3 : ℝ) ≤ N) (hx : 0 < x) (hxhi : x ≤ N)
    (hM : 0 < M) (hM₁ : M₁ ≤ 2 * M) (hH : 0 < H) (hHH₁ : H ≤ H₁)
    (hH₁ : H₁ ≤ 2 * H) (hprod : M * H ≤ 2 * x)
    (hm : m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊) :
    ‖row lam l₃ K N α x H H₁ (fun l : ℕ => (Real.log l : ℂ)) m‖ ≤
      8 * Real.log N * ∑ k ∈ Icc 1 K, LeanLab.Tolev2009.Decomp310aScalar.phaseCap α x (m * k) := by
  have hmp : 1 ≤ m := by have := (mem_Ioc.mp hm).1; omega
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hP : 0 ≤ ∑ k ∈ Icc 1 K, LeanLab.Tolev2009.Decomp310aScalar.phaseCap α x (m * k) :=
    sum_nonneg (fun k hk => LeanLab.Tolev2009.Decomp310aScalar.phaseCap_nonneg α x (m * k) hx.le)
  by_cases hHH : ⌊H⌋₊ < ⌊H₁⌋₊
  · have hmm : (m : ℝ) ≤ (⌊M₁⌋₊ : ℝ) := by exact_mod_cast (mem_Ioc.mp hm).2
    have hfloorpos : 0 < ⌊M₁⌋₊ := lt_of_lt_of_le (by omega : 0 < m) (mem_Ioc.mp hm).2
    have hM₁0 : 0 ≤ M₁ := by
      by_contra hh
      have hz := Nat.floor_of_nonpos (le_of_lt (lt_of_not_ge hh))
      rw [hz] at hfloorpos
      omega
    have hmle : (m : ℝ) ≤ M₁ := hmm.trans (Nat.floor_le hM₁0)
    have hmone : (1 : ℝ) ≤ m := by exact_mod_cast hmp
    have hMlo : (1 : ℝ) / 2 ≤ M := by linarith
    have hH₁0 : 0 < H₁ := hH.trans_le hHH₁
    have hendpoint : H₁ ≤ 8 * (N : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hH₁ hM.le,
        mul_le_mul_of_nonneg_right hMlo hH₁0.le]
    have hN0 : 0 < (N : ℝ) := by linarith
    have hNcube : (8 : ℝ) ≤ (N : ℝ) ^ 3 := by
      have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 3) hN 3
      norm_num at hh
      linarith
    have htop4 : (⌊H₁⌋₊ : ℝ) ≤ (N : ℝ) ^ 4 := by
      calc
        _ ≤ H₁ := Nat.floor_le hH₁0.le
        _ ≤ 8 * (N : ℝ) := hendpoint
        _ ≤ (N : ℝ) ^ 3 * N := mul_le_mul_of_nonneg_right hNcube hN0.le
        _ = _ := by ring
    have hlog : Real.log ⌊H₁⌋₊ ≤ 4 * Real.log N := by
      have ht : 0 < (⌊H₁⌋₊ : ℝ) := by exact_mod_cast (show 0 < ⌊H₁⌋₊ by omega)
      have hh := Real.log_le_log ht htop4
      rw [Real.log_pow] at hh
      norm_num at hh ⊢
      exact hh
    have hp : ∀ t : ℕ, ⌊H⌋₊ < t → t ≤ ⌊H₁⌋₊ →
        ‖row lam l₃ K N α x H (t : ℝ) (fun _ => 1) m‖ ≤
          ∑ k ∈ Icc 1 K, LeanLab.Tolev2009.Decomp310aScalar.phaseCap α x (m * k) := by
      intro t ht htu
      apply t144_row_norm_le_phase lam l₃ K N m α x H (t : ℝ) hlam hmp hx
      intro k hk hc
      exact t144_progression_bound l₃ k N m α x H (t : ℝ) (mem_Icc.mp hk).1 hmp hc hx
    apply (t144_logarithmic_row_norm_le_prefix lam l₃ K N m α x H H₁ _ hP hHH hp).trans
    nlinarith [mul_le_mul_of_nonneg_right hlog hP]
  · have he : Ioc ⌊H⌋₊ ⌊H₁⌋₊ = ∅ := Ioc_eq_empty_of_le (le_of_not_gt hHH)
    simp only [row, he, sum_empty, norm_zero]
    positivity

/-- LEAF. Tolev 1999 page 86 display 65, the unweighted inner progression sum.
Only the positive tau5 weighted row majorant is estimated. There is no first coefficient a.
The fixed residue and full interval cutoff are the explicit 2009 adaptation. OPEN. -/
theorem constant_rows :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((249 : ℝ) / 500) ≤ H →
          ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
            ((tau5 m : ℝ) * Real.log N) *
              ‖row lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x H H₁ (fun _ => 1) m‖ ≤
                C * N * Real.log N ^ (330 - 4 * A) := by
  intro A hA l₃ hl₃
  obtain ⟨C, N₀, hC, hav⟩ := LeanLab.Tolev2009.Decomp310aScalar.phase_average A hA
  refine ⟨C, max N₀ 3, hC, ?_⟩
  intro N hodd hN lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by have := (le_max_right N₀ 3).trans hN; linarith)]
    exact Real.exp_one_lt_d9.le.trans (by have := (le_max_right N₀ 3).trans hN; linarith)
  have hL0 : 0 < Real.log N := by linarith
  let P : ℕ → ℝ := fun m => ∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N), LeanLab.Tolev2009.Decomp310aScalar.phaseCap α x (m * k)
  have hP : ∀ m, 0 ≤ P m := fun m => sum_nonneg (fun k hk => LeanLab.Tolev2009.Decomp310aScalar.phaseCap_nonneg α x (m * k) (by linarith))
  have hr : ∀ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
      ‖row lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x H H₁ (fun _ => 1) m‖ ≤ P m := by
    intro m hm
    apply t144_row_norm_le_phase lam l₃ _ N m α x H H₁ hlam
      (by have := (mem_Ioc.mp hm).1; omega) (by linarith)
    intro k hk hc
    exact t144_progression_bound l₃ k N m α x H H₁ (mem_Icc.mp hk).1
      (by have := (mem_Ioc.mp hm).1; omega) hc (by linarith)
  have hav' := hav N hodd ((le_max_left _ _).trans hN) α hα hminor x M H
    hxlo hxhi hx hM hH hprodlo hprodhi hsize
  have hsub : Ioc ⌊M⌋₊ ⌊M₁⌋₊ ⊆ Ioc ⌊M⌋₊ ⌊2 * M⌋₊ :=
    Ioc_subset_Ioc le_rfl (Nat.floor_mono hM₁)
  calc
    _ ≤ Real.log N * ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, (tau5 m : ℝ) * P m := by
      rw [mul_sum]
      apply sum_le_sum
      intro m hm
      have ht := mul_le_mul_of_nonneg_left (hr m hm)
        (show 0 ≤ (tau5 m : ℝ) * Real.log N by positivity)
      nlinarith
    _ ≤ Real.log N * ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, (tau5 m : ℝ) * P m :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub (fun m hm hn => mul_nonneg (Nat.cast_nonneg _) (hP m))) hL0.le
    _ ≤ Real.log N * (C * N * Real.log N ^ (328 - 4 * A)) :=
      mul_le_mul_of_nonneg_left hav' hL0.le
    _ = C * N * Real.log N ^ (329 - 4 * A) := by
      rw [show (329 - 4 * A) = (1 : ℝ) + (328 - 4 * A) by ring,
        Real.rpow_add hL0, Real.rpow_one]
      ring
    _ ≤ _ := mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (by linarith)) (by positivity)

/-- LEAF. Tolev 1999 page 86 display 66, the Abel summation variant.
Only the positive tau5 weighted row majorant is estimated. There is no first coefficient a.
The fixed residue and full interval cutoff are the explicit 2009 adaptation. OPEN. -/
theorem logarithmic_rows :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((249 : ℝ) / 500) ≤ H →
          ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊,
            ((tau5 m : ℝ) * Real.log N) *
              ‖row lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x H H₁ (fun l : ℕ => (Real.log l : ℂ)) m‖ ≤
                C * N * Real.log N ^ (330 - 4 * A) := by
  intro A hA l₃ hl₃
  obtain ⟨C, N₀, hC, hav⟩ := LeanLab.Tolev2009.Decomp310aScalar.phase_average A hA
  refine ⟨8 * C, max N₀ 3, by positivity, ?_⟩
  intro N hodd hN lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize
  have hN3 : (3 : ℝ) ≤ N := (le_max_right _ _).trans hN
  have hL : 1 ≤ Real.log N := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact Real.exp_one_lt_d9.le.trans (by linarith)
  have hL0 : 0 < Real.log N := by linarith
  let P : ℕ → ℝ := fun m => ∑ k ∈ Icc 1 (cutoff3 (10 ^ 4 * A) N), LeanLab.Tolev2009.Decomp310aScalar.phaseCap α x (m * k)
  have hP : ∀ m, 0 ≤ P m := fun m => sum_nonneg (fun k hk => LeanLab.Tolev2009.Decomp310aScalar.phaseCap_nonneg α x (m * k) (by linarith))
  have hav' := hav N hodd ((le_max_left _ _).trans hN) α hα hminor x M H
    hxlo hxhi hx hM hH hprodlo hprodhi hsize
  have hsub : Ioc ⌊M⌋₊ ⌊M₁⌋₊ ⊆ Ioc ⌊M⌋₊ ⌊2 * M⌋₊ :=
    Ioc_subset_Ioc le_rfl (Nat.floor_mono hM₁)
  calc
    _ ≤ (8 * Real.log N ^ 2) * ∑ m ∈ Ioc ⌊M⌋₊ ⌊M₁⌋₊, (tau5 m : ℝ) * P m := by
      rw [mul_sum]
      apply sum_le_sum
      intro m hm
      have ht := mul_le_mul_of_nonneg_left
        (t144_logarithmic_row_norm_le_phase lam l₃ (cutoff3 (10 ^ 4 * A) N) N m α x M M₁ H H₁ hlam
          hN3 (by linarith) hxhi hM hM₁ hH hHH₁ hH₁ hprodhi hm)
        (show 0 ≤ (tau5 m : ℝ) * Real.log N by positivity)
      nlinarith
    _ ≤ (8 * Real.log N ^ 2) * ∑ m ∈ Ioc ⌊M⌋₊ ⌊2 * M⌋₊, (tau5 m : ℝ) * P m :=
      mul_le_mul_of_nonneg_left
        (sum_le_sum_of_subset_of_nonneg hsub (fun m hm hn => mul_nonneg (Nat.cast_nonneg _) (hP m))) (by positivity)
    _ ≤ (8 * Real.log N ^ 2) * (C * N * Real.log N ^ (328 - 4 * A)) :=
      mul_le_mul_of_nonneg_left hav' (by positivity)
    _ = _ := by
      rw [show (330 - 4 * A) = (2 : ℝ) + (328 - 4 * A) by ring,
        Real.rpow_add hL0, Real.rpow_two]
      ring

/-- The exact sealed Type I statement follows from the two row majorants.
CONDITIONAL ON constant_rows and logarithmic_rows. -/
theorem typeI_estimate :
    ∀ A : ℝ, 10 ^ 4 ≤ A → ∀ l₃ : ℕ, 1 ≤ l₃ →
      ∃ C N₀ : ℝ, 0 ≤ C ∧ ∀ N : ℕ, Odd N → N₀ ≤ N →
        ∀ lam : ℕ → ℝ, (∀ k, |lam k| ≤ 1) →
        ∀ α ∈ Set.Ioo (-1 / τof A N) (1 - 1 / τof A N), α ∉ majorArcs (Qof A N) (τof A N) →
        ∀ x M M₁ H H₁ : ℝ,
          (N : ℝ) * Real.log N ^ (-4 * A) ≤ x → x ≤ N → 2 < x →
          0 < M → M ≤ M₁ → M₁ ≤ 2 * M →
          0 < H → H ≤ H₁ → H₁ ≤ 2 * H → x / 4 ≤ M * H → M * H ≤ 2 * x →
          x ^ ((249 : ℝ) / 500) ≤ H →
          ∀ a b : ℕ → ℂ,
            (∀ m, ‖a m‖ ≤ (tau5 m : ℝ) * Real.log N) →
            (b = (fun _ => 1) ∨ b = (fun l : ℕ => (Real.log l : ℂ))) →
            ‖bilinear lam l₃ (cutoff3 (10 ^ 4 * A) N) N α x M M₁ H H₁ a b‖ ≤
              C * N * Real.log N ^ (330 - 4 * A) := by
  intro A hA l₃ hl₃
  obtain ⟨C₁, N₁, hC₁, h₁⟩ := constant_rows A hA l₃ hl₃
  obtain ⟨C₂, N₂, hC₂, h₂⟩ := logarithmic_rows A hA l₃ hl₃
  refine ⟨C₁ + C₂, max N₁ N₂, add_nonneg hC₁ hC₂, ?_⟩
  intro N hodd hN lam hlam α hα hminor x M M₁ H H₁
    hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize a b ha hb
  have hN₁ : N₁ ≤ N := (le_max_left _ _).trans hN
  have hN₂ : N₂ ≤ N := (le_max_right _ _).trans hN
  apply (bilinear_norm_le_rows lam l₃ _ N α x M M₁ H H₁ a b ha).trans
  rcases hb with rfl | rfl
  · apply (h₁ N hodd hN₁ lam hlam α hα hminor x M M₁ H H₁
      hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hC₂) (Nat.cast_nonneg N))
      (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)
  · apply (h₂ N hodd hN₂ lam hlam α hα hminor x M M₁ H H₁
      hxlo hxhi hx hM hMM₁ hM₁ hH hHH₁ hH₁ hprodlo hprodhi hsize).trans
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left hC₁) (Nat.cast_nonneg N))
      (Real.rpow_nonneg (Real.log_natCast_nonneg N) _)

end LeanLab.Tolev2009.Decomp310a
