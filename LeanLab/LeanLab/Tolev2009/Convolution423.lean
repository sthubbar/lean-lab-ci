/-
AI wrote this Lean code. Codex task423.
Binary Goldbach is open.
Source: Tolev 2009 page 1, the weighted representation count.
This finite mass comparison audits the old separate prime count split.
-/
import LeanLab.Tolev2009.Statements

open Finset Real
namespace LeanLab.Tolev2009.Convolution423

/-- A box of odd prime triples contributes its full mass to odd representation counts.
Tolev 2009 page 1 display 2, using only the definition of the weighted count. -/
theorem prime_box_mass (X : ℕ) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ Odd p ∧ X ≤ p ∧ p ≤ 8 * X) :
    (∑ p ∈ S, Real.log p) ^ 3 ≤
      ∑ N ∈ (Icc (3 * X) (24 * X)).filter Odd,
        LeanLab.Tolev2009.R (fun _ => 1) (fun _ => 0) N := by
  classical
  let T := S ×ˢ S ×ˢ S
  let I := (Icc (3 * X) (24 * X)).filter Odd
  let w : ℕ × ℕ × ℕ → ℝ := fun p => Real.log p.1 * Real.log p.2.1 * Real.log p.2.2
  have hm : ∀ p ∈ T, p.1 + p.2.1 + p.2.2 ∈ I := by
    intro p hp
    rcases mem_product.mp hp with ⟨hu, hvw⟩
    rcases mem_product.mp hvw with ⟨hv, hw⟩
    obtain ⟨_, hou, hXu, huX⟩ := hS _ hu
    obtain ⟨_, hov, hXv, hvX⟩ := hS _ hv
    obtain ⟨_, how, hXw, hwX⟩ := hS _ hw
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩,
      (hou.add_odd hov).add_odd how⟩
  have hc : (∑ p ∈ T, w p) = (∑ p ∈ S, Real.log p) ^ 3 := by
    simp only [T, w, sum_product]
    simp_rw [← Finset.mul_sum, ← Finset.sum_mul]
    rw [← Finset.sum_mul_sum]
    ring
  have hf := Finset.sum_fiberwise_of_maps_to hm w
  calc
    _ = ∑ p ∈ T, w p := hc.symm
    _ = ∑ N ∈ I, ∑ p ∈ T with p.1 + p.2.1 + p.2.2 = N, w p := hf.symm
    _ ≤ ∑ N ∈ I, LeanLab.Tolev2009.R (fun _ => 1) (fun _ => 0) N := by
      apply Finset.sum_le_sum
      intro N _
      unfold LeanLab.Tolev2009.R
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        obtain ⟨hp, hs⟩ := mem_filter.mp hp
        rcases mem_product.mp hp with ⟨hu, hvw⟩
        rcases mem_product.mp hvw with ⟨hv, hw⟩
        have hu' := (hS _ hu).1
        have hv' := (hS _ hv).1
        have hw' := (hS _ hw).1
        refine mem_filter.mpr ⟨mem_product.mpr ⟨mem_range.mpr (by omega),
          mem_product.mpr ⟨mem_range.mpr (by omega), mem_range.mpr (by omega)⟩⟩,
          hu', hv', hw', hs, ?_, ?_, ?_⟩ <;> exact Nat.mod_one _
      · intro p _ _
        exact mul_nonneg (mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _))
          (Real.log_natCast_nonneg _)

open Filter

/-- The elementary Chebyshev lower bound gives positive linear theta mass eventually.
This is a library consequence used to audit the separate prime count bound. -/
theorem theta_linear_lower :
    ∃ X₀ : ℝ, ∀ n : ℕ, X₀ ≤ n →
      (n : ℝ) * Real.log 2 / 2 ≤ Chebyshev.theta n := by
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have he := (isLittleO_log_rpow_rpow_atTop 1 (by norm_num : (0 : ℝ) < 1 / 2)).bound
    (by positivity : (0 : ℝ) < Real.log 2 / 16)
  obtain ⟨X, hX⟩ := eventually_atTop.mp he
  refine ⟨max X 16, ?_⟩
  intro n hn
  have hn16 : (16 : ℝ) ≤ n := (le_max_right _ _).trans hn
  have hnp : (0 : ℝ) < n := by linarith
  have hb := hX (n : ℝ) ((le_max_left _ _).trans hn)
  simp only [Real.rpow_one, Real.norm_eq_abs] at hb
  rw [abs_of_nonneg (Real.log_natCast_nonneg n),
    abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg n) _), ← Real.sqrt_eq_rpow] at hb
  have hs : Real.sqrt n ≤ n := by
    rw [Real.sqrt_le_iff]
    exact ⟨hnp.le, by nlinarith⟩
  have hlog : Real.log ((n : ℝ) + 1) ≤ Real.log 2 + Real.log n := by
    have h := Real.log_le_log (by positivity : (0 : ℝ) < n + 1)
      (by linarith : (n : ℝ) + 1 ≤ 2 * n)
    rwa [Real.log_mul (by norm_num) hnp.ne'] at h
  have hsmall : Real.log n ≤ Real.log 2 / 16 * n :=
    hb.trans (mul_le_mul_of_nonneg_left hs (by positivity))
  have hconst : Real.log 2 ≤ Real.log 2 / 16 * n := by nlinarith
  have hplus : Real.log ((n : ℝ) + 1) ≤ Real.log 2 / 8 * n := by linarith
  have herr : 2 * Real.sqrt n * Real.log n ≤ Real.log 2 / 8 * n := by
    calc
      _ ≤ 2 * Real.sqrt n * (Real.log 2 / 16 * Real.sqrt n) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = Real.log 2 / 8 * (Real.sqrt n) ^ 2 := by ring
      _ = Real.log 2 / 8 * n := by rw [Real.sq_sqrt (Nat.cast_nonneg n)]
  have htheta := Chebyshev.theta_ge n
  nlinarith

/-- A fixed ratio prime interval has positive linear logarithmic mass eventually.
This follows from the elementary Chebyshev bounds. -/
theorem interval_prime_mass :
    ∃ X₀ : ℝ, ∀ X : ℕ, X₀ ≤ X →
      Real.log 2 * (X : ℝ) ≤
        ∑ p ∈ (Icc X (8 * X)).filter Nat.Prime, Real.log p := by
  classical
  obtain ⟨Y, hY⟩ := theta_linear_lower
  refine ⟨max Y 3, ?_⟩
  intro X hX
  have hX3 : (3 : ℝ) ≤ X := (le_max_right _ _).trans hX
  have hlow := hY (8 * X) (by push_cast; nlinarith [(le_max_left _ _).trans hX])
  have hupp := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg X)
  have hlog4 : Real.log (4 : ℝ) = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
  rw [hlog4] at hupp
  let S := (Icc X (8 * X)).filter Nat.Prime
  let P := (Icc 0 X).filter Nat.Prime
  have hsub : (Icc 0 (8 * X)).filter Nat.Prime ⊆ P ∪ S := by
    intro p hp
    obtain ⟨hp, hprime⟩ := mem_filter.mp hp
    by_cases h : p ≤ X
    · exact mem_union_left _ (mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, h⟩, hprime⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨mem_Icc.mpr
        ⟨by omega, (mem_Icc.mp hp).2⟩, hprime⟩)
  have hs := Finset.sum_le_sum_of_subset_of_nonneg hsub
    (f := fun p : ℕ => Real.log p) (fun p _ _ => Real.log_natCast_nonneg p)
  have hi : 0 ≤ ∑ p ∈ P ∩ S, Real.log p :=
    sum_nonneg (fun p _ => Real.log_natCast_nonneg p)
  have he := Finset.sum_union_inter (s₁ := P) (s₂ := S) (f := fun p : ℕ => Real.log p)
  have hcover : Chebyshev.theta (8 * X : ℕ) ≤
      Chebyshev.theta X + ∑ p ∈ S, Real.log p := by
    simp only [Chebyshev.theta_eq_sum_Icc, Nat.floor_natCast]
    change (∑ p ∈ (Icc 0 (8 * X)).filter Nat.Prime, Real.log p) ≤
      (∑ p ∈ P, Real.log p) + ∑ p ∈ S, Real.log p
    linarith
  have hl2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  push_cast at hlow hcover
  dsimp only [S] at hcover
  nlinarith

/-- The total odd representation mass in a fixed ratio interval has cubic size.
This is a counting audit, not a pointwise ternary asymptotic. -/
theorem interval_representation_mass :
    ∃ X₀ : ℝ, ∀ X : ℕ, X₀ ≤ X →
      Real.log 2 ^ 3 * (X : ℝ) ^ 3 ≤
        ∑ N ∈ (Icc (3 * X) (24 * X)).filter Odd,
          LeanLab.Tolev2009.R (fun _ => 1) (fun _ => 0) N := by
  classical
  obtain ⟨Y, hY⟩ := interval_prime_mass
  refine ⟨max Y 3, ?_⟩
  intro X hX
  have hX3 : (3 : ℝ) ≤ X := (le_max_right _ _).trans hX
  let S := (Icc X (8 * X)).filter Nat.Prime
  have hS : ∀ p ∈ S, p.Prime ∧ Odd p ∧ X ≤ p ∧ p ≤ 8 * X := by
    intro p hp
    obtain ⟨hp, hprime⟩ := mem_filter.mp hp
    have hpX := mem_Icc.mp hp
    have hXnat : 3 ≤ X := by exact_mod_cast hX3
    exact ⟨hprime, hprime.odd_of_ne_two (by omega), hpX⟩
  have hm := hY X ((le_max_left _ _).trans hX)
  have hcube : (Real.log 2 * (X : ℝ)) ^ 3 ≤ (∑ p ∈ S, Real.log p) ^ 3 := by
    exact pow_le_pow_left₀ (by positivity) hm 3
  calc
    _ = (Real.log 2 * (X : ℝ)) ^ 3 := by ring
    _ ≤ (∑ p ∈ S, Real.log p) ^ 3 := hcube
    _ ≤ _ := prime_box_mass X S hS

/-- The uncentered weighted prime count has no uniform saving of one logarithm.
This concerns the old separate R leaf, not the centered error in the paper. -/
theorem uncentered_count_no_log_saving :
    ¬ ∃ C N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
      LeanLab.Tolev2009.R (fun _ => 1) (fun _ => 0) N ≤
        C * (N : ℝ) ^ 2 / Real.log N := by
  classical
  rintro ⟨C, N₀, hC⟩
  obtain ⟨Y, hY⟩ := interval_representation_mass
  let D := max C 1
  have hD : 0 < D := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1) (le_max_right _ _)
  have hc : 0 < Real.log (2 : ℝ) ^ 3 := pow_pos (Real.log_pos (by norm_num)) _
  let L := 1 + 13824 * D / Real.log 2 ^ 3
  obtain ⟨X, hX⟩ := exists_nat_gt (max (max Y N₀) (max 3 (Real.exp L)))
  have hXY : Y ≤ (X : ℝ) := (le_max_left _ _).trans ((le_max_left _ _).trans hX.le)
  have hXN : N₀ ≤ (X : ℝ) := (le_max_right _ _).trans ((le_max_left _ _).trans hX.le)
  have hX3 : (3 : ℝ) ≤ X := (le_max_left _ _).trans ((le_max_right _ _).trans hX.le)
  have hXp : (0 : ℝ) < X := by linarith
  have hlog : L < Real.log X := (Real.lt_log_iff_exp_lt hXp).mpr
    ((le_max_right _ _).trans_lt ((le_max_right _ _).trans_lt hX))
  have hLp : 0 < L := by dsimp [L]; positivity
  have hlogX : 0 < Real.log X := hLp.trans hlog
  let I := (Icc (3 * X) (24 * X)).filter Odd
  have hterm : ∀ N ∈ I, LeanLab.Tolev2009.R (fun _ => 1) (fun _ => 0) N ≤
      D * (24 * (X : ℝ)) ^ 2 / Real.log X := by
    intro N hN
    obtain ⟨hN, hodd⟩ := mem_filter.mp hN
    have hb := mem_Icc.mp hN
    have hNX : (X : ℝ) ≤ N := by exact_mod_cast (show X ≤ N by omega)
    have hNup : (N : ℝ) ≤ 24 * X := by exact_mod_cast hb.2
    have hln : Real.log X ≤ Real.log N := Real.log_le_log hXp hNX
    have hlnp : 0 < Real.log N := hlogX.trans_le hln
    calc
      _ ≤ C * (N : ℝ) ^ 2 / Real.log N := hC N hodd (hXN.trans hNX)
      _ ≤ D * (N : ℝ) ^ 2 / Real.log N := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)) hlnp.le
      _ ≤ D * (N : ℝ) ^ 2 / Real.log X :=
        div_le_div_of_nonneg_left (mul_nonneg hD.le (sq_nonneg _)) hlogX hln
      _ ≤ _ := div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg N) hNup 2) hD.le) hlogX.le
  have hcard : I.card ≤ 24 * X := by
    have hh := Finset.card_filter_le (s := Icc (3 * X) (24 * X)) (p := Odd)
    have hXnat : 1 ≤ X := by exact_mod_cast (show (1 : ℝ) ≤ X by linarith)
    dsimp only [I]
    exact hh.trans (by rw [Nat.card_Icc]; omega)
  have hsum := Finset.sum_le_sum hterm
  simp only [sum_const, nsmul_eq_mul] at hsum
  have hupper : (∑ N ∈ I, LeanLab.Tolev2009.R (fun _ => 1) (fun _ => 0) N) ≤
      13824 * D * (X : ℝ) ^ 3 / Real.log X := by
    calc
      _ ≤ (I.card : ℝ) * (D * (24 * (X : ℝ)) ^ 2 / Real.log X) := hsum
      _ ≤ (24 * (X : ℝ)) * (D * (24 * (X : ℝ)) ^ 2 / Real.log X) :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
      _ = _ := by ring
  have hlower := hY X hXY
  have hmass := hlower.trans hupper
  have hmass' := (le_div_iff₀ hlogX).mp hmass
  have hscaled : (Real.log 2 ^ 3 * Real.log X) * (X : ℝ) ^ 3 ≤
      (13824 * D) * (X : ℝ) ^ 3 := by convert hmass' using 1 <;> ring
  have hcancel := (mul_le_mul_iff_of_pos_right (pow_pos hXp 3)).mp hscaled
  have hlarge : 13824 * D / Real.log 2 ^ 3 < Real.log X := by dsimp [L] at hlog; linarith
  have hlarge' := (div_lt_iff₀ hc).mp hlarge
  nlinarith

end LeanLab.Tolev2009.Convolution423
