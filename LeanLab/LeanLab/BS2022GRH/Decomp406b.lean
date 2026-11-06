/- AI wrote this Lean code for CODEX task406. Goldbach is open.
Finite dyadic covering and scalar bounds on journal pp. 1225 and 1226.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Decomp374f
import LeanLab.BS2022GRH.Decomp374d

namespace LeanLab.BS2022GRH.Decomp406b
open Real Finset Classical ChenThresholdGRH Decomp148a Decomp374a Decomp374f
noncomputable section

/-- LEAF. Journal p. 1225, dyadic partition between displays 14 and 15.
Every integer r at least three with D0 less than r less than D lies in a block.
The base max D0 2 avoids a spurious block count when D0 is less than two.
Only nonnegative finite weights occur here, with no character or analytic input. -/
theorem dyadic_cover (D D₀ : ℝ) (hD : 5 ≤ D) (hD₀ : 1 < D₀) (hD₀D : D₀ ≤ D)
    (W : ℕ → ℝ) (hW : ∀ r, 0 ≤ W r) :
    (∑ r ∈ (Ico 3 ⌈D⌉₊).filter (fun r : ℕ => D₀ < (r : ℝ)), W r) ≤
      ∑ k ∈ range ⌈log (D / max D₀ 2) / log 2⌉₊,
        ∑ r ∈ blockModuli ((2 : ℝ) ^ k * max D₀ 2), W r := by
  let T := (Ico 3 ⌈D⌉₊).filter (fun r : ℕ => D₀ < (r : ℝ))
  let K := ⌈log (D / max D₀ 2) / log 2⌉₊
  let R : ℕ → ℝ := fun k => (2 : ℝ) ^ k * max D₀ 2
  have hb : 0 < max D₀ 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right _ _)
  have hcover : ∀ r ∈ T, ∃ k ∈ range K, r ∈ blockModuli (R k) := by
    intro r hr
    obtain ⟨hrI, hrD₀⟩ := mem_filter.mp hr
    obtain ⟨hr3, hrceil⟩ := mem_Ico.mp hrI
    have hrR : (3 : ℝ) ≤ r := by exact_mod_cast hr3
    have hrD : (r : ℝ) < D := Nat.lt_ceil.mp hrceil
    have hbr : max D₀ 2 ≤ (r : ℝ) := max_le hrD₀.le (by linarith)
    have hratio : 1 ≤ (r : ℝ) / max D₀ 2 := (le_div_iff₀ hb).mpr (by simpa using hbr)
    obtain ⟨k, hklo, hkhi⟩ := exists_nat_pow_near hratio (by norm_num : (1 : ℝ) < 2)
    have hkr : R k ≤ (r : ℝ) := (le_div_iff₀ hb).mp hklo
    have hrk : (r : ℝ) < 2 * R k := by
      have hh := (div_lt_iff₀ hb).mp hkhi
      dsimp [R]
      simpa only [pow_succ, mul_assoc, mul_comm, mul_left_comm] using hh
    have hkD : R k < D := hkr.trans_lt hrD
    have hlog := log_lt_log (show 0 < R k by dsimp [R]; positivity) hkD
    dsimp [R] at hlog
    rw [log_mul (by positivity) hb.ne', log_pow] at hlog
    have hklog : (k : ℝ) < log (D / max D₀ 2) / log 2 := by
      apply (lt_div_iff₀ (log_pos (by norm_num : (1 : ℝ) < 2))).mpr
      rw [log_div (by linarith : D ≠ 0) hb.ne']
      linarith
    refine ⟨k, mem_range.mpr (Nat.lt_ceil.mpr hklog), ?_⟩
    exact mem_filter.mpr ⟨mem_Ico.mpr ⟨hr3, Nat.lt_ceil.mpr hrk⟩, hkr⟩
  calc
    _ ≤ ∑ r ∈ T, ∑ k ∈ range K, if r ∈ blockModuli (R k) then W r else 0 := by
      apply sum_le_sum
      intro r hr
      obtain ⟨k, hk, hkr⟩ := hcover r hr
      have hsingle := single_le_sum (f := fun k => if r ∈ blockModuli (R k) then W r else 0)
        (s := range K) (fun k _ => by split_ifs <;> linarith [hW r]) hk
      simpa only [if_pos hkr] using hsingle
    _ = ∑ k ∈ range K, ∑ r ∈ T, if r ∈ blockModuli (R k) then W r else 0 := sum_comm
    _ ≤ _ := by
      apply sum_le_sum
      intro k hk
      rw [← sum_filter]
      have hsub : T.filter (fun r => r ∈ blockModuli (R k)) ⊆ blockModuli (R k) := by
        intro r hr
        exact (mem_filter.mp hr).2
      exact sum_le_sum_of_subset_of_nonneg hsub (fun r _ _ => hW r)

/-- The number of blocks is at most log D over log two, journal p. 1225. -/
theorem block_count_le (D D₀ : ℝ) (hD : 5 ≤ D) (hD₀ : 1 < D₀) (hD₀D : D₀ ≤ D) :
    (⌈log (D / max D₀ 2) / log 2⌉₊ : ℝ) ≤ log D / log 2 := by
  have hbase : 0 < max D₀ 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right _ _)
  have hbD : max D₀ 2 ≤ D := max_le hD₀D (by linarith)
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hlbase : log (2 : ℝ) ≤ log (max D₀ 2) := log_le_log (by norm_num) (le_max_right _ _)
  have ht : 0 ≤ log (D / max D₀ 2) / log 2 := by
    apply div_nonneg _ hl2.le
    exact log_nonneg ((le_div_iff₀ hbase).mpr (by simpa using hbD))
  have hc := Nat.ceil_lt_add_one ht
  rw [log_div (by linarith : D ≠ 0) hbase.ne'] at hc ⊢
  apply le_of_lt (hc.trans_le _)
  apply (le_div_iff₀ hl2).mpr
  field_simp
  linarith

/-- Every selected radius is at least D0 and less than D, journal p. 1225. -/
theorem block_radius_bounds (D D₀ : ℝ) (hD : 5 ≤ D) (hD₀ : 1 < D₀)
    (k : ℕ) (hk : k ∈ range ⌈log (D / max D₀ 2) / log 2⌉₊) :
    D₀ ≤ (2 : ℝ) ^ k * max D₀ 2 ∧ (2 : ℝ) ^ k * max D₀ 2 < D := by
  have hb : 0 < max D₀ 2 := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 2) (le_max_right _ _)
  have hl2 : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hk' : (k : ℝ) < log (D / max D₀ 2) / log 2 := Nat.lt_ceil.mp (mem_range.mp hk)
  have hlog := (lt_div_iff₀ hl2).mp hk'
  rw [log_div (by linarith : D ≠ 0) hb.ne'] at hlog
  constructor
  · exact (le_max_left D₀ 2).trans (le_mul_of_one_le_left hb.le (one_le_pow₀ (by norm_num)))
  · apply (log_lt_log_iff (by positivity) (by linarith : 0 < D)).mp
    rw [log_mul (by positivity) hb.ne', log_pow]
    linarith

/-- The last scalar inequality of display 15, journal p. 1225.
The square root block bound is dominated by one common cap. -/
theorem block_scalar_le (X Y D D₀ R : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y)
    (hD₀ : 0 < D₀) (hD₀R : D₀ ≤ R) (hRD : R ≤ D) :
    √((X + 4 * R ^ 2) * (Y + 4 * R ^ 2) * X * Y) / R ≤ largeFactor X Y D D₀ := by
  have hR : 0 < R := hD₀.trans_le hD₀R
  have hx := sq_sqrt hX
  have hy := sq_sqrt hY
  have hxy := sq_sqrt (mul_nonneg hX hY)
  have hroot : √((X + 4 * R ^ 2) * (Y + 4 * R ^ 2) * X * Y) ≤
      (√X + 2 * R) * (√Y + 2 * R) * √(X * Y) := by
    apply (sqrt_le_iff).mpr
    constructor
    · positivity
    · have hxx : X + 4 * R ^ 2 ≤ (√X + 2 * R) ^ 2 := by nlinarith [mul_nonneg (sqrt_nonneg X) hR.le]
      have hyy : Y + 4 * R ^ 2 ≤ (√Y + 2 * R) ^ 2 := by nlinarith [mul_nonneg (sqrt_nonneg Y) hR.le]
      have hm := mul_le_mul hxx hyy (by positivity : 0 ≤ Y + 4 * R ^ 2)
        (by positivity : 0 ≤ (√X + 2 * R) ^ 2)
      rw [mul_pow, mul_pow, hxy]
      convert mul_le_mul_of_nonneg_right hm (mul_nonneg hX hY) using 1 <;> ring
  have hprod : √X * √Y = √(X * Y) := (sqrt_mul hX Y).symm
  have hmul : √X * √Y * √(X * Y) = X * Y := by
    rw [hprod]
    nlinarith
  have hrecip : X * Y / R ≤ X * Y / D₀ :=
    div_le_div_of_nonneg_left (mul_nonneg hX hY) hD₀ hD₀R
  calc
    _ ≤ ((√X + 2 * R) * (√Y + 2 * R) * √(X * Y)) / R :=
      div_le_div_of_nonneg_right hroot hR.le
    _ = 4 * R * √(X * Y) + 2 * (√X + √Y) * √(X * Y) + X * Y / R := by
      field_simp
      nlinarith [hmul]
    _ ≤ largeFactor X Y D D₀ := by
      unfold largeFactor
      nlinarith [mul_le_mul_of_nonneg_right hRD (sqrt_nonneg (X * Y))]

/-- Exact statement of Decomp374f.dyadic_conductor_slice from the finite cover.
CONDITIONAL ON the explicit block estimates. The finite cover is proved. -/
theorem dyadic_conductor_slice (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (a : ℤ) (s : ℕ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hY : 25 ≤ Y) (hZ : 25 ≤ Z)
    (hZY : Z < Y) (hD : 1 < D) (hDX : D < √(X * Y))
    (hD₀ : 1 < D₀) (hD₀D : D₀ ≤ D) (hbal : √(X * Y) / D ≤ D₀)
    (hblock : ∀ R : ℝ, 1 ≤ R →
      (∑ r ∈ Decomp374a.blockModuli R,
        (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s) ≤
        √((X + 4 * R ^ 2) * (Y + 4 * R ^ 2) * X * Y) / R) :
    (∑ r ∈ (conductors D a).filter (fun r : ℕ => D₀ < (r : ℝ)),
      (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s) ≤
      log D / log 2 * largeFactor X Y D D₀ := by
  have hD5 := Decomp374d.five_le_level X Y D D₀ hX hY hD hD₀D hbal
  let W : ℕ → ℝ := fun r => (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s
  have hw : ∀ r, 0 ≤ W r := by
    intro r
    dsimp [W, primitiveTerm]
    positivity
  have hsubset : (conductors D a).filter (fun r : ℕ => D₀ < (r : ℝ)) ⊆
      (Ico 3 ⌈D⌉₊).filter (fun r : ℕ => D₀ < (r : ℝ)) := by
    intro r hr
    obtain ⟨hr, hlt⟩ := mem_filter.mp hr
    exact mem_filter.mpr ⟨(mem_filter.mp hr).1, hlt⟩
  have hcap : 0 ≤ largeFactor X Y D D₀ := by unfold largeFactor; positivity
  calc
    _ ≤ ∑ r ∈ (Ico 3 ⌈D⌉₊).filter (fun r : ℕ => D₀ < (r : ℝ)), W r :=
      sum_le_sum_of_subset_of_nonneg hsubset (fun r _ _ => hw r)
    _ ≤ _ := dyadic_cover D D₀ hD5 hD₀ hD₀D W hw
    _ ≤ ∑ _k ∈ range ⌈log (D / max D₀ 2) / log 2⌉₊, largeFactor X Y D D₀ := by
      apply sum_le_sum
      intro k hk
      have hb := block_radius_bounds D D₀ hD5 hD₀ k hk
      exact (hblock _ (by linarith)).trans
        (block_scalar_le X Y D D₀ _ (by linarith) (by linarith) (by linarith) hb.1 hb.2.le)
    _ = (⌈log (D / max D₀ 2) / log 2⌉₊ : ℝ) * largeFactor X Y D D₀ := by simp
    _ ≤ _ := mul_le_mul_of_nonneg_right (block_count_le D D₀ hD5 hD₀ hD₀D) hcap

end
end LeanLab.BS2022GRH.Decomp406b

#print axioms LeanLab.BS2022GRH.Decomp406b.dyadic_cover
#print axioms LeanLab.BS2022GRH.Decomp406b.block_count_le
#print axioms LeanLab.BS2022GRH.Decomp406b.block_radius_bounds
#print axioms LeanLab.BS2022GRH.Decomp406b.block_scalar_le
#print axioms LeanLab.BS2022GRH.Decomp406b.dyadic_conductor_slice
