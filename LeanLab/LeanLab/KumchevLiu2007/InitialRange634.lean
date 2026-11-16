/-
Elementary prefix bounds for the initial interval in P0088 page 8.
They handle a small H regime without using the A2.3 input.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Eq33RouteD
import LeanLab.KumchevLiu2007.Eq33RouteB

namespace LeanLab.KumchevLiu2007.Task634

open Real Complex MeasureTheory Task556a
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 8 after display 31: in the initial interval the short sum is
a prefix containing at most H divided by square root Y plus one frequencies. -/
theorem roughShortSum_initial_norm_le (Y P H α t : ℝ) (hY : 0 < Y) (hH : 0 ≤ H)
    (ht : t ≤ Y / 4) : ‖roughShortSum Y P H α t‖ ≤ H / Real.sqrt Y + 1 := by
  let s := (squareWindow Y).filter
    (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H)
  let a : ℕ := ⌈Real.sqrt Y / 2⌉₊
  let b : ℕ := ⌊Real.sqrt Y / 2 + H / Real.sqrt Y⌋₊
  have hr : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have hsq := Real.sq_sqrt hY.le
  have hsub : s ⊆ Finset.Icc a b := by
    intro m hm
    obtain ⟨hmw, _, hmt⟩ := Finset.mem_filter.mp hm
    have hlow : Real.sqrt Y / 2 ≤ (m : ℝ) := (Finset.mem_filter.mp hmw).2.1
    have hprod : ((m : ℝ) - Real.sqrt Y / 2) * Real.sqrt Y ≤ H := by
      nlinarith [sq_nonneg ((m : ℝ) - Real.sqrt Y / 2)]
    have hu : (m : ℝ) ≤ Real.sqrt Y / 2 + H / Real.sqrt Y := by
      have h := (le_div_iff₀ hr).mpr hprod
      linarith
    exact Finset.mem_Icc.mpr ⟨Nat.ceil_le.mpr hlow,
      (Nat.le_floor_iff (by positivity)).mpr hu⟩
  have hcard : (s.card : ℝ) ≤ H / Real.sqrt Y + 1 := by
    have hcard := Finset.card_le_card hsub
    by_cases hab : a ≤ b + 1
    · have hcast : ((Finset.Icc a b).card : ℝ) = (b : ℝ) + 1 - a := by
        rw [Nat.card_Icc, Nat.cast_sub hab, Nat.cast_add, Nat.cast_one]
      have ha : Real.sqrt Y / 2 ≤ (a : ℝ) := Nat.le_ceil _
      have hb : (b : ℝ) ≤ Real.sqrt Y / 2 + H / Real.sqrt Y :=
        Nat.floor_le (by positivity)
      have hc : (s.card : ℝ) ≤ ((Finset.Icc a b).card : ℝ) := by exact_mod_cast hcard
      rw [hcast] at hc
      linarith
    · have he : Finset.Icc a b = ∅ := Finset.Icc_eq_empty_of_lt (by omega)
      rw [he, Finset.card_empty] at hcard
      have : s.card = 0 := Nat.eq_zero_of_le_zero hcard
      rw [this, Nat.cast_zero]
      positivity
  have hn : ‖roughShortSum Y P H α t‖ ≤ (s.card : ℝ) := by
    unfold roughShortSum
    change ‖∑ m ∈ s, _‖ ≤ _
    calc
      _ ≤ ∑ _m ∈ s, (1 : ℝ) := norm_sum_le_of_le _ fun m hm => by
        rw [norm_mul, fourier_apply, Circle.norm_coe, mul_one]
        exact roughWeight_norm_le_one _ _
      _ = _ := by simp
  exact hn.trans hcard

/-- P0088 page 8 after display 31: the elementary initial energy is at most
H times the square of H divided by square root Y plus one. -/
theorem initial_energy_prefix_bound (Y P H α : ℝ) (hY : 0 < Y) (hH : 0 ≤ H) :
    (∫ t in (Y / 4 - H)..(Y / 4), ‖roughShortSum Y P H α t‖ ^ 2) ≤
      H * (H / Real.sqrt Y + 1) ^ 2 := by
  have hi : IntervalIntegrable (fun t => ‖roughShortSum Y P H α t‖ ^ 2)
      volume (Y / 4 - H) (Y / 4) :=
    Eq33RouteD.short_sum_sq_intervalIntegrable (squareWindow Y)
      (fun m => roughWeight (Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ)) m *
        fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) H _ _
  calc
    _ ≤ ∫ _t in (Y / 4 - H)..(Y / 4), (H / Real.sqrt Y + 1) ^ 2 := by
      apply intervalIntegral.integral_mono_on (by linarith) hi intervalIntegrable_const
      intro t ht
      exact pow_le_pow_left₀ (norm_nonneg _)
        (roughShortSum_initial_norm_le Y P H α t hY hH ht.2) 2
    _ = _ := by simp

/-- P0088 page 8 after display 31, a proved small H regime: once H reaches
square root Y and H times L to the A is at most Y, the initial energy has the
required H squared over L to the A bound with constant four. -/
theorem initial_energy_small (Y P H α L A : ℝ) (hY : 0 < Y) (hL : 0 < L)
    (hH : Real.sqrt Y ≤ H) (hsmall : H * L ^ A ≤ Y) :
    (∫ t in (Y / 4 - H)..(Y / 4), ‖roughShortSum Y P H α t‖ ^ 2) ≤
      4 * H ^ 2 / L ^ A := by
  have hr : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY
  have hH0 : 0 ≤ H := hr.le.trans hH
  have hLa : 0 < L ^ A := Real.rpow_pos_of_pos hL _
  have hfrac : 1 ≤ H / Real.sqrt Y := (le_div_iff₀ hr).mpr (by simpa using hH)
  have hs : (H / Real.sqrt Y + 1) ^ 2 ≤ (2 * H / Real.sqrt Y) ^ 2 := by
    apply pow_le_pow_left₀ (by positivity) _ 2
    rw [mul_div_assoc]
    linarith
  have hratio : H / Y ≤ 1 / L ^ A :=
    (div_le_div_iff₀ hY hLa).mpr (by simpa using hsmall)
  calc
    _ ≤ H * (H / Real.sqrt Y + 1) ^ 2 := initial_energy_prefix_bound Y P H α hY hH0
    _ ≤ H * (2 * H / Real.sqrt Y) ^ 2 := mul_le_mul_of_nonneg_left hs hH0
    _ = 4 * H ^ 2 * (H / Y) := by
      rw [div_pow, mul_pow, Real.sq_sqrt hY.le]
      ring
    _ ≤ 4 * H ^ 2 * (1 / L ^ A) := mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

/-- P0088 page 8 after display 31: the small H part of A23_initial_range
is unconditional under the extra inequality H times log X to the A plus two
at most Y. The written lower bound on H already ensures H reaches square root Y. -/
theorem A23_initial_range_small (A B ε X H α : ℝ) (hX : 2 ≤ X) (hε : 0 < ε)
    (hH : X ^ (7 / 18 + ε) ≤ H)
    (hsmall : H * Real.log X ^ (A + 2) ≤ windowY X ε) :
    (∫ t in (windowY X ε / 4 - H)..(windowY X ε / 4),
      ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
        4 * H ^ 2 / Real.log X ^ (A + 2) := by
  have hX0 : 0 < X := by linarith
  have hY : 0 < windowY X ε := Real.rpow_pos_of_pos hX0 _
  have hroot : Real.sqrt (windowY X ε) ≤ H := by
    calc
      _ = X ^ ((7 / 12 + ε / 2) * (1 / 2 : ℝ)) := by
        rw [Real.sqrt_eq_rpow, windowY, ← Real.rpow_mul hX0.le]
      _ ≤ X ^ (7 / 18 + ε) :=
        Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ H := hH
  exact initial_energy_small _ _ _ _ _ _ hY (Real.log_pos (by linarith)) hroot hsmall

end LeanLab.KumchevLiu2007.Task634

#print axioms LeanLab.KumchevLiu2007.Task634.roughShortSum_initial_norm_le
#print axioms LeanLab.KumchevLiu2007.Task634.initial_energy_prefix_bound
#print axioms LeanLab.KumchevLiu2007.Task634.initial_energy_small
#print axioms LeanLab.KumchevLiu2007.Task634.A23_initial_range_small
