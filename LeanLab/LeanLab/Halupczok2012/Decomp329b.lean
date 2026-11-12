import LeanLab.Halupczok2012.Decomp329a
import LeanLab.Halupczok2012.DecompJ219

/-!
Public supply for Corollary 1.3 on journal pages 345 to 346.
The finite step is separate from logarithmic domination.
The analytic count and Corollary 1.2 are explicit inputs.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp329b

open scoped Classical

set_option maxHeartbeats 1000000 in
/-- Pages 345 to 346, Corollary 1.3 conditional on Corollary 1.2 and a uniform Wu count. -/
theorem corollary3_of_count (hCor2 : Corollary2)
    (c_wu : ℝ) (hc_wu : 0 < c_wu) (Y0_wu : ℝ) (_hY0_wu : 0 < Y0_wu)
    (hwu : ∀ (X Y : ℝ), Y0_wu ≤ Y → X ^ (0.971 : ℝ) ≤ Y → Y ≤ X →
      c_wu * Y / (Real.log Y) ^ 2 ≤
        ((@Finset.filter ℕ (fun (p : ℕ) => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2))
          (Classical.decPred _) (kRange X Y)).card : ℝ)) : Corollary3 := by
  intro ε c hε hc
  obtain ⟨C, Y0c, hcor⟩ := hCor2 3 ε c (by norm_num) hε hc
  let M : ℝ := max C 0 + 2
  obtain ⟨Y0d, _, hdom⟩ := leaf_wu_dominates_exc c_wu M hc_wu
  have hev : ∀ᶠ Y : ℝ in Filter.atTop, (Real.log Y) ^ (3 : ℕ) ≤ Y := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := 1) 3 zero_lt_one).bound zero_lt_one
    filter_upwards [h, Filter.eventually_ge_atTop (0 : ℝ)] with Y hY hY0
    have he : (Real.log Y) ^ (3 : ℝ) = (Real.log Y) ^ (3 : ℕ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by rfl, Real.rpow_natCast]
    have hb : |(Real.log Y) ^ (3 : ℕ)| ≤ Y := by
      simpa only [Real.rpow_one, one_mul, Real.norm_eq_abs, abs_of_nonneg hY0, he] using hY
    exact (le_abs_self _).trans hb
  obtain ⟨Ycube, hcube⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max 4 (max Y0_wu (max Y0c (max Y0d Ycube))), ?_⟩
  intro X1 X2 Y n hY hX1pow hYX1 hX2pow hYX2 hnodd hn6 hsum hnupper
  have hY4 : (4 : ℝ) ≤ Y := (le_max_left _ _).trans hY
  have hrest : max Y0_wu (max Y0c (max Y0d Ycube)) ≤ Y := (le_max_right _ _).trans hY
  have hY0wu : Y0_wu ≤ Y := (le_max_left _ _).trans hrest
  have hrest' : max Y0c (max Y0d Ycube) ≤ Y := (le_max_right _ _).trans hrest
  have hY0c : Y0c ≤ Y := (le_max_left _ _).trans hrest'
  have hrest'' : max Y0d Ycube ≤ Y := (le_max_right _ _).trans hrest'
  have hY0d : Y0d ≤ Y := (le_max_left _ _).trans hrest''
  have hYcube : Ycube ≤ Y := (le_max_right _ _).trans hrest''
  have hlog : 0 < Real.log Y := Real.log_pos (by linarith)
  have hL3 : (Real.log Y) ^ (-3 : ℝ) = 1 / (Real.log Y) ^ (3 : ℕ) := by
    rw [Real.rpow_neg hlog.le,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by rfl, Real.rpow_natCast, one_div]
  have hbase : 1 ≤ Y * (Real.log Y) ^ (-3 : ℝ) := by
    rw [hL3, ← div_eq_mul_one_div, le_div_iff₀ (by positivity)]
    simpa only [one_mul] using hcube Y hYcube
  have hweight : 0 ≤ Y * (Real.log Y) ^ (-3 : ℝ) := by positivity
  let K1 : ℝ := ((n : ℝ) - X1 - Y) / 2
  have hexc : (cor2Exc K1 X2 Y : ℝ) ≤ C * Y * Real.log Y ^ (-3 : ℝ) := by
    apply hcor K1 X2 Y hY0c hX2pow hYX2 <;> dsimp [K1] <;> linarith
  have hcount := hwu X1 Y hY0wu hX1pow hYX1
  have hM : C * Y * Real.log Y ^ (-3 : ℝ) + 2 ≤
      M * Y * Real.log Y ^ (-3 : ℝ) := by
    have hC : C ≤ max C 0 := le_max_left _ _
    have hb := mul_le_mul_of_nonneg_right hC hweight
    dsimp [M]
    nlinarith
  have hcnt : cor2Exc K1 X2 Y + 2 ≤
      ((kRange X1 Y).filter (fun p => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2))).card := by
    have hle : (cor2Exc K1 X2 Y : ℝ) + 2 ≤
        (((kRange X1 Y).filter
          (fun p => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2))).card : ℝ) := by
      calc
        _ ≤ C * Y * Real.log Y ^ (-3 : ℝ) + 2 := by linarith [hexc]
        _ ≤ M * Y * Real.log Y ^ (-3 : ℝ) := hM
        _ ≤ c_wu * Y / (Real.log Y) ^ 2 := (hdom Y hY0d).le
        _ ≤ _ := by
          rw [Finset.filter_congr_decidable] at hcount
          exact hcount
    exact_mod_cast hle
  exact Decomp329a.representation_of_surplus (by linarith) (by linarith)
    hnodd hn6 hsum hcnt

/-- Pages 345 to 346, the exact assembly statement with both cited inputs explicit. -/
theorem corollary3_of_inputs (hCor2 : Corollary2)
    (hWu : ∃ c > 0, ∃ Y0 > 0, ∀ (X Y : ℝ), Y0 ≤ Y → X ^ (0.971 : ℝ) ≤ Y → Y ≤ X →
    c * Y / (Real.log Y) ^ 2 ≤ (@Finset.filter ℕ (fun (p : ℕ) => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2)) (Classical.decPred _) (kRange X Y)).card) : Corollary3 := by
  obtain ⟨c, hc, Y0, hY0, hcount⟩ := hWu
  exact corollary3_of_count hCor2 c hc Y0 hY0 hcount

/-- Pages 345 to 346, supply for the sealed corollary_3_assembly_leaf statement.
This wrapper still depends on the existing open Wu leaf. -/
theorem corollary_3_assembly_supply (hCor2 : Corollary2) : Corollary3 :=
  corollary3_of_inputs hCor2 leaf_wu_theorem

end LeanLab.Halupczok2012.Decomp329b
