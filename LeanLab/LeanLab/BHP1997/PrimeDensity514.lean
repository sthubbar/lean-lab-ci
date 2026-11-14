/-
P0069 page 3 display 1.8 and page 51 display 5.17.
The existing normalization audit is unconditional for the raw prime indicator.
This concerns a raw candidate. It does not refute the normalized lower coefficient or the paper.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Prime514
import LeanLab.BHP1997.Audit1624

namespace LeanLab.BHP1997.PrimeDensity514
open Classical Real Filter Decomp132 DecompC165b
open scoped BigOperators

/-- P0069 page 3 display 1.8 and page 51 display 5.17. The raw prime indicator\ntracks the reciprocal logarithm on the two prefixes used by the existing half interval audit.\nThe ordinary prime number theorem of Prime514 discharges that audit input. -/
theorem prime_reciprocal_tracking {ε : ℝ} (hε : 0 ≤ ε) :
    ∃ K X : ℝ, ∀ x : ℝ, X ≤ x → ∀ n : ℕ,
      n = Audit1624.midEnd ε x ∨ n = Audit1624.highEnd ε x →
      |∑ m ∈ Finset.Ioc (Audit1624.lowEnd ε x) n,
        (primeWeight m - 1 / Real.log (m : ℝ))| ≤
          K * Audit1624.shortY ε x / Real.log (Audit1624.shortY ε x) ^ 3 := by
  obtain ⟨C, hC⟩ := Prime514.pnt_short_interval 3 (by norm_num)
  have hs : (0 : ℝ) < 11/20 + ε := by linarith
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    ((tendsto_rpow_atTop hs).eventually (eventually_ge_atTop (max C 4)))
  refine ⟨4 * max C 1, X, fun x hx n hn => ?_⟩
  let Y := Audit1624.shortY ε x
  let L := Audit1624.lowEnd ε x
  let U := Audit1624.highEnd ε x
  have hCY : C ≤ Y := (le_max_left _ _).trans (hX x hx)
  have hY4 : 4 ≤ Y := (le_max_right _ _).trans (hX x hx)
  have hY0 : 0 < Y := by linarith
  have hL : (L : ℝ) ≤ Y := Nat.floor_le hY0.le
  have hU : (U : ℝ) ≤ 2 * Y := Nat.floor_le (by positivity)
  have hUlt : 2 * Y < (U : ℝ) + 1 := Nat.lt_floor_add_one _
  have hgap : L + 3 ≤ U := by
    have : (L : ℝ) + 3 ≤ (U : ℝ) := by linarith
    exact_mod_cast this
  change n = L + (U-L)/2 ∨ n = U at hn
  have hnL : L + 1 ≤ n := by omega
  have hnU : n ≤ U := by omega
  have hYn : Y ≤ (n : ℝ) := by
    have hfloor : Y < (L : ℝ) + 1 := Nat.lt_floor_add_one Y
    have hle : (L : ℝ) + 1 ≤ (n : ℝ) := by exact_mod_cast hnL
    linarith
  have hnY : (n : ℝ) ≤ 4 * Y := by
    have hnu : (n : ℝ) ≤ U := by exact_mod_cast hnU
    linarith
  have hb := hC (4 * Y) (by linarith) Y (n : ℝ) hY0.le hYn hnY
  rw [Nat.floor_natCast] at hb
  change |∑ m ∈ Finset.Ioc L n, (primeWeight m - 1 / Real.log (m : ℝ))| ≤ _ at hb ⊢
  have hlogY : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlog4 : 0 < Real.log (4 * Y) := Real.log_pos (by linarith)
  have hlogs : Real.log Y ≤ Real.log (4 * Y) := Real.log_le_log hY0 (by linarith)
  have hden : Real.log Y ^ 3 ≤ Real.log (4 * Y) ^ 3 :=
    pow_le_pow_left₀ hlogY.le hlogs 3
  have hpow : Real.log (4 * Y) ^ (3 : ℝ) = Real.log (4 * Y) ^ 3 := by norm_cast
  rw [Real.rpow_neg hlog4.le, hpow] at hb
  calc _ ≤ C * (4 * Y) * (Real.log (4 * Y) ^ 3)⁻¹ := hb
    _ ≤ max C 1 * (4 * Y) * (Real.log (4 * Y) ^ 3)⁻¹ := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) (by positivity)
    _ = (4 * max C 1) * Y / Real.log (4 * Y) ^ 3 := by ring
    _ ≤ (4 * max C 1) * Y / Real.log Y ^ 3 :=
      div_le_div_of_nonneg_left (by have := le_max_right C 1; positivity)
        (by positivity) hden

/-- P0069 page 3 display 1.8. The raw prime indicator admits no fixed constant\ncenter with every log power saving on J. This discharges the prime candidate case\nof Audit1624. It does not concern the normalized lower coefficient. -/
theorem primeWeight_not_right_conditions {ε B v : ℝ} (hε : 0 ≤ ε) :
    ¬RightConditions ε B v (fun _ => primeWeight) := by
  intro h
  obtain ⟨K, X, htrack⟩ := prime_reciprocal_tracking hε
  exact Audit1624.not_right_conditions_of_reciprocal_tracking hε h htrack

end LeanLab.BHP1997.PrimeDensity514
