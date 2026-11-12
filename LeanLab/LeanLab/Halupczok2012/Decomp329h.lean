import LeanLab.Halupczok2012.Decomp329f

/-!
Nonvacuity checks for the interval packing input.
Source: the interval convention in Halupczok page 332 and the count on page 345.
The model predicate counts every natural number.
This verifies consistency of the generic packing hypotheses.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp329h

open scoped Classical

/-- Halupczok's half open interval convention gives at least H minus one integers. -/
theorem window_card_lower {X H : ℝ} (hX : 0 ≤ X) (hH : 0 ≤ H) :
    H - 1 ≤ ((kRange X H).card : ℝ) := by
  have he : kRange X H = Finset.Ioc ⌊X⌋₊ ⌊X + H⌋₊ := by
    ext k
    rw [Fourier398.window_mem, Finset.mem_Ioc, Nat.floor_lt hX,
      Nat.le_floor_iff (by linarith : 0 ≤ X + H)]
  have hfloor : ⌊X⌋₊ ≤ ⌊X + H⌋₊ := Nat.floor_mono (by linarith)
  rw [he, Nat.card_Ioc, Nat.cast_sub hfloor]
  have hleft := Nat.floor_le hX
  have hright := Nat.lt_floor_add_one (X + H)
  linarith

/-- The packing input has a positive constant and an unbounded concrete model.
Use theta one, threshold four and the predicate counting every natural number. -/
theorem packing_input_nonvacuous :
    0 < (Real.log 4) ^ 2 / 4 ∧
    ∀ X : ℝ, 4 ≤ X → 2 ≤ X →
      ((Real.log 4) ^ 2 / 4) * X ^ (1 : ℝ) / (Real.log X) ^ 2 ≤
        (((kRange X (X ^ (1 : ℝ))).filter (fun _ => True)).card : ℝ) := by
  have hL4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  refine ⟨by positivity, ?_⟩
  intro X hX hX2
  have hXp : 0 < X := by linarith
  have hlog : Real.log 4 ≤ Real.log X := Real.log_le_log (by norm_num) hX
  have hLX : 0 < Real.log X := hL4.trans_le hlog
  have hsq : (Real.log 4) ^ 2 ≤ (Real.log X) ^ 2 :=
    pow_le_pow_left₀ hL4.le hlog 2
  have hbound : ((Real.log 4) ^ 2 / 4) * X / (Real.log X) ^ 2 ≤ X / 4 := by
    apply (div_le_iff₀ (by positivity : 0 < (Real.log X) ^ 2)).mpr
    have hmul := mul_le_mul_of_nonneg_right hsq (show 0 ≤ X / 4 by positivity)
    nlinarith
  have hcard := window_card_lower (X := X) (H := X) hXp.le hXp.le
  simp only [Real.rpow_one, Finset.filter_true]
  exact hbound.trans (by linarith)

end LeanLab.Halupczok2012.Decomp329h
