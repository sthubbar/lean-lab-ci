/-
P0069, Section 5, page 51, display 5.17.
The explicit logarithmic endpoints and lower integer cutoff for the
four exponent quadrature. This reuses the proved scale estimates of
FourDensityMain517a and contains no prime number theorem input.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.FourExponentFibre517

namespace LeanLab.BHP1997.LowerShortC165
open DecompC165d

/-- Page 51 display 5.17. The integer cutoff grows by a fixed power,
its logarithmic cells cover the E4 box, and its error saves that power. -/
theorem four_exponent_scale_data {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ x : ℝ, C ≤ x →
      let L := ⌊x ^ (11/200 : ℝ) / 2⌋₊
      let N := ⌊2 * x ^ (11/20 + ε)⌋₊
      let Z := scaleZ ε x
      1 ≤ x ∧ 1 ≤ L ∧ L ≤ N ∧ 1 < Z ∧ 1 ≤ Real.log Z ∧
        (N : ℝ)+1 ≤ Z ∧
        Real.log ((L : ℝ)+1) / Real.log Z ≤ lowerFourGridReal 0 ∧
        lowerFourGridReal 128 ≤ Real.log ((N : ℝ)+1) / Real.log Z ∧
        1 / ((L : ℝ)*Real.log Z) ≤ 4 * x ^ (-(11/200) : ℝ) := by
  obtain ⟨C0, hC0⟩ := four_transfer_scales hε hε8 1 (by norm_num) 4 (by norm_num)
  refine ⟨max C0 1, le_max_right _ _, fun x hx => ?_⟩
  obtain ⟨hx1, hL4, hLN, hlog10, hidx, _, _⟩ := hC0 x ((le_max_left C0 1).trans hx)
  let L := ⌊x ^ (11/200 : ℝ) / 2⌋₊
  let N := ⌊2 * x ^ (11/20 + ε)⌋₊
  let Z := scaleZ ε x
  change 10 ≤ Real.log Z at hlog10
  have hx0 : 0 < x := by linarith
  have hY1 : 1 ≤ x ^ (11/20 + ε) := Real.one_le_rpow hx1 (by linarith)
  have hZ : 1 < Z := by dsimp [Z, scaleZ, shortY]; linarith
  have hZ0 : 0 < Z := by linarith
  have hlog : 0 < Real.log Z := Real.log_pos hZ
  have hL1 : 1 ≤ L := by
    change 4 ≤ (L : ℝ) at hL4
    have : 4 ≤ L := by exact_mod_cast hL4
    omega
  have hLp : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hfloor : (L : ℝ) ≤ x ^ (11/200 : ℝ) / 2 := Nat.floor_le (by positivity)
  have hfloor' : x ^ (11/200 : ℝ) / 2 < (L : ℝ)+1 := Nat.lt_floor_add_one _
  have hLlower : x ^ (11/200 : ℝ) / 4 ≤ (L : ℝ) := by
    change 4 ≤ (L : ℝ) at hL4
    linarith
  have hLupper : (L : ℝ)+1 ≤ x ^ (11/200 : ℝ) := by
    change 4 ≤ (L : ℝ) at hL4
    linarith
  have hNle : (N : ℝ) ≤ 2*x ^ (11/20 + ε) := Nat.floor_le (by positivity)
  have hNlt : 2*x ^ (11/20 + ε) < (N : ℝ)+1 := Nat.lt_floor_add_one _
  have hNZ : (N : ℝ)+1 ≤ Z := by dsimp [Z, scaleZ, shortY]; linarith
  have hlogZ : Real.log Z = Real.log 4 + (11/20+ε) * Real.log x := by
    dsimp [Z, scaleZ, shortY]
    rw [Real.log_mul (by norm_num) (Real.rpow_pos_of_pos hx0 _).ne', Real.log_rpow hx0]
  have hlo : Real.log ((L : ℝ)+1) / Real.log Z ≤ lowerFourGridReal 0 := by
    have hl := Real.log_le_log (by positivity : (0 : ℝ) < (L : ℝ)+1) hLupper
    rw [Real.log_rpow hx0] at hl
    have hlogx : 0 ≤ Real.log x := Real.log_nonneg hx1
    have hlog4 : 0 ≤ Real.log (4 : ℝ) := Real.log_nonneg (by norm_num)
    have halpha : Real.log ((L : ℝ)+1) / Real.log Z ≤ (1/10 : ℝ) := by
      apply (div_le_iff₀ hlog).mpr
      rw [hlogZ]
      nlinarith [mul_nonneg hε.le hlogx]
    exact halpha.trans (by norm_num [lowerFourGridReal, lowerFourGridPoint])
  have hhi : lowerFourGridReal 128 ≤ Real.log ((N : ℝ)+1) / Real.log Z := by
    have hlarge := Real.log_le_log
      (by positivity : (0 : ℝ) < 2*x ^ (11/20 + ε)) hNlt.le
    have heq : 2*x ^ (11/20 + ε) = Z/2 := by dsimp [Z, scaleZ, shortY]; ring
    rw [heq, Real.log_div hZ0.ne' (by norm_num)] at hlarge
    have hl2 : Real.log (2 : ℝ) ≤ 1 := by linarith [Real.log_two_lt_d9]
    apply (le_div_iff₀ hlog).mpr
    norm_num [lowerFourGridReal, lowerFourGridPoint]
    change 10 ≤ Real.log Z at hlog10
    nlinarith
  have herr : 1 / ((L : ℝ)*Real.log Z) ≤ 4*x ^ (-(11/200) : ℝ) := by
    have hp : 0 < x ^ (11/200 : ℝ) := Real.rpow_pos_of_pos hx0 _
    have h1 : 1 / (L : ℝ) ≤ 4 / x ^ (11/200 : ℝ) :=
      (div_le_div_iff₀ hLp hp).mpr (by linarith)
    have h2 : (L : ℝ) ≤ (L : ℝ)*Real.log Z := by
      change 10 ≤ Real.log Z at hlog10
      nlinarith
    calc _ ≤ 1 / (L : ℝ) := one_div_le_one_div_of_le hLp h2
      _ ≤ 4 / x ^ (11/200 : ℝ) := h1
      _ = _ := by rw [Real.rpow_neg hx0.le]; rfl
  exact ⟨hx1, hL1, hLN, hZ, by linarith, hNZ, hlo, hhi, herr⟩

#print axioms four_exponent_scale_data
end LeanLab.BHP1997.LowerShortC165
