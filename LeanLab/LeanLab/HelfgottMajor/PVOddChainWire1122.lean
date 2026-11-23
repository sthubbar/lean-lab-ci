import Mathlib
import LeanLab.HelfgottMajor.PVOddFold1122
import LeanLab.HelfgottMajor.PVOddSmall1122

/-!
Route burst S68, burst-20261122, tag pv420-wire, odd chain.
Pomerance 2011 Theorem 1 odd case, Frolenkov arXiv 1107.0381 displays 12 to 22. The proofs of
`PVOddCotBound1122.odd_cot_bound`, `PVOddTrunc1122.odd_full_bound`, `PVOddTrunc1122.odd_truncated`
and `PVOddWire1122.pomerance_odd_case` are repeated here with every LEAF that has a PROVED twin
replaced by it: `cot_sum_fold` by `PVOddFold1122.cot_sum_fold` and `odd_cot_bound` by the copy
below. The chain then rests only on the HARD LEAF `PVOddTrunc1122.odd_truncated_large`.
Existing files cannot be edited, hence the copies. No new sorry.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVOddChainWire1122

open Real Finset

/-- Exactly `PVOddTrunc1122.odd_cot_bound`, from `PVOddCot1122.polya_interval_cot`,
|τ(χ⁻¹)| = √q, |χ| ≤ 1, and the PROVED twin `PVOddFold1122.cot_sum_fold`. PROVED. -/
theorem odd_cot_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq7 : 7 ≤ q) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 + 1 / sqrt q * ∑ m ∈ Icc 1 ((q - 1) / 2),
        Real.cot (π * m / q) * |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| := by
  set T := ∑ m ∈ Icc 1 ((q - 1) / 2),
    Real.cot (π * m / q) * |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| with hT
  have hT0 : 0 ≤ T := LeanLab.HelfgottMajor.PVOddCotBound1122.fold_nonneg M N
  have hsq : 0 < sqrt (q : ℝ) := sqrt_pos.mpr (by exact_mod_cast (show 0 < q by omega))
  by_cases hMN : M ≤ N + 1
  · have hid := LeanLab.HelfgottMajor.PVOddCot1122.polya_interval_cot hχ (by omega) hMN
    have hτ := LeanLab.HelfgottMajor.PV420Split1122.norm_gauss
      (LeanLab.HelfgottMajor.PVEvenPolya1122.isPrimitive_inv hχ)
    have hF := LeanLab.HelfgottMajor.PVOddFold1122.cot_sum_fold χ hq7 hodd M N
    set τ := gaussSum χ⁻¹ ZMod.stdAddChar
    set S := ∑ m ∈ Icc M N, χ (m : ZMod q)
    set F := ∑ h : ZMod q, χ⁻¹ h * (Real.cot (π * h.val / q) : ℂ) *
        (ZMod.stdAddChar h ^ (N + 1) - ZMod.stdAddChar h ^ M)
    have h1 : ‖χ ((N + 1 : ℕ) : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
    have h2 : ‖χ (M : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one _ _
    have hn : ‖τ * S‖ ≤ ‖τ‖ + 1 / 2 * ‖F‖ := by
      rw [hid]
      calc ‖-(1 / 2) * τ * (χ ((N + 1 : ℕ) : ZMod q) - χ (M : ZMod q)) - Complex.I / 2 * F‖
          ≤ ‖-(1 / 2) * τ * (χ ((N + 1 : ℕ) : ZMod q) - χ (M : ZMod q))‖ +
            ‖Complex.I / 2 * F‖ := norm_sub_le _ _
        _ ≤ 1 / 2 * ‖τ‖ * (‖χ ((N + 1 : ℕ) : ZMod q)‖ + ‖χ (M : ZMod q)‖) + 1 / 2 * ‖F‖ := by
          gcongr
          · rw [norm_mul, norm_mul, norm_neg]
            gcongr
            · simp
            · exact norm_sub_le _ _
          · rw [norm_mul, norm_div, Complex.norm_I]; simp
        _ ≤ ‖τ‖ + 1 / 2 * ‖F‖ := by nlinarith [norm_nonneg τ]
    rw [norm_mul, hτ] at hn
    have : sqrt q * ‖S‖ ≤ sqrt q * (1 + 1 / sqrt q * T) := by
      rw [mul_add, mul_one, ← mul_assoc, mul_one_div_cancel hsq.ne', one_mul]
      linarith
    exact le_of_mul_le_mul_left this hsq
  · have he : Icc M N = ∅ := Finset.Icc_eq_empty (by omega)
    rw [he, sum_empty, norm_zero]
    have : 0 ≤ 1 / sqrt (q : ℝ) * T := mul_nonneg (by positivity) hT0
    linarith

example : type_of% @odd_cot_bound =
    type_of% @LeanLab.HelfgottMajor.PVOddTrunc1122.odd_cot_bound := rfl

/-- The full length expansion: `odd_cot_bound` with cot(π h/q) ≤ q/(π h) from `cot_le`, the
form of Frolenkov display 22 before truncation. PROVED, with the PROVED `odd_cot_bound` above. -/
theorem odd_full_bound {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq7 : 7 ≤ q) (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 + sqrt q / π * ∑ m ∈ Icc 1 ((q - 1) / 2),
        |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| / m := by
  refine (odd_cot_bound χ hχ hq7 hodd M N).trans ?_
  have hsq : 0 < sqrt (q : ℝ) := sqrt_pos.mpr (by exact_mod_cast (show 0 < q by omega))
  have hqq : (q : ℝ) = sqrt q * sqrt q := (mul_self_sqrt (Nat.cast_nonneg q)).symm
  gcongr 1 + ?_
  rw [mul_sum, mul_sum]
  refine sum_le_sum fun m hm => ?_
  rw [mem_Icc] at hm
  have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm.1
  have h2 : 2 * m < q := by omega
  have hc := LeanLab.HelfgottMajor.PVOddTrunc1122.cot_le hm.1 h2
  set c := |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))|
  have hc0 : 0 ≤ c := abs_nonneg _
  have hmpos : (0 : ℝ) < m := by linarith
  calc 1 / sqrt q * (Real.cot (π * m / q) * c) ≤ 1 / sqrt q * (q / (π * m) * c) := by
        gcongr
    _ = sqrt q / π * (c / m) := by
        have hs2 : sqrt (q : ℝ) ^ 2 = q := sq_sqrt (Nat.cast_nonneg q)
        field_simp
        first
          | (rw [hs2])
          | (rw [← hs2]; ring)
          | (nlinarith [hs2])
          | (simp [hs2])

/-- Assembly: exactly `PVCases1122.odd_truncated`. For q ≤ 1000, H = (q-1)/2 with
`odd_full_bound` and `remainder_ge_one`; for q > 1000, the HARD LEAF `PVOddTrunc1122.odd_truncated_large`, on which alone it rests. -/
theorem odd_truncated {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq7 : 7 ≤ q) (hodd : χ (-1) ≠ 1) :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ M N : ℕ,
      ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
        sqrt q / π * ∑ m ∈ Icc 1 H,
          |cos (m * (2 * π * M / q)) - cos (m * (2 * π * (N + 1) / q))| / m +
        (1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q -
          sqrt q / π * (log H + eulerMascheroniConstant + log 2 + 3 / H)) := by
  by_cases hQ : q ≤ 1000
  · refine ⟨(q - 1) / 2, by omega, fun M N => ?_⟩
    have a := odd_full_bound χ hχ hq7 hodd M N
    have b := LeanLab.HelfgottMajor.PVOddTrunc1122.remainder_ge_one hq7 hQ
    linarith
  · exact LeanLab.HelfgottMajor.PVOddTrunc1122.odd_truncated_large χ hχ (by omega) hodd

example : type_of% @odd_truncated =
    type_of% @LeanLab.HelfgottMajor.PVCases1122.odd_truncated := rfl

/-- Assembly: exactly `PV420Split1122.pomerance_odd_case`, P0014 page 36 display 4.20 odd case,
from `PVCases1122.odd_from_truncated`, the wired `odd_truncated` above for q at least 7, and
the PROVED `odd_small` below 7. Rests only on `PVOddTrunc1122.odd_truncated_large`. -/
theorem pomerance_odd_case {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1)
    (hS4 : ∀ (α β : ℝ) (n : ℕ), 1 ≤ n → ∑ m ∈ Icc 1 n, |cos (m * α) - cos (m * β)| / m <
      log n + eulerMascheroniConstant + log 2 + 3 / n)
    (hG : ∀ n : ZMod q, χ⁻¹ n * gaussSum χ ZMod.stdAddChar = ∑ x : ZMod q, χ x *
      ((ZMod.stdAddChar (n * x) - ZMod.stdAddChar (-(n * x))) / 2))
    (hτ : ‖gaussSum χ ZMod.stdAddChar‖ = sqrt q)
    (hodd : χ (-1) ≠ 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q :=
  if h7 : 7 ≤ q then
    LeanLab.HelfgottMajor.PVCases1122.odd_from_truncated χ hS4
      (odd_truncated χ hχ h7 hodd) M N
  else LeanLab.HelfgottMajor.PVOddSmall1122.odd_small χ hχ hq (by omega) hodd M N

example : type_of% @pomerance_odd_case =
    type_of% @LeanLab.HelfgottMajor.PV420Split1122.pomerance_odd_case := rfl

end LeanLab.HelfgottMajor.PVOddChainWire1122

#print axioms LeanLab.HelfgottMajor.PVOddChainWire1122.odd_cot_bound
#print axioms LeanLab.HelfgottMajor.PVOddChainWire1122.odd_full_bound
#print axioms LeanLab.HelfgottMajor.PVOddChainWire1122.odd_truncated
#print axioms LeanLab.HelfgottMajor.PVOddChainWire1122.pomerance_odd_case
