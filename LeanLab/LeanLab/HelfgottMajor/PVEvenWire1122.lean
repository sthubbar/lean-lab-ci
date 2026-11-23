import Mathlib
import LeanLab.HelfgottMajor.PVCotIdentity1122

/-!
Route burst S68, burst-20261122, tag pv-even-wire.
Wiring of the S68 proof `PVCotIdentity1122.cot_identity` into the even case of Pomerance 2011
Theorem 1, Frolenkov arXiv 1107.0381 displays 12 to 17 and display 1. `PVEvenTrunc1122` and
`PVCases1122` cannot be edited, so their proofs of `initial_le_cot_sum`, `even_truncated` and
`pomerance_even_case` are repeated here verbatim with the LEAF `cot_identity` replaced by its
PROVED twin. The even case then rests only on the HARD LEAF `PVEvenTrunc1122.cot_tail`.
No new sorry.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVEvenWire1122

open Real Finset
open LeanLab.HelfgottMajor.PVEvenTrunc1122 (norm_gauss_inv cot_head cot_tail)
open LeanLab.HelfgottMajor.PVCases1122 (interval_le_two_initial even_initial)

/-- From the exact identity and `|τ(χ⁻¹)| = √q`: `|S(K)| ≤ |∑_h …|/(2√q) + 1/2`. PROVED, with the PROVED
twin of `cot_identity`. -/
theorem initial_le_cot_sum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (heven : χ (-1) = 1) (K : ℕ) :
    ‖∑ m ∈ range K, χ (m : ZMod q)‖ ≤
      ‖∑ h : ZMod q, χ⁻¹ h *
        ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)‖ /
        (2 * sqrt q) + 1 / 2 := by
  have hid := LeanLab.HelfgottMajor.PVCotIdentity1122.cot_identity χ hχ hq heven K
  have hn := congrArg norm hid
  rw [norm_mul, norm_gauss_inv hχ] at hn
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hs : 0 < sqrt (q : ℝ) := sqrt_pos.mpr hq0
  have hc : ‖χ (K : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
  set S := ∑ m ∈ range K, χ (m : ZMod q)
  set T := ∑ h : ZMod q, χ⁻¹ h *
        ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)
  have h2 : ‖(2 : ℂ) * S‖ ≤ ‖2 * S + χ (K : ZMod q)‖ + ‖χ (K : ZMod q)‖ := by
    have := norm_sub_le (2 * S + χ (K : ZMod q)) (χ (K : ZMod q))
    simpa using this
  rw [norm_mul] at h2
  have h22 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [h22] at h2
  have key : ‖2 * S + χ (K : ZMod q)‖ = ‖T‖ / sqrt q := by
    rw [eq_div_iff hs.ne', mul_comm]; exact hn
  rw [key] at h2
  have : ‖T‖ / (2 * sqrt q) = (‖T‖ / sqrt q) / 2 := by field_simp
  rw [this]
  linarith

/-- Assembly: exactly `PVCases1122.even_truncated`, from the PROVED twin of `cot_identity`, the PROVED `cot_head`
and the HARD LEAF `cot_tail`, on which alone it rests. -/
theorem even_truncated {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (heven : χ (-1) = 1) :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ K : ℕ,
      ‖∑ m ∈ range K, χ (m : ZMod q)‖ ≤
        sqrt q / π * ∑ j ∈ Icc 1 H, |sin (j * (2 * π * K / q))| / j +
        (1 / π ^ 2 * sqrt q * log q + 2 / π ^ 2 * sqrt q * log (log q) + 3 / 4 * sqrt q -
          2 / π ^ 2 * sqrt q * (log H + eulerMascheroniConstant + log 2 + 3 / H)) := by
  obtain ⟨H, hH, hHq, htail⟩ := cot_tail χ hχ hq heven
  refine ⟨H, hH, fun K => ?_⟩
  have h1 := initial_le_cot_sum χ hχ hq heven K
  have h2 := cot_head χ hχ hq heven H hH hHq K
  have h3 := htail K
  have hsplit := (sum_filter_add_sum_filter_not univ
    (fun h : ZMod q => h.val ≤ H ∨ q - H ≤ h.val)
    (fun h : ZMod q => χ⁻¹ h *
        ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ)))
  have htri := norm_add_le
    (∑ h ∈ univ.filter (fun h : ZMod q => h.val ≤ H ∨ q - H ≤ h.val), χ⁻¹ h *
        ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ))
    (∑ h ∈ univ.filter (fun h : ZMod q => ¬ (h.val ≤ H ∨ q - H ≤ h.val)), χ⁻¹ h *
        ((cot (π * (h.val : ℝ) / q) * sin (2 * π * K * (h.val : ℝ) / q) : ℝ) : ℂ))
  rw [hsplit] at htri
  have hq0 : (0 : ℝ) < q := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne q)
  have hd : 0 < 2 * sqrt (q : ℝ) := by positivity
  have hdiv := div_le_div_of_nonneg_right htri hd.le
  rw [add_div] at hdiv
  linarith

example : type_of% @even_truncated =
    type_of% @LeanLab.HelfgottMajor.PVCases1122.even_truncated := rfl

/-- Assembly: exactly `PV420Split1122.pomerance_even_case`, from `interval_le_two_initial`,
`even_initial` and the wired `even_truncated` above. -/
theorem pomerance_even_case {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1)
    (hL3 : ∀ (x : ℝ) (n : ℕ), 1 ≤ n → ∑ j ∈ Icc 1 n, |sin (j * x)| / j <
      2 / π * log n + 2 / π * (eulerMascheroniConstant + log 2 + 3 / n))
    (hG : ∀ n : ZMod q, χ⁻¹ n * gaussSum χ ZMod.stdAddChar = ∑ x : ZMod q, χ x *
      ((ZMod.stdAddChar (n * x) + ZMod.stdAddChar (-(n * x))) / 2))
    (hτ : ‖gaussSum χ ZMod.stdAddChar‖ = sqrt q)
    (heven : χ (-1) = 1) (M N : ℕ) :
    ‖∑ m ∈ Icc M N, χ (m : ZMod q)‖ ≤
      2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q := by
  have htr := even_truncated χ hχ hq heven
  have a := even_initial χ hL3 htr (N + 1)
  have b := even_initial χ hL3 htr M
  have c := interval_le_two_initial χ M N
  have e : 2 * (1 / π ^ 2 * sqrt q * log q + 2 / π ^ 2 * sqrt q * log (log q) + 3 / 4 * sqrt q) =
      2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q := by ring
  linarith

example : type_of% @pomerance_even_case =
    type_of% @LeanLab.HelfgottMajor.PV420Split1122.pomerance_even_case := rfl

end LeanLab.HelfgottMajor.PVEvenWire1122

#print axioms LeanLab.HelfgottMajor.PVEvenWire1122.initial_le_cot_sum
#print axioms LeanLab.HelfgottMajor.PVEvenWire1122.even_truncated
#print axioms LeanLab.HelfgottMajor.PVEvenWire1122.pomerance_even_case
