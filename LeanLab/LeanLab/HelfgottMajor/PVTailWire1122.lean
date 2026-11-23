import Mathlib
import LeanLab.HelfgottMajor.PV420Wire1122
import LeanLab.HelfgottMajor.PVCotTail1122
import LeanLab.HelfgottMajor.PVOddLarge1122

/-!
Route burst S75, burst-20261122, tag tail-wire.
Wiring of the S75 splits `PVCotTail1122.cot_tail` and `PVOddLarge1122.odd_truncated_large`, along
Pomerance 2011 Lemma 4, display 5 and Sections 3 and 4, into P0014 page 36 display 4.20. The
proofs of `PVEvenWire1122.even_truncated`, `PVEvenWire1122.pomerance_even_case`,
`PVOddChainWire1122.odd_truncated`, `PVOddChainWire1122.pomerance_odd_case` and
`PV420Wire1122.polya_vinogradov_4_20` are repeated here verbatim with the two HARD LEAFs replaced
by the S75 assemblies, since existing files cannot be edited. No new sorry; what remains open is
the set of smaller LEAFs of `PVTailAbel1122`, `PVCotTail1122` and `PVOddLarge1122`.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVTailWire1122

open Real Finset
open LeanLab.HelfgottMajor.PVEvenTrunc1122 (norm_gauss_inv cot_head)
open LeanLab.HelfgottMajor.PVCases1122 (interval_le_two_initial even_initial)

/-- Assembly: exactly `PVCases1122.even_truncated`, from the PROVED twin of `cot_identity`, the PROVED `cot_head`
and `PVCotTail1122.cot_tail`, the S75 split of the HARD LEAF `PVEvenTrunc1122.cot_tail`. -/
theorem even_truncated {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) (heven : χ (-1) = 1) :
    ∃ H : ℕ, 1 ≤ H ∧ ∀ K : ℕ,
      ‖∑ m ∈ range K, χ (m : ZMod q)‖ ≤
        sqrt q / π * ∑ j ∈ Icc 1 H, |sin (j * (2 * π * K / q))| / j +
        (1 / π ^ 2 * sqrt q * log q + 2 / π ^ 2 * sqrt q * log (log q) + 3 / 4 * sqrt q -
          2 / π ^ 2 * sqrt q * (log H + eulerMascheroniConstant + log 2 + 3 / H)) := by
  obtain ⟨H, hH, hHq, htail⟩ := LeanLab.HelfgottMajor.PVCotTail1122.cot_tail χ hχ hq heven
  refine ⟨H, hH, fun K => ?_⟩
  have h1 := LeanLab.HelfgottMajor.PVEvenWire1122.initial_le_cot_sum χ hχ hq heven K
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

/-- Assembly: exactly `PVCases1122.odd_truncated`. For q ≤ 1000, H = (q-1)/2 with
`odd_full_bound` and `remainder_ge_one`; for q > 1000, `PVOddLarge1122.odd_truncated_large`, the S75 split of the HARD LEAF. -/
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
    have a := LeanLab.HelfgottMajor.PVOddChainWire1122.odd_full_bound χ hχ hq7 hodd M N
    have b := LeanLab.HelfgottMajor.PVOddTrunc1122.remainder_ge_one hq7 hQ
    linarith
  · exact LeanLab.HelfgottMajor.PVOddLarge1122.odd_truncated_large χ hχ (by omega) hodd

example : type_of% @odd_truncated =
    type_of% @LeanLab.HelfgottMajor.PVCases1122.odd_truncated := rfl


/-- Assembly: exactly `PV420Split1122.pomerance_odd_case`, P0014 page 36 display 4.20 odd case,
from `PVCases1122.odd_from_truncated`, the wired `odd_truncated` above for q at least 7, and
the PROVED `odd_small` below 7. Rests only on `PVOddLarge1122.odd_truncated_large`. -/
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


open Real Finset

/-- P0014 page 36 display 4.20, exactly the sealed `PolyaVinogradov123.polya_vinogradov_4_20`,
resting on the S75 splits `PVCotTail1122.cot_tail` and `PVOddLarge1122.odd_truncated_large`. -/
theorem polya_vinogradov_4_20 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) :
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      if χ (-1) = 1 then
        2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q
      else
        1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  refine ciSup_le fun n => ?_
  split_ifs with h
  · exact pomerance_even_case χ hχ hq
      LeanLab.HelfgottMajor.PVLemmasWire1122.pomerance_lemma3
      (LeanLab.HelfgottMajor.PV420Split1122.gauss_twist_even hχ h)
      (LeanLab.HelfgottMajor.PV420Split1122.norm_gauss hχ) h 1 n
  · exact pomerance_odd_case χ hχ hq
      LeanLab.HelfgottMajor.PVLemmasWire1122.pomerance_sec4
      (LeanLab.HelfgottMajor.PV420Split1122.gauss_twist_odd hχ h)
      (LeanLab.HelfgottMajor.PV420Split1122.norm_gauss hχ) h 1 n

example : type_of% @polya_vinogradov_4_20 =
    type_of% @LeanLab.HelfgottMajor.PolyaVinogradov123.polya_vinogradov_4_20 := rfl

end LeanLab.HelfgottMajor.PVTailWire1122

#print axioms LeanLab.HelfgottMajor.PVTailWire1122.even_truncated
#print axioms LeanLab.HelfgottMajor.PVTailWire1122.pomerance_even_case
#print axioms LeanLab.HelfgottMajor.PVTailWire1122.odd_truncated
#print axioms LeanLab.HelfgottMajor.PVTailWire1122.pomerance_odd_case
#print axioms LeanLab.HelfgottMajor.PVTailWire1122.polya_vinogradov_4_20
