import Mathlib
import LeanLab.HelfgottMajor.PVCosLower1122
import LeanLab.HelfgottMajor.PVSec4Core1122
import LeanLab.HelfgottMajor.PVAbsSinFourier1122

/-!
Route burst S68, burst-20261122, tag pv-lemmas-wire.
Wiring of the S68 proofs of the three LEAFs of `PVLemmas1122` into the two round one LEAFs
`PV420Split1122.pomerance_lemma3` and `PV420Split1122.pomerance_sec4`, Pomerance 2011 Lemma 3 and
Section 4, quoted as Lemmas 1 and 2 of Frolenkov arXiv 1107.0381, and into the assembly of
P0014 page 36 display 4.20.

`PVLemmas1122` cannot be edited, so its proofs of `sin_sum_le`, `pomerance_lemma3` and
`pomerance_sec4` are repeated here verbatim with the LEAFs replaced by their PROVED twins
`PVAbsSinFourier1122.abs_sin_fourier`, `PVCosLower1122.cos_partial_lower` and
`PVSec4Core1122.sec4_core_of_cos`. No new sorry.

AI wrote this Lean code. Binary Goldbach is open.
-/

namespace LeanLab.HelfgottMajor.PVLemmasWire1122

open Real Finset Filter Topology
open LeanLab.HelfgottMajor.PVLemmas1122 (harmonic_lt series_quarter)

/-- Partial summation step of Pomerance Lemma 3, the proof of `PVLemmas1122.sin_sum_le` with the
PROVED Fourier series of the absolute sine and the PROVED cosine lower bound. -/
theorem sin_sum_le (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Icc 1 n, |sin (j * x)| / j ≤
      2 / π * ∑ j ∈ Icc 1 n, (1 : ℝ) / j + 2 / π * (log 2 + 2 / n) := by
  set c : ℝ := log 2 + 2 / n
  set f : ℕ → ℝ → ℝ := fun k t =>
    4 / π * (cos (2 * ((k : ℝ) + 1) * t) / (4 * ((k : ℝ) + 1) ^ 2 - 1)) with hf
  have hT : HasSum (fun k : ℕ => ∑ j ∈ Icc 1 n, f k (j * x) / j)
      (∑ j ∈ Icc 1 n, (2 / π - |sin (j * x)|) / j) :=
    hasSum_sum fun j _ =>
      (LeanLab.HelfgottMajor.PVAbsSinFourier1122.abs_sin_fourier (j * x)).div_const _
  have hL : HasSum (fun k : ℕ => 4 / π * (-c) * (1 / (4 * ((k : ℝ) + 1) ^ 2 - 1)))
      (4 / π * (-c) * (1 / 2)) := series_quarter.mul_left _
  have hle : ∀ k : ℕ, 4 / π * (-c) * (1 / (4 * ((k : ℝ) + 1) ^ 2 - 1)) ≤
      ∑ j ∈ Icc 1 n, f k (j * x) / j := by
    intro k
    have hd : (0 : ℝ) < 4 * ((k : ℝ) + 1) ^ 2 - 1 := by nlinarith [(k.cast_nonneg : (0:ℝ) ≤ k)]
    have hrw : ∑ j ∈ Icc 1 n, f k (j * x) / j =
        4 / π * (1 / (4 * ((k : ℝ) + 1) ^ 2 - 1)) *
          ∑ j ∈ Icc 1 n, cos (j * (2 * ((k : ℝ) + 1) * x)) / j := by
      rw [mul_sum]; refine sum_congr rfl fun j _ => ?_
      simp only [hf]
      have : 2 * ((k : ℝ) + 1) * (j * x) = j * (2 * ((k : ℝ) + 1) * x) := by ring
      rw [this]; ring
    rw [hrw]
    have hcl := LeanLab.HelfgottMajor.PVCosLower1122.cos_partial_lower
      (2 * ((k : ℝ) + 1) * x) n hn
    have hpos : 0 ≤ 4 / π * (1 / (4 * ((k : ℝ) + 1) ^ 2 - 1)) := by
      have := Real.pi_pos; positivity
    nlinarith
  have hbound := hasSum_le hle hL hT
  have hsplit : ∑ j ∈ Icc 1 n, (2 / π - |sin (j * x)|) / j =
      2 / π * ∑ j ∈ Icc 1 n, (1 : ℝ) / j - ∑ j ∈ Icc 1 n, |sin (j * x)| / j := by
    rw [mul_sum, ← sum_sub_distrib]; refine sum_congr rfl fun j _ => ?_; ring
  rw [hsplit] at hbound
  have e : 4 / π * (-c) * (1 / 2) = -(2 / π * c) := by ring
  linarith

/-- Pomerance 2011 Lemma 3, exactly the round one LEAF `PV420Split1122.pomerance_lemma3`. PROVED. -/
theorem pomerance_lemma3 (x : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ Icc 1 n, |sin (j * x)| / j <
      2 / π * log n + 2 / π * (eulerMascheroniConstant + log 2 + 3 / n) := by
  have h1 := sin_sum_le x n hn
  have h2 := harmonic_lt n hn
  have hp : 0 < 2 / π := by have := Real.pi_pos; positivity
  have h3 : 2 / π * ∑ j ∈ Icc 1 n, (1 : ℝ) / j <
      2 / π * (log n + eulerMascheroniConstant + 1 / n) := mul_lt_mul_of_pos_left h2 hp
  have e : (3 : ℝ) / n = 1 / n + 2 / n := by ring
  rw [e]; nlinarith

example : type_of% @pomerance_lemma3 =
    type_of% @LeanLab.HelfgottMajor.PV420Split1122.pomerance_lemma3 := rfl

/-- Pomerance 2011 Section 4, exactly the round one LEAF `PV420Split1122.pomerance_sec4`. PROVED. -/
theorem pomerance_sec4 (α β : ℝ) (n : ℕ) (hn : 1 ≤ n) :
    ∑ m ∈ Icc 1 n, |cos (m * α) - cos (m * β)| / m <
      log n + eulerMascheroniConstant + log 2 + 3 / n := by
  have h1 := LeanLab.HelfgottMajor.PVSec4Core1122.sec4_core_of_cos
    LeanLab.HelfgottMajor.PVCosLower1122.cos_partial_lower α β n hn
  have h2 := harmonic_lt n hn
  have e : (3 : ℝ) / n = 1 / n + 2 / n := by ring
  rw [e]; linarith

example : type_of% @pomerance_sec4 =
    type_of% @LeanLab.HelfgottMajor.PV420Split1122.pomerance_sec4 := rfl

/-- P0014 page 36 display 4.20, the assembly of `PV420Split1122.polya_vinogradov_4_20` with the
PROVED Lemma 3 and Section 4 above; it rests only on the case LEAFs
`PV420Split1122.pomerance_even_case` and `pomerance_odd_case`. -/
theorem polya_vinogradov_4_20 {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (hχ : χ.IsPrimitive) (hq : q ≠ 1) :
    (⨆ n : ℕ, ‖∑ m ∈ Finset.Icc 1 n, χ (m : ZMod q)‖) ≤
      if χ (-1) = 1 then
        2 / π ^ 2 * sqrt q * log q + 4 / π ^ 2 * sqrt q * log (log q) + 3 / 2 * sqrt q
      else
        1 / (2 * π) * sqrt q * log q + 1 / π * sqrt q * log (log q) + sqrt q := by
  open LeanLab.HelfgottMajor.PV420Split1122 in
  refine ciSup_le fun n => ?_
  open LeanLab.HelfgottMajor.PV420Split1122 in
  split_ifs with h
  · exact LeanLab.HelfgottMajor.PV420Split1122.pomerance_even_case χ hχ hq pomerance_lemma3
      (LeanLab.HelfgottMajor.PV420Split1122.gauss_twist_even hχ h)
      (LeanLab.HelfgottMajor.PV420Split1122.norm_gauss hχ) h 1 n
  · exact LeanLab.HelfgottMajor.PV420Split1122.pomerance_odd_case χ hχ hq pomerance_sec4
      (LeanLab.HelfgottMajor.PV420Split1122.gauss_twist_odd hχ h)
      (LeanLab.HelfgottMajor.PV420Split1122.norm_gauss hχ) h 1 n

example : type_of% @polya_vinogradov_4_20 =
    type_of% @LeanLab.HelfgottMajor.PolyaVinogradov123.polya_vinogradov_4_20 := rfl

end LeanLab.HelfgottMajor.PVLemmasWire1122

#print axioms LeanLab.HelfgottMajor.PVLemmasWire1122.sin_sum_le
#print axioms LeanLab.HelfgottMajor.PVLemmasWire1122.pomerance_lemma3
#print axioms LeanLab.HelfgottMajor.PVLemmasWire1122.pomerance_sec4
#print axioms LeanLab.HelfgottMajor.PVLemmasWire1122.polya_vinogradov_4_20
