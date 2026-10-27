/-
P0095 Lu 2010, page 2391, the estimate quoted from reference 12 page 107.
CODEX task47, unit U-8094. AI wrote this Lean code. Binary Goldbach is open.

The lab's proved Vaughan bound is stronger than Lu's quoted bound.
This file translates the sum conventions and absorbs its fourth log power.
-/
import LeanLab.ExceptionalSet.Lu2010Dirichlet
import LeanLab.PNTPort.Vinogradov.Final

namespace LeanLab.ExceptionalSet.Lu2010Bound12
open Finset Real
open LeanLab.ExceptionalSet.Lu2010Orth
open LeanLab.ExceptionalSet.Lu2010Dirichlet

theorem ee_eq_e (x : ℝ) : ee x = LeanLab.PNTPort.LargeSieve.e x := by
  unfold ee LeanLab.PNTPort.LargeSieve.e
  congr 1
  push_cast
  ring

/-- Lu's real cutoff sum equals the lab's integer cutoff sum at its floor. -/
theorem Ssum_eq_S (x α : ℝ) :
    Ssum x 0 α = LeanLab.PNTPort.Vinogradov.S ⌊x⌋₊ α := by
  classical
  unfold Ssum LeanLab.PNTPort.Vinogradov.S
  rw [← sum_filter]
  have hs : (range (⌊x⌋₊ + 1)).filter (fun n : ℕ => (0 : ℝ) < n ∧ (n : ℝ) ≤ x) =
      Icc 1 ⌊x⌋₊ := by
    ext n
    simp only [mem_filter, mem_range, mem_Icc]
    constructor
    · rintro ⟨hn, hp, _⟩
      constructor
      · exact_mod_cast (show (1 : ℕ) ≤ n by exact Nat.one_le_iff_ne_zero.mpr (by intro hn0; simp [hn0] at hp))
      · omega
    · rintro ⟨h1, hn⟩
      have hx : 0 ≤ x := by
        by_contra hx
        have : ⌊x⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
        omega
      exact ⟨by omega, by exact_mod_cast (show 0 < n by omega), (Nat.le_floor_iff hx).mp hn⟩
  rw [hs]
  apply sum_congr rfl
  intro n _
  rw [ee_eq_e]

/-- A global log-power estimate, with a concrete constant for every positive epsilon. -/
theorem log_four_bound {ε x : ℝ} (hε : 0 < ε) (hx : 1 ≤ x) :
    (1 + Real.log x) ^ 4 ≤ (1 + 4 / ε) ^ 4 * x ^ ε := by
  have hx0 : 0 < x := by linarith
  have hδ : 0 < ε / 4 := by positivity
  have hlog := Real.log_le_rpow_div hx0.le hδ
  have hpow : 1 ≤ x ^ (ε / 4) := Real.one_le_rpow hx hδ.le
  have h : 1 + Real.log x ≤ (1 + 4 / ε) * x ^ (ε / 4) := by
    have he : x ^ (ε / 4) / (ε / 4) = (4 / ε) * x ^ (ε / 4) := by field_simp
    rw [he] at hlog
    nlinarith
  have hlog0 : 0 ≤ 1 + Real.log x := by linarith [Real.log_nonneg hx]
  calc (1 + Real.log x) ^ 4 ≤ ((1 + 4 / ε) * x ^ (ε / 4)) ^ 4 :=
      pow_le_pow_left₀ hlog0 h 4
    _ = (1 + 4 / ε) ^ 4 * x ^ ε := by
      have he : (x ^ (ε / 4)) ^ (4 : ℕ) = x ^ ε := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
        congr 1
        ring
      rw [mul_pow, he]

/-- Lu's quoted bound follows from the lab's proved Vaughan estimate. -/
theorem bound12_proved : Bound12 := by
  intro ε hε
  refine ⟨300 * (1 + 4 / ε) ^ 4, by positivity, ?_⟩
  intro x hx α h q hq hqx hcop hapx
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hn : (⌊x⌋₊ : ℝ) ≤ x := Nat.floor_le hx0.le
  have hn1 : 1 ≤ ⌊x⌋₊ := Nat.one_le_floor_iff _ |>.2 hx1
  have hn0 : (0 : ℝ) < ⌊x⌋₊ := by exact_mod_cast hn1
  have hnq : q ≤ ⌊x⌋₊ := Nat.le_floor hqx
  have hV := LeanLab.PNTPort.Vinogradov.vinogradov_minor hq
    (Int.isCoprime_iff_gcd_eq_one.mpr hcop) hapx hnq
  have hlog : (1 + Real.log (⌊x⌋₊ : ℝ)) ^ 4 ≤ (1 + Real.log x) ^ 4 := by
    apply pow_le_pow_left₀ (by linarith [Real.log_nonneg (show (1 : ℝ) ≤ ⌊x⌋₊ by exact_mod_cast hn1)])
    linarith [Real.log_le_log hn0 hn]
  have ht1 : (⌊x⌋₊ : ℝ) / Real.sqrt q ≤ x * (q : ℝ) ^ (-(1 / 2) : ℝ) := by
    calc (⌊x⌋₊ : ℝ) / Real.sqrt q ≤ x / Real.sqrt q :=
        div_le_div_of_nonneg_right hn (Real.sqrt_nonneg _)
      _ = x * (q : ℝ) ^ (-(1 / 2) : ℝ) := by
        rw [Real.sqrt_eq_rpow, Real.rpow_neg hq0.le, div_eq_mul_inv]
  have ht2 : (⌊x⌋₊ : ℝ) ^ (4 / 5 : ℝ) ≤ x ^ (9 / 10 : ℝ) :=
    (Real.rpow_le_rpow hn0.le hn (by norm_num)).trans
      (Real.rpow_le_rpow_of_exponent_le hx1 (by norm_num))
  have ht3 : Real.sqrt ((⌊x⌋₊ : ℝ) * q) ≤ x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) := by
    calc
      Real.sqrt ((⌊x⌋₊ : ℝ) * q) ≤ Real.sqrt (x * q) := by
        apply Real.sqrt_le_sqrt
        exact mul_le_mul_of_nonneg_right hn hq0.le
      _ = x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) := by
        rw [Real.sqrt_mul hx0.le, Real.sqrt_eq_rpow, Real.sqrt_eq_rpow]
  let T := x ^ (1 / 2 : ℝ) * (q : ℝ) ^ (1 / 2 : ℝ) + x ^ (9 / 10 : ℝ) +
    x * (q : ℝ) ^ (-(1 / 2) : ℝ)
  have hT0 : 0 ≤ T := by dsimp [T]; positivity
  have hT : (⌊x⌋₊ : ℝ) / Real.sqrt q + (⌊x⌋₊ : ℝ) ^ (4 / 5 : ℝ) +
      Real.sqrt ((⌊x⌋₊ : ℝ) * q) ≤ T := by dsimp [T]; linarith
  rw [Ssum_eq_S]
  calc ‖LeanLab.PNTPort.Vinogradov.S ⌊x⌋₊ α‖
      ≤ 300 * ((⌊x⌋₊ : ℝ) / Real.sqrt q + (⌊x⌋₊ : ℝ) ^ (4 / 5 : ℝ) +
        Real.sqrt ((⌊x⌋₊ : ℝ) * q)) * (1 + Real.log (⌊x⌋₊ : ℝ)) ^ 4 := hV
    _ ≤ 300 * T * (1 + Real.log x) ^ 4 := by
      apply mul_le_mul (mul_le_mul_of_nonneg_left hT (by norm_num)) hlog
        (by positivity) (by positivity)
    _ ≤ 300 * T * ((1 + 4 / ε) ^ 4 * x ^ ε) :=
      mul_le_mul_of_nonneg_left (log_four_bound hε hx1) (by positivity)
    _ = _ := by dsimp [T]; ring

/-- The minor arc supremum estimate now needs no cited textbook hypothesis. -/
theorem minorSup_proved : ∃ N1 : ℕ, ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ N, N1 ≤ N →
    ∀ α ∈ LeanLab.ExceptionalSet.Lu2010Arcs.per N \ LeanLab.ExceptionalSet.Lu2010Arcs.major N,
      α ≠ 1 - 1 / QQ N → ∀ t ∈ Set.Icc (LeanLab.ExceptionalSet.Lu2010Assembly.aa N)
        (LeanLab.ExceptionalSet.Lu2010Assembly.bb N),
      ‖Ssum (N - t * LeanLab.ExceptionalSet.Lu2010Assembly.dd N)
        (N - t * LeanLab.ExceptionalSet.Lu2010Assembly.dd N - LeanLab.ExceptionalSet.Lu2010Assembly.dd N) α‖ ≤
        Cs * (N : ℝ) ^ (1 - LeanLab.ExceptionalSet.Lu2010Assembly.c / 2 + 0.000004) :=
  minorSup_of_bound12 bound12_proved

/-- Lu's theorem, conditional only on the existing major arc and equation 86 bundle. -/
theorem lu_of_major_and_eq86 (J : InputsL) : LeanLab.ExceptionalSet.PowerBound 0.879 :=
  lu_of_inputsL J bound12_proved

end LeanLab.ExceptionalSet.Lu2010Bound12

#print axioms LeanLab.ExceptionalSet.Lu2010Bound12.ee_eq_e
#print axioms LeanLab.ExceptionalSet.Lu2010Bound12.Ssum_eq_S
#print axioms LeanLab.ExceptionalSet.Lu2010Bound12.log_four_bound
#print axioms LeanLab.ExceptionalSet.Lu2010Bound12.bound12_proved
#print axioms LeanLab.ExceptionalSet.Lu2010Bound12.minorSup_proved
#print axioms LeanLab.ExceptionalSet.Lu2010Bound12.lu_of_major_and_eq86
