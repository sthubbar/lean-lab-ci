/-
AI-written Lean code, Codex task05, 2026-10-21.
An explicit improvement of the lab Selberg bound for twin primes.
The constant is a lab calculation, not a constant printed by Brun in 1919.
-/
import LeanLab.Brun1919.Sieve

open Finset

noncomputable section
namespace LeanLab.Brun1919

/-- A degree-eight Taylor bound for the normalized quarter-level sieve error. -/
lemma quarter_polylog_exp (t : ℝ) (ht : 0 ≤ t) :
    16 * t ^ 2 * ((1 + t) ^ 6 + 2) ≤ 256 * Real.exp (3 * t) := by
  have hs := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ 3 * t) 9
  have hp : 16 * t ^ 2 * ((1 + t) ^ 6 + 2) ≤
      256 * ∑ i ∈ range 9, (3 * t) ^ i / (i.factorial : ℝ) := by
    have hd : 256 * (∑ i ∈ range 9, (3 * t) ^ i / (i.factorial : ℝ)) -
        16 * t ^ 2 * ((1 + t) ^ 6 + 2) =
        256 + 768 * t + 1104 * t ^ 2 + 1056 * t ^ 3 + 624 * t ^ 4 +
          (992 / 5 : ℝ) * t ^ 5 + (96 / 5 : ℝ) * t ^ 6 +
          (528 / 35 : ℝ) * t ^ 7 + (898 / 35 : ℝ) * t ^ 8 := by
      norm_num [Finset.sum_range_succ, Nat.factorial]
      <;> ring
    apply sub_nonneg.mp
    rw [hd]
    positivity
  exact hp.trans (by gcongr)

/-- The complete quarter-level remainder, after multiplication by the logarithm squared. -/
lemma quarter_sieve_error (x : ℝ) (hx : 1 ≤ x) :
    (x ^ (1 / 4 : ℝ) * (1 + Real.log (x ^ (1 / 4 : ℝ))) ^ 6 +
        (x ^ (1 / 4 : ℝ) + 1)) * Real.log x ^ 2 ≤ 256 * x := by
  have hx0 : 0 < x := by linarith
  set z := x ^ (1 / 4 : ℝ) with hz
  set t := Real.log x / 4 with ht
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx
  have ht0 : 0 ≤ t := by dsimp [t]; positivity
  have hz0 : 0 ≤ z := (Real.rpow_pos_of_pos hx0 _).le
  have hz1 : 1 ≤ z := Real.one_le_rpow hx (by norm_num)
  have hlogz : Real.log z = t := by
    rw [hz, Real.log_rpow hx0, ht]
    ring
  have hzx : z * Real.exp (3 * t) = x := by
    rw [hz, Real.rpow_def_of_pos hx0, ← Real.exp_add]
    convert Real.exp_log hx0 using 1 <;> dsimp [t] <;> ring
  have hL : Real.log x ^ 2 = 16 * t ^ 2 := by rw [ht]; ring
  have hp := quarter_polylog_exp t ht0
  have hb : z * (1 + Real.log z) ^ 6 + (z + 1) ≤ z * ((1 + t) ^ 6 + 2) := by
    rw [hlogz]
    nlinarith
  calc
    (z * (1 + Real.log z) ^ 6 + (z + 1)) * Real.log x ^ 2
        ≤ (z * ((1 + t) ^ 6 + 2)) * Real.log x ^ 2 := by gcongr
    _ = z * (16 * t ^ 2 * ((1 + t) ^ 6 + 2)) := by rw [hL]; ring
    _ ≤ z * (256 * Real.exp (3 * t)) := by gcongr
    _ = 256 * (z * Real.exp (3 * t)) := by ring
    _ = 256 * x := by rw [hzx]

/-- The explicit twin-prime count bound with constant 1024 and quarter-power sieve level. -/
theorem twinCount_le_1024 (N : ℕ) (hN : 3 ≤ N) :
    (twinCount N : ℝ) ≤ 1024 * N / Real.log N ^ 2 := by
  have hN1 : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hN0 : 0 < (N : ℝ) := by linarith
  have hz : 1 < (N : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_lt_rpow hN1 (by norm_num)
  have h := twinCount_le N hz
  have hl : Real.log ((N : ℝ) ^ (1 / 4 : ℝ)) = Real.log N / 4 := by
    rw [Real.log_rpow hN0]
    ring
  have herr := quarter_sieve_error (N : ℝ) (by linarith)
  have hden : 0 < Real.log (N : ℝ) ^ 2 := sq_pos_of_pos (Real.log_pos hN1)
  have he : (N : ℝ) ^ (1 / 4 : ℝ) *
      (1 + Real.log ((N : ℝ) ^ (1 / 4 : ℝ))) ^ 6 +
        ((N : ℝ) ^ (1 / 4 : ℝ) + 1) ≤ 256 * N / Real.log N ^ 2 :=
    (le_div_iff₀ hden).mpr herr
  have hm : 48 * (N : ℝ) / Real.log ((N : ℝ) ^ (1 / 4 : ℝ)) ^ 2 =
      768 * N / Real.log N ^ 2 := by
    rw [hl]
    field_simp
    <;> ring
  rw [hm] at h
  calc
    (twinCount N : ℝ) ≤ 768 * N / Real.log N ^ 2 +
        ((N : ℝ) ^ (1 / 4 : ℝ) *
          (1 + Real.log ((N : ℝ) ^ (1 / 4 : ℝ))) ^ 6 +
          ((N : ℝ) ^ (1 / 4 : ℝ) + 1)) := by linarith
    _ ≤ 768 * N / Real.log N ^ 2 + 256 * N / Real.log N ^ 2 := by linarith
    _ = 1024 * N / Real.log N ^ 2 := by ring

/-- A smaller explicit witness for the existing upper-bound statement. -/
theorem twinUpper_1024 : TwinUpper := ⟨1024, twinCount_le_1024⟩

#print axioms twinUpper_1024

#print axioms twinCount_le_1024

#print axioms quarter_sieve_error

#print axioms quarter_polylog_exp

end LeanLab.Brun1919
