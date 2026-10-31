/-
AI-written Lean code, Codex task05, 2026-10-22.
A degree-sixteen positive-coefficient certificate for a sharper quarter-level error.
The rational certificate is generated algebraically and checked by the Lean kernel.
All constants are lab calculations, not constants quoted from Brun's paper.
-/
import LeanLab.Brun1919.SharperUpper

open Finset

noncomputable section
namespace LeanLab.Brun1919

/-- A sharper exponential envelope for the normalized quarter-level sieve remainder. -/
lemma quarter_polylog_exp_128 (t : ℝ) (ht : 0 ≤ t) :
    16 * t ^ 2 * ((1 + t) ^ 6 + 2) ≤ 128 * Real.exp (3 * t) := by
  have hs := Real.sum_le_exp_of_nonneg (by positivity : 0 ≤ 3 * t) 17
  have hp : 0 ≤ 128 * (∑ i ∈ range 17, (3 * t) ^ i / (i.factorial : ℝ)) -
      16 * t ^ 2 * ((1 + t) ^ 6 + 2) := by
    by_cases h2 : t ≤ 2
    · have h2t : 0 ≤ 2 - t := by linarith
      have hid : 128 * (∑ i ∈ range 17, (3 * t) ^ i / (i.factorial : ℝ)) -
          16 * t ^ 2 * ((1 + t) ^ 6 + 2) =
          (1 / 512 : ℝ) * (2 - t) ^ 16 +
          (11 / 256 : ℝ) * t * (2 - t) ^ 15 +
          (453 / 1024 : ℝ) * t ^ 2 * (2 - t) ^ 14 +
          (1451 / 512 : ℝ) * t ^ 3 * (2 - t) ^ 13 +
          (12931 / 1024 : ℝ) * t ^ 4 * (2 - t) ^ 12 +
          (26471 / 640 : ℝ) * t ^ 5 * (2 - t) ^ 11 +
          (524841 / 5120 : ℝ) * t ^ 6 * (2 - t) ^ 10 +
          (3493159 / 17920 : ℝ) * t ^ 7 * (2 - t) ^ 9 +
          (10232113 / 35840 : ℝ) * t ^ 8 * (2 - t) ^ 8 +
          (574611 / 1792 : ℝ) * t ^ 9 * (2 - t) ^ 7 +
          (48899257 / 179200 : ℝ) * t ^ 10 * (2 - t) ^ 6 +
          (169861357 / 985600 : ℝ) * t ^ 11 * (2 - t) ^ 5 +
          (14034591 / 179200 : ℝ) * t ^ 12 * (2 - t) ^ 4 +
          (78721271 / 3203200 : ℝ) * t ^ 13 * (2 - t) ^ 3 +
          (184139173 / 35875840 : ℝ) * t ^ 14 * (2 - t) ^ 2 +
          (29890543 / 40768000 : ℝ) * t ^ 15 * (2 - t) +
          (66318177 / 896896000 : ℝ) * t ^ 16 := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
        <;> ring
      rw [hid]
      positivity
    · have h2t : 0 ≤ t - 2 := by linarith
      have hid : 128 * (∑ i ∈ range 17, (3 * t) ^ i / (i.factorial : ℝ)) -
          16 * t ^ 2 * ((1 + t) ^ 6 + 2) =
          (4244363328 / 875875 : ℝ) +
          (1844566336 / 125125 : ℝ) * (t - 2) +
          (345316016 / 7007 : ℝ) * (t - 2) ^ 2 +
          (2399492448 / 25025 : ℝ) * (t - 2) ^ 3 +
          (42389568 / 385 : ℝ) * (t - 2) ^ 4 +
          (808844112 / 9625 : ℝ) * (t - 2) ^ 5 +
          (40844968 / 875 : ℝ) * (t - 2) ^ 6 +
          (4942888 / 245 : ℝ) * (t - 2) ^ 7 +
          (1243061 / 175 : ℝ) * (t - 2) ^ 8 +
          (510543 / 245 : ℝ) * (t - 2) ^ 9 +
          (891567 / 1750 : ℝ) * (t - 2) ^ 10 +
          (1966113 / 19250 : ℝ) * (t - 2) ^ 11 +
          (50301 / 3080 : ℝ) * (t - 2) ^ 12 +
          (400221 / 200200 : ℝ) * (t - 2) ^ 13 +
          (19683 / 112112 : ℝ) * (t - 2) ^ 14 +
          (19683 / 2002000 : ℝ) * (t - 2) ^ 15 +
          (59049 / 224224000 : ℝ) * (t - 2) ^ 16 := by
        norm_num [Finset.sum_range_succ, Nat.factorial]
        <;> ring
      rw [hid]
      positivity
  calc
    _ ≤ 128 * ∑ i ∈ range 17, (3 * t) ^ i / (i.factorial : ℝ) := sub_nonneg.mp hp
    _ ≤ 128 * Real.exp (3 * t) := by gcongr

/-- The complete quarter-level remainder, after multiplication by the logarithm squared. -/
lemma quarter_sieve_error_128 (x : ℝ) (hx : 1 ≤ x) :
    (x ^ (1 / 4 : ℝ) * (1 + Real.log (x ^ (1 / 4 : ℝ))) ^ 6 +
        (x ^ (1 / 4 : ℝ) + 1)) * Real.log x ^ 2 ≤ 128 * x := by
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
  have hp := quarter_polylog_exp_128 t ht0
  have hb : z * (1 + Real.log z) ^ 6 + (z + 1) ≤ z * ((1 + t) ^ 6 + 2) := by
    rw [hlogz]
    nlinarith
  calc
    (z * (1 + Real.log z) ^ 6 + (z + 1)) * Real.log x ^ 2
        ≤ (z * ((1 + t) ^ 6 + 2)) * Real.log x ^ 2 := by gcongr
    _ = z * (16 * t ^ 2 * ((1 + t) ^ 6 + 2)) := by rw [hL]; ring
    _ ≤ z * (128 * Real.exp (3 * t)) := by gcongr
    _ = 128 * (z * Real.exp (3 * t)) := by ring
    _ = 128 * x := by rw [hzx]


/-- The explicit twin-prime count bound with constant 896 and quarter-power sieve level. -/
theorem twinCount_le_896 (N : ℕ) (hN : 3 ≤ N) :
    (twinCount N : ℝ) ≤ 896 * N / Real.log N ^ 2 := by
  have hN1 : 1 < (N : ℝ) := by exact_mod_cast (by omega : 1 < N)
  have hN0 : 0 < (N : ℝ) := by linarith
  have hz : 1 < (N : ℝ) ^ (1 / 4 : ℝ) :=
    Real.one_lt_rpow hN1 (by norm_num)
  have h := twinCount_le N hz
  have hl : Real.log ((N : ℝ) ^ (1 / 4 : ℝ)) = Real.log N / 4 := by
    rw [Real.log_rpow hN0]
    ring
  have herr := quarter_sieve_error_128 (N : ℝ) (by linarith)
  have hden : 0 < Real.log (N : ℝ) ^ 2 := sq_pos_of_pos (Real.log_pos hN1)
  have he : (N : ℝ) ^ (1 / 4 : ℝ) *
      (1 + Real.log ((N : ℝ) ^ (1 / 4 : ℝ))) ^ 6 +
        ((N : ℝ) ^ (1 / 4 : ℝ) + 1) ≤ 128 * N / Real.log N ^ 2 :=
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
    _ ≤ 768 * N / Real.log N ^ 2 + 128 * N / Real.log N ^ 2 := by linarith
    _ = 896 * N / Real.log N ^ 2 := by ring


/-- The explicit witness 896 for the unchanged upper-bound statement. -/
theorem twinUpper_896 : TwinUpper := ⟨896, twinCount_le_896⟩

#print axioms twinUpper_896

#print axioms twinCount_le_896

#print axioms quarter_sieve_error_128

#print axioms quarter_polylog_exp_128

end LeanLab.Brun1919
