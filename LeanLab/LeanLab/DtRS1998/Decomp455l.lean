/-
AI wrote this Lean code for CODEX task455.
P0037 Section 5.2 page 212, supporting fixed list sieve certificates.
The first 200 offsets alone miss one index. The full target list does not.
This is a limit of a certificate prefix, not a paper error.
Binary Goldbach is open.
-/
import LeanLab.DtRS1998.Decomp455a

namespace LeanLab.DtRS1998.Decomp455l

open Decomp455a

set_option maxRecDepth 100000
set_option maxHeartbeats 0

/-- P0037 page 212, supporting alternative certificate data.
At j = 35109324 none of the first 200 offsets gives a prime complement.
This does not negate any leaf for the complete 213 offset list. -/
theorem short_prefix_misses :
    ¬ ∃ a ∈ offsets.take 200, (2 * 35109324 + a).Prime := by
  have hcheck : (offsets.take 200).all (fun a =>
      ([3, 5, 7, 11, 13, 17, 19, 29, 31, 41, 43, 53, 61, 67, 71, 73, 79, 83, 113, 157, 239, 263, 661, 709, 1009, 1109, 1373, 1979, 2143, 2837, 3217, 3853, 5449, 6299] : List ℕ).any (fun d =>
        decide (2 ≤ d ∧ d < 2 * 35109324 + a ∧
          (2 * 35109324 + a) % d = 0))) = true := by decide +kernel
  rintro ⟨a, ha, hp⟩
  obtain ⟨d, _, hd⟩ := List.any_eq_true.mp (List.all_eq_true.mp hcheck a ha)
  have hd' : 2 ≤ d ∧ d < 2 * 35109324 + a ∧
      (2 * 35109324 + a) % d = 0 := of_decide_eq_true hd
  exact Nat.not_prime_of_dvd_of_lt (Nat.dvd_of_mod_eq_zero hd'.2.2)
    hd'.1 hd'.2.1 hp

#print axioms short_prefix_misses

/-- P0037 page 212, an individual exceptional complement certificate.
The full list supplies the omitted offset and the prime 71552837. -/
theorem exceptional_offset :
    1334189 ∈ offsets ∧ 1334189 ∉ offsets.take 200 ∧
      (2 * 35109324 + 1334189).Prime := by
  refine ⟨by decide +kernel, by decide +kernel, ?_⟩
  exact Nat.prime_def_minFac.mpr ⟨by decide, by decide +kernel⟩

#print axioms exceptional_offset

end LeanLab.DtRS1998.Decomp455l
