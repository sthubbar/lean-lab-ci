import LeanLab.AlmostPrimeSums.Decomp1527c
import LeanLab.PNTPort.BVMax.PiPi

/-!
AI wrote this Lean code for CODEX task703. Goldbach is open.
The classical prime centered Bombieri Vinogradov input used in BJS
p. 21 equation 67 and p. 53 equation 166 is already proved in PNTPort.
This file converts
its finite prime counts to the exact sealed LevelBV interface.
https://arxiv.org/abs/2207.09452
-/

namespace LeanLab.AlmostPrimeSums.BV703

open Finset Real
open LeanLab.AlmostPrimeSums.Decomp1527c
open LeanLab.PNTPort.BVMax

/-- The proved prime centered distribution estimate supplies LevelBV. -/
theorem levelBV703 : LevelBV := by
  have hcount (n q a : ℕ) : piAP (n : ℝ) q a = (primesAP n q a : ℝ) := by
    unfold piAP
    rw [Nat.floor_natCast]
    unfold piN primesAP
    have hset : (Icc 1 n).filter (fun p => p % q = a % q ∧ p.Prime) =
        (range (n + 1)).filter (fun p => p.Prime ∧ p % q = a % q) := by
      ext p
      simp only [mem_filter, mem_Icc, mem_range]
      constructor
      · rintro ⟨⟨hp1, hpn⟩, hmod, hprime⟩
        exact ⟨by omega, hprime, hmod⟩
      · rintro ⟨hpn, hprime, hmod⟩
        exact ⟨⟨hprime.one_lt.le, by omega⟩, hmod, hprime⟩
    rw [hset]
  have htotal (n : ℕ) : piAP (n : ℝ) 1 1 = (Nat.primeCounting n : ℝ) := by
    rw [hcount]
    have hset : (range (n + 1)).filter (fun p => p.Prime ∧ p % 1 = 1 % 1) =
        n.primesLE := by
      ext p
      simp only [mem_filter, mem_range, Nat.mem_primesLE]
      constructor
      · rintro ⟨hpn, hp, _⟩
        exact ⟨by omega, hp⟩
      · rintro ⟨hpn, hp⟩
        exact ⟨by omega, hp, Nat.mod_one p⟩
    simp only [primesAP, hset, Nat.primesLE_card_eq_primeCounting]
  intro A hA
  obtain ⟨B, hB, C, hC⟩ := bvPiPi A hA
  refine ⟨B, C, ?_⟩
  intro x hx y a hy ha
  have h := hC (x : ℝ) (by exact_mod_cast hx) a ha (fun q => (y q : ℝ))
    (fun q => ⟨Nat.cast_nonneg _, by exact_mod_cast hy q⟩)
  simp_rw [htotal] at h
  simpa only [hcount] using h

end LeanLab.AlmostPrimeSums.BV703
