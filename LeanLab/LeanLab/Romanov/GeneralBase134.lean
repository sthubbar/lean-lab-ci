import Mathlib

/-!
# Admissible residues for a general base

Gallagher 1975, page 126, displays 5 and 6.
A prime outside the base and its predecessor forces both necessary coprimality conditions.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.Romanov.GeneralBase134

open Finset

/-- Gallagher page 126, displays 5 and 6, for every base at least two. -/
theorem general_base_admissibility (g K p : ℕ) (hg : 2 ≤ g) (hp : p.Prime) (hpg : ¬ p ∣ g * (g - 1))
    (ν : Fin K → ℕ) (hν : ∀ i, 1 ≤ ν i) :
    Nat.Coprime (p + ∑ i, g ^ ν i) g ∧
      Nat.Coprime ((p + ∑ i, g ^ ν i) - K) (g - 1) := by
  classical
  have hcop : p.Coprime (g * (g - 1)) := hp.coprime_iff_not_dvd.mpr hpg
  have hcopg : p.Coprime g := hcop.of_dvd_right (dvd_mul_right g (g - 1))
  have hcopg1 : p.Coprime (g - 1) := hcop.of_dvd_right (dvd_mul_left (g - 1) g)
  have hzero : (∑ i, g ^ ν i) ≡ 0 [MOD g] := by
    have hsum := Nat.ModEq.sum (s := (univ : Finset (Fin K))) (fun i _ =>
      (show g ≡ 0 [MOD g] by simp [Nat.ModEq]).pow (ν i))
    have hz (i : Fin K) : (0 : ℕ) ^ ν i = 0 := zero_pow (by have := hν i; omega)
    simpa only [hz, sum_const_zero] using hsum
  have hone : g ≡ 1 [MOD g - 1] :=
    ((Nat.modEq_iff_dvd' (by omega : 1 ≤ g)).mpr (dvd_refl (g - 1))).symm
  have hones : (∑ i, g ^ ν i) ≡ K [MOD g - 1] := by
    simpa only [one_pow, sum_const, card_univ, Fintype.card_fin, smul_eq_mul, mul_one] using
      Nat.ModEq.sum (s := (univ : Finset (Fin K))) (fun i _ => hone.pow (ν i))
  have hsumK : K ≤ p + ∑ i, g ^ ν i := by
    have h : K ≤ ∑ i : Fin K, g ^ ν i := by
      calc K = ∑ _i : Fin K, 1 := by simp
        _ ≤ ∑ i : Fin K, g ^ ν i := sum_le_sum (fun i _ => Nat.one_le_pow _ _ (by omega))
    omega
  constructor
  · have hmod : (p + ∑ i, g ^ ν i) ≡ p [MOD g] := by
      simpa only [add_zero] using (Nat.ModEq.refl p).add hzero
    change Nat.gcd _ _ = 1
    rw [hmod.gcd_eq]
    exact hcopg.gcd_eq_one
  · have hmod : (p + ∑ i, g ^ ν i) ≡ p + K [MOD g - 1] := (Nat.ModEq.refl p).add hones
    have hsub := Nat.ModEq.sub hsumK (by omega : K ≤ p + K) hmod (Nat.ModEq.refl K)
    simp only [Nat.add_sub_cancel] at hsub
    change Nat.gcd _ _ = 1
    rw [hsub.gcd_eq]
    exact hcopg1.gcd_eq_one

end LeanLab.Romanov.GeneralBase134
