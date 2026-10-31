/-
Vaughan 1977, P0066, page 97, proof of Lemma 3.
Source: https://doi.org/10.1515/crll.1977.290.93
The case of coprime residues is cited from Montgomery and Vaughan 1973, Theorem 2.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.SchnirelmannBounds.Vaughan1977Lemma3

open Finset Real
open scoped Classical

namespace LeanLab.SchnirelmannBounds.Vaughan1977Lemma3

/-- The cited input restricted to coprime residues, as in the proof on page 97. -/
def Lemma3Coprime : Prop :=
  ∀ (x y : ℝ) (k l : ℕ), 0 < k → (k : ℝ) < x → k.Coprime l →
    (pi_interval x y k l : ℝ) ≤ 2 * x / ((k.totient : ℝ) * Real.log (x / k))

/-- A prime in a noncoprime residue class equals the common divisor. -/
theorem prime_eq_gcd {k l p : ℕ} (hkl : ¬ k.Coprime l) (hp : p.Prime)
    (hpl : p ≡ l [MOD k]) : p = Nat.gcd l k := by
  have hg : Nat.gcd p k ≠ 1 := by
    intro h
    apply hkl
    rw [Nat.coprime_iff_gcd_eq_one, Nat.gcd_comm, ← hpl.gcd_eq, h]
  have hd := (Nat.dvd_prime hp).mp (Nat.gcd_dvd_left p k)
  have he : Nat.gcd p k = p := hd.resolve_left hg
  exact he.symm.trans hpl.gcd_eq

/-- The interval contains at most one prime in a noncoprime residue class. -/
theorem pi_interval_le_one (x y : ℝ) {k l : ℕ} (hkl : ¬ k.Coprime l) :
    pi_interval x y k l ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro p hp q hq
  simp only [Finset.mem_filter] at hp hq
  exact (prime_eq_gcd hkl hp.2.1 hp.2.2).trans (prime_eq_gcd hkl hq.2.1 hq.2.2).symm

/-- The Brun-Titchmarsh right side exceeds one for every positive modulus below x. -/
theorem one_le_bt_rhs {x : ℝ} {k : ℕ} (hk : 0 < k) (hkx : (k : ℝ) < x) :
    1 ≤ 2 * x / ((k.totient : ℝ) * Real.log (x / k)) := by
  have hk0 : (0 : ℝ) < k := by exact_mod_cast hk
  have hx0 : 0 < x := lt_trans hk0 hkx
  have hlog : 0 < Real.log (x / k) := Real.log_pos ((one_lt_div hk0).mpr hkx)
  have hφ0 : (0 : ℝ) < k.totient := by exact_mod_cast Nat.totient_pos.mpr hk
  have hφ : (k.totient : ℝ) ≤ k := by exact_mod_cast Nat.totient_le k
  have ht : Real.log (x / k) < x / k :=
    lt_of_le_of_lt (Real.log_le_sub_one_of_pos (div_pos hx0 hk0)) (by linarith)
  have hlt := mul_lt_mul_of_pos_left ht hk0
  have hcancel : (k : ℝ) * (x / k) = x := by field_simp
  rw [hcancel] at hlt
  have hd : (k.totient : ℝ) * Real.log (x / k) < x :=
    lt_of_le_of_lt (mul_le_mul_of_nonneg_right hφ hlog.le) hlt
  rw [le_div_iff₀ (mul_pos hφ0 hlog)]
  linarith

/-- Vaughan's noncoprime case is elementary and has no cited input. -/
theorem lemma3_noncoprime (x y : ℝ) {k l : ℕ} (hk : 0 < k) (hkx : (k : ℝ) < x)
    (hkl : ¬ k.Coprime l) :
    (pi_interval x y k l : ℝ) ≤ 2 * x / ((k.totient : ℝ) * Real.log (x / k)) := by
  exact le_trans (by exact_mod_cast pi_interval_le_one x y hkl) (one_le_bt_rhs hk hkx)

/-- Lemma 3, CONDITIONAL ON the cited coprime form alone. -/
theorem lemma3_of_coprime (h : Lemma3Coprime) : Lemma3 := by
  intro x y k l hk hkx
  by_cases hc : k.Coprime l
  · exact h x y k l hk hkx hc
  · exact lemma3_noncoprime x y hk hkx hc

example : ¬ Nat.Coprime 2 0 ∧ Nat.Prime 2 ∧ 2 ≡ 0 [MOD 2] := by decide

end LeanLab.SchnirelmannBounds.Vaughan1977Lemma3

#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma3.prime_eq_gcd
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma3.pi_interval_le_one
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma3.one_le_bt_rhs
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma3.lemma3_noncoprime
#print axioms LeanLab.SchnirelmannBounds.Vaughan1977Lemma3.lemma3_of_coprime
