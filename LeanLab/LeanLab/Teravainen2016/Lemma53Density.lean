/-
P0076, Section 5, page 21, the local density step in the proof of Lemma 5.3.
Split of Lemma53Split.local_density into the exact CRT count of the set of display 5.1 at the
modulus q, a cited LEAF, and the proved bound q times the product of 1 - omega p / p over the
primes of q is at least q^(9/10), since every such prime exceeds w.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Teravainen2016.Lemma53Split

open Finset
open scoped Classical

namespace LeanLab.Teravainen2016.Lemma53Split

open LeanLab.Teravainen2016

/-- LEAF: proof of Lemma 5.3, page 21, the count behind display 5.2 at the modulus q:
for q coprime to W and to Q', the set of display 5.1 for q and W Q' has exactly
q times the product over p dividing q of 1 - omega p / p elements, omega p = 2 for p = 3 mod 4
and 1 otherwise, by the Chinese remainder theorem, since W Q' is invertible mod q and the
residues W Q' c + b = 0 and = 1 mod p are distinct. Class MEDIUM. -/
theorem leaf_qres_count (J w : ℕ) (hJ : 5 ≤ J) (hw : wBig ≤ w) (b : ℤ)
    (hb : Amenable (WW J w) b) (q Q' : ℕ) (hq : 1 ≤ q) (hQ' : Q'.Coprime q)
    (hqW : IsCoprime (q : ℤ) (WW J w)) :
    (#(QRes q (WW J w * Q') b) : ℝ) =
      q * ∏ p ∈ q.primeFactors, (1 - (if p % 4 = 3 then (2 : ℝ) else 1) / p) := by
  sorry

/-- wBig is at least 1024. -/
theorem wBig_ge_1024 : (1024 : ℝ) ≤ wBig := by
  unfold wBig
  have h : (10 : ℝ) ^ ((4 : ℝ)) ≤ (10 : ℝ) ^ ((10 : ℝ) ^ (10 : ℝ)) := by
    apply Real.rpow_le_rpow_of_exponent_le (by norm_num)
    have : (10 : ℝ) ^ (1 : ℝ) ≤ (10 : ℝ) ^ (10 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
    simp at this
    linarith
  have h2 : (10 : ℝ) ^ ((4 : ℝ)) = 10000 := by norm_num
  linarith

/-- The statement of Lemma53Split.local_density, CONDITIONAL ON leaf_qres_count.
Each factor 1 - omega p / p is at least 1/2, which is at least p^(-1/10) for p at least 1024,
and the product of the primes of q is at most q. -/
theorem local_density_of_leaves (J w : ℕ) (hJ : 5 ≤ J) (hw : wBig ≤ w) (b : ℤ)
    (hb : Amenable (WW J w) b) (q Q' : ℕ) (hq : 1 ≤ q) (hQ' : Q'.Coprime q)
    (hqW : IsCoprime (q : ℤ) (WW J w)) :
    (q : ℝ) ^ ((9 : ℝ) / 10) ≤ #(QRes q (WW J w * Q') b) := by
  rw [leaf_qres_count J w hJ hw b hb q Q' hq hQ' hqW]
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hw1024 : (1024 : ℝ) ≤ w := wBig_ge_1024.trans hw
  have hfac : ∀ p ∈ q.primeFactors,
      (p : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 1 - (if p % 4 = 3 then (2 : ℝ) else 1) / p := by
    intro p hp
    have hpw : w < p := prime_factor_gt_w hJ hqW hp
    have hp1024 : (1024 : ℝ) ≤ p := hw1024.trans (by exact_mod_cast hpw.le)
    have hp0 : (0 : ℝ) < p := by linarith
    have h2 : (2 : ℝ) ≤ (p : ℝ) ^ (1 / 10 : ℝ) := by
      calc (2 : ℝ) = (1024 : ℝ) ^ (1 / 10 : ℝ) := by
            rw [show (1024 : ℝ) = 2 ^ (10 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
            norm_num
        _ ≤ (p : ℝ) ^ (1 / 10 : ℝ) := Real.rpow_le_rpow (by norm_num) hp1024 (by norm_num)
    have hneg : (p : ℝ) ^ (-(1 / 10 : ℝ)) ≤ 1 / 2 := by
      rw [Real.rpow_neg hp0.le]
      rw [inv_le_comm₀ (by positivity) (by norm_num)]
      linarith
    have hω : (if p % 4 = 3 then (2 : ℝ) else 1) / p ≤ 1 / 2 := by
      rw [div_le_iff₀ hp0]
      split_ifs <;> linarith
    linarith
  have hprod : ∏ p ∈ q.primeFactors, (p : ℝ) ^ (-(1 / 10 : ℝ)) ≤
      ∏ p ∈ q.primeFactors, (1 - (if p % 4 = 3 then (2 : ℝ) else 1) / p) :=
    prod_le_prod₀ (fun p _ => by positivity) hfac
  have hpf : ∏ p ∈ q.primeFactors, (p : ℝ) ^ (-(1 / 10 : ℝ)) =
      ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ (-(1 / 10 : ℝ)) := by
    push_cast
    rw [Real.finset_prod_rpow _ _ (fun p _ => by positivity)]
  have hle : ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ≤ q := by
    exact_mod_cast Nat.le_of_dvd (by omega) (Nat.prod_primeFactors_dvd q)
  have hpos : (0 : ℝ) < ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) := by
    exact_mod_cast Nat.pos_of_ne_zero (prod_ne_zero_iff.mpr fun p hp =>
      (Nat.prime_of_mem_primeFactors hp).ne_zero)
  have hmono : (q : ℝ) ^ (-(1 / 10 : ℝ)) ≤
      ((∏ p ∈ q.primeFactors, p : ℕ) : ℝ) ^ (-(1 / 10 : ℝ)) :=
    Real.rpow_le_rpow_of_nonpos hpos hle (by norm_num)
  have hq910 : (q : ℝ) ^ ((9 : ℝ) / 10) = q * (q : ℝ) ^ (-(1 / 10 : ℝ)) := by
    rw [← Real.rpow_one_add' hq0.le (by norm_num)]
    norm_num
  rw [hq910]
  apply mul_le_mul_of_nonneg_left _ hq0.le
  rw [hpf] at hprod
  exact hmono.trans hprod

end LeanLab.Teravainen2016.Lemma53Split
