/-
P0083 Perelli 1996, page 481 between equations 3 and 4 and page 487 equation 28, elementary divisor mean support.
Proves that the n in an interval [A, B] for which a monic integer polynomial G has G(a n) highly divisible
at every prime power of e number at most deg(G)^omega(e) * (a (B - A) / e + 1), by root clustering mod prime
powers and the chinese remainder theorem.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib.Algebra.Polynomial.Div
import Mathlib.Algebra.Polynomial.Monic
import Mathlib.Data.Nat.ChineseRemainder
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Prime.Int
import Mathlib.Data.Int.ModEq
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic

namespace LeanLab.Perelli1996.DivMean

open Polynomial

/-- Step 1: prime power divisibility passes to the second factor. -/
theorem pow_dvd_right {p : ℤ} (hp : Prime p) (A c : ℕ) :
    ∀ (x y : ℤ), p ^ (A + c) ∣ x * y → ¬ p ^ (c + 1) ∣ x → p ^ A ∣ y := by
  induction c with
  | zero =>
    intro x y h hx
    rw [zero_add, pow_one] at hx
    exact hp.pow_dvd_of_dvd_mul_left _ hx (by simpa using h)
  | succ c ih =>
    intro x y h hx
    by_cases hpx : p ∣ x
    · obtain ⟨x', rfl⟩ := hpx
      apply ih x' y
      · have h1 : p ^ (A + c) * p ∣ (x' * y) * p := by
          rw [← pow_succ]
          convert h using 1
          ring
        exact (mul_dvd_mul_iff_right hp.ne_zero).mp h1
      · intro hc
        apply hx
        have h2 : p * p ^ (c + 1) ∣ p * x' := mul_dvd_mul_left p hc
        rwa [← pow_succ'] at h2
    · exact (pow_dvd_pow p (by omega)).trans (hp.pow_dvd_of_dvd_mul_left _ hpx h)

/-- Step 2: roots modulo a high prime power cluster into at most `k` classes modulo `p ^ b`. -/
theorem root_cluster (p : ℤ) (hp : Prime p) (b : ℕ) (hb : 1 ≤ b) :
    ∀ (k : ℕ) (F : ℤ[X]), F.natDegree ≤ k → ¬ p ∣ F.coeff k →
      ∃ S : Finset ℤ, S.card ≤ k ∧
        ∀ n : ℤ, p ^ (1 + k * (b - 1)) ∣ F.eval n → ∃ s ∈ S, p ^ b ∣ n - s := by
  intro k
  induction k with
  | zero =>
    intro F hF hc
    refine ⟨∅, by simp, fun n hn => ?_⟩
    exfalso
    have h1 : F.eval n = F.coeff 0 := by
      conv_lhs => rw [eq_C_of_natDegree_le_zero hF]
      simp
    rw [h1, Nat.zero_mul, Nat.add_zero, pow_one] at hn
    exact hc hn
  | succ k ih =>
    intro F hF hc
    by_cases h : ∃ n0 : ℤ, p ^ (1 + (k + 1) * (b - 1)) ∣ F.eval n0
    swap
    · exact ⟨∅, by simp, fun n hn => (h ⟨n, hn⟩).elim⟩
    obtain ⟨n0, hn0⟩ := h
    obtain ⟨Q, hQ⟩ := X_sub_C_dvd_sub_C_eval (a := n0) (p := F)
    have hQdeg : Q.natDegree ≤ k := by
      by_cases hQ0 : Q = 0
      · simp [hQ0]
      have h1 : ((X - C n0) * Q).natDegree = (X - C n0).natDegree + Q.natDegree :=
        (monic_X_sub_C n0).natDegree_mul' hQ0
      rw [← hQ, natDegree_sub_C, natDegree_X_sub_C] at h1
      omega
    have hQc : Q.coeff k = F.coeff (k + 1) := by
      have h1 := congrArg (fun P => P.coeff (k + 1)) hQ
      simp only [coeff_sub, sub_mul, coeff_X_mul, coeff_C_mul, coeff_C_succ, sub_zero] at h1
      rw [coeff_eq_zero_of_natDegree_lt (by omega : Q.natDegree < k + 1)] at h1
      rw [h1]
      simp
    obtain ⟨S', hS'c, hS'⟩ := ih Q hQdeg (by rw [hQc]; exact hc)
    refine ⟨insert n0 S', (Finset.card_insert_le _ _).trans (by omega), fun n hn => ?_⟩
    by_cases hd : p ^ b ∣ n - n0
    · exact ⟨n0, Finset.mem_insert_self _ _, hd⟩
    have h2 : F.eval n - F.eval n0 = (n - n0) * Q.eval n := by
      have h := congrArg (fun P => P.eval n) hQ
      simpa using h
    have h3 : p ^ ((1 + k * (b - 1)) + (b - 1)) ∣ (n - n0) * Q.eval n := by
      rw [← h2]
      have e : 1 + k * (b - 1) + (b - 1) = 1 + (k + 1) * (b - 1) := by ring
      rw [e]
      exact dvd_sub hn hn0
    have h4 := pow_dvd_right hp (1 + k * (b - 1)) (b - 1) (n - n0) (Q.eval n) h3
      (by rwa [Nat.sub_add_cancel hb])
    obtain ⟨s, hs, hsd⟩ := hS' n h4
    exact ⟨s, Finset.mem_insert_of_mem hs, hsd⟩

/-- Step 3: the admissible arguments lie in few residue classes modulo `e`. -/
theorem residues (G : ℤ[X]) (hG : G.Monic) :
    ∀ e : ℕ, e ≠ 0 → ∃ R : Finset ℕ, R.card ≤ G.natDegree ^ e.primeFactors.card ∧
      ∀ y : ℕ, (∀ p b : ℕ, p.Prime → 1 ≤ b → p ^ b ∣ e →
          ((p : ℤ) ^ (1 + G.natDegree * (b - 1))) ∣ G.eval (y : ℤ)) →
        ∃ r ∈ R, y ≡ r [MOD e] := by
  intro e
  induction e using Nat.recOnPosPrimePosCoprime with
  | prime_pow p b hp hb =>
    intro _
    have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
    obtain ⟨S, hSc, hS⟩ := root_cluster (p : ℤ) hpZ b hb G.natDegree G le_rfl
      (by rw [hG.coeff_natDegree]; exact hpZ.not_dvd_one)
    refine ⟨S.image (fun s => (s % (p : ℤ) ^ b).toNat), ?_, fun y hy => ?_⟩
    · rw [Nat.primeFactors_prime_pow hb.ne' hp, Finset.card_singleton, pow_one]
      exact Finset.card_image_le.trans hSc
    · obtain ⟨s, hs, hsd⟩ := hS y (hy p b hp hb dvd_rfl)
      refine ⟨_, Finset.mem_image_of_mem _ hs, ?_⟩
      apply Int.natCast_modEq_iff.mp
      have hne : (p : ℤ) ^ b ≠ 0 := pow_ne_zero _ hpZ.ne_zero
      rw [Int.toNat_of_nonneg (Int.emod_nonneg _ hne), Nat.cast_pow, Int.modEq_iff_dvd]
      obtain ⟨t, ht⟩ := hsd
      exact ⟨-t - s / (p : ℤ) ^ b, by rw [Int.emod_def]; linear_combination (-1 : ℤ) * ht⟩
  | zero => intro h; exact (h rfl).elim
  | one =>
    intro _
    exact ⟨{0}, by simp, fun y _ => ⟨0, by simp, Nat.modEq_one⟩⟩
  | coprime m n hm hn hcop ihm ihn =>
    intro _
    obtain ⟨Rm, hRmc, hRm⟩ := ihm (by omega)
    obtain ⟨Rn, hRnc, hRn⟩ := ihn (by omega)
    refine ⟨(Rm ×ˢ Rn).image (fun x => (Nat.chineseRemainder hcop x.1 x.2 : ℕ)), ?_,
      fun y hy => ?_⟩
    · rw [hcop.primeFactors_mul, Finset.card_union_of_disjoint hcop.disjoint_primeFactors,
        pow_add]
      exact Finset.card_image_le.trans
        ((Finset.card_product _ _).le.trans (Nat.mul_le_mul hRmc hRnc))
    · obtain ⟨rm, hrm, hym⟩ := hRm y (fun p b hp hb hd => hy p b hp hb (hd.mul_right n))
      obtain ⟨rn, hrn, hyn⟩ := hRn y (fun p b hp hb hd => hy p b hp hb (hd.mul_left m))
      refine ⟨_, Finset.mem_image_of_mem _ (Finset.mk_mem_product hrm hrn), ?_⟩
      have hz := (Nat.chineseRemainder hcop rm rn).2
      exact (Nat.modEq_and_modEq_iff_modEq_mul hcop).mp
        ⟨hym.trans hz.1.symm, hyn.trans hz.2.symm⟩

/-- Step 4: one residue class of `a * n` modulo `e` meets `[A, B]` in few points. -/
theorem count_residue (a e A B r : ℕ) (ha : 0 < a)
    [DecidablePred fun n : ℕ => a * n ≡ r [MOD e]] :
    ((Finset.Icc A B).filter (fun n => a * n ≡ r [MOD e])).card ≤ a * (B - A) / e + 1 := by
  rw [← Finset.card_range (a * (B - A) / e + 1)]
  apply Finset.card_le_card_of_injOn (fun n => (a * n - a * A) / e)
  · intro n hn
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hn
    simp only [Finset.coe_range, Set.mem_Iio]
    apply Nat.lt_succ_of_le
    apply Nat.div_le_div_right
    rw [← Nat.mul_sub]
    exact Nat.mul_le_mul_left a (Nat.sub_le_sub_right hn.1.2 A)
  · intro n hn n' hn' hq
    simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_ofPred_eq] at hn hn'
    simp only at hq
    have h1 : a * A ≤ a * n := Nat.mul_le_mul_left a hn.1.1
    have h1' : a * A ≤ a * n' := Nat.mul_le_mul_left a hn'.1.1
    have hmod : (a * n - a * A) % e = (a * n' - a * A) % e := by
      apply Nat.ModEq.add_right_cancel' (a * A)
      rw [Nat.sub_add_cancel h1, Nat.sub_add_cancel h1']
      exact hn.2.trans hn'.2.symm
    have h2 := Nat.div_add_mod (a * n - a * A) e
    have h2' := Nat.div_add_mod (a * n' - a * A) e
    rw [hq, hmod] at h2
    have h3 : a * n - a * A = a * n' - a * A := h2.symm.trans h2'
    have h4 : a * n = a * n' := by omega
    exact Nat.eq_of_mul_eq_mul_left ha h4

open Classical in
theorem count_root_condition (G : ℤ[X]) (hG : G.Monic) (e : ℕ) (he : 0 < e) (a A B : ℕ) (ha : 0 < a) :
    ((Finset.Icc A B).filter (fun n => ∀ p b : ℕ, p.Prime → 1 ≤ b → p ^ b ∣ e →
        ((p : ℤ) ^ (1 + G.natDegree * (b - 1))) ∣ G.eval ((a * n : ℕ) : ℤ))).card
      ≤ G.natDegree ^ e.primeFactors.card * (a * (B - A) / e + 1) := by
  obtain ⟨R, hRc, hR⟩ := residues G hG e he.ne'
  have hsub : ((Finset.Icc A B).filter (fun n => ∀ p b : ℕ, p.Prime → 1 ≤ b → p ^ b ∣ e →
        ((p : ℤ) ^ (1 + G.natDegree * (b - 1))) ∣ G.eval ((a * n : ℕ) : ℤ))) ⊆
      R.biUnion (fun r => (Finset.Icc A B).filter (fun n => a * n ≡ r [MOD e])) := by
    intro n hn
    rw [Finset.mem_filter] at hn
    obtain ⟨r, hr, hnr⟩ := hR (a * n) hn.2
    exact Finset.mem_biUnion.mpr ⟨r, hr, Finset.mem_filter.mpr ⟨hn.1, hnr⟩⟩
  refine (Finset.card_le_card hsub).trans ?_
  refine (Finset.card_biUnion_le_card_mul _ _ _
    (fun r _ => count_residue a e A B r ha)).trans ?_
  exact Nat.mul_le_mul_right _ hRc

end LeanLab.Perelli1996.DivMean

#print axioms LeanLab.Perelli1996.DivMean.count_root_condition
