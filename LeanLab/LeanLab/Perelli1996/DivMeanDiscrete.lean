/-
P0083 Perelli 1996, page 481 between equations 3 and 4 and page 487 equation 28, elementary divisor mean support.
Proves discrete_divisor_mean: the sum over n in [A, B] of d(F(n))^2 for an integer polynomial F with positive leading coefficient is at most a constant times (a (B - A) + Y) times a power of 1 + log Y, by combining the root count, the divisor majorant and the divisor power sum of the sibling files.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib.RingTheory.Polynomial.IntegralNormalization
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Tactic
import LeanLab.Perelli1996.DivMeanCluster
import LeanLab.Perelli1996.DivMeanPointwise
import LeanLab.Perelli1996.DivMeanSum

open Polynomial

namespace LeanLab.Perelli1996.DivMean

open Classical in
/-- Summation core: a pointwise majorant plus a count of the admissible `n` for each `e`. -/
theorem sum_core (k a A B Y : ℕ) (hk : 1 ≤ k) (v : ℕ → ℕ) (P : ℕ → ℕ → Prop)
    (h1 : ∀ n ∈ Finset.Icc A B, ∃ e ∈ Finset.Icc 1 Y,
      (v n).divisors.card ≤ (6 * k) ^ (6 * k - 1) * e.divisors.card ^ ((6 * k) ^ 2) ∧ P e n)
    (h2 : ∀ e ∈ Finset.Icc 1 Y, ((Finset.Icc A B).filter (fun n => P e n)).card ≤
      e.divisors.card ^ k * (a * (B - A) / e + 1)) :
    ∑ n ∈ Finset.Icc A B, ((v n).divisors.card : ℝ) ^ 2 ≤
      ((6 * k : ℕ) : ℝ) ^ (12 * k) * ((a * (B - A) + Y : ℕ) : ℝ) *
        (1 + Real.log Y) ^ (2 ^ (2 ^ (72 * k ^ 2 + k))) := by
  obtain ⟨C, hC⟩ : ∃ C : ℝ, C = (((6 * k : ℕ) : ℝ) ^ (6 * k - 1)) ^ 2 := ⟨_, rfl⟩
  have hC0 : 0 ≤ C := by rw [hC]; exact sq_nonneg _
  have hκ1 : (1 : ℝ) ≤ ((6 * k : ℕ) : ℝ) := by exact_mod_cast (by omega : 1 ≤ 6 * k)
  have hCle : C ≤ ((6 * k : ℕ) : ℝ) ^ (12 * k) := by
    rw [hC, ← pow_mul]
    exact pow_le_pow_right₀ hκ1 (by omega)
  have hW0 : (0 : ℝ) ≤ ((a * (B - A) + Y : ℕ) : ℝ) := Nat.cast_nonneg _
  have hL1 : (1 : ℝ) ≤ 1 + Real.log Y := by
    have := Real.log_natCast_nonneg Y
    linarith
  have hL0 : (0 : ℝ) ≤ (1 + Real.log Y) ^ (2 ^ (2 ^ (72 * k ^ 2 + k))) :=
    pow_nonneg (by linarith) _
  have step2 : ∀ n ∈ Finset.Icc A B, ((v n).divisors.card : ℝ) ^ 2 ≤
      ∑ e ∈ Finset.Icc 1 Y,
        C * (e.divisors.card : ℝ) ^ (72 * k ^ 2) * (if P e n then (1 : ℝ) else 0) := by
    intro n hn
    obtain ⟨e, he, hc, hP⟩ := h1 n hn
    have hterm : ((v n).divisors.card : ℝ) ^ 2 ≤
        C * (e.divisors.card : ℝ) ^ (72 * k ^ 2) * (if P e n then (1 : ℝ) else 0) := by
      simp only [hP, ↓reduceIte, mul_one]
      have hc' : ((v n).divisors.card : ℝ) ≤
          ((6 * k : ℕ) : ℝ) ^ (6 * k - 1) * (e.divisors.card : ℝ) ^ ((6 * k) ^ 2) := by
        exact_mod_cast hc
      have hexp : (6 * k) ^ 2 * 2 = 72 * k ^ 2 := by ring
      calc ((v n).divisors.card : ℝ) ^ 2
          ≤ (((6 * k : ℕ) : ℝ) ^ (6 * k - 1) * (e.divisors.card : ℝ) ^ ((6 * k) ^ 2)) ^ 2 :=
            pow_le_pow_left₀ (Nat.cast_nonneg _) hc' 2
        _ = C * (e.divisors.card : ℝ) ^ (72 * k ^ 2) := by
            rw [hC, mul_pow, ← pow_mul (e.divisors.card : ℝ), hexp]
    refine hterm.trans (Finset.single_le_sum
      (f := fun e => C * (e.divisors.card : ℝ) ^ (72 * k ^ 2) * (if P e n then (1 : ℝ) else 0))
      (fun e _ => ?_) he)
    exact mul_nonneg (mul_nonneg hC0 (pow_nonneg (Nat.cast_nonneg _) _))
      (by split_ifs <;> norm_num)
  calc ∑ n ∈ Finset.Icc A B, ((v n).divisors.card : ℝ) ^ 2
      ≤ ∑ n ∈ Finset.Icc A B, ∑ e ∈ Finset.Icc 1 Y,
          C * (e.divisors.card : ℝ) ^ (72 * k ^ 2) * (if P e n then (1 : ℝ) else 0) :=
        Finset.sum_le_sum step2
    _ = ∑ e ∈ Finset.Icc 1 Y, C * (e.divisors.card : ℝ) ^ (72 * k ^ 2) *
          (((Finset.Icc A B).filter (fun n => P e n)).card : ℝ) := by
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl (fun e _ => ?_)
        rw [← Finset.mul_sum, Finset.sum_boole]
    _ ≤ ∑ e ∈ Finset.Icc 1 Y, C * ((a * (B - A) + Y : ℕ) : ℝ) *
          ((e.divisors.card : ℝ) ^ (72 * k ^ 2 + k) / (e : ℝ)) := by
        refine Finset.sum_le_sum (fun e he => ?_)
        have he1 : 1 ≤ e := (Finset.mem_Icc.mp he).1
        have heY : e ≤ Y := (Finset.mem_Icc.mp he).2
        have he0 : (0 : ℝ) < (e : ℝ) := by exact_mod_cast he1
        have hcard : (((Finset.Icc A B).filter (fun n => P e n)).card : ℝ) ≤
            (e.divisors.card : ℝ) ^ k * (((a * (B - A) / e : ℕ) : ℝ) + 1) := by
          exact_mod_cast h2 e he
        have hdiv : (((a * (B - A) / e : ℕ) : ℝ) + 1) ≤
            ((a * (B - A) + Y : ℕ) : ℝ) / (e : ℝ) := by
          rw [le_div_iff₀ he0]
          have h3 : (a * (B - A) / e) * e ≤ a * (B - A) := Nat.div_mul_le_self _ _
          have h4 : (((a * (B - A) / e : ℕ) : ℝ)) * (e : ℝ) ≤ ((a * (B - A) : ℕ) : ℝ) := by
            exact_mod_cast h3
          have h5 : (e : ℝ) ≤ (Y : ℝ) := by exact_mod_cast heY
          have h6 : ((a * (B - A) + Y : ℕ) : ℝ) = ((a * (B - A) : ℕ) : ℝ) + (Y : ℝ) :=
            Nat.cast_add _ _
          rw [h6, add_mul, one_mul]
          linarith
        have hT0 : (0 : ℝ) ≤ (e.divisors.card : ℝ) := Nat.cast_nonneg _
        calc C * (e.divisors.card : ℝ) ^ (72 * k ^ 2) *
              (((Finset.Icc A B).filter (fun n => P e n)).card : ℝ)
            ≤ C * (e.divisors.card : ℝ) ^ (72 * k ^ 2) *
                ((e.divisors.card : ℝ) ^ k * (((a * (B - A) + Y : ℕ) : ℝ) / (e : ℝ))) :=
              mul_le_mul_of_nonneg_left
                (hcard.trans (mul_le_mul_of_nonneg_left hdiv (pow_nonneg hT0 _)))
                (mul_nonneg hC0 (pow_nonneg hT0 _))
          _ = C * ((a * (B - A) + Y : ℕ) : ℝ) *
                ((e.divisors.card : ℝ) ^ (72 * k ^ 2 + k) / (e : ℝ)) := by
              rw [pow_add]
              ring
    _ = C * ((a * (B - A) + Y : ℕ) : ℝ) *
          ∑ e ∈ Finset.Icc 1 Y, (e.divisors.card : ℝ) ^ (72 * k ^ 2 + k) / (e : ℝ) := by
        rw [Finset.mul_sum]
    _ ≤ C * ((a * (B - A) + Y : ℕ) : ℝ) *
          (1 + Real.log Y) ^ (2 ^ (2 ^ (72 * k ^ 2 + k))) :=
        mul_le_mul_of_nonneg_left (sum_card_divisors_pow_div_le _ _) (mul_nonneg hC0 hW0)
    _ ≤ ((6 * k : ℕ) : ℝ) ^ (12 * k) * ((a * (B - A) + Y : ℕ) : ℝ) *
          (1 + Real.log Y) ^ (2 ^ (2 ^ (72 * k ^ 2 + k))) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCle hW0) hL0

open Classical in
/-- The divisor mean for a monic polynomial `G` evaluated at `a * n`, with the values written
as `a ^ (k - 1) * v n`. -/
theorem monic_core (G : ℤ[X]) (hG : G.Monic) (k a A B M Y : ℕ) (hk : 1 ≤ k)
    (hGd : G.natDegree = k) (ha : 0 < a) (v : ℕ → ℕ)
    (hv : ∀ n ∈ Finset.Icc A B, 0 < v n ∧ v n ≤ M ∧
      G.eval ((a * n : ℕ) : ℤ) = ((a ^ (k - 1) * v n : ℕ) : ℤ))
    (hY : a ^ (k - 1) * M < (Y + 1) ^ (6 * k)) :
    ∑ n ∈ Finset.Icc A B, ((v n).divisors.card : ℝ) ^ 2 ≤
      ((6 * k : ℕ) : ℝ) ^ (12 * k) * ((a * (B - A) + Y : ℕ) : ℝ) *
        (1 + Real.log Y) ^ (2 ^ (2 ^ (72 * k ^ 2 + k))) := by
  subst hGd
  have step1 : ∀ n ∈ Finset.Icc A B, ∃ e ∈ Finset.Icc 1 Y,
      (v n).divisors.card ≤
        (6 * G.natDegree) ^ (6 * G.natDegree - 1) * e.divisors.card ^ ((6 * G.natDegree) ^ 2) ∧
      (∀ p b : ℕ, p.Prime → 1 ≤ b → p ^ b ∣ e →
        ((p : ℤ) ^ (1 + G.natDegree * (b - 1))) ∣ G.eval ((a * n : ℕ) : ℤ)) := by
    intro n hn
    obtain ⟨hv0, hvM, hev⟩ := hv n hn
    have hm : 0 < a ^ (G.natDegree - 1) * v n := Nat.mul_pos (pow_pos ha _) hv0
    obtain ⟨e, he, hpow, hcard, hdiv⟩ :=
      divisor_majorant G.natDegree (6 * G.natDegree) (by omega) (by omega) _ hm
    refine ⟨e, ?_, ?_, ?_⟩
    · rw [Finset.mem_Icc]
      refine ⟨he, ?_⟩
      have h1 : e ^ (6 * G.natDegree) < (Y + 1) ^ (6 * G.natDegree) :=
        lt_of_le_of_lt (hpow.trans (Nat.mul_le_mul_left _ hvM)) hY
      have h2 : e < Y + 1 := lt_of_pow_lt_pow_left₀ _ (Nat.zero_le _) h1
      omega
    · exact (Finset.card_le_card
        (Nat.divisors_subset_of_dvd hm.ne' (Dvd.intro_left _ rfl))).trans hcard
    · intro p b hp hb hpe
      rw [hev]
      exact_mod_cast hdiv p b hp hb hpe
  refine sum_core G.natDegree a A B Y hk v
    (fun e n => ∀ p b : ℕ, p.Prime → 1 ≤ b → p ^ b ∣ e →
      ((p : ℤ) ^ (1 + G.natDegree * (b - 1))) ∣ G.eval ((a * n : ℕ) : ℤ)) step1 ?_
  intro e he
  have he1 : 0 < e := (Finset.mem_Icc.mp he).1
  exact (count_root_condition G hG e he1 a A B ha).trans (Nat.mul_le_mul_right _ (pow_card_primeFactors_le G.natDegree e he1))

theorem discrete_divisor_mean (F : ℤ[X]) (hk : 1 ≤ F.natDegree) (ha : 0 < F.leadingCoeff)
    (A B M Y : ℕ)
    (hpos : ∀ n ∈ Finset.Icc A B, 0 < F.eval (n : ℤ) ∧ (F.eval (n : ℤ)).toNat ≤ M)
    (hY : F.leadingCoeff.toNat ^ (F.natDegree - 1) * M < (Y + 1) ^ (6 * F.natDegree)) :
    ∑ n ∈ Finset.Icc A B, (((F.eval (n : ℤ)).toNat.divisors.card : ℝ)) ^ 2 ≤
      ((6 * F.natDegree : ℕ) : ℝ) ^ (12 * F.natDegree) *
        ((F.leadingCoeff.toNat * (B - A) + Y : ℕ) : ℝ) *
        (1 + Real.log Y) ^ (2 ^ (2 ^ (72 * F.natDegree ^ 2 + F.natDegree))) := by
  have hF0 : F ≠ 0 := by
    rintro rfl
    simp at ha
  obtain ⟨a, ha'⟩ : ∃ a : ℕ, (a : ℤ) = F.leadingCoeff :=
    ⟨F.leadingCoeff.toNat, Int.toNat_of_nonneg ha.le⟩
  have hat : F.leadingCoeff.toNat = a := by
    rw [← ha']
    exact Int.toNat_natCast a
  rw [hat] at hY ⊢
  have ha0 : 0 < a := by
    have h : (0 : ℤ) < (a : ℤ) := by
      rw [ha']
      exact ha
    exact_mod_cast h
  refine monic_core F.integralNormalization (monic_integralNormalization hF0)
    F.natDegree a A B M Y hk natDegree_integralNormalization ha0
    (fun n => (F.eval (n : ℤ)).toNat) (fun n hn => ?_) hY
  obtain ⟨h0, hM⟩ := hpos n hn
  have hvn : ((F.eval (n : ℤ)).toNat : ℤ) = F.eval (n : ℤ) := Int.toNat_of_nonneg h0.le
  refine ⟨by omega, hM, ?_⟩
  have key := integralNormalization_eval₂_leadingCoeff_mul hk (RingHom.id ℤ) (n : ℤ)
  simp only [eval₂_id, RingHom.id_apply] at key
  rw [← ha'] at key
  rw [Nat.cast_mul, Nat.cast_mul, Nat.cast_pow, hvn, key]

end LeanLab.Perelli1996.DivMean

#print axioms LeanLab.Perelli1996.DivMean.discrete_divisor_mean
