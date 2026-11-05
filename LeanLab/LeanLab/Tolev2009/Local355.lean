/-
AI wrote this Lean code. Codex task355.
Binary Goldbach is open.
Source: Halupczok 2008 pages 14 to 17, the common prime power factors.
-/
import LeanLab.Tolev2009.CRT355
import LeanLab.Tolev2009.Displays14to16

open Finset Real
namespace LeanLab.Tolev2009.Local355
open LeanLab.Tolev2009.Faithful LeanLab.Tolev2009.SeriesIdentification

/-- Halupczok page 14, a denominator dividing the modulus fixes one coefficient residue. -/
theorem coeffRes_of_dvd (k l q : ℕ) (hq : 1 ≤ q) (hqk : q ∣ k) (hl : Nat.Coprime l k) :
    coeffRes k l q = {l % q} := by
  have hlq : Nat.Coprime l q := hl.coprime_dvd_right hqk
  ext r
  simp only [coeffRes, Nat.gcd_eq_right hqk, mem_filter, mem_range, mem_singleton]
  constructor
  · rintro ⟨hr, hcop, he⟩
    simpa only [Nat.mod_eq_of_lt hr] using he
  · rintro rfl
    refine ⟨Nat.mod_lt _ (by omega), ?_, Nat.mod_mod _ _⟩
    exact (coprime_modEq q (l % q) l (Nat.mod_mod _ _)).mpr hlq

/-- Halupczok page 14, the restricted coefficient is a single exponential in this case. -/
theorem coeff_of_dvd (k l q a : ℕ) (hq : 1 ≤ q) (hqk : q ∣ k) (hl : Nat.Coprime l k) :
    coeff k l q a = ee ((a : ℝ) * l / q) := by
  rw [coeff, coeffRes_of_dvd k l q hq hqk hl, sum_singleton]
  exact (ee_rat_mod a l q hq).symm

/-- Halupczok page 14, the normalized local factor has unit norm for a dividing denominator. -/
theorem localSum_of_dvd (k l q a : ℕ) (hk : 1 ≤ k) (hq : 1 ≤ q)
    (hqk : q ∣ k) (hl : Nat.Coprime l k) :
    localSum k l q a = ee ((a : ℝ) * l / q) := by
  have hφ : (k.totient : ℂ) ≠ 0 := by
    exact_mod_cast (Nat.totient_pos.mpr hk).ne'
  rw [localSum_eq_coeff k l q a hk hq hl, Nat.lcm_eq_left hqk,
    div_self hφ, one_mul, coeff_of_dvd k l q a hq hqk hl]

/-- Halupczok page 14, common denominator coefficients have norm at most phi q.
The bound also covers residues failing the source compatibility condition. -/
theorem ssTerm_norm_of_dvd (k l : Fin 3 → ℕ) (N q : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hq : 1 ≤ q) (hqk : ∀ i, q ∣ k i) : ‖ssTerm k l N q‖ ≤ q.totient := by
  unfold ssTerm
  calc
    _ ≤ ∑ a ∈ (range q).filter (fun a => Nat.Coprime a q),
        ‖ee (-((a : ℝ) * N / q)) * ∏ i : Fin 3, localSum (k i) (l i) q a‖ := norm_sum_le _ _
    _ = ∑ _a ∈ (range q).filter (fun a => Nat.Coprime a q), (1 : ℝ) := by
      apply sum_congr rfl
      intro a ha
      simp_rw [norm_mul, norm_prod, localSum_of_dvd _ _ _ _ (hk _) hq (hqk _) (hl _),
        LeanLab.Tolev2009.Displays14to16.norm_ee]
      simp
    _ = _ := by simp [Nat.totient_eq_card_coprime, Nat.coprime_comm]

/-- Halupczok page 17, the scalar sum of common prime power first moments telescopes. -/
theorem prime_power_moment (p γ : ℕ) (hp : p.Prime) :
    1 + ∑ j ∈ Icc 1 γ, ((p ^ j : ℕ) : ℝ) * ((p ^ j).totient : ℝ) ≤
      (p : ℝ) ^ (2 * γ) := by
  induction γ with
  | zero => simp
  | succ γ ih =>
    rw [sum_Icc_succ_top (by omega)]
    have hpR : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
    have he : (p : ℝ) ^ (2 * (γ + 1)) = (p : ℝ) ^ (2 * γ) * (p : ℝ) ^ 2 := by
      rw [show 2 * (γ + 1) = 2 * γ + 2 by omega, pow_add]
    have ht : ((p ^ (γ + 1) : ℕ) : ℝ) * ((p ^ (γ + 1)).totient : ℝ) =
        (p : ℝ) ^ (2 * γ) * p * ((p : ℝ) - 1) := by
      rw [Nat.totient_prime_pow_succ hp, Nat.cast_mul, Nat.cast_pow,
        Nat.cast_sub hp.one_le, Nat.cast_one, Nat.cast_pow,
        show 2 * γ = γ + γ by omega, pow_add, pow_succ]
      ring
    rw [ht]
    calc
      _ ≤ (p : ℝ) ^ (2 * γ) + (p : ℝ) ^ (2 * γ) * p * ((p : ℝ) - 1) := by linarith
      _ = (p : ℝ) ^ (2 * γ) * (1 + p * ((p : ℝ) - 1)) := by ring
      _ ≤ (p : ℝ) ^ (2 * γ) * (p : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left (by nlinarith) (pow_nonneg (Nat.cast_nonneg p) _)
      _ = _ := he.symm

/-- Halupczok pages 16 to 17, bound the complete common prime power Euler factor. -/
theorem common_prime_factor (k l : Fin 3 → ℕ) (N p γ : ℕ) (hp : p.Prime)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i))
    (hpk : ∀ i, p ^ γ ∣ k i) :
    1 + ∑ j ∈ Icc 1 γ, ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖ ≤
      (p : ℝ) ^ (2 * γ) := by
  calc
    _ ≤ 1 + ∑ j ∈ Icc 1 γ, ((p ^ j : ℕ) : ℝ) * ((p ^ j).totient : ℝ) := by
      apply add_le_add le_rfl
      apply sum_le_sum
      intro j hj
      exact mul_le_mul_of_nonneg_left
        (ssTerm_norm_of_dvd k l N (p ^ j) hk hl (Nat.one_le_pow _ _ hp.one_le)
          (fun i => (pow_dvd_pow p (mem_Icc.mp hj).2).trans (hpk i))) (Nat.cast_nonneg _)
    _ ≤ _ := prime_power_moment p γ hp

/-- Halupczok page 17, multiply all common prime power factors to obtain the common gcd squared. -/
theorem common_prime_product (k l : Fin 3 → ℕ) (N : ℕ)
    (hk : ∀ i, 1 ≤ k i) (hl : ∀ i, Nat.Coprime (l i) (k i)) :
    let d := Nat.gcd (Nat.gcd (k 0) (k 1)) (k 2)
    (∏ p ∈ d.primeFactors,
      (1 + ∑ j ∈ Icc 1 (d.factorization p), ((p ^ j : ℕ) : ℝ) * ‖ssTerm k l N (p ^ j)‖)) ≤
        (d : ℝ) ^ 2 := by
  dsimp only
  let d := Nat.gcd (Nat.gcd (k 0) (k 1)) (k 2)
  have hd : 0 < d := Nat.gcd_pos_of_pos_left (k 2) (Nat.gcd_pos_of_pos_left (k 1) (hk 0))
  have hdk : ∀ i, d ∣ k i := by
    intro i
    fin_cases i
    · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_left _ _)
    · exact (Nat.gcd_dvd_left _ _).trans (Nat.gcd_dvd_right _ _)
    · exact Nat.gcd_dvd_right _ _
  calc
    _ ≤ ∏ p ∈ d.primeFactors, (p : ℝ) ^ (2 * d.factorization p) := by
      apply prod_le_prod₀
      · intro p hp
        positivity
      · intro p hp
        have hprime := Nat.prime_of_mem_primeFactors hp
        exact common_prime_factor k l N p (d.factorization p) hprime hk hl
          (fun i => ((hprime.pow_dvd_iff_le_factorization hd.ne').mpr le_rfl).trans (hdk i))
    _ = (∏ p ∈ d.primeFactors, (p : ℝ) ^ d.factorization p) ^ 2 := by
      rw [← prod_pow]
      apply prod_congr rfl
      intro p hp
      rw [← pow_mul, Nat.mul_comm]
    _ = _ := by
      have he : (∏ p ∈ d.primeFactors, (p : ℝ) ^ d.factorization p) = d := by
        exact_mod_cast (Nat.prod_primeFactors_pow_factorization hd.ne').symm
      rw [he]

/-- Halupczok page 16, the coefficient free triangle envelope cannot prove summability.
This is an implementation obstruction, not an error in the paper. -/
theorem naive_majorant_not_summable :
    ¬ Summable (fun q : ℕ => (q : ℝ) * (q.totient : ℝ)) := by
  intro hs
  have hs' : Summable (fun n : ℕ => ((n + 1 : ℕ) : ℝ) * ((n + 1).totient : ℝ)) :=
    hs.comp_injective Nat.succ_injective
  have hlow (n : ℕ) : (1 : ℝ) ≤ ((n + 1 : ℕ) : ℝ) * ((n + 1).totient : ℝ) := by
    exact_mod_cast Nat.mul_pos (Nat.succ_pos n) (Nat.totient_pos.mpr (Nat.succ_pos n))
  have hone : Summable (fun _ : ℕ => (1 : ℝ)) :=
    hs'.of_nonneg_of_le (fun _ => by norm_num) hlow
  have hbad : (0 : ℝ) < -1 := Real.summable_nat_rpow.mp (by simpa using hone)
  norm_num at hbad

end LeanLab.Tolev2009.Local355
