/-
P0083 Perelli 1996, pages 486 and 487, equations 26 through 32.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.DecompJ228
import LeanLab.Perelli1996.Definitions103

namespace LeanLab.Perelli1996.Decomp289a
open Finset Real Polynomial MeasureTheory
open LeanLab.Perelli1996.Decomp88
noncomputable section

/-- The order Q of the Section 3 dissection on page 486. -/
def meanOrder (F : ℤ[X]) (N H B : ℝ) : ℝ :=
  H ^ F.natDegree * Real.log N ^ (-B)

/-- The nonnegative remainder sum Sigma P below equation 27 on page 486.
Reduced residues use representatives one through q, as in the paper.
The existing characterRemainder uses an inclusive cutoff with a zero term
in its principal kernel. This is the endpoint variant of the printed sum. -/
def remainderMass (F : ℤ[X]) (c N H B : ℝ) : ℝ :=
  ∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊,
    ∑ a ∈ (Icc 1 q).filter (fun a => Nat.Coprime a q),
      ∫ η in Set.Icc (-(1 / ((q : ℝ) * meanOrder F N H B)))
        (1 / ((q : ℝ) * meanOrder F N H B)),
        ‖characterRemainder ⌊c * N⌋₊ q (a : ℤ) η‖ ^ 2

/-- The remainder mass is nonnegative, as a sum of squared norms. -/
theorem remainderMass_nonneg (F : ℤ[X]) (c N H B : ℝ) :
    0 ≤ remainderMass F c N H B := by
  unfold remainderMass
  positivity

/-- LEAF. Pages 486 and 487, equations 26 through 28.
The circle method compares the prime mean with the weighted singular mean.
This retains the character remainder instead of assuming its saving. -/
theorem leaf_weighted_mean (F : ℤ[X]) (hF : Admissible F)
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∃ B c C N₀ : ℝ, 0 < B ∧ 0 < c ∧ 0 < C ∧ 3 ≤ N₀ ∧
      ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      |(∑ n ∈ win F N H, R (Fv F n).toNat) -
        ∑ n ∈ win F N H, (Fv F n : ℝ) * Sing (Fv F n).toNat| ≤
        C * H * (remainderMass F c N H B +
          Real.sqrt (N * Real.log N * remainderMass F c N H B)) +
        C * H * N * Real.log N ^ (-A) := by
  -- ATTEMPT 1 of 3: use the proved mean square input of Theorem 1 on this window.
  -- The Lean error of our own attempt was
  --   Application type mismatch: The argument hH has type
  --     N ^ (1 / (6 * ↑F.natDegree) + ε) ≤ H
  --   but is expected to have type
  --     N ^ (1 / (3 * ↑F.natDegree) + ε / 2) ≤ H
  --   in the application hK N H hNK hH
  -- so the mean square input stops at windows of length N ^ (1 / (3k) + ε / 2)
  -- while this leaf starts at N ^ (1 / (6k) + ε).
  -- ATTEMPT 2 of 3: dominate the error with the remainder mass term. The trivial
  -- bound |R m| ≤ m (log m) ^ 2 together with abs_sing_le_cube gives a left hand
  -- side of size C H N (log N) ^ 2, so this route needs
  --   remainderMass F c N H B ≥ c N (log N) ^ 2
  -- which needs the Chebyshev level estimate sum over n ≤ M of n Λ n ≥ c M ^ 2 log M.
  -- Mathlib only has Chebyshev.psi_ge and Chebyshev.theta_ge with theta n ≥ c n,
  -- so the peak of the character remainder gives at best a mass of order N.
  -- ATTEMPT 3 of 3: use the circle method expansion of the paper with the
  -- remainderMass and square root terms of equations 26 to 28. No such identity
  -- exists in this repository and the character input it needs is open.
  -- BLOCKED: OUT OF REACH. Missing result: the character expansion of the window
  -- sum of R (Fv F n).toNat - (Fv F n) * Sing (Fv F n).toNat with the error split
  -- into C H remainderMass, C H sqrt (N log N remainderMass) and C H N log ^ (-A),
  -- as in Perelli 1996 pages 486 and 487 equations 26 to 28, together with a
  -- Chebyshev level lower bound for the von Mangoldt weighted moment.
  sorry



/-- The reciprocal divisor sum is at most the harmonic sum. -/
private theorem sum_divisors_inv_le (n : ℕ) (hn : 1 ≤ n) :
    (∑ d ∈ n.divisors, ((d : ℝ))⁻¹) ≤ 1 + Real.log n := by
  have hn0 : n ≠ 0 := by omega
  have hsub : n.divisors ⊆ Finset.Icc 1 n := by
    intro d hd
    exact Finset.mem_Icc.mpr ⟨Nat.pos_of_mem_divisors hd,
      Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_divisors hd)⟩
  have h1 : (∑ d ∈ n.divisors, ((d : ℝ))⁻¹) ≤ ∑ d ∈ Finset.Icc 1 n, ((d : ℝ))⁻¹ :=
    Finset.sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ => by positivity)
  have h2 : (∑ d ∈ Finset.Icc 1 n, ((d : ℝ))⁻¹) = (harmonic n : ℝ) := by
    simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
  rw [h2] at h1
  exact h1.trans (harmonic_le_one_add_log n)

/-- The singular series is at most a constant times a cube of a logarithm. -/
private theorem abs_sing_le_cube (n : ℕ) (hn : 1 ≤ n) :
    |LeanLab.Perelli1996.Sing n| ≤
      (|LeanLab.Perelli1996.Section3.singularConstant| + 1) * (8 * (1 + Real.log n) ^ 3) := by
  classical
  have hn0 : n ≠ 0 := by omega
  have hlog0 : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn)
  have hbase : (0 : ℝ) ≤ 1 + Real.log n := by linarith
  rcases Nat.even_or_odd n with he | ho
  · have hSdef' : LeanLab.Perelli1996.Sing n =
        LeanLab.Perelli1996.Section3.singularConstant *
          ∑ d ∈ n.divisors, LeanLab.Perelli1996.Section3.arithmeticFactor d :=
      LeanLab.Perelli1996.Section3.sing_even_divisor_sum n hn0 he
    rw [hSdef']
    have hS0 : 0 ≤ ∑ d ∈ n.divisors, LeanLab.Perelli1996.Section3.arithmeticFactor d :=
      Finset.sum_nonneg (fun d _ => LeanLab.Perelli1996.Section3.arithmeticFactor_nonneg d)
    have hdiv : (∑ d ∈ n.divisors, ((d : ℝ))⁻¹) ≤ 1 + Real.log n :=
      sum_divisors_inv_le n hn
    have hterm : (∑ d ∈ n.divisors, LeanLab.Perelli1996.Section3.arithmeticFactor d) ≤
        8 * (1 + Real.log n) ^ 3 := by
      have hstep : ∀ d ∈ n.divisors,
          LeanLab.Perelli1996.Section3.arithmeticFactor d ≤
            8 * (1 + Real.log n) ^ 2 * ((d : ℝ))⁻¹ := by
        intro d hd
        have hd1 : 1 ≤ d := Nat.pos_of_mem_divisors hd
        have hdn : d ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) (Nat.dvd_of_mem_divisors hd)
        have hdR : (0 : ℝ) < d := by exact_mod_cast hd1
        have hlogd : Real.log d ≤ Real.log n := by
          apply Real.log_le_log (by exact_mod_cast hd1)
          exact_mod_cast hdn
        have hlogd0 : 0 ≤ Real.log d := Real.log_nonneg (by exact_mod_cast hd1)
        have hsq : (1 + Real.log d) ^ 2 ≤ (1 + Real.log n) ^ 2 :=
          pow_le_pow_left₀ (by linarith) (by linarith) 2
        have hb : LeanLab.Perelli1996.Section3.arithmeticFactor d ≤
            8 * (1 + Real.log d) ^ 2 / (d : ℝ) :=
          LeanLab.Perelli1996.Section3.arithmeticFactor_le d hd1
        have h8 : 8 * (1 + Real.log d) ^ 2 / (d : ℝ) ≤
            8 * (1 + Real.log n) ^ 2 / (d : ℝ) := by
          apply div_le_div_of_nonneg_right _ hdR.le
          nlinarith
        calc LeanLab.Perelli1996.Section3.arithmeticFactor d
            ≤ 8 * (1 + Real.log n) ^ 2 / (d : ℝ) := hb.trans h8
          _ = 8 * (1 + Real.log n) ^ 2 * ((d : ℝ))⁻¹ := by rw [div_eq_mul_inv]
      calc (∑ d ∈ n.divisors, LeanLab.Perelli1996.Section3.arithmeticFactor d)
          ≤ ∑ d ∈ n.divisors, 8 * (1 + Real.log n) ^ 2 * ((d : ℝ))⁻¹ :=
            Finset.sum_le_sum hstep
        _ = 8 * (1 + Real.log n) ^ 2 * ∑ d ∈ n.divisors, ((d : ℝ))⁻¹ := by
            rw [Finset.mul_sum]
        _ ≤ 8 * (1 + Real.log n) ^ 2 * (1 + Real.log n) :=
            mul_le_mul_of_nonneg_left hdiv (by positivity)
        _ = 8 * (1 + Real.log n) ^ 3 := by ring
    rw [abs_mul, abs_of_nonneg hS0]
    have hfin : |LeanLab.Perelli1996.Section3.singularConstant| *
          (∑ d ∈ n.divisors, LeanLab.Perelli1996.Section3.arithmeticFactor d)
        ≤ (|LeanLab.Perelli1996.Section3.singularConstant| + 1) *
            (8 * (1 + Real.log n) ^ 3) :=
      mul_le_mul (by linarith) hterm hS0 (by positivity)
    exact hfin
  · rw [LeanLab.Perelli1996.Section3.sing_odd_zero n ho, abs_zero]
    have h3 : (0:ℝ) ≤
        (|LeanLab.Perelli1996.Section3.singularConstant| + 1) * (8 * (1 + Real.log n) ^ 3) :=
      by positivity
    exact h3

/-- On the polynomial window the value `F n` is within `c H N^{(k-1)/k}` of `a_k N`, and at
least one. -/
private theorem window_bound (F : ℤ[X]) (hF : Admissible F) :
    ∃ c N₁ : ℝ, 0 < c ∧ 1 ≤ N₁ ∧ ∀ (N H : ℝ), N₁ ≤ N →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) → 1 ≤ H → ∀ n : ℕ, n ∈ win F N H →
        |((Fv F n : ℝ) - (F.leadingCoeff : ℝ) * N)| ≤
          c * H * N ^ (((F.natDegree : ℝ) - 1) / (F.natDegree : ℝ)) ∧
        1 ≤ (Fv F n : ℝ) := by
  classical
  obtain ⟨hk1, hlc⟩ := hF
  have hk0 : 0 < F.natDegree := by omega
  have hkR : (0 : ℝ) < (F.natDegree : ℝ) := by exact_mod_cast hk0
  have hk1R : (1 : ℝ) ≤ (F.natDegree : ℝ) := by exact_mod_cast hk1
  set a : ℝ := ((F.leadingCoeff : ℤ) : ℝ) with ha_def
  have ha : 0 < a := by
    rw [ha_def]; exact_mod_cast hlc
  set B : ℝ := ∑ i ∈ range F.natDegree, |((F.coeff i : ℤ) : ℝ)| with hB_def
  have hB0 : 0 ≤ B := Finset.sum_nonneg (fun i _ => abs_nonneg _)
  refine ⟨(B + a * (F.natDegree : ℝ) + 1) * 2 ^ (F.natDegree + 1),
    max 1 (max (2 ^ F.natDegree) (((B + 1) / a) ^ F.natDegree)), ?_, ?_, ?_⟩
  · have : (0:ℝ) < 2 ^ F.natDegree := by positivity
    have : (0:ℝ) < B + a * (F.natDegree : ℝ) + 1 := by
      have : (0:ℝ) < a * (F.natDegree : ℝ) := by positivity
      linarith
    positivity
  · exact le_max_left _ _
  intro N H hN hHle hH1 n hn
  set r : ℝ := N ^ (1 / (F.natDegree : ℝ)) with hr_def
  have hN1 : (1:ℝ) ≤ N := le_trans (le_max_left _ _) hN
  have hN0 : (0:ℝ) < N := lt_of_lt_of_le one_pos hN1
  have hN0le : (0:ℝ) ≤ N := hN0.le
  have hr_pos : (0:ℝ) < r := Real.rpow_pos_of_pos hN0 _
  have hr1 : (1:ℝ) ≤ r := by
    have h : (1:ℝ) ^ (1 / (F.natDegree : ℝ)) ≤ r := by
      rw [hr_def]
      apply Real.rpow_le_rpow (by norm_num) hN1
      positivity
    simpa using h
  have hrk : r ^ (F.natDegree : ℝ) = N := by
    rw [hr_def, ← Real.rpow_mul hN0le]
    have h1 : 1 / (F.natDegree : ℝ) * (F.natDegree : ℝ) = 1 := by
      field_simp
    rw [h1, Real.rpow_one]
  have hrk' : r ^ F.natDegree = N := by
    rw [← Real.rpow_natCast r F.natDegree, hrk]
  have hbig : ((B + 1) / a) ≤ r := by
    have hbase0 : (0:ℝ) ≤ (B + 1) / a := by positivity
    have hle : (((B + 1) / a) ^ F.natDegree) ≤ N := by
      refine le_trans ?_ hN
      exact le_trans (le_max_right (2 ^ F.natDegree) _) (le_max_right 1 _)
    have h2 : ((((B + 1) / a) ^ F.natDegree) : ℝ) ^ (1 / (F.natDegree : ℝ)) ≤ r := by
      rw [hr_def]
      apply Real.rpow_le_rpow (by positivity) hle
      positivity
    have h3 : ((((B + 1) / a) ^ F.natDegree) : ℝ) ^ (1 / (F.natDegree : ℝ)) = (B + 1) / a := by
      rw [← Real.rpow_natCast ((B + 1) / a) F.natDegree, ← Real.rpow_mul hbase0]
      have h1 : ((F.natDegree : ℝ)) * (1 / (F.natDegree : ℝ)) = 1 := by
        field_simp
      rw [h1, Real.rpow_one]
    rwa [h3] at h2
  -- membership in the window
  have hmem : (⌈r⌉₊ : ℕ) ≤ n ∧ n ≤ ⌊r + H⌋₊ := by
    have h := hn
    rw [win, Finset.mem_Icc] at h
    exact h
  have hnR : r ≤ (n : ℝ) := le_trans (Nat.le_ceil r) (by exact_mod_cast hmem.1)
  have hnRH : (n : ℝ) ≤ r + H := by
    have h2 : (n : ℝ) ≤ (⌊r + H⌋₊ : ℝ) := by exact_mod_cast hmem.2
    refine h2.trans (Nat.floor_le ?_)
    positivity
  have hn2r : (n : ℝ) ≤ 2 * r := by
    have := hHle
    linarith
  have hn1 : (1:ℝ) ≤ (n : ℝ) := le_trans hr1 hnR
  have hn0 : (0:ℝ) ≤ (n : ℝ) := le_trans zero_le_one hn1
  -- the value as a real polynomial sum
  set k := F.natDegree with hk_def
  have hval : ((Fv F n : ℝ)) = ∑ i ∈ range (k + 1), ((F.coeff i : ℤ) : ℝ) * (n : ℝ) ^ i := by
    unfold Fv
    rw [Polynomial.eval_eq_sum_range]
    push_cast
    simp [hk_def]
  have hcoeff : ((F.coeff k : ℤ) : ℝ) = a := by
    rw [hk_def, Polynomial.coeff_natDegree, ha_def]
  have hsplit : ((Fv F n : ℝ)) - a * (n:ℝ) ^ k =
      ∑ i ∈ range k, ((F.coeff i : ℤ) : ℝ) * (n : ℝ) ^ i := by
    rw [hval, Finset.sum_range_succ, hcoeff]
    ring
  -- lower terms
  have hlow : |∑ i ∈ range k, ((F.coeff i : ℤ) : ℝ) * (n : ℝ) ^ i| ≤ B * (2*r) ^ (k - 1) := by
    have hterm : ∀ i ∈ range k, |((F.coeff i : ℤ) : ℝ) * (n : ℝ) ^ i| ≤
        |((F.coeff i : ℤ) : ℝ)| * (2*r) ^ (k-1) := by
      intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      have hnk : (n:ℝ) ^ i ≤ (n:ℝ) ^ (k-1) := by
        apply pow_le_pow_right₀ hn1 (by omega)
      have h1 : |(n:ℝ) ^ i| ≤ (2*r) ^ (k-1) := by
        rw [abs_of_nonneg (by positivity)]
        exact hnk.trans (pow_le_pow_left₀ hn0 hn2r _)
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
    calc |∑ i ∈ range k, ((F.coeff i : ℤ) : ℝ) * (n : ℝ) ^ i|
        ≤ ∑ i ∈ range k, |((F.coeff i : ℤ) : ℝ) * (n : ℝ) ^ i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range k, |((F.coeff i : ℤ) : ℝ)| * (2*r) ^ (k-1) := Finset.sum_le_sum hterm
      _ = B * (2*r) ^ (k-1) := by rw [← Finset.sum_mul, hB_def]
  -- the top term difference
  have hgeom : (∑ i ∈ range k, (n:ℝ) ^ i * r ^ (k - 1 - i)) * ((n:ℝ) - r) = (n:ℝ)^k - r^k :=
    geom_sum₂_mul_of_ge hnR k
  have hgeom_bound : |(∑ i ∈ range k, (n:ℝ) ^ i * r ^ (k - 1 - i))| ≤ k * (2*r) ^ (k-1) := by
    have hterm : ∀ i ∈ range k, |(n:ℝ) ^ i * r ^ (k - 1 - i)| ≤ (2*r) ^ (k-1) := by
      intro i hi
      have hik : i < k := Finset.mem_range.mp hi
      have h1 : (n:ℝ) ^ i ≤ (2*r) ^ i := pow_le_pow_left₀ hn0 hn2r i
      have h2 : r ^ (k - 1 - i) ≤ (2*r) ^ (k - 1 - i) := by
        apply pow_le_pow_left₀ hr_pos.le
        linarith
      have h3 : (2*r) ^ i * (2*r) ^ (k - 1 - i) = (2*r) ^ (k-1) := by
        rw [← pow_add]
        congr 1
        omega
      rw [abs_mul]
      calc |(n:ℝ) ^ i| * |r ^ (k - 1 - i)| = (n:ℝ) ^ i * r ^ (k-1-i) := by
            rw [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)]
        _ ≤ (2*r) ^ i * (2*r) ^ (k - 1 - i) := by
            apply mul_le_mul h1 h2 (by positivity) (by positivity)
        _ = (2*r) ^ (k-1) := h3
    calc |∑ i ∈ range k, (n:ℝ) ^ i * r ^ (k - 1 - i)|
        ≤ ∑ i ∈ range k, |(n:ℝ) ^ i * r ^ (k - 1 - i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ range k, (2*r) ^ (k-1) := Finset.sum_le_sum hterm
      _ = k * (2*r) ^ (k-1) := by
          rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  have htop : |(n:ℝ)^k - r^k| ≤ k * (2*r)^(k-1) * (H + 1) := by
    have hd : |(n:ℝ) - r| ≤ H + 1 := by
      rw [abs_of_nonneg (by linarith)]
      linarith
    have := hgeom
    rw [← this, abs_mul]
    calc |∑ i ∈ range k, (n:ℝ) ^ i * r ^ (k - 1 - i)| * |(n:ℝ) - r|
        ≤ (k * (2*r)^(k-1)) * (H+1) := mul_le_mul hgeom_bound hd (abs_nonneg _) (by positivity)
      _ = k * (2*r)^(k-1) * (H+1) := by ring
  -- combine
  have hpow_eq : (2*r)^(k-1) ≤ 2^k * N ^ (((k:ℝ) - 1) / (k:ℝ)) := by
    have key : N ^ (((k:ℝ) - 1) / (k:ℝ)) = r ^ (k-1) := by
      have h1 : r ^ (k-1) = r ^ ((k:ℝ) - 1) := by
        rw [← Real.rpow_natCast r (k-1)]
        congr 1
        rw [Nat.cast_sub hk1]
        norm_num
      rw [h1, hr_def, ← Real.rpow_mul hN0le]
      congr 1
      field_simp
    have h2 : (2:ℝ) ^ (k-1) ≤ 2^k := pow_le_pow_right₀ (by norm_num) (by omega)
    calc (2*r)^(k-1) = 2^(k-1) * r^(k-1) := by rw [mul_pow]
      _ = 2^(k-1) * N ^ (((k:ℝ) - 1) / (k:ℝ)) := by rw [key]
      _ ≤ 2^k * N ^ (((k:ℝ) - 1) / (k:ℝ)) :=
          mul_le_mul_of_nonneg_right h2 (by positivity)
  have hkey : ((Fv F n : ℝ)) - a * N =
      (∑ i ∈ range k, ((F.coeff i : ℤ) : ℝ) * (n : ℝ) ^ i) + a * ((n:ℝ)^k - r^k) := by
    rw [← hrk', ← hsplit]
    ring
  have ht0 : (0:ℝ) ≤ N ^ (((k:ℝ) - 1) / (k:ℝ)) := by positivity
  have h2k : (0:ℝ) < 2 ^ k := by positivity
  constructor
  · calc |((Fv F n : ℝ)) - a * N|
        = |(∑ i ∈ range k, ((F.coeff i : ℤ) : ℝ) * (n : ℝ) ^ i) + a * ((n:ℝ)^k - r^k)| := by
            rw [hkey]
      _ ≤ |∑ i ∈ range k, ((F.coeff i : ℤ) : ℝ) * (n : ℝ) ^ i| + |a * ((n:ℝ)^k - r^k)| :=
            abs_add_le _ _
      _ ≤ B * (2*r)^(k-1) + a * (k * (2*r)^(k-1) * (H+1)) := by
            have h2 : |a * ((n:ℝ)^k - r^k)| = a * |(n:ℝ)^k - r^k| := by
              rw [abs_mul, abs_of_pos ha]
            rw [h2]
            exact add_le_add hlow (mul_le_mul_of_nonneg_left htop ha.le)
      _ ≤ (B + a * (k:ℝ) + 1) * 2 ^ (k+1) * H * N ^ (((k:ℝ) - 1) / (k:ℝ)) := by
            set S : ℝ := 2 ^ k * N ^ (((k:ℝ) - 1) / (k:ℝ)) with hSdef
            have hS0 : (0:ℝ) ≤ S := by rw [hSdef]; positivity
            have hAk : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
            have e1 : (2*r)^(k-1) ≤ S := by rw [hSdef]; exact hpow_eq
            have hH1' : H + 1 ≤ 2 * H := by linarith
            have e3 : (2*r)^(k-1) * (H+1) ≤ S * (2*H) :=
              mul_le_mul e1 hH1' (by linarith) hS0
            have hTA : B * (2*r)^(k-1) ≤ B * S := mul_le_mul_of_nonneg_left e1 hB0
            have hTC : a * (k * ((2*r)^(k-1) * (H+1))) ≤ a * (k * (S * (2*H))) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left e3 hAk) ha.le
            have hpow : (B + a * (k:ℝ) + 1) * (2:ℝ)^(k+1) * H *
                N ^ (((k:ℝ) - 1) / (k:ℝ)) = (B + a*(k:ℝ) + 1) * (S * (2*H)) := by
              rw [hSdef, pow_succ]; ring
            rw [hpow]
            have h2H : (1:ℝ) ≤ 2*H := by linarith
            have hB1 : B*S ≤ B*S*(2*H) := by
              calc B*S = B*S*1 := by ring
                _ ≤ B*S*(2*H) := mul_le_mul_of_nonneg_left h2H (by positivity)
            have hexp : (B + a*(k:ℝ) + 1)*(S*(2*H)) =
                B*S*(2*H) + a*(k:ℝ)*(S*(2*H)) + S*(2*H) := by ring
            rw [hexp]
            have h3 : (0:ℝ) ≤ S*(2*H) := by positivity
            linarith [hTA, hTC, hB1, h3]

  · -- the value is at least one
    have hbig2 : B + 1 ≤ a * r := by
      rw [div_le_iff₀ ha] at hbig
      linarith
    have hsom : |∑ i ∈ range k, ((F.coeff i : ℤ) : ℝ) * (n : ℝ) ^ i| ≤ B * (n:ℝ)^(k-1) := by
      calc |∑ i ∈ range k, ((F.coeff i : ℤ) : ℝ) * (n : ℝ) ^ i|
          ≤ ∑ i ∈ range k, |((F.coeff i : ℤ) : ℝ) * (n : ℝ) ^ i| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i ∈ range k, |((F.coeff i : ℤ) : ℝ)| * (n:ℝ)^(k-1) := by
            apply Finset.sum_le_sum
            intro i hi
            have hik : i < k := Finset.mem_range.mp hi
            have hnk : (n:ℝ) ^ i ≤ (n:ℝ) ^ (k-1) := pow_le_pow_right₀ hn1 (by omega)
            have hnn : (0:ℝ) ≤ (n:ℝ) ^ i := by positivity
            rw [abs_mul, abs_of_nonneg hnn]
            exact mul_le_mul_of_nonneg_left hnk (abs_nonneg _)
        _ = B * (n:ℝ)^(k-1) := by rw [← Finset.sum_mul, hB_def]
    have hval1 : a * (n:ℝ)^k - B*(n:ℝ)^(k-1) ≤ ((Fv F n : ℝ)) := by
      have := (abs_le.mp hsom).1
      linarith [hsplit]
    have hnp : (1:ℝ) ≤ (n:ℝ)^(k-1) := one_le_pow₀ hn1
    have h5 : (1:ℝ) ≤ a*(n:ℝ) - B := by
      have : a*r ≤ a*(n:ℝ) := by nlinarith [hnR, ha]
      linarith
    have hstep : (1:ℝ) ≤ a*(n:ℝ)^k - B*(n:ℝ)^(k-1) := by
      have hpow : (n:ℝ)^k = (n:ℝ)^(k-1) * (n:ℝ) := by
        have hk2 : k = (k-1)+1 := by omega
        conv_lhs => rw [hk2]
        rw [pow_succ]
      rw [hpow]
      have hmul : a * ((n:ℝ)^(k-1) * (n:ℝ)) - B * (n:ℝ)^(k-1)
          = (n:ℝ)^(k-1) * (a*(n:ℝ) - B) := by ring
      rw [hmul]
      nlinarith [hnp, h5]
    linarith [hval1, hstep]


/-- The window has at most `H + 1` elements. -/
private theorem win_card_le (F : ℤ[X]) (N H : ℝ) (hH : 0 ≤ H)
    (hr0 : 0 ≤ N ^ (1 / (F.natDegree : ℝ))) :
    ((win F N H).card : ℝ) ≤ H + 1 := by
  set r : ℝ := N ^ (1 / (F.natDegree : ℝ)) with hr
  set A₁ : ℕ := ⌈r⌉₊ with hA₁
  set B₁ : ℕ := ⌊r + H⌋₊ with hB₁
  have hcard : (win F N H).card = B₁ + 1 - A₁ := by
    rw [win, hA₁, hB₁]; exact Nat.card_Icc _ _
  by_cases h : A₁ ≤ B₁ + 1
  · have hcast : ((B₁ + 1 - A₁ : ℕ) : ℝ) = (B₁ : ℝ) + 1 - (A₁ : ℝ) := by
      rw [Nat.cast_sub h]; push_cast; ring
    rw [hcard, hcast]
    have hrr : (0:ℝ) ≤ r := by rw [hr]; exact hr0
    have hB : (B₁ : ℝ) ≤ r + H := Nat.floor_le (by linarith)
    have hA : r ≤ (A₁ : ℝ) := Nat.le_ceil r
    linarith
  · have hzero : (win F N H).card = 0 := by rw [hcard]; omega
    rw [hzero]; push_cast; linarith

/-- Absorbing a power of a logarithm into a small power of `N`. -/
private theorem log_growth (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∃ N₀ : ℝ, 1 ≤ N₀ ∧ ∀ N : ℝ, N₀ ≤ N → (1 + Real.log N) ^ (3 + A) ≤ N ^ ε := by
  have hcoef : (0:ℝ) < 2 ^ (-(3 + A)) := by positivity
  have hlit := (isLittleO_log_rpow_rpow_atTop (3 + A) hε).def hcoef
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.1 hlit
  refine ⟨max (max 1 (Real.exp 1)) N₁, le_trans (le_max_left _ _) (le_max_left _ _), ?_⟩
  intro N hN
  have hN1 : 1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNexp : Real.exp 1 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN0 : (0:ℝ) < N := lt_of_lt_of_le one_pos hN1
  have hL1 : 1 ≤ Real.log N := by
    have h := Real.log_le_log (Real.exp_pos 1) hNexp
    rwa [Real.log_exp] at h
  have hL0 : (0:ℝ) ≤ Real.log N := by linarith
  have hbound := hN₁ N (le_trans (le_max_right _ _) hN)
  have hnorm1 : ‖Real.log N ^ (3 + A)‖ = Real.log N ^ (3 + A) := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hnorm2 : ‖N ^ ε‖ = N ^ ε := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  rw [hnorm1, hnorm2] at hbound
  have hbase : 1 + Real.log N ≤ 2 * Real.log N := by linarith
  have hnn : (0:ℝ) ≤ 1 + Real.log N := by linarith
  have h2 : (1 + Real.log N) ^ (3 + A) ≤ (2 * Real.log N) ^ (3 + A) :=
    Real.rpow_le_rpow hnn hbase (by positivity)
  have h3 : (2 * Real.log N) ^ (3 + A) = 2 ^ (3 + A) * Real.log N ^ (3 + A) :=
    Real.mul_rpow (by norm_num) hL0
  have h4 : (2:ℝ) ^ (3 + A) * Real.log N ^ (3 + A) ≤
      2 ^ (3 + A) * (2 ^ (-(3 + A)) * N ^ ε) := by
    apply mul_le_mul_of_nonneg_left hbound (by positivity)
  have h5 : (2:ℝ) ^ (3 + A) * (2 ^ (-(3 + A)) * N ^ ε) = N ^ ε := by
    rw [← mul_assoc, ← Real.rpow_add (by norm_num : (0:ℝ) < 2)]
    norm_num
  calc (1 + Real.log N) ^ (3 + A) ≤ (2 * Real.log N) ^ (3 + A) := h2
    _ = 2 ^ (3 + A) * Real.log N ^ (3 + A) := h3
    _ ≤ 2 ^ (3 + A) * (2 ^ (-(3 + A)) * N ^ ε) := h4
    _ = N ^ ε := h5

/-- LEAF. Page 487 equation 29.
Replace F n by its leading term on the shorter polynomial window.
This leaf involves the singular series but no prime representation count. -/
theorem leaf_leading_term (F : ℤ[X]) (hF : Admissible F)
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      |(∑ n ∈ win F N H, (Fv F n : ℝ) * Sing (Fv F n).toNat) -
        (F.leadingCoeff : ℝ) * N * ∑ n ∈ win F N H, Sing (Fv F n).toNat| ≤
        C * H * N * Real.log N ^ (-A) := by

  classical
  have hk1 : 1 ≤ F.natDegree := hF.1
  have hlc : 0 < F.leadingCoeff := hF.2
  have hk0 : F.natDegree ≠ 0 := by omega
  obtain ⟨c, N₁, hc, hN₁, hwin⟩ := window_bound F hF
  obtain ⟨NL, hNL1, hNL⟩ := log_growth A ε hA hε
  set a : ℝ := ((F.leadingCoeff : ℤ) : ℝ) with ha_def
  have ha : 0 < a := by rw [ha_def]; exact_mod_cast hlc
  set cS : ℝ := (|LeanLab.Perelli1996.Section3.singularConstant| + 1) * (8 * 27) with hcS
  have hcS0 : (0:ℝ) ≤ cS := by rw [hcS]; positivity
  refine ⟨2 * c * cS, max (max 3 (Real.exp 1)) (max N₁ (max NL (a + c))), ?_, ?_, ?_⟩
  · have h1 : (0:ℝ) < cS := by rw [hcS]; have := abs_nonneg LeanLab.Perelli1996.Section3.singularConstant; nlinarith
    nlinarith [hc, h1]
  · exact le_trans (le_max_left _ _) (le_max_left _ _)
  intro N H hN hHlo hHhi
  have hN3 : 3 ≤ N := le_trans (le_trans (le_max_left 3 (Real.exp 1)) (le_max_left _ _)) hN
  have hNexp : Real.exp 1 ≤ N :=
    le_trans (le_trans (le_max_right 3 (Real.exp 1)) (le_max_left _ _)) hN
  have hNN1 : N₁ ≤ N :=
    le_trans (le_trans (le_max_left N₁ (max NL (a + c))) (le_max_right (max 3 (Real.exp 1)) _)) hN
  have hNNL : NL ≤ N :=
    le_trans (le_trans (le_trans (le_max_left NL (a + c)) (le_max_right N₁ _))
      (le_max_right (max 3 (Real.exp 1)) _)) hN
  have hNac : a + c ≤ N :=
    le_trans (le_trans (le_trans (le_max_right NL (a + c)) (le_max_right N₁ _))
      (le_max_right (max 3 (Real.exp 1)) _)) hN
  have hN1 : (1:ℝ) ≤ N := by linarith
  have hN0 : (0:ℝ) < N := lt_of_lt_of_le one_pos hN1
  have hL1 : 1 ≤ Real.log N := by
    have h := Real.log_le_log (Real.exp_pos 1) hNexp
    rwa [Real.log_exp] at h
  have hL0 : (0:ℝ) < Real.log N := lt_of_lt_of_le one_pos hL1
  have hac0 : (0:ℝ) < a + c := by linarith
  -- H is at least one
  have hH1 : (1:ℝ) ≤ H := by
    refine le_trans ?_ hHlo
    have h := Real.one_le_rpow hN1 (by positivity : (0:ℝ) ≤ 1 / (6 * (F.natDegree : ℝ)) + ε)
    simpa using h
  have hH0 : (0:ℝ) < H := lt_of_lt_of_le one_pos hH1
  -- H lies below the top of the window
  have hHtop : H ≤ N ^ (1 / (F.natDegree : ℝ)) := by
    refine le_trans hHhi (Real.rpow_le_rpow_of_exponent_le hN1 ?_)
    linarith
  -- the sum rewrites
  have hsum_eq : (∑ n ∈ win F N H, (Fv F n : ℝ) * Sing (Fv F n).toNat) -
      (F.leadingCoeff : ℝ) * N * ∑ n ∈ win F N H, Sing (Fv F n).toNat =
      ∑ n ∈ win F N H, (((Fv F n : ℝ) - a * N) * Sing (Fv F n).toNat) := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro n _
    rw [ha_def]; ring
  rw [hsum_eq]
  -- termwise bound
  have hterm : ∀ n ∈ win F N H,
      |((Fv F n : ℝ) - a * N) * Sing (Fv F n).toNat| ≤
        c * H * N ^ (((F.natDegree : ℝ) - 1) / (F.natDegree : ℝ)) *
          (cS * (1 + Real.log N) ^ 3) := by
    intro n hn
    obtain ⟨hgap, hpos⟩ := hwin N H hNN1 hHtop hH1 n hn
    have hmR : (((Fv F n).toNat : ℕ) : ℝ) = ((Fv F n : ℤ) : ℝ) := by
      have h : (((Fv F n).toNat : ℕ) : ℤ) = Fv F n :=
        Int.toNat_of_nonneg (by exact_mod_cast (show (0:ℝ) ≤ ((Fv F n : ℤ) : ℝ) by linarith))
      calc (((Fv F n).toNat : ℕ) : ℝ) = ((((Fv F n).toNat : ℕ) : ℤ) : ℝ) := by push_cast; ring
        _ = ((Fv F n : ℤ) : ℝ) := by rw [h]
    have hm1 : 1 ≤ (Fv F n).toNat := by
      have h : (1:ℝ) ≤ (((Fv F n).toNat : ℕ) : ℝ) := by rw [hmR]; exact hpos
      exact_mod_cast h
    have hsing := abs_sing_le_cube (Fv F n).toNat hm1
    have hmle : (((Fv F n).toNat : ℕ) : ℝ) ≤ (a + c) * N := by
      have hX0 : (0:ℝ) ≤ N ^ (((F.natDegree : ℝ) - 1) / (F.natDegree : ℝ)) := by positivity
      have hHn : H * N ^ (((F.natDegree : ℝ) - 1) / (F.natDegree : ℝ)) ≤ N := by
        refine le_trans (mul_le_mul_of_nonneg_right hHhi hX0) ?_
        have hexp : 1 / (F.natDegree : ℝ) - ε + ((F.natDegree : ℝ) - 1) / (F.natDegree : ℝ)
            ≤ 1 := by
          field_simp
          nlinarith [hε]
        calc N ^ (1 / (F.natDegree : ℝ) - ε) * N ^ (((F.natDegree : ℝ) - 1) / (F.natDegree : ℝ))
            = N ^ (1 / (F.natDegree : ℝ) - ε + ((F.natDegree : ℝ) - 1) / (F.natDegree : ℝ)) :=
              (Real.rpow_add hN0 _ _).symm
          _ ≤ N ^ (1:ℝ) := Real.rpow_le_rpow_of_exponent_le hN1 hexp
          _ = N := Real.rpow_one N
      rw [hmR]
      have h2 : ((Fv F n : ℤ) : ℝ) - a * N ≤ c * H * N ^ (((F.natDegree : ℝ) - 1) / (F.natDegree : ℝ)) :=
        (le_abs_self _).trans hgap
      nlinarith [hHn]
    have hlogm : Real.log ((((Fv F n).toNat : ℕ) : ℝ)) ≤ 2 * Real.log N := by
      have h1 : Real.log ((((Fv F n).toNat : ℕ) : ℝ)) ≤ Real.log ((a + c) * N) :=
        Real.log_le_log (by exact_mod_cast hm1) hmle
      have h2 : Real.log ((a + c) * N) = Real.log (a + c) + Real.log N :=
        Real.log_mul (ne_of_gt hac0) (ne_of_gt hN0)
      have h3 : Real.log (a + c) ≤ Real.log N := Real.log_le_log hac0 hNac
      rw [h2] at h1
      linarith
    have hcube : (1 + Real.log ((((Fv F n).toNat : ℕ) : ℝ))) ^ 3 ≤ 27 * (1 + Real.log N) ^ 3 := by
      have hbase : 1 + Real.log ((((Fv F n).toNat : ℕ) : ℝ)) ≤ 3 * (1 + Real.log N) := by
        linarith
      have hnn : (0:ℝ) ≤ 1 + Real.log ((((Fv F n).toNat : ℕ) : ℝ)) := by
        have : (0:ℝ) ≤ Real.log ((((Fv F n).toNat : ℕ) : ℝ)) := Real.log_nonneg (by exact_mod_cast hm1)
        linarith
      calc (1 + Real.log ((((Fv F n).toNat : ℕ) : ℝ))) ^ 3
          ≤ (3 * (1 + Real.log N)) ^ 3 := pow_le_pow_left₀ hnn hbase 3
        _ = 27 * (1 + Real.log N) ^ 3 := by norm_num [mul_pow]
    have hsing2 : |Sing (Fv F n).toNat| ≤ cS * (1 + Real.log N) ^ 3 := by
      refine hsing.trans ?_
      have h8 : 8 * (1 + Real.log ((((Fv F n).toNat : ℕ) : ℝ))) ^ 3 ≤
          8 * (27 * (1 + Real.log N) ^ 3) :=
        mul_le_mul_of_nonneg_left hcube (by norm_num)
      have h2 : (|LeanLab.Perelli1996.Section3.singularConstant| + 1) *
            (8 * (1 + Real.log ((((Fv F n).toNat : ℕ) : ℝ))) ^ 3) ≤
          (|LeanLab.Perelli1996.Section3.singularConstant| + 1) * (8 * (27 * (1 + Real.log N) ^ 3)) :=
        mul_le_mul_of_nonneg_left h8 (by positivity)
      refine h2.trans (le_of_eq ?_)
      rw [hcS]; ring
    rw [abs_mul]
    exact mul_le_mul hgap hsing2 (by positivity) (by positivity)
  have hcard : ((win F N H).card : ℝ) ≤ H + 1 :=
    win_card_le F N H hH0.le (by positivity)
  set t : ℝ := N ^ (((F.natDegree : ℝ) - 1) / (F.natDegree : ℝ)) with ht_def
  set L : ℝ := Real.log N with hL_def
  set U : ℝ := (1 + Real.log N) ^ 3 with hU_def
  have ht0 : (0:ℝ) ≤ t := by rw [ht_def]; positivity
  have hU0 : (0:ℝ) ≤ U := by rw [hU_def]; positivity
  have hL0' : (0:ℝ) ≤ L := by rw [hL_def]; linarith
  have hLpos : (0:ℝ) < L := by rw [hL_def]; linarith
  have hLp : (0:ℝ) < L ^ A := Real.rpow_pos_of_pos hLpos A
  have hHt : H * t ≤ N ^ (1 - ε) := by
    have ht' : t = N ^ (((F.natDegree : ℝ) - 1) / (F.natDegree : ℝ)) := ht_def
    rw [ht']
    refine le_trans (mul_le_mul_of_nonneg_right hHhi (by positivity)) ?_
    rw [← Real.rpow_add hN0]
    have hexp : 1 / (F.natDegree : ℝ) - ε + ((F.natDegree : ℝ) - 1) / (F.natDegree : ℝ)
        = 1 - ε := by
      have hkR : (F.natDegree : ℝ) ≠ 0 := by positivity
      field_simp
      ring
    rw [hexp]
  have hlogX : U * L ^ A ≤ N ^ ε := by
    have h1 : L ^ A ≤ (1 + Real.log N) ^ A := by
      rw [hL_def]
      exact Real.rpow_le_rpow hL0.le (by linarith) hA.le
    have h2 : (1 + Real.log N) ^ 3 * L ^ A ≤
        (1 + Real.log N) ^ 3 * (1 + Real.log N) ^ A :=
      mul_le_mul_of_nonneg_left h1 (by positivity)
    have h3 : (1 + Real.log N) ^ 3 * (1 + Real.log N) ^ A =
        (1 + Real.log N) ^ (3 + A) := by
      rw [show (3 + A : ℝ) = (3:ℝ) + A by ring, Real.rpow_add (by linarith)]
      norm_num [Real.rpow_natCast]
    rw [h3] at h2
    have h4 : U = (1 + Real.log N) ^ 3 := hU_def
    rw [h4]
    exact h2.trans (hNL N hNNL)
  have hkey : H * t * U * L ^ A ≤ N := by
    have h1 : H * t * U * L ^ A = (H * t) * (U * L ^ A) := by ring
    rw [h1]
    have h2 := mul_le_mul hHt hlogX (by positivity) (by positivity)
    refine h2.trans ?_
    rw [← Real.rpow_add hN0, show (1 - ε) + ε = 1 by ring, Real.rpow_one]
  have hsum_bound : |∑ n ∈ win F N H, ((Fv F n : ℝ) - a * N) * Sing (Fv F n).toNat| ≤
      (win F N H).card * (c * H * t * (cS * U)) := by
    calc |∑ n ∈ win F N H, ((Fv F n : ℝ) - a * N) * Sing (Fv F n).toNat|
        ≤ ∑ n ∈ win F N H, |((Fv F n : ℝ) - a * N) * Sing (Fv F n).toNat| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ n ∈ win F N H, (c * H * t * (cS * U)) := Finset.sum_le_sum hterm
      _ = (win F N H).card * (c * H * t * (cS * U)) := by
          rw [Finset.sum_const, nsmul_eq_mul]
  have hmain : (win F N H).card * (c * H * t * (cS * U)) ≤ 2 * c * cS * H * N * L ^ (-A) := by
    have hrhs : 2 * c * cS * H * N * L ^ (-A) = 2 * c * cS * H * N / L ^ A := by
      rw [Real.rpow_neg hL0', div_eq_mul_inv]
    rw [hrhs, le_div_iff₀ hLp]
    have hcard2 : ((win F N H).card : ℝ) ≤ 2 * H := by linarith
    have e1 : ((win F N H).card : ℝ) * (c * H * t * (cS * U)) * L ^ A ≤
        ((2*H) * (c * H * t * (cS * U))) * L ^ A := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right hcard2 (by positivity)
    refine e1.trans ?_
    have e2 : ((2*H) * (c * H * t * (cS * U))) * L ^ A =
        2 * c * cS * H * (H * t * U * L ^ A) := by ring
    rw [e2]
    exact mul_le_mul_of_nonneg_left hkey (by positivity)
  exact hsum_bound.trans hmain

/-- LEAF. Page 487 equations 31 and 32.
Character orthogonality followed by the zero free region and zero density
estimate gives Sigma P at most N times L to the power minus two A minus one.
The cutoff c is fixed before N tends to infinity. -/
theorem leaf_remainder_mean (F : ℤ[X]) (hF : Admissible F)
    (c B A ε : ℝ) (hc : 0 < c) (hB : 0 < B) (hA : 0 < A) (hε : 0 < ε) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      remainderMass F c N H B ≤ C * N * Real.log N ^ (-2 * A - 1) := by
  -- ATTEMPT 1 of 3: use the published character remainder input of this paper,
  -- which is Decomp88.leaf_character of pages 484 and 485 equations 18 to 25.
  -- The Lean error of our own attempt was
  --   Application type mismatch: The argument hH has type
  --     N ^ (1 / (6 * ↑F.natDegree) + ε) ≤ H
  --   but is expected to have type
  --     N ^ (1 / (3 * ↑F.natDegree) + ε / 2) ≤ H
  --   in the application hrem N H hNN' hH
  -- The same input also uses the radius 1 / (q * fareyOrder F N H B) and an
  -- interval integral, while this leaf uses the radius 1 / (q * meanOrder F N H B)
  -- and a set integral over Set.Icc, so it cannot be applied term by term.
  -- ATTEMPT 2 of 3: bound the character remainder pointwise. From
  -- ArithmeticFunction.vonMangoldt_le_log and Kernel.norm_T_le one gets
  --   norm (characterRemainder M q a η) ≤ (M + 1) log (M + 1) + (M + 1)
  -- and summing the arc lengths gives a mass of order
  --   N ^ 2 (log N) ^ 2 (log N) ^ (2 B) / H ^ k
  -- which is larger than the target N log ^ (-2 A - 1) N by a factor of N.
  -- ATTEMPT 3 of 3: use Parseval over a full period. The period mass is
  -- sum over n ≤ M of (Λ n - 1) ^ 2, and Mathlib has no lower bound of the
  -- needed size for it, while the arc interval is much shorter than the period.
  -- BLOCKED: OUT OF REACH. Missing result: a uniform bound of
  --   (integral over |η| ≤ 1 / (q * meanOrder F N H B)) of
  --     norm (characterRemainder ⌊c * N⌋₊ q a η) ^ 2
  --   by C N log ^ (-B) N for every q ≤ log N ^ B and every a coprime to q,
  -- which is the input of Perelli 1996 pages 484 and 485 equations 18 to 25.
  -- That input is Decomp88.leaf_character and it is open in this repository.
  sorry

/-- The exact existing prime mean target from the three smaller leaves.
CONDITIONAL ON weighted mean, leading term and character remainder leaves. -/
theorem leaf_prime_mean_estimate (F : ℤ[X]) (hF : Admissible F) :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C N₀ : ℝ,
      ∀ N H : ℝ, N₀ ≤ N → N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
        H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
        |(∑ n ∈ win F N H, R (Fv F n).toNat) -
          (F.leadingCoeff : ℝ) * N * ∑ n ∈ win F N H, Sing (Fv F n).toNat| ≤
            C * H * N * Real.log N ^ (-A) := by
  intro A ε hA hε
  obtain ⟨B, c, CW, NW, hB, hc, hCW, hNW, hw⟩ := leaf_weighted_mean F hF A ε hA hε
  obtain ⟨CT, NT, hCT, hNT, ht⟩ := leaf_leading_term F hF A ε hA hε
  obtain ⟨CR, NR, hCR, hNR, hr⟩ := leaf_remainder_mean F hF c B A ε hc hB hA hε
  refine ⟨CW * (CR + Real.sqrt CR + 1) + CT,
    max (Real.exp 1 + 3) (max NW (max NT NR)), ?_⟩
  intro N H hN hH hHu
  have hNexp : Real.exp 1 + 3 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by have := Real.exp_pos 1; linarith
  have hL : 1 ≤ Real.log N := by
    have := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ N by linarith)
    simpa using this
  have hL0 : 0 < Real.log N := by linarith
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH
  have hNW' := (le_max_left NW (max NT NR)).trans ((le_max_right _ _).trans hN)
  have hNT' := (le_max_left NT NR).trans ((le_max_right NW _).trans ((le_max_right _ _).trans hN))
  have hNR' := (le_max_right NT NR).trans ((le_max_right NW _).trans ((le_max_right _ _).trans hN))
  have hr' := hr N H hNR' hH hHu
  have hpow := Real.rpow_le_rpow_of_exponent_le hL (show -2 * A - 1 ≤ -A by linarith)
  have hsmall : remainderMass F c N H B ≤ CR * N * Real.log N ^ (-A) :=
    hr'.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  have hsq : Real.sqrt (N * Real.log N * remainderMass F c N H B) ≤
      Real.sqrt CR * N * Real.log N ^ (-A) := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    calc N * Real.log N * remainderMass F c N H B
        ≤ N * Real.log N * (CR * N * Real.log N ^ (-2 * A - 1)) :=
          mul_le_mul_of_nonneg_left hr' (by positivity)
      _ = (Real.sqrt CR * N * Real.log N ^ (-A)) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hCR.le,
          ← Real.rpow_mul_natCast hL0.le]
        have he : Real.log N * Real.log N ^ (-2 * A - 1) = Real.log N ^ (-A * 2) := by
          calc
            _ = Real.log N ^ (1 : ℝ) * Real.log N ^ (-2 * A - 1) := by rw [Real.rpow_one]
            _ = Real.log N ^ (1 + (-2 * A - 1)) := (Real.rpow_add hL0 _ _).symm
            _ = _ := by congr 1; ring
        calc _ = CR * N ^ 2 * (Real.log N * Real.log N ^ (-2 * A - 1)) := by ring
          _ = _ := by rw [he]; norm_num
  calc _ ≤ |(∑ n ∈ win F N H, R (Fv F n).toNat) -
          ∑ n ∈ win F N H, (Fv F n : ℝ) * Sing (Fv F n).toNat| +
        |(∑ n ∈ win F N H, (Fv F n : ℝ) * Sing (Fv F n).toNat) -
          (F.leadingCoeff : ℝ) * N * ∑ n ∈ win F N H, Sing (Fv F n).toNat| :=
          abs_sub_le _ _ _
    _ ≤ (CW * H * (remainderMass F c N H B +
          Real.sqrt (N * Real.log N * remainderMass F c N H B)) +
          CW * H * N * Real.log N ^ (-A)) + CT * H * N * Real.log N ^ (-A) :=
          add_le_add (hw N H hNW' hH hHu) (ht N H hNT' hH hHu)
    _ ≤ (CW * H * (CR * N * Real.log N ^ (-A) +
          Real.sqrt CR * N * Real.log N ^ (-A)) +
          CW * H * N * Real.log N ^ (-A)) + CT * H * N * Real.log N ^ (-A) := by
          gcongr
    _ = _ := by ring

end
end LeanLab.Perelli1996.Decomp289a
