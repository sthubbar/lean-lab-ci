/-
P0083, pages 488 and 489, equations 33 through 37.
The singular average is an elementary input to the analytic Theorem 2.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.SingularDivisor88
import LeanLab.Perelli1996.WeightedCounting
import LeanLab.Perelli1996.WeightedEuler
import LeanLab.Perelli1996.Tails88
import LeanLab.Perelli1996.Decomp88

namespace LeanLab.Perelli1996.Section3
open Finset Real Polynomial
noncomputable section

/-- The prime two factor makes the singular series vanish on odd integers, page 477. -/
theorem sing_odd_zero (n : ℕ) (hn : Odd n) : Sing n = 0 := by
  have hnd : ¬ 2 ∣ n := by
    intro hd
    exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr hd)
  unfold Sing
  apply tprod_of_exists_eq_zero
  refine ⟨⟨2, Nat.prime_two⟩, ?_⟩
  rw [if_neg hnd]
  norm_num

/-- Equation 33 for a single positive value, with the odd divisor support of f explicit. -/
theorem sing_divisor_indicator (n D : ℕ) (hn : 0 < n) (hnD : n ≤ D) :
    Sing n = singularConstant * ∑ d ∈ Icc 1 D,
      if 2 * d ∣ n then arithmeticFactor d else 0 := by
  classical
  by_cases he : Even n
  · rw [sing_even_divisor_sum n hn.ne' he]
    congr 1
    have hset : n.divisors = (Icc 1 D).filter (fun d => d ∣ n) := by
      ext d
      simp only [Nat.mem_divisors, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hd, _⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn, (Nat.le_of_dvd hn hd).trans hnD⟩, hd⟩
      · rintro ⟨_, hd⟩
        exact ⟨hd, hn.ne'⟩
    rw [hset, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro d hd
    by_cases h2 : 2 ∣ d
    · simp [arithmeticFactor_even h2]
    · have hcop : Nat.Coprime 2 d := Nat.prime_two.coprime_iff_not_dvd.mpr h2
      have hiff : 2 * d ∣ n ↔ d ∣ n := by
        constructor
        · exact fun h => dvd_trans (dvd_mul_left d 2) h
        · exact fun h => hcop.mul_dvd_of_dvd_of_dvd he.two_dvd h
      simp only [hiff]
  · have hodd : Odd n := Nat.not_even_iff_odd.mp he
    rw [sing_odd_zero n hodd]
    have hz : ∑ d ∈ Icc 1 D, (if 2 * d ∣ n then arithmeticFactor d else 0) = 0 := by
      apply Finset.sum_eq_zero
      intro d hd
      rw [if_neg (by intro h; exact he (even_iff_two_dvd.mpr (dvd_trans (dvd_mul_right 2 d) h)))]
    rw [hz, mul_zero]

/-- Equation 33 as an exact finite weighted root count. -/
theorem finite_singular_count (F : ℤ[X]) (D : ℕ) (N H : ℝ)
    (hvalues : ∀ n ∈ win F N H, 0 < Fv F n ∧ (Fv F n).toNat ≤ D) :
    (∑ n ∈ win F N H, Sing (Fv F n).toNat) =
      singularConstant * ∑ d ∈ Icc 1 D, arithmeticFactor d *
        ((Counting.rootWindow F (2 * d) (N ^ (1 / (F.natDegree : ℝ))) H).card : ℝ) := by
  classical
  have hterm (n : ℕ) (hn : n ∈ win F N H) :
      Sing (Fv F n).toNat = singularConstant * ∑ d ∈ Icc 1 D,
        if (2 * d : ℤ) ∣ Fv F n then arithmeticFactor d else 0 := by
    have hv := hvalues n hn
    have hn0 : 0 < (Fv F n).toNat := by have := hv.1; omega
    rw [sing_divisor_indicator _ D hn0 hv.2]
    congr 1
    apply Finset.sum_congr rfl
    intro d hd
    have hcast : ((Fv F n).toNat : ℤ) = Fv F n := Int.toNat_of_nonneg hv.1.le
    have hiff : 2 * d ∣ (Fv F n).toNat ↔ (2 * d : ℤ) ∣ Fv F n := by
      rw [← hcast]
      exact_mod_cast (Int.natCast_dvd_natCast : ((2 * d : ℕ) : ℤ) ∣ ((Fv F n).toNat : ℤ) ↔ _).symm
    simp only [hiff]
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_comm]
  congr 1
  apply Finset.sum_congr rfl
  intro d hd
  change (∑ n ∈ win F N H, if (2 * d : ℤ) ∣ Fv F n then arithmeticFactor d else 0) =
    arithmeticFactor d * (((win F N H).filter (fun n => (2 * d : ℤ) ∣ Fv F n)).card : ℝ)
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_comm]

/-- Equation 37 with both finite cutoff errors explicit before choosing D proportional to N. -/
theorem singular_count_error (F : ℤ[X]) (hF : Admissible F) {ε : ℝ}
    (hε : 0 < ε) (hε1 : ε < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, 1 ≤ D → ∀ N H : ℝ, 0 ≤ N → 0 ≤ H →
      (∀ n ∈ win F N H, 0 < Fv F n ∧ (Fv F n).toNat ≤ D) →
      |(∑ n ∈ win F N H, Sing (Fv F n).toNat) -
        ((Roots.rootResidues F 2).card : ℝ) / 2 * H * singularConstant *
        ∏' p : {p : ℕ // p.Prime ∧ 2 < p},
          (1 + ((Roots.rootResidues F p.1).card : ℝ) / ((p.1 : ℝ) * ((p.1 : ℝ) - 2)))| ≤
        C * ((D : ℝ) ^ ε + H * (D : ℝ) ^ (-1 + ε)) := by
  classical
  obtain ⟨CP, hCP, hpartial⟩ := weighted_roots_partial_bound F hF hε
  obtain ⟨CT, hCT, htail⟩ := weighted_roots_tail_bound F hF hε hε1
  let ρ : ℝ := (Roots.rootResidues F 2).card
  let S := singularConstant
  let C := 1 + |S| * (2 * ρ * CP + ρ / 2 * CT)
  have hρ : 0 ≤ ρ := Nat.cast_nonneg _
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨C, hC, fun D hD N H hN hH hvalues => ?_⟩
  let g (d : ℕ) : ℝ := arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ) / d
  let tail := ∑' d : {d : ℕ // D < d}, g d.1
  have hg0 (d : ℕ) : 0 ≤ g d := by
    dsimp [g]
    exact div_nonneg (mul_nonneg (arithmeticFactor_nonneg d) (Nat.cast_nonneg _)) (Nat.cast_nonneg _)
  have ht0 : 0 ≤ tail := tsum_nonneg (fun d => hg0 d.1)
  have hs : Summable g := summable_weighted_roots F hF
  have hprefix : (∑ d ∈ range (D + 1), g d) = ∑ d ∈ Icc 1 D, g d := by
    have hset : range (D + 1) = insert 0 (Icc 1 D) := by
      ext d
      simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
      omega
    rw [hset, Finset.sum_insert (by simp)]
    simp [g]
  have htail_eq : (∑' d : {d : ℕ // d ∉ range (D + 1)}, g d.1) = tail := by
    let e : {d : ℕ // d ∉ range (D + 1)} ≃ {d : ℕ // D < d} :=
      Equiv.subtypeEquivRight (fun d => by simp only [Finset.mem_range]; omega)
    exact e.tsum_eq (fun d => g d.1)
  have hseries := hs.sum_add_tsum_subtype_compl (range (D + 1))
  rw [hprefix, htail_eq] at hseries
  have hdiff : |(∑ d ∈ Icc 1 D, g d) - ∑' d, g d| = tail := by
    have heq : (∑ d ∈ Icc 1 D, g d) - ∑' d, g d = -tail := by linarith
    rw [heq, abs_neg, abs_of_nonneg ht0]
  let W := ∑ d ∈ Icc 1 D, arithmeticFactor d *
    ((Counting.rootWindow F (2 * d) (N ^ (1 / (F.natDegree : ℝ))) H).card : ℝ)
  have hcount := finite_weighted_count_error F D (Real.rpow_nonneg hN (1 / (F.natDegree : ℝ))) hH
  change |W - ρ * H / 2 * (∑ d ∈ Icc 1 D, g d)| ≤
    2 * ρ * ∑ d ∈ Icc 1 D, arithmeticFactor d * ((Roots.rootResidues F d).card : ℝ) at hcount
  have hfirst : |W - ρ * H / 2 * (∑' d, g d)| ≤
      2 * ρ * (CP * (D : ℝ) ^ ε) + ρ * H / 2 * (CT * (D : ℝ) ^ (-1 + ε)) := by
    calc |W - ρ * H / 2 * (∑' d, g d)| =
        |(W - ρ * H / 2 * (∑ d ∈ Icc 1 D, g d)) +
          ρ * H / 2 * ((∑ d ∈ Icc 1 D, g d) - ∑' d, g d)| := by congr 1; ring
      _ ≤ |W - ρ * H / 2 * (∑ d ∈ Icc 1 D, g d)| +
          |ρ * H / 2 * ((∑ d ∈ Icc 1 D, g d) - ∑' d, g d)| := abs_add_le _ _
      _ = |W - ρ * H / 2 * (∑ d ∈ Icc 1 D, g d)| + ρ * H / 2 * tail := by
        rw [abs_mul, abs_of_nonneg (by positivity : 0 ≤ ρ * H / 2), hdiff]
      _ ≤ 2 * ρ * (CP * (D : ℝ) ^ ε) + ρ * H / 2 * (CT * (D : ℝ) ^ (-1 + ε)) := by
        exact add_le_add (hcount.trans (mul_le_mul_of_nonneg_left (hpartial D hD) (by positivity)))
          (mul_le_mul_of_nonneg_left (htail D hD) (by positivity))
  have heuler := weighted_roots_eulerProduct_odd F hF
  change (∑' d, g d) = _ at heuler
  have hexact := finite_singular_count F D N H hvalues
  have hcoef1 : |S| * (2 * ρ * CP) ≤ C := by
    dsimp [C]
    have hh : 0 ≤ |S| * (ρ / 2 * CT) := by positivity
    nlinarith
  have hcoef2 : |S| * (ρ / 2 * CT) ≤ C := by
    dsimp [C]
    have hh : 0 ≤ |S| * (2 * ρ * CP) := by positivity
    nlinarith
  calc |(∑ n ∈ win F N H, Sing (Fv F n).toNat) -
        ((Roots.rootResidues F 2).card : ℝ) / 2 * H * singularConstant *
          ∏' p : {p : ℕ // p.Prime ∧ 2 < p},
            (1 + ((Roots.rootResidues F p.1).card : ℝ) / ((p.1 : ℝ) * ((p.1 : ℝ) - 2)))|
      = |S| * |W - ρ * H / 2 * (∑' d, g d)| := by
        rw [hexact, ← heuler, ← abs_mul]
        congr 1
        dsimp [S, W, ρ]
        ring
    _ ≤ |S| * (2 * ρ * (CP * (D : ℝ) ^ ε) + ρ * H / 2 * (CT * (D : ℝ) ^ (-1 + ε))) :=
      mul_le_mul_of_nonneg_left hfirst (abs_nonneg S)
    _ = (|S| * (2 * ρ * CP)) * (D : ℝ) ^ ε +
        (|S| * (ρ / 2 * CT)) * (H * (D : ℝ) ^ (-1 + ε)) := by ring
    _ ≤ C * (D : ℝ) ^ ε + C * (H * (D : ℝ) ^ (-1 + ε)) := by gcongr
    _ = _ := by ring

/-- The elementary singular average input, page 489 equation 37, with no cited assumptions. -/
theorem singularAverage (F : ℤ[X]) : SingularAverage F := by
  intro hF ε hε
  let δ : ℝ := min ε (1 / 2)
  have hδ : 0 < δ := lt_min hε (by norm_num)
  have hδε : δ ≤ ε := min_le_left _ _
  have hδ1 : δ < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  obtain ⟨C, hC, herror⟩ := singular_count_error F hF hδ hδ1
  obtain ⟨c, Nc, hc, hNc, hcut⟩ := Decomp88.leaf_cutoff F hF
  obtain ⟨X₀, hX₀, hlower⟩ := B.poly_lower F hF
  let c' := max c 1
  have hc' : 1 ≤ c' := le_max_right _ _
  have hcc' : c ≤ c' := le_max_left _ _
  have hk : (0 : ℝ) < F.natDegree := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hF.1)
  have hk0 : F.natDegree ≠ 0 := by have := hF.1; omega
  refine ⟨C * ((c' + 1) ^ δ + 1), max Nc (max 3 (X₀ ^ F.natDegree)), ?_⟩
  intro N H hN hH hHu
  have hNcN : Nc ≤ N := (le_max_left _ _).trans hN
  have hN3 : 3 ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans hN)
  have hNX : X₀ ^ F.natDegree ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans hN)
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hHN : H ≤ N := by
    refine hHu.trans ?_
    calc
      N ^ (1 / (F.natDegree : ℝ)) ≤ N ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le hN1
        apply (div_le_iff₀ hk).mpr
        have hh : (1 : ℝ) ≤ F.natDegree := by exact_mod_cast hF.1
        linarith
      _ = N := Real.rpow_one N
  let D : ℕ := ⌈c' * N⌉₊
  have hND : N ≤ (D : ℝ) := by
    calc N ≤ c' * N := by nlinarith
      _ ≤ (D : ℝ) := Nat.le_ceil _
  have hD : 1 ≤ D := by have : (1 : ℝ) ≤ D := hN1.trans hND; exact_mod_cast this
  have hDupper : (D : ℝ) ≤ (c' + 1) * N := by
    have hh : (D : ℝ) < c' * N + 1 := Nat.ceil_lt_add_one (by positivity)
    linarith
  have hvalues : ∀ n ∈ win F N H, 0 < Fv F n ∧ (Fv F n).toNat ≤ D := by
    intro n hn
    have hnlo : N ^ (1 / (F.natDegree : ℝ)) ≤ (n : ℝ) :=
      (Nat.le_ceil _).trans (by exact_mod_cast (Finset.mem_Icc.mp hn).1)
    have hnk : N ≤ (n : ℝ) ^ F.natDegree := by
      have hh := pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) hnlo F.natDegree
      rwa [B.rpow_k N hN0.le F.natDegree hk0] at hh
    have hXn : X₀ ≤ (n : ℝ) :=
      (pow_le_pow_iff_left₀ hX₀ (Nat.cast_nonneg n) hk0).mp (hNX.trans hnk)
    have hl := hlower n hXn
    change (n : ℝ) ^ F.natDegree / 2 ≤ (Fv F n : ℝ) at hl
    have hpos : (0 : ℝ) < Fv F n := by linarith
    refine ⟨by exact_mod_cast hpos, ?_⟩
    have hv := (hcut N H hNcN hH hHu n hn).2
    have hf := Nat.floor_le (show 0 ≤ c * N by positivity)
    have hvcast : ((Fv F n).toNat : ℝ) ≤ (⌊c * N⌋₊ : ℝ) := by exact_mod_cast hv
    have hvR : ((Fv F n).toNat : ℝ) ≤ c * N := hvcast.trans hf
    have hDcast : ((Fv F n).toNat : ℝ) ≤ D :=
      hvR.trans ((mul_le_mul_of_nonneg_right hcc' hN0.le).trans (Nat.le_ceil _))
    exact_mod_cast hDcast
  have herrorN := herror D hD N H hN0.le hH hvalues
  have hNpow : N ^ δ ≤ N ^ ε := Real.rpow_le_rpow_of_exponent_le hN1 hδε
  have hpartial : (D : ℝ) ^ δ ≤ (c' + 1) ^ δ * N ^ ε := by
    calc (D : ℝ) ^ δ ≤ ((c' + 1) * N) ^ δ :=
        Real.rpow_le_rpow (Nat.cast_nonneg D) hDupper hδ.le
      _ = (c' + 1) ^ δ * N ^ δ := Real.mul_rpow (by positivity) hN0.le
      _ ≤ (c' + 1) ^ δ * N ^ ε := by gcongr
  have htail : H * (D : ℝ) ^ (-1 + δ) ≤ N ^ ε := by
    have hdPow : (D : ℝ) ^ (-1 + δ) ≤ N ^ (-1 + δ) :=
      Real.rpow_le_rpow_of_nonpos hN0 hND (by linarith)
    calc H * (D : ℝ) ^ (-1 + δ) ≤ N * N ^ (-1 + δ) := by gcongr
      _ = N ^ δ := by
        calc
          N * N ^ (-1 + δ) = N ^ (1 + (-1 + δ)) := by
            rw [Real.rpow_add hN0 1 (-1 + δ), Real.rpow_one]
          _ = N ^ δ := by congr 1; ring
      _ ≤ N ^ ε := hNpow
  calc _ ≤ C * ((D : ℝ) ^ δ + H * (D : ℝ) ^ (-1 + δ)) := herrorN
    _ ≤ C * ((c' + 1) ^ δ * N ^ ε + N ^ ε) := by gcongr
    _ = C * ((c' + 1) ^ δ + 1) * N ^ ε := by ring

end
end LeanLab.Perelli1996.Section3
