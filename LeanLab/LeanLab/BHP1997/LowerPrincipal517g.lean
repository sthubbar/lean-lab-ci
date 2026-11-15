/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character.
Assembly of the E2 and E4 density statements `leaf_two_rough_density` and
`leaf_four_rough_density` of `LowerPrincipal517a.lean` from the three leaves of
`LowerPrincipal517f.lean`: the rough cofactor is replaced by its Buchstab density with
`leaf_rough_interval_density`, summed over the outer primes, and the remaining sum over the
outer primes is `leaf_two_density_main` or `leaf_four_density_main`.

No new definition and no sorry in this file. The two theorems are CONDITIONAL ON the three
leaves of `LowerPrincipal517f.lean`. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.LowerPrincipal517f

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators

/-- P0069 page 51 display 5.17. Real valued form of the reindexing of one subtracted sum of
display 5.15 by the cofactor: the multiples `m = d * n` of an outer product `d ≥ 1` in `(L, U]`
correspond to the cofactors `n` in `(L / d, U / d]`. -/
theorem real_sum_dvd_reindex {d : ℕ} (hd : 1 ≤ d) (L U : ℕ) (g : ℕ → ℝ) :
    ∑ m ∈ Finset.Ioc L U, (if d ∣ m then g m else 0) =
      ∑ n ∈ Finset.Ioc (L / d) (U / d), g (d * n) := by
  have hd0 : 0 < d := hd
  have hinj : ∀ x ∈ Finset.Ioc (L / d) (U / d), ∀ y ∈ Finset.Ioc (L / d) (U / d),
      d * x = d * y → x = y := fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hd0 h
  have h1 : ∑ n ∈ Finset.Ioc (L / d) (U / d), g (d * n) =
      ∑ m ∈ (Finset.Ioc (L / d) (U / d)).image (fun n => d * n),
        (if d ∣ m then g m else 0) := by
    rw [Finset.sum_image hinj]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp
  rw [h1]
  symm
  refine Finset.sum_subset ?_ ?_
  · intro m hm
    rcases Finset.mem_image.mp hm with ⟨n, hn, rfl⟩
    rw [Finset.mem_Ioc] at hn ⊢
    exact ⟨(Nat.div_lt_iff_lt_mul hd0).mp hn.1 |>.trans_eq (Nat.mul_comm n d),
      (Nat.mul_comm d n).trans_le ((Nat.le_div_iff_mul_le hd0).mp hn.2)⟩
  · intro m hm hnot
    by_cases hdm : d ∣ m
    · exfalso
      apply hnot
      rcases hdm with ⟨n, rfl⟩
      rw [Finset.mem_Ioc] at hm
      refine Finset.mem_image.mpr ⟨n, ?_, rfl⟩
      rw [Finset.mem_Ioc]
      exact ⟨(Nat.div_lt_iff_lt_mul hd0).mpr (hm.1.trans_eq (Nat.mul_comm d n)),
        (Nat.le_div_iff_mul_le hd0).mpr ((Nat.mul_comm n d).trans_le hm.2)⟩
    · simp [hdm]

/-- P0069 page 51 display 5.17. Summation of the rough variable density estimate over the
outer prime factors of a subtracted sum of display 5.15, with no character. Each index `i`
carries an outer product `d i ≤ L` and a roughness level `z i ≥ X ^ c`; the inner sum over the
cofactor `m / d i` is bounded by the interval density estimate `hmain`, which is the conclusion
of `leaf_rough_interval_density` at the scale `X`. -/
theorem rough_family_density_sum (ω : ℝ → ℝ) {c C A X : ℝ} (hC : 0 < C) (hX1 : 1 ≤ X)
    (hmain : ∀ z : ℕ, X ^ c ≤ (z : ℝ) → ∀ a b : ℕ, 1 ≤ a → (b : ℝ) ≤ X →
      |∑ n ∈ Finset.Ioc a b, (Task308.roughIndicator n z -
          ω (Real.log n / Real.log z) / Real.log z)| ≤ C * b * Real.log X ^ (-A))
    {ι : Type} (I : Finset ι) (d z : ι → ℕ) (L U : ℕ) (M : ℝ)
    (hI : ∀ i ∈ I, 1 ≤ d i ∧ d i ≤ L ∧ X ^ c ≤ (z i : ℝ)) (hU : (U : ℝ) ≤ X)
    (hM : ∑ i ∈ I, (1 : ℝ) / (d i : ℝ) ≤ M) :
    |∑ m ∈ Finset.Ioc L U, ∑ i ∈ I, (if d i ∣ m then
        Task308.roughIndicator (m / d i) (z i) -
          ω (Real.log ((m / d i : ℕ) : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ)
        else 0)| ≤ C * M * U * Real.log X ^ (-A) := by
  have hlog : 0 ≤ Real.log X ^ (-A) := Real.rpow_nonneg (Real.log_nonneg hX1) _
  have hUnn : (0 : ℝ) ≤ (U : ℝ) := Nat.cast_nonneg U
  rw [Finset.sum_comm]
  have hterm : ∀ i ∈ I, |∑ m ∈ Finset.Ioc L U, (if d i ∣ m then
        Task308.roughIndicator (m / d i) (z i) -
          ω (Real.log ((m / d i : ℕ) : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ)
        else 0)| ≤ C * U * Real.log X ^ (-A) * ((1 : ℝ) / (d i : ℝ)) := by
    intro i hi
    obtain ⟨hd1, hdL, hz⟩ := hI i hi
    have hd0 : 0 < d i := hd1
    have hdR : (0 : ℝ) < (d i : ℝ) := Nat.cast_pos.mpr hd0
    rw [real_sum_dvd_reindex hd1 L U
      (fun m => Task308.roughIndicator (m / d i) (z i) -
          ω (Real.log ((m / d i : ℕ) : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ))]
    have hre : ∑ n ∈ Finset.Ioc (L / d i) (U / d i),
        (Task308.roughIndicator (d i * n / d i) (z i) -
          ω (Real.log ((d i * n / d i : ℕ) : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ)) =
        ∑ n ∈ Finset.Ioc (L / d i) (U / d i),
          (Task308.roughIndicator n (z i) -
            ω (Real.log (n : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ)) := by
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Nat.mul_div_cancel_left n hd0]
    rw [hre]
    have hcast : ((U / d i : ℕ) : ℝ) ≤ (U : ℝ) / (d i : ℝ) := Nat.cast_div_le
    have hUd : (U : ℝ) / (d i : ℝ) ≤ U :=
      div_le_self hUnn (by exact_mod_cast hd1)
    have hb := hmain (z i) hz (L / d i) (U / d i)
      (Nat.div_pos hdL hd0) (hcast.trans (hUd.trans hU))
    calc |∑ n ∈ Finset.Ioc (L / d i) (U / d i),
          (Task308.roughIndicator n (z i) -
            ω (Real.log (n : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ))|
        ≤ C * ((U / d i : ℕ) : ℝ) * Real.log X ^ (-A) := hb
      _ ≤ C * ((U : ℝ) / (d i : ℝ)) * Real.log X ^ (-A) :=
          mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hcast hC.le) hlog
      _ = C * U * Real.log X ^ (-A) * ((1 : ℝ) / (d i : ℝ)) := by ring
  have hK : 0 ≤ C * U * Real.log X ^ (-A) := mul_nonneg (mul_nonneg hC.le hUnn) hlog
  calc |∑ i ∈ I, ∑ m ∈ Finset.Ioc L U, (if d i ∣ m then
        Task308.roughIndicator (m / d i) (z i) -
          ω (Real.log ((m / d i : ℕ) : ℝ) / Real.log (z i : ℝ)) / Real.log (z i : ℝ)
        else 0)|
      ≤ ∑ i ∈ I, C * U * Real.log X ^ (-A) * ((1 : ℝ) / (d i : ℝ)) :=
        (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum hterm)
    _ = C * U * Real.log X ^ (-A) * ∑ i ∈ I, (1 : ℝ) / (d i : ℝ) := by rw [Finset.mul_sum]
    _ ≤ C * U * Real.log X ^ (-A) * M := mul_le_mul_of_nonneg_left hM hK
    _ = C * M * U * Real.log X ^ (-A) := by ring

/-- P0069 page 51 display 5.17. The add and subtract step for one subtracted sum of display
5.15: a coefficient `T m` that is a family sum of rough indicators `r i m` over the outer
primes, minus its density `D m`, is the family sum of the differences `r i m - w i m` plus the
family sum of the local densities `w i m` minus `D m`. -/
theorem family_density_split {ι : Type} (I : Finset ι) (S : Finset ℕ) (T D : ℕ → ℝ)
    (r w : ι → ℕ → ℝ) (P : ι → ℕ → Prop) [∀ i m, Decidable (P i m)]
    (hT : ∀ m ∈ S, T m = ∑ i ∈ I, if P i m then r i m else 0) :
    ∑ m ∈ S, (T m - D m) =
      ∑ m ∈ S, ∑ i ∈ I, (if P i m then r i m - w i m else 0) +
        ∑ m ∈ S, ((∑ i ∈ I, if P i m then w i m else 0) - D m) := by
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m hm => ?_
  rw [hT m hm]
  have h : ∑ i ∈ I, (if P i m then r i m - w i m else 0) =
      (∑ i ∈ I, if P i m then r i m else 0) - ∑ i ∈ I, if P i m then w i m else 0 := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    split_ifs <;> simp
  rw [h]
  ring

/-- P0069 page 51, display 5.17, the E2 term, assembled from the leaves of
`LowerPrincipal517f.lean`. The statement is exactly that of `leaf_two_rough_density`. The sum
over `p1 p2 n3 = m` with exponents in E2 is written as a family sum over prime pairs; the rough
cofactor `n3` is replaced by its Buchstab density with `leaf_rough_interval_density` at the
scale `2 Y`, summed over the pairs with `Decomp514a.pair_reciprocal_sum_le`; the remaining sum
over the pairs is `leaf_two_density_main`. -/
theorem two_rough_density_of_leaves (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
      |∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (lowerTwoTerms ε x m -
          lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C0, hC0, hbb⟩ := leaf_rough_interval_density ω hω hz (c := 1 / 10) (by norm_num)
    (A + 2) (by linarith)
  obtain ⟨C1, hmainleaf⟩ := leaf_two_density_main ω hω hz hε hε8 A hA
  refine ⟨max (8 * C0 * (2 : ℝ) ^ A + C1)
    (max ((2 : ℝ) ^ 36) (max (Real.exp ((2 : ℝ) ^ (A + 1))) (max (C0 ^ 2) C1))), ?_⟩
  generalize hCdef : max (8 * C0 * (2 : ℝ) ^ A + C1)
    (max ((2 : ℝ) ^ 36) (max (Real.exp ((2 : ℝ) ^ (A + 1))) (max (C0 ^ 2) C1))) = C
  have hC1 : 8 * C0 * (2 : ℝ) ^ A + C1 ≤ C := by rw [← hCdef]; exact le_max_left _ _
  have hC2 : (2 : ℝ) ^ 36 ≤ C := by
    rw [← hCdef]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hC3 : Real.exp ((2 : ℝ) ^ (A + 1)) ≤ C := by
    rw [← hCdef]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hC4 : C0 ^ 2 ≤ C := by
    rw [← hCdef]
    exact (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hC5 : C1 ≤ C := by
    rw [← hCdef]
    exact (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  intro x hx t ht
  have hx36 : (2 : ℝ) ^ 36 ≤ x := hC2.trans hx
  have hxe : Real.exp ((2 : ℝ) ^ (A + 1)) ≤ x := hC3.trans hx
  have hxC : C0 ^ 2 ≤ x := hC4.trans hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx36
  have hxpos : 0 < x := by linarith
  have hY49 : (4 : ℝ) ^ 9 ≤ x ^ (11 / 20 + ε) := by
    refine Decomp514a.shortY_ge_of_sq_le hε hx1 ?_
    have h49 : ((4 : ℝ) ^ 9) ^ 2 = (2 : ℝ) ^ 36 := by norm_num
    rw [h49]
    exact hx36
  have hYC : C0 ≤ x ^ (11 / 20 + ε) := Decomp514a.shortY_ge_of_sq_le hε hx1 hxC
  have hY1 : (1 : ℝ) ≤ x ^ (11 / 20 + ε) := le_trans (by norm_num) hY49
  have hYpos : 0 < x ^ (11 / 20 + ε) := by linarith
  have hl : (2 : ℝ) ^ (A + 1) ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hxe
  have h2A : (1 : ℝ) ≤ (2 : ℝ) ^ A := Real.one_le_rpow (by norm_num) hA.le
  have hl1 : 1 ≤ Real.log x := by
    rw [Real.rpow_add_one (by norm_num) A] at hl
    linarith
  obtain ⟨hlX1, hlX2⟩ := Decomp514a.log_scale_bounds hε hε8 hxpos hl1
  obtain ⟨hqpow, hout, hlXone⟩ := Decomp514a.log_power_transfer hA hl hlX1 hlX2
  have hscale : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_nonneg hYpos.le (Real.rpow_nonneg (by linarith) _)
  have hC0A : 0 ≤ 8 * C0 * (2 : ℝ) ^ A :=
    mul_nonneg (mul_nonneg (by norm_num) hC0.le) (by linarith)
  have hfinal : (8 * C0 * (2 : ℝ) ^ A + C1) * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ≤
      C * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :=
    mul_le_mul_of_nonneg_right hC1 hscale
  have hCnn : 0 ≤ C := le_trans (by positivity) hC2
  rcases lt_or_ge t 0 with ht0 | ht0
  · have hemp : (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun m _ hmt => ?_
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hmt' : (m : ℝ) ≤ t := hmt
      linarith
    rw [hemp, Finset.sum_empty, abs_zero]
    calc (0 : ℝ) ≤ C * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := mul_nonneg hCnn hscale
      _ = C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by ring
  · rw [Decomp514a.rightInterval_filter_eq ε x t ht0]
    have hNle : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
      Nat.floor_le (by linarith)
    have hN1 : 1 ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ :=
      Nat.le_floor (by rw [Nat.cast_one]; linarith)
    have hUN : min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊ ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ := min_le_left _ _
    have hUle : ((min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊ : ℕ) : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
      (Nat.cast_le.mpr hUN).trans hNle
    have hsp := family_density_split
      (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
          (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
          i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
            lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)))
      (Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ (min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊))
      (lowerTwoTerms ε x)
      (fun m : ℕ => lowerTwoDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))
      (fun (i : ℕ × ℕ) (m : ℕ) => Task308.roughIndicator (m / (i.1 * i.2)) i.2)
      (fun (i : ℕ × ℕ) (m : ℕ) =>
        ω (Real.log ((m / (i.1 * i.2) : ℕ) : ℝ) / Real.log (i.2 : ℝ)) / Real.log (i.2 : ℝ))
      (fun (i : ℕ × ℕ) (m : ℕ) => i.1 * i.2 ∣ m)
      (fun m hm => by
        have hm' := Finset.mem_Ioc.mp hm
        exact Decomp514a.lowerTwoTerms_eq_family ε x (by omega) (hm'.2.trans hUN))
    have h1 := rough_family_density_sum ω hC0
      (show (1 : ℝ) ≤ 2 * x ^ (11 / 20 + ε) by linarith)
      (hbb (2 * x ^ (11 / 20 + ε)) (by linarith))
      (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
          (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ =>
          i.1.Prime ∧ i.2.Prime ∧ i.2 < i.1 ∧
            lowerTwoDiscarded ε (expo ε x i.1) (expo ε x i.2)))
      (fun i : ℕ × ℕ => i.1 * i.2) (fun i : ℕ × ℕ => i.2)
      ⌊x ^ (11 / 20 + ε)⌋₊ (min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊)
      ((2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 2)
      (by
        intro i hi
        obtain ⟨-, hp1, hp2, -, hdisc⟩ := Finset.mem_filter.mp hi
        obtain ⟨hb1, hb2⟩ := Decomp514a.lowerTwo_outer_bounds hε8 hY49 hp1 hp2 hdisc
        exact ⟨Nat.mul_pos hp1.pos hp2.pos, hb1, hb2⟩)
      hUle
      (by
        refine le_trans (Decomp514a.pair_reciprocal_sum_le ⌊2 * x ^ (11 / 20 + ε)⌋₊ _
          (Finset.filter_subset _ _)) ?_
        have hNR : (1 : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by exact_mod_cast hN1
        have hlogN0 : 0 ≤ Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := Real.log_nonneg hNR
        have hlogN : Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤
            Real.log (2 * x ^ (11 / 20 + ε)) := Real.log_le_log (by linarith) hNle
        exact pow_le_pow_left₀ (by linarith) (by linarith) 2)
    have h2 := hmainleaf x (hC5.trans hx) (min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊) hUN
    have h0 : 0 ≤ C0 * (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 2 :=
      mul_nonneg hC0.le (sq_nonneg _)
    have h1' : 0 ≤ Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 2)) :=
      Real.rpow_nonneg (by linarith) _
    have h3 : C0 * (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 2 *
          ((min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊ : ℕ) : ℝ) *
          Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 2)) ≤
        8 * C0 * (2 : ℝ) ^ A * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
      calc C0 * (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 2 *
            ((min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊ : ℕ) : ℝ) *
            Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 2))
          ≤ C0 * (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 2 * (2 * x ^ (11 / 20 + ε)) *
            Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 2)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hUle h0) h1'
        _ = 2 * C0 * x ^ (11 / 20 + ε) * (Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 2)) *
            (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 2) := by ring
        _ ≤ 2 * C0 * x ^ (11 / 20 + ε) * (4 * (2 : ℝ) ^ A * Real.log x ^ (-A)) :=
            mul_le_mul_of_nonneg_left hout
              (mul_nonneg (mul_nonneg (by norm_num) hC0.le) hYpos.le)
        _ = 8 * C0 * (2 : ℝ) ^ A * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by ring
    refine (congrArg abs hsp).le.trans ((abs_add_le _ _).trans
      ((add_le_add (h1.trans h3) h2).trans ?_))
    calc 8 * C0 * (2 : ℝ) ^ A * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) +
          C1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)
        = (8 * C0 * (2 : ℝ) ^ A + C1) * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by ring
      _ ≤ C * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := hfinal
      _ = C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by ring

/-- P0069 page 51, display 5.17, the E4 term, assembled from the leaves of
`LowerPrincipal517f.lean`. The statement is exactly that of `leaf_four_rough_density`. The sum
over `p1 p2 p3 p4 n5 = m` with exponents in E4 is written as a family sum over prime
quadruples; the rough cofactor `n5` is replaced by its Buchstab density with
`leaf_rough_interval_density` at the scale `2 Y`, summed over the quadruples with
`Decomp514a.four_reciprocal_sum_le`; the remaining sum over the quadruples is
`leaf_four_density_main`. -/
theorem four_rough_density_of_leaves (ω : ℝ → ℝ)
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
      |∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (lowerFourTerms ε x m -
          lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))| ≤
        C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C0, hC0, hbb⟩ := leaf_rough_interval_density ω hω hz (c := 1 / 10) (by norm_num)
    (A + 4) (by linarith)
  obtain ⟨C1, hmainleaf⟩ := leaf_four_density_main ω hω hz hε hε8 A hA
  refine ⟨max (32 * C0 * (2 : ℝ) ^ A + C1)
    (max ((2 : ℝ) ^ 12) (max (Real.exp ((2 : ℝ) ^ (A + 1))) (max (C0 ^ 2) C1))), ?_⟩
  generalize hCdef : max (32 * C0 * (2 : ℝ) ^ A + C1)
    (max ((2 : ℝ) ^ 12) (max (Real.exp ((2 : ℝ) ^ (A + 1))) (max (C0 ^ 2) C1))) = C
  have hC1 : 32 * C0 * (2 : ℝ) ^ A + C1 ≤ C := by rw [← hCdef]; exact le_max_left _ _
  have hC2 : (2 : ℝ) ^ 12 ≤ C := by
    rw [← hCdef]; exact (le_max_left _ _).trans (le_max_right _ _)
  have hC3 : Real.exp ((2 : ℝ) ^ (A + 1)) ≤ C := by
    rw [← hCdef]
    exact (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hC4 : C0 ^ 2 ≤ C := by
    rw [← hCdef]
    exact (le_max_left _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  have hC5 : C1 ≤ C := by
    rw [← hCdef]
    exact (le_max_right _ _).trans
      ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _)))
  intro x hx t ht
  have hx12 : (2 : ℝ) ^ 12 ≤ x := hC2.trans hx
  have hxe : Real.exp ((2 : ℝ) ^ (A + 1)) ≤ x := hC3.trans hx
  have hxC : C0 ^ 2 ≤ x := hC4.trans hx
  have hx1 : (1 : ℝ) ≤ x := le_trans (by norm_num) hx12
  have hxpos : 0 < x := by linarith
  have hY43 : (4 : ℝ) ^ 3 ≤ x ^ (11 / 20 + ε) := by
    refine Decomp514a.four_shortY_ge_of_sq_le hε hx1 ?_
    have h43 : ((4 : ℝ) ^ 3) ^ 2 = (2 : ℝ) ^ 12 := by norm_num
    rw [h43]
    exact hx12
  have hYC : C0 ≤ x ^ (11 / 20 + ε) := Decomp514a.four_shortY_ge_of_sq_le hε hx1 hxC
  have hY1 : (1 : ℝ) ≤ x ^ (11 / 20 + ε) := le_trans (by norm_num) hY43
  have hYpos : 0 < x ^ (11 / 20 + ε) := by linarith
  have hl : (2 : ℝ) ^ (A + 1) ≤ Real.log x := (Real.le_log_iff_exp_le hxpos).mpr hxe
  have h2A : (1 : ℝ) ≤ (2 : ℝ) ^ A := Real.one_le_rpow (by norm_num) hA.le
  have hl1 : 1 ≤ Real.log x := by
    rw [Real.rpow_add_one (by norm_num) A] at hl
    linarith
  have hlX1 := Decomp514a.four_log_scale_ge hε hxpos hl1
  obtain ⟨hqpow, hout, hlXone⟩ := Decomp514a.four_log_power_transfer hA hl hlX1
  have hscale : 0 ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_nonneg hYpos.le (Real.rpow_nonneg (by linarith) _)
  have hC0A : 0 ≤ 32 * C0 * (2 : ℝ) ^ A :=
    mul_nonneg (mul_nonneg (by norm_num) hC0.le) (by linarith)
  have hfinal : (32 * C0 * (2 : ℝ) ^ A + C1) * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) ≤
      C * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) :=
    mul_le_mul_of_nonneg_right hC1 hscale
  have hCnn : 0 ≤ C := le_trans (by positivity) hC2
  rcases lt_or_ge t 0 with ht0 | ht0
  · have hemp : (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr fun m _ hmt => ?_
      have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
      have hmt' : (m : ℝ) ≤ t := hmt
      linarith
    rw [hemp, Finset.sum_empty, abs_zero]
    calc (0 : ℝ) ≤ C * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := mul_nonneg hCnn hscale
      _ = C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by ring
  · rw [Decomp514a.four_rightInterval_filter_eq ε x t ht0]
    have hNle : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
      Nat.floor_le (by linarith)
    have hN1 : 1 ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ :=
      Nat.le_floor (by rw [Nat.cast_one]; linarith)
    have hUN : min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊ ≤ ⌊2 * x ^ (11 / 20 + ε)⌋₊ := min_le_left _ _
    have hUle : ((min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊ : ℕ) : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
      (Nat.cast_le.mpr hUN).trans hNle
    have hsp := family_density_split
      (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
          (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
          (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
          (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
          i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
            i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
            lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
              (expo ε x i.2.2.2)))
      (Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ (min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊))
      (lowerFourTerms ε x)
      (fun m : ℕ => lowerFourDensityAt ω ε (Real.log m / Real.log (scaleZ ε x)) /
            Real.log (scaleZ ε x))
      (fun (i : ℕ × ℕ × ℕ × ℕ) (m : ℕ) =>
        Task308.roughIndicator (m / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2)) i.2.2.2)
      (fun (i : ℕ × ℕ × ℕ × ℕ) (m : ℕ) =>
        ω (Real.log ((m / (i.1 * i.2.1 * i.2.2.1 * i.2.2.2) : ℕ) : ℝ) /
            Real.log (i.2.2.2 : ℝ)) / Real.log (i.2.2.2 : ℝ))
      (fun (i : ℕ × ℕ × ℕ × ℕ) (m : ℕ) => i.1 * i.2.1 * i.2.2.1 * i.2.2.2 ∣ m)
      (fun m hm => by
        have hm' := Finset.mem_Ioc.mp hm
        exact Decomp514a.four_terms_eq_family ε x (by omega) (hm'.2.trans hUN))
    have h1 := rough_family_density_sum ω hC0
      (show (1 : ℝ) ≤ 2 * x ^ (11 / 20 + ε) by linarith)
      (hbb (2 * x ^ (11 / 20 + ε)) (by linarith))
      (((Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
          (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
          (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊) ×ˢ
          (Finset.Icc 1 ⌊2 * x ^ (11 / 20 + ε)⌋₊)).filter (fun i : ℕ × ℕ × ℕ × ℕ =>
          i.1.Prime ∧ i.2.1.Prime ∧ i.2.2.1.Prime ∧ i.2.2.2.Prime ∧ i.2.1 < i.1 ∧
            i.2.2.1 < i.2.1 ∧ i.2.2.2 < i.2.2.1 ∧
            lowerFourRegion ε (expo ε x i.1) (expo ε x i.2.1) (expo ε x i.2.2.1)
              (expo ε x i.2.2.2)))
      (fun i : ℕ × ℕ × ℕ × ℕ => i.1 * i.2.1 * i.2.2.1 * i.2.2.2)
      (fun i : ℕ × ℕ × ℕ × ℕ => i.2.2.2)
      ⌊x ^ (11 / 20 + ε)⌋₊ (min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊)
      ((2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 4)
      (by
        intro i hi
        obtain ⟨-, hp1, hp2, hp3, hp4, -, -, -, hreg⟩ := Finset.mem_filter.mp hi
        obtain ⟨hb1, hb2⟩ := Decomp514a.four_outer_bounds hε hε8 hY43 hp1 hp2 hp3 hp4 hreg
        exact ⟨Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hp1.pos hp2.pos) hp3.pos) hp4.pos,
          hb1, hb2⟩)
      hUle
      (by
        refine le_trans (Decomp514a.four_reciprocal_sum_le ⌊2 * x ^ (11 / 20 + ε)⌋₊ _
          (Finset.filter_subset _ _)) ?_
        have hNR : (1 : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by exact_mod_cast hN1
        have hlogN0 : 0 ≤ Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := Real.log_nonneg hNR
        have hlogN : Real.log (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤
            Real.log (2 * x ^ (11 / 20 + ε)) := Real.log_le_log (by linarith) hNle
        exact pow_le_pow_left₀ (by linarith) (by linarith) 4)
    have h2 := hmainleaf x (hC5.trans hx) (min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊) hUN
    have h0 : 0 ≤ C0 * (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 4 :=
      mul_nonneg hC0.le (by positivity)
    have h1' : 0 ≤ Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 4)) :=
      Real.rpow_nonneg (by linarith) _
    have h3 : C0 * (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 4 *
          ((min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊ : ℕ) : ℝ) *
          Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 4)) ≤
        32 * C0 * (2 : ℝ) ^ A * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
      calc C0 * (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 4 *
            ((min ⌊2 * x ^ (11 / 20 + ε)⌋₊ ⌊t⌋₊ : ℕ) : ℝ) *
            Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 4))
          ≤ C0 * (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 4 * (2 * x ^ (11 / 20 + ε)) *
            Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 4)) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hUle h0) h1'
        _ = 2 * C0 * x ^ (11 / 20 + ε) * (Real.log (2 * x ^ (11 / 20 + ε)) ^ (-(A + 4)) *
            (2 * Real.log (2 * x ^ (11 / 20 + ε))) ^ 4) := by ring
        _ ≤ 2 * C0 * x ^ (11 / 20 + ε) * (16 * (2 : ℝ) ^ A * Real.log x ^ (-A)) :=
            mul_le_mul_of_nonneg_left hout
              (mul_nonneg (mul_nonneg (by norm_num) hC0.le) hYpos.le)
        _ = 32 * C0 * (2 : ℝ) ^ A * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by ring
    refine (congrArg abs hsp).le.trans ((abs_add_le _ _).trans
      ((add_le_add (h1.trans h3) h2).trans ?_))
    calc 32 * C0 * (2 : ℝ) ^ A * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) +
          C1 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)
        = (32 * C0 * (2 : ℝ) ^ A + C1) * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by ring
      _ ≤ C * (x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := hfinal
      _ = C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by ring

#print axioms two_rough_density_of_leaves
#print axioms four_rough_density_of_leaves

end LeanLab.BHP1997.LowerShortC165
