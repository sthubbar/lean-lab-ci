/-
P0045, journal page 777, displays 20 to 24, and pages 778 to 779, displays 28 to 30.
The finite period estimates give D4Asymp conditional on the uniform tail of the actual count.
The tail predicate is written in full. D4TailProof proves it without cited inputs.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LPZ2007.D4Limits
import LeanLab.LPZ2007.D4Count
import LeanLab.LPZ2007.R3FromS3

namespace LeanLab.LPZ2007.D4Asymptotic

open Finset Filter Topology Real
open LeanLab.LPZ2007 LeanLab.LPZ2007.D4Count LeanLab.LPZ2007.R3FromS3

noncomputable section

attribute [local instance] Classical.propDecidable

/-- Every odd modulus of period at most T is at most 2 to the T. -/
theorem modulus_le_two_pow {d T : ℕ} (hd : Odd d) (hT : xi d ≤ T) : d ≤ 2 ^ T := by
  have hx : 0 < xi d := xi_pos hd
  have hp : 1 ≤ 2 ^ xi d := Nat.one_le_two_pow
  have hmod : d ∣ 2 ^ xi d - 1 := by
    rw [← ZMod.natCast_eq_zero_iff]
    push_cast [Nat.cast_sub hp]
    rw [two_pow_xi, sub_self]
  have hpos : 0 < 2 ^ xi d - 1 := by
    have : 2 ≤ 2 ^ xi d := by
      simpa using Nat.pow_le_pow_right (by decide : 0 < 2) hx
    omega
  exact (Nat.le_of_dvd hpos hmod).trans
    ((Nat.sub_le _ _).trans (Nat.pow_le_pow_right (by decide) hT))

/-- The normalized periodic count, with non odd squarefree moduli set to zero. -/
def aTerm (k : ℕ) (X : ℝ) (N d : ℕ) : ℝ :=
  if OddSqf d then fd d * (cnt d k ⌊Lp X⌋₊ (N : ZMod d) : ℝ) / Lg X ^ k else 0

/-- A nonnegative envelope for the error at one modulus. -/
def errorTerm (k d : ℕ) (L : ℝ) : ℝ :=
  fd d * (xi d : ℝ) ^ (k - 1) *
    (|(((⌊L - √L⌋₊ / xi d : ℕ) : ℝ) / L) ^ k - (1 / (xi d : ℝ)) ^ k| +
     |((((⌊L - √L⌋₊ / xi d : ℕ) : ℝ) + 1) / L) ^ k - (1 / (xi d : ℝ)) ^ k|)

/-- For a fixed odd modulus the envelope tends to zero. -/
theorem errorTerm_tendsto {d : ℕ} (hd : Odd d) (k : ℕ) :
    Tendsto (errorTerm k d) atTop (𝓝 0) := by
  unfold errorTerm
  simpa only [mul_zero] using
    (D4Limits.period_error_tendsto (xi d) k (xi_pos hd)).const_mul
      (fd d * (xi d : ℝ) ^ (k - 1))

/-- The error envelope is uniform in the residue N. -/
theorem aTerm_error {d k : ℕ} (hd : OddSqf d) (hk : 1 ≤ k) {X : ℝ}
    (hL : 0 < Lg X) (N : ℕ) :
    |aTerm k X N d - cTerm k N d| ≤ errorTerm k d (Lg X) := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hQ : 0 < Lg X ^ (j + 1) := pow_pos hL _
  obtain ⟨hlo, hhi⟩ := count_jd_bounds hd.1 ⌊Lp X⌋₊ (j + 1) N
  have hlo' : (((⌊Lp X⌋₊ / xi d : ℕ) : ℝ) / Lg X) ^ (j + 1) * jd d (j + 1) N ≤
      (cnt d (j + 1) ⌊Lp X⌋₊ (N : ZMod d) : ℝ) / Lg X ^ (j + 1) := by
    rw [div_pow, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hQ]
    exact_mod_cast hlo
  have hhi' : (cnt d (j + 1) ⌊Lp X⌋₊ (N : ZMod d) : ℝ) / Lg X ^ (j + 1) ≤
      ((((⌊Lp X⌋₊ / xi d : ℕ) : ℝ) + 1) / Lg X) ^ (j + 1) * jd d (j + 1) N := by
    rw [div_pow, div_mul_eq_mul_div, div_le_div_iff_of_pos_right hQ]
    exact_mod_cast hhi
  have hb := D4Limits.between_mul_error (t := (1 / (xi d : ℝ)) ^ (j + 1))
    (J := (xi d : ℝ) ^ j) (Nat.cast_nonneg (jd d (j + 1) N))
    (by exact_mod_cast eq19 hd.1 j N) hlo' hhi'
  have he : aTerm (j + 1) X N d - cTerm (j + 1) N d =
      fd d * ((cnt d (j + 1) ⌊Lp X⌋₊ (N : ZMod d) : ℝ) / Lg X ^ (j + 1) -
        (1 / (xi d : ℝ)) ^ (j + 1) * jd d (j + 1) N) := by
    simp only [aTerm, cTerm, ite_eq_left hd, one_div_pow]
    ring
  rw [he, abs_mul, abs_of_nonneg (fd_nonneg d)]
  have := mul_le_mul_of_nonneg_left hb (fd_nonneg d)
  simpa [errorTerm, Lp, mul_assoc] using this

/-- A finite collection of moduli has uniformly vanishing error. -/
theorem finite_head_approx (s : Finset ℕ) (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ N : ℕ,
      |∑ d ∈ s, aTerm k X N d - ∑ d ∈ s, cTerm k N d| ≤ ε := by
  let E : ℝ → ℝ := fun L => ∑ d ∈ s, if OddSqf d then errorTerm k d L else 0
  have hE : Tendsto E atTop (𝓝 0) := by
    have h := tendsto_finsetSum s (fun d _ => show
        Tendsto (fun L => if OddSqf d then errorTerm k d L else 0) atTop (𝓝 0) from by
      by_cases hd : OddSqf d
      · simpa only [ite_eq_left hd] using errorTerm_tendsto hd.1 k
      · simpa only [ite_eq_right hd] using (tendsto_const_nhds :
          Tendsto (fun _ : ℝ => (0 : ℝ)) atTop (𝓝 0)))
    simpa [E] using h
  have hLg : Tendsto Lg atTop atTop := Real.tendsto_logb_atTop (by norm_num)
  obtain ⟨X0, hX0⟩ := ((tendsto_order.1 (hE.comp hLg)).2 ε hε).exists_forall_of_atTop
  refine ⟨max X0 2, fun X hX N => ?_⟩
  have hL : 0 < Lg X := Lg_pos (by have := (le_max_right X0 2).trans hX; linarith)
  calc |∑ d ∈ s, aTerm k X N d - ∑ d ∈ s, cTerm k N d|
      = |∑ d ∈ s, (aTerm k X N d - cTerm k N d)| := by rw [sum_sub_distrib]
    _ ≤ ∑ d ∈ s, |aTerm k X N d - cTerm k N d| := abs_sum_le_sum_abs _ _
    _ ≤ E (Lg X) := by
      apply sum_le_sum
      intro d hd
      by_cases ho : OddSqf d
      · simpa only [ite_eq_left ho] using aTerm_error ho hk hL N
      · simp [aTerm, cTerm, ho]
    _ ≤ ε := (hX0 X ((le_max_left _ _).trans hX)).le

/-- The coefficient tail is bounded uniformly in N by the Romanov tail. -/
theorem coefficient_tail (D j N : ℕ) :
    0 ≤ Ckn (j + 1) N - ∑ d ∈ range D, cTerm (j + 1) N d ∧
    Ckn (j + 1) N - ∑ d ∈ range D, cTerm (j + 1) N d ≤
      ∑' n, romanovTerm (n + D) := by
  have hs := Ckn_summable Lemma61Port.lemma61_proved j N
  have he : Ckn (j + 1) N - ∑ d ∈ range D, cTerm (j + 1) N d =
      ∑' n, cTerm (j + 1) N (n + D) := by
    have h := Summable.sum_add_tsum_nat_add D hs
    rw [← Ckn_eq] at h
    linarith
  rw [he]
  exact ⟨tsum_nonneg (fun n => cTerm_nonneg _ _ _),
    Summable.tsum_le_tsum (fun n => cTerm_le j N (n + D))
      ((summable_nat_add_iff D).2 hs)
      ((summable_nat_add_iff D).2 Lemma61Port.lemma61_proved)⟩

/-- The normalized count agrees with the divisor term once subtraction is exact. -/
theorem aTerm_eq_count (k : ℕ) (X : ℝ) (N d : ℕ)
    (hsmall : ∀ ν ∈ tuples k ⌊Lp X⌋₊, pow2sum ν ≤ N) :
    aTerm k X N d =
      (if OddSqf d then fd d *
        (#{ν ∈ tuples k ⌊Lp X⌋₊ | d ∣ N - pow2sum ν} : ℝ) else 0) / Lg X ^ k := by
  unfold aTerm
  rw [D4count_eq_cnt d k _ N hsmall]
  split_ifs <;> simp

/-- The full normalized D4 is the finite sum of normalized counts. -/
theorem D4_div_eq_sum (k : ℕ) (X : ℝ) (N : ℕ)
    (hsmall : ∀ ν ∈ tuples k ⌊Lp X⌋₊, pow2sum ν ≤ N) :
    D4 k X N / Lg X ^ k = ∑ d ∈ range (N + 1), aTerm k X N d := by
  have hzero : ¬ OddSqf 0 := by simp [OddSqf]
  have he : ∑ d ∈ Icc 1 N, aTerm k X N d =
      ∑ d ∈ range (N + 1), aTerm k X N d := by
    apply sum_subset
    · intro d hd
      simp only [mem_Icc] at hd
      simp only [mem_range]; omega
    · intro d hd hdn
      have : d = 0 := by simp only [mem_range, mem_Icc] at *; omega
      subst d; simp [aTerm, hzero]
  rw [← he]
  simp only [D4, sum_filter, sum_div]
  exact sum_congr rfl fun d _ => (aTerm_eq_count k X N d hsmall).symm

/-- Cutting beyond 2 to the T leaves only moduli of period greater than T. -/
theorem count_tail_le {k N T D : ℕ} {X ε : ℝ} (hD : 2 ^ T ≤ D)
    (hL : 0 < Lg X) (hsmall : ∀ ν ∈ tuples k ⌊Lp X⌋₊, pow2sum ν ≤ N)
    (htail : ∑ d ∈ (Icc 1 N).filter (fun d => OddSqf d ∧ T < xi d),
      fd d * (#{ν ∈ tuples k ⌊Lp X⌋₊ | d ∣ N - pow2sum ν} : ℝ) ≤ ε * Lg X ^ k) :
    ∑ d ∈ Ico (D + 1) (N + 1), aTerm k X N d ≤ ε := by
  have hQ : 0 < Lg X ^ k := pow_pos hL _
  let F : ℕ → ℝ := fun d => fd d *
    (#{ν ∈ tuples k ⌊Lp X⌋₊ | d ∣ N - pow2sum ν} : ℝ)
  have he : ∑ d ∈ Ico (D + 1) (N + 1), aTerm k X N d =
      (∑ d ∈ (Ico (D + 1) (N + 1)).filter OddSqf, F d) / Lg X ^ k := by
    rw [sum_filter, sum_div]
    exact sum_congr rfl fun d _ => aTerm_eq_count k X N d hsmall
  have hsub : (Ico (D + 1) (N + 1)).filter OddSqf ⊆
      (Icc 1 N).filter (fun d => OddSqf d ∧ T < xi d) := by
    intro d hd
    obtain ⟨hdI, ho⟩ := mem_filter.1 hd
    obtain ⟨hd1, hd2⟩ := mem_Ico.1 hdI
    have hξ : T < xi d := by
      by_contra hn
      have := modulus_le_two_pow ho.1 (by omega : xi d ≤ T)
      omega
    exact mem_filter.2 ⟨mem_Icc.2 ⟨by omega, by omega⟩, ho, hξ⟩
  rw [he, div_le_iff₀ hQ]
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun d _ _ =>
    mul_nonneg (fd_nonneg d) (Nat.cast_nonneg _))).trans htail

/-- Displays 20 to 24, conditional on the actual uniform large-period tail. -/
theorem d4Asymp_of_uniform_tail (hTail : (∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ T0 : ℕ, ∀ T : ℕ, T0 ≤ T →
    ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ N : ℕ, Even N → InJ X N →
      ∑ d ∈ (Icc 1 N).filter (fun d => OddSqf d ∧ T < xi d),
        fd d * (#{ν ∈ tuples k ⌊Lp X⌋₊ | d ∣ N - pow2sum ν} : ℝ) ≤ ε * Lg X ^ k)) : D4Asymp := by
  intro k hk η hη
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hε : 0 < η / 3 := by positivity
  obtain ⟨D0, hD0⟩ := ((tendsto_order.1 (tendsto_sum_nat_add romanovTerm)).2
    (η / 3) hε).exists_forall_of_atTop
  obtain ⟨T0, hT0⟩ := hTail (j + 1) hk (η / 3) hε
  let T := max T0 D0
  let D := 2 ^ T
  have hTD : T < D := Nat.lt_two_pow_self
  obtain ⟨Xt, ht⟩ := hT0 T (le_max_left _ _)
  obtain ⟨Xh, hh⟩ := finite_head_approx (range (D + 1)) (j + 1) hk (η / 3) hε
  let Xb : ℝ := max 2 (max (3 * ((D : ℝ) + 1))
    ((2 : ℝ) ^ (36 * ((j + 1 : ℕ) : ℝ) ^ 2)))
  refine ⟨max Xt (max Xh Xb), fun X hX N hNe hNJ => ?_⟩
  have hXt : Xt ≤ X := (le_max_left _ _).trans hX
  have hXh : Xh ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hXb : Xb ≤ X := ((le_max_right _ _).trans (le_max_right _ _)).trans hX
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hXb
  have hXL : (2 : ℝ) ^ (36 * ((j + 1 : ℕ) : ℝ) ^ 2) ≤ X :=
    ((le_max_right _ _).trans (le_max_right _ _)).trans hXb
  have hXD : 3 * ((D : ℝ) + 1) ≤ X :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans hXb
  have hL : 0 < Lg X := Lg_pos (by linarith)
  have hQ : 0 < Lg X ^ (j + 1) := pow_pos hL _
  have hDN : D ≤ N := by exact_mod_cast (show (D : ℝ) ≤ N by linarith [hNJ.1])
  have hsmall : ∀ ν ∈ tuples (j + 1) ⌊Lp X⌋₊, pow2sum ν ≤ N := by
    intro ν hν
    have h1 := Eq14FromCor42.pow2sum_small hk (by linarith : 0 < X)
      (Eq14FromCor42.Lg_ge hXL) hν
    exact_mod_cast (show (pow2sum ν : ℝ) ≤ N by linarith [hNJ.1])
  have hactual := count_tail_le (D := D) (le_refl _) hL hsmall (ht X hXt N hNe hNJ)
  have hactual0 : 0 ≤ ∑ d ∈ Ico (D + 1) (N + 1), aTerm (j + 1) X N d := by
    apply sum_nonneg
    intro d _
    unfold aTerm
    split_ifs
    · exact div_nonneg (mul_nonneg (fd_nonneg _) (Nat.cast_nonneg _)) hQ.le
    · exact le_refl _
  have hcoeff := coefficient_tail (D + 1) j N
  have hcoeff_le : Ckn (j + 1) N - ∑ d ∈ range (D + 1), cTerm (j + 1) N d ≤ η / 3 :=
    hcoeff.2.trans (hD0 (D + 1) (by have := le_max_right T0 D0; omega)).le
  have hhead := hh X hXh N
  have hsplit := sum_range_add_sum_Ico (aTerm (j + 1) X N) (by omega : D + 1 ≤ N + 1)
  have hnormalized : |D4 (j + 1) X N / Lg X ^ (j + 1) - Ckn (j + 1) N| ≤ η := by
    rw [D4_div_eq_sum _ _ _ hsmall]
    obtain ⟨hl, hu⟩ := abs_le.1 hhead
    apply abs_le.2
    constructor <;> linarith [hcoeff.1]
  have he : (D4 (j + 1) X N - Ckn (j + 1) N * Lg X ^ (j + 1)) / Lg X ^ (j + 1) =
      D4 (j + 1) X N / Lg X ^ (j + 1) - Ckn (j + 1) N := by
    field_simp
  rw [← he, abs_div, abs_of_pos hQ] at hnormalized
  exact (div_le_iff₀ hQ).1 hnormalized

/-- The repaired main theorem is conditional on Cor42W and the actual divisor tail. -/
theorem mainJ_of_cor42_uniform_tail (hC : Eq14FromCor42.Cor42W)
    (hTail : (∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε → ∃ T0 : ℕ, ∀ T : ℕ, T0 ≤ T →
    ∃ X0 : ℝ, ∀ X : ℝ, X0 ≤ X → ∀ N : ℕ, Even N → InJ X N →
      ∑ d ∈ (Icc 1 N).filter (fun d => OddSqf d ∧ T < xi d),
        fd d * (#{ν ∈ tuples k ⌊Lp X⌋₊ | d ∣ N - pow2sum ν} : ℝ) ≤ ε * Lg X ^ k)) : MainJ_twoC0 :=
  mainJ_twoC0_of_cor42_d4 hC (d4Asymp_of_uniform_tail hTail)

/-- A concrete finite instance of the cited tail has no exponent tuples. -/
theorem tail_at_two (T : ℕ) :
    ∑ d ∈ (Icc 1 2).filter (fun d => OddSqf d ∧ T < xi d),
      fd d * (#{ν ∈ tuples 1 ⌊Lp 2⌋₊ | d ∣ 2 - pow2sum ν} : ℝ) = 0 := by
  have hLp : Lp 2 = 0 := by norm_num [Lp, Lg, Real.logb_self_eq_one]
  have htu : tuples 1 0 = ∅ := by decide
  simp [hLp, htu]

end
end LeanLab.LPZ2007.D4Asymptotic

#print axioms LeanLab.LPZ2007.D4Asymptotic.modulus_le_two_pow
#print axioms LeanLab.LPZ2007.D4Asymptotic.errorTerm_tendsto
#print axioms LeanLab.LPZ2007.D4Asymptotic.aTerm_error
#print axioms LeanLab.LPZ2007.D4Asymptotic.finite_head_approx
#print axioms LeanLab.LPZ2007.D4Asymptotic.coefficient_tail
#print axioms LeanLab.LPZ2007.D4Asymptotic.aTerm_eq_count
#print axioms LeanLab.LPZ2007.D4Asymptotic.D4_div_eq_sum
#print axioms LeanLab.LPZ2007.D4Asymptotic.count_tail_le
#print axioms LeanLab.LPZ2007.D4Asymptotic.d4Asymp_of_uniform_tail
#print axioms LeanLab.LPZ2007.D4Asymptotic.mainJ_of_cor42_uniform_tail
#print axioms LeanLab.LPZ2007.D4Asymptotic.tail_at_two
