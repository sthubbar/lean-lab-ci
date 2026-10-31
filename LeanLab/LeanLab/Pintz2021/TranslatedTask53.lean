import LeanLab.Pintz2021.DivisorSumTask53
import LeanLab.LanguascoPintzZaccagnini2007.Lemma62

/-!
Translated congruence counts and divisor tails for P0054 Lemma 2.
Source: author copy page 14 display 4.9 and page 15 Romanov paragraph.
The arithmetic proofs in LPZ2007 are reused with their actual hypotheses.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Pintz2021.TranslatedTask53

open Finset DivisorSumTask53

attribute [local instance] Classical.propDecidable

/-- The translated exponent count for the combined odd moduli. -/
theorem translated_count_le (m q K d : ℕ) (hq : Odd q) (hq0 : 0 < q)
    (hd : Odd d) (hd0 : 0 < d) :
    (eligibleExponents m (Nat.lcm d q) K).card ≤
      K / LeanLab.LPZ2007.xi (Nat.lcm d q) + 1 := by
  have ho : Odd (Nat.lcm d q) := (hd.mul hq).of_dvd_nat (Nat.lcm_dvd_mul d q)
  have hp : 0 < Nat.lcm d q := Nat.lcm_pos hd0 hq0
  exact LeanLab.LPZ2007.card_nu_le ho hp K m

/-- Large odd squarefree divisors have a small weighted tail uniformly in q. -/
theorem uniform_divisor_tail {ε : ℝ} (hε : 0 < ε) :
    ∃ D : ℕ, ∀ q : ℕ, Odd q → 0 < q → ∀ T : Finset ℕ,
      (∀ d ∈ T, D < d ∧ Odd d ∧ Squarefree d) →
      ∑ d ∈ T, divisorWeight d / LeanLab.LPZ2007.xi (Nat.lcm d q) ≤ ε := by
  obtain ⟨D, hD⟩ :=
    (tendsto_order.1 (tendsto_sum_nat_add LeanLab.LPZ2007.seriesTerm)).2 ε hε
      |>.exists_forall_of_atTop
  refine ⟨D, fun q hq hq0 T hT => ?_⟩
  have htail : ∑' k, LeanLab.LPZ2007.seriesTerm (k + (D + 1)) < ε :=
    hD (D + 1) (by omega)
  calc
    _ ≤ ∑ d ∈ T, LeanLab.LPZ2007.seriesTerm d := by
      apply sum_le_sum
      intro d hd
      obtain ⟨_, hodd, hsq⟩ := hT d hd
      have hd0 : 0 < d := hsq.ne_zero.bot_lt
      have hds : LeanLab.LPZ2007.OddSqf d := ⟨hd0, hodd, hsq⟩
      have hlodd : Odd (Nat.lcm d q) :=
        (hodd.mul hq).of_dvd_nat (Nat.lcm_dvd_mul d q)
      have hlpos : 0 < Nat.lcm d q := Nat.lcm_pos hd0 hq0
      have hmono : LeanLab.LPZ2007.xi d ≤ LeanLab.LPZ2007.xi (Nat.lcm d q) :=
        LeanLab.LPZ2007.xi_mono hlodd hlpos (Nat.dvd_lcm_left d q)
      have hxi : (0 : ℝ) < LeanLab.LPZ2007.xi d := by
        exact_mod_cast (LeanLab.LPZ2007.xi_odd hodd hd0).1
      have hw : divisorWeight d = LeanLab.LPZ2007.fd d :=
        (LeanLab.LPZ2007.fd_eq hds).symm
      rw [hw, LeanLab.LPZ2007.seriesTerm, ite_eq_left hds]
      exact div_le_div_of_nonneg_left (LeanLab.LPZ2007.fd_nonneg hds) hxi
        (by exact_mod_cast hmono)
    _ ≤ ∑' k, LeanLab.LPZ2007.seriesTerm (k + (D + 1)) :=
      LeanLab.LPZ2007.tail_le D T (fun d hd => (hT d hd).1)
    _ ≤ ε := htail.le

/-- The finite three-part estimate keeps the boundary product from the count. -/
theorem lemma2_three_part_bound (m q K D : ℕ) (L : ℝ)
    (hq : Odd q) (hq0 : 0 < q) (hK : (K : ℝ) ≤ L) (hD : 4 ≤ D) :
    ∑ ν ∈ eligibleExponents m q K, Sing (m - 2 ^ ν) ≤
      2 * C0 * (L * (Real.exp 27 * Real.log D) / LeanLab.LPZ2007.xi q +
        L * ∑' k, LeanLab.LPZ2007.seriesTerm (k + (D + 1)) +
        LeanLab.LPZ2007.H (∏ ν ∈ eligibleExponents m q K, (m - 2 ^ ν))) := by
  have hV : ∀ ν ∈ eligibleExponents m q K,
      ν ∈ Icc 1 K ∧ 2 ^ ν < m ∧ q ∣ m - 2 ^ ν := by
    intro ν hν
    exact mem_filter.mp hν
  have hmain := LeanLab.LPZ2007.sum_H_le (eligibleExponents m q K) K m q D L
    hV hq hq0 hK hD
  rw [← LeanLab.LPZ2007.H_eq_sum] at hmain
  have heq : ∑ ν ∈ eligibleExponents m q K, Sing (m - 2 ^ ν) =
      2 * C0 * ∑ ν ∈ eligibleExponents m q K, LeanLab.LPZ2007.H (m - 2 ^ ν) := by
    rw [mul_sum]
    rfl
  rw [heq]
  exact mul_le_mul_of_nonneg_left hmain (by have := Applications.C0_pos; positivity)

/-- The boundary product costs only a logarithm of a quadratic logarithmic cutoff. -/
theorem boundary_product_le (m q K : ℕ) {X : ℝ} (hX : 1 ≤ X) (hm : (m : ℝ) ≤ X)
    (hK : (K : ℝ) ≤ Real.logb 2 X) :
    LeanLab.LPZ2007.H (∏ ν ∈ eligibleExponents m q K, (m - 2 ^ ν)) ≤
      Real.exp 27 * Real.log (⌈(Real.logb 2 X) ^ 2⌉₊ + 4 : ℕ) := by
  set V := eligibleExponents m q K
  set P := ∏ ν ∈ V, (m - 2 ^ ν)
  set L := Real.logb 2 X
  have hL0 : 0 ≤ L := Real.logb_nonneg (by norm_num) hX
  have hP0 : P ≠ 0 := by
    apply prod_ne_zero_iff.mpr
    intro ν hν
    exact (Nat.sub_pos_of_lt (mem_filter.mp hν).2.1).ne'
  have hcardV : (V.card : ℝ) ≤ L := by
    have hc : V.card ≤ K := by
      calc
        V.card ≤ (Icc 1 K).card := card_le_card (filter_subset _ _)
        _ = K := by simp
    exact (by exact_mod_cast hc : (V.card : ℝ) ≤ K).trans hK
  have hω : (P.primeFactors.card : ℝ) ≤ L ^ 2 := by
    have h1 : 2 ^ P.primeFactors.card ≤ P := LeanLab.Romanov.two_pow_card_le P hP0
    have h2 : P ≤ m ^ V.card := by
      calc
        P ≤ ∏ _ν ∈ V, m := prod_le_prod fun ν _ => Nat.sub_le m (2 ^ ν)
        _ = m ^ V.card := prod_const m
    have h3 : (2 : ℝ) ^ P.primeFactors.card ≤ X ^ V.card := by
      calc
        (2 : ℝ) ^ P.primeFactors.card ≤ (m : ℝ) ^ V.card := by
          exact_mod_cast h1.trans h2
        _ ≤ X ^ V.card := pow_le_pow_left₀ (Nat.cast_nonneg _) hm _
    have h4 := Real.log_le_log (by positivity) h3
    rw [Real.log_pow, Real.log_pow] at h4
    have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
    have hLX : Real.log X = L * Real.log 2 := by
      dsimp only [L]
      rw [Real.logb, div_mul_cancel₀ _ hl2.ne']
    rw [hLX] at h4
    have hω' : (P.primeFactors.card : ℝ) ≤ V.card * L := by nlinarith
    nlinarith
  have hωceil : P.primeFactors.card ≤ ⌈L ^ 2⌉₊ + 4 := by
    have hc := hω.trans (Nat.le_ceil (L ^ 2))
    have : P.primeFactors.card ≤ ⌈L ^ 2⌉₊ := by exact_mod_cast hc
    omega
  rw [LeanLab.LPZ2007.H_eq_sum]
  exact LeanLab.LPZ2007.sum_W_opf_le P (⌈L ^ 2⌉₊ + 4) (by omega) hωceil

/-- The boundary is a uniformly small multiple of the logarithmic scale. -/
theorem boundary_product_small (m q K : ℕ) {X ε : ℝ} (hX : 1 ≤ X)
    (hm : (m : ℝ) ≤ X) (hK : (K : ℝ) ≤ Real.logb 2 X) (hε : 0 < ε)
    (hscale : (6 * Real.exp 27 / ε) ^ 2 + 1 ≤ Real.logb 2 X) :
    LeanLab.LPZ2007.H (∏ ν ∈ eligibleExponents m q K, (m - 2 ^ ν)) ≤
      ε * Real.logb 2 X := by
  set L := Real.logb 2 X
  have hL1 : 1 ≤ L := by nlinarith [sq_nonneg (6 * Real.exp 27 / ε)]
  have hlog : Real.log (⌈L ^ 2⌉₊ + 4 : ℕ) ≤ Real.log (L ^ 2 + 5) := by
    apply Real.log_le_log (by positivity)
    push_cast
    linarith [Nat.ceil_lt_add_one (sq_nonneg L)]
  have hly := hlog.trans (LeanLab.LPZ2007.log_sq_add_le L hL1)
  exact (boundary_product_le m q K hX hm hK).trans
    (LeanLab.LPZ2007.aux_third (Real.exp 27) ε L _ (Real.exp_pos 27) hε hscale hly)

/-- An explicit finite criterion combining all three contributions. -/
theorem lemma2_sum_le_of_parameters (m q K D : ℕ) {X δ : ℝ}
    (hX : 1 ≤ X) (hm : (m : ℝ) ≤ X) (hK : (K : ℝ) ≤ Real.logb 2 X)
    (hq : Odd q) (hq0 : 0 < q) (hD : 4 ≤ D) (hδ : 0 < δ)
    (hsmall : Real.exp 27 * Real.log D / LeanLab.LPZ2007.xi q ≤ δ)
    (htail : ∑' k, LeanLab.LPZ2007.seriesTerm (k + (D + 1)) ≤ δ)
    (hscale : (6 * Real.exp 27 / δ) ^ 2 + 1 ≤ Real.logb 2 X) :
    ∑ ν ∈ eligibleExponents m q K, Sing (m - 2 ^ ν) ≤
      6 * C0 * δ * Real.logb 2 X := by
  set L := Real.logb 2 X
  have hL0 : 0 ≤ L := Real.logb_nonneg (by norm_num) hX
  have h1 : L * (Real.exp 27 * Real.log D) / LeanLab.LPZ2007.xi q ≤ δ * L := by
    calc
      _ = (Real.exp 27 * Real.log D / LeanLab.LPZ2007.xi q) * L := by ring
      _ ≤ δ * L := mul_le_mul_of_nonneg_right hsmall hL0
  have h2 : L * ∑' k, LeanLab.LPZ2007.seriesTerm (k + (D + 1)) ≤ δ * L := by
    have h := mul_le_mul_of_nonneg_left htail hL0
    linarith
  have h3 := boundary_product_small m q K hX hm hK hδ hscale
  have hsum := lemma2_three_part_bound m q K D L hq hq0 hK hD
  have hC0 := Applications.C0_pos
  calc
    _ ≤ 2 * C0 * (L * (Real.exp 27 * Real.log D) / LeanLab.LPZ2007.xi q +
        L * ∑' k, LeanLab.LPZ2007.seriesTerm (k + (D + 1)) +
        LeanLab.LPZ2007.H (∏ ν ∈ eligibleExponents m q K, (m - 2 ^ ν))) := hsum
    _ ≤ 2 * C0 * (3 * δ * L) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    _ = _ := by ring

end LeanLab.Pintz2021.TranslatedTask53

#print axioms LeanLab.Pintz2021.TranslatedTask53.translated_count_le
#print axioms LeanLab.Pintz2021.TranslatedTask53.uniform_divisor_tail
#print axioms LeanLab.Pintz2021.TranslatedTask53.lemma2_three_part_bound
#print axioms LeanLab.Pintz2021.TranslatedTask53.boundary_product_le
#print axioms LeanLab.Pintz2021.TranslatedTask53.boundary_product_small
#print axioms LeanLab.Pintz2021.TranslatedTask53.lemma2_sum_le_of_parameters
#print axioms LeanLab.LPZ2007.card_nu_le
#print axioms LeanLab.LPZ2007.lemma61_proved
#print axioms LeanLab.LPZ2007.tail_le
#print axioms LeanLab.LPZ2007.sum_H_le
