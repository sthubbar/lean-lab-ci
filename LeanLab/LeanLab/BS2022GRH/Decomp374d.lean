/- AI wrote this Lean code for CODEX task374. Goldbach is open.
Separate the finite character cap and the two totient sums in journal display 13.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Decomp148a
import LeanLab.BS2022GRH.DecompC164b
import LeanLab.BS2022GRH.Totient374

namespace LeanLab.BS2022GRH.Decomp374d
open Real Finset Classical ChenThresholdGRH Decomp148a
noncomputable section

/-- The uniform character factor in display 13, journal p. 1224. -/
def smallFactor (Y D D₀ : ℝ) : ℝ :=
  1.3841 * log D / log (log D) + 2 * D₀ + 2 * D₀ * qG Y * √Y * log Y

/-- Universal scalar maximum used on Robin p. 381, below 0.37. -/
private theorem log_le_point37_mul (t : ℝ) (ht : 0 < t) : log t ≤ 0.37 * t := by
  have h := log_le_sub_one_of_pos (div_pos ht (exp_pos 1))
  rw [log_div ht.ne' (exp_pos 1).ne', log_exp] at h
  have he : (1 : ℝ) / exp 1 ≤ 0.37 := by
    apply (div_le_iff₀ (exp_pos 1)).mpr
    nlinarith [exp_one_gt_d9]
  have hm := mul_le_mul_of_nonneg_right he ht.le
  calc
    log t ≤ t / exp 1 := by linarith
    _ ≤ 0.37 * t := by simpa only [one_div, div_eq_mul_inv, one_mul, mul_comm] using hm

/-- Robin Theorem 11 through journal Lemma 4, uniformly in the cofactor. -/
private theorem omega_uniform (D : ℝ) (s : ℕ) (hD : 5 ≤ D) (hs : 1 ≤ s)
    (hsD : (s : ℝ) < D) :
    (s.primeFactors.card : ℝ) ≤ 1.3841 * log D / log (log D) := by
  have h4 : PaperInputs148.Lemma4J := PublishedInputs232.lemma4_robin
  have hlogD : 1 < log D := by
    rw [lt_log_iff_exp_lt (by linarith : 0 < D)]
    linarith [exp_one_lt_d9]
  have hllD : 0 < log (log D) := log_pos hlogD
  by_cases hs16 : 16 ≤ s
  · have hsR : (16 : ℝ) ≤ s := by exact_mod_cast hs16
    have hs0 : (0 : ℝ) < s := by linarith
    have h16 : exp 1 ≤ log (16 : ℝ) := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, log_pow]
      norm_num only [Nat.cast_ofNat]
      nlinarith only [Real.log_two_gt_d9, Real.exp_one_lt_d9]
    have hslog : exp 1 ≤ log (s : ℝ) := h16.trans (log_le_log (by norm_num) hsR)
    have hlogs : 0 < log (s : ℝ) := (exp_pos 1).trans_le hslog
    have hlls : 0 < log (log (s : ℝ)) := by
      apply log_pos
      linarith [exp_one_gt_d9]
    have hmono := log_div_self_antitoneOn hslog
      (hslog.trans (log_le_log hs0 hsD.le)) (log_le_log hs0 hsD.le)
    have hm : log (s : ℝ) / log (log (s : ℝ)) ≤ log D / log (log D) := by
      apply (div_le_div_iff₀ hlls hllD).mpr
      have hh := (div_le_div_iff₀ (by linarith : 0 < log D) hlogs).mp hmono
      nlinarith
    apply (h4 s (by omega)).le.trans
    simpa only [mul_div_assoc] using
      mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 1.3841)
  · have hfinite : ∀ m ∈ Icc 1 15, m.primeFactors.card ≤ 2 := by decide +kernel
    have hcard : (s.primeFactors.card : ℝ) ≤ 2 := by
      exact_mod_cast hfinite s (mem_Icc.mpr ⟨hs, by omega⟩)
    apply hcard.trans
    apply (le_div_iff₀ hllD).mpr
    have hl := log_le_point37_mul (log D) (by linarith)
    nlinarith

/-- Removing the prime divisors of the cofactor costs at most `ω s`, p. 1224. -/
private theorem prime_deletion (Y Z : ℝ) (s r : ℕ) (hs : 1 ≤ s)
    (χ : DirichletCharacter ℂ r) :
    ‖∑ p ∈ (pRange Y Z).filter (fun p => ¬ p ∣ s), χ p‖ ≤
      ‖∑ p ∈ pRange Y Z, χ p‖ + (s.primeFactors.card : ℝ) := by
  have hsub : (pRange Y Z).filter (fun p => p ∣ s) ⊆ s.primeFactors := by
    intro p hp
    obtain ⟨hp, hps⟩ := mem_filter.mp hp
    have hprime := (mem_filter.mp hp).2.1
    exact Nat.mem_primeFactors.mpr ⟨hprime, hps, by omega⟩
  have hnorm : ‖∑ p ∈ (pRange Y Z).filter (fun p => p ∣ s), χ p‖ ≤
      (s.primeFactors.card : ℝ) := by
    apply (norm_sum_le _ _).trans
    calc
      _ ≤ ∑ _p ∈ (pRange Y Z).filter (fun p => p ∣ s), (1 : ℝ) :=
        sum_le_sum (fun p _ => χ.norm_le_one _)
      _ = (((pRange Y Z).filter (fun p => p ∣ s)).card : ℝ) := by simp
      _ ≤ _ := Nat.cast_le.mpr (card_le_card hsub)
  have hsplit := sum_filter_add_sum_filter_not (pRange Y Z) (fun p => ¬ p ∣ s) (fun p => χ p)
  simp only [not_not] at hsplit
  rw [eq_sub_of_add_eq hsplit]
  exact (norm_sub_le _ _).trans (add_le_add le_rfl hnorm)

/-- The coefficient character sum is at most `X` for bounded coefficients. -/
private theorem coeff_l1 (c : ℕ → ℂ) (X : ℝ) (s r : ℕ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (χ : DirichletCharacter ℂ r) :
    ‖∑ n ∈ (nRange X).filter (fun n => Nat.Coprime n s), c n * χ n‖ ≤ X := by
  apply (norm_sum_le _ _).trans
  calc
    _ ≤ ∑ _n ∈ (nRange X).filter (fun n => Nat.Coprime n s), (1 : ℝ) := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul]
      exact mul_le_one₀ (hc n) (norm_nonneg _) (χ.norm_le_one _)
    _ = (((nRange X).filter (fun n => Nat.Coprime n s)).card : ℝ) := by simp
    _ ≤ ((nRange X).card : ℝ) := Nat.cast_le.mpr (card_filter_le _ _)
    _ ≤ X := by
      have hceil : 1 ≤ ⌈X⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
      simp only [nRange, Nat.card_Ico]
      rw [Nat.cast_sub hceil, Nat.cast_one]
      linarith [Nat.ceil_lt_add_one (show 0 ≤ X by linarith)]

/-- A primitive character of level at least three is nonprincipal. -/
private theorem prim_ne_one (r : ℕ) (hr : 3 ≤ r) (χ : DirichletCharacter ℂ r)
    (hχ : χ.IsPrimitive) : χ ≠ 1 := by
  letI : NeZero r := ⟨by omega⟩
  intro heq
  have hcon : χ.conductor = 1 := DirichletCharacter.eq_one_iff_conductor_eq_one.mp heq
  have hlev : χ.conductor = r := hχ
  omega

/-- LEAF. Journal p. 1224 before display 13, the single conductor and cofactor cap.
Use the prime character bound, the contribution of prime divisors of s,
and Robin Theorem 11 through journal Lemma 4. There is no outer modulus sum. -/
theorem primitive_term_cap (hG : GRH) (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (r s : ℕ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hY : 25 ≤ Y) (hZ : 25 ≤ Z)
    (hZY : Z < Y) (hD : 5 ≤ D) (hD₀ : 1 < D₀) (hD₀D : D₀ ≤ D)
    (hD₀Z : D₀ ≤ √Z) (hr : 3 ≤ r) (hrD : (r : ℝ) ≤ D₀)
    (hs : 1 ≤ s) (hsD : (s : ℝ) < D) :
    primitiveTerm c X Y Z r s ≤ D₀ * X * smallFactor Y D D₀ := by
  letI : NeZero r := ⟨by omega⟩
  have hq : 0 < qG Y := DecompC164b.qG_positive Y hY
  let B := 2 * D₀ * (1 + qG Y * √Y * log Y) + 1.3841 * log D / log (log D)
  have hB : 0 ≤ B := by
    have hlog : 1 < log D := by
      rw [lt_log_iff_exp_lt (by linarith : 0 < D)]
      linarith [exp_one_lt_d9]
    have hlog0 : 0 < log D := by linarith
    have hll : 0 < log (log D) := log_pos hlog
    have hylog : 0 ≤ log Y := log_nonneg (by linarith)
    have hE : 0 ≤ 1 + qG Y * √Y * log Y := by positivity
    have hD0 : (0 : ℝ) ≤ 2 * D₀ := by linarith
    have h1 : 0 ≤ 2 * D₀ * (1 + qG Y * √Y * log Y) := mul_nonneg hD0 hE
    have h2 : 0 ≤ 1.3841 * log D / log (log D) :=
      div_nonneg (mul_nonneg (by norm_num) hlog0.le) hll.le
    dsimp [B]
    linarith
  have hφ : (r.totient : ℝ) ≤ D₀ :=
    (Nat.cast_le.mpr (Nat.totient_le r)).trans hrD
  have he : 0 ≤ 1 + qG Y * √Y * log Y := by
    have hl := log_nonneg (show 1 ≤ Y by linarith)
    positivity
  have hsum : ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive →
      ‖∑ p ∈ (pRange Y Z).filter (fun p => ¬ p ∣ s), χ p‖ ≤ B := by
    intro χ hχ
    have hp := Decomp148b.prime_character_bound hG Y Z r hZ hZY hr
      (hrD.trans hD₀Z) χ (prim_ne_one r hr χ hχ)
    have ho := omega_uniform D s hD hs hsD
    have ht := prime_deletion Y Z s r hs χ
    have hm := mul_le_mul_of_nonneg_right hφ he
    dsimp [B]
    linarith
  have hcard : (((univ : Finset (DirichletCharacter ℂ r)).filter
      (fun χ => χ.IsPrimitive)).card : ℝ) ≤ D₀ := by
    have hc' := card_filter_le (univ : Finset (DirichletCharacter ℂ r)) (fun χ => χ.IsPrimitive)
    have hall : Fintype.card (DirichletCharacter ℂ r) = r.totient := by
      rw [← Nat.card_eq_fintype_card,
        DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ r]
    rw [card_univ, hall] at hc'
    exact (Nat.cast_le.mpr hc').trans hφ
  calc
    primitiveTerm c X Y Z r s ≤ ∑ _χ ∈
        (univ : Finset (DirichletCharacter ℂ r)).filter (fun χ => χ.IsPrimitive), X * B := by
      apply sum_le_sum
      intro χ hχ
      exact mul_le_mul (coeff_l1 c X s r hc hX χ)
        (hsum χ (mem_filter.mp hχ).2) (norm_nonneg _) (by linarith)
    _ = (((univ : Finset (DirichletCharacter ℂ r)).filter
        (fun χ => χ.IsPrimitive)).card : ℝ) * (X * B) := by simp
    _ ≤ D₀ * (X * B) := mul_le_mul_of_nonneg_right hcard (mul_nonneg (by linarith) hB)
    _ = _ := by dsimp [B, smallFactor]; ring

/-- LEAF. Journal p. 1224 display 13, the two reciprocal totient sums.
Apply Ramare Theorem 3.1 through journal Lemma 5 to the squarefree supports.
This estimate has no character, arbitrary coefficient sequence or GRH hypothesis. -/
theorem small_totient_mass (D D₀ : ℝ) (a : ℤ)
    (hD : 1 < D) (hD₀ : 1 < D₀) (hD₀D : D₀ ≤ D) :
    (∑ r ∈ (conductors D a).filter (fun r : ℕ => (r : ℝ) ≤ D₀),
      (r.totient : ℝ)⁻¹ * ∑ s ∈ moduli (D / r) a, (s.totient : ℝ)⁻¹) ≤
      Mphi D₀ * Mphi D * log D ^ 2 := by
  exact Totient374.small_totient_mass_of_phi PublishedInputs232.lemma5_phi D D₀ a hD hD₀ hD₀D

/-- The balance assumptions force D at least five, journal p. 1224. -/
theorem five_le_level (X Y D D₀ : ℝ) (hX : 25 ≤ X) (hY : 25 ≤ Y)
    (hD : 1 < D) (hD₀D : D₀ ≤ D) (hbal : √(X * Y) / D ≤ D₀) : 5 ≤ D := by
  have hs : (25 : ℝ) ≤ √(X * Y) := by
    have hxy : 25 ^ 2 ≤ X * Y := by nlinarith
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr hxy
  have hm := (div_le_iff₀ (by linarith : 0 < D)).mp hbal
  have hmul := mul_le_mul_of_nonneg_right hD₀D (by linarith : 0 ≤ D)
  nlinarith

/-- The common cap is nonnegative on the source domain, journal display 13. -/
theorem smallFactor_nonneg (Y D D₀ : ℝ) (hY : 25 ≤ Y) (hD : 5 ≤ D)
    (hD₀ : 1 < D₀) : 0 ≤ smallFactor Y D D₀ := by
  have hlog : 1 ≤ log D := by
    rw [le_log_iff_exp_le (by linarith : 0 < D)]
    linarith [exp_one_lt_d9]
  have hq := DecompC164b.qG_positive Y hY
  have hylog : 0 ≤ log Y := log_nonneg (by linarith)
  have hll : 0 ≤ log (log D) := log_nonneg hlog
  unfold smallFactor
  positivity

/-- Exact statement of Decomp148b.small_conductors from the local cap and totient mass.
CONDITIONAL ON primitive_term_cap and small_totient_mass. No direct sorry. -/
theorem small_conductors (hG : GRH) (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (a : ℤ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hY : 25 ≤ Y) (hZ : 25 ≤ Z)
    (hZY : Z < Y) (hD : 1 < D) (hD₀ : 1 < D₀) (hD₀D : D₀ ≤ D)
    (hD₀Z : D₀ ≤ √Z) (hbal : √(X * Y) / D ≤ D₀) (ha : Even a) :
    smallMass c X Y Z D D₀ a ≤ smallBound X Y D D₀ := by
  have hD5 := five_le_level X Y D D₀ hX hY hD hD₀D hbal
  have hfac := smallFactor_nonneg Y D D₀ hY hD5 hD₀
  let B : ℝ := D₀ * X * smallFactor Y D D₀
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hsum : smallMass c X Y Z D D₀ a ≤
      (∑ r ∈ (conductors D a).filter (fun r : ℕ => (r : ℝ) ≤ D₀),
        (r.totient : ℝ)⁻¹ * ∑ s ∈ moduli (D / r) a, (s.totient : ℝ)⁻¹) * B := by
    unfold smallMass
    rw [sum_mul]
    apply sum_le_sum
    intro r hr
    obtain ⟨hrmem, hrD⟩ := mem_filter.mp hr
    have hr3 : 3 ≤ r := (mem_Ico.mp (mem_filter.mp hrmem).1).1
    unfold conductorTerm
    rw [mul_assoc, sum_mul]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply sum_le_sum
    intro s hs
    have hs1 : 1 ≤ s := (mem_Ico.mp (mem_filter.mp hs).1).1
    have hsquot : (s : ℝ) < D / r := Nat.lt_ceil.mp (mem_Ico.mp (mem_filter.mp hs).1).2
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast (show 1 ≤ r by omega)
    have hsD : (s : ℝ) < D := hsquot.trans_le
      (div_le_self (by linarith : 0 ≤ D) hr1)
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact primitive_term_cap hG c X Y Z D D₀ r s hc hX hY hZ hZY hD5 hD₀ hD₀D
      hD₀Z hr3 hrD hs1 hsD
  apply hsum.trans
  have hw := mul_le_mul_of_nonneg_right (small_totient_mass D D₀ a hD hD₀ hD₀D) hB
  convert hw using 1 <;> dsimp [B, smallFactor, smallBound] <;> ring

end
end LeanLab.BS2022GRH.Decomp374d

#print axioms LeanLab.BS2022GRH.Decomp374d.primitive_term_cap
#print axioms LeanLab.BS2022GRH.Decomp374d.small_totient_mass
#print axioms LeanLab.BS2022GRH.Decomp374d.five_le_level
#print axioms LeanLab.BS2022GRH.Decomp374d.smallFactor_nonneg
#print axioms LeanLab.BS2022GRH.Decomp374d.small_conductors
