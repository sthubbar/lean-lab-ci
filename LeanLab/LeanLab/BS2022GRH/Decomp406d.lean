/- AI wrote this Lean code for CODEX task406. Goldbach is open.
Finite character and prime deletion steps on journal p. 1224 before display 13.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Decomp374b
import LeanLab.BS2022GRH.Decomp374d
import LeanLab.BS2022GRH.Decomp406c

namespace LeanLab.BS2022GRH.Decomp406d
open Real Finset Classical ChenThresholdGRH Decomp148a Decomp374d
noncomputable section

/-- LEAF. Journal p. 1224 before display 13, uniform application of Lemma 4.
The input is Robin Theorem 11, pp. 380 and 381. Treat the small cofactor cases
separately before using monotonicity of log x over log log x above sixteen.
This scalar transfer has no characters or GRH assumption. -/
theorem uniform_omega_bound (h4 : PaperInputs148.Lemma4J) (D : ℝ) (s : ℕ)
    (hD : 5 ≤ D) (hs : 1 ≤ s) (hsD : (s : ℝ) < D) :
    (s.primeFactors.card : ℝ) ≤ 1.3841 * log D / log (log D) := by
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
    simpa only [mul_div_assoc] using mul_le_mul_of_nonneg_left hm (by norm_num : (0 : ℝ) ≤ 1.3841)
  · have hfinite : ∀ m ∈ Icc 1 15, m.primeFactors.card ≤ 2 := by decide +kernel
    have hcard : (s.primeFactors.card : ℝ) ≤ 2 := by
      exact_mod_cast hfinite s (mem_Icc.mpr ⟨hs, by omega⟩)
    apply hcard.trans
    apply (le_div_iff₀ hllD).mpr
    have hl := Decomp406c.log_le_point37_mul (log D) (by linarith)
    nlinarith

/-- Removing prime divisors of a positive cofactor costs at most omega s, p. 1224. -/
theorem prime_deletion (Y Z : ℝ) (s r : ℕ) (hs : 1 ≤ s)
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

/-- The coefficient character sum is at most X for bounded coefficients, p. 1224. -/
theorem coefficient_l1 (c : ℕ → ℂ) (X : ℝ) (s r : ℕ)
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

/-- Primitive characters at level at least three are nonprincipal, p. 1224. -/
theorem primitive_ne_one (r : ℕ) (hr : 3 ≤ r) (χ : DirichletCharacter ℂ r)
    (hχ : χ.IsPrimitive) : χ ≠ 1 := by
  letI : NeZero r := ⟨by omega⟩
  intro heq
  have hcon : χ.conductor = 1 := DirichletCharacter.eq_one_iff_conductor_eq_one.mp heq
  have hlev : χ.conductor = r := hχ
  omega

/-- Exact statement of Decomp374d.primitive_term_cap from the smaller scalar transfer.
CONDITIONAL ON uniform_omega_bound, the Robin input and the prime character estimate. -/
theorem primitive_term_cap (hG : GRH) (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (r s : ℕ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hY : 25 ≤ Y) (hZ : 25 ≤ Z)
    (hZY : Z < Y) (hD : 5 ≤ D) (hD₀ : 1 < D₀) (hD₀D : D₀ ≤ D)
    (hD₀Z : D₀ ≤ √Z) (hr : 3 ≤ r) (hrD : (r : ℝ) ≤ D₀)
    (hs : 1 ≤ s) (hsD : (s : ℝ) < D) :
    primitiveTerm c X Y Z r s ≤ D₀ * X * smallFactor Y D D₀ := by
  letI : NeZero r := ⟨by omega⟩
  let B := 2 * D₀ * (1 + qG Y * √Y * log Y) +
    1.3841 * log D / log (log D)
  have hfac := Decomp374d.smallFactor_nonneg Y D D₀ hY hD hD₀
  have hB : 0 ≤ B := by
    change 0 ≤ B
    convert hfac using 1 <;> dsimp [B, Decomp374d.smallFactor] <;> ring
  have hφ : (r.totient : ℝ) ≤ D₀ :=
    (Nat.cast_le.mpr (Nat.totient_le r)).trans hrD
  have hq := DecompC164b.qG_positive Y hY
  have he : 0 ≤ 1 + qG Y * √Y * log Y := by
    have hl := log_nonneg (show 1 ≤ Y by linarith)
    positivity
  have hsum : ∀ χ : DirichletCharacter ℂ r, χ.IsPrimitive →
      ‖∑ p ∈ (pRange Y Z).filter (fun p => ¬ p ∣ s), χ p‖ ≤ B := by
    intro χ hχ
    have hp := Decomp374b.prime_character_bound hG Y Z r hZ hZY hr
      (hrD.trans hD₀Z) χ (primitive_ne_one r hr χ hχ)
    have ho := uniform_omega_bound Decomp406c.lemma4_robin D s hD hs hsD
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
      exact mul_le_mul (coefficient_l1 c X s r hc hX χ)
        (hsum χ (mem_filter.mp hχ).2) (norm_nonneg _) (by linarith)
    _ = (((univ : Finset (DirichletCharacter ℂ r)).filter
        (fun χ => χ.IsPrimitive)).card : ℝ) * (X * B) := by simp
    _ ≤ D₀ * (X * B) := mul_le_mul_of_nonneg_right hcard (mul_nonneg (by linarith) hB)
    _ = _ := by dsimp [B, Decomp374d.smallFactor]; ring

end
end LeanLab.BS2022GRH.Decomp406d

#print axioms LeanLab.BS2022GRH.Decomp406d.uniform_omega_bound
#print axioms LeanLab.BS2022GRH.Decomp406d.prime_deletion
#print axioms LeanLab.BS2022GRH.Decomp406d.coefficient_l1
#print axioms LeanLab.BS2022GRH.Decomp406d.primitive_ne_one
#print axioms LeanLab.BS2022GRH.Decomp406d.primitive_term_cap
