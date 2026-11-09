/- AI wrote the Lean code for CODEX task332. Goldbach is open.
Use the caller's Lemma 3 throughout the bilinear proof without an independent progression leaf.
Journal p. 1224 display 13 and p. 1226 displays 16 to 18.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Decomp406e

namespace LeanLab.BS2022GRH.CharacterInputs332
open Real Finset Classical ChenThresholdGRH Decomp148a Decomp374d Decomp374f Decomp148d Decomp406d
noncomputable section

/-- The supplied Lemma 3 bounds a single prime prefix after reduced residue cancellation.
Journal p. 1224 before display 13. CONDITIONAL ON h3 and GRH. -/
theorem prefix_bound (h3 : Lemma3J) (hG : GRH) (x : ℝ) (r : ℕ)
    (hx : 25 ≤ x) (hr : 3 ≤ r) (hrx : (r : ℝ) ≤ √x)
    (χ : DirichletCharacter ℂ r) (hχ : χ ≠ 1) :
    ‖Decomp374b.primePrefix x χ‖ ≤ r.totient * (qG x * √x * log x) := by
  apply Prefix374.norm_sum_of_residue_errors _ r (by omega) χ hχ
  intro a ha
  have har : a % r = a := Nat.mod_eq_of_lt (mem_range.mp (mem_filter.mp ha).1)
  have hp := h3 hG r a x x hr hrx le_rfl (mem_filter.mp ha).2
  simpa only [filter_filter, har] using hp

/-- The supplied Lemma 3 bounds the full prime interval with both boundary corrections.
Journal p. 1224 before display 13. CONDITIONAL ON h3 and GRH. -/
theorem prime_character_bound (h3 : Lemma3J) (hG : GRH) (Y Z : ℝ) (r : ℕ)
    (hZ : 25 ≤ Z) (hZY : Z < Y) (hr : 3 ≤ r) (hrZ : (r : ℝ) ≤ √Z)
    (χ : DirichletCharacter ℂ r) (hχ : χ ≠ 1) :
    ‖∑ p ∈ pRange Y Z, χ p‖ ≤ 2 * r.totient * (1 + qG Y * √Y * log Y) := by
  have hy : 25 ≤ Y := hZ.trans hZY.le
  have hY := prefix_bound h3 hG Y r hy hr (hrZ.trans (sqrt_le_sqrt hZY.le)) χ hχ
  have hZ' := prefix_bound h3 hG Z r hZ hr hrZ χ hχ
  have hm := Decomp374b.error_envelope_mono Y Z hZ hZY
  have he := Decomp374b.interval_boundary Y Z r hZ hZY χ
  have ht := norm_sub_le (Decomp374b.primePrefix Y χ) (Decomp374b.primePrefix Z χ)
  have hi := norm_add_le
    ((∑ p ∈ pRange Y Z, χ p) - (Decomp374b.primePrefix Y χ - Decomp374b.primePrefix Z χ))
    (Decomp374b.primePrefix Y χ - Decomp374b.primePrefix Z χ)
  rw [sub_add_cancel] at hi
  have hφ : (1 : ℝ) ≤ r.totient := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < r)
  have hm' := mul_le_mul_of_nonneg_left hm (by positivity : (0 : ℝ) ≤ r.totient)
  calc
    _ ≤ 2 + r.totient * (qG Y * √Y * log Y) +
        r.totient * (qG Z * √Z * log Z) := by linarith
    _ ≤ 2 * r.totient * (1 + qG Y * √Y * log Y) := by nlinarith

/-- The single conductor cap uses only the explicit Lemma 3 and Robin inputs.
Journal p. 1224 display 13. CONDITIONAL ON h3, h4 and GRH. -/
theorem primitive_term_cap (h3 : Lemma3J) (h4 : PaperInputs148.Lemma4J) (hG : GRH) (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (r s : ℕ)
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
    have hp := prime_character_bound h3 hG Y Z r hZ hZY hr
      (hrD.trans hD₀Z) χ (primitive_ne_one r hr χ hχ)
    have ho := uniform_omega_bound h4 D s hD hs hsD
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

/-- The small conductor sum uses only explicit Lemmas 3, 4 and 5.
Journal p. 1224 display 13. CONDITIONAL ON h3, h4, hPhi and GRH. -/
theorem small_conductors (h3 : Lemma3J) (h4 : PaperInputs148.Lemma4J)
    (hPhi : PaperInputs148.Lemma5PhiJ) (hG : GRH) (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (a : ℤ)
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
    exact primitive_term_cap h3 h4 hG c X Y Z D D₀ r s hc hX hY hZ hZY hD5 hD₀ hD₀D
      hD₀Z hr3 hrD hs1 hsD
  apply hsum.trans
  have hw := mul_le_mul_of_nonneg_right (Totient374.small_totient_mass_of_phi hPhi D D₀ a hD hD₀ hD₀D) hB
  convert hw using 1 <;> dsimp [B, smallFactor, smallBound] <;> ring

/-- The cofactor totient sum uses only the explicit reciprocal totient input.
Journal p. 1226 display 16. CONDITIONAL ON hPhi. -/
theorem cofactor_totient_sum (hPhi : PaperInputs148.Lemma5PhiJ) (D : ℝ) (a : ℤ) (hD : 1 < D) :
    (∑ s ∈ moduli D a, (s.totient : ℝ)⁻¹) ≤ Mphi D * log D := by
  have hsub : moduli D a ⊆ (Icc 1 ⌊D⌋₊).filter (fun s => Squarefree s) := by
    intro s hs
    obtain ⟨hsI, hsQ⟩ := mem_filter.mp hs
    obtain ⟨hs1, hsU⟩ := mem_Ico.mp hsI
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hs1, Nat.le_floor (Nat.lt_ceil.mp hsU).le⟩, hsQ.1⟩
  have h := sum_le_sum_of_subset_of_nonneg hsub
    (fun s _ _ => by positivity : ∀ s ∈ (Icc 1 ⌊D⌋₊).filter (fun s => Squarefree s),
      s ∉ moduli D a → 0 ≤ (s.totient : ℝ)⁻¹)
  exact h.trans (by simpa only [one_div] using hPhi D hD)

/-- The sharp large conductor estimate uses only the explicit reciprocal totient input.
Journal p. 1226 display 16. CONDITIONAL ON hPhi. -/
theorem large_conductors (hPhi : PaperInputs148.Lemma5PhiJ) (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (a : ℤ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hY : 25 ≤ Y) (hZ : 25 ≤ Z)
    (hZY : Z < Y) (hD : 1 < D) (hDX : D < √(X * Y))
    (hD₀ : 1 < D₀) (hD₀D : D₀ ≤ D) (hbal : √(X * Y) / D ≤ D₀) (ha : Even a) :
    largeMass c X Y Z D D₀ a ≤ largeBound X Y D D₀ := by
  let T := (conductors D a).filter (fun r : ℕ => D₀ < (r : ℝ))
  let K := log D / log 2 * largeFactor X Y D D₀
  have hK : 0 ≤ K := by
    have hlog := (log_pos hD).le
    dsimp [K, largeFactor]
    positivity
  have hp (r s : ℕ) : 0 ≤ primitiveTerm c X Y Z r s := by
    unfold primitiveTerm
    exact sum_nonneg (fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hinner (r : ℕ) (hr : r ∈ T) :
      (∑ s ∈ moduli (D / r) a, (s.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s) ≤
      ∑ s ∈ moduli D a, (s.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s := by
    have hr3 : 3 ≤ r := (mem_Ico.mp (mem_filter.mp (mem_filter.mp hr).1).1).1
    exact sum_le_sum_of_subset_of_nonneg (cofactor_subset D a r (by linarith) (by omega))
      (fun s _ _ => mul_nonneg (by positivity) (hp r s))
  have hslices (s : ℕ) : (∑ r ∈ T,
      (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s) ≤ K := by
    apply Decomp406b.dyadic_conductor_slice c X Y Z D D₀ a s hc hX hY hZ hZY hD hDX hD₀ hD₀D hbal
    intro R hR
    exact Decomp406a.dyadic_block c X Y Z R s hc hX hY hZ hZY hR
  calc
    largeMass c X Y Z D D₀ a ≤ ∑ r ∈ T, (r.totient : ℝ)⁻¹ *
        ∑ s ∈ moduli D a, (s.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s := by
      exact sum_le_sum (fun r hr => mul_le_mul_of_nonneg_left (hinner r hr) (by positivity))
    _ = ∑ s ∈ moduli D a, (s.totient : ℝ)⁻¹ *
        ∑ r ∈ T, (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s := by
      simp_rw [mul_sum]
      rw [sum_comm]
      apply sum_congr rfl
      intro s hs
      apply sum_congr rfl
      intro r hr
      ring
    _ ≤ ∑ s ∈ moduli D a, (s.totient : ℝ)⁻¹ * K :=
      sum_le_sum (fun s _ => mul_le_mul_of_nonneg_left (hslices s) (by positivity))
    _ = (∑ s ∈ moduli D a, (s.totient : ℝ)⁻¹) * K := by rw [sum_mul]
    _ ≤ (Mphi D * log D) * K :=
      mul_le_mul_of_nonneg_right (cofactor_totient_sum hPhi D a hD) hK
    _ = largeBound X Y D D₀ := by dsimp [K, largeFactor, largeBound]; ring

/-- Lemma 8 follows from the explicit Lemma 3, Robin and reciprocal totient inputs.
Journal p. 1226 displays 17 and 18. CONDITIONAL ON h3, h4 and hPhi.
No original prime character or progression placeholder is invoked. -/
theorem lemma8_of_inputs (h3 : Lemma3J) (h4 : PaperInputs148.Lemma4J)
    (hPhi : PaperInputs148.Lemma5PhiJ) : Lemma8J := by
  intro hG c X Y Z D a hc hX hY hZ hZY hD hDX hbal hcutD ha
  have hcut := cutoff_gt_one X Y D hD hDX hbal
  have hs := (small_conductors h3 h4 hPhi hG c X Y Z D (cutoff Y) a hc hX hY hZ hZY hD hcut
    (hcutD.trans (min_le_left _ _)) (hcutD.trans (min_le_right _ _)) hbal ha).trans
    (small_normalized X Y D hX hY hD hDX hbal (hcutD.trans (min_le_left _ _)))
  have hl := (large_conductors hPhi c X Y Z D (cutoff Y) a hc hX hY hZ hZY hD hDX hcut
    (hcutD.trans (min_le_left _ _)) hbal ha).trans
    (large_normalized X Y D hX hY hD hDX hbal (hcutD.trans (min_le_left _ _)))
  calc bilinear c X Y Z D a
      ≤ smallMass c X Y Z D (cutoff Y) a + largeMass c X Y Z D (cutoff Y) a :=
        split_reduction c X Y Z D (cutoff Y) a hD ha
    _ ≤ smallCoeff X Y D * scale X Y D + largeCoeff X Y D * scale X Y D := add_le_add hs hl
    _ = mJ X Y D * scale X Y D := by rw [mJ, add_mul]

end
end LeanLab.BS2022GRH.CharacterInputs332
#print axioms LeanLab.BS2022GRH.CharacterInputs332.prefix_bound
#print axioms LeanLab.BS2022GRH.CharacterInputs332.prime_character_bound
#print axioms LeanLab.BS2022GRH.CharacterInputs332.primitive_term_cap
#print axioms LeanLab.BS2022GRH.CharacterInputs332.small_conductors
#print axioms LeanLab.BS2022GRH.CharacterInputs332.cofactor_totient_sum
#print axioms LeanLab.BS2022GRH.CharacterInputs332.large_conductors
#print axioms LeanLab.BS2022GRH.CharacterInputs332.lemma8_of_inputs
