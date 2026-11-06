/- AI wrote this Lean code for CODEX task406. Goldbach is open.
Acyclic assemblies for journal displays 13 through 18 and Lemma 8.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Decomp406a
import LeanLab.BS2022GRH.Decomp406b
import LeanLab.BS2022GRH.Decomp406d
import LeanLab.BS2022GRH.Decomp148d

namespace LeanLab.BS2022GRH.Decomp406e
open Real Finset Classical ChenThresholdGRH Decomp148a Decomp374d Decomp374f Decomp148d
noncomputable section

/-- Exact small conductor statement, journal p. 1224 display 13.
CONDITIONAL ON the prime character estimate, the new Robin leaves and Lemma 5.
The finite cap is supplied by Decomp406d rather than the original placeholder. -/
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
    exact Decomp406d.primitive_term_cap hG c X Y Z D D₀ r s hc hX hY hZ hZY hD5 hD₀ hD₀D
      hD₀Z hr3 hrD hs1 hsD
  apply hsum.trans
  have hw := mul_le_mul_of_nonneg_right (small_totient_mass D D₀ a hD hD₀ hD₀D) hB
  convert hw using 1 <;> dsimp [B, smallFactor, smallBound] <;> ring


/-- Exact large conductor statement, journal p. 1226 display 16.
CONDITIONAL ON the existing reciprocal totient input of Lemma 5.
The block moments and finite dyadic summation use the new proved bridges. -/
theorem large_conductors (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (a : ℤ)
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
      mul_le_mul_of_nonneg_right (cofactor_totient_sum D a hD) hK
    _ = largeBound X Y D D₀ := by dsimp [K, largeFactor, largeBound]; ring


/-- Exact Lemma8J statement, journal p. 1226 displays 17 and 18.
CONDITIONAL ON the explicit progression, scalar envelope, Robin and totient inputs.
Neither original small conductor nor original large conductor placeholder is used. -/
theorem lemma8J : Lemma8J := by
  intro hG c X Y Z D a hc hX hY hZ hZY hD hDX hbal hcutD ha
  have hcut := cutoff_gt_one X Y D hD hDX hbal
  have hs := (small_conductors hG c X Y Z D (cutoff Y) a hc hX hY hZ hZY hD hcut
    (hcutD.trans (min_le_left _ _)) (hcutD.trans (min_le_right _ _)) hbal ha).trans
    (small_normalized X Y D hX hY hD hDX hbal (hcutD.trans (min_le_left _ _)))
  have hl := (large_conductors c X Y Z D (cutoff Y) a hc hX hY hZ hZY hD hDX hcut
    (hcutD.trans (min_le_left _ _)) hbal ha).trans
    (large_normalized X Y D hX hY hD hDX hbal (hcutD.trans (min_le_left _ _)))
  calc bilinear c X Y Z D a
      ≤ smallMass c X Y Z D (cutoff Y) a + largeMass c X Y Z D (cutoff Y) a :=
        split_reduction c X Y Z D (cutoff Y) a hD ha
    _ ≤ smallCoeff X Y D * scale X Y D + largeCoeff X Y D * scale X Y D := add_le_add hs hl
    _ = mJ X Y D * scale X Y D := by rw [mJ, add_mul]

end
end LeanLab.BS2022GRH.Decomp406e

#print axioms LeanLab.BS2022GRH.Decomp406e.small_conductors
#print axioms LeanLab.BS2022GRH.Decomp406e.large_conductors
#print axioms LeanLab.BS2022GRH.Decomp406e.lemma8J
