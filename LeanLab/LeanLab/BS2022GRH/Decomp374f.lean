/- AI wrote this Lean code for CODEX task374. Goldbach is open.
Separate the dyadic sum for one cofactor from the outer totient sum in display 16.
https://doi.org/10.1007/s11139-024-00866-x -/
import LeanLab.BS2022GRH.Decomp374a
import LeanLab.BS2022GRH.PublishedInputs232

namespace LeanLab.BS2022GRH.Decomp374f
open Real Finset Classical ChenThresholdGRH Decomp148a
noncomputable section

/-- The per block scalar bound on the last line of display 15, journal p. 1225. -/
def largeFactor (X Y D D₀ : ℝ) : ℝ :=
  4 * D * √(X * Y) + 2 * (√X + √Y) * √(X * Y) + X * Y / D₀

/-- LEAF. Journal pp. 1225 and 1226, dyadic counting from display 15 to display 16.
For one fixed cofactor sum the conductor blocks, with no outer cofactor sum.
The hypothesis supplies the two moment assembly separately. -/
theorem dyadic_conductor_slice (c : ℕ → ℂ) (X Y Z D D₀ : ℝ) (a : ℤ) (s : ℕ)
    (hc : ∀ n, ‖c n‖ ≤ 1) (hX : 25 ≤ X) (hY : 25 ≤ Y) (hZ : 25 ≤ Z)
    (hZY : Z < Y) (hD : 1 < D) (hDX : D < √(X * Y))
    (hD₀ : 1 < D₀) (hD₀D : D₀ ≤ D) (hbal : √(X * Y) / D ≤ D₀)
    (hblock : ∀ R : ℝ, 1 ≤ R →
      (∑ r ∈ Decomp374a.blockModuli R,
        (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s) ≤
        √((X + 4 * R ^ 2) * (Y + 4 * R ^ 2) * X * Y) / R) :
    (∑ r ∈ (conductors D a).filter (fun r : ℕ => D₀ < (r : ℝ)),
      (r.totient : ℝ)⁻¹ * primitiveTerm c X Y Z r s) ≤
      log D / log 2 * largeFactor X Y D D₀ := by
  sorry

/-- Enlarge a cofactor range to the full squarefree support, journal display 16. -/
theorem cofactor_subset (D : ℝ) (a : ℤ) (r : ℕ) (hD : 0 ≤ D) (hr : 1 ≤ r) :
    moduli (D / r) a ⊆ moduli D a := by
  intro s hs
  obtain ⟨hsI, hsQ⟩ := mem_filter.mp hs
  obtain ⟨hs1, hsU⟩ := mem_Ico.mp hsI
  apply mem_filter.mpr
  refine ⟨mem_Ico.mpr ⟨hs1, ?_⟩, hsQ⟩
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hslt : (s : ℝ) < D / r := Nat.lt_ceil.mp hsU
  exact Nat.lt_ceil.mpr (hslt.trans_le (div_le_self hD hrR))

/-- The outer squarefree cofactor weight is the existing Lemma 5 input, display 16.
CONDITIONAL ON PublishedInputs232.lemma5_phi. -/
theorem cofactor_totient_sum (D : ℝ) (a : ℤ) (hD : 1 < D) :
    (∑ s ∈ moduli D a, (s.totient : ℝ)⁻¹) ≤ Mphi D * log D := by
  have hsub : moduli D a ⊆ (Icc 1 ⌊D⌋₊).filter (fun s => Squarefree s) := by
    intro s hs
    obtain ⟨hsI, hsQ⟩ := mem_filter.mp hs
    obtain ⟨hs1, hsU⟩ := mem_Ico.mp hsI
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨hs1, Nat.le_floor (Nat.lt_ceil.mp hsU).le⟩, hsQ.1⟩
  have h := sum_le_sum_of_subset_of_nonneg hsub
    (fun s _ _ => by positivity : ∀ s ∈ (Icc 1 ⌊D⌋₊).filter (fun s => Squarefree s),
      s ∉ moduli D a → 0 ≤ (s.totient : ℝ)⁻¹)
  exact h.trans (by simpa only [one_div] using PublishedInputs232.lemma5_phi D hD)

/-- Exact statement of Decomp148c.large_conductors with the outer sum proved.
CONDITIONAL ON the dyadic conductor slice, the two moments and the existing Lemma 5 input. -/
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
    apply dyadic_conductor_slice c X Y Z D D₀ a s hc hX hY hZ hZY hD hDX hD₀ hD₀D hbal
    intro R hR
    exact Decomp374a.dyadic_block c X Y Z R s hc hX hY hZ hZY hR
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

end
end LeanLab.BS2022GRH.Decomp374f

#print axioms LeanLab.BS2022GRH.Decomp374f.dyadic_conductor_slice
#print axioms LeanLab.BS2022GRH.Decomp374f.cofactor_subset
#print axioms LeanLab.BS2022GRH.Decomp374f.cofactor_totient_sum
#print axioms LeanLab.BS2022GRH.Decomp374f.large_conductors
