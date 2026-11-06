/-
Shared corollary assembly from the analytic OPEN leaves.
AI wrote this Lean code. Goldbach is open.
-/
import LeanLab.LZPowersOfTwo.Decomp293e
import LeanLab.LZPowersOfTwo.Decomp418e

open Real Finset MeasureTheory Filter

noncomputable section
namespace LeanLab.LZPowersOfTwo

/-- P0079 page 3, corollary proof, ordered case. CONDITIONAL ON the three
smaller analytic inputs. Rescaling changes the existential threshold, not the solution set. -/
theorem ordered_large_s418 (ν l1 l2 : ℝ) (μ : ℕ → ℝ)
    (hn : l1 / l2 < 0) (hr : 1 ≤ |l1 / l2|) (hi : Irrational (l1 / l2))
    (hc : (ν = nuTr ∧ IsTr (l1 / l2)) ∨ (ν = nuAlg ∧ IsAlg (l1 / l2)))
    (hμ : ∀ i, μ i ≠ 0) (r1 r2 : ℚ)
    (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1)
    (η : ℝ) (hη : 0 < η) (hη1 : η < |l1 / r1.num|) (hη2 : η < |l2 / r2.num|) :
    ∃ S0 : ℕ, ∀ s : ℕ, 2 ≤ s → S0 ≤ s → ∀ γ : ℝ,
      (Sol l1 l2 (fun i : Fin s => μ i) γ η).Infinite := by
  obtain ⟨t, ht, h1, h2, hratio⟩ := exists_scale293 l1 l2 hn
  have hrat1 : (r1 : ℝ) = (t * l1) / (t * μ 0) := by
    rw [mul_div_mul_left _ _ ht]
    exact hr1
  have hrat2 : (r2 : ℝ) = (t * l2) / (t * μ 1) := by
    rw [mul_div_mul_left _ _ ht]
    exact hr2
  have hc' : (ν = nuTr ∧ IsTr ((t * l1) / (t * l2))) ∨
      (ν = nuAlg ∧ IsAlg ((t * l1) / (t * l2))) := by simpa [hratio] using hc
  have hlat1 : |t| * η < |(t * l1) / r1.num| := by
    rw [mul_div_assoc, abs_mul]
    exact mul_lt_mul_of_pos_left hη1 (abs_pos.mpr ht)
  have hlat2 : |t| * η < |(t * l2) / r2.num| := by
    rw [mul_div_assoc, abs_mul]
    exact mul_lt_mul_of_pos_left hη2 (abs_pos.mpr ht)
  obtain ⟨S0, H⟩ := normalized_large_s418 ν (t * l1) (t * l2) (fun i => t * μ i)
    h1 h2 (by simpa [hratio] using hr) (by simpa [hratio] using hi) hc'
    (fun i => mul_ne_zero ht (hμ i)) r1 r2 hrat1 hrat2 (|t| * η)
    (mul_pos (abs_pos.mpr ht) hη) hlat1 hlat2
  refine ⟨S0, fun s hs hS γ => ?_⟩
  have hsol := H s hs hS (t * γ)
  rwa [sol_scale ht] at hsol

/-- P0079 page 3, corollary proof. CONDITIONAL ON the three smaller analytic inputs.
The two coefficient kinds share all changes of variables and the existential threshold argument. -/
theorem corollary_cases418 (ν : ℝ) (kind : ℝ → Prop)
    (hk : ∀ x : ℝ, kind x → (ν = nuTr ∧ IsTr x) ∨ (ν = nuAlg ∧ IsAlg x)) :
    CorollaryStatement ν kind := by
  intro l1 l2 μ hn hi hc hμ r1 r2 hr1 hr2
  refine ⟨1, by norm_num, fun η hη _ hη1 hη2 => ?_⟩
  by_cases hr : 1 ≤ |l1 / l2|
  · obtain ⟨S0, H⟩ := ordered_large_s418 ν l1 l2 μ hn hr hi (hk _ hc) hμ r1 r2 hr1 hr2
      η hη hη1 hη2
    exact ⟨S0, fun τ hτ γ s hs hS => sol_infinite_mono hτ (H s hs hS γ)⟩
  · have h1 : l1 ≠ 0 := by intro h; simp [h] at hn
    have h2 : l2 ≠ 0 := by intro h; simp [h] at hn
    have hneg : l2 / l1 < 0 := by simpa only [inv_div] using inv_lt_zero.mpr hn
    have hratio : 1 ≤ |l2 / l1| := by
      have hsmall : |l1 / l2| < 1 := lt_of_not_ge hr
      rw [abs_div] at hsmall ⊢
      exact (one_le_div (abs_pos.mpr h1)).mpr ((div_lt_one (abs_pos.mpr h2)).mp hsmall).le
    have hirr : Irrational (l2 / l1) := by simpa only [inv_div] using hi.inv
    have hkind : (ν = nuTr ∧ IsTr (l2 / l1)) ∨ (ν = nuAlg ∧ IsAlg (l2 / l1)) := by
      rcases hk _ hc with ⟨hv, hx⟩ | ⟨hv, hx⟩
      · left
        refine ⟨hv, ?_⟩
        change Transcendental ℚ (l2 / l1)
        rw [← inv_div]
        exact fun ha => hx (IsAlgebraic.inv_iff.mp ha)
      · right
        refine ⟨hv, ?_⟩
        change IsAlgebraic ℚ (l2 / l1)
        simpa only [inv_div] using hx.inv
    let μ' : ℕ → ℝ := fun i => μ (Equiv.swap 0 1 i)
    have hm0 : μ' 0 = μ 1 := by simp [μ']
    have hm1 : μ' 1 = μ 0 := by simp [μ']
    obtain ⟨S0, H⟩ := ordered_large_s418 ν l2 l1 μ' hneg hratio hirr hkind
      (fun i => hμ _) r2 r1 (by simpa [hm0] using hr2) (by simpa [hm1] using hr1)
      η hη hη2 hη1
    refine ⟨S0, fun τ hτ γ s hs hS => ?_⟩
    exact sol_infinite_mono hτ (sol_infinite_swap_coeff293 hs (H s hs hS γ))

/-- P0079 page 3, corollary, transcendental case. CONDITIONAL ON the three
OPEN smaller analytic inputs. The conclusion is the sealed target's exact statement. -/
theorem lz_corollary_tr418 : CorollaryStatement nuTr IsTr := by
  exact corollary_cases418 nuTr IsTr (fun _ h => Or.inl ⟨rfl, h⟩)

/-- P0079 page 3, corollary, algebraic case. CONDITIONAL ON the same three
OPEN smaller analytic inputs. The conclusion is the sealed target's exact statement. -/
theorem lz_corollary_alg418 : CorollaryStatement nuAlg IsAlg := by
  exact corollary_cases418 nuAlg IsAlg (fun _ h => Or.inr ⟨rfl, h⟩)

end LeanLab.LZPowersOfTwo
