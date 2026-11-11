import LeanLab.LanguascoPintzZaccagnini2007.DecompJ218

/-!
P0045 preprint page 6, the remark after the proof of Corollary 4.2.
Any lower bound on odd radicals tending to infinity suffices for the exceptional tuple sum.
This adapts the existing major_arcs_j2_131 proof and uses the proved Lemma 6.2.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real Filter

/-- P0045 page 6, remark following display 10, and displays 12 to 14.
A bounded exceptional modulus family with uniformly diverging odd radicals
has arbitrarily small singular series mass over the exceptional tuples. -/
theorem major_arcs_j2_diverging481 (g : ℕ → ℝ)
    (hg : Tendsto g atTop atTop) (k : ℕ) (hk : 1 ≤ k)
    (K₁ Cstar : ℕ) (hC : 0 < Cstar) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ E : Finset ℕ, E.card ≤ K₁ →
      (∀ r ∈ E, g X ≤ (oddRad131 r : ℝ)) →
      ∀ N ∈ evenJ131 X, ∀ B ⊆ tuples131 k X,
        (∀ ν ∈ B, ¬ Nonexceptional131 Cstar E (N - tuplePower131 ν)) →
        ∑ ν ∈ B, Sing (N - tuplePower131 ν) ≤ ε * Lg X ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hK : (0 : ℝ) < (K₁ : ℝ) + 1 := by positivity
  set ε' : ℝ := ε / ((K₁ : ℝ) + 1) with hε'def
  have hε' : 0 < ε' := div_pos hε hK
  have hεK : ((K₁ : ℝ) + 1) * ε' = ε := by
    rw [hε'def]
    field_simp
  obtain ⟨r₀, X₁, h62⟩ := lemma62_proved ε' hε'
  obtain ⟨X₂, hX₂⟩ := tuple_window131 (j + 1)
  obtain ⟨X₃, hX₃⟩ := (hg.eventually_ge_atTop
    ((r₀ : ℝ) * Cstar)).exists_forall_of_atTop
  refine ⟨max X₁ (max X₂ X₃), fun X hX E hcard hrad N hN B hB hbad => ?_⟩
  have hx1 : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hx2 : X₂ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hx3 : X₃ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  obtain ⟨hL, hw⟩ := hX₂ X hx2
  have hL3 := hX₃ X hx3
  have hCr : (0 : ℝ) < Cstar := by exact_mod_cast hC
  have hLk : 0 ≤ Lg X ^ (j + 1) := by positivity
  have hsmall : ∀ r ∈ E, r₀ ≤ oddFree131 Cstar r := by
    intro r hr
    have h1 := hrad r hr
    have h2 : (oddRad131 r : ℝ) ≤ oddFree131 Cstar r * Cstar := by
      exact_mod_cast oddRad_le131 hC r
    have h5 : (r₀ : ℝ) * Cstar ≤ oddFree131 Cstar r * Cstar := hL3.trans (h1.trans h2)
    exact_mod_cast le_of_mul_le_mul_right h5 hCr
  have hLnn : 0 ≤ Lg X := by linarith
  have hone : ∀ r ∈ E, ∑ ν ∈ tuples131 (j + 1) X,
      (if oddFree131 Cstar r ∣ N - tuplePower131 ν then Sing (N - tuplePower131 ν) else 0) ≤
        ε' * Lg X ^ (j + 1) := by
    intro r hr
    have ho := oddFree_odd131 Cstar r
    have hA : ∀ m : ℕ, (X : ℝ) / 2 ≤ m → m ≤ X → Amr X m (oddFree131 Cstar r) ≤ ε' * Lg X :=
      fun m hm1 hm2 => h62 X hx1 m _ hm1 hm2 ho.pos ho (hsmall r hr)
    exact tuple_sum_dvd_le131 hA hε'.le hL hw hN
  have hnn : ∀ (ν : Fin (j + 1) → ℕ), ∀ r ∈ E, 0 ≤
      (if oddFree131 Cstar r ∣ N - tuplePower131 ν then
        Sing (N - tuplePower131 ν) else 0) := by
    intro ν r _
    split_ifs
    · exact Sing_nonneg131 _
    · exact le_rfl
  calc ∑ ν ∈ B, Sing (N - tuplePower131 ν)
      ≤ ∑ ν ∈ B, ∑ r ∈ E,
        (if oddFree131 Cstar r ∣ N - tuplePower131 ν then Sing (N - tuplePower131 ν) else 0) := by
        refine sum_le_sum fun ν hν => ?_
        have hex : ∃ r ∈ E, r ∣ Cstar * (N - tuplePower131 ν) := by
          by_contra hcon
          exact hbad ν hν (fun r hr hd => hcon ⟨r, hr, hd⟩)
        obtain ⟨r, hr, hd⟩ := hex
        have hs := single_le_sum (hnn ν) hr
        rwa [if_pos (oddFree_dvd131 hd)] at hs
    _ ≤ ∑ ν ∈ tuples131 (j + 1) X, ∑ r ∈ E,
        (if oddFree131 Cstar r ∣ N - tuplePower131 ν then Sing (N - tuplePower131 ν) else 0) :=
        sum_le_sum_of_subset_of_nonneg hB fun ν _ _ => sum_nonneg (hnn ν)
    _ = ∑ r ∈ E, ∑ ν ∈ tuples131 (j + 1) X,
        (if oddFree131 Cstar r ∣ N - tuplePower131 ν then Sing (N - tuplePower131 ν) else 0) :=
        sum_comm
    _ ≤ ∑ _r ∈ E, ε' * Lg X ^ (j + 1) := sum_le_sum hone
    _ = (E.card : ℝ) * (ε' * Lg X ^ (j + 1)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ((K₁ : ℝ) + 1) * (ε' * Lg X ^ (j + 1)) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hε'.le hLk)
        have : (E.card : ℝ) ≤ K₁ := by exact_mod_cast hcard
        linarith
    _ = ε * Lg X ^ (j + 1) := by
        linear_combination (Lg X ^ (j + 1)) * hεK

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.major_arcs_j2_diverging481
