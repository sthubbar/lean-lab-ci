import LeanLab.LanguascoPintzZaccagnini2007.Decomp131
import LeanLab.LanguascoPintzZaccagnini2007.Growing481

/-!
P0045 preprint page 6, the remark that any diverging odd radical bound suffices.
This supplies that remark through the existing narrow window and two parameter main route.
All analytic statements below are explicit hypotheses. No cited leaf is invoked.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real Filter

/-- P0045 page 6, Corollary 4.2 with the qualitative weakening of display 10
in the remark after its proof. The same g, P and E serve the whole window at each eta. -/
def Cor42GrowingStatement481 : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ (K₁ Cstar : ℕ) (A : ℝ) (g : ℕ → ℝ),
      0 < Cstar ∧ 0 ≤ A ∧ Tendsto g atTop atTop ∧
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        ∃ (P : ℝ) (E : Finset ℕ), AdmissibleP131 X P ∧ E.card ≤ K₁ ∧
          (∀ r ∈ E, g X ≤ (oddRad131 r : ℝ)) ∧
          (∀ n ∈ evenJ131 X, Nonexceptional131 Cstar E n →
            |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) ∧
          (∀ n ∈ evenJ131 X, |binaryMajor131 X n P| ≤ A * n * Sing n)

/-- P0045 page 6, display 10 implies the qualitative hypothesis in the following remark.
This converter is CONDITIONAL on the explicit printed corollary hypothesis. -/
theorem growing_of_cor42_481 (hcor : Cor42OnWindow131 evenJ131) :
    Cor42GrowingStatement481 := by
  intro η hη
  obtain ⟨K₁, Cstar, c, A, hC, hc, hA, X₀, hX₀⟩ := hcor η hη
  have hg : Tendsto (fun X : ℕ => c * Lg X ^ 2) atTop atTop :=
    ((Filter.tendsto_pow_atTop (by decide : (2 : ℕ) ≠ 0)).comp
      Lg_tendsto1619).const_mul_atTop hc
  refine ⟨K₁, Cstar, A, (fun X => c * Lg X ^ 2), hC, hA, hg, X₀, ?_⟩
  intro X hX
  obtain ⟨P, E, hP, hE, hgood, hall⟩ := hX₀ X hX
  exact ⟨P, E, hP, hE.1, hE.2, hgood, hall⟩

/-- P0045 page 6, qualitative radical growth remark, with display 25 on the narrow window.
This is CONDITIONAL on the explicit qualitative corollary and singular average inputs.
The proof adapts major_asymptotic_narrow1619 without changing that sealed theorem. -/
theorem narrow_asymptotic_of_growing481 (hj1 : Cor42GrowingStatement481)
    (hcomb : SingularAverageStatement131) (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∃ P : ℝ, AdmissibleP131 X P ∧
      ∀ N ∈ evenJNarrow1619 k X,
        |majorContribution131 k X N P - coefficient131 k N * N * Lg X ^ k| ≤
          ε * N * Lg X ^ k := by
  classical
  set B : ℝ := 2 * LeanLab.ChenExplicit.twinC * ∑' d, seriesTerm d with hB
  have hB0 : 0 ≤ B := by
    refine le_trans ?_ (coefficient_le131 hk 0)
    exact mul_nonneg (mul_nonneg (by norm_num) LeanLab.ChenExplicit.twinC_pos.le)
      (by linarith [Ck_ge_one131 hk 0])
  have hB1 : 0 < B + 1 := by linarith
  set η : ℝ := ε / (3 * (B + 1)) with hηdef
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) hB1)
  obtain ⟨K₁, Cstar, A, g, hC, hA, hg, X₁, hX₁⟩ := hj1 η hη
  have hA1 : 0 < A + 1 := by linarith
  have hε₂ : 0 < ε / (3 * (A + 1)) := div_pos hε (mul_pos (by norm_num) hA1)
  obtain ⟨X₂, hX₂⟩ := major_arcs_j2_diverging481 g hg k hk K₁ Cstar hC _ hε₂
  obtain ⟨X₃, hX₃⟩ := hcomb k hk (ε / 3) (by positivity)
  obtain ⟨X₄, hX₄⟩ := hcomb k hk 1 one_pos
  obtain ⟨X₅, hX₅⟩ := tuple_window131 k
  refine ⟨max X₁ (max X₂ (max X₃ (max X₄ X₅))), fun X hX => ?_⟩
  have hx1 : X₁ ≤ X := by omega
  have hx2 : X₂ ≤ X := by omega
  have hx3 : X₃ ≤ X := by omega
  have hx4 : X₄ ≤ X := by omega
  have hx5 : X₅ ≤ X := by omega
  obtain ⟨P, E, hP, hcard, hrad, hgood, hup⟩ := hX₁ X hx1
  refine ⟨P, hP, fun N hN' => ?_⟩
  have hN : N ∈ evenJ131 X := (mem_filter.mp hN').1
  obtain ⟨hL, hw⟩ := hX₅ X hx5
  have hL0 : 0 ≤ Lg X := by linarith
  have hLk : 0 ≤ Lg X ^ k := by positivity
  obtain ⟨hN1, hN2, -, hN4⟩ := evenJ_nat131 hN
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsm : ∀ ν ∈ tuples131 k X, 6 * tuplePower131 ν ≤ X := by
    intro ν hν
    have := tuplePower_le131 hν
    have h6 : 6 * (k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊) =
        6 * k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ := by ring
    omega
  have hle : ∀ ν ∈ tuples131 k X, tuplePower131 ν ≤ N := by
    intro ν hν
    have := hsm ν hν
    omega
  have hwin : ∀ ν ∈ tuples131 k X, N - tuplePower131 ν ∈ evenJ131 X := fun ν hν =>
    narrow_shift_mem1619 hN' hν
  set Bad := (tuples131 k X).filter
    (fun ν => ¬ Nonexceptional131 Cstar E (N - tuplePower131 ν)) with hBad
  have hsplit : |∑ ν ∈ tuples131 k X, binaryMajor131 X (N - tuplePower131 ν) P -
      ∑ ν ∈ tuples131 k X, ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν)| ≤
      η * ∑ ν ∈ tuples131 k X, ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) +
        (A + 1) * N * ∑ ν ∈ Bad, Sing (N - tuplePower131 ν) := by
    refine split_bound131 (tuples131 k X)
      (fun ν => ¬ Nonexceptional131 Cstar E (N - tuplePower131 ν))
      (fun ν => binaryMajor131 X (N - tuplePower131 ν) P)
      (fun ν => ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν))
      (fun ν => Sing (N - tuplePower131 ν)) η ((A + 1) * N) hη.le
      (mul_nonneg hA1.le hNr)
      (fun ν _ => mul_nonneg (Nat.cast_nonneg _) (Sing_nonneg131 _))
      (fun ν _ => Sing_nonneg131 _) ?_ ?_
    · intro ν hν hb
      have h := hgood _ (hwin ν hν) (not_not.mp hb)
      have e : η * ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) =
          η * (((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν)) := by ring
      rw [e] at h
      exact h
    · intro ν hν _
      show |binaryMajor131 X (N - tuplePower131 ν) P -
          ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν)| ≤
        (A + 1) * N * Sing (N - tuplePower131 ν)
      have hu := abs_le.mp (hup _ (hwin ν hν))
      have hS := Sing_nonneg131 (N - tuplePower131 ν)
      have hn : ((N - tuplePower131 ν : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le _ _
      have hn0 : (0 : ℝ) ≤ ((N - tuplePower131 ν : ℕ) : ℝ) := Nat.cast_nonneg _
      have h0 := mul_nonneg hn0 hS
      have h1 : A * ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) ≤
          A * N * Sing (N - tuplePower131 ν) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hA) hS
      have h2 : ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) ≤
          N * Sing (N - tuplePower131 ν) := mul_le_mul_of_nonneg_right hn hS
      rw [abs_le]
      constructor <;> linarith [hu.1, hu.2]
  have hjj := hX₂ X hx2 E hcard hrad N hN Bad (filter_subset _ _) (fun ν hν => (mem_filter.mp hν).2)
  have hc3 := hX₃ X hx3 N hN
  have hc1 := hX₄ X hx4 N hN
  rw [← major_expand131 k X N P hle] at hsplit
  set W := ∑ ν ∈ tuples131 k X,
    ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) with hW
  set M := majorContribution131 k X N P with hM
  have hNL : 0 ≤ (N : ℝ) * Lg X ^ k := mul_nonneg hNr hLk
  have hcoef : coefficient131 k N * N * Lg X ^ k ≤ B * ((N : ℝ) * Lg X ^ k) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (coefficient_le131 hk N) hNL
  have hWup : W ≤ (B + 1) * ((N : ℝ) * Lg X ^ k) := by
    have := (abs_le.mp hc1).2
    nlinarith
  have hterm1 : η * W ≤ ε / 3 * ((N : ℝ) * Lg X ^ k) := by
    have h := mul_le_mul_of_nonneg_left hWup hη.le
    have he : η * ((B + 1) * ((N : ℝ) * Lg X ^ k)) = ε / 3 * ((N : ℝ) * Lg X ^ k) := by
      rw [hηdef]
      field_simp
    rw [he] at h
    exact h
  have hterm2 : (A + 1) * N * ∑ ν ∈ Bad, Sing (N - tuplePower131 ν) ≤
      ε / 3 * ((N : ℝ) * Lg X ^ k) := by
    have h := mul_le_mul_of_nonneg_left hjj (mul_nonneg hA1.le hNr)
    have he : (A + 1) * N * (ε / (3 * (A + 1)) * Lg X ^ k) =
        ε / 3 * ((N : ℝ) * Lg X ^ k) := by
      field_simp
    rw [he] at h
    exact h
  have hfin := abs_sub_le M W (coefficient131 k N * N * Lg X ^ k)
  have hc3' : |W - coefficient131 k N * N * Lg X ^ k| ≤ ε / 3 * ((N : ℝ) * Lg X ^ k) := by
    calc _ ≤ _ := hc3
      _ = _ := by ring
  calc _ ≤ _ := hfin
    _ ≤ ε / 3 * ((N : ℝ) * Lg X ^ k) + ε / 3 * ((N : ℝ) * Lg X ^ k) +
        ε / 3 * ((N : ℝ) * Lg X ^ k) := by linarith
    _ = ε * N * Lg X ^ k := by ring

/-- P0045 page 6 qualitative remark and page 9 Section 5.
The repaired main theorem needs only diverging odd radicals in its analytic input.
This theorem is CONDITIONAL on hcor, which is not asserted here. -/
theorem repaired_main_of_growing481 (hcor : Cor42GrowingStatement481) : RepairedMainJ131 :=
  repaired_main_of_narrow1619 (narrow_count1619
    (fun k hk ε hε => narrow_asymptotic_of_growing481 hcor
      major_arcs_combine_supply383 k hk ε hε))

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.growing_of_cor42_481
#print axioms LeanLab.LPZ2007.narrow_asymptotic_of_growing481
#print axioms LeanLab.LPZ2007.repaired_main_of_growing481
