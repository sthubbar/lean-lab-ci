/-
S10-07, ROUTE BURST burst-20261124, second file. The side condition `φ(r)² ≥ 8 r` of
`leaf_count_second_forces_no_siegel_S10` is removed with the uniform totient bound
`q⁷ ≤ 2401 φ(q)⁸` of `LeanLab.Zinoviev1997.TotientTail`, proved there with no open leaf. It
gives `φ(r)² ≥ 8 r` for every `r ≥ 3000`.

Result: the statement of `leaf_count_second` of `SPLIT_prop81.lean` implies that there are
`c > 0` and `r₀` such that no primitive real character of conductor `r ≥ r₀` has a real zero
`1 - δ` with `0 < δ < c / log r`. That is the nonexistence of Landau-Siegel zeros, which is
OPEN. So the leaf is not provable without settling an open problem.

AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.BhowmikGrimmelt2026.Prop81SecondSiegelS10
import LeanLab.Zinoviev1997.TotientTail

namespace LeanLab.BhowmikGrimmelt2026

/-- `φ(r)² ≥ 8 r` for `r ≥ 3000`, from `r⁷ ≤ 2401 φ(r)⁸`, Zinoviev1997 `seventh_le_totient_eighth`:
if `φ(r)² < 8 r` then `r⁷ < 2401 · 4096 r⁴`, so `r³ < 2401 · 4096 < 3000³`. -/
theorem totient_sq_ge_eight_S10 (r : ℕ) (hr : 3000 ≤ r) :
    8 * (r : ℝ) ≤ (Nat.totient r : ℝ) ^ 2 := by
  have hnat : 8 * r ≤ Nat.totient r ^ 2 := by
    by_contra hcon
    push_neg at hcon
    have h7 := LeanLab.Zinoviev1997.seventh_le_totient_eighth r (by omega)
    have h8 : Nat.totient r ^ 8 < (8 * r) ^ 4 := by
      have := Nat.pow_lt_pow_left hcon (by norm_num : (4 : ℕ) ≠ 0)
      rw [← pow_mul] at this
      simpa using this
    have h3 : 3000 ^ 3 ≤ r ^ 3 := Nat.pow_le_pow_left hr 3
    have hbig : 2401 * (8 * r) ^ 4 ≤ r ^ 7 := by
      have e1 : 2401 * (8 * r) ^ 4 = (2401 * 4096) * r ^ 4 := by ring
      have e2 : r ^ 7 = r ^ 3 * r ^ 4 := by ring
      rw [e1, e2]
      apply Nat.mul_le_mul_right
      have : 2401 * 4096 ≤ 3000 ^ 3 := by norm_num
      omega
    have : 2401 * Nat.totient r ^ 8 < 2401 * (8 * r) ^ 4 :=
      Nat.mul_lt_mul_of_pos_left h8 (by norm_num)
    omega
  exact_mod_cast hnat

/-- S10-07, the clean form. The statement of `leaf_count_second`, copied verbatim as `hleaf`,
implies that there are `c > 0` and `r₀` such that no primitive real character of conductor
`r ≥ r₀` has a real zero `1 - δ` with `0 < δ < c / log r`: Landau-Siegel zeros do not exist.
This is open; see `leaf_count_second_forces_no_siegel_S10` for the argument. -/
theorem leaf_count_second_forces_no_siegel_all_S10
    (hleaf : ∀ (ϑ : ℝ), 2 / 5 ≤ ϑ → ϑ < 4 / 9 → ∀ (ε : ℝ), 0 < ε →
      ∃ Cε : ℝ, ∀ (X : ℝ), 2 ≤ X → ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (δ : ℝ),
        χ.IsPrimitive → IsRealChar χ → (r : ℝ) ≤ X ^ ϑ → 0 < δ → δ < (1 / 2) / Real.log X →
        DirichletCharacter.LFunction χ ((1 - δ : ℝ) : ℂ) = 0 →
        (((((Finset.Icc ⌈X / 2⌉₊ ⌊X⌋₊)).filter (fun N : ℕ => Even N ∧
            ¬ ‖genSing χ χ N * betaC ((1 - δ : ℝ) : ℂ) ((1 - δ : ℝ) : ℂ) *
                (N : ℂ) ^ (2 * ((1 - δ : ℝ) : ℂ) - 1)‖ ≤
            (4 : ℝ) * (singular N * X * (δ * Real.log X) ^ ((1 : ℝ) / 10) +
                singular N * N * r / (Nat.totient r : ℝ) ^ 2 +
                  X ^ (1 - (1 : ℝ) / 10)) / 2)).card : ℕ) : ℝ) ≤
          Cε * X ^ (3 / 5 + ε)) :
    ∃ c : ℝ, 0 < c ∧ ∃ r₀ : ℕ, ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), r₀ ≤ r →
      χ.IsPrimitive → IsRealChar χ →
      ∀ δ : ℝ, 0 < δ → δ < c / Real.log r →
        DirichletCharacter.LFunction χ ((1 - δ : ℝ) : ℂ) ≠ 0 := by
  obtain ⟨c, hc, r₀, h⟩ := leaf_count_second_forces_no_siegel_S10 hleaf
  refine ⟨c, hc, max r₀ 3000, ?_⟩
  intro r _ χ hr hprim hreal δ hδ hδc
  exact h r χ (le_trans (le_max_left _ _) hr) hprim hreal
    (totient_sq_ge_eight_S10 r (le_trans (le_max_right _ _) hr)) δ hδ hδc

/-- Faithfulness check, not a result: the hypothesis is exactly the statement of
`leaf_count_second`. This example depends on the open leaf and is not counted as proved. -/
example : True := by
  have _h := leaf_count_second_forces_no_siegel_all_S10
    (fun ϑ h1 h2 ε hε => leaf_count_second ϑ h1 h2 ε hε)
  trivial

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.totient_sq_ge_eight_S10
#print axioms LeanLab.BhowmikGrimmelt2026.leaf_count_second_forces_no_siegel_all_S10
