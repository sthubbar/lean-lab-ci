import LeanLab.BHP1997.SPLIT_upper_self_scaled_conditions

namespace LeanLab.BHP1997.Upper312Route
open Classical Complex Decomp132 DecompC165b DecompC165d

/-- LEAF: principal distribution under the auxiliary hypothesis that the logarithm exceeds one. This removes the small x regime where Real.log x is close to zero. -/
theorem leaf_principal_log_ge_one
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {b1 : ℝ → ℕ → ℝ}
    (hb : ∀ x m, b1 x m = if 2 ≤ x ^ (11 / 20 + ε) ∧ m ∈ rightInterval ε x then Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperRawWeight ε (m : ℝ) m else 0) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → 1 < Real.log x →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b1 x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q) -
              ((ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
                upperDeletedIntegral ω ε : ℝ) : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ≤
            C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF: elementary analytic fact that the logarithm exceeds one once x exceeds the exponential of one. This is a purely real analysis step used to enforce the auxiliary hypothesis of the previous leaf. -/
theorem leaf_log_ge_one_of_x_ge
    (x : ℝ) (hx : Real.exp 1 < x) : 1 < Real.log x := by
  sorry

theorem upper_self_scaled_principal_distribution_F753
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) {b1 : ℝ → ℕ → ℝ}
    (hb : ∀ x m, b1 x m = if 2 ≤ x ^ (11 / 20 + ε) ∧ m ∈ rightInterval ε x then Real.log (m : ℝ) / Real.log (x ^ (11 / 20 + ε)) * upperRawWeight ε (m : ℝ) m else 0) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
      1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
          ((b1 x m : ℂ) * (1 : DirichletCharacter ℂ q) (m : ZMod q) -
            ((ω (1/(1/4+(2*(1/16-1/10^5))/8-ε)) / (1/4+(2*(1/16-1/10^5))/8-ε) +
              upperDeletedIntegral ω ε : ℝ) : ℂ) / Real.log (x ^ (11 / 20 + ε)))‖ ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C0, hC0⟩ := leaf_principal_log_ge_one h4 h9 hω hz hε hε8 hb A hA
  let C := max C0 (Real.exp 1 + 1)
  refine ⟨C, fun x hx q hq hqA t ht => ?_⟩
  have hx0 : C0 ≤ x := le_trans (le_max_left _ _) hx
  have hxexp : Real.exp 1 < x := by
    have h1 : Real.exp 1 + 1 ≤ x := le_trans (le_max_right _ _) hx
    have hlt : Real.exp 1 < Real.exp 1 + 1 := by linarith
    exact lt_trans hlt h1
  have hlog : 1 < Real.log x := leaf_log_ge_one_of_x_ge x hxexp
  have hbound := hC0 x hx0 hlog q hq hqA t ht
  exact hbound

end LeanLab.BHP1997.Upper312Route
