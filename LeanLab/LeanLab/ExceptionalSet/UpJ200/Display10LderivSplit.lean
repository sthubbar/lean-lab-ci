import LeanLab.ExceptionalSet.UpJ200.Display10Leaves

/-!
# Split of `Display10Leaves.leaf_Lderiv_tail`

Burst burst-20261122, Claude cloud session S112. AI wrote the Lean code. Binary Goldbach is open.

`leaf_Lderiv_tail_proved` is the exact type twin of `Display10Leaves.leaf_Lderiv_tail`, PROVED
from two leaves of Davenport chapter 14: the convergence of the Dirichlet series of `-L'(σ, χ)`
for `σ > 0`, and the finite partial summation bound for the tail blocks `r ≤ n < M`.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Display10LderivSplit

open Real Filter Topology

/-- LEAF: Davenport, Multiplicative Number Theory, chapter 14 with chapter 4, the Abel summation
continuation of `L(s, χ)` and its derivative to `Re s > 0` for nonprincipal `χ`, class MEDIUM.
For real `σ > 0` the partial sums of `∑ χ(n) log n n^{-σ}` converge to `-L'(σ, χ)`, where `L'`
is the complex derivative of Mathlib's continued `LFunction`. -/
theorem leaf_Lderiv_series : ∀ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r), χ ≠ 1 →
    ∀ σ : ℝ, 0 < σ →
      Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M,
          χ n * ((Real.log n : ℂ) * (n : ℂ) ^ (-(σ : ℂ))))
        atTop (𝓝 (-deriv χ.LFunction (σ : ℂ))) := by
  sorry

/-- LEAF: Davenport, Multiplicative Number Theory, chapter 14, finite partial summation for the
block `∑_{r ≤ n < M} χ(n) log n n^{-σ}` using `|∑_{n ≤ x} χ(n)| ≤ r` and that `log t t^{-σ}` is
eventually decreasing with value `≤ e log r / r` near `t = r`, for `1 - 1/log r ≤ σ ≤ 1`,
class MEDIUM. The bound is uniform in `M`. -/
theorem leaf_Lderiv_block : ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (_ : NeZero r)
    (χ : DirichletCharacter ℂ r), χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
    ∀ σ : ℝ, 1 - 1 / Real.log r ≤ σ → σ ≤ 1 → ∀ M : ℕ, r ≤ M →
      ‖∑ n ∈ Finset.Ico r M, χ n * ((Real.log n : ℂ) * (n : ℂ) ^ (-(σ : ℂ)))‖ ≤
        C * Real.log r := by
  sorry

/-- Exact type twin of `Display10Leaves.leaf_Lderiv_tail`, PROVED from the two leaves above. -/
theorem leaf_Lderiv_tail_proved : ∃ C : ℝ, 0 < C ∧ ∀ (r : ℕ) (_ : NeZero r)
    (χ : DirichletCharacter ℂ r), χ.IsPrimitive → χ ^ 2 = 1 → χ ≠ 1 →
    ∀ σ : ℝ, 1 - 1 / Real.log r ≤ σ → σ ≤ 1 →
      ‖deriv χ.LFunction (σ : ℂ) + ∑ n ∈ Finset.range r,
          χ n * ((Real.log n : ℂ) * (n : ℂ) ^ (-(σ : ℂ)))‖ ≤ C * Real.log r := by
  obtain ⟨C, hC, hblock⟩ := leaf_Lderiv_block
  refine ⟨C, hC, ?_⟩
  intro r hr χ hprim hsq hχ σ hσ1 hσ2
  have hr2 : 2 ≤ r := Display10Leaves.two_le_of_ne_one hχ
  have hlog : 0 < Real.log r := Real.log_pos (by exact_mod_cast (by omega : 1 < r))
  have hr3 : 3 ≤ r := by
    by_contra hlt
    have hr : r = 2 := by omega
    subst hr
    apply hχ
    ext a
    have hcard : Fintype.card (ZMod 2)ˣ = 1 := by
      rw [ZMod.card_units_eq_totient]; rfl
    have : a = 1 := by
      have := Fintype.card_le_one_iff_subsingleton.mp hcard.le
      exact Subsingleton.elim _ _
    subst this
    simp
  have hσpos : 0 < σ := by
    have h3 : (3 : ℝ) ≤ r := by exact_mod_cast hr3
    have hl3 : 1 < Real.log 3 := by
      rw [Real.lt_log_iff_exp_lt (by norm_num)]
      have := Real.exp_one_lt_d9
      norm_num at this ⊢
      linarith
    have hl : 1 < Real.log r := lt_of_lt_of_le hl3 (Real.log_le_log (by norm_num) h3)
    have : 1 / Real.log r < 1 := by rw [div_lt_one hlog]; exact hl
    linarith
  set f : ℕ → ℂ := fun n => χ n * ((Real.log n : ℂ) * (n : ℂ) ^ (-(σ : ℂ))) with hf
  set H : ℂ := ∑ n ∈ Finset.range r, f n
  have hT := leaf_Lderiv_series r hr χ hχ σ hσpos
  have hT2 : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M, f n - H) atTop
      (𝓝 (-deriv χ.LFunction (σ : ℂ) - H)) := hT.sub_const H
  have hnorm : Tendsto (fun M : ℕ => ‖∑ n ∈ Finset.range M, f n - H‖) atTop
      (𝓝 ‖-deriv χ.LFunction (σ : ℂ) - H‖) := hT2.norm
  have hev : ∀ᶠ M : ℕ in atTop, ‖∑ n ∈ Finset.range M, f n - H‖ ≤ C * Real.log r := by
    filter_upwards [eventually_ge_atTop r] with M hM
    have heq : ∑ n ∈ Finset.range M, f n - H = ∑ n ∈ Finset.Ico r M, f n := by
      rw [← Finset.sum_range_add_sum_Ico f hM]
      ring
    rw [heq]
    exact hblock r hr χ hprim hsq hχ σ hσ1 hσ2 M hM
  have hlim := le_of_tendsto hnorm hev
  have : deriv χ.LFunction (σ : ℂ) + H = -(-deriv χ.LFunction (σ : ℂ) - H) := by ring
  rw [this, norm_neg]
  exact hlim

#print axioms leaf_Lderiv_tail_proved

end LeanLab.ExceptionalSet.UpJ200.Display10LderivSplit
