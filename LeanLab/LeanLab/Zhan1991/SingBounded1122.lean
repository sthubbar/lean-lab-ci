import LeanLab.Zhan1991.SPLIT_major_1122
import LeanLab.Zhan1991.SingConv

/-!
P0068 Zhan 1991, step 5 of the major arc split SPLIT_major_1122, burst-20261122, session S80:
the singular series of page 260 is bounded, `0 ≤ 𝔖(N) ≤ exp (Σ_p 4/p²)`. PROVED. This closes
the LEAF `singBounded_leaf` by a separate proof, `singBounded_proof`, without editing that file.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Zhan1991

/-- Page 260, the singular series is bounded: every Euler factor lies in `[0, exp (4/p²)]`, so
every finite partial product lies in `[0, exp (Σ_p 4/p²)]`, and so does the limit. PROVED. -/
theorem singBounded_proof : SingBounded := by
  set S := ∑' p : {p : ℕ // p.Prime}, (4 : ℝ) / ((p.1 : ℝ) ^ 2) with hS
  refine ⟨Real.exp S, fun N => ?_⟩
  set f : {p : ℕ // p.Prime} → ℝ := fun p ↦
    if p.1 ∣ N then 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 else 1 + 1 / ((p.1 : ℝ) - 1) ^ 3 with hf
  have hm : HasProd f (Sing N) := (sing_multipliable N).hasProd
  have hf0 : ∀ p, 0 ≤ f p := by
    intro p
    have h2 : (1 : ℝ) ≤ (p.1 : ℝ) - 1 := by
      have : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.2.two_le
      linarith
    simp only [hf]
    split_ifs
    · rw [sub_nonneg, div_le_one (by positivity)]
      nlinarith
    · positivity
  have hf1 : ∀ p, f p ≤ Real.exp (4 / ((p.1 : ℝ) ^ 2)) := by
    intro p
    have hb : f p ≤ 1 + 4 / ((p.1 : ℝ) ^ 2) := by
      have h2 : (1 : ℝ) ≤ (p.1 : ℝ) - 1 := by
        have : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.2.two_le
        linarith
      have hc := factor_bound p.2 (abs_cube_le p.2)
      rw [Real.norm_eq_abs, abs_of_pos (by positivity)] at hc
      simp only [hf]
      split_ifs
      · have : 0 ≤ 4 / ((p.1 : ℝ) ^ 2) := by positivity
        have : 0 ≤ 1 / ((p.1 : ℝ) - 1) ^ 2 := by positivity
        linarith
      · linarith
    exact hb.trans (by have := Real.add_one_le_exp (4 / ((p.1 : ℝ) ^ 2)); linarith)
  have hsum := summable_four_div_sq_primes
  have hfin : ∀ s : Finset {p : ℕ // p.Prime}, ∏ p ∈ s, f p ≤ Real.exp S := by
    intro s
    calc ∏ p ∈ s, f p ≤ ∏ p ∈ s, Real.exp (4 / ((p.1 : ℝ) ^ 2)) :=
          Finset.prod_le_prod₀ (fun p _ => hf0 p) (fun p _ => hf1 p)
      _ = Real.exp (∑ p ∈ s, 4 / ((p.1 : ℝ) ^ 2)) := (Real.exp_sum _ _).symm
      _ ≤ Real.exp S := Real.exp_le_exp.mpr
          (hsum.sum_le_tsum s (fun p _ => by positivity))
  have hup : Sing N ≤ Real.exp S := le_of_tendsto' hm hfin
  have hlo : 0 ≤ Sing N := ge_of_tendsto' hm (fun s => Finset.prod_nonneg (fun p _ => hf0 p))
  rw [abs_of_nonneg hlo]
  exact hup


/-- `major_evaluation110` through the split with step 5 PROVED: CONDITIONAL ON steps 1 to 4. -/
theorem major_evaluation_split_p2 :
    ∃ d₀ : ℝ, 0 < d₀ ∧ ∀ d : ℝ, d₀ ≤ d → ∀ c : ℝ, 0 < c →
      ∃ K N₀ : ℝ, ∀ N : ℕ, Odd N → N₀ ≤ N →
        |majorTerm110 N ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) d
          - 3 * Sing N * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-3 : ℝ)|
          ≤ K * ((N : ℝ) ^ (5 / 8 : ℝ) * Real.log N ^ c) ^ 2 *
              Real.log N ^ (-4 : ℝ) :=
  majorEval_of_steps (majorAssembly_of_approx majorArcApprox_cited) singIntEval_leaf
    singTruncEval_leaf singBounded_proof

end LeanLab.Zhan1991
