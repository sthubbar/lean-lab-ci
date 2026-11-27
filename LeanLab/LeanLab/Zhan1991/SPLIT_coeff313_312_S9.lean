/-
P0068 Zhan 1991, page 266 display (3.13) as used on page 268, read for (3.12) by page 269: the
LEAF `coeff313_312_leaf_S9` of SPLIT_FJdirpoly_312_S9.lean split into the pointwise bound
`|b(n)| ≤ r(n) (1 + log n)`, PROVED, and the divisor moment bound for `r`, a new LEAF.
Here `r(n)` counts the tuples `n_j ∈ I_j`, `j ∈ J`, with `Π n_j = n`, so `r(n) ≤ d_{|J|}(n)`.
Burst 20261124, session S9, unit C-extra-5. Source: papers/P0068.pdf, journal page 266, pdf
page 8, display (3.13) checked on the page image at 110 dpi. AI-written Lean code, Claude.
Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Zhan1991.SPLIT_FJdirpoly_312_S9

namespace LeanLab.Zhan1991
open Finset Real

noncomputable section

/-- `r(m)`, the number of tuples `(n_j)_{j ∈ J}`, `n_j ∈ I_j`, with `Π n_j = m`; it is at most
`d_{|J|}(m)`, the divisor function of (3.13), page 266. -/
def rFJ312 (Nv : Fin 20 → ℝ) (J : Finset (Fin 20)) (m : ℕ) : ℕ :=
  ((J.pi (fun j => dyad (Nv j))).filter (fun p => ∏ x ∈ J.attach, p x x.2 = m)).card

/-- LEAF: page 266 display (3.13), `Σ_{n≤x} d_k²(n) ≪ x (log x)^{c_k}` and
`Σ_{n≤x} d_k²(n)/n ≪ (log x)^{c_k}`, applied with `r(n) ≤ d_{|J|}(n)`, `|J| ≤ 20`,
`x = Π ⌊2N_j⌋ ≤ 2^{20} Π N_j ≤ 2^{20} N`, and `1 + log n ≪ L`:
`Σ_{n ≤ x} (qT + n) (r(n)(1 + log n))² n⁻¹ ≪ (qT + Π_{j ∈ J} N_j) L^{c₀}` for `T ≥ 1`.
Class MEDIUM. -/
theorem divisor313_312_leaf_S9 : ∃ c7 : ℝ, 0 ≤ c7 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (Nv : Fin 20 → ℝ) (J : Finset (Fin 20)), N₀ ≤ N → Cond35 N Nv →
      ∀ (q : ℕ) (T : ℝ), 1 ≤ T →
        ∑ n ∈ Finset.Icc 1 (∏ j ∈ J, ⌊2 * Nv j⌋₊),
            ((q : ℝ) * T + n) * ((rFJ312 Nv J n : ℝ) * (1 + Real.log n)) ^ 2 *
            (n : ℝ) ^ (-2 * (1 / 2 : ℝ))
          ≤ K * ((q : ℝ) * T + ∏ j ∈ J, Nv j) * Real.log N ^ c7 := by
  sorry

/-- PROVED: `|a_j(n)| ≤ log n` for `j = 1` and `≤ 1` otherwise, (3.6) of page 264. -/
theorem aj_norm_le_S9 (j n : ℕ) (hn : 1 ≤ n) :
    ‖aj j n‖ ≤ if j = 1 then Real.log n else 1 := by
  unfold aj
  split_ifs with h1 h2
  · rw [Complex.norm_real, Real.norm_of_nonneg (Real.log_nonneg (by exact_mod_cast hn))]
  · simp
  · rw [Complex.norm_intCast]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one

/-- PROVED: for a tuple `n_j ∈ I_j` with `Π n_j = m`, `|Π a_j(n_j)| ≤ 1 + log m`, since only
`a_1` is not bounded by `1` and `n_1 ≤ m`. -/
theorem prod_aj_norm_le_S9 (Nv : Fin 20 → ℝ) (J : Finset (Fin 20))
    (p : (j : Fin 20) → j ∈ J → ℕ) (hp : p ∈ J.pi (fun j => dyad (Nv j))) (m : ℕ)
    (hm : ∏ x ∈ J.attach, p x x.2 = m) :
    ‖∏ x ∈ J.attach, aj (x.val.val + 1) (p x x.2)‖ ≤ 1 + Real.log m := by
  rw [Finset.mem_pi] at hp
  have hpos : ∀ x ∈ J.attach, 1 ≤ p x x.2 := fun x _ => by
    have h := hp x x.2
    simp only [dyad, Finset.mem_filter, Finset.mem_Icc] at h
    exact h.1.1
  have hle : ∀ x ∈ J.attach, p x x.2 ≤ m := fun x hx => by
    rw [← hm]; exact Finset.single_le_prod' (fun y hy => hpos y hy) hx
  have hm1 : 1 ≤ m := by rw [← hm]; exact Finset.one_le_prod' hpos
  have hlog : 0 ≤ Real.log m := Real.log_nonneg (by exact_mod_cast hm1)
  rw [norm_prod]
  have hf : ∀ x ∈ J.attach, ‖aj (x.val.val + 1) (p x x.2)‖ ≤
      if x.val.val = 0 then 1 + Real.log m else 1 := by
    intro x hx
    have h := aj_norm_le_S9 (x.val.val + 1) (p x x.2) (hpos x hx)
    by_cases h0 : x.val.val = 0
    · rw [if_pos (by omega)] at h
      rw [if_pos h0]
      have : Real.log (p x x.2) ≤ Real.log m :=
        Real.log_le_log (by exact_mod_cast hpos x hx) (by exact_mod_cast hle x hx)
      linarith
    · rw [if_neg (by omega)] at h
      rw [if_neg h0]; exact h
  calc ∏ x ∈ J.attach, ‖aj (x.val.val + 1) (p x x.2)‖
      ≤ ∏ x ∈ J.attach, (if x.val.val = 0 then 1 + Real.log m else 1) := by
        gcongr with x hx
        exact hf x hx
    _ ≤ 1 + Real.log m := by
        rw [Finset.prod_ite, Finset.prod_const, Finset.prod_const_one, mul_one]
        have hc : (J.attach.filter (fun x => x.val.val = 0)).card ≤ 1 := by
          apply Finset.card_le_one.mpr
          intro a ha b hb
          simp only [Finset.mem_filter] at ha hb
          exact Subtype.ext (Fin.ext (by omega))
        calc (1 + Real.log m) ^ (J.attach.filter (fun x => x.val.val = 0)).card
            ≤ (1 + Real.log m) ^ 1 := pow_le_pow_right₀ (by linarith) hc
          _ = 1 + Real.log m := pow_one _

/-- PROVED: `|b(m)| ≤ r(m) (1 + log m)`, page 268 second line. -/
theorem bFJ312_norm_le_S9 (Nv : Fin 20 → ℝ) (J : Finset (Fin 20)) (m : ℕ) :
    ‖bFJ312 Nv J m‖ ≤ (rFJ312 Nv J m : ℝ) * (1 + Real.log m) := by
  unfold bFJ312 rFJ312
  refine le_trans (norm_sum_le _ _) ?_
  calc _ ≤ ∑ p ∈ (J.pi (fun j => dyad (Nv j))).filter
          (fun p => ∏ x ∈ J.attach, p x x.2 = m), (1 + Real.log m) := by
        apply Finset.sum_le_sum
        intro p hp
        rw [Finset.mem_filter] at hp
        exact prod_aj_norm_le_S9 Nv J p hp.1 m hp.2
    _ = _ := by rw [Finset.sum_const, nsmul_eq_mul]

/-- PROVED from `divisor313_312_leaf_S9`: the statement of the LEAF `coeff313_312_leaf_S9`.
Same statement, same constants. -/
theorem coeff313_312_of_divisor_S9 : ∃ c7 : ℝ, 0 ≤ c7 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (Nv : Fin 20 → ℝ) (J : Finset (Fin 20)), N₀ ≤ N → Cond35 N Nv →
      ∀ (q : ℕ) (T : ℝ), 1 ≤ T →
        ∑ n ∈ Finset.Icc 1 (∏ j ∈ J, ⌊2 * Nv j⌋₊), ((q : ℝ) * T + n) * ‖bFJ312 Nv J n‖ ^ 2 *
            (n : ℝ) ^ (-2 * (1 / 2 : ℝ))
          ≤ K * ((q : ℝ) * T + ∏ j ∈ J, Nv j) * Real.log N ^ c7 := by
  obtain ⟨c7, hc7, K, N0, hD⟩ := divisor313_312_leaf_S9
  refine ⟨c7, hc7, K, N0, fun N Nv J hN hC q T hT => le_trans ?_ (hD N Nv J hN hC q T hT)⟩
  apply Finset.sum_le_sum
  intro n hn
  have hT0 : (0 : ℝ) ≤ q * T := by positivity
  gcongr
  exact bFJ312_norm_le_S9 Nv J n

end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.aj_norm_le_S9
#print axioms LeanLab.Zhan1991.prod_aj_norm_le_S9
#print axioms LeanLab.Zhan1991.bFJ312_norm_le_S9
#print axioms LeanLab.Zhan1991.coeff313_312_of_divisor_S9
