import LeanLab.ExceptionalSet.Decomp450c

/-!
Audit of the auxiliary absorption claim in SPLIT_lemma4.
P0082 page 359 omits the discrepancy proof. It does not assert this scalar comparison.
The formal helper has an extra factor N that its exponential saving cannot absorb.
AI wrote this Lean code. Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.Decomp450i

open Real Filter Finset

/-- The absorption helper of SPLIT_lemma4 is false already at kappa1 and B1 equal to one.
For every admissible gamma the left side contains a term of order N squared times
subpower decay, while the proposed right side is at most B times N. -/
theorem not_absorption_at_one (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ¬ (∃ κ B : ℝ, 0 < κ ∧ 1 ≤ B ∧ ∀ N : ℕ, 3 ≤ N →
        4 * N / ((Nat.ceil (Real.log N) : ℝ) + 1) +
          4 * N * (N * Real.exp (-Real.log N ^ (3 - 2 * γ))
            * ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log N)), 1 / ((h : ℝ) + 1))
          ≤ B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ))) := by
  rintro ⟨κ, B, hκ, hB, hbound⟩
  obtain ⟨Ne, he⟩ := Decomp450c.exp_log_pow_le γ 2 h1 h2 (by norm_num)
  have hl : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have ht : Tendsto (fun N : ℕ => Real.exp (Real.log (N : ℝ) ^ (3 - 2 * γ))) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((tendsto_rpow_atTop (by linarith : 0 < 3 - 2 * γ)).comp hl)
  obtain ⟨Nb, hb⟩ := eventually_atTop.mp (ht.eventually_ge_atTop (B + 1))
  obtain ⟨Nl, hl'⟩ := eventually_atTop.mp (hl.eventually_ge_atTop 1)
  let N : ℕ := max 3 (max Ne (max Nb Nl))
  have hN3 : 3 ≤ N := le_max_left _ _
  have hNe : Ne ≤ N := (le_max_left _ _).trans (le_max_right _ _)
  have hNb : Nb ≤ N := (le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hNl : Nl ≤ N := (le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : 1 ≤ Real.log (N : ℝ) := hl' N hNl
  have hp : 0 ≤ Real.log (N : ℝ) ^ (3 - 2 * γ) := Real.rpow_nonneg (by linarith) _
  have hexp : Real.exp (2 * Real.log (N : ℝ) ^ (3 - 2 * γ)) *
      Real.exp (-Real.log (N : ℝ) ^ (3 - 2 * γ)) =
        Real.exp (Real.log (N : ℝ) ^ (3 - 2 * γ)) := by
    rw [← Real.exp_add]
    congr 1
    ring
  have hm := mul_le_mul_of_nonneg_right (he N hNe)
    (Real.exp_pos (-Real.log (N : ℝ) ^ (3 - 2 * γ))).le
  rw [hexp] at hm
  have hgrowth : B + 1 ≤ (N : ℝ) * Real.exp (-Real.log (N : ℝ) ^ (3 - 2 * γ)) :=
    (hb N hNb).trans hm
  have hceil : 1 ≤ Nat.ceil (Real.log (N : ℝ)) := by
    have hh : (1 : ℝ) ≤ (Nat.ceil (Real.log (N : ℝ)) : ℝ) := hlog.trans (Nat.le_ceil _)
    exact_mod_cast hh
  have hsum : (1 / 2 : ℝ) ≤
      ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log (N : ℝ))), 1 / ((h : ℝ) + 1) := by
    have hh := Finset.single_le_sum
      (f := fun h : ℕ => (1 : ℝ) / ((h : ℝ) + 1))
      (s := Finset.Icc 1 (Nat.ceil (Real.log (N : ℝ))))
      (fun h _ => by positivity)
      (show 1 ∈ Finset.Icc 1 (Nat.ceil (Real.log (N : ℝ))) by simp [hceil])
    norm_num at hh ⊢
    exact hh
  have hterm : 2 * (N : ℝ) * (N * Real.exp (-Real.log (N : ℝ) ^ (3 - 2 * γ))) ≤
      4 * N * (N * Real.exp (-Real.log (N : ℝ) ^ (3 - 2 * γ)) *
        ∑ h ∈ Finset.Icc 1 (Nat.ceil (Real.log (N : ℝ))), 1 / ((h : ℝ) + 1)) := by
    have hh := mul_le_mul_of_nonneg_left hsum
      (by positivity : 0 ≤ 4 * (N : ℝ) * (N * Real.exp (-Real.log (N : ℝ) ^ (3 - 2 * γ))))
    nlinarith [hh]
  have hfirst : (0 : ℝ) ≤ 4 * N / ((Nat.ceil (Real.log (N : ℝ)) : ℝ) + 1) := by positivity
  have hdecay : Real.exp (-κ * Real.log (N : ℝ) ^ (3 - 2 * γ)) ≤ 1 := by
    apply Real.exp_le_one_iff.mpr
    nlinarith
  have hrhs : B * N * Real.exp (-κ * Real.log (N : ℝ) ^ (3 - 2 * γ)) ≤ B * N :=
    mul_le_of_le_one_right (by positivity) hdecay
  have hbad := (hbound N hN3).trans hrhs
  have hlarge := mul_le_mul_of_nonneg_left hgrowth (by positivity : 0 ≤ 2 * (N : ℝ))
  have hBN := mul_le_mul_of_nonneg_right hB hNpos.le
  nlinarith

end LeanLab.ExceptionalSet.Decomp450i
