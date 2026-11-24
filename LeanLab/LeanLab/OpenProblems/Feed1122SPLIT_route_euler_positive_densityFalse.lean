import LeanLab.OpenProblems.State1612

/-!
# Falsifier for `leaf_second_moment_card` (OpenProblems, SPLIT_route_euler_positive_density)

`leaf_second_moment_card` in `SPLIT_route_euler_positive_density.lean` quantifies over every
`R : ℕ → ℕ` whose vanishing set off `0` is the non-representable set.  That hypothesis does not
control the size of `R`, so the second moment bound fails for `R n = n` on representable `n`:
at a representable `X` the single term `X ^ 2` already exceeds `b * X ^ 2 / (log X) ^ 2` once
`(log X) ^ 2 > b`, and representable `X` are unbounded, since `n = (p - 1) / 4` is representable,
`8n + 3 = 1 ^ 2 + 2p`, for every prime `p ≡ 1 mod 4`.

This is the same defect that `leaf_first_moment_card` had before its repair, which pinned `R` by
`hRdef`.  The theorem below proves the negation of the leaf's exact statement.  No definition is
introduced.  AI wrote the Lean code.
-/

namespace LeanLab.OpenProblems.State1612

open LeanLab
open scoped Classical

/-- The exact statement of `leaf_second_moment_card` is false: a counterexample is
`R n = if IsEuler (8n+3) then n else 0`. -/
theorem leaf_second_moment_card_false :
    ¬ (∀ R : ℕ → ℕ, (∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3))) →
      ∃ b : ℝ, 0 < b ∧ ∀ᶠ X : ℕ in Filter.atTop,
        Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
            (fun n => (R n : ℝ) ^ 2)
          ≤ b * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2) := by
  intro h
  set R : ℕ → ℕ := fun n => if IsEuler (8 * n + 3) then n else 0 with hRdef
  have hR : ∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3)) := by
    intro n hn
    simp only [hRdef]
    split_ifs with hE
    · simp only [hE, iff_true]; omega
    · simp [hE]
  obtain ⟨b, hb, hev⟩ := h R hR
  have hlog : Filter.Tendsto (fun X : ℕ => Real.log (X : ℝ)) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hev2 := hev.and ((hlog.eventually_gt_atTop (b + 1)).and (Filter.eventually_ge_atTop 1))
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp hev2
  obtain ⟨p, hp, hpN, hpmod⟩ := Nat.exists_prime_gt_modEq_one (k := 4) (4 * N + 1) (by norm_num)
  have hp4 : p % 4 = 1 := by
    have := hpmod
    unfold Nat.ModEq at this
    simpa using this
  set n := p / 4 with hn
  have hp_eq : p = 4 * n + 1 := by omega
  have hnN : N ≤ n := by omega
  obtain ⟨hbound, hlogn, hn1⟩ := hN n hnN
  have hE : IsEuler (8 * n + 3) := ⟨1, p, odd_one, hp, by rw [hp_eq]; ring⟩
  have hRn : R n = n := by simp [hRdef, hE]
  have hmem : n ∈ (Finset.Icc 1 n).filter (fun m => IsEuler (8 * m + 3)) := by
    simp [Finset.mem_filter, Finset.mem_Icc, hE]; omega
  have hsingle : ((R n : ℕ) : ℝ) ^ 2 ≤
      Finset.sum ((Finset.Icc 1 n).filter (fun m => IsEuler (8 * m + 3)))
        (fun m => (R m : ℝ) ^ 2) :=
    Finset.single_le_sum (f := fun m => (R m : ℝ) ^ 2) (fun _ _ => sq_nonneg _) hmem
  rw [hRn] at hsingle
  have hn0 : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn1
  have hL : 0 < Real.log (n : ℝ) := by linarith
  have hL2 : b < Real.log (n : ℝ) ^ 2 := by nlinarith
  have hfin : (n : ℝ) ^ 2 ≤ b * (n : ℝ) ^ 2 / Real.log (n : ℝ) ^ 2 := hsingle.trans hbound
  rw [le_div_iff₀ (by positivity)] at hfin
  have hn2 : (0 : ℝ) < (n : ℝ) ^ 2 := by positivity
  nlinarith

end LeanLab.OpenProblems.State1612
