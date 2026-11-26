/-
FALSE: the LEAF `leaf_second_moment_card` of SPLIT_route_euler_positive_density.lean, as stated,
is refuted. AI-written Lean code, Claude, unit S8-08 of burst-20261124. Checked only by the Lean
kernel. Euler's 8n + 3 problem and binary Goldbach are OPEN; this refutes only a split leaf.

The leaf quantifies over every `R : ℕ → ℕ` that is nonzero exactly at the representable `n`.
That hypothesis says nothing about the size of `R`, so `R n = n` at the representable `n` and `0`
elsewhere meets it. Every `n = (p - 1) / 4` with `p ≡ 1 mod 4` prime is representable, since
`8n + 3 = 1 ^ 2 + 2p`, and at `X = n` the square sum is at least `n ^ 2`, which beats
`b * n ^ 2 / (log n) ^ 2` once `(log n) ^ 2 > b`. Mathlib's `Nat.exists_prime_gt_modEq_one`
gives such primes beyond any bound. The intended leaf needs `R` to be the list count of
`leaf_representation_multiplicity`, the `hRdef` hypothesis that `leaf_first_moment_card` carries.
-/
import LeanLab.OpenProblems.SPLIT_route_euler_positive_density

namespace LeanLab.OpenProblems.State1612

open scoped Classical

/-- FALSE certificate for `leaf_second_moment_card`: its statement, quantified over all `R`
meeting its hypothesis, fails for `R n = n` on the representable `n`. -/
theorem leaf_second_moment_card_false :
    ¬ ∀ R : ℕ → ℕ, (∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3))) →
      ∃ b : ℝ, 0 < b ∧ ∀ᶠ X : ℕ in Filter.atTop,
        Finset.sum ((Finset.Icc 1 X).filter (fun n => IsEuler (8 * n + 3)))
            (fun n => (R n : ℝ) ^ 2)
          ≤ b * (X : ℝ) ^ 2 / (Real.log (X : ℝ)) ^ 2 := by
  classical
  intro h
  set R : ℕ → ℕ := fun n => if IsEuler (8 * n + 3) then n else 0 with hRdef
  have hR : ∀ n : ℕ, 1 ≤ n → (R n ≠ 0 ↔ IsEuler (8 * n + 3)) := by
    intro n hn
    by_cases he : IsEuler (8 * n + 3)
    · simp only [hRdef, he, ite_true]; exact ⟨fun _ => trivial, fun _ => by omega⟩
    · simp [hRdef, he]
  obtain ⟨b, hb, hev⟩ := h R hR
  obtain ⟨N0, hN0⟩ := Filter.eventually_atTop.mp hev
  set M : ℕ := max N0 (⌈Real.exp (b + 1)⌉₊ + 1) with hM
  obtain ⟨p, hp, hpM, hp1⟩ := Nat.exists_prime_gt_modEq_one (4 * M + 1) (k := 4) (by norm_num)
  have hp4 : p % 4 = 1 := by
    have := hp1; unfold Nat.ModEq at this; simpa using this
  set n : ℕ := p / 4 with hn
  have hpn : p = 4 * n + 1 := by omega
  have hnM : M ≤ n := by omega
  have hEul : IsEuler (8 * n + 3) := ⟨1, p, odd_one, hp, by rw [hpn]; ring⟩
  have hn1 : 1 ≤ n := by
    have : 1 ≤ M := le_trans (by omega) (le_max_right _ _)
    omega
  have hX := hN0 n (le_trans (le_max_left _ _) hnM)
  have hmem : n ∈ (Finset.Icc 1 n).filter (fun k => IsEuler (8 * k + 3)) := by
    simp [hn1, hEul]
  have hsingle : ((R n : ℕ) : ℝ) ^ 2 ≤ Finset.sum ((Finset.Icc 1 n).filter
      (fun k => IsEuler (8 * k + 3))) (fun k => (R k : ℝ) ^ 2) :=
    Finset.single_le_sum (f := fun k => (R k : ℝ) ^ 2) (fun _ _ => sq_nonneg _) hmem
  have hRn : R n = n := by simp [hRdef, hEul]
  rw [hRn] at hsingle
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  have hexp : Real.exp (b + 1) ≤ (n : ℝ) := by
    have h1 : Real.exp (b + 1) ≤ (⌈Real.exp (b + 1)⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : ⌈Real.exp (b + 1)⌉₊ ≤ n := le_trans (by omega) (le_trans (le_max_right _ _) hnM)
    have h3 : (⌈Real.exp (b + 1)⌉₊ : ℝ) ≤ n := by exact_mod_cast h2
    linarith
  have hlog : b + 1 ≤ Real.log n := by
    rw [Real.le_log_iff_exp_le hnpos]; exact hexp
  have hlog2 : b < Real.log n ^ 2 := by nlinarith
  have hL : 0 < Real.log n ^ 2 := by nlinarith
  have hlt : b * (n : ℝ) ^ 2 / Real.log n ^ 2 < (n : ℝ) ^ 2 := by
    rw [div_lt_iff₀ hL]
    have : 0 < (n : ℝ) ^ 2 := by positivity
    nlinarith
  linarith [hX, hsingle, hlt]

-- Faithfulness check: the negated Prop is exactly the type of `leaf_second_moment_card`.
#check (leaf_second_moment_card_false leaf_second_moment_card : False)

end LeanLab.OpenProblems.State1612

#print axioms LeanLab.OpenProblems.State1612.leaf_second_moment_card_false
