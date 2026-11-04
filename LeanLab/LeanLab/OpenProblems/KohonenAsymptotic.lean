import LeanLab.OpenProblems.SearchAdditive2Basis

/-!
# Kohonen's lower bound at every sufficiently large cardinality

AI wrote the Lean code. This is known mathematics. Goldbach remains OPEN.
No record improvement is claimed.

Source: J. Kohonen, An improved lower bound for finite additive 2-bases,
https://arxiv.org/abs/1606.04770, version 2, page 1 equation 1,
page 3 Theorem 1, and page 5 the passage to the asymptotic lower bound.
The sealed certificate gives size at most `42*t + 8` and coverage below
`510*t^2`. Those conservative finite bounds suffice for the printed
asymptotic coefficient `85/294`. Padding makes the cardinality exact.
-/

namespace LeanLab.OpenProblems.SearchAdditive2Basis

/-- At every cardinality at least fifty, round the parameter down and pad the basis. -/
theorem kohonen_cardinality_bound (k : ℕ) (hk : 50 ≤ k) :
    ∃ A : Finset ℕ, A.card = k ∧
      ∀ n < 510 * ((k - 8) / 42) ^ 2, ∃ a ∈ A, ∃ b ∈ A, a + b = n := by
  have ht : 0 < (k - 8) / 42 := by omega
  obtain ⟨B, hB, hcover⟩ := kohonen_certificate ((k - 8) / 42) ht
  have hsize : B.card ≤ k := by omega
  have hT : k ≤ (B ∪ Finset.range k).card := by
    simpa using Finset.card_le_card
      (Finset.subset_union_right : Finset.range k ⊆ B ∪ Finset.range k)
  obtain ⟨A, hBA, _, hA⟩ := Finset.exists_subsuperset_card_eq
    (Finset.subset_union_left : B ⊆ B ∪ Finset.range k) hsize hT
  refine ⟨A, hA, fun n hn => ?_⟩
  obtain ⟨a, ha, b, hb, hab⟩ := hcover n hn
  exact ⟨a, hBA ha, b, hBA hb, hab⟩

/-- Kohonen's asymptotic lower coefficient, expressed without an extremal-range definition.
For each positive epsilon, every sufficiently large exact cardinality has a basis
whose covered initial range is at least `85/294 - epsilon` times its cardinality squared. -/
theorem kohonen_asymptotic :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ k : ℕ in Filter.atTop,
      ∃ A : Finset ℕ, A.card = k ∧ ∃ n : ℕ,
        (85 / 294 - ε) * (k : ℝ) ^ 2 ≤ (n : ℝ) ∧
        ∀ m ≤ n, ∃ a ∈ A, ∃ b ∈ A, a + b = m := by
  intro ε hε
  obtain ⟨K, hK⟩ := exists_nat_ge (29 / ε)
  rw [Filter.eventually_atTop]
  refine ⟨max 50 K, fun k hk => ?_⟩
  have hk50 : 50 ≤ k := (le_max_left ..).trans hk
  have hKk : K ≤ k := (le_max_right ..).trans hk
  have hk0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hεk : 29 ≤ ε * (k : ℝ) := by
    have hr : 29 / ε ≤ (k : ℝ) := hK.trans (by exact_mod_cast hKk)
    have := (div_le_iff₀ hε).mp hr
    nlinarith
  let t := (k - 8) / 42
  have ht : 1 ≤ t := by dsimp [t]; omega
  have hcloseNat : k ≤ 42 * t + 49 := by dsimp [t]; omega
  have hclose : (k : ℝ) - 49 ≤ 42 * (t : ℝ) := by
    have hr : (k : ℝ) ≤ 42 * (t : ℝ) + 49 := by exact_mod_cast hcloseNat
    linarith
  have hk49 : (0 : ℝ) ≤ (k : ℝ) - 49 := by
    have hr : (50 : ℝ) ≤ k := by exact_mod_cast hk50
    linarith
  have hsq : ((k : ℝ) - 49) ^ 2 ≤ 1764 * (t : ℝ) ^ 2 := by
    have h := pow_le_pow_left₀ hk49 hclose 2
    nlinarith
  have hbudget : 29 * (k : ℝ) ≤ ε * (k : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hεk hk0
    nlinarith
  have hbound : (85 / 294 - ε) * (k : ℝ) ^ 2 ≤ 510 * (t : ℝ) ^ 2 - 1 := by
    nlinarith
  have hn : 1 ≤ 510 * t ^ 2 := by nlinarith
  have hcast : ((510 * t ^ 2 - 1 : ℕ) : ℝ) = 510 * (t : ℝ) ^ 2 - 1 := by
    rw [Nat.cast_sub hn]
    push_cast
    rfl
  obtain ⟨A, hA, hcover⟩ := kohonen_cardinality_bound k hk50
  refine ⟨A, hA, 510 * t ^ 2 - 1, ?_, fun m hm => ?_⟩
  · rwa [hcast]
  · exact hcover m (by dsimp [t] at *; omega)

end LeanLab.OpenProblems.SearchAdditive2Basis

#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.kohonen_cardinality_bound
#print axioms LeanLab.OpenProblems.SearchAdditive2Basis.kohonen_asymptotic
