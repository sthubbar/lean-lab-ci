/-
The case `S = {1}` of the lab class in Lemma 10 of J. Brudern and A. Perelli, Goldbach numbers
in sparse sequences, Ann. Inst. Fourier 48 (1998), p. 370-371, P0082, stated as
`KaracubaSplit.LeafS1Case`, proved here with no `sorry` and no named hypothesis, and the two
corollaries that make the route to `Lemma10` and `Theorem2` conditional only on the named
hypothesis `KaracubaThm1Named`, Karacuba 1971 Theorem 1, p. 244.

The proof assembles pieces that were already proved on the branch but never joined:
* `leaf_s1_deriv_sign` and `leaf_s1_small_N_boundary` of `SPLIT_leaf_s1_case`, proved;
* `leaf_s1_monotone_saving_split` of `SPLIT_leaf_s1_monotone_saving`, proved from
  `S1Saving.s1_saving_core` of `S1FirstDerivativeSaving1539`, which applies the lab theorem
  `kusmin_landau` of `LeanLab.BakerHarmanPintz1997.PortedVanDerCorput` to the Taylor
  polynomial of `f` on blocks of length about `N ^ ((θ + Θ₀) / 2)`, between the at most
  `k - 3` roots of its second derivative, so no monotonicity of `f'` is assumed.
The assembly below is the body of `leaf_s1_case_split` of `SPLIT_leaf_s1_case` with the open
leaf `leaf_s1_monotone_saving` replaced by its proved split.

AI wrote the Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.DQLemma10Decisions
import LeanLab.ExceptionalSet.SPLIT_leaf_s1_monotone_saving

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-- PROVED. `LeafS1Case`, the case `S = {1}` of the lab class, which Brudern-Perelli add to
Karacuba's class, P0082 p. 370-371. Below `N₀` the trivial bound, above it the first
derivative saving through Kusmin-Landau on Taylor blocks. -/
theorem leafS1Case_proved : LeafS1Case := by
  intro θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  obtain ⟨B₁, c₁, N₀, hB₁, hc₁, hN₀, hbig⟩ :=
    leaf_s1_monotone_saving_split θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1
  obtain ⟨B₂, _, hsmall⟩ :=
    leaf_s1_small_N_boundary θ Θ Θ₀ δ hδ0 hδ1 hΘ0 hΘθ hθΘ₀ hΘ₀1 (min c₁ 1) N₀
      (lt_min hc₁ one_pos) (min_le_right _ _) hN₀
  refine ⟨max B₁ B₂, min c₁ 1, lt_of_lt_of_le hB₁ (le_max_left _ _), lt_min hc₁ one_pos, ?_⟩
  intro N hN f k hk3 hsm hder hδk hf'
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  rcases lt_or_ge (N : ℝ) N₀ with hlt | hge
  · refine (hsmall N hN hlt f k hk3 hsm hder hδk hf').trans ?_
    exact mul_le_mul_of_nonneg_right (le_max_right B₁ B₂)
      (Real.rpow_nonneg (Nat.cast_nonneg N) _)
  · have hsgn := leaf_s1_deriv_sign N hN f k θ Θ hk3 hΘ0 hΘθ hsm hf'
    refine (hbig N hge f k hk3 hsm hder hδk hf' hsgn).trans ?_
    refine mul_le_mul (le_max_left B₁ B₂) ?_ (Real.rpow_nonneg (Nat.cast_nonneg N) _)
      (le_trans hB₁.le (le_max_left _ _))
    apply Real.rpow_le_rpow_of_exponent_le hNr
    have hk2 : (0 : ℝ) < (k : ℝ) ^ 2 := by
      have : (0 : ℝ) < (k : ℝ) := by
        have : (0 : ℕ) < k := by omega
        exact_mod_cast this
      positivity
    have hmin : min c₁ 1 / (k : ℝ) ^ 2 ≤ c₁ / (k : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right (min_le_left _ _) hk2.le
    linarith

end LeanLab.ExceptionalSet.U1539.KaracubaSplit

namespace LeanLab.ExceptionalSet.U1539.DQLemma10

open LeanLab.ExceptionalSet.U1539
open LeanLab.ExceptionalSet.U1539.KaracubaSplit

/-- CONDITIONAL ON `KaracubaThm1Named` only. Lemma 10 of Brudern-Perelli. -/
theorem lemma10_of_karacuba_named (hK : KaracubaThm1Named) : Lemma10 :=
  lemma10_of_named hK leafS1Case_proved

/-- CONDITIONAL ON `KaracubaThm1Named` only. Theorem 2 of Brudern-Perelli. -/
theorem theorem2_of_karacuba_named (hK : KaracubaThm1Named) : Theorem2 :=
  theorem2_of_named hK leafS1Case_proved

end LeanLab.ExceptionalSet.U1539.DQLemma10

#print axioms LeanLab.ExceptionalSet.U1539.KaracubaSplit.leafS1Case_proved
#print axioms LeanLab.ExceptionalSet.U1539.DQLemma10.lemma10_of_karacuba_named
#print axioms LeanLab.ExceptionalSet.U1539.DQLemma10.theorem2_of_karacuba_named
