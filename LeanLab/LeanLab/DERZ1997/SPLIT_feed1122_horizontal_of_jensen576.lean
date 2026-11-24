import LeanLab.DERZ1997.Decomp576a

/-!
Split of horizontal_of_jensen576 from Decomp576a.
Trudgian https://arxiv.org/abs/1206.1844v4 pages 4 to 7.
The phase lift, the zero-count argument bound, the paired Jensen inequality and the
limit in the power are all proved here or in Decomp576a.  The one open leaf is the
reflection pairing count of display 3.9 with the loose budget 1.5.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.DERZ1997.Decomp576a
open Complex Filter Topology MeasureTheory Set
open scoped ComplexConjugate

/-- LEAF: Trudgian page 6 display 3.9 with displays 3.10 and 3.11, the Gamma reflection
pairing count.  HARD.  For all large indices the zeros of the real-part power on the
open segment from one half to two are covered by a finite set whose size plus one is at
most the number of reflected zero pairs, in the shape required by the proved
partial_paired_zero_jensen585, plus the loose budget 1.5 times the power.  The budget
covers the Gamma reflection phase and the zeros between the pairing range and the right
endpoint 2.  No argument or Jensen mass appears in this leaf.
-/
theorem reflection_pairing_count_feed1122 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {T : ℝ} (hT : 1 ≤ |T|)
    (hgood : ∀ σ ∈ Icc (1 / 2 : ℝ) 2,
      DirichletCharacter.LFunction χ ((σ : ℂ) + (T : ℂ) * I) ≠ 0)
    (N : ℕ → ℕ) (hN : StrictMono N)
    (hcentre : Tendsto (fun k =>
      (DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + (T : ℂ) * I) ^ N k).re /
        ‖DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + (T : ℂ) * I)‖ ^ N k)
      atTop (𝓝 1)) :
    ∀ᶠ k in atTop, ∃ (S : Finset ℝ) (n : ℕ) (x y : Fin n → ℝ),
      (∀ σ ∈ Ioo (1 / 2 : ℝ) 2, realPartPower576 χ T (N k) (σ : ℂ) = 0 → σ ∈ S) ∧
      Function.Injective (Sum.elim x y) ∧
      (∀ i, 1 / 2 ≤ x i ∧ x i ≤ 1 / 2 + Real.sqrt 2 * (1 / 2 + 1 / 4)) ∧
      (∀ i, y i ≤ 1 / 2 ∧ 1 - x i ≤ y i) ∧
      (∀ i, realPartPower576 χ T (N k) (x i : ℂ) = 0) ∧
      (∀ i, realPartPower576 χ T (N k) (y i : ℂ) = 0) ∧
      (S.card : ℝ) + 1 ≤ (n : ℝ) + 1.5 * (N k : ℝ) := by
  sorry

/-- The real-part power is eventually nonzero at the Jensen centre.
Trudgian page 7, the centre normalization after display 4.2, from Rosser's power sequence.
-/
theorem centre_ne_zero_feed1122 {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (T : ℝ) (N : ℕ → ℕ)
    (hcentre : Tendsto (fun k =>
      (DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + (T : ℂ) * I) ^ N k).re /
        ‖DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + (T : ℂ) * I)‖ ^ N k)
      atTop (𝓝 1)) :
    ∀ᶠ k in atTop, realPartPower576 χ T (N k) (5 / 4 : ℂ) ≠ 0 := by
  filter_upwards [hcentre.eventually (lt_mem_nhds (by norm_num : (0 : ℝ) < 1))] with k hk
  intro h0
  have hr := realPartPower_real576 χ T (5 / 4 : ℝ) (N k)
  have hc : ((5 / 4 : ℝ) : ℂ) = (5 / 4 : ℂ) := by push_cast; ring
  rw [hc, h0] at hr
  have hre : (DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + (T : ℂ) * I) ^ N k).re = 0 := by
    have := congrArg Complex.re hr
    simpa using this.symm
  rw [hre, zero_div] at hk
  exact lt_irrefl _ hk

/-- Split of horizontal_of_jensen576, statement copied verbatim.
Trudgian pages 4 to 7, displays 2.7, 2.8, 3.9 and 4.2 to 4.3.
Proved from the reflection pairing leaf, horizontal_card_bound585,
partial_paired_zero_jensen585 and jensen_mass_mean585.
-/
theorem horizontal_of_jensen576_split {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (hne : χ ≠ 1)
    {T : ℝ} (hT : 1 ≤ |T|)
    (hgood : ∀ σ ∈ Icc (1 / 2 : ℝ) 2,
      DirichletCharacter.LFunction χ ((σ : ℂ) + (T : ℂ) * I) ≠ 0)
    (N : ℕ → ℕ) (hN : StrictMono N)
    (hcentre : Tendsto (fun k =>
      (DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + (T : ℂ) * I) ^ N k).re /
        ‖DirichletCharacter.LFunction χ ((5 / 4 : ℂ) + (T : ℂ) * I)‖ ^ N k)
      atTop (𝓝 1))
    {B : ℝ} (hB : ∀ ε > 0, ∀ᶠ k in atTop, jensenMass576 χ T (N k) ≤ B + ε) :
    |horizontal576 χ T| ≤ B + 1.5 := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hpos : ∀ᶠ k in atTop, 0 < N k := by
    filter_upwards [eventually_ge_atTop 1] with k hk
    exact lt_of_lt_of_le hk (hN.id_le k)
  obtain ⟨k, hpair, hm, hk, hc⟩ :=
    ((reflection_pairing_count_feed1122 χ hχ hne hT hgood N hN hcentre).and
      ((hB ε hε).and (hpos.and (centre_ne_zero_feed1122 χ T N hcentre)))).exists
  obtain ⟨S, n, x, y, hS, hinj, hx, hy, hfx, hfy, hcard⟩ := hpair
  have hh := Backlund585.horizontal_card_bound585 χ hne T hgood hk S hS
  have hj := Backlund585.partial_paired_zero_jensen585 (realPartPower576 χ T (N k))
    (realPartPower_differentiable576 χ hne T (N k)) hc x y hinj hx hy hfx hfy
  rw [← Backlund585.jensen_mass_mean585 χ T hk] at hj
  have hlog : 0 < Real.log (12 / 7 : ℝ) := Real.log_pos (by norm_num)
  have hNr : (0 : ℝ) < N k := Nat.cast_pos.mpr hk
  have hn : (n : ℝ) ≤ (N k : ℝ) * jensenMass576 χ T (N k) := by
    simp only [Fintype.card_fin] at hj
    nlinarith
  have hq : ((S.card : ℝ) + 1) / N k ≤ jensenMass576 χ T (N k) + 1.5 := by
    rw [div_le_iff₀ hNr]
    nlinarith
  linarith

end LeanLab.DERZ1997.Decomp576a
