/-
P0085 Alsetri 2025, arXiv 2505.09648, Lemma 2.1 (intended form, 1/2 replacing Shao's 5/8) in
the case n = 6: for 1 ≥ a₀ ≥ … ≥ a₅ ≥ 0, if aᵢaⱼ + aⱼaₖ + aₖaᵢ ≤ 1/2 (aᵢ + aⱼ + aₖ) whenever
i + j + k ≥ 6, then a₀ + … + a₅ ≤ 3. The paper's proof splits into eight regions; here a
degree-4 Positivstellensatz certificate (found by linear programming, 43 products of the
hypotheses and squares, exact rational coefficients) is checked by `linarith`.
Then Alsetri Prop 3.1 at the prime 7 (`half31_seven`), as in Shao's `prop31_prime`.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
-/
import LeanLab.DensityGoldbach.AlsetriProp31

open Finset
open scoped Pointwise

namespace LeanLab.DensityGoldbach

/-- The real core of the `n = 6` case. -/
lemma half21_six_core (a0 a1 a2 a3 a4 a5 : ℝ) (h0 : a0 ≤ 1) (h5 : 0 ≤ a5)
    (d0 : a1 ≤ a0) (d1 : a2 ≤ a1) (d2 : a3 ≤ a2) (d3 : a4 ≤ a3) (d4 : a5 ≤ a4)
    (g015 : a0 * a1 + a1 * a5 + a5 * a0 ≤ 1 / 2 * (a0 + a1 + a5))
    (g024 : a0 * a2 + a2 * a4 + a4 * a0 ≤ 1 / 2 * (a0 + a2 + a4))
    (g025 : a0 * a2 + a2 * a5 + a5 * a0 ≤ 1 / 2 * (a0 + a2 + a5))
    (g033 : a0 * a3 + a3 * a3 + a3 * a0 ≤ 1 / 2 * (a0 + a3 + a3))
    (g044 : a0 * a4 + a4 * a4 + a4 * a0 ≤ 1 / 2 * (a0 + a4 + a4))
    (g055 : a0 * a5 + a5 * a5 + a5 * a0 ≤ 1 / 2 * (a0 + a5 + a5))
    (g114 : a1 * a1 + a1 * a4 + a4 * a1 ≤ 1 / 2 * (a1 + a1 + a4))
    (g115 : a1 * a1 + a1 * a5 + a5 * a1 ≤ 1 / 2 * (a1 + a1 + a5))
    (g144 : a1 * a4 + a4 * a4 + a4 * a1 ≤ 1 / 2 * (a1 + a4 + a4))
    (g222 : a2 * a2 + a2 * a2 + a2 * a2 ≤ 1 / 2 * (a2 + a2 + a2))
    (g444 : a4 * a4 + a4 * a4 + a4 * a4 ≤ 1 / 2 * (a4 + a4 + a4))
    (g455 : a4 * a5 + a5 * a5 + a5 * a4 ≤ 1 / 2 * (a4 + a5 + a5))
    (g555 : a5 * a5 + a5 * a5 + a5 * a5 ≤ 1 / 2 * (a5 + a5 + a5)) :
    a0 + a1 + a2 + a3 + a4 + a5 ≤ 3 := by
  have h2 : a2 ≤ 1 / 2 := by nlinarith
  linarith [mul_nonneg (sub_nonneg.2 g015) (sub_nonneg.2 d1),
    mul_nonneg (sub_nonneg.2 g015) (sub_nonneg.2 d2),
    mul_nonneg (sub_nonneg.2 g015) (sub_nonneg.2 d3),
    mul_nonneg (sub_nonneg.2 g015) (sub_nonneg.2 d4),
    mul_nonneg (sub_nonneg.2 g015) h5,
    mul_nonneg (sub_nonneg.2 g024) (sub_nonneg.2 d4),
    mul_nonneg (sub_nonneg.2 g024) h5,
    mul_nonneg (sub_nonneg.2 g025) h5,
    mul_nonneg (sub_nonneg.2 g044) (sub_nonneg.2 h2),
    mul_nonneg (sub_nonneg.2 g055) (sub_nonneg.2 h2),
    mul_nonneg (sub_nonneg.2 g114) (sub_nonneg.2 d2),
    mul_nonneg (sub_nonneg.2 g114) (sub_nonneg.2 d3),
    mul_nonneg (sub_nonneg.2 g114) (sub_nonneg.2 d4),
    mul_nonneg (sub_nonneg.2 g114) (sub_nonneg.2 h0),
    mul_nonneg (sub_nonneg.2 g114) (sub_nonneg.2 h2),
    mul_nonneg (sub_nonneg.2 g115) (sub_nonneg.2 h0),
    mul_nonneg (sub_nonneg.2 g144) (sub_nonneg.2 h0),
    mul_nonneg (sub_nonneg.2 g444) (sub_nonneg.2 h0),
    mul_nonneg (sub_nonneg.2 g444) (sub_nonneg.2 h2),
    mul_nonneg (sub_nonneg.2 g455) (sub_nonneg.2 h0),
    mul_nonneg (sub_nonneg.2 g555) (sub_nonneg.2 d0),
    mul_nonneg (sub_nonneg.2 g555) (sub_nonneg.2 h0),
    mul_nonneg (sub_nonneg.2 g555) (sub_nonneg.2 h2),
    mul_nonneg (sub_nonneg.2 d0) (sub_nonneg.2 d1),
    mul_nonneg (sub_nonneg.2 d0) (sub_nonneg.2 h0),
    mul_nonneg (sub_nonneg.2 d1) (sub_nonneg.2 h2),
    mul_nonneg (sub_nonneg.2 d2) (sub_nonneg.2 h0),
    mul_nonneg (sub_nonneg.2 d2) (sub_nonneg.2 h2),
    mul_nonneg (sub_nonneg.2 d3) (sub_nonneg.2 h0),
    mul_nonneg (sub_nonneg.2 d3) (sub_nonneg.2 h2),
    mul_nonneg (sub_nonneg.2 d4) h5,
    mul_nonneg (sub_nonneg.2 d4) (sub_nonneg.2 h0),
    mul_nonneg (sub_nonneg.2 d4) (sub_nonneg.2 h2),
    mul_nonneg (sub_nonneg.2 h0) (sub_nonneg.2 h2),
    sq_nonneg (a0 + a5 - 1),
    sq_nonneg (a1 + a4 - 1),
    sq_nonneg (a1 + a5 - 1),
    sq_nonneg (a2 + a3 - 1),
    sq_nonneg (2 * a3 - 1)]

/-- **Alsetri Prop 3.1 at the prime 7**: sort `f`, the `n = 6` lemma contrapositively, then
superlevel sets and Cauchy-Davenport. -/
theorem half31_seven : Half31 7 := by
  have hp : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  intro f hf hsum x
  set U := unitsMod 7 with hU
  have hn : #U = 6 := card_unitsMod_prime 7
  rw [Nat.totient_prime hp.out] at hsum
  obtain ⟨a, hbd, hmo, hasum, hlev⟩ := sort_seq U f hf
  rw [hn] at hbd hmo hasum hlev
  obtain ⟨i, j, k, hi, hj, hk, hs, hlt⟩ : ∃ i j k, i < 6 ∧ j < 6 ∧ k < 6 ∧
      6 ≤ i + j + k ∧ 1 / 2 * (a i + a j + a k) < a i * a j + a j * a k + a k * a i := by
    by_contra hne
    push Not at hne
    have g := fun i j k (hs : 6 ≤ i + j + k) (hi : i < 6) (hj : j < 6) (hk : k < 6) =>
      hne i j k hi hj hk hs
    have c := half21_six_core (a 0) (a 1) (a 2) (a 3) (a 4) (a 5) (hbd 0 (by omega)).2
      (hbd 5 (by omega)).1 (hmo 0 1 (by omega) (by omega)) (hmo 1 2 (by omega) (by omega))
      (hmo 2 3 (by omega) (by omega)) (hmo 3 4 (by omega) (by omega))
      (hmo 4 5 (by omega) (by omega))
      (g 0 1 5 (by omega) (by omega) (by omega) (by omega))
      (g 0 2 4 (by omega) (by omega) (by omega) (by omega))
      (g 0 2 5 (by omega) (by omega) (by omega) (by omega))
      (g 0 3 3 (by omega) (by omega) (by omega) (by omega))
      (g 0 4 4 (by omega) (by omega) (by omega) (by omega))
      (g 0 5 5 (by omega) (by omega) (by omega) (by omega))
      (g 1 1 4 (by omega) (by omega) (by omega) (by omega))
      (g 1 1 5 (by omega) (by omega) (by omega) (by omega))
      (g 1 4 4 (by omega) (by omega) (by omega) (by omega))
      (g 2 2 2 (by omega) (by omega) (by omega) (by omega))
      (g 4 4 4 (by omega) (by omega) (by omega) (by omega))
      (g 4 5 5 (by omega) (by omega) (by omega) (by omega))
      (g 5 5 5 (by omega) (by omega) (by omega) (by omega))
    simp only [sum_range_succ, sum_range_zero, zero_add] at hasum
    norm_num at hsum
    linarith
  have huniv := three_levels 7 _ _ _ i j k (hlev i hi) (hlev j hj) (hlev k hk) (by omega)
  have hx : x ∈ U.filter (fun u => a i ≤ f u) + U.filter (fun u => a j ≤ f u) +
      U.filter (fun u => a k ≤ f u) := by rw [huniv]; exact mem_univ x
  obtain ⟨y, hy, z3, hz3, rfl⟩ := mem_add.1 hx
  obtain ⟨z1, hz1, z2, hz2, rfl⟩ := mem_add.1 hy
  obtain ⟨hz1U, hz1f⟩ := mem_filter.1 hz1
  obtain ⟨hz2U, hz2f⟩ := mem_filter.1 hz2
  obtain ⟨hz3U, hz3f⟩ := mem_filter.1 hz3
  have hh : 0 < hhalf (a i) (a j) (a k) := by unfold hhalf; linarith
  exact ⟨z1, hz1U, z2, hz2U, z3, hz3U, rfl, hhalf_mono _ _ _ _ _ _ (hbd i hi).1 (hbd j hj).1
    (hbd k hk).1 (hf _).2 (hf _).2 (hf _).2 hz1f hz2f hz3f hh⟩

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.half31_seven
