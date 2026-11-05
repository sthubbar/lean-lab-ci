import LeanLab.ChenDoubleSieve.Decomp367b
import LeanLab.ChenDoubleSieve.Decomp363c

/-!
Totient mass and logarithmic integral replacement for the finite F5 main term.
Source: https://arxiv.org/pdf/0705.1652, pages 38 and 39 equation 10.5.
No two dimensional integral limit or lower sieve leaf is used.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task367
open Task275 Task348
open Wu04Functional (IsLinearSieve)

/-- The total reciprocal totient mass of the actual F5 pair domain. -/
def lowerTotientMass5 (N : ℕ) : ℝ :=
  ∑ p ∈ lowerPairs5 N, 1 / (Nat.totient (p.1 * p.2) : ℝ)

/-- The actual reciprocal totient mass is nonnegative. -/
theorem lowerTotientMass5_nonneg (N : ℕ) : 0 ≤ lowerTotientMass5 N := by
  exact sum_nonneg (by intros; positivity)

/-- The actual reciprocal totient mass is controlled by the full reciprocal pair mass. -/
theorem lowerTotientMass5_le (N : ℕ) :
    lowerTotientMass5 N ≤ 4 * pairMass (fullPairs5 N) := by
  have hsub : lowerPairs5 N ⊆ fullPairs5 N := by
    rw [lowerPairs5_eq_filter]
    exact filter_subset _ _
  calc
    _ ≤ ∑ p ∈ lowerPairs5 N, 4 * (1 / ((p.1 : ℝ) * p.2)) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hp1, hp2, hne⟩ := fullPairs5_primes (hsub hp)
      simpa only [div_eq_mul_inv, one_mul] using reciprocal_totient_pair hp1 hp2 hne
    _ = 4 * pairMass (lowerPairs5 N) := by simp only [pairMass, mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (pairMass_mono hsub) (by norm_num)

/-- One positive constant bounds the actual reciprocal totient mass on the tail. -/
theorem lowerTotientMass5_bounded : ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ,
    ∀ N : ℕ, N0 ≤ N → lowerTotientMass5 N ≤ K := by
  obtain ⟨K, hK, M, hM⟩ := fullPairs5_mass_bounded
  refine ⟨4 * K, by positivity, M, ?_⟩
  intro N hN
  exact (lowerTotientMass5_le N).trans (by gcongr; exact hM N hN)

/-- The actual lower sieve prime sum is bounded without an integral limit.
CONDITIONAL ON IsLinearSieve only. -/
theorem lowerSum5_bounded (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) : ∃ K : ℝ, 0 < K ∧ ∃ N0 : ℕ,
      ∀ N : ℕ, N0 ≤ N → |lowerSum5 f B N| ≤ K := by
  obtain ⟨M, hM, J, hJ⟩ := lower_values_bounded F f h B hB
  obtain ⟨K, hK, L, hL⟩ := lowerTotientMass5_bounded
  refine ⟨M * K + 1, by positivity, max J L, ?_⟩
  intro N hN
  have hsub : lowerPairs5 N ⊆ fullPairs5 N := by
    rw [lowerPairs5_eq_filter]
    exact filter_subset _ _
  calc
    _ ≤ ∑ p ∈ lowerPairs5 N, |f (lowerLevel B N (p.1 * p.2)) /
        (Nat.totient (p.1 * p.2) : ℝ)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ lowerPairs5 N, M * (1 / (Nat.totient (p.1 * p.2) : ℝ)) := by
      apply sum_le_sum
      intro p hp
      obtain ⟨hd, hb⟩ := fullPairs5_product (hsub hp)
      rw [abs_div, abs_of_nonneg (show (0 : ℝ) ≤ (Nat.totient (p.1 * p.2) : ℝ) from Nat.cast_nonneg _)]
      simpa only [div_eq_mul_inv, one_mul] using
        div_le_div_of_nonneg_right (hJ N (by omega) _ hd hb) (Nat.cast_nonneg _)
    _ = M * lowerTotientMass5 N := by simp only [lowerTotientMass5, mul_sum]
    _ ≤ M * K := mul_le_mul_of_nonneg_left (hL N (by omega)) hM
    _ ≤ M * K + 1 := by linarith

/-- The li form of the finite F5 main term in Lemma 2.2. -/
def liMain5 (f : ℝ → ℝ) (B : ℝ) (N : ℕ) : ℝ :=
  Wu04.li N * lowerDensity N * lowerSum5 f B N

/-- The exact li replacement factors as a scalar relative error times the main term. -/
theorem liMain5_difference (f : ℝ → ℝ) (B : ℝ) {N : ℕ} (hN : 2 ≤ N) :
    main5 f B N - liMain5 f B N =
      (1 - Wu04.li N / ((N : ℝ) / log N)) *
        ((N : ℝ) / log N * lowerDensity N) * lowerSum5 f B N := by
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hlog : log (N : ℝ) ≠ 0 :=
    (log_pos (by exact_mod_cast (show 1 < N by omega))).ne'
  unfold main5 liMain5
  field_simp [hpos.ne', hlog]

/-- Replacing li by N over log N costs an arbitrarily small Theta budget.
CONDITIONAL ON IsLinearSieve only. -/
theorem liMain5_error_absorbed (F f : ℝ → ℝ) (h : IsLinearSieve F f)
    (B : ℝ) (hB : 0 < B) (η : ℝ) (hη : 0 < η) : ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      |main5 f B N - liMain5 f B N| ≤ η * Θ N := by
  obtain ⟨K, hK, M, hM⟩ := lowerSum5_bounded F f h B hB
  obtain ⟨L, hL, J, hJ⟩ := Task363.density_scale_bounded
  have hli : Tendsto (fun N : ℕ => |1 - Wu04.li N / ((N : ℝ) / log N)|)
      atTop (𝓝 0) := by
    simpa only [Function.comp_def, sub_self, abs_zero] using
      ((Task363.li_ratio_tendsto.comp tendsto_natCast_atTop_atTop).const_sub 1).abs
  obtain ⟨T, hT⟩ := eventually_atTop.1
    (hli.eventually (eventually_lt_nhds (show 0 < η / (L * K) by positivity)))
  refine ⟨max 2 (max M (max J T)), ?_⟩
  intro N hEven hN
  have hN2 : 2 ≤ N := by omega
  have ht : 0 < Θ N := Θ_pos hN2
  have hlog : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hscale : 0 ≤ (N : ℝ) / log N * lowerDensity N :=
    mul_nonneg (by positivity) (lowerDensity_pos hEven).le
  rw [liMain5_difference f B hN2, abs_mul, abs_mul, abs_of_nonneg hscale]
  calc
    _ ≤ (η / (L * K)) * (L * Θ N) * K := by
      apply mul_le_mul
      · exact mul_le_mul (hT N (by omega)).le (hJ N hEven (by omega)) hscale (by positivity)
      · exact hM N (by omega)
      · exact abs_nonneg _
      · positivity
    _ = η * Θ N := by field_simp

end LeanLab.ChenDoubleSieve.Task367
