import LeanLab.ChenDoubleSieve.Decomp363e
import LeanLab.ChenDoubleSieve.Decomp348d
import LeanLab.ChenDoubleSieve.NormalizerPositive

/-!
Quantitative error preparation for the OPEN lower sieve input.
Source: https://arxiv.org/pdf/0705.1652, page 6 after equation 2.5.
The signed sieve estimate remains an explicit hypothesis.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task392
open Task275 Task348 Task363

/-- The explicit error majorant printed after equations 2.4 and 2.5. -/
def sieveError (ε K B : ℝ) (N : ℕ) : ℝ :=
  ε + ε ^ (-8 : ℤ) * exp K / (log (sieveLevel B N)) ^ (1 / 3 : ℝ)

/-- The logarithm of the actual finite level tends to infinity for every fixed B. -/
theorem log_sieveLevel_tendsto (B : ℝ) :
    Tendsto (fun N : ℕ => log (sieveLevel B N)) atTop atTop := by
  obtain ⟨M, hM⟩ := sieveLevel_eventually_admissible B
  have ht : Tendsto (fun N : ℕ => (1 / 6 : ℝ) * log (N : ℝ)) atTop atTop :=
    Tendsto.const_mul_atTop (by norm_num)
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  apply tendsto_atTop_mono' atTop _ ht
  filter_upwards [eventually_ge_atTop (max 2 M)] with N hN
  have hpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hle := (hM N (by omega)).2
  have hlog := log_le_log (by positivity : 0 < ((N : ℝ) ^ kappa1) ^ 2) hle
  rw [log_pow, log_rpow hpos] at hlog
  norm_num [kappa1] at hlog
  linarith

/-- At fixed epsilon and K, the explicit error majorant tends to epsilon. -/
theorem sieveError_tendsto (ε K B : ℝ) :
    Tendsto (sieveError ε K B) atTop (𝓝 ε) := by
  have ht := ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 3)).comp
    (log_sieveLevel_tendsto B)).const_div_atTop (ε ^ (-8 : ℤ) * exp K)
  change Tendsto (fun N : ℕ => ε + ε ^ (-8 : ℤ) * exp K /
    (log (sieveLevel B N)) ^ (1 / 3 : ℝ)) atTop (𝓝 ε)
  simpa only [Function.comp_def, add_zero] using ht.const_add ε

/-- Epsilon can be chosen before B so every fixed B eventually fits any positive budget. -/
theorem sieveError_budget (K A δ : ℝ) (hA : 0 ≤ A) (hδ : 0 < δ) :
    ∃ ε : ℝ, 0 < ε ∧ ε < 1 / 8 ∧
      ∀ B : ℝ, ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → A * sieveError ε K B N ≤ δ := by
  let ε : ℝ := min (1 / 16) (δ / (2 * (A + 1)))
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε8 : ε < 1 / 8 := (min_le_left _ _).trans_lt (by norm_num)
  have hεA : A * ε < δ := by
    have he : ε ≤ δ / (2 * (A + 1)) := min_le_right _ _
    have hb : A * (δ / (2 * (A + 1))) < δ := by
      rw [← mul_div_assoc, div_lt_iff₀ (by positivity : 0 < 2 * (A + 1))]
      nlinarith
    exact (mul_le_mul_of_nonneg_left he hA).trans_lt hb
  refine ⟨ε, hε, hε8, ?_⟩
  intro B
  have ht := (sieveError_tendsto ε K B).const_mul A
  obtain ⟨N0, hN0⟩ := eventually_atTop.1 (ht.eventually (gt_mem_nhds hεA))
  exact ⟨N0, fun N hN => (hN0 N hN).le⟩

/-- The quantitative signed form of equation 2.5 implies the exact raw lower
sieve target. The construction of the rows is an explicit analytic premise. -/
theorem lower_sieve_of_quantitative (f : ℝ → ℝ)
    (hquant : ∃ K A : ℝ, 0 ≤ A ∧
      ∀ ε : ℝ, 0 < ε → ε < 1 / 8 → ∃ L : ℕ,
        ∀ B : ℝ, 0 < B → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
          ∃ E : ℝ, ∃ weights : ℕ → ℕ → ℝ,
            |E| ≤ A * sieveError ε K B N ∧
            (∀ l ∈ range L, ∀ q ∈ remainderModuli B N, |weights l q| ≤ 1) ∧
            liMain0 f B N + (Wu04.li N * lowerDensity N) * E -
              (∑ l ∈ range L, ∑ q ∈ remainderModuli B N,
                weights l q * ((#((primeSequence N).filter (fun a => q ∣ a)) : ℝ) -
                  Wu04.li N / (q.totient : ℝ))) ≤ sieveTerms N 0) :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ B : ℝ, 0 < B → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
        liMain0 f B N - δ * (Wu04.li N * lowerDensity N) -
          C * rawRemainder B N ≤ sieveTerms N 0 := by
  obtain ⟨K, A, hA, hquant⟩ := hquant
  intro δ hδ
  obtain ⟨ε, hε, hε8, hbudget⟩ := sieveError_budget K A δ hA hδ
  obtain ⟨L, hL⟩ := hquant ε hε hε8
  refine ⟨L, by positivity, ?_⟩
  intro B hB
  obtain ⟨M, hM⟩ := hbudget B
  obtain ⟨J, hJ⟩ := hL B hB
  refine ⟨max 3 (max M J), ?_⟩
  intro N hEven hN
  obtain ⟨E, weights, hE, hweights, hs⟩ := hJ N hEven (by omega)
  have hd : 0 ≤ Wu04.li N * lowerDensity N :=
    mul_nonneg (Wu04.li_positive (by exact_mod_cast (show 2 < N by omega))).le
      (lowerDensity_pos hEven).le
  have hEδ : -δ ≤ E := by
    have hb := hM N (by omega)
    have he := neg_abs_le E
    linarith
  have he := mul_le_mul_of_nonneg_left hEδ hd
  have hr := (le_abs_self _).trans (rows_remainder_bound B N (range L) weights hweights)
  simp only [card_range] at hr
  nlinarith only [hs, he, hr]

/-- The generic quantitative implication has a satisfiable zero function
instance. This is a hypothesis check, not a linear sieve pair. -/
theorem lower_sieve_zero_instance :
    ∀ δ : ℝ, 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
      ∀ B : ℝ, 0 < B → ∃ N0 : ℕ, ∀ N : ℕ, Even N → N0 ≤ N →
        liMain0 (fun _ => 0) B N - δ * (Wu04.li N * lowerDensity N) -
          C * rawRemainder B N ≤ sieveTerms N 0 := by
  apply lower_sieve_of_quantitative
  refine ⟨1, 0, by norm_num, ?_⟩
  intro ε hε hε8
  refine ⟨0, ?_⟩
  intro B hB
  refine ⟨0, ?_⟩
  intro N hEven hN
  refine ⟨0, (fun _ _ => 0), ?_, ?_, ?_⟩
  · simp
  · intro l hl
    simp at hl
  · simp [liMain0, sieveTerms]

end LeanLab.ChenDoubleSieve.Task392
