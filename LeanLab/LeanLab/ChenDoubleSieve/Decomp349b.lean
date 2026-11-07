import LeanLab.ChenDoubleSieve.Decomp349a

/-!
Supply split for the switched upper bounds in Wu 2004.
Source: https://arxiv.org/pdf/0705.1652, pages 39 to 41 equations 10.6 to 10.11.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- The ordered prime pair domain for the three switched coordinates.
Coordinate nine retains its crossing lower cut at sigma two. -/
def switchedPairs (N : ℕ) (i : Fin 12) : Finset (ℕ × ℕ) :=
  Wu08Sum.P2 N (fun p q =>
    (if i = 6 then (N : ℝ) ^ sigma1 ≤ p else
      if i = 7 then (N : ℝ) ^ sigma2 ≤ p else
        (N : ℝ) ^ kappa2 ≤ p ∧ (p : ℝ) < (N : ℝ) ^ sigma2 ∧
          (N : ℝ) ^ sigma2 ≤ q) ∧
    p < q ∧ (q : ℝ) < sqrt ((N : ℝ) / p))

/-- The finite reciprocal logarithmic main term of equation 10.9.
The factor N is retained outside the sum in switchedMain. -/
def switchedSum (N : ℕ) (i : Fin 12) : ℝ :=
  ∑ q ∈ switchedPairs N i,
    1 / (((q.1 : ℝ) * q.2) * log ((N : ℝ) / ((q.1 : ℝ) * q.2)))

/-- The switched main term before prime partial summation. -/
def switchedMain (N : ℕ) (i : Fin 12) : ℝ :=
  8 * CN N * N / log N * switchedSum N i

/-- LEAF. Wu 2004 pages 40 and 41 equations 10.6 to 10.8 and 10.11.
Only the switched sieve comparison is asserted, with the uniform li replacement.
No limiting integral coefficient occurs. -/
theorem switched_finite_upper :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
          sieveTerms N i ≤ switchedMain N i + η * Θ N := by
  sorry

/-- LEAF. Wu 2004 page 41 equation 10.9 and its analogues in 10.11.
Only the finite prime sum limit is asserted. There is no actual sieve count.
The coprimality restriction is removed within this limit. -/
theorem switched_sum_tendsto :
    ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
      Tendsto (fun N : ℕ => 8 * log N * switchedSum N i) evenAtTop
        (𝓝 (integralTerms (fun _ => 0) (fun _ => 0) (fun _ => 0) i)) := by
  sorry

/-- Exact normalization of the finite switched main term. -/
theorem switchedMain_ratio {N : ℕ} (hN : 2 ≤ N) (i : Fin 12) :
    switchedMain N i / Θ N = 8 * log N * switchedSum N i := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  unfold switchedMain Θ
  field_simp [(CN_pos N).ne', hn.ne', hl.ne']
  <;> ring

set_option maxHeartbeats 2000000 in
/-- The switched integral coefficients do not depend on the three functions. -/
theorem switched_integral_independent (F f ω : ℝ → ℝ) (i : Fin 12)
    (hi : i ∈ ({6, 7, 9} : Finset (Fin 12))) :
    integralTerms F f ω i =
      integralTerms (fun _ => 0) (fun _ => 0) (fun _ => 0) i := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl <;>
    norm_num [integralTerms]

/-- The square root boundary forces a positive remaining prime logarithm. -/
theorem pair_remaining_log_pos {x p q : ℝ} (hp : 0 < p) (hq : 1 ≤ q)
    (hboundary : q < sqrt (x / p)) : 0 < log (x / (p * q)) := by
  have hq0 : 0 ≤ q := by linarith
  have hsq : q ^ 2 < x / p := (Real.lt_sqrt hq0).mp hboundary
  have hmul : q ^ 2 * p < x := (lt_div_iff₀ hp).mp hsq
  have hq2 : q ≤ q ^ 2 := by nlinarith
  have hprod : p * q < x := by
    have hm := mul_le_mul_of_nonneg_left hq2 hp.le
    nlinarith
  apply Real.log_pos
  exact (one_lt_div (mul_pos hp (by linarith))).mpr hprod

/-- Every switched pair has prime coordinates and the printed square root cut. -/
theorem switchedPairs_properties {N : ℕ} {i : Fin 12} {p : ℕ × ℕ}
    (hp : p ∈ switchedPairs N i) :
    p.1.Prime ∧ p.2.Prime ∧ p.1.Coprime N ∧ p.2.Coprime N ∧
      p.1 < p.2 ∧ (p.2 : ℝ) < sqrt ((N : ℝ) / p.1) := by
  have hmem := hp
  simp only [switchedPairs, Wu08Sum.P2, Finset.mem_filter] at hmem
  have hs := hmem.2
  exact ⟨hs.1, hs.2.1, hs.2.2.1, hs.2.2.2.1,
    hs.2.2.2.2.2.1, hs.2.2.2.2.2.2⟩

/-- The finite switched prime sum is nonnegative without an analytic sieve input. -/
theorem switchedSum_nonneg (N : ℕ) (i : Fin 12) : 0 ≤ switchedSum N i := by
  apply Finset.sum_nonneg
  intro p hp
  have hs := switchedPairs_properties hp
  have hp0 : (0 : ℝ) < p.1 := by exact_mod_cast hs.1.pos
  have hq1 : (1 : ℝ) ≤ p.2 := by exact_mod_cast hs.2.1.one_lt.le
  have hl := pair_remaining_log_pos hp0 hq1 hs.2.2.2.2.2
  exact one_div_nonneg.mpr (mul_nonneg (by positivity) hl.le)

/-- The finite switched main term is nonnegative on the natural numbers. -/
theorem switchedMain_nonneg (N : ℕ) (i : Fin 12) : 0 ≤ switchedMain N i := by
  have hc := (CN_pos N).le
  have hs := switchedSum_nonneg N i
  unfold switchedMain
  exact mul_nonneg (div_nonneg (by positivity) (Real.log_natCast_nonneg N)) hs

/-- The exact sealed switched_upper conclusion from two smaller leaves.
OPEN through switched_finite_upper and switched_sum_tendsto. -/
theorem switched_upper_supplied (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
        sieveTerms N i ≤ (integralTerms F f ω i + ε) * Θ N := by
  apply finite_upper_threshold
  intro i hi
  apply upper_of_main _ _ (fun _ N => switchedMain N i)
  · intro η hη
    obtain ⟨M, hM⟩ := switched_finite_upper η hη
    exact ⟨1, by norm_num, M, fun N hEven hN => hM N hEven hN i hi⟩
  · intro B hB
    rw [switched_integral_independent F f ω i hi]
    apply (switched_sum_tendsto i hi).congr'
    filter_upwards [(eventually_ge_atTop (2 : ℕ)).filter_mono inf_le_left] with N hN
    exact (switchedMain_ratio hN i).symm

end LeanLab.ChenDoubleSieve.Task349
