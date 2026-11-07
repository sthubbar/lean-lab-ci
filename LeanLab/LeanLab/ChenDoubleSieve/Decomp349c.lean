import LeanLab.ChenDoubleSieve.Decomp349b
import LeanLab.ChenDoubleSieve.Decomp367d

/-!
Supply split for the refined upper bounds in Wu 2004.
Source: https://arxiv.org/pdf/0705.1652, page 41 equation 10.12.
The first prime cutoff and the Buchstab argument are retained in finite sums.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- The improved switched weight below the one tenth first prime cutoff. -/
def refinedWeight (N p : ℕ) : ℝ :=
  if (p : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) then
    (36 / 5 : ℝ) / (1 - log p / log N) else 8

/-- The crossing prime pair domain for Upsilon nine. -/
def refinedPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  Wu08Sum.P2 N (fun p q => (N : ℝ) ^ kappa1 ≤ p ∧
    (p : ℝ) < (N : ℝ) ^ sigma1 ∧ (N : ℝ) ^ sigma1 ≤ q ∧
    (q : ℝ) < sqrt ((N : ℝ) / p))

/-- The two actual ordered four prime domains from Upsilon thirteen and fourteen. -/
def refinedQuads (N : ℕ) (i : Fin 12) : Finset (ℕ × ℕ × ℕ × ℕ) :=
  Wu08Sum.P4 N (fun p q r s => (N : ℝ) ^ kappa1 ≤ p ∧ p < q ∧ q < r ∧
    (if i = 10 then r < s ∧ (s : ℝ) < (N : ℝ) ^ kappa2 else
      (r : ℝ) < (N : ℝ) ^ kappa2 ∧ (N : ℝ) ^ kappa2 ≤ s ∧
        (s : ℝ) < (N : ℝ) ^ (1 / 2 - 2 * kappa1) / r))

/-- The four forced prime product, embedded in the reals. -/
def quadProduct (q : ℕ × ℕ × ℕ × ℕ) : ℝ :=
  (q.1 : ℝ) * q.2.1 * q.2.2.1 * q.2.2.2

/-- The finite refined main sum, before prime partial summation.
The pair coordinate uses the remaining prime logarithm.
The quadruple coordinates use the second prime logarithm and Buchstab factor. -/
def refinedSum (ω : ℝ → ℝ) (N : ℕ) (i : Fin 12) : ℝ :=
  if i = 8 then
    ∑ q ∈ refinedPairs N, refinedWeight N q.1 /
      (((q.1 : ℝ) * q.2) * log ((N : ℝ) / ((q.1 : ℝ) * q.2)))
  else
    ∑ q ∈ refinedQuads N i, refinedWeight N q.1 *
      ω (log ((N : ℝ) / quadProduct q) / log q.2.1) /
        (quadProduct q * log q.2.1)

/-- The finite refined main term for equation 10.12. -/
def refinedMain (ω : ℝ → ℝ) (N : ℕ) (i : Fin 12) : ℝ :=
  CN N * N / log N * refinedSum ω N i

/-- LEAF. Wu 2004 page 41 equation 10.12, Lemmas 2.6 and 2.10.
The refined sieve estimate retains a finite prime sum, not an integral.
Uniform prime and rough number count errors belong to this estimate. -/
theorem refined_finite_upper (ω : ℝ → ℝ) (hω : IsBuchstab ω) :
    ∀ η : ℝ, 0 < η → ∃ N0 : ℕ,
      ∀ N : ℕ, Even N → N0 ≤ N →
        ∀ i : Fin 12, i ∈ ({8, 10, 11} : Finset (Fin 12)) →
          sieveTerms N i ≤ refinedMain ω N i + η * Θ N := by
  sorry

/-- LEAF. Wu 2004 page 41 equation 10.12, prime partial summation.
The one tenth split produces the two printed integral pieces.
There is no actual sieve count in this limit. -/
theorem refined_sum_tendsto (F f ω : ℝ → ℝ) (hω : IsBuchstab ω) :
    ∀ i : Fin 12, i ∈ ({8, 10, 11} : Finset (Fin 12)) →
      Tendsto (fun N : ℕ => log N * refinedSum ω N i) evenAtTop
        (𝓝 (integralTerms F f ω i)) := by
  sorry

/-- Exact normalization of the finite refined main term. -/
theorem refinedMain_ratio (ω : ℝ → ℝ) {N : ℕ} (hN : 2 ≤ N) (i : Fin 12) :
    refinedMain ω N i / Θ N = log N * refinedSum ω N i := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  unfold refinedMain Θ
  field_simp [(CN_pos N).ne', hn.ne', hl.ne']
  <;> ring

/-- The refined first prime weight expressed in logarithmic coordinates. -/
def refinedCoordinateWeight (t : ℝ) : ℝ :=
  if t ≤ (1 / 10 : ℝ) then (36 / 5 : ℝ) / (1 - t) else 8

/-- The finite cutoff is exactly the printed one tenth coordinate cutoff. -/
theorem refinedWeight_coordinates {N p : ℕ} (hN : 2 ≤ N) (hp : 0 < p) :
    refinedWeight N p = refinedCoordinateWeight (log p / log N) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hpr : (0 : ℝ) < p := by exact_mod_cast hp
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hc : (p : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) ↔
      log (p : ℝ) / log N ≤ (1 / 10 : ℝ) := by
    rw [← log_le_log_iff hpr (rpow_pos_of_pos hn _), log_rpow hn,
      div_le_iff₀ hl]
  simp only [refinedWeight, refinedCoordinateWeight, hc]

/-- The refinement lies between 36/5 and the ordinary switched weight eight. -/
theorem refinedWeight_bounds {N p : ℕ} (hN : 2 ≤ N) (hp : 1 ≤ p) :
    (36 / 5 : ℝ) ≤ refinedWeight N p ∧ refinedWeight N p ≤ 8 := by
  rw [refinedWeight_coordinates hN (by omega)]
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have ht : 0 ≤ log (p : ℝ) / log N := div_nonneg (log_natCast_nonneg p) hl.le
  unfold refinedCoordinateWeight
  split_ifs with h
  · have hd : 0 < 1 - log (p : ℝ) / log N := by linarith
    constructor
    · apply (le_div_iff₀ hd).2
      nlinarith
    · apply (div_le_iff₀ hd).2
      linarith
  · constructor <;> norm_num

/-- The two branches agree at the one tenth boundary. -/
theorem refinedCoordinateWeight_boundary : refinedCoordinateWeight (1 / 10) = 8 := by
  norm_num [refinedCoordinateWeight]

/-- The fourfold finite Buchstab argument is exactly the printed argument
when all primes are expressed as log p over log N. -/
theorem quad_buchstab_coordinates {N : ℕ} {q : ℕ × ℕ × ℕ × ℕ}
    (hN : 2 ≤ N) (h1 : 0 < q.1) (h2 : 1 < q.2.1)
    (h3 : 0 < q.2.2.1) (h4 : 0 < q.2.2.2) :
    log ((N : ℝ) / quadProduct q) / log q.2.1 =
      (1 - log (q.1 : ℝ) / log N - log (q.2.1 : ℝ) / log N -
        log (q.2.2.1 : ℝ) / log N - log (q.2.2.2 : ℝ) / log N) /
          (log (q.2.1 : ℝ) / log N) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hp : (0 : ℝ) < q.1 := by exact_mod_cast h1
  have hq : (0 : ℝ) < q.2.1 := by exact_mod_cast (show 0 < q.2.1 by omega)
  have hr : (0 : ℝ) < q.2.2.1 := by exact_mod_cast h3
  have hs : (0 : ℝ) < q.2.2.2 := by exact_mod_cast h4
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hqlog : 0 < log (q.2.1 : ℝ) := log_pos (by exact_mod_cast h2)
  rw [log_div hn.ne' (by unfold quadProduct; positivity)]
  unfold quadProduct
  rw [log_mul (by positivity : (q.1 : ℝ) * q.2.1 * q.2.2.1 ≠ 0) hs.ne',
    log_mul (by positivity : (q.1 : ℝ) * q.2.1 ≠ 0) hr.ne',
    log_mul hp.ne' hq.ne']
  field_simp [hl.ne', hqlog.ne']
  <;> ring

/-- Every finite four prime Buchstab argument is in the sharp tail range.
This connects the actual tuple domains to the existing integral argument bounds. -/
theorem refined_buchstab_argument {N : ℕ} (hN : 2 ≤ N) {i : Fin 12}
    (hi : i ∈ ({10, 11} : Finset (Fin 12))) {v : ℕ × ℕ × ℕ × ℕ}
    (hv : v ∈ refinedQuads N i) :
    (3.5 : ℝ) ≤ log ((N : ℝ) / quadProduct v) / log v.2.1 := by
  have hmem := hv
  simp only [refinedQuads, Wu08Sum.P4, Finset.mem_filter] at hmem
  rcases hmem.2 with
    ⟨hp, hq, hr, hs, hpc, hqc, hrc, hsc, hlo, hpq, hqr, hrest⟩
  have hl : 0 < log (N : ℝ) := log_pos (by exact_mod_cast (show 1 < N by omega))
  have hqt : 0 < log (v.2.1 : ℝ) / log N :=
    div_pos (log_pos (by exact_mod_cast hq.one_lt)) hl
  rw [quad_buchstab_coordinates hN hp.pos hq.one_lt hr.pos hs.pos]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · simp only [↓reduceIte] at hrest
    have hslt := (Task367.lt_power_cutoff_iff hN hs.pos kappa2).mp hrest.2
    have hrlt : (v.2.2.1 : ℝ) < (N : ℝ) ^ kappa2 :=
      (show (v.2.2.1 : ℝ) < v.2.2.2 by exact_mod_cast hrest.1).trans hrest.2
    have hqlt : (v.2.1 : ℝ) < (N : ℝ) ^ kappa2 :=
      (show (v.2.1 : ℝ) < v.2.2.1 by exact_mod_cast hqr).trans hrlt
    have hplt : (v.1 : ℝ) < (N : ℝ) ^ kappa2 :=
      (show (v.1 : ℝ) < v.2.1 by exact_mod_cast hpq).trans hqlt
    exact fourfold13_argument _ _ _ _ hqt
      ((Task367.lt_power_cutoff_iff hN hp.pos kappa2).mp hplt).le
      ((Task367.lt_power_cutoff_iff hN hq.pos kappa2).mp hqlt).le
      ((Task367.lt_power_cutoff_iff hN hr.pos kappa2).mp hrlt).le hslt.le
  · simp only [show (11 : Fin 12) ≠ 10 by decide, ↓reduceIte] at hrest
    have hrlt := hrest.1
    have hqlt : (v.2.1 : ℝ) < (N : ℝ) ^ kappa2 :=
      (show (v.2.1 : ℝ) < v.2.2.1 by exact_mod_cast hqr).trans hrlt
    have hplt : (v.1 : ℝ) < (N : ℝ) ^ kappa2 :=
      (show (v.1 : ℝ) < v.2.1 by exact_mod_cast hpq).trans hqlt
    have hcross := (Task367.crossing_cutoff_iff hN hr.pos hs.pos).mp hrest.2.2
    apply fourfold14_argument _ _ _ _ hqt
      ((Task367.lt_power_cutoff_iff hN hp.pos kappa2).mp hplt).le
      ((Task367.lt_power_cutoff_iff hN hq.pos kappa2).mp hqlt).le
    norm_num [kappa1] at *
    linarith

/-- The exact sealed refined_upper conclusion from two smaller leaves.
OPEN through refined_finite_upper and refined_sum_tendsto. -/
theorem refined_upper_supplied (F f ω : ℝ → ℝ) (h : IsLinearSieve F f)
    (hω : IsBuchstab ω) : ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ,
    ∀ N : ℕ, Even N → N0 ≤ N →
      ∀ i : Fin 12, i ∈ ({8, 10, 11} : Finset (Fin 12)) →
        sieveTerms N i ≤ (integralTerms F f ω i + ε) * Θ N := by
  apply finite_upper_threshold
  intro i hi
  apply upper_of_main _ _ (fun _ N => refinedMain ω N i)
  · intro η hη
    obtain ⟨M, hM⟩ := refined_finite_upper ω hω η hη
    exact ⟨1, by norm_num, M, fun N hEven hN => hM N hEven hN i hi⟩
  · intro B hB
    apply (refined_sum_tendsto F f ω hω i hi).congr'
    filter_upwards [(eventually_ge_atTop (2 : ℕ)).filter_mono inf_le_left] with N hN
    exact (refinedMain_ratio ω hN i).symm

end LeanLab.ChenDoubleSieve.Task349
