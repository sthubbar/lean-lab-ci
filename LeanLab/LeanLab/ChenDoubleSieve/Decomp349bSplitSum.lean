import LeanLab.ChenDoubleSieve.Decomp349b
import LeanLab.ChenDoubleSieve.Decomp348e
import LeanLab.ChenDoubleSieve.Task693Integrals

/-!
Split of `Task349.switched_sum_tendsto`, Wu 2004 page 41, equation 10.9 and its
analogue in 10.11. Source: https://arxiv.org/pdf/0705.1652.
The coprimality restriction is removed, the free prime double sum is replaced by
a double integral by prime partial summation, and the double integral is
evaluated in closed form.
AI wrote the Lean code. Binary Goldbach is open.
-/
noncomputable section
open Real Finset Filter Set
open scoped Classical Topology
namespace LeanLab.ChenDoubleSieve.Task349
open Task275 Task348
open Wu04Functional (IsLinearSieve IsBuchstab)

/-- The switched prime pairs of `switchedPairs` without the coprimality to N,
Wu 2004 page 41 display 10.9. -/
def freePairs (N : ℕ) (i : Fin 12) : Finset (ℕ × ℕ) :=
  (Finset.range N ×ˢ Finset.range N).filter (fun q => q.1.Prime ∧ q.2.Prime ∧
    (if i = 6 then (N : ℝ) ^ sigma1 ≤ q.1 else
      if i = 7 then (N : ℝ) ^ sigma2 ≤ q.1 else
        (N : ℝ) ^ kappa2 ≤ q.1 ∧ (q.1 : ℝ) < (N : ℝ) ^ sigma2 ∧
          (N : ℝ) ^ sigma2 ≤ q.2) ∧
    q.1 < q.2 ∧ (q.2 : ℝ) < sqrt ((N : ℝ) / q.1))

/-- The switched sum of `switchedSum` over `freePairs`. -/
def freeSum (N : ℕ) (i : Fin 12) : ℝ :=
  ∑ q ∈ freePairs N i,
    1 / (((q.1 : ℝ) * q.2) * log ((N : ℝ) / ((q.1 : ℝ) * q.2)))

/-- The double integral limit of Wu 2004 page 41 before evaluation, in the
variables t equal log p over log N and u equal log q over log N. -/
def switchedIntegral (i : Fin 12) : ℝ :=
  if i = 9 then
    ∫ t in kappa2..sigma2, ∫ u in sigma2..((1 - t) / 2), 1 / (t * u * (1 - t - u))
  else
    ∫ t in (if i = 6 then sigma1 else sigma2)..(1 / 3 : ℝ),
      ∫ u in t..((1 - t) / 2), 1 / (t * u * (1 - t - u))

/-- LEAF: Wu 2004 page 41, removal of the coprimality condition in 10.9: at most
1 over kappa two primes above N to kappa two divide N, so the pairs with p or q
dividing N contribute o of 1 over log N. Class MEDIUM. -/
theorem leaf_coprime_removal :
    ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
      Tendsto (fun N : ℕ => 8 * log N * (switchedSum N i - freeSum N i)) evenAtTop
        (𝓝 0) := by
  intro i _hi
  apply tendsto_inf_left (x₂ := principal {N : ℕ | Even N})
  apply Metric.tendsto_atTop.mpr
  intro ε hε
  obtain ⟨M, hM⟩ := badPairs_mass_small (κ := kappa2)
    (by norm_num [kappa2]) (ε / 48) (by positivity)
  refine ⟨max 2 M, ?_⟩
  intro N hN
  have hN2 : 2 ≤ N := by omega
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hlog : 0 < log (N : ℝ) := log_pos hN1
  let R := freePairs N i
  let C : ℕ × ℕ → Prop := fun q => q.1.Coprime N ∧ q.2.Coprime N
  let P := (range N).filter (fun p : ℕ => p.Prime ∧ (N : ℝ) ^ kappa2 ≤ p)
  let W : ℕ × ℕ → ℝ := fun q =>
    1 / (((q.1 : ℝ) * q.2) * log ((N : ℝ) / ((q.1 : ℝ) * q.2)))
  have hprops : ∀ q ∈ R, q.1.Prime ∧ q.2.Prime ∧
      (N : ℝ) ^ kappa2 ≤ q.1 ∧ (N : ℝ) ^ kappa2 ≤ q.2 ∧
      q.1 < q.2 ∧ (q.2 : ℝ) < sqrt ((N : ℝ) / q.1) := by
    intro q hq
    obtain ⟨_, hp, hqprime, hcut, hpq, hsqrt⟩ := mem_filter.mp hq
    have hlow : (N : ℝ) ^ kappa2 ≤ q.1 := by
      by_cases h6 : i = 6
      · simp only [if_pos h6] at hcut
        exact (rpow_le_rpow_of_exponent_le hN1.le
          (by norm_num [kappa2, sigma1])).trans hcut
      · by_cases h7 : i = 7
        · simp only [if_neg h6, if_pos h7] at hcut
          exact (rpow_le_rpow_of_exponent_le hN1.le
            (by norm_num [kappa2, sigma2])).trans hcut
        · simp only [if_neg h6, if_neg h7] at hcut
          exact hcut.1
    exact ⟨hp, hqprime, hlow, hlow.trans (by exact_mod_cast hpq.le), hpq, hsqrt⟩
  have hP : ∀ p ∈ P, p.Prime ∧ (N : ℝ) ^ kappa2 ≤ p ∧ p ≤ N := by
    intro p hp
    obtain ⟨hrange, hprime, hlow⟩ := mem_filter.mp hp
    exact ⟨hprime, hlow, (mem_range.mp hrange).le⟩
  have hsub : R ⊆ P ×ˢ P := by
    intro q hq
    have hs := hprops q hq
    have hgrid := (mem_filter.mp hq).1
    exact mem_product.mpr ⟨mem_filter.mpr ⟨(mem_product.mp hgrid).1, hs.1, hs.2.2.1⟩,
      mem_filter.mpr ⟨(mem_product.mp hgrid).2, hs.2.1, hs.2.2.2.1⟩⟩
  have heq : switchedPairs N i = R.filter C := by
    ext q
    simp only [switchedPairs, Wu08Sum.P2, R, freePairs, C, mem_filter]
    tauto
  have hdiff : switchedSum N i - freeSum N i =
      -(∑ q ∈ R.filter (fun q => ¬ C q), W q) := by
    have hs := sum_filter_add_sum_filter_not (s := R) (p := C) (f := W)
    change (∑ q ∈ switchedPairs N i, W q) - (∑ q ∈ R, W q) = _
    rw [heq]
    linarith
  have hpoint : ∀ q ∈ R, 0 ≤ 8 * log N * W q ∧
      8 * log N * W q ≤ 24 * (1 / ((q.1 : ℝ) * q.2)) := by
    intro q hq
    obtain ⟨hp, hqprime, _, _, hpq, hsqrt⟩ := hprops q hq
    have hp0 : (0 : ℝ) < q.1 := by exact_mod_cast hp.pos
    have hq0 : (0 : ℝ) < q.2 := by exact_mod_cast hqprime.pos
    have hpqR : (q.1 : ℝ) ≤ q.2 := by exact_mod_cast hpq.le
    have hsq : (q.2 : ℝ) ^ 2 < (N : ℝ) / q.1 :=
      (Real.lt_sqrt hq0.le).mp hsqrt
    have hprod : (q.1 : ℝ) * (q.2 : ℝ) ^ 2 < N := by
      simpa [mul_comm] using (lt_div_iff₀ hp0).mp hsq
    have hl := log_lt_log (mul_pos hp0 (pow_pos hq0 2)) hprod
    rw [log_mul hp0.ne' (pow_ne_zero 2 hq0.ne'), log_pow] at hl
    norm_num only [Nat.cast_ofNat] at hl
    have hlogs := log_le_log hp0 hpqR
    have hmargin : log (N : ℝ) / 3 < log ((N : ℝ) / ((q.1 : ℝ) * q.2)) := by
      rw [log_div (ne_of_gt (lt_trans zero_lt_one hN1)) (mul_ne_zero hp0.ne' hq0.ne'),
        log_mul hp0.ne' hq0.ne']
      linarith
    have hden : 0 < log ((N : ℝ) / ((q.1 : ℝ) * q.2)) := by linarith
    constructor
    · dsimp [W]
      positivity
    · calc
        8 * log N * W q = (8 * log N / log ((N : ℝ) / ((q.1 : ℝ) * q.2))) *
            (1 / ((q.1 : ℝ) * q.2)) := by dsimp [W]; ring
        _ ≤ 24 * (1 / ((q.1 : ℝ) * q.2)) :=
          mul_le_mul_of_nonneg_right ((div_le_iff₀ hden).mpr (by linarith)) (by positivity)
  have hbadsub : R.filter (fun q => ¬ C q) ⊆ badPairs N P P := by
    intro q hq
    obtain ⟨hqR, hqC⟩ := mem_filter.mp hq
    apply mem_filter.mpr
    refine ⟨hsub hqR, ?_⟩
    simpa only [C, not_and_or] using hqC
  rw [Real.dist_eq, sub_zero, hdiff, mul_neg, abs_neg, Finset.mul_sum]
  calc
    _ ≤ ∑ q ∈ R.filter (fun q => ¬ C q), |8 * log N * W q| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ q ∈ R.filter (fun q => ¬ C q), 24 * (1 / ((q.1 : ℝ) * q.2)) := by
      apply sum_le_sum
      intro q hq
      have hs := hpoint q (mem_filter.mp hq).1
      rw [abs_of_nonneg hs.1]
      exact hs.2
    _ = 24 * pairMass (R.filter (fun q => ¬ C q)) := by rw [pairMass, Finset.mul_sum]
    _ ≤ 24 * pairMass (badPairs N P P) :=
      mul_le_mul_of_nonneg_left (pairMass_mono hbadsub) (by norm_num)
    _ ≤ 24 * (ε / 48) :=
      mul_le_mul_of_nonneg_left (hM N (by omega) P P hP hP) (by norm_num)
    _ < ε := by linarith

/-- LEAF: Wu 2004 page 41, display 10.9 and 10.11: prime partial summation with
the prime number theorem replaces the free double prime sum by the double
integral in t and u. Class HARD. -/
theorem leaf_free_sum_tendsto :
    ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
      Tendsto (fun N : ℕ => 8 * log N * freeSum N i) atTop
        (𝓝 (8 * switchedIntegral i)) := by
  sorry

/-- LEAF: Wu 2004 page 41, evaluation of the double integral: the inner integral is
log of 1 minus 2 t over t, or log of 1 minus t minus sigma two over sigma two,
divided by 1 minus t, and the substitution s equal 1 minus t over t gives the
coefficients of 10.9 and 10.11. Class MEDIUM. -/
theorem leaf_switched_integral_eval :
    ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
      8 * switchedIntegral i =
        integralTerms (fun _ => 0) (fun _ => 0) (fun _ => 0) i := by
  intro i hi
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl | rfl
  · change 8 * (∫ t in sigma1..(1 / 3 : ℝ),
        ∫ u in t..((1 - t) / 2), 1 / (t * u * (1 - t - u))) =
      8 * ∫ u in (2 : ℝ)..(1 / sigma1 - 1), log (u - 1) / u
    rw [Task693.triangle_switching_integral (by norm_num [sigma1]) (by norm_num [sigma1])]
  · change 8 * (∫ t in sigma2..(1 / 3 : ℝ),
        ∫ u in t..((1 - t) / 2), 1 / (t * u * (1 - t - u))) =
      8 * ∫ u in (2 : ℝ)..(1 / sigma2 - 1), log (u - 1) / u
    rw [Task693.triangle_switching_integral (by norm_num [sigma2]) (by norm_num [sigma2])]
  · change 8 * (∫ t in kappa2..sigma2,
        ∫ u in sigma2..((1 - t) / 2), 1 / (t * u * (1 - t - u))) =
      8 * ∫ t in kappa2..sigma2,
        log (1 / sigma2 - 1 - t / sigma2) / (t * (1 - t))
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    rw [Set.uIcc_of_le (by norm_num [kappa2, sigma2] : kappa2 ≤ sigma2)] at ht
    have ht0 : 0 < t := lt_of_lt_of_le (by norm_num [kappa2]) ht.1
    have ht1 : t < 1 := by have := ht.2; norm_num [sigma2] at this; linarith
    have hsig : 0 < sigma2 := by norm_num [sigma2]
    have hupper : sigma2 ≤ (1 - t) / 2 := by
      have := ht.2
      norm_num [sigma2] at *
      linarith
    dsimp only
    rw [Task693.inner_switching_integral ht0 ht1 hsig hupper]
    congr 2
    field_simp
    ring

/-- `switched_sum_tendsto`, exactly as stated in `Decomp349b`, proved from the three
leaves above. CONDITIONAL ON the LEAFs. -/
theorem switched_sum_tendsto_of_leaves :
    ∀ i : Fin 12, i ∈ ({6, 7, 9} : Finset (Fin 12)) →
      Tendsto (fun N : ℕ => 8 * log N * switchedSum N i) evenAtTop
        (𝓝 (integralTerms (fun _ => 0) (fun _ => 0) (fun _ => 0) i)) := by
  intro i hi
  have h1 := leaf_coprime_removal i hi
  have h2 := tendsto_inf_left (x₂ := principal {N : ℕ | Even N})
    (leaf_free_sum_tendsto i hi)
  have h := h1.add h2
  rw [zero_add, leaf_switched_integral_eval i hi] at h
  refine h.congr' (Eventually.of_forall fun N => ?_)
  simp only
  ring

end LeanLab.ChenDoubleSieve.Task349
