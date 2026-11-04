/- AI wrote the Lean code for CODEX task236.
Partial summation for journal Lemma 14 pp. 1238 and 1239. Goldbach is open. -/
import LeanLab.BS2022GRH.SliceMass236
namespace LeanLab.BS2022GRH.SliceMass236
open Real Finset Classical MeasureTheory intervalIntegral
noncomputable section

/-- The derivative of the outer weight, journal p. 1238. -/
def Hderiv (N u : ℝ) : ℝ :=
  ((log (log N - log u - log (N ^ (1 / 3 : ℝ))) -
      log (log (N ^ (1 / 3 : ℝ)))) -
    (log N - log u) / (log N - log u - log (N ^ (1 / 3 : ℝ)))) /
      (u * (log N - log u) ^ 2)

/-- Scalar quotient rule normalization for the outer weight, p. 1238. -/
theorem outer_derivative_algebra (u A B C : ℝ) (hu : u ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0) :
    (((-u⁻¹) / B) * A - C * (-u⁻¹)) / A ^ 2 = (C - A / B) / (u * A ^ 2) := by
  field_simp
  <;> ring

/-- Differentiate the outer partial summation weight, journal p. 1238. -/
theorem H_hasDeriv (N u : ℝ) (hN : 1 < N) (hu : 0 < u)
    (hgap : 0 < log N - log u - log (N ^ (1 / 3 : ℝ))) :
    HasDerivAt (H N) (Hderiv N u) u := by
  have hL : 0 < log (N ^ (1 / 3 : ℝ)) := by
    rw [log_rpow (by linarith : 0 < N)]
    exact mul_pos (by norm_num) (log_pos hN)
  have hA : log N - log u ≠ 0 := by linarith
  have hdA := (hasDerivAt_const u (log N)).sub (hasDerivAt_log hu.ne')
  have hdB := (hdA.sub_const (log (N ^ (1 / 3 : ℝ)))).log hgap.ne'
  dsimp only [Pi.sub_apply] at hdA hdB
  convert (hdB.sub_const (log (log (N ^ (1 / 3 : ℝ))))).div hdA hA using 1
  · rfl
  · unfold Hderiv
    simp only [zero_sub]
    exact (outer_derivative_algebra u (log N - log u)
      (log N - log u - log (N ^ (1 / 3 : ℝ)))
      (log (log N - log u - log (N ^ (1 / 3 : ℝ))) - log (log (N ^ (1 / 3 : ℝ))))
      hu.ne' hA hgap.ne').symm

/-- Exact Abel summation for the second prime variable, journal pp. 1238 and 1239.
All endpoint contributions remain visible. -/
theorem H_prime_abel (N a b : ℝ) (hN : 1 < N) (ha : 0 < a) (hab : a ≤ b)
    (hgap : 0 < log N - log b - log (N ^ (1 / 3 : ℝ))) :
    (∑ k ∈ Ioc ⌊a⌋₊ ⌊b⌋₊, H N k * (if k.Prime then (1 : ℝ) / k else 0)) =
      H N b * (∑ k ∈ Icc 0 ⌊b⌋₊, if k.Prime then (1 : ℝ) / k else 0) -
      H N a * (∑ k ∈ Icc 0 ⌊a⌋₊, if k.Prime then (1 : ℝ) / k else 0) -
      ∫ t in Set.Ioc a b, Hderiv N t *
        ∑ k ∈ Icc 0 ⌊t⌋₊, if k.Prime then (1 : ℝ) / k else 0 := by
  have hgap' (t : ℝ) (ht : t ∈ Set.Icc a b) :
      0 < log N - log t - log (N ^ (1 / 3 : ℝ)) := by
    have hl := log_le_log (ha.trans_le ht.1) ht.2
    linarith
  have hd (t : ℝ) (ht : t ∈ Set.Icc a b) := H_hasDeriv N t hN (ha.trans_le ht.1) (hgap' t ht)
  have hcont : ContinuousOn (Hderiv N) (Set.Icc a b) := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    have ht0 := ha.trans_le ht.1
    have hg := hgap' t ht
    have hL : 0 < log (N ^ (1 / 3 : ℝ)) := by
      rw [log_rpow (by linarith : 0 < N)]
      exact mul_pos (by norm_num) (log_pos hN)
    have hA : log N - log t ≠ 0 := by linarith
    unfold Hderiv
    fun_prop (disch := first | assumption | positivity)
  have hint : IntegrableOn (deriv (H N)) (Set.Icc a b) := by
    apply hcont.integrableOn_Icc.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hd t ht).deriv.symm
  have hs := sum_mul_eq_sub_sub_integral_mul
    (fun k : ℕ => if k.Prime then (1 : ℝ) / k else 0) ha.le hab
    (fun t ht => (hd t ht).differentiableAt) hint
  rw [hs]
  congr 1
  apply setIntegral_congr_fun measurableSet_Ioc
  intro t ht
  dsimp only
  rw [(hd t ⟨ht.1.le, ht.2⟩).deriv]

/-- Evaluate the inner integral by the displayed logarithmic primitive, p. 1238.
The positivity guards state the exact interval on which the logarithms are regular. -/
theorem inner_integral_eq (N p y : ℝ) (hN : 0 < N) (hp : 0 < p) (hy : 1 < y)
    (hyR : y ≤ √(N / p)) :
    (∫ t in y..√(N / p), 1 / (t * log t * (log N - log p - log t))) =
      (log (log N - log p - log y) - log (log y)) / (log N - log p) := by
  have hdiv : 0 < N / p := div_pos hN hp
  have hR : 1 < √(N / p) := hy.trans_le hyR
  have hlogR : log (√(N / p)) = (log N - log p) / 2 := by
    rw [sqrt_eq_rpow, log_rpow hdiv, log_div hN.ne' hp.ne']
    ring
  have hApos : 0 < log N - log p := by linarith [log_pos hR]
  have hgap (t : ℝ) (ht : t ∈ Set.uIcc y (√(N / p))) : 0 < log N - log p - log t := by
    rw [Set.uIcc_of_le hyR] at ht
    have hlog := log_le_log (lt_trans zero_lt_one (hy.trans_le ht.1)) ht.2
    linarith
  have hgt (t : ℝ) (ht : t ∈ Set.uIcc y (√(N / p))) : 1 < t := by
    rw [Set.uIcc_of_le hyR] at ht
    exact hy.trans_le ht.1
  have hcont : ContinuousOn (fun t : ℝ => 1 / (t * log t * (log N - log p - log t)))
      (Set.uIcc y (√(N / p))) := by
    apply continuousOn_of_forall_continuousAt
    intro t ht
    have ht1 := hgt t ht
    have ht0 : 0 < t := by linarith
    have hgt0 := hgap t ht
    have hlogt : 0 < log t := log_pos ht1
    fun_prop (disch := first | assumption | positivity)
  have hint : IntervalIntegrable
      (fun t : ℝ => 1 / (t * log t * (log N - log p - log t))) volume y (√(N / p)) :=
    hcont.intervalIntegrable
  have heq := integral_eq_sub_of_hasDerivAt
    (fun t ht => kernelPrimitive_hasDeriv N p t (hgt t ht) (hgap t ht)) hint
  rw [heq]
  unfold kernelPrimitive
  rw [hlogR]
  have he : log N - log p - (log N - log p) / 2 = (log N - log p) / 2 := by ring
  rw [he, sub_self, zero_div]
  ring

end
end LeanLab.BS2022GRH.SliceMass236
#print axioms LeanLab.BS2022GRH.SliceMass236.H_hasDeriv
#print axioms LeanLab.BS2022GRH.SliceMass236.H_prime_abel
#print axioms LeanLab.BS2022GRH.SliceMass236.inner_integral_eq

#print axioms LeanLab.BS2022GRH.SliceMass236.outer_derivative_algebra
