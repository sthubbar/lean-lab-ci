/-
P0095 W. C. Lu 2010, the first step of the proof of Lemma 1, p. 2362. Unit U-6844,
CLOUD MANUAL-M1, 2026-10-21, track T1.

With e(x) = e^{2πix}, (2) S(x, y, α) = Σ_{y<n≤x} Λ(n) e(nα), Q = N^{3/4} and
  D̃(k) = ∫_{-1/Q}^{1-1/Q} ∫_a^b S(td+d, td, α) S(N-td, N-td-d, α) e(-kα) dt dα,
p. 2361, the proof of Lemma 1 starts "From the definitions of D̃(k) and S(x, y, α) we have
D̃(k) = ∫_a^b Σ_{td<n≤td+d, N-td-d<m≤N-td, n+m-k=0} Λ(n)Λ(m) dt". This file PROVES that
identity, `Dtil_eq_Dt`, by linearity in both integrals and ∫ e(jα) dα = [j = 0] over an
interval of length 1. With Lu2010Lemma1, Lemma 1 itself is now PROVED in the weakened form
D(k) = D̃(k) + O(N^0.99995), and `InputsO` keeps only (9), (84) or (85), Section 9 and (86).

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach itself is OPEN.
-/
import Mathlib
import LeanLab.ExceptionalSet.Lu2010Lemma1

namespace LeanLab.ExceptionalSet.Lu2010Orth
open Real Filter Topology Finset ArithmeticFunction MeasureTheory Complex
  LeanLab.ExceptionalSet LeanLab.ExceptionalSet.Lu2010Assembly LeanLab.ExceptionalSet.Lu2010Lemma1

/-- `e(x) = e^{2πix}`. -/
noncomputable def ee (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

/-- (2): `S(x, y, α) = Σ_{y < n ≤ x} Λ(n) e(nα)`. -/
noncomputable def Ssum (x y α : ℝ) : ℂ :=
  ∑ n ∈ range (⌊x⌋₊ + 1), if y < n ∧ (n : ℝ) ≤ x then (Λ n : ℂ) * ee (n * α) else 0

/-- `Q = N^{3/4}`, p. 2361. -/
noncomputable def QQ (N : ℕ) : ℝ := (N : ℝ) ^ (3 / 4 : ℝ)

/-- p. 2361: `D̃(k) = ∫_{-1/Q}^{1-1/Q} ∫_a^b S(td+d, td, α) S(N-td, N-td-d, α) e(-kα) dt dα`. -/
noncomputable def Dtil (N k : ℕ) : ℂ :=
  ∫ α in (-1 / QQ N)..(1 - 1 / QQ N), ∫ t in Set.Icc (aa N) (bb N),
    Ssum (t * dd N + dd N) (t * dd N) α * Ssum (N - t * dd N) (N - t * dd N - dd N) α *
      ee (-(k * α))

theorem ee_add (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

theorem ee_continuous (j : ℝ) : Continuous fun α : ℝ => ee (j * α) := by
  unfold ee; fun_prop

/-- `∫_u^{u+1} e(jα) dα = [j = 0]` for an integer `j`. -/
theorem integral_ee (j : ℤ) (u : ℝ) :
    ∫ α in u..(u + 1), ee ((j : ℝ) * α) = if j = 0 then 1 else 0 := by
  split_ifs with hj
  · subst hj; simp [ee]
  · have hc : (2 * π * Complex.I * (j : ℂ)) ≠ 0 := by
      have : (j : ℂ) ≠ 0 := by exact_mod_cast hj
      have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
      simp [hpi, this, Complex.I_ne_zero]
    have hrw : (fun α : ℝ => ee ((j : ℝ) * α)) =
        fun α : ℝ => Complex.exp ((2 * π * Complex.I * (j : ℂ)) * α) := by
      funext α; unfold ee; congr 1; push_cast; ring
    rw [hrw, integral_exp_mul_complex hc]
    have hper : Complex.exp (2 * π * Complex.I * (j : ℂ) * ((u + 1 : ℝ) : ℂ)) =
        Complex.exp (2 * π * Complex.I * (j : ℂ) * (u : ℂ)) := by
      have : 2 * π * Complex.I * (j : ℂ) * ((u + 1 : ℝ) : ℂ) =
          2 * π * Complex.I * (j : ℂ) * (u : ℂ) + (j : ℂ) * (2 * π * Complex.I) := by
        push_cast; ring
      rw [this, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
    rw [hper, sub_self, zero_div]

/-- The pair set: `td < n ≤ td+d` and `N-td-d < m ≤ N-td`. -/
def pset (N n m : ℕ) : Set ℝ :=
  {t | t * dd N < n ∧ (n : ℝ) ≤ t * dd N + dd N ∧
    (N : ℝ) - t * dd N - dd N < m ∧ (m : ℝ) ≤ N - t * dd N}

theorem pset_measurable (N n m : ℕ) : MeasurableSet (pset N n m) := by
  have m1 : Measurable fun t : ℝ => t * dd N := by fun_prop
  have m2 : Measurable fun t : ℝ => t * dd N + dd N := by fun_prop
  have m3 : Measurable fun t : ℝ => (N : ℝ) - t * dd N - dd N := by fun_prop
  have m4 : Measurable fun t : ℝ => (N : ℝ) - t * dd N := by fun_prop
  exact (measurableSet_lt m1 measurable_const).inter ((measurableSet_le measurable_const m2).inter
    ((measurableSet_lt m3 measurable_const).inter (measurableSet_le measurable_const m4)))

/-- Extending the range of `S` to `range (K+1)` when `x ≤ K`. -/
theorem Ssum_eq_range {x y α : ℝ} {K : ℕ} (hx : x ≤ K) :
    Ssum x y α = ∑ n ∈ range (K + 1), if y < n ∧ (n : ℝ) ≤ x then (Λ n : ℂ) * ee (n * α) else 0 := by
  unfold Ssum
  apply Finset.sum_subset
  · intro n hn
    simp only [Finset.mem_range] at hn ⊢
    have : ⌊x⌋₊ ≤ K := Nat.floor_le_of_le hx
    omega
  · intro n _ hn
    simp only [Finset.mem_range, not_lt] at hn
    have : x < n := Nat.lt_of_floor_lt (by omega)
    rw [if_neg]; intro h; linarith [h.2]

/-- The integrand at `t ∈ [a, b]`, expanded with `K = k + 2N`. -/
theorem integrand_eq {N k : ℕ} (hN : 0 < N) {t α : ℝ} (ht : t ∈ Set.Icc (aa N) (bb N)) :
    Ssum (t * dd N + dd N) (t * dd N) α * Ssum (N - t * dd N) (N - t * dd N - dd N) α *
      ee (-(k * α)) =
    ∑ n ∈ range (k + 2 * N + 1), ∑ m ∈ range (k + 2 * N + 1),
      (pset N n m).indicator (fun _ => ((Λ n * Λ m : ℝ) : ℂ)) t *
        ee (((n : ℤ) + m - k : ℤ) * α) := by
  have hd := dd_pos hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have ha0 : 0 ≤ aa N := by unfold aa; positivity
  have hba : (bb N - aa N) * dd N = N / 3 := bad_mul N hN
  have had : aa N * dd N = N / 3 := by
    unfold aa dd; rw [div_mul_eq_mul_div, ← rpow_add hN']; norm_num
  have hbd : bb N * dd N ≤ N := by nlinarith
  have hd1 : dd N ≤ N := by
    unfold dd
    calc (N : ℝ) ^ (0.9999 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          rpow_le_rpow_of_exponent_le (by exact_mod_cast hN) (by norm_num)
      _ = N := rpow_one _
  obtain ⟨hta, htb⟩ := ht
  have ht0 : 0 ≤ t * dd N := mul_nonneg (ha0.trans hta) hd.le
  have htb' : t * dd N ≤ bb N * dd N := mul_le_mul_of_nonneg_right htb hd.le
  have hK : (k : ℝ) + 2 * N ≥ 0 := by positivity
  have h1 : t * dd N + dd N ≤ ((k + 2 * N : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]
  have h2 : (N : ℝ) - t * dd N ≤ ((k + 2 * N : ℕ) : ℝ) := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) k]
  rw [Ssum_eq_range h1, Ssum_eq_range h2, Finset.sum_mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl; intro n _
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro m _
  simp only [Set.indicator, pset, Set.mem_setOf_eq]
  have hee : ee (n * α) * ee (m * α) * ee (-(k * α)) = ee (((n : ℤ) + m - k : ℤ) * α) := by
    rw [← ee_add, ← ee_add]; congr 1; push_cast; ring
  rw [← hee]
  split_ifs <;> first | (exfalso; tauto) | (push_cast; ring) | simp | tauto

/-- The pair weights `c(n, m) = Λ(n)Λ(m) |pset ∩ [a, b]|`. -/
noncomputable def cc (N n m : ℕ) : ℝ :=
  Λ n * Λ m * (volume (pset N n m ∩ Set.Icc (aa N) (bb N))).toReal

/-- The inner `t`-integral at fixed `α`. -/
theorem inner_eq {N : ℕ} (hN : 0 < N) (k : ℕ) (α : ℝ) :
    ∫ t in Set.Icc (aa N) (bb N),
      Ssum (t * dd N + dd N) (t * dd N) α * Ssum (N - t * dd N) (N - t * dd N - dd N) α *
        ee (-(k * α)) =
    ∑ n ∈ range (k + 2 * N + 1), ∑ m ∈ range (k + 2 * N + 1),
      (cc N n m : ℂ) * ee (((n : ℤ) + m - k : ℤ) * α) := by
  rw [setIntegral_congr_fun measurableSet_Icc (fun t ht => integrand_eq (k := k) (α := α) hN ht)]
  have hint : ∀ n m : ℕ, IntegrableOn (fun t => (pset N n m).indicator
      (fun _ => ((Λ n * Λ m : ℝ) : ℂ)) t * ee (((n : ℤ) + m - k : ℤ) * α))
      (Set.Icc (aa N) (bb N)) := by
    intro n m
    exact ((integrableOn_const (by simp [Real.volume_Icc])).indicator
      (pset_measurable N n m)).mul_const _
  rw [integral_finsetSum _ (fun n _ => integrable_finsetSum _ (fun m _ => hint n m))]
  apply Finset.sum_congr rfl; intro n _
  rw [integral_finsetSum _ (fun m _ => hint n m)]
  apply Finset.sum_congr rfl; intro m _
  rw [integral_mul_const, setIntegral_indicator (pset_measurable N n m), setIntegral_const]
  unfold cc
  rw [Complex.real_smul]
  push_cast
  rw [Set.inter_comm]
  simp only [Measure.real]
  ring

/-- **The first step of Lemma 1, PROVED**: `D̃(k) = Dt(k)`. -/
theorem Dtil_eq_Dt {N : ℕ} (hN : 0 < N) (k : ℕ) : Dtil N k = (Dt N k : ℂ) := by
  have hQ : 0 < QQ N := rpow_pos_of_pos (by exact_mod_cast hN) _
  unfold Dtil
  simp_rw [inner_eq hN k]
  have hu : 1 - 1 / QQ N = -1 / QQ N + 1 := by ring
  rw [hu]
  rw [intervalIntegral.integral_finset_sum
    (f := fun n α => ∑ m ∈ range (k + 2 * N + 1), (cc N n m : ℂ) * ee (((n : ℤ) + m - k : ℤ) * α))
    (fun n _ => Continuous.intervalIntegrable (continuous_finset_sum _ (fun (m : ℕ) _ =>
      continuous_const.mul (ee_continuous (((n : ℤ) + (m : ℤ) - k : ℤ) : ℝ)))) _ _)]
  simp_rw [fun n => intervalIntegral.integral_finset_sum (μ := volume) (a := -1 / QQ N)
    (b := -1 / QQ N + 1) (s := range (k + 2 * N + 1))
    (f := fun m α => (cc N n m : ℂ) * ee (((n : ℤ) + m - k : ℤ) * α))
    (fun (m : ℕ) _ => Continuous.intervalIntegrable (continuous_const.mul
      (ee_continuous (((n : ℤ) + (m : ℤ) - k : ℤ) : ℝ))) _ _)]
  simp_rw [intervalIntegral.integral_const_mul, integral_ee]
  -- only m = k - n survives
  rw [Dt_eq hN]
  push_cast
  have hrow : ∀ n ∈ range (k + 2 * N + 1),
      ∑ m ∈ range (k + 2 * N + 1), (cc N n m : ℂ) * (if ((n : ℤ) + m - k : ℤ) = 0 then 1 else 0) =
      if n ≤ k then (cc N n (k - n) : ℂ) else 0 := by
    intro n _
    simp_rw [mul_ite, mul_one, mul_zero]
    split_ifs with hnk
    · rw [Finset.sum_eq_single (k - n)]
      · rw [if_pos (by omega)]
      · intro m _ hm; rw [if_neg (by omega)]
      · intro h; simp only [Finset.mem_range] at h; omega
    · apply Finset.sum_eq_zero; intro m _; rw [if_neg (by omega)]
  rw [Finset.sum_congr rfl hrow, ← Finset.sum_filter]
  have hfil : (range (k + 2 * N + 1)).filter (fun n => n ≤ k) = range (k + 1) := by
    ext n; simp only [Finset.mem_filter, Finset.mem_range]; omega
  rw [hfil]
  apply Finset.sum_congr rfl; intro n hn
  simp only [Finset.mem_range] at hn
  unfold cc w
  have hset : pset N n (k - n) = tset N k n := by
    unfold pset tset; ext t
    simp only [Set.mem_setOf_eq]
    rw [Nat.cast_sub (by omega)]
  rw [hset]
  push_cast; ring

/-- **Lemma 1, PROVED** in the weakened form: on the window, for every large `N`,
`|D(k) - D̃(k)| ≤ N^{0.99995}`. The printed form has `N^{1-0.0001}`, Q-6843a. -/
theorem lemma1 : ∃ N1 : ℕ, ∀ N, N1 ≤ N → ∀ k ∈ Win N,
    ‖(DLu N k : ℂ) - Dtil N k‖ ≤ (N : ℝ) ^ (1 - 0.00005 : ℝ) := by
  obtain ⟨N1, h⟩ := lemma1_eventually
  refine ⟨max N1 1, fun N hN k hk => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hN)
  rw [Dtil_eq_Dt hNpos, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  exact h N (le_trans (le_max_left _ _) hN) k hk

/-- **Cited input**, the displays left after Lemma 1: (9) as the split `D̃ = D₁ + D₂`,
(84) or (85), Section 9 and (86), on Lemma 1's window. -/
structure InputsO where
  D1 : ℕ → ℕ → ℝ
  D2 : ℕ → ℕ → ℂ
  D6 : ℕ → ℕ → ℂ
  S : ℕ → ℝ
  S_ge : ∀ k, Even k → 1 ≤ S k
  N0 : ℕ
  Cerr : ℝ
  c1 : ℝ
  c1_pos : 0 < c1
  C9 : ℝ
  C86 : ℝ
  eq9 : ∀ N, N0 ≤ N → ∀ k ∈ Win N, Dtil N k = (D1 N k : ℂ) + D2 N k
  lower : ∀ N, N0 ≤ N →
    (∀ k ∈ Win N, Even k →
      S k * (bb N - aa N) * dd N *
        ((Real.log (Real.log (Real.log N)))⁻¹ - Cerr * (Real.log (Real.log N)) ^ (-(1 / 2) : ℝ))
        - ‖D6 N k‖ < D1 N k) ∨
    (∀ k ∈ Win N, Even k →
      S k * (bb N - aa N) * dd N * c1 * PP N ^ (-0.00001 : ℝ) * Real.log (PP N) *
        (2 * c⁻¹ - Cerr * (Real.log (Real.log (Real.log N))) ^ (-0.1 : ℝ))
        - ‖D6 N k‖ ≤ D1 N k)
  sec9 : ∀ N, N0 ≤ N → ∑ k ∈ Win N, ‖D2 N k‖ ^ 2 ≤ C9 * (N : ℝ) ^ (3 - c + 0.00011)
  eq86 : ∀ N, N0 ≤ N →
    ∑ k ∈ Win N, ‖D6 N k‖ ^ 2 ≤ C86 * PP N ^ (-1 : ℝ) * dd N * (N : ℝ) ^ (2.0003 : ℝ)

/-- `InputsO` gives `InputsT`, by `Dtil_eq_Dt`. -/
def InputsO.toInputsT (J : InputsO) : InputsT :=
  { D1 := J.D1, D2 := J.D2, D6 := J.D6, S := J.S, S_ge := J.S_ge,
    N0 := max J.N0 1, Cerr := J.Cerr, c1 := J.c1, c1_pos := J.c1_pos, C9 := J.C9, C86 := J.C86
    orth9 := fun N hN k hk => by
      rw [← Dtil_eq_Dt (lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hN))]
      exact J.eq9 N (le_trans (le_max_left _ _) hN) k hk
    lower := fun N hN => J.lower N (le_trans (le_max_left _ _) hN)
    sec9 := fun N hN => J.sec9 N (le_trans (le_max_left _ _) hN)
    eq86 := fun N hN => J.eq86 N (le_trans (le_max_left _ _) hN) }

/-- CONDITIONAL ON `InputsO`: the paper's Theorem `E(x) ≪ x^{0.879}`. -/
theorem lu_of_inputsO (J : InputsO) : PowerBound 0.879 := lu_of_inputsT J.toInputsT

/-- CONDITIONAL ON `InputsO`: `E X ≪ X^{0.8789126}`. -/
theorem lu_sharp_of_inputsO (J : InputsO) : PowerBound θ := lu_sharp_of_inputsT J.toInputsT

/-- CONDITIONAL ON `InputsO`: Pintz's eventual form `E X < X^{0.879}`. -/
theorem lu_eventually_of_inputsO (J : InputsO) : Lu2010.lu_eventually_stmt :=
  lu_eventually_of_inputsT J.toInputsT

end LeanLab.ExceptionalSet.Lu2010Orth

#print axioms LeanLab.ExceptionalSet.Lu2010Orth.ee_add
#print axioms LeanLab.ExceptionalSet.Lu2010Orth.ee_continuous
#print axioms LeanLab.ExceptionalSet.Lu2010Orth.integral_ee
#print axioms LeanLab.ExceptionalSet.Lu2010Orth.pset_measurable
#print axioms LeanLab.ExceptionalSet.Lu2010Orth.Ssum_eq_range
#print axioms LeanLab.ExceptionalSet.Lu2010Orth.integrand_eq
#print axioms LeanLab.ExceptionalSet.Lu2010Orth.inner_eq
#print axioms LeanLab.ExceptionalSet.Lu2010Orth.Dtil_eq_Dt
#print axioms LeanLab.ExceptionalSet.Lu2010Orth.lemma1
#print axioms LeanLab.ExceptionalSet.Lu2010Orth.InputsO.toInputsT
#print axioms LeanLab.ExceptionalSet.Lu2010Orth.lu_of_inputsO
#print axioms LeanLab.ExceptionalSet.Lu2010Orth.lu_sharp_of_inputsO
#print axioms LeanLab.ExceptionalSet.Lu2010Orth.lu_eventually_of_inputsO
