import LeanLab.Routes.R5040Cesaro

/-!
# R-5040, the Cesàro moment of the Goldbach count as an integral of `ψ(t) ψ(N - t)`

Lab proof, route R-5040, unit U-6777, CLOUD 20261021T0017Z-cloud54, T3 field 5. AI wrote this
file. Known, elementary, no cited input.

Plain math twin. For every natural `N`,
`Σ_{n ≤ N} (N - n) R(n) = ∫_0^N ψ(t) ψ(N - t) dt = Σ_{a ≤ N} Λ(a) ψ₁(N - a)`,
with `R(n) = Σ_{a + b = n} Λ(a)Λ(b)`, `ψ` Mathlib's `Chebyshev.psi` and `ψ₁(y) = Σ_{b ≤ y} Λ(b)(y - b)`,
the lab's `Rg`. Proof: on `[0, N]`, `ψ(t) ψ(N - t) = Σ_{a, b ≤ N} Λ(a)Λ(b) 1[a ≤ t ≤ N - b]`, the
indicator integrates to `max(0, N - a - b)`, and `cesaro_eq_conv` closes it. This is the integral
form that the explicit formula for `ψ` can be inserted into twice; it is not progress on Goldbach,
which is open.

* `psi_eq_sum_indicator`, `psi_sub_eq_sum_indicator`: `ψ` on `[0, N]` as a finite sum of steps;
* `integral_indicator_Icc`: `∫_0^N 1[a ≤ t ≤ N - b] dt = max(0, N - a - b)` for naturals `a, b`;
* `integral_psi_mul_psi_eq_conv`: `∫_0^N ψ(t) ψ(N - t) dt = Σ_{a ≤ N} Λ(a) ψ₁(N - a)`;
* `cesaro_eq_integral`: `Σ_{n ≤ N} (N - n) R(n) = ∫_0^N ψ(t) ψ(N - t) dt`;
* `cesaro_five`, `integral_five`: the instance `N = 5`, both sides equal `(log 2)²`.
-/

open Finset MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.Routes.R5040

open LZCesaroShort

/-- For `0 ≤ t ≤ N`, `ψ(t) = Σ_{a ≤ N} Λ(a) 1[a ≤ t]`. -/
lemma psi_eq_sum_indicator {N : ℕ} {t : ℝ} (h0 : 0 ≤ t) (hN : t ≤ N) :
    Chebyshev.psi t =
      ∑ a ∈ range (N + 1), Λ a * (Set.Ici (a : ℝ)).indicator (fun _ => (1 : ℝ)) t := by
  rw [Chebyshev.psi_eq_sum_Icc]
  have hfl : ⌊t⌋₊ ≤ N := Nat.floor_le_of_le hN
  have hsub : Icc 0 ⌊t⌋₊ ⊆ range (N + 1) := by
    intro x hx; rw [mem_Icc] at hx; rw [mem_range]; omega
  rw [← sum_subset hsub]
  · apply sum_congr rfl; intro a ha
    rw [mem_Icc] at ha
    have : (a : ℝ) ≤ t := (Nat.le_floor_iff h0).mp ha.2
    rw [Set.indicator_of_mem (Set.mem_Ici.mpr this)]; ring
  · intro a _ ha
    rw [mem_Icc, not_and_or] at ha
    rcases ha with ha | ha
    · omega
    · have : ¬ (a : ℝ) ≤ t := fun h => ha ((Nat.le_floor_iff h0).mpr h)
      rw [Set.indicator_of_notMem (fun h => this (Set.mem_Ici.mp h))]; ring

/-- For `0 ≤ t ≤ N`, `ψ(N - t) = Σ_{b ≤ N} Λ(b) 1[t ≤ N - b]`. -/
lemma psi_sub_eq_sum_indicator {N : ℕ} {t : ℝ} (h0 : 0 ≤ t) (hN : t ≤ N) :
    Chebyshev.psi ((N : ℝ) - t) =
      ∑ b ∈ range (N + 1), Λ b * (Set.Iic ((N : ℝ) - b)).indicator (fun _ => (1 : ℝ)) t := by
  rw [psi_eq_sum_indicator (N := N) (by linarith) (by linarith)]
  apply sum_congr rfl; intro b _
  congr 1
  by_cases h : (b : ℝ) ≤ N - t
  · rw [Set.indicator_of_mem (Set.mem_Ici.mpr h),
      Set.indicator_of_mem (Set.mem_Iic.mpr (by linarith))]
  · rw [Set.indicator_of_notMem (fun h' => h (Set.mem_Ici.mp h')),
      Set.indicator_of_notMem (fun h' => h (by have := Set.mem_Iic.mp h'; linarith))]

lemma indicator_mul_indicator (a c t : ℝ) :
    (Set.Ici a).indicator (fun _ => (1 : ℝ)) t * (Set.Iic c).indicator (fun _ => (1 : ℝ)) t =
      (Set.Icc a c).indicator (fun _ => (1 : ℝ)) t := by
  by_cases h1 : a ≤ t <;> by_cases h2 : t ≤ c <;>
    simp [h1, h2]

lemma intervalIntegrable_indicator_Icc (a c : ℝ) (N : ℕ) :
    IntervalIntegrable ((Set.Icc a c).indicator (fun _ => (1 : ℝ))) volume 0 (N : ℝ) := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (Nat.cast_nonneg N)]
  exact (integrableOn_const (by simp)).indicator measurableSet_Icc

/-- `∫_0^N 1[a ≤ t ≤ N - b] dt = max(0, N - a - b)` for naturals `a, b`. -/
lemma integral_indicator_Icc (N a b : ℕ) :
    ∫ t in (0 : ℝ)..N, (Set.Icc (a : ℝ) ((N : ℝ) - b)).indicator (fun _ => (1 : ℝ)) t =
      max 0 ((N : ℝ) - a - b) := by
  rw [intervalIntegral.integral_of_le (Nat.cast_nonneg N),
    show (Set.Icc (a : ℝ) ((N : ℝ) - b)).indicator (fun _ => (1 : ℝ)) =
      (Set.Icc (a : ℝ) ((N : ℝ) - b)).indicator 1 from rfl,
    integral_indicator_one measurableSet_Icc, measureReal_def,
    Measure.restrict_apply measurableSet_Icc]
  have hb : (0 : ℝ) ≤ b := Nat.cast_nonneg b
  have ha : (0 : ℝ) ≤ a := Nat.cast_nonneg a
  have hup : volume (Set.Icc (a : ℝ) ((N : ℝ) - b) ∩ Set.Ioc 0 N) ≤
      ENNReal.ofReal ((N : ℝ) - b - a) := by
    calc _ ≤ volume (Set.Icc (a : ℝ) ((N : ℝ) - b)) := measure_mono Set.inter_subset_left
      _ = _ := Real.volume_Icc
  have hlo : ENNReal.ofReal ((N : ℝ) - b - a) ≤
      volume (Set.Icc (a : ℝ) ((N : ℝ) - b) ∩ Set.Ioc 0 N) := by
    calc ENNReal.ofReal ((N : ℝ) - b - a) = volume (Set.Ioo (a : ℝ) ((N : ℝ) - b)) :=
          Real.volume_Ioo.symm
      _ ≤ _ := by
        apply measure_mono
        intro x hx
        rw [Set.mem_Ioo] at hx
        exact ⟨⟨hx.1.le, hx.2.le⟩, ⟨by linarith, by linarith⟩⟩
  rw [le_antisymm hup hlo, ENNReal.toReal_ofReal', max_comm]
  ring_nf

/-- `∫_0^N ψ(t) ψ(N - t) dt = Σ_{a ≤ N} Λ(a) ψ₁(N - a)`, with `ψ₁` the lab's `Rg N`. -/
theorem integral_psi_mul_psi_eq_conv (N : ℕ) :
    ∫ t in (0 : ℝ)..N, Chebyshev.psi t * Chebyshev.psi ((N : ℝ) - t) =
      ∑ a ∈ range (N + 1), Λ a * Rg N ((N : ℝ) - a) := by
  have hcongr : Set.EqOn (fun t => Chebyshev.psi t * Chebyshev.psi ((N : ℝ) - t))
      (fun t => ∑ a ∈ range (N + 1), ∑ b ∈ range (N + 1), Λ a * Λ b *
        (Set.Icc (a : ℝ) ((N : ℝ) - b)).indicator (fun _ => (1 : ℝ)) t) (Set.uIcc 0 (N : ℝ)) := by
    intro t ht
    rw [Set.uIcc_of_le (Nat.cast_nonneg N), Set.mem_Icc] at ht
    simp only
    rw [psi_eq_sum_indicator ht.1 ht.2, psi_sub_eq_sum_indicator ht.1 ht.2, sum_mul_sum]
    apply sum_congr rfl; intro a _; apply sum_congr rfl; intro b _
    rw [← indicator_mul_indicator]; ring
  rw [intervalIntegral.integral_congr hcongr, intervalIntegral.integral_finsetSum]
  · apply sum_congr rfl; intro a _
    rw [intervalIntegral.integral_finsetSum]
    · rw [Rg, mul_sum]
      apply sum_congr rfl; intro b _
      rw [intervalIntegral.integral_const_mul, integral_indicator_Icc]
      rw [show (N : ℝ) - a - b = (N : ℝ) - a - (b : ℝ) from rfl]; ring
    · intro b _
      exact (intervalIntegrable_indicator_Icc _ _ N).const_mul _
  · intro a _
    have := IntervalIntegrable.sum (range (N + 1)) fun b _ =>
      (intervalIntegrable_indicator_Icc (a : ℝ) ((N : ℝ) - b) N).const_mul (Λ a * Λ b)
    convert this using 1
    ext t; simp [Finset.sum_apply]

/-- **R-5040 field 5, Stieltjes step.** For every natural `N`,
`Σ_{n ≤ N} (N - n) R(n) = ∫_0^N ψ(t) ψ(N - t) dt`. -/
theorem cesaro_eq_integral (N : ℕ) :
    ∑ n ∈ range (N + 1), ((N : ℝ) - n) * R n =
      ∫ t in (0 : ℝ)..N, Chebyshev.psi t * Chebyshev.psi ((N : ℝ) - t) := by
  rw [cesaro_eq_conv, integral_psi_mul_psi_eq_conv]

/-! ## Vacuity instance, `N = 5`: both sides equal `(log 2)²` -/

lemma vM2 : Λ 2 = Real.log 2 := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]; norm_num

lemma vM3 : Λ 3 = Real.log 3 := by
  rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three]; norm_num

lemma vM4 : Λ 4 = Real.log 2 := by
  rw [show (4 : ℕ) = 2 ^ 2 by norm_num,
    ArithmeticFunction.vonMangoldt_apply_pow (by norm_num), vM2]

/-- `Σ_{n ≤ 5} (5 - n) R(n) = (log 2)²`: only `R(4) = Λ(2)²` has positive weight. -/
theorem cesaro_five :
    ∑ n ∈ range (5 + 1), ((5 : ℕ) - (n : ℝ)) * R n = Real.log 2 ^ 2 := by
  have h0 : Λ 0 = 0 := ArithmeticFunction.map_zero
  have h1 : Λ 1 = 0 := ArithmeticFunction.vonMangoldt_apply_one
  simp only [R, sum_range_succ, range_zero, sum_empty, Nat.sum_antidiagonal_eq_sum_range_succ
    (fun i j => Λ i * Λ j)]
  simp [h0, h1, vM2, vM3, vM4]
  ring

/-- The instance `N = 5` of `cesaro_eq_integral`: `∫_0^5 ψ(t) ψ(5 - t) dt = (log 2)²`. -/
theorem integral_five :
    ∫ t in (0 : ℝ)..(5 : ℕ), Chebyshev.psi t * Chebyshev.psi (((5 : ℕ) : ℝ) - t) =
      Real.log 2 ^ 2 := by
  rw [← cesaro_eq_integral, cesaro_five]

end LeanLab.Routes.R5040
