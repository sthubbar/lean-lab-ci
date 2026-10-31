/-
P0028, arXiv 1610.02017, Lemma 4.3 on pages 9 and 10.
The trivial decomposition has a constant that depends on N.
It handles bounded N but does not establish the uniform existence statement.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSIntervalLift
import LeanLab.Ternary.MMSLemma43

namespace LeanLab.Ternary.MMS
open Finset

/-- Fourier pseudorandomness bounds each interval value by 1 + ηN. -/
theorem prop31Hyp_pointwise_le {N : ℕ} {η ε K q : ℝ} {f : ℕ → ℝ}
    (hf : Prop31Hyp N η ε K q f) (n : ℕ) (hn : n ∈ Icc 1 N) : f n ≤ 1 + η * N := by
  obtain ⟨ν, hν, hh⟩ := hf.2.2.1
  let d := intervalLift N ν - intervalLift N (fun _ => 1)
  have hd (γ : ℝ) : intHat d γ = fhat N ν γ - fhat N (fun _ => 1) γ := by
    have he : intHat d γ = intHat (intervalLift N ν) γ -
        intHat (intervalLift N (fun _ => 1)) γ := by simp [d, intHat]
    simpa only [intHat_intervalLift] using he
  have hv := intHat_inversion d (n : ℤ)
  have hval : d (n : ℤ) = ν n - 1 := by simp [d, intervalLift_apply_nat, hn]
  rw [hval] at hv
  simp only [Int.cast_natCast] at hv
  have hb : ‖∫ γ in (0 : ℝ)..1, intHat d γ * e ((n : ℝ) * γ)‖ ≤ η * N := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := 1) (C := η * N)
      (f := fun γ : ℝ => intHat d γ * e ((n : ℝ) * γ)) (fun γ hγ => by
        rw [norm_mul, norm_e, mul_one, hd]
        exact hh γ)
    simpa using h
  rw [hv, Complex.norm_real, Real.norm_eq_abs] at hb
  have hub := (abs_le.mp hb).2
  linarith [hν n hn]

/-- The same N-dependent bound holds after extension by zero. -/
theorem prop31Hyp_lift_bounds {N : ℕ} {η ε K q : ℝ} {f : ℕ → ℝ}
    (hf : Prop31Hyp N η ε K q f) (hη : 0 ≤ η) (n : ℤ) :
    0 ≤ intervalLift N f n ∧ intervalLift N f n ≤ 1 + (N : ℝ) * η := by
  refine ⟨intervalLift_nonneg N f hf.1 n, ?_⟩
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn with m
    rw [intervalLift_apply_nat]
    split_ifs with hm
    · have := prop31Hyp_pointwise_le hf m hm
      nlinarith
    · positivity
  · rw [intervalLift_apply_neg N f n (lt_of_not_ge hn)]
    positivity

/-- The restriction norm of zero is zero when q is positive. -/
theorem intLq_zero {q : ℝ} (hq : 0 < q) : intLq 0 q = 0 := by
  simp [intLq, intHat, Real.zero_rpow hq.ne', Real.zero_rpow (inv_ne_zero hq.ne')]

/-- The trivial decomposition satisfies the four local conditions with C = N.
The constant depends on N, so this theorem does not prove Lemma43. -/
theorem lemma43_trivial_model {N : ℕ} {η ε K q δ : ℝ} {f : ℕ → ℝ}
    (hf : Prop31Hyp N η ε K q f) (hη : 0 ≤ η) (hε : 0 < ε)
    (hq : 0 < q) (hK : 0 ≤ K) (hδ : 0 ≤ δ) :
    Lemma43Data N η ε K q δ N f (intervalLift N f) 0 := by
  refine ⟨by simp, prop31Hyp_lift_bounds hf hη, ?_, ?_, ?_, ?_⟩
  · intro γ
    simp only [intHat, map_zero, norm_zero]
    positivity
  · intro P hP hlen
    have hlen' : η * N ≤ P.card := by
      have hdiv : 0 ≤ δ / ε := div_nonneg hδ hε.le
      have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      nlinarith
    have havg : avg (fun n => intervalLift N f n) P = avg f P := by
      unfold avg
      congr 1
      apply sum_congr rfl
      intro n hn
      have hnN : n ∈ Icc 1 N := by
        obtain ⟨a, d, L, hd, hL, hEq, hIn⟩ := hP
        exact mem_Icc.mpr (hIn n hn)
      simp [intervalLift_apply_nat, hnN]
    rw [havg]
    have := hf.2.1 P hP hlen'
    linarith
  · rw [intLq_intervalLift]
    exact hf.2.2.2
  · rw [intLq_zero hq]
    positivity

end LeanLab.Ternary.MMS
