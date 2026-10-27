/-
P0063 J. G. van der Corput 1936/1937, main theorem of page 267, PROVED unconditional, as printed.

Lab proof, unit U-1039, PC run 20261019T0703Z-249. AI wrote the Lean code. Known mathematics.
`VdCTheorem` is the statement of page 267 exactly as stated in VanDerCorput1937.lean: for every
natural m there is c₁ with, for every N ≥ 3, the number of even naturals n ≤ N that are not a
sum of two ODD primes below c₁ N (log N)^{-m}. It follows from the lab's `LogPowerSaving`, whose
only extra exceptions are n = 2 and n = 4, and `LogPowerSaving` is
`PNTPort.PsiChi.goldbach_logPowerSaving`, proved unconditional by Heath-Brown's route from the
lab's Siegel-Walfisz theorem, not by van der Corput's own proof. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.VanDerCorput1937
import LeanLab.PNTPort.PsiChi.Unconditional

namespace LeanLab.ExceptionalSet
open Real

attribute [local instance] Classical.propDecidable

/-- The only even `n ≥ 1` that are Goldbach sums but not sums of two odd primes are 2 + 2. -/
lemma Eodd_le_E_add_two (N : ℕ) : Eodd N ≤ E N + 2 := by
  unfold Eodd E
  have hsub : (Finset.Icc 1 N).filter (fun n => Even n ∧ ¬ IsOddGoldbachSum n) ⊆
      (Finset.Icc 4 N).filter (fun n => Even n ∧ ¬ IsGoldbachSum n) ∪ {2, 4} := by
    intro n hn
    simp only [Finset.mem_filter, Finset.mem_Icc] at hn
    simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
      Finset.mem_singleton]
    obtain ⟨⟨h1, hN⟩, hev, hno⟩ := hn
    by_cases h4 : n ≤ 4
    · right
      obtain ⟨k, hk⟩ := hev
      omega
    · left
      refine ⟨⟨by omega, hN⟩, hev, ?_⟩
      rintro ⟨p, q, hp, hq, hpq⟩
      apply hno
      refine ⟨p, q, hp, hq, ?_, ?_, hpq⟩
      · rcases hp.eq_two_or_odd' with rfl | hpo
        · exfalso
          have hqe : Even q := by
            obtain ⟨k, hk⟩ := hev
            exact ⟨k - 1, by omega⟩
          rcases hq.eq_two_or_odd' with rfl | hqo
          · omega
          · exact (Nat.not_even_iff_odd.mpr hqo) hqe
        · exact hpo
      · rcases hq.eq_two_or_odd' with rfl | hqo
        · exfalso
          have hpe : Even p := by
            obtain ⟨k, hk⟩ := hev
            exact ⟨k - 1, by omega⟩
          rcases hp.eq_two_or_odd' with rfl | hpo
          · omega
          · exact (Nat.not_even_iff_odd.mpr hpo) hpe
        · exact hqo
  calc _ ≤ ((Finset.Icc 4 N).filter (fun n => Even n ∧ ¬ IsGoldbachSum n) ∪ {2, 4}).card :=
        Finset.card_le_card hsub
    _ ≤ _ + ({2, 4} : Finset ℕ).card := Finset.card_union_le _ _
    _ = _ := by simp

/-- For `N ≥ 3`, `(log N)^m ≤ (m+1)^(m+1) N`. -/
lemma log_pow_le (m N : ℕ) (hN : 3 ≤ N) :
    Real.log N ^ m ≤ ((m : ℝ) + 1) ^ (m + 1) * N := by
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
  have hm : (0 : ℝ) < (m : ℝ) + 1 := by positivity
  have hε : (0 : ℝ) < 1 / ((m : ℝ) + 1) := by positivity
  have h1 := Real.log_le_rpow_div hN0 hε
  rw [div_div_eq_mul_div, div_one] at h1
  -- log N ≤ N^{1/(m+1)} (m+1)
  have hL0 : 0 ≤ Real.log N := by linarith
  have hpow : Real.log N ^ (m + 1) ≤ (N ^ (1 / ((m : ℝ) + 1)) * ((m : ℝ) + 1)) ^ (m + 1) :=
    pow_le_pow_left₀ hL0 h1 _
  have hrp : ((N : ℝ) ^ (1 / ((m : ℝ) + 1))) ^ (m + 1) = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hN0]
    have : 1 / ((m : ℝ) + 1) * ((m + 1 : ℕ) : ℝ) = 1 := by
      push_cast; field_simp
    rw [this, Real.rpow_one]
  rw [mul_pow, hrp] at hpow
  have hmono : Real.log N ^ m ≤ Real.log N ^ (m + 1) :=
    pow_le_pow_right₀ hL1 (Nat.le_succ m)
  linarith

/-- `LogPowerSaving` gives van der Corput's theorem exactly as printed on page 267. -/
theorem vdcTheorem_of_logPowerSaving (h : LogPowerSaving) : VdCTheorem := by
  intro m
  obtain ⟨C, hC⟩ := h (((m + 1 : ℕ) : ℝ)) (by positivity)
  set K : ℝ := ((m : ℝ) + 1) ^ (m + 1) with hK
  have hK0 : 0 < K := by positivity
  refine ⟨|C| + 3 * K + 1, fun N hN => ?_⟩
  have hNr : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) (by have := Real.exp_one_lt_d9; linarith)
  have hL0 : 0 < Real.log N := by linarith
  set L := Real.log N with hLdef
  have hLm : 0 < L ^ m := pow_pos hL0 m
  -- rewrite the target's real power
  have hrw : (|C| + 3 * K + 1) * N * L ^ (-(m : ℝ)) = (|C| + 3 * K + 1) * (N / L ^ m) := by
    rw [Real.rpow_neg hL0.le, Real.rpow_natCast]; ring
  rw [hrw]
  -- E N ≤ |C| N / L^m
  have hE : (E N : ℝ) ≤ |C| * (N / L ^ m) := by
    have h2 := hC N (by omega)
    rw [Real.rpow_natCast] at h2
    have hmono : L ^ m ≤ L ^ (m + 1) := pow_le_pow_right₀ hL1 (Nat.le_succ m)
    calc (E N : ℝ) ≤ C * N / L ^ (m + 1) := h2
      _ ≤ |C| * N / L ^ (m + 1) := by
          apply div_le_div_of_nonneg_right _ (by positivity)
          exact mul_le_mul_of_nonneg_right (le_abs_self C) hN0.le
      _ ≤ |C| * N / L ^ m := by
          apply div_le_div_of_nonneg_left (by positivity) hLm hmono
      _ = |C| * (N / L ^ m) := by ring
  -- 1 ≤ K N / L^m
  have hone : 1 ≤ K * (N / L ^ m) := by
    have := log_pow_le m N hN
    rw [mul_div_assoc', le_div_iff₀ hLm, one_mul]
    simpa [hK] using this
  have hEo : (Eodd N : ℝ) ≤ E N + 2 := by exact_mod_cast Eodd_le_E_add_two N
  have hq : 0 < N / L ^ m := div_pos hN0 hLm
  nlinarith

/-- **van der Corput's theorem**, page 267, PROVED unconditional; ineffective constants. -/
theorem vdcTheorem : VdCTheorem :=
  vdcTheorem_of_logPowerSaving PNTPort.PsiChi.goldbach_logPowerSaving

end LeanLab.ExceptionalSet
