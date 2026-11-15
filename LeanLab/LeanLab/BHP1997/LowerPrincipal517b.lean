/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character:
the prime term on every prefix of J, from the prime number theorem with error term.
No new definition, nothing left open in this file. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a
import LeanLab.BHP1997.Prime514

namespace LeanLab.BHP1997.LowerShortC165
open Classical Complex Decomp132 DecompC165b DecompC165d
open scoped BigOperators

/-- P0069 page 51, display 5.17, the prime term: the prime number theorem with error term on
every prefix of J, with local density `1 / log m`. -/
theorem prime_density_prefix {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
      |∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
        (primeWeight m - 1 / Real.log (m : ℝ))| ≤
        C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, h1⟩ := Prime514.pnt_short_interval A hA
  obtain ⟨C0, h0⟩ := Prime514.short_scale_cutoff hε hε8 0 1 one_pos
  let K : ℝ := 2 * max C1 0 * (2 : ℝ) ^ A
  have hK0 : 0 ≤ K := by positivity
  let C := max (max C0 (C1 ^ 2)) K
  have h0C : C0 ≤ C := (le_max_left _ _).trans (le_max_left _ _)
  have h1C : C1 ^ 2 ≤ C := (le_max_right _ _).trans (le_max_left _ _)
  have hKC : K ≤ C := le_max_right _ _
  refine ⟨C, fun x hx t ht => ?_⟩
  obtain ⟨hx2, hX2, -, hloglow⟩ := h0 x (h0C.trans hx)
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  have hY : 0 < x ^ (11/20 + ε) := Real.rpow_pos_of_pos hx0 _
  have hlog : 0 < Real.log x := Real.log_pos (by linarith)
  have hscale : 0 ≤ x ^ (11/20 + ε) * Real.log x ^ (-A) := by positivity
  by_cases htY : t ≤ x ^ (11/20 + ε)
  · have he : (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro m hm
      obtain ⟨hmJ, hmt⟩ := Finset.mem_filter.mp hm
      have hmgt := (Finset.mem_Ioc.mp hmJ).1
      have hmle := Nat.le_floor (hmt.trans htY)
      omega
    rw [he, Finset.sum_empty, abs_zero]
    simpa only [mul_assoc] using mul_nonneg (hK0.trans hKC) hscale
  have hYt : x ^ (11/20 + ε) ≤ t := (lt_of_not_ge htY).le
  have ht0 : 0 ≤ t := hY.le.trans hYt
  have htu : ⌊t⌋₊ ≤ ⌊2 * x ^ (11/20 + ε)⌋₊ := Nat.floor_le_floor ht
  have hfilter : (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t) =
      Finset.Ioc ⌊x ^ (11/20 + ε)⌋₊ ⌊t⌋₊ := by
    ext m
    have hmf : (m : ℝ) ≤ t ↔ m ≤ ⌊t⌋₊ := ⟨Nat.le_floor,
      fun hm => (Nat.cast_le.mpr hm).trans (Nat.floor_le ht0)⟩
    simp only [rightInterval, Finset.mem_filter, Finset.mem_Ioc, hmf]
    omega
  -- the ambient scale twice Y is past the prime number theorem threshold
  have hsq : Real.sqrt x ≤ x ^ (11/20 + ε) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  have hC1X : C1 ≤ 2 * x ^ (11/20 + ε) := by
    have h3 : |C1| ≤ Real.sqrt x := by
      rw [← Real.sqrt_sq_eq_abs]
      exact Real.sqrt_le_sqrt (h1C.trans hx)
    have := le_abs_self C1
    linarith
  have hb := h1 (2 * x ^ (11/20 + ε)) hC1X (x ^ (11/20 + ε)) t hY.le hYt ht
  have hhalf : 0 < Real.log x / 2 := by positivity
  have hpow : Real.log (2 * x ^ (11/20 + ε)) ^ (-A) ≤ (2 : ℝ) ^ A * Real.log x ^ (-A) := by
    calc _ ≤ (Real.log x / 2) ^ (-A) := by
          rw [Real.rpow_neg (hhalf.le.trans hloglow), Real.rpow_neg hhalf.le]
          exact inv_anti₀ (Real.rpow_pos_of_pos hhalf _)
            (Real.rpow_le_rpow hhalf.le hloglow hA.le)
      _ = _ := by
          rw [Real.div_rpow hlog.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
            div_inv_eq_mul, mul_comm]
  have hlogXpow : 0 ≤ Real.log (2 * x ^ (11/20 + ε)) ^ (-A) :=
    Real.rpow_nonneg (hhalf.le.trans hloglow) _
  rw [hfilter]
  calc _ ≤ C1 * (2 * x ^ (11/20 + ε)) * Real.log (2 * x ^ (11/20 + ε)) ^ (-A) := hb
    _ ≤ max C1 0 * (2 * x ^ (11/20 + ε)) * Real.log (2 * x ^ (11/20 + ε)) ^ (-A) := by
      gcongr
      exact le_max_left _ _
    _ ≤ max C1 0 * (2 * x ^ (11/20 + ε)) * ((2 : ℝ) ^ A * Real.log x ^ (-A)) :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = K * (x ^ (11/20 + ε) * Real.log x ^ (-A)) := by simp only [K]; ring
    _ ≤ C * (x ^ (11/20 + ε) * Real.log x ^ (-A)) :=
      mul_le_mul_of_nonneg_right hKC hscale
    _ = _ := by ring

end LeanLab.BHP1997.LowerShortC165
