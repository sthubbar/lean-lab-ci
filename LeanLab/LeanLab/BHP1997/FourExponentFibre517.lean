/-
P0069, Section 5, page 51, display 5.17.
The integer quadrature on a last exponent fibre with explicit logarithmic
endpoints. The exterior support and strict ordering are separate finite
sum steps in the full four variable estimate.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.FourExponentVariation517
import LeanLab.BHP1997.FourExponentBV517

namespace LeanLab.BHP1997.LowerShortC165
open MeasureTheory
open scoped BigOperators

/-- Page 51 display 5.17. A last coordinate integer quadrature, including
all region and Buchstab jumps, saves its lower integer cutoff. -/
theorem four_exponent_kernel_log_quadrature_d {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε s Z : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hZ : 1 < Z)
    (a b c : ℝ) (L N : ℕ) (hL : 1 ≤ L)
    (hN : (L : ℝ)+(N : ℝ)+1 ≤ Z) :
    |(∑ i ∈ Finset.range N,
        fourExponentKernel ω ε s a b c (Real.log ((L : ℝ)+(i : ℝ)+1) / Real.log Z) /
          (((L : ℝ)+(i : ℝ)+1) * Real.log Z)) -
        ∫ t in (Real.log ((L : ℝ)+1) / Real.log Z)..
          (Real.log ((L : ℝ)+(N : ℝ)+1) / Real.log Z),
            fourExponentKernel ω ε s a b c t| ≤
      200000000 / ((L : ℝ) * Real.log Z) := by
  let l := Real.log ((L : ℝ)+1) / Real.log Z
  let r := Real.log ((L : ℝ)+(N : ℝ)+1) / Real.log Z
  have hlog : 0 < Real.log Z := Real.log_pos hZ
  have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hN0 : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  have hl0 : 0 ≤ l := div_nonneg (Real.log_nonneg (by linarith)) hlog.le
  have hlr : l ≤ r := div_le_div_of_nonneg_right
    (Real.log_le_log (by linarith) (by linarith)) hlog.le
  have hr1 : r ≤ 1 := (div_le_one hlog).mpr (Real.log_le_log (by linarith) hN)
  have hvar := four_exponent_kernel_evariation_d hω hz hε hε8 hs0 hs1 a b c l r hlr
  have hv : eVariationOn (fourExponentKernel ω ε s a b c) (Set.Icc l r) ≤
      ENNReal.ofReal 120100000 :=
    hvar.trans (ENNReal.ofReal_le_ofReal (by linarith))
  have hvr : (eVariationOn (fourExponentKernel ω ε s a b c) (Set.Icc l r)).toReal ≤
      120100000 := by
    have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top hv
    norm_num at h
    exact h
  have hi := four_exponent_kernel_integrable_d hω hz hε hε8 s a b c l r
  have hb := four_exponent_kernel_bounded_variation_d hω hz hε hε8 hs0 hs1 a b c l r hlr
  have hq := four_exponent_log_bv_quadrature (fourExponentKernel ω ε s a b c)
    hZ (by norm_num : (0 : ℝ) ≤ 10^5) L N hL
    (fun i _ => by
      simpa only [fourExponentKernel] using
        Decomp514a.four_density_integrand_bound hω hz hε hε8 s a b c
          (Real.log ((L : ℝ)+(i : ℝ)+1) / Real.log Z)) hi hb
  refine hq.trans ?_
  exact div_le_div_of_nonneg_right (by linarith) (by positivity)

/-- Page 51 display 5.17. The last exponent support stays strictly inside
the displayed integration box. The kernel vanishes on both exterior tails. -/
theorem four_exponent_kernel_d_support {ω : ℝ → ℝ} {ε : ℝ}
    (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (s a b c d : ℝ)
    (hd : d ≤ DecompC165d.lowerFourGridReal 0 ∨ DecompC165d.lowerFourGridReal 128 ≤ d) :
    fourExponentKernel ω ε s a b c d = 0 := by
  by_cases hr : lowerFourRegion ε a b c d
  · have hmin := hr.1
    have hmax := (Decomp514a.four_density_region_box hε hε8 hr).2.2.2.2.1
    have hlo : DecompC165d.lowerFourGridReal 0 < d := by
      norm_num [DecompC165d.lowerFourGridReal, DecompC165d.lowerFourGridPoint] at hmin hε8 ⊢
      linarith
    have hhi : d < DecompC165d.lowerFourGridReal 128 := by
      norm_num [DecompC165d.lowerFourGridReal, DecompC165d.lowerFourGridPoint] at hmax ⊢
      linarith
    rcases hd with hd | hd <;> linarith
  · simp only [fourExponentKernel, if_neg hr]

/-- Page 51 display 5.17. Extending a last coordinate integral beyond the
actual grid box adds only zero tails. -/
theorem four_exponent_kernel_extend_interval_d {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8) (s a b c l r : ℝ)
    (hl : l ≤ DecompC165d.lowerFourGridReal 0)
    (hr : DecompC165d.lowerFourGridReal 128 ≤ r) :
    (∫ t in l..r, fourExponentKernel ω ε s a b c t) =
      ∫ t in DecompC165d.lowerFourGridReal 0..DecompC165d.lowerFourGridReal 128,
        fourExponentKernel ω ε s a b c t := by
  have hlo : (∫ t in l..DecompC165d.lowerFourGridReal 0,
      fourExponentKernel ω ε s a b c t) = 0 := by
    apply intervalIntegral.integral_zero_ae
    apply Filter.Eventually.of_forall
    intro t ht
    rw [Set.uIoc_of_le hl] at ht
    exact four_exponent_kernel_d_support hε hε8 s a b c t (Or.inl ht.2)
  have hhi : (∫ t in DecompC165d.lowerFourGridReal 128..r,
      fourExponentKernel ω ε s a b c t) = 0 := by
    apply intervalIntegral.integral_zero_ae
    apply Filter.Eventually.of_forall
    intro t ht
    rw [Set.uIoc_of_le hr] at ht
    exact four_exponent_kernel_d_support hε hε8 s a b c t (Or.inr ht.1.le)
  have h1 := intervalIntegral.integral_add_adjacent_intervals
    (four_exponent_kernel_integrable_d hω hz hε hε8 s a b c l (DecompC165d.lowerFourGridReal 0))
    (four_exponent_kernel_integrable_d hω hz hε hε8 s a b c
      (DecompC165d.lowerFourGridReal 0) (DecompC165d.lowerFourGridReal 128))
  have h2 := intervalIntegral.integral_add_adjacent_intervals
    (four_exponent_kernel_integrable_d hω hz hε hε8 s a b c l (DecompC165d.lowerFourGridReal 128))
    (four_exponent_kernel_integrable_d hω hz hε hε8 s a b c (DecompC165d.lowerFourGridReal 128) r)
  rw [hlo, zero_add] at h1
  rw [hhi, add_zero] at h2
  exact h2.symm.trans h1.symm

/-- Page 51 display 5.17. Aligning complete logarithmic cells with the
full integration box costs nothing outside the E4 support. -/
theorem four_exponent_kernel_full_grid_d {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε s Z : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hZ : 1 < Z)
    (a b c : ℝ) (L N : ℕ) (hL : 1 ≤ L) (hLN : L ≤ N)
    (hN : (N : ℝ)+1 ≤ Z)
    (hlo : Real.log ((L : ℝ)+1) / Real.log Z ≤ DecompC165d.lowerFourGridReal 0)
    (hhi : DecompC165d.lowerFourGridReal 128 ≤ Real.log ((N : ℝ)+1) / Real.log Z) :
    |(∑ n ∈ Finset.Icc 1 N,
        fourExponentKernel ω ε s a b c (Real.log (n : ℝ) / Real.log Z) /
          ((n : ℝ) * Real.log Z)) -
        ∫ t in DecompC165d.lowerFourGridReal 0..DecompC165d.lowerFourGridReal 128,
          fourExponentKernel ω ε s a b c t| ≤
      200000000 / ((L : ℝ) * Real.log Z) := by
  let f : ℕ → ℝ := fun n =>
    fourExponentKernel ω ε s a b c (Real.log (n : ℝ) / Real.log Z) /
      ((n : ℝ) * Real.log Z)
  have hlog : 0 < Real.log Z := Real.log_pos hZ
  have hpre : ∑ n ∈ Finset.Ioc 0 L, f n = 0 := by
    apply Finset.sum_eq_zero
    intro n hn
    obtain ⟨hn0, hnL⟩ := Finset.mem_Ioc.mp hn
    have hnreal : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn0
    have hnlt : (n : ℝ) < (L : ℝ)+1 := by exact_mod_cast Nat.lt_succ_of_le hnL
    have hlt := (div_lt_div_iff_of_pos_right hlog).mpr (Real.log_lt_log hnreal hnlt)
    change fourExponentKernel ω ε s a b c (Real.log (n : ℝ) / Real.log Z) /
      ((n : ℝ) * Real.log Z) = 0
    rw [four_exponent_kernel_d_support hε hε8 s a b c _ (Or.inl (hlt.le.trans hlo)), zero_div]
  have hsum : (∑ n ∈ Finset.Icc 1 N, f n) =
      ∑ i ∈ Finset.range (N-L),
        fourExponentKernel ω ε s a b c (Real.log ((L : ℝ)+(i : ℝ)+1) / Real.log Z) /
          (((L : ℝ)+(i : ℝ)+1) * Real.log Z) := by
    have hs := Finset.sum_Ioc_consecutive f (Nat.zero_le L) hLN
    have heq0 : Finset.Ioc 0 N = Finset.Icc 1 N := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Icc]
      omega
    rw [hpre, zero_add, heq0] at hs
    rw [← hs]
    have heq : Finset.Ioc L N = Finset.Ico (L+1) (N+1) := by
      ext n
      simp only [Finset.mem_Ioc, Finset.mem_Ico]
      omega
    have hlen : N+1-(L+1) = N-L := by omega
    rw [heq, Finset.sum_Ico_eq_sum_range, hlen]
    apply Finset.sum_congr rfl
    intro i _
    have hidx : L+1+i = L+i+1 := by omega
    simp only [hidx, f, Nat.cast_add, Nat.cast_one]
  have hend : (L : ℝ)+((N-L : ℕ) : ℝ)+1 = (N : ℝ)+1 := by
    rw [Nat.cast_sub hLN]
    ring
  have hq := four_exponent_kernel_log_quadrature_d hω hz hε hε8 hs0 hs1 hZ a b c L (N-L) hL
    (by rw [hend]; exact hN)
  rw [hend] at hq
  have hext := four_exponent_kernel_extend_interval_d hω hz hε hε8 s a b c
    (Real.log ((L : ℝ)+1) / Real.log Z) (Real.log ((N : ℝ)+1) / Real.log Z) hlo hhi
  rw [hext] at hq
  change |(∑ n ∈ Finset.Icc 1 N, f n) - _| ≤ _
  rw [hsum]
  exact hq

/-- Page 51 display 5.17. Strict last integer ordering removes one
endpoint term. Its cost has the same lower cutoff saving as the quadrature. -/
theorem four_exponent_kernel_strict_grid_d {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε s Z : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (hs0 : 0 ≤ s) (hs1 : s ≤ 1) (hZ : 1 < Z)
    (a b : ℝ) (L N q : ℕ) (hL : 1 ≤ L) (hLN : L ≤ N)
    (hq : q ∈ Finset.Icc 1 N) (hN : (N : ℝ)+1 ≤ Z)
    (hlo : Real.log ((L : ℝ)+1) / Real.log Z ≤ DecompC165d.lowerFourGridReal 0)
    (hhi : DecompC165d.lowerFourGridReal 128 ≤ Real.log ((N : ℝ)+1) / Real.log Z) :
    |(∑ n ∈ Finset.Icc 1 N,
        if n < q then
          fourExponentKernel ω ε s a b (Real.log (q : ℝ) / Real.log Z)
            (Real.log (n : ℝ) / Real.log Z) / ((n : ℝ) * Real.log Z)
        else 0) -
        ∫ t in DecompC165d.lowerFourGridReal 0..DecompC165d.lowerFourGridReal 128,
          fourExponentKernel ω ε s a b (Real.log (q : ℝ) / Real.log Z) t| ≤
      200100000 / ((L : ℝ) * Real.log Z) := by
  let B := Finset.Icc 1 N
  let c := Real.log (q : ℝ) / Real.log Z
  let f : ℕ → ℝ := fun n =>
    fourExponentKernel ω ε s a b c (Real.log (n : ℝ) / Real.log Z) / ((n : ℝ) * Real.log Z)
  have hlog : 0 < Real.log Z := Real.log_pos hZ
  have hL0 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (show 0 < L by omega)
  have hq1 := (Finset.mem_Icc.mp hq).1
  have hq0 : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (show 0 < q by omega)
  have hzero : ∀ n ∈ B, q < n → f n = 0 := by
    intro n hn hqn
    have hlt : c < Real.log (n : ℝ) / Real.log Z :=
      (div_lt_div_iff_of_pos_right hlog).mpr
        (Real.log_lt_log hq0 (by exact_mod_cast hqn))
    by_cases hr : lowerFourRegion ε a b c (Real.log (n : ℝ) / Real.log Z)
    · have h := hr.2.1
      linarith
    · simp only [f, fourExponentKernel, if_neg hr, zero_div]
  have hstrict : (∑ n ∈ B, if n < q then f n else 0) = (∑ n ∈ B, f n) - f q := by
    have hs := Finset.sum_erase_add B f hq
    have hg := Finset.sum_erase_add B (fun n => if n < q then f n else 0) hq
    have he : (∑ n ∈ B.erase q, if n < q then f n else 0) = ∑ n ∈ B.erase q, f n := by
      apply Finset.sum_congr rfl
      intro n hn
      obtain ⟨hnq, hnB⟩ := Finset.mem_erase.mp hn
      by_cases h : n < q
      · simp only [if_pos h]
      · rw [if_neg h, hzero n hnB (by omega)]
    rw [he, if_neg (lt_irrefl q), add_zero] at hg
    linarith
  have hM : |f q| ≤ (10 : ℝ)^5 / ((L : ℝ) * Real.log Z) := by
    by_cases hqL : q ≤ L
    · have hlt : c < Real.log ((L : ℝ)+1) / Real.log Z :=
        (div_lt_div_iff_of_pos_right hlog).mpr
          (Real.log_lt_log hq0 (by exact_mod_cast Nat.lt_succ_of_le hqL))
      have hzq := four_exponent_kernel_d_support (ω := ω) hε hε8 s a b c c (Or.inl (hlt.le.trans hlo))
      change |fourExponentKernel ω ε s a b c c / ((q : ℝ)*Real.log Z)| ≤ _
      rw [hzq, zero_div, abs_zero]
      positivity
    · have hden : (L : ℝ)*Real.log Z ≤ (q : ℝ)*Real.log Z :=
        mul_le_mul_of_nonneg_right (by exact_mod_cast (show L ≤ q by omega)) hlog.le
      change |fourExponentKernel ω ε s a b c c / ((q : ℝ)*Real.log Z)| ≤ _
      rw [abs_div, abs_of_pos (mul_pos hq0 hlog)]
      calc _ ≤ (10 : ℝ)^5 / ((q : ℝ)*Real.log Z) :=
          div_le_div_of_nonneg_right
            (by simpa only [fourExponentKernel] using
              Decomp514a.four_density_integrand_bound hω hz hε hε8 s a b c c)
            (by positivity)
        _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) (by positivity) hden
  have hg := four_exponent_kernel_full_grid_d hω hz hε hε8 hs0 hs1 hZ a b c L N hL hLN hN hlo hhi
  change |(∑ n ∈ B, if n < q then f n else 0) - _| ≤ _
  rw [hstrict]
  calc _ = |((∑ n ∈ B, f n) -
        ∫ t in DecompC165d.lowerFourGridReal 0..DecompC165d.lowerFourGridReal 128,
          fourExponentKernel ω ε s a b c t) - f q| := by congr 1; ring
    _ ≤ |(∑ n ∈ B, f n) -
        ∫ t in DecompC165d.lowerFourGridReal 0..DecompC165d.lowerFourGridReal 128,
          fourExponentKernel ω ε s a b c t| + |f q| := abs_sub _ _
    _ ≤ 200000000 / ((L : ℝ)*Real.log Z) + 10^5 / ((L : ℝ)*Real.log Z) := add_le_add hg hM
    _ = _ := by ring

#print axioms four_exponent_kernel_log_quadrature_d
#print axioms four_exponent_kernel_d_support
#print axioms four_exponent_kernel_extend_interval_d
#print axioms four_exponent_kernel_full_grid_d
#print axioms four_exponent_kernel_strict_grid_d
end LeanLab.BHP1997.LowerShortC165
