/-
P0069, Section 5, page 51, display 5.17.
Uniform variation in the three outer exponent coordinates.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.FourExponentOuterRegularity517
import LeanLab.BHP1997.FourExponentVariationTools517
import LeanLab.BHP1997.FourExponentVariation517

namespace LeanLab.BHP1997.LowerShortC165
open Classical Decomp514a
open scoped BigOperators

/-- Page 51 display 5.17. The a coordinate kernel variation is bounded
by its smooth change and the 601 active region and Buchstab jumps. -/
theorem four_exponent_kernel_variation_a {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (s b c d : ℝ) (z : ℕ → ℝ) (hm : Monotone z)
    {lo hi : ℕ} (hlo : lo ≤ hi) :
    (∑ i ∈ Finset.Ico lo hi,
      |fourExponentKernel ω ε s (z (i+1)) b c d - fourExponentKernel ω ε s (z i) b c d|) ≤
        2000000*(z hi-z lo)+60100000 := by
  classical
  let f := fun v : ℝ => fourExponentKernel ω ε s v b c d
  let P := fun v : ℝ => lowerFourRegion ε v b c d ∧ 2*d ≤ s-v-b-c
  have hf : ∀ v : ℝ, |f v| ≤ (10 : ℝ)^5 := fun v => by
    simpa only [f, fourExponentKernel] using four_density_integrand_bound hω hz hε hε8 s v b c d
  have hzP : ∀ v : ℝ, ¬ P v → f v = 0 := by
    intro v hv
    change fourExponentKernel ω ε s v b c d = 0
    rw [four_exponent_kernel_active hε hε8 ω s v b c d]
    exact if_neg hv
  have hlip : ∀ u v : ℝ, P u → P v → |f v-f u| ≤ 2000000*|v-u| := by
    intro u v hu hv
    have hd := (four_density_region_box hε hε8 hu.1).1
    have hd0 : 0 < d := by linarith
    have huarg : 1 ≤ (s-u-b-c-d)/d := (le_div_iff₀ hd0).mpr (by linarith [hu.2])
    have hvarg : 1 ≤ (s-v-b-c-d)/d := (le_div_iff₀ hd0).mpr (by linarith [hv.2])
    exact four_exponent_kernel_coordinate_a hω hz hε hε8 hv.1 hu.1 hvarg huarg
  have hr := four_region_jumps ε z hm 0 1 b 0 c 0 d 0 lo hi
  simp only [zero_mul, add_zero, one_mul, zero_add] at hr
  have hc := four_atom_jump hm (fun _ => 2*d) (fun n => s-(z n)-b-c)
    (-1) (s-b-c-2*d) (fun n => by ring) lo hi
  have hJ : (∑ i ∈ Finset.Ico lo hi,
      |(if P (z (i+1)) then (1 : ℝ) else 0)-(if P (z i) then (1 : ℝ) else 0)|) ≤ 601 := by
    exact (indicator_variation_and_le
      (fun n => lowerFourRegion ε (z n) b c d)
      (fun n => 2*d ≤ s-(z n)-b-c) (Finset.Ico lo hi)).trans (by linarith)
  have h := four_exponent_piecewise_variation f P (by norm_num : (0 : ℝ) ≤ 2000000)
    (by norm_num : (0 : ℝ) ≤ 10^5) hf hzP hlip z hm hlo (J := 601) (by
      convert hJ using 1
      apply Finset.sum_congr rfl
      intro i hiS
      by_cases h1 : P (z (i+1)) <;> by_cases h0 : P (z i) <;> simp [h1, h0])
  norm_num at h
  exact h

/-- Page 51 display 5.17. The b coordinate kernel variation is bounded
by its smooth change and the 601 active region and Buchstab jumps. -/
theorem four_exponent_kernel_variation_b {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (s a c d : ℝ) (z : ℕ → ℝ) (hm : Monotone z)
    {lo hi : ℕ} (hlo : lo ≤ hi) :
    (∑ i ∈ Finset.Ico lo hi,
      |fourExponentKernel ω ε s a (z (i+1)) c d - fourExponentKernel ω ε s a (z i) c d|) ≤
        2000000*(z hi-z lo)+60100000 := by
  classical
  let f := fun v : ℝ => fourExponentKernel ω ε s a v c d
  let P := fun v : ℝ => lowerFourRegion ε a v c d ∧ 2*d ≤ s-a-v-c
  have hf : ∀ v : ℝ, |f v| ≤ (10 : ℝ)^5 := fun v => by
    simpa only [f, fourExponentKernel] using four_density_integrand_bound hω hz hε hε8 s a v c d
  have hzP : ∀ v : ℝ, ¬ P v → f v = 0 := by
    intro v hv
    change fourExponentKernel ω ε s a v c d = 0
    rw [four_exponent_kernel_active hε hε8 ω s a v c d]
    exact if_neg hv
  have hlip : ∀ u v : ℝ, P u → P v → |f v-f u| ≤ 2000000*|v-u| := by
    intro u v hu hv
    have hd := (four_density_region_box hε hε8 hu.1).1
    have hd0 : 0 < d := by linarith
    have huarg : 1 ≤ (s-a-u-c-d)/d := (le_div_iff₀ hd0).mpr (by linarith [hu.2])
    have hvarg : 1 ≤ (s-a-v-c-d)/d := (le_div_iff₀ hd0).mpr (by linarith [hv.2])
    exact four_exponent_kernel_coordinate_b hω hz hε hε8 hv.1 hu.1 hvarg huarg
  have hr := four_region_jumps ε z hm a 0 0 1 c 0 d 0 lo hi
  simp only [zero_mul, add_zero, one_mul, zero_add] at hr
  have hc := four_atom_jump hm (fun _ => 2*d) (fun n => s-a-(z n)-c)
    (-1) (s-a-c-2*d) (fun n => by ring) lo hi
  have hJ : (∑ i ∈ Finset.Ico lo hi,
      |(if P (z (i+1)) then (1 : ℝ) else 0)-(if P (z i) then (1 : ℝ) else 0)|) ≤ 601 := by
    exact (indicator_variation_and_le
      (fun n => lowerFourRegion ε a (z n) c d)
      (fun n => 2*d ≤ s-a-(z n)-c) (Finset.Ico lo hi)).trans (by linarith)
  have h := four_exponent_piecewise_variation f P (by norm_num : (0 : ℝ) ≤ 2000000)
    (by norm_num : (0 : ℝ) ≤ 10^5) hf hzP hlip z hm hlo (J := 601) (by
      convert hJ using 1
      apply Finset.sum_congr rfl
      intro i hiS
      by_cases h1 : P (z (i+1)) <;> by_cases h0 : P (z i) <;> simp [h1, h0])
  norm_num at h
  exact h

/-- Page 51 display 5.17. The c coordinate kernel variation is bounded
by its smooth change and the 601 active region and Buchstab jumps. -/
theorem four_exponent_kernel_variation_c {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    (s a b d : ℝ) (z : ℕ → ℝ) (hm : Monotone z)
    {lo hi : ℕ} (hlo : lo ≤ hi) :
    (∑ i ∈ Finset.Ico lo hi,
      |fourExponentKernel ω ε s a b (z (i+1)) d - fourExponentKernel ω ε s a b (z i) d|) ≤
        2000000*(z hi-z lo)+60100000 := by
  classical
  let f := fun v : ℝ => fourExponentKernel ω ε s a b v d
  let P := fun v : ℝ => lowerFourRegion ε a b v d ∧ 2*d ≤ s-a-b-v
  have hf : ∀ v : ℝ, |f v| ≤ (10 : ℝ)^5 := fun v => by
    simpa only [f, fourExponentKernel] using four_density_integrand_bound hω hz hε hε8 s a b v d
  have hzP : ∀ v : ℝ, ¬ P v → f v = 0 := by
    intro v hv
    change fourExponentKernel ω ε s a b v d = 0
    rw [four_exponent_kernel_active hε hε8 ω s a b v d]
    exact if_neg hv
  have hlip : ∀ u v : ℝ, P u → P v → |f v-f u| ≤ 2000000*|v-u| := by
    intro u v hu hv
    have hd := (four_density_region_box hε hε8 hu.1).1
    have hd0 : 0 < d := by linarith
    have huarg : 1 ≤ (s-a-b-u-d)/d := (le_div_iff₀ hd0).mpr (by linarith [hu.2])
    have hvarg : 1 ≤ (s-a-b-v-d)/d := (le_div_iff₀ hd0).mpr (by linarith [hv.2])
    exact four_exponent_kernel_coordinate_c hω hz hε hε8 hv.1 hu.1 hvarg huarg
  have hr := four_region_jumps ε z hm a 0 b 0 0 1 d 0 lo hi
  simp only [zero_mul, add_zero, one_mul, zero_add] at hr
  have hc := four_atom_jump hm (fun _ => 2*d) (fun n => s-a-b-(z n))
    (-1) (s-a-b-2*d) (fun n => by ring) lo hi
  have hJ : (∑ i ∈ Finset.Ico lo hi,
      |(if P (z (i+1)) then (1 : ℝ) else 0)-(if P (z i) then (1 : ℝ) else 0)|) ≤ 601 := by
    exact (indicator_variation_and_le
      (fun n => lowerFourRegion ε a b (z n) d)
      (fun n => 2*d ≤ s-a-b-(z n)) (Finset.Ico lo hi)).trans (by linarith)
  have h := four_exponent_piecewise_variation f P (by norm_num : (0 : ℝ) ≤ 2000000)
    (by norm_num : (0 : ℝ) ≤ 10^5) hf hzP hlip z hm hlo (J := 601) (by
      convert hJ using 1
      apply Finset.sum_congr rfl
      intro i hiS
      by_cases h1 : P (z (i+1)) <;> by_cases h0 : P (z i) <;> simp [h1, h0])
  norm_num at h
  exact h

#print axioms four_exponent_kernel_variation_a
#print axioms four_exponent_kernel_variation_b
#print axioms four_exponent_kernel_variation_c
end LeanLab.BHP1997.LowerShortC165
