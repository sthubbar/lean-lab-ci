/-
AI wrote this Lean code. Binary Goldbach is open.
P0026 pages 175 to 179, norm comparison and continuous cosine recurrence.
The degree 16 Taylor majorant is the certified variant from task125.
-/
import LeanLab.PlattTrudgian2014.Decomp125
import LeanLab.PlattTrudgian2014.TransferIteration125

namespace LeanLab.PlattTrudgian2014

open MeasureTheory Filter
open scoped Topology

/-- P0026 page 177, continuous moments with the angle rescaled to the unit interval. -/
noncomputable def halfProductMoment281 (L : ℕ) (i : Fin 16) : ℝ :=
  ∫ x : ℝ in 0..1, Real.cos (2 * Real.pi * (i : ℝ) * x) *
    ∏ j ∈ Finset.range L, halfCosPoly125 (2 * Real.pi * (2 : ℝ) ^ j * x)

/-- LEAF. P0026 page 179, continuous initial values below Lemma 6.
At length zero the zeroth moment is one and the other moments vanish. -/
theorem half_product_initial281 (i : Fin 16) :
    halfProductMoment281 0 i = if i = 0 then 1 else 0 := by
  unfold halfProductMoment281
  simp only [Finset.range_zero, Finset.prod_empty, mul_one]
  by_cases hi : i = 0
  · simp [hi]
  · have hn : (i : ℝ) ≠ 0 := by
      exact_mod_cast (show (i : ℕ) ≠ 0 from fun h => hi (Fin.ext h))
    rw [intervalIntegral.integral_comp_mul_left Real.cos
      (mul_ne_zero (mul_ne_zero (by norm_num) Real.pi_ne_zero) hn)]
    have hs : Real.sin (2 * Real.pi * (i : ℝ)) = 0 := by
      convert Real.sin_nat_mul_pi (2 * (i : ℕ)) using 1 <;> push_cast <;> ring
    simp [integral_cos, hs, hi]

/-- LEAF. P0026 pages 178 to 179, Lemmas 5 and 6.
The continuous cosine moments satisfy the certified finite matrix recurrence.
This is a finite integral identity and has no norm moment conclusion. -/
theorem half_product_recurrence281 (L : ℕ) (i : Fin 16) :
    halfProductMoment281 (L + 1) i =
      ∑ j : Fin 16, (halfTransfer125 i j : ℝ) * halfProductMoment281 L j := by
  sorry

/-- LEAF. P0026 page 177, display 5.2, followed by Lemma 7 on page 179.
Multiplying the positive pointwise majorants bounds the real exponential moment. -/
theorem half_real_moment_majorized281
    (hmajor : ∀ x : ℝ, Real.exp ((halfParameter125 : ℝ) * Real.cos x) ≤ halfCosPoly125 x)
    (L : ℕ) :
    (∫ x : ℝ in 0..1, Real.exp ((halfParameter125 : ℝ) * (G L x).re)) ≤
      halfProductMoment281 L 0 := by
  have he (x : ℝ) :
      Real.exp ((halfParameter125 : ℝ) * (G L x).re) =
        ∏ j ∈ Finset.range L,
          Real.exp ((halfParameter125 : ℝ) * Real.cos (2 * Real.pi * (2 : ℝ) ^ j * x)) := by
    rw [G_eq_sum_phase, Complex.re_sum, Finset.mul_sum, Real.exp_sum]
    apply Finset.prod_congr rfl
    intro j _
    unfold phase
    rw [Complex.exp_ofReal_mul_I_re]
    congr 3
    ring
  have hf : Continuous (fun x : ℝ => Real.exp ((halfParameter125 : ℝ) * (G L x).re)) := by
    fun_prop
  have hg : Continuous (fun x : ℝ =>
      ∏ j ∈ Finset.range L, halfCosPoly125 (2 * Real.pi * (2 : ℝ) ^ j * x)) := by
    unfold halfCosPoly125
    fun_prop
  unfold halfProductMoment281
  simp only [Fin.val_zero, Nat.cast_zero, mul_zero, zero_mul, Real.cos_zero, one_mul]
  apply intervalIntegral.integral_mono (by norm_num)
    (hf.intervalIntegrable _ _) (hg.intervalIntegrable _ _)
  intro x
  dsimp only
  rw [he]
  exact Finset.prod_le_prod₀ (fun j _ => Real.exp_nonneg _)
    (fun j _ => hmajor (2 * Real.pi * (2 : ℝ) ^ j * x))

/-- LEAF. P0026 pages 175 to 177, display 4.13 and the proof of Lemma 4.
For the nonnegative coefficients of t times G, the norm moment costs only a square root.
The comparison contains no transfer matrix or pressure assertion. -/
theorem norm_real_moment_comparison281 (t : ℝ) (ht : 0 ≤ t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ,
      (∫ x : ℝ in 0..1, Real.exp (t * ‖G L x‖)) ≤
        C * (1 + Real.sqrt (t * L)) *
          (∫ x : ℝ in 0..1, Real.exp (t * (G L x).re)) := by
  sorry

/-- LEAF. P0026 page 173 display 4.3, absorption of the prefactor in display 4.13.
Every positive exponential rate absorbs the square root prefactor uniformly in length. -/
theorem sqrt_prefactor_absorbed281 (t δ : ℝ) (ht : 0 ≤ t) (hδ : 0 < δ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ L : ℕ,
      1 + Real.sqrt (t * L) ≤ B * Real.exp (δ * L) := by
  refine ⟨2 + t / δ, by positivity, fun L => ?_⟩
  have hx : 0 ≤ t * (L : ℝ) := mul_nonneg ht (Nat.cast_nonneg L)
  have hs : Real.sqrt (t * L) ≤ 1 + t * L := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_nonneg (t * (L : ℝ))]
  have he : 1 ≤ Real.exp (δ * L) := Real.one_le_exp_iff.mpr (by positivity)
  have hd : δ * (L : ℝ) ≤ Real.exp (δ * L) := by
    linarith [Real.add_one_le_exp (δ * L)]
  have hm := mul_le_mul_of_nonneg_left hd (div_nonneg ht hδ.le)
  have hc : t / δ * (δ * (L : ℝ)) = t * L := by field_simp [hδ.ne']
  rw [hc] at hm
  nlinarith

/-- P0026 Theorem 2 and Lemmas 4 to 7, the exact sealed half norm moment target.
CONDITIONAL ON the open leaves above. The finite certificates and iteration are reused. -/
theorem half_norm_moment_transfer_decomposed281
    (hmajor : ∀ x : ℝ, Real.exp ((halfParameter125 : ℝ) * Real.cos x) ≤ halfCosPoly125 x)
    (hcoeff : ∀ j : Fin 17, 0 ≤ halfCoeff125 j)
    (hvec : ∀ j : Fin 16, 0 < halfVector125 j)
    (hcert : ∀ i : Fin 16, (∑ j : Fin 16, halfTransfer125 i j * halfVector125 j) ≤
      halfRadius125 * halfVector125 i) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ L : ℕ,
      (∫ x : ℝ in 0..1, Real.exp ((halfParameter125 : ℝ) * ‖G L x‖)) ≤
        A * Real.exp ((Real.log (halfRadius125 : ℝ) + 0.0000000000001) * L) := by
  have ht : (0 : ℝ) ≤ halfParameter125 := by exact_mod_cast half_parameter_box125.1.le
  have hr : (0 : ℝ) < halfRadius125 := by exact_mod_cast (lt_trans (by norm_num) half_radius_box125.1)
  have hU : ∀ i j : Fin 16, (0 : ℝ) ≤ halfTransfer125 i j := by
    intro i j
    have hb (k : ℤ) : 0 ≤ halfCoeffInt125 k := by
      unfold halfCoeffInt125
      split_ifs
      · exact hcoeff _
      · exact le_rfl
    have hb1 := hb (2 * (j : ℤ) - i)
    have hb2 := hb (2 * (j : ℤ) + i)
    have hb3 := hb ((i : ℤ) - 2 * j)
    have hu : 0 ≤ halfTransfer125 i j := by
      unfold halfTransfer125
      split_ifs <;> positivity
    exact_mod_cast hu
  have hw0 : (halfVector125 0 : ℝ) = 1 := by norm_num [halfVector125]
  have hbase : ∀ i : Fin 16, halfProductMoment281 0 i ≤ (halfVector125 i : ℝ) := by
    intro i
    rw [half_product_initial281]
    split_ifs with hi
    · simpa [hi, hw0]
    · exact_mod_cast (hvec i).le
  have hiter (L : ℕ) : halfProductMoment281 L 0 ≤ (halfRadius125 : ℝ) ^ L := by
    have hc (i : Fin 16) :
        (∑ j : Fin 16, (halfTransfer125 i j : ℝ) * (halfVector125 j : ℝ)) ≤
          (halfRadius125 : ℝ) * (halfVector125 i : ℝ) := by exact_mod_cast hcert i
    simpa [hw0] using transfer_iterate125
      (fun i j => (halfTransfer125 i j : ℝ)) (fun i => (halfVector125 i : ℝ))
      (halfRadius125 : ℝ) 1 halfProductMoment281 hU hr.le (by norm_num)
      (by simpa using hbase) half_product_recurrence281 hc L 0
  obtain ⟨C, hC, hcomp⟩ := norm_real_moment_comparison281 (halfParameter125 : ℝ) ht
  obtain ⟨B, hB, habs⟩ := sqrt_prefactor_absorbed281 (halfParameter125 : ℝ)
    0.0000000000001 ht (by norm_num)
  refine ⟨C * B, mul_nonneg hC hB, fun L => ?_⟩
  have hm := (half_real_moment_majorized281 hmajor L).trans (hiter L)
  calc
    _ ≤ C * (1 + Real.sqrt ((halfParameter125 : ℝ) * L)) * (halfRadius125 : ℝ) ^ L :=
      (hcomp L).trans (mul_le_mul_of_nonneg_left hm (by positivity))
    _ ≤ C * (B * Real.exp (0.0000000000001 * L)) * (halfRadius125 : ℝ) ^ L := by
      gcongr
      exact habs L
    _ = C * B * (Real.exp (0.0000000000001 * L) *
        Real.exp (Real.log (halfRadius125 : ℝ) * L)) := by
      have hp : (halfRadius125 : ℝ) ^ L =
          Real.exp (Real.log (halfRadius125 : ℝ) * L) := by
        rw [mul_comm, Real.exp_nat_mul, Real.exp_log hr]
      rw [hp]
      ring
    _ = _ := by
      rw [← Real.exp_add]
      congr 2
      ring

set_option format.width 240

#print axioms half_product_initial281
#print axioms half_product_recurrence281
#print axioms half_real_moment_majorized281
#print axioms norm_real_moment_comparison281
#print axioms sqrt_prefactor_absorbed281
#print axioms half_norm_moment_transfer_decomposed281

end LeanLab.PlattTrudgian2014
