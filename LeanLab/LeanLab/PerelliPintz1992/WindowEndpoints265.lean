/-
P0070, pages 364 and 365. Quarter radius and the clipping endpoint error.
These bounds retain the endpoint contribution. They do not close Estimate7.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.PerelliPintz1992.Decomp97a

namespace LeanLab.PerelliPintz1992.Section6
open Real MeasureTheory Set Filter
open scoped ENNReal NNReal
noncomputable section
attribute [local instance] Classical.propDecidable

/-- Page 364, the corrected quarter radius Prop follows from the proved comparison.
The existential logarithmic exponent can be zero. -/
theorem characterGallagherStep_quarter : CharacterGallagherStep := by
  refine ⟨Real.pi ^ 2 / 16, 1, 0, by positivity, ?_⟩
  intro N hN q hq χ
  have hNp : 0 < N := by
    have : 1 ≤ N := by exact_mod_cast hN
    omega
  simpa only [pow_zero, mul_one] using character_gallagher_quarter hNp hq χ

/-- Page 365, the endpoint term contains exactly the terms of the moving interval
outside the clipped coefficient support from N through two N. -/
def characterEndpointSum (N : ℕ) {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ)) (x h : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊).filter (fun n => n < N ∨ 2 * N < n),
    ((ArithmeticFunction.vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0)

/-- Pages 364 and 365, exact decomposition into clipped and endpoint sums. -/
theorem movingCharacterSum_eq_clipped_add_endpoint (N : ℕ) {q : ℕ+}
    (χ : DirichletCharacter ℂ (q : ℕ)) (x h : ℝ) (hxh : 0 ≤ x + h) :
    movingCharacterSum χ x h =
      (∑ n ∈ (Finset.Icc N (2 * N)).filter
        (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + h),
        ((ArithmeticFunction.vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0)) +
      characterEndpointSum N χ x h := by
  let s := Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0
  have hi : s.filter (fun n => N ≤ n ∧ n ≤ 2 * N) =
      (Finset.Icc N (2 * N)).filter (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + h) := by
    ext n
    simp only [s, Finset.mem_filter, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hxh]
    tauto
  have ho : s.filter (fun n => ¬ (N ≤ n ∧ n ≤ 2 * N)) =
      s.filter (fun n => n < N ∨ 2 * N < n) := by
    ext n
    simp only [Finset.mem_filter, not_and_or, not_le]
  have hs := Finset.sum_filter_add_sum_filter_not s (fun n => N ≤ n ∧ n ≤ 2 * N) f
  rw [hi, ho] at hs
  by_cases hc : χ = 1
  · simpa only [s, f, movingCharacterSum, characterEndpointSum, ite_eq_left hc] using hs.symm
  · simpa only [s, f, movingCharacterSum, characterEndpointSum, ite_eq_right hc] using hs.symm

/-- Pages 364 and 365, finite natural windows have genuine Lp norms.
This uses Mathlib interval indicators and finite sums. -/
theorem nat_inclusive_window_memLp (s : Finset ℕ) (a : ℕ → ℂ) (h : ℝ) (p : ℝ≥0∞) :
    MemLp (fun x : ℝ => ∑ n ∈ s.filter
      (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + h), a n) p := by
  have he : (fun x : ℝ => ∑ n ∈ s.filter
      (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + h), a n) =
      fun x : ℝ => ∑ n ∈ s, (Icc ((n : ℝ) - h) n).indicator (fun _ => a n) x := by
    funext x
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro n hn
    have hp : (x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + h) ↔ (n : ℝ) - h ≤ x ∧ x ≤ n := by
      constructor <;> rintro ⟨h₁, h₂⟩ <;> constructor <;> linarith
    simp only [Set.indicator_apply, Set.mem_Icc, hp]
  rw [he]
  apply memLp_finsetSum
  intro n hn
  exact memLp_indicator_const p measurableSet_Icc.nullMeasurableSet (a n)
    (Or.inr (by simp))

/-- Page 365, an unclipped character interval on a bounded positive x range is Lp.
The upper endpoint bound makes its coefficient support a fixed finite set. -/
theorem movingCharacterSum_memLp_restrict {q : ℕ+} (χ : DirichletCharacter ℂ (q : ℕ))
    (M : ℕ) (a b h : ℝ) (ha : 0 ≤ a) (hh : 0 ≤ h) (hM : b + h ≤ M) (p : ℝ≥0∞) :
    MemLp (fun x : ℝ => movingCharacterSum χ x h) p (volume.restrict (Ioc a b)) := by
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0
  apply (memLp_congr_ae ?_).mp ((nat_inclusive_window_memLp (Finset.Icc 0 M) f h p).restrict (Ioc a b))
  filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
  have hxh : 0 ≤ x + h := by linarith [hx.1]
  have he : Finset.Icc ⌈x⌉₊ ⌊x + h⌋₊ = (Finset.Icc 0 M).filter
      (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + h) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Nat.ceil_le, Nat.le_floor_iff hxh]
    constructor
    · rintro ⟨h₁, h₂⟩
      have hnM : (n : ℝ) ≤ M := by linarith [hx.2]
      exact ⟨⟨Nat.zero_le n, by exact_mod_cast hnM⟩, h₁, h₂⟩
    · tauto
  unfold movingCharacterSum
  rw [he]
  by_cases hc : χ = 1
  · simp only [f, ite_eq_left hc]
  · simp only [f, ite_eq_right hc]

/-- Pages 364 and 365, the sealed clipped W is controlled by the unclipped window
plus its explicit endpoint mean square. No endpoint term is discarded. -/
theorem W_sq_le_unclipped_add_endpoint {N : ℕ} (hN : 0 < N) {q : ℕ+}
    (hq : (q : ℝ) ≤ Decomp97.Q N) (χ : DirichletCharacter ℂ (q : ℕ)) :
    Decomp97.W N χ ^ 2 ≤
      (2 / ((N : ℝ) * ((q : ℝ) * Decomp97.Q N) ^ 2)) *
        (∫ x in Ioc ((N : ℝ) / 2) (2 * N : ℝ),
          ‖movingCharacterSum χ x (2 * (q : ℝ) * Decomp97.Q N)‖ ^ 2) +
      (2 / ((N : ℝ) * ((q : ℝ) * Decomp97.Q N) ^ 2)) *
        (∫ x in Ioc ((N : ℝ) / 2) (2 * N : ℝ),
          ‖characterEndpointSum N χ x (2 * (q : ℝ) * Decomp97.Q N)‖ ^ 2) := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast hN
  have hqp : (0 : ℝ) < q := by exact_mod_cast q.property
  have hQp : 0 < Decomp97.Q N := hqp.trans_le hq
  have hQsq : (Decomp97.Q N) ^ 2 = (N : ℝ) / 4 := by
    unfold Decomp97.Q
    rw [← Real.sqrt_eq_rpow]
    nlinarith [Real.sq_sqrt (Nat.cast_nonneg N)]
  let h := 2 * (q : ℝ) * Decomp97.Q N
  have hh : 0 ≤ h := by dsimp [h]; positivity
  have hshort : h ≤ (N : ℝ) / 2 := by
    dsimp [h]
    nlinarith [mul_le_mul_of_nonneg_right hq hQp.le]
  let A := Ioc ((N : ℝ) / 2) (2 * N : ℝ)
  let f : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0
  let w : ℝ → ℂ := fun x => ∑ n ∈ (Finset.Icc N (2 * N)).filter
    (fun n : ℕ => x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + h), f n
  let u : ℝ → ℂ := fun x => movingCharacterSum χ x h
  let v : ℝ → ℂ := fun x => characterEndpointSum N χ x h
  have hsplit (x : ℝ) (hx : x ∈ A) : u x = w x + v x :=
    movingCharacterSum_eq_clipped_add_endpoint N χ x h (by dsimp [A] at hx; linarith [hx.1])
  have hwm : MemLp w 2 (volume.restrict A) :=
    (nat_inclusive_window_memLp (Finset.Icc N (2 * N)) f h 2).restrict A
  have hum : MemLp u 2 (volume.restrict A) :=
    movingCharacterSum_memLp_restrict χ (3 * N) ((N : ℝ) / 2) (2 * N) h
      (by positivity) hh (by push_cast; linarith) 2
  have hvm : MemLp v 2 (volume.restrict A) := by
    apply (memLp_congr_ae ?_).mp (hum.sub hwm)
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    change u x - w x = v x
    rw [hsplit x hx]
    abel
  have hw := (memLp_two_iff_integrable_sq_norm hwm.aestronglyMeasurable).mp hwm
  have hu := (memLp_two_iff_integrable_sq_norm hum.aestronglyMeasurable).mp hum
  have hv := (memLp_two_iff_integrable_sq_norm hvm.aestronglyMeasurable).mp hvm
  have hi : (∫ x in A, ‖w x‖ ^ 2) ≤
      2 * (∫ x in A, ‖u x‖ ^ 2) + 2 * (∫ x in A, ‖v x‖ ^ 2) := by
    rw [← integral_const_mul, ← integral_const_mul, ← integral_add (hu.const_mul 2) (hv.const_mul 2)]
    apply integral_mono_ae hw ((hu.const_mul 2).add (hv.const_mul 2))
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with x hx
    have he : w x = u x - v x := by rw [hsplit x hx]; abel
    have hn : ‖w x‖ ≤ ‖u x‖ + ‖v x‖ := by rw [he]; exact norm_sub_le _ _
    have hs := pow_le_pow_left₀ (norm_nonneg (w x)) hn 2
    change ‖w x‖ ^ 2 ≤ 2 * ‖u x‖ ^ 2 + 2 * ‖v x‖ ^ 2
    nlinarith [sq_nonneg (‖u x‖ - ‖v x‖)]
  have hW : Decomp97.W N χ ^ 2 =
      (1 / (((q : ℝ) * Decomp97.Q N) ^ 2 * N)) * (∫ x in A, ‖w x‖ ^ 2) := by
    unfold Decomp97.W
    have hn : 0 ≤ (1 / (((q : ℝ) * Decomp97.Q N) ^ 2 * N)) * (∫ x in A, ‖w x‖ ^ 2) := by
      apply mul_nonneg (by positivity)
      exact integral_nonneg (fun x => sq_nonneg _)
    exact Real.sq_sqrt hn
  rw [hW]
  have hb := mul_le_mul_of_nonneg_left hi
    (show 0 ≤ 1 / (((q : ℝ) * Decomp97.Q N) ^ 2 * N) by positivity)
  convert hb using 1
  ring

/-- Page 365, conditional transfer from the matched MovingWindowStep to the sealed W.
The endpoint mean square is retained with its full coefficient. -/
theorem movingWindowStep_with_endpoints (hstep : MovingWindowStep) :
    ∃ C N₀ : ℝ, 0 < C ∧ ∀ N : ℕ, N₀ ≤ N → ∀ q : ℕ+,
      (q : ℝ) ≤ Decomp97.Q N → ∀ χ : DirichletCharacter ℂ (q : ℕ),
      ∀ E : ℝ, 0 ≤ E →
        (∀ θ : ℝ, ((q : ℝ) * Decomp97.Q N) / (20 * N) ≤ θ →
          θ ≤ (20 * (q : ℝ) * Decomp97.Q N) / N →
          (∫ x in Ioc ((N : ℝ) / 2) (3 * N : ℝ),
            ‖movingCharacterSum χ x (θ * x)‖ ^ 2) ≤ E) →
        Decomp97.W N χ ^ 2 ≤ C * E / ((N : ℝ) * ((q : ℝ) * Decomp97.Q N) ^ 2) +
          (2 / ((N : ℝ) * ((q : ℝ) * Decomp97.Q N) ^ 2)) *
            (∫ x in Ioc ((N : ℝ) / 2) (2 * N : ℝ),
              ‖characterEndpointSum N χ x (2 * (q : ℝ) * Decomp97.Q N)‖ ^ 2) := by
  obtain ⟨C, N₀, hC, hbound⟩ := hstep
  refine ⟨2 * C, max N₀ 1, by positivity, ?_⟩
  intro N hN q hq χ E hE hEs
  have hNold : N₀ ≤ (N : ℝ) := (le_max_left _ _).trans hN
  have hNpR : 0 < (N : ℝ) := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 1)
    ((le_max_right N₀ 1).trans hN)
  have hNp : 0 < N := by exact_mod_cast hNpR
  have hu := hbound N hNold q hq χ E hE hEs
  have hb := W_sq_le_unclipped_add_endpoint hNp hq χ
  have htwo := mul_le_mul_of_nonneg_left hu (by norm_num : (0 : ℝ) ≤ 2)
  have he :
      (2 / ((N : ℝ) * ((q : ℝ) * Decomp97.Q N) ^ 2)) *
        (∫ x in Ioc ((N : ℝ) / 2) (2 * N : ℝ),
          ‖movingCharacterSum χ x (2 * (q : ℝ) * Decomp97.Q N)‖ ^ 2) ≤
        (2 * C) * E / ((N : ℝ) * ((q : ℝ) * Decomp97.Q N) ^ 2) := by
    convert htwo using 1 <;> ring
  exact hb.trans (add_le_add he le_rfl)

end
end LeanLab.PerelliPintz1992.Section6
