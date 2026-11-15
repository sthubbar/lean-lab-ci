/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 8, displays 30 and 31 and
the sentence after display 31, Gallagher's lemma with hypothesis A2.3.

This file proves the statement of `Task556d.kernel_mass_of_A23` under the name
`kernel_mass_of_A23_route` from two smaller leaves:

* `gallagher_roughSum`, Gallagher's lemma in the exact form used after display 31,
  which the paper only cites,
* `A23_initial_range`, the initial range of t that hypothesis A2.3 as written
  does not cover when it is inserted into Gallagher's integral.

Display 30, the subdivision argument with its logarithm, and display 31, the
passage from the local minor arc mass to short arcs centred at minor arc
points, are fully proved here.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp556d
import Mathlib.NumberTheory.Harmonic.Bounds

namespace LeanLab.KumchevLiu2007.Eq33RouteB

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a Task556d
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 8, Gallagher's lemma as cited after display 31, in the
exact form used: with T = 1 / (2 H) the integral over the arc of radius T of
the squared rough sum S2 centred at alpha is at most pi^2 T^2 times the
integral over all t of the squared short sums over t < m^2 ≤ t + H. The short
sums vanish unless Y/4 - H ≤ t < Y, and the t range is written as the initial
range from Y/4 - H to Y/4 plus the range from Y/4 to Y of hypothesis A2.3. -/
theorem gallagher_roughSum (Y P H α : ℝ) (hH : 0 < H) :
    (∫ β in (-(1 / (2 * H)))..(1 / (2 * H)), ‖roughSum Y P (α + β)‖ ^ 2) ≤
      (π / (2 * H)) ^ 2 *
        ((∫ t in (Y / 4 - H)..(Y / 4), ‖roughShortSum Y P H α t‖ ^ 2) +
          ∫ t in (Y / 4)..Y, ‖roughShortSum Y P H α t‖ ^ 2) := by
  sorry

/-- LEAF: P0088 page 8, the sentence after display 31, hypothesis A2.3 inserted
into Gallagher's integral on the initial range of t from Y/4 - H to Y/4. The
paper states A2.3 only for t from Y/4 to Y and does not treat this range; here
the short sums are the truncated sums over Y/4 ≤ m^2 ≤ t + H. -/
theorem A23_initial_range (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B) (hε : 0 < ε)
    (hinput : ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
      (∫ t in windowY X ε / 4..windowY X ε,
        ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
          C * H ^ 2 / Real.log X ^ (A + 2)) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
      (∫ t in (windowY X ε / 4 - H)..(windowY X ε / 4),
        ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
          C * H ^ 2 / Real.log X ^ (A + 2) := by
  sorry

/-- Page 4 display 13: the squared rough sum S2 is continuous on the real line. -/
theorem continuous_roughSum_sq (Y P : ℝ) :
    Continuous (fun α : ℝ => ‖roughSum Y P α‖ ^ 2) := by
  unfold roughSum
  refine (continuous_norm.comp ?_).pow 2
  exact continuous_finsetSum _ fun m _ => continuous_const.mul
    ((fourier ((m ^ 2 : ℕ) : ℤ)).continuous.comp (AddCircle.continuous_mk' 1))

/-- Page 7 display 29: circle distance of two real points is at most their real distance. -/
theorem circle_dist_le_abs (x y : ℝ) :
    dist (x : AddCircle (1 : ℝ)) (y : AddCircle (1 : ℝ)) ≤ |x - y| := by
  rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq]
  have h := round_le ((1 : ℝ)⁻¹ * (x - y)) 0
  simpa using h

/-- Page 7 display 29: the short kernel is continuous in alpha. -/
theorem continuous_shortKernel {H : ℝ} (hH : 0 < H) (β : ℝ) :
    Continuous (fun α : ℝ => shortKernel H α β) := by
  unfold shortKernel
  refine Continuous.inv₀ ?_ ?_
  · exact continuous_const.max (((AddCircle.continuous_mk' 1)).dist continuous_const)
  · intro α
    exact (lt_of_lt_of_le (inv_pos.mpr hH) (le_max_left _ _)).ne'

/-- Page 8 display 30, the kernel on one grid cell. -/
theorem shortKernel_le_grid {H : ℝ} (hH : 0 < H) (α β x δ : ℝ) (hx : |x - α| ≤ δ) :
    shortKernel H α β ≤
      (max H⁻¹ (dist (x : AddCircle (1 : ℝ)) (β : AddCircle (1 : ℝ)) - δ))⁻¹ := by
  unfold shortKernel
  have ht := dist_triangle (x : AddCircle (1 : ℝ)) (α : AddCircle (1 : ℝ)) (β : AddCircle (1 : ℝ))
  have hd := circle_dist_le_abs x α
  have hpos : 0 < max H⁻¹ (dist (x : AddCircle (1 : ℝ)) (β : AddCircle (1 : ℝ)) - δ) :=
    lt_of_lt_of_le (inv_pos.mpr hH) (le_max_left _ _)
  rw [inv_le_inv₀ (lt_of_lt_of_le (inv_pos.mpr hH) (le_max_left _ _)) hpos]
  exact max_le_max le_rfl (by linarith)

/-- P0088 page 8 display 30, the subdivision argument in grid form, fully proved.
The unit interval is cut at the points k / N with N the ceiling of H. Each alpha
lies within 1/N ≤ 1/H of a grid point gamma = k / N, where the kernel is at most
the inverse of max of 1/H and the circle distance from gamma to beta minus 1/N.
So the weighted minor mass is at most the sum of these grid weights times the
largest local mass over the sets J gamma. -/
theorem display30_grid (Y P H β M : ℝ) (hH : 2 ≤ H)
    (hloc : ∀ γ ∈ Set.Icc (0 : ℝ) 1,
      (∫ α in (majorArcs H P)ᶜ ∩ Set.Icc (γ - 1 / H) (γ + 1 / H),
        ‖roughSum Y P α‖ ^ 2) ≤ M) :
    kernelMass Y H P β ≤
      (∑ k ∈ Finset.Icc 1 ⌈H⌉₊,
        (max H⁻¹ (dist (((k : ℝ) / (⌈H⌉₊ : ℝ) : ℝ) : AddCircle (1 : ℝ))
          (β : AddCircle (1 : ℝ)) - 1 / (⌈H⌉₊ : ℝ)))⁻¹) * M := by
  have hHpos : 0 < H := by linarith
  have hNH : H ≤ (⌈H⌉₊ : ℝ) := Nat.le_ceil H
  have hNpos : (0 : ℝ) < (⌈H⌉₊ : ℝ) := by linarith
  generalize hN : (⌈H⌉₊ : ℕ) = N at hNH hNpos ⊢
  have hinv : 1 / (N : ℝ) ≤ 1 / H := one_div_le_one_div_of_le hHpos hNH
  have hc := continuous_roughSum_sq Y P
  have hK := continuous_shortKernel hHpos β
  have hmm : MeasurableSet (majorArcs H P)ᶜ := (measurableSet_majorArcs H P).compl
  have hc0 : ∀ k : ℕ, 0 ≤ (max H⁻¹ (dist (((k : ℝ) / (N : ℝ) : ℝ) : AddCircle (1 : ℝ))
      (β : AddCircle (1 : ℝ)) - 1 / (N : ℝ)))⁻¹ := fun k =>
    inv_nonneg.mpr ((inv_pos.mpr hHpos).le.trans (le_max_left _ _))
  have hIk : ∀ k : ℕ, IntegrableOn (fun α : ℝ => ‖roughSum Y P α‖ ^ 2)
      ((majorArcs H P)ᶜ ∩ Set.Icc ((k : ℝ) / N - 1 / H) ((k : ℝ) / N + 1 / H)) := fun k =>
    (hc.continuousOn.integrableOn_Icc (μ := volume)).mono_set Set.inter_subset_right
  have hmk : ∀ k : ℕ, MeasurableSet
      ((majorArcs H P)ᶜ ∩ Set.Icc ((k : ℝ) / N - 1 / H) ((k : ℝ) / N + 1 / H)) := fun k =>
    hmm.inter measurableSet_Icc
  have hint : Integrable (fun α : ℝ => ∑ k ∈ Finset.Icc 1 N,
      (max H⁻¹ (dist (((k : ℝ) / (N : ℝ) : ℝ) : AddCircle (1 : ℝ))
        (β : AddCircle (1 : ℝ)) - 1 / (N : ℝ)))⁻¹ *
      ((majorArcs H P)ᶜ ∩ Set.Icc ((k : ℝ) / N - 1 / H) ((k : ℝ) / N + 1 / H)).indicator
        (fun α : ℝ => ‖roughSum Y P α‖ ^ 2) α) :=
    integrable_finsetSum _ fun k _ => ((hIk k).integrable_indicator (hmk k)).const_mul _
  have hD : MeasurableSet (Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H P)ᶜ) := measurableSet_Ioc.inter hmm
  have hpt : ∀ α ∈ Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H P)ᶜ,
      ‖roughSum Y P α‖ ^ 2 * shortKernel H α β ≤ ∑ k ∈ Finset.Icc 1 N,
      (max H⁻¹ (dist (((k : ℝ) / (N : ℝ) : ℝ) : AddCircle (1 : ℝ))
        (β : AddCircle (1 : ℝ)) - 1 / (N : ℝ)))⁻¹ *
      ((majorArcs H P)ᶜ ∩ Set.Icc ((k : ℝ) / N - 1 / H) ((k : ℝ) / N + 1 / H)).indicator
        (fun α : ℝ => ‖roughSum Y P α‖ ^ 2) α := by
    rintro α ⟨⟨hα0, hα1⟩, hαm⟩
    have hk1 : 1 ≤ ⌈α * N⌉₊ := Nat.one_le_iff_ne_zero.mpr (by
      rw [Ne, Nat.ceil_eq_zero, not_le]; positivity)
    have hkN : ⌈α * N⌉₊ ≤ N := by
      rw [Nat.ceil_le]
      calc α * N ≤ 1 * N := by gcongr
        _ = N := one_mul _
    have hlo : α * N ≤ (⌈α * N⌉₊ : ℝ) := Nat.le_ceil _
    have hhi : (⌈α * N⌉₊ : ℝ) < α * N + 1 := Nat.ceil_lt_add_one (by positivity)
    generalize ⌈α * N⌉₊ = k at hk1 hkN hlo hhi
    have hq1 : α ≤ (k : ℝ) / N := by rw [le_div_iff₀ hNpos]; exact hlo
    have hq2 : (k : ℝ) / N ≤ α + 1 / N := by
      rw [div_le_iff₀ hNpos, add_mul, one_div, inv_mul_cancel₀ hNpos.ne']; exact hhi.le
    have habs : |(k : ℝ) / N - α| ≤ 1 / (N : ℝ) := by
      rw [abs_le]; constructor <;> linarith
    have hker := shortKernel_le_grid hHpos α β ((k : ℝ) / N) (1 / (N : ℝ)) habs
    have hmem : α ∈ (majorArcs H P)ᶜ ∩ Set.Icc ((k : ℝ) / N - 1 / H) ((k : ℝ) / N + 1 / H) :=
      ⟨hαm, by linarith, by linarith⟩
    have hsingle := Finset.single_le_sum (f := fun k : ℕ =>
      (max H⁻¹ (dist (((k : ℝ) / (N : ℝ) : ℝ) : AddCircle (1 : ℝ))
        (β : AddCircle (1 : ℝ)) - 1 / (N : ℝ)))⁻¹ *
      ((majorArcs H P)ᶜ ∩ Set.Icc ((k : ℝ) / N - 1 / H) ((k : ℝ) / N + 1 / H)).indicator
        (fun α : ℝ => ‖roughSum Y P α‖ ^ 2) α)
      (fun j _ => mul_nonneg (hc0 j) (Set.indicator_nonneg (fun _ _ => sq_nonneg _) _))
      (Finset.mem_Icc.mpr ⟨hk1, hkN⟩)
    refine le_trans ?_ hsingle
    simp only [Set.indicator_of_mem hmem]
    rw [mul_comm]
    exact mul_le_mul_of_nonneg_right hker (sq_nonneg _)
  have h1 : kernelMass Y H P β ≤ ∫ α in Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H P)ᶜ,
      ∑ k ∈ Finset.Icc 1 N,
      (max H⁻¹ (dist (((k : ℝ) / (N : ℝ) : ℝ) : AddCircle (1 : ℝ))
        (β : AddCircle (1 : ℝ)) - 1 / (N : ℝ)))⁻¹ *
      ((majorArcs H P)ᶜ ∩ Set.Icc ((k : ℝ) / N - 1 / H) ((k : ℝ) / N + 1 / H)).indicator
        (fun α : ℝ => ‖roughSum Y P α‖ ^ 2) α := by
    unfold kernelMass
    refine setIntegral_mono_on ?_ hint.integrableOn hD hpt
    exact ((hc.mul hK).continuousOn.integrableOn_Icc (μ := volume) (a := 0) (b := 1)).mono_set
      (fun x hx => ⟨hx.1.1.le, hx.1.2⟩)
  have h2 := setIntegral_le_integral (s := Set.Ioc (0 : ℝ) 1 ∩ (majorArcs H P)ᶜ) hint
    (Filter.Eventually.of_forall fun α => Finset.sum_nonneg fun j _ =>
      mul_nonneg (hc0 j) (Set.indicator_nonneg (fun _ _ => sq_nonneg _) _))
  have h3 : (∫ α : ℝ, ∑ k ∈ Finset.Icc 1 N,
      (max H⁻¹ (dist (((k : ℝ) / (N : ℝ) : ℝ) : AddCircle (1 : ℝ))
        (β : AddCircle (1 : ℝ)) - 1 / (N : ℝ)))⁻¹ *
      ((majorArcs H P)ᶜ ∩ Set.Icc ((k : ℝ) / N - 1 / H) ((k : ℝ) / N + 1 / H)).indicator
        (fun α : ℝ => ‖roughSum Y P α‖ ^ 2) α) = ∑ k ∈ Finset.Icc 1 N,
      (max H⁻¹ (dist (((k : ℝ) / (N : ℝ) : ℝ) : AddCircle (1 : ℝ))
        (β : AddCircle (1 : ℝ)) - 1 / (N : ℝ)))⁻¹ *
      ∫ α in (majorArcs H P)ᶜ ∩ Set.Icc ((k : ℝ) / N - 1 / H) ((k : ℝ) / N + 1 / H),
        ‖roughSum Y P α‖ ^ 2 := by
    rw [integral_finsetSum _ fun k _ => ((hIk k).integrable_indicator (hmk k)).const_mul _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [integral_const_mul, integral_indicator (hmk k)]
  rw [Finset.sum_mul]
  refine (h1.trans h2).trans (h3.le.trans ?_)
  refine Finset.sum_le_sum fun k hk => ?_
  have hkk := Finset.mem_Icc.mp hk
  refine mul_le_mul_of_nonneg_left (hloc _ ⟨by positivity, ?_⟩) (hc0 k)
  rw [div_le_one hNpos]
  exact_mod_cast hkk.2

/-- P0088 page 8 display 30, the counting half of the simple subdivision
argument, which gives the factor H L, fully proved. With N the ceiling of H, the
grid weights at the points k / N, namely the inverse of max of 1/H and the circle
distance from k / N to beta minus 1/N, sum to at most 8 H (1 + log H). Each grid
point is sent to the sign and size of the integer part of its scaled signed
circle offset from beta; this map is injective, at most six grid points get
weight H and the others are bounded by two harmonic sums. -/
theorem display30_grid_sum (H β : ℝ) (hH : 2 ≤ H) :
    (∑ k ∈ Finset.Icc 1 ⌈H⌉₊,
      (max H⁻¹ (dist (((k : ℝ) / (⌈H⌉₊ : ℝ) : ℝ) : AddCircle (1 : ℝ))
        (β : AddCircle (1 : ℝ)) - 1 / (⌈H⌉₊ : ℝ)))⁻¹) ≤ 8 * H * (1 + Real.log H) := by
  have hHpos : 0 < H := by linarith
  have hNH : H ≤ (⌈H⌉₊ : ℝ) := Nat.le_ceil H
  have hNlt : (⌈H⌉₊ : ℝ) < H + 1 := Nat.ceil_lt_add_one hHpos.le
  generalize (⌈H⌉₊ : ℕ) = N at hNH hNlt ⊢
  have hNpos : (0 : ℝ) < N := by linarith
  have hN2r : (2 : ℝ) ≤ N := hH.trans hNH
  have hN2 : 2 ≤ N := by exact_mod_cast hN2r
  have hWH : ∀ t : ℝ, (max H⁻¹ t)⁻¹ ≤ H := fun t => by
    have := inv_anti₀ (inv_pos.mpr hHpos) (le_max_left H⁻¹ t)
    simpa using this
  have hW0 : ∀ t : ℝ, 0 ≤ (max H⁻¹ t)⁻¹ := fun t =>
    inv_nonneg.mpr ((inv_pos.mpr hHpos).le.trans (le_max_left _ _))
  let iF : ℕ → ℤ := fun k => ⌊(k : ℝ) - β * N - (round ((k : ℝ) / N - β) : ℤ) * N⌋
  have hpt : ∀ k : ℕ,
      (max H⁻¹ (dist (((k : ℝ) / (N : ℝ) : ℝ) : AddCircle (1 : ℝ))
        (β : AddCircle (1 : ℝ)) - 1 / (N : ℝ)))⁻¹ ≤
        (max H⁻¹ ((((iF k).natAbs : ℝ) - 2) / N))⁻¹ ∧ (iF k).natAbs ≤ N := by
    intro k
    have hd : dist (((k : ℝ) / (N : ℝ) : ℝ) : AddCircle (1 : ℝ)) (β : AddCircle (1 : ℝ)) =
        |((k : ℝ) / N - β) - round ((k : ℝ) / N - β)| := by
      rw [dist_eq_norm, ← AddCircle.coe_sub, AddCircle.norm_eq]
      simp
    have hround := abs_sub_round ((k : ℝ) / N - β)
    have hux : (k : ℝ) - β * N - (round ((k : ℝ) / N - β) : ℤ) * N =
        N * (((k : ℝ) / N - β) - round ((k : ℝ) / N - β)) := by
      field_simp
    have hfl := Int.floor_le ((k : ℝ) - β * N - (round ((k : ℝ) / N - β) : ℤ) * N)
    have hlt := Int.lt_floor_add_one ((k : ℝ) - β * N - (round ((k : ℝ) / N - β) : ℤ) * N)
    have hi : ((iF k).natAbs : ℝ) = |((iF k : ℤ) : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    have habs : |(k : ℝ) - β * N - (round ((k : ℝ) / N - β) : ℤ) * N| =
        N * |((k : ℝ) / N - β) - round ((k : ℝ) / N - β)| := by
      rw [hux, abs_mul, abs_of_pos hNpos]
    have hiu : |((iF k : ℤ) : ℝ)| ≤
        |(k : ℝ) - β * N - (round ((k : ℝ) / N - β) : ℤ) * N| + 1 := by
      have h1 := neg_abs_le ((k : ℝ) - β * N - (round ((k : ℝ) / N - β) : ℤ) * N)
      have h2 := le_abs_self ((k : ℝ) - β * N - (round ((k : ℝ) / N - β) : ℤ) * N)
      rw [abs_le]
      constructor
      · show _ ≤ ((⌊(k : ℝ) - β * N - (round ((k : ℝ) / N - β) : ℤ) * N⌋ : ℤ) : ℝ)
        linarith
      · show ((⌊(k : ℝ) - β * N - (round ((k : ℝ) / N - β) : ℤ) * N⌋ : ℤ) : ℝ) ≤ _
        linarith
    constructor
    · have hpos : 0 < max H⁻¹ ((((iF k).natAbs : ℝ) - 2) / N) :=
        lt_of_lt_of_le (inv_pos.mpr hHpos) (le_max_left _ _)
      apply inv_anti₀ hpos
      apply max_le_max le_rfl
      rw [hd, div_le_iff₀ hNpos, sub_mul, one_div, inv_mul_cancel₀ hNpos.ne', hi]
      linarith [mul_comm (N : ℝ) |((k : ℝ) / N - β) - round ((k : ℝ) / N - β)|]
    · have hr : ((iF k).natAbs : ℝ) ≤ N := by
        rw [hi]
        have := mul_le_mul_of_nonneg_left hround hNpos.le
        linarith
      exact_mod_cast hr
  have hfloor : ∀ k : ℕ, iF k =
      (k : ℤ) - round ((k : ℝ) / N - β) * N + ⌊-(β * N)⌋ := by
    intro k
    show ⌊(k : ℝ) - β * N - (round ((k : ℝ) / N - β) : ℤ) * N⌋ = _
    rw [show (k : ℝ) - β * N - (round ((k : ℝ) / N - β) : ℤ) * N =
      (((k : ℤ) - round ((k : ℝ) / N - β) * N : ℤ) : ℝ) + -(β * N) by push_cast; ring,
      Int.floor_intCast_add]
  have hinj : ∀ a ∈ Finset.Icc 1 N, ∀ b ∈ Finset.Icc 1 N,
      (decide (0 ≤ iF a), (iF a).natAbs) = (decide (0 ≤ iF b), (iF b).natAbs) → a = b := by
    intro a ha b hb h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    simp only [decide_eq_decide] at h1 h2
    have hi : iF a = iF b := by
      rcases Int.natAbs_eq_natAbs_iff.mp h2 with h3 | h3
      · exact h3
      · by_cases hb0 : 0 ≤ iF b
        · have := h1.mpr hb0
          omega
        · have : ¬ 0 ≤ iF a := fun h => hb0 (h1.mp h)
          omega
    rw [hfloor a, hfloor b] at hi
    have hdvd : (N : ℤ) ∣ (a : ℤ) - b :=
      ⟨round ((a : ℝ) / N - β) - round ((b : ℝ) / N - β), by linear_combination hi⟩
    have ha' := Finset.mem_Icc.mp ha
    have hb' := Finset.mem_Icc.mp hb
    have habs : |(a : ℤ) - b| < N := by
      rw [abs_lt]
      constructor <;> omega
    have := Int.eq_zero_of_abs_lt_dvd hdvd habs
    omega
  have hsum : (∑ n ∈ Finset.range (N + 1), (max H⁻¹ (((n : ℝ) - 2) / N))⁻¹) ≤
      3 * H + N * (1 + Real.log N) := by
    rw [show N + 1 = 3 + (N - 2) by omega, Finset.sum_range_add]
    have hA : (∑ n ∈ Finset.range 3, (max H⁻¹ (((n : ℝ) - 2) / N))⁻¹) ≤ 3 * H := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero]
      have a0 := hWH ((((0 : ℕ) : ℝ) - 2) / N)
      have a1 := hWH ((((1 : ℕ) : ℝ) - 2) / N)
      have a2 := hWH ((((2 : ℕ) : ℝ) - 2) / N)
      linarith
    have hB : (∑ l ∈ Finset.range (N - 2), (max H⁻¹ ((((3 + l : ℕ) : ℝ) - 2) / N))⁻¹) ≤
        N * ∑ l ∈ Finset.range N, ((l : ℝ) + 1)⁻¹ := by
      rw [Finset.mul_sum]
      calc _ ≤ ∑ l ∈ Finset.range (N - 2), (N : ℝ) * ((l : ℝ) + 1)⁻¹ :=
            Finset.sum_le_sum fun l _ => ?_
        _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.range_mono (Nat.sub_le _ _)) (fun l _ _ => by positivity)
      have e : (((3 + l : ℕ) : ℝ) - 2) / N = ((l : ℝ) + 1) / N := by push_cast; ring
      rw [e]
      have hp : 0 < ((l : ℝ) + 1) / N := by positivity
      calc _ ≤ (((l : ℝ) + 1) / N)⁻¹ := inv_anti₀ hp (le_max_right _ _)
        _ = _ := by rw [inv_div, div_eq_mul_inv]
    have hC : (∑ l ∈ Finset.range N, ((l : ℝ) + 1)⁻¹) ≤ 1 + Real.log N := by
      have h := harmonic_le_one_add_log N
      have e : ((harmonic N : ℚ) : ℝ) = ∑ l ∈ Finset.range N, ((l : ℝ) + 1)⁻¹ := by
        simp [harmonic]
      rw [e] at h
      exact h
    have hD := mul_le_mul_of_nonneg_left hC hNpos.le
    linarith
  have hlogN : Real.log N ≤ 1 / 2 + Real.log H := by
    have h32 : (N : ℝ) ≤ 3 / 2 * H := by linarith
    calc Real.log N ≤ Real.log (3 / 2 * H) := Real.log_le_log hNpos h32
      _ = Real.log (3 / 2) + Real.log H := Real.log_mul (by norm_num) hHpos.ne'
      _ ≤ 1 / 2 + Real.log H := by
        have : Real.log (3 / 2 : ℝ) ≤ 1 / 2 := by
          rw [Real.log_le_iff_le_exp (by norm_num)]
          have := Real.add_one_le_exp (1 / 2 : ℝ)
          linarith
        linarith
  have hlogH : 1 / 2 ≤ Real.log H := by
    have h1 := Real.log_le_log (by norm_num : (0 : ℝ) < 2) hH
    have h2 := Real.log_two_gt_d9
    linarith
  have hlogN0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hprod : (N : ℝ) * (1 + Real.log N) ≤ 3 / 2 * H * (3 / 2 + Real.log H) :=
    mul_le_mul (by linarith) (by linarith) (by linarith) (by positivity)
  have hHL : H * (1 / 2) ≤ H * Real.log H := mul_le_mul_of_nonneg_left hlogH hHpos.le
  calc (∑ k ∈ Finset.Icc 1 N,
        (max H⁻¹ (dist (((k : ℝ) / (N : ℝ) : ℝ) : AddCircle (1 : ℝ))
          (β : AddCircle (1 : ℝ)) - 1 / (N : ℝ)))⁻¹)
      ≤ ∑ k ∈ Finset.Icc 1 N, (max H⁻¹ ((((iF k).natAbs : ℝ) - 2) / N))⁻¹ :=
        Finset.sum_le_sum fun k _ => (hpt k).1
    _ = ∑ p ∈ (Finset.Icc 1 N).image (fun k : ℕ => (decide (0 ≤ iF k), (iF k).natAbs)),
          (max H⁻¹ (((p.2 : ℝ) - 2) / N))⁻¹ :=
        (Finset.sum_image (f := fun p : Bool × ℕ => (max H⁻¹ (((p.2 : ℝ) - 2) / N))⁻¹)
          (fun a ha b hb h => hinj a (by simpa using ha) b (by simpa using hb) h)).symm
    _ ≤ ∑ p ∈ (Finset.univ : Finset Bool) ×ˢ Finset.range (N + 1),
          (max H⁻¹ (((p.2 : ℝ) - 2) / N))⁻¹ := by
        refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun p _ _ => hW0 _)
        intro p hp
        obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hp
        simp only [Finset.mem_product, Finset.mem_univ, Finset.mem_range, true_and]
        exact Nat.lt_succ_of_le (hpt k).2
    _ = 2 * ∑ n ∈ Finset.range (N + 1), (max H⁻¹ (((n : ℝ) - 2) / N))⁻¹ := by
        rw [Finset.sum_product]
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_bool, nsmul_eq_mul]
        norm_num
    _ ≤ 2 * (3 * H + N * (1 + Real.log N)) := by linarith
    _ ≤ 8 * H * (1 + Real.log H) := by nlinarith

/-- P0088 page 8 display 30, the simple subdivision argument: the weighted
minor mass is at most a constant times H (1 + log H) times the largest local
mass over the sets J gamma. Proved from the grid form and the grid sum. -/
theorem display30_subdivision (Y P H β M : ℝ) (hH : 2 ≤ H)
    (_hβ : β ∈ Set.Icc (0 : ℝ) 1)
    (hloc : ∀ γ ∈ Set.Icc (0 : ℝ) 1,
      (∫ α in (majorArcs H P)ᶜ ∩ Set.Icc (γ - 1 / H) (γ + 1 / H),
        ‖roughSum Y P α‖ ^ 2) ≤ M) :
    kernelMass Y H P β ≤ 8 * H * (1 + Real.log H) * M := by
  have hM : 0 ≤ M :=
    (setIntegral_nonneg ((measurableSet_majorArcs H P).compl.inter measurableSet_Icc)
      (fun x _ => sq_nonneg _)).trans (hloc 0 ⟨le_rfl, zero_le_one⟩)
  exact (display30_grid Y P H β M hH hloc).trans
    (mul_le_mul_of_nonneg_right (display30_grid_sum H β hH) hM)

/-- Page 8 display 31, measure bookkeeping: for a nonnegative continuous
integrand the integral over a union of two bounded sets is at most the sum. -/
theorem setIntegral_union_le_of_nonneg {f : ℝ → ℝ} (hf : Continuous f)
    (h0 : ∀ x, 0 ≤ f x) {S T : Set ℝ} {a b : ℝ} (hS : MeasurableSet S)
    (hT : MeasurableSet T) (hSs : S ⊆ Set.Icc a b) (hTs : T ⊆ Set.Icc a b) :
    (∫ x in S ∪ T, f x) ≤ (∫ x in S, f x) + ∫ x in T, f x := by
  have hI : IntegrableOn f (Set.Icc a b) := hf.continuousOn.integrableOn_Icc
  have hIS : IntegrableOn f S := hI.mono_set hSs
  have hIT : IntegrableOn f T := hI.mono_set hTs
  have hu : S ∪ T = S ∪ (T \ S) := Set.union_sdiff_self.symm
  rw [hu, setIntegral_union Set.disjoint_sdiff_right (hT.diff hS) hIS
    (hIT.mono_set Set.sdiff_subset)]
  have hm : (∫ x in T \ S, f x) ≤ ∫ x in T, f x :=
    setIntegral_mono_set hIT (Filter.Eventually.of_forall h0)
      (Set.sdiff_subset.eventuallyLE)
  linarith

/-- Page 8 display 31, one piece: a part of the minor arcs inside an interval of
length r lies in the arc of radius r about any of its points, which is a minor
arc point alpha, and translation turns the integral into the one over beta. -/
theorem display31_piece (Y P H r a M : ℝ) (hr : 0 < r) (hM : 0 ≤ M)
    (hG : ∀ α : ℝ, α ∉ majorArcs H P →
      (∫ β in (-r)..r, ‖roughSum Y P (α + β)‖ ^ 2) ≤ M) :
    (∫ α in (majorArcs H P)ᶜ ∩ Set.Icc a (a + r), ‖roughSum Y P α‖ ^ 2) ≤ M := by
  by_cases hne : ((majorArcs H P)ᶜ ∩ Set.Icc a (a + r)).Nonempty
  · obtain ⟨α0, hα0m, hα0l, hα0u⟩ := hne
    have hc := continuous_roughSum_sq Y P
    have hsub : (majorArcs H P)ᶜ ∩ Set.Icc a (a + r) ⊆ Set.Icc (α0 - r) (α0 + r) := by
      rintro x ⟨_, hxl, hxu⟩
      exact ⟨by linarith, by linarith⟩
    have h1 : (∫ α in (majorArcs H P)ᶜ ∩ Set.Icc a (a + r), ‖roughSum Y P α‖ ^ 2) ≤
        ∫ α in Set.Icc (α0 - r) (α0 + r), ‖roughSum Y P α‖ ^ 2 :=
      setIntegral_mono_set hc.continuousOn.integrableOn_Icc
        (Filter.Eventually.of_forall fun x => sq_nonneg _) hsub.eventuallyLE
    have h2 : (∫ α in Set.Icc (α0 - r) (α0 + r), ‖roughSum Y P α‖ ^ 2) =
        ∫ β in (-r)..r, ‖roughSum Y P (α0 + β)‖ ^ 2 := by
      rw [integral_Icc_eq_integral_Ioc,
        ← intervalIntegral.integral_of_le (by linarith : α0 - r ≤ α0 + r),
        intervalIntegral.integral_comp_add_left (fun x => ‖roughSum Y P x‖ ^ 2) α0]
      rw [show α0 + -r = α0 - r by ring]
    rw [h2] at h1
    exact h1.trans (hG α0 hα0m)
  · rw [Set.not_nonempty_iff_eq_empty.mp hne]
    simpa using hM

/-- Page 8 display 31: the local mass of S2 squared over J gamma, the minor
arcs inside the interval of radius 1/H about gamma, is at most four times the
largest integral of S2 squared over an arc of radius 1/(2H) centred at a minor
arc point alpha. The paper writes radius 1/H; the radius 1/(2H) is the one that
matches Gallagher's lemma with short sums of length H, and it only costs the
constant four in place of two. -/
theorem display31_shift (Y P H γ M : ℝ) (hH : 0 < H) (hM : 0 ≤ M)
    (hG : ∀ α : ℝ, α ∉ majorArcs H P →
      (∫ β in (-(1 / (2 * H)))..(1 / (2 * H)), ‖roughSum Y P (α + β)‖ ^ 2) ≤ M) :
    (∫ α in (majorArcs H P)ᶜ ∩ Set.Icc (γ - 1 / H) (γ + 1 / H),
      ‖roughSum Y P α‖ ^ 2) ≤ 4 * M := by
  have hr : 0 < 1 / (2 * H) := by positivity
  have hrr : 1 / H = 2 * (1 / (2 * H)) := by field_simp
  rw [hrr]
  generalize 1 / (2 * H) = r at hr hG ⊢
  have hc := continuous_roughSum_sq Y P
  have h0 : ∀ x : ℝ, 0 ≤ ‖roughSum Y P x‖ ^ 2 := fun x => sq_nonneg _
  have hmeas : ∀ a : ℝ, MeasurableSet ((majorArcs H P)ᶜ ∩ Set.Icc a (a + r)) :=
    fun a => (measurableSet_majorArcs H P).compl.inter measurableSet_Icc
  have hp := fun a => display31_piece Y P H r a M hr hM hG
  have hbd : ∀ a : ℝ, γ - 2 * r ≤ a → a + r ≤ γ + 2 * r →
      (majorArcs H P)ᶜ ∩ Set.Icc a (a + r) ⊆ Set.Icc (γ - 2 * r) (γ + 2 * r) := by
    rintro a hl hu x ⟨_, hxl, hxu⟩
    exact ⟨by linarith, by linarith⟩
  have hb0 := hbd (γ - 2 * r) (by linarith) (by linarith)
  have hb1 := hbd (γ - r) (by linarith) (by linarith)
  have hb2 := hbd γ (by linarith) (by linarith)
  have hb3 := hbd (γ + r) (by linarith) (by linarith)
  have hcover : (majorArcs H P)ᶜ ∩ Set.Icc (γ - 2 * r) (γ + 2 * r) ⊆
      (((majorArcs H P)ᶜ ∩ Set.Icc (γ - 2 * r) (γ - 2 * r + r)) ∪
        ((majorArcs H P)ᶜ ∩ Set.Icc (γ - r) (γ - r + r))) ∪
      (((majorArcs H P)ᶜ ∩ Set.Icc γ (γ + r)) ∪
        ((majorArcs H P)ᶜ ∩ Set.Icc (γ + r) (γ + r + r))) := by
    rintro x ⟨hxm, hxl, hxu⟩
    rcases le_total x (γ - r) with h1 | h1
    · exact Or.inl (Or.inl ⟨hxm, hxl, by linarith⟩)
    · rcases le_total x γ with h2 | h2
      · exact Or.inl (Or.inr ⟨hxm, h1, by linarith⟩)
      · rcases le_total x (γ + r) with h3 | h3
        · exact Or.inr (Or.inl ⟨hxm, h2, h3⟩)
        · exact Or.inr (Or.inr ⟨hxm, h3, by linarith⟩)
  have hA := setIntegral_union_le_of_nonneg hc h0 (hmeas (γ - 2 * r)) (hmeas (γ - r)) hb0 hb1
  have hB := setIntegral_union_le_of_nonneg hc h0 (hmeas γ) (hmeas (γ + r)) hb2 hb3
  have hAB := setIntegral_union_le_of_nonneg hc h0
    ((hmeas (γ - 2 * r)).union (hmeas (γ - r))) ((hmeas γ).union (hmeas (γ + r)))
    (Set.union_subset hb0 hb1) (Set.union_subset hb2 hb3)
  have hmono := setIntegral_mono_set
    ((hc.continuousOn.integrableOn_Icc (μ := volume) (a := γ - 2 * r) (b := γ + 2 * r)).mono_set
      (Set.union_subset (Set.union_subset hb0 hb1) (Set.union_subset hb2 hb3)))
    (Filter.Eventually.of_forall h0) hcover.eventuallyLE
  have q0 := hp (γ - 2 * r)
  have q1 := hp (γ - r)
  have q2 := hp γ
  have q3 := hp (γ + r)
  refine hmono.trans (hAB.trans ?_)
  linarith

/-- P0088 page 8 displays 30 and 31 with Gallagher's lemma and hypothesis A2.3:
the statement of `Task556d.kernel_mass_of_A23`, proved from the proved displays
30 and 31, the Gallagher leaf and the initial range leaf.
CONDITIONAL ON those two leaves. -/
theorem kernel_mass_of_A23_route (A B ε : ℝ) (hA : 0 < A) (hB : 0 < B) (hε : 0 < ε)
    (hinput : ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
      (∫ t in windowY X ε / 4..windowY X ε,
        ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
          C * H ^ 2 / Real.log X ^ (A + 2)) :
    ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
      X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
      ∀ β ∈ Set.Icc (0 : ℝ) 1,
        kernelMass (windowY X ε) H (Real.log X ^ B) β ≤ C * H / Real.log X ^ A := by
  obtain ⟨C1, X1, hC1, hX1, h1⟩ := A23_initial_range A B ε hA hB hε hinput
  obtain ⟨C0, X0, hC0, hX0, h0⟩ := hinput
  refine ⟨16 * π ^ 2 * (C0 + C1), max (max X0 X1) 8, by positivity,
    hX0.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro X H hX hH hHX β hβ
  have hX8 : 8 ≤ X := (le_max_right _ _).trans hX
  have hXa : X0 ≤ X := ((le_max_left _ _).trans (le_max_left _ _)).trans hX
  have hXb : X1 ≤ X := ((le_max_right _ _).trans (le_max_left _ _)).trans hX
  have hXpos : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hXpos]
    exact (Real.exp_one_lt_d9.le.trans (by norm_num)).trans hX8
  have hLpos : 0 < Real.log X := by linarith
  have h8 : (8 : ℝ) ^ (1 / 3 : ℝ) = 2 := by
    rw [show (8 : ℝ) = 2 ^ (3 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    norm_num
  have hH2 : 2 ≤ H := by
    calc (2 : ℝ) = (8 : ℝ) ^ (1 / 3 : ℝ) := h8.symm
      _ ≤ (8 : ℝ) ^ (7 / 18 + ε) :=
        Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
      _ ≤ X ^ (7 / 18 + ε) := Real.rpow_le_rpow (by norm_num) hX8 (by linarith)
      _ ≤ H := hH
  have hHpos : 0 < H := by linarith
  have hHX' : H ≤ X := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ X)
      (by linarith : 1 - ε ≤ (1 : ℝ))
    rw [Real.rpow_one] at this
    exact hHX.trans this
  have hlogH : Real.log H ≤ Real.log X := Real.log_le_log hHpos hHX'
  have hLp : 0 < Real.log X ^ (A + 2) := Real.rpow_pos_of_pos hLpos _
  have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hLpos _
  have hG : ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
      (∫ β in (-(1 / (2 * H)))..(1 / (2 * H)),
        ‖roughSum (windowY X ε) (Real.log X ^ B) (α + β)‖ ^ 2) ≤
        π ^ 2 / 4 * (C0 + C1) / Real.log X ^ (A + 2) := by
    intro α hα
    have e := h1 X H hXb hH hHX α hα
    have m := h0 X H hXa hH hHX α hα
    have g := gallagher_roughSum (windowY X ε) (Real.log X ^ B) H α hHpos
    calc _ ≤ _ := g
      _ ≤ (π / (2 * H)) ^ 2 * (C1 * H ^ 2 / Real.log X ^ (A + 2) +
            C0 * H ^ 2 / Real.log X ^ (A + 2)) := by gcongr
      _ = _ := by field_simp; ring
  have hM0 : 0 ≤ π ^ 2 / 4 * (C0 + C1) / Real.log X ^ (A + 2) := by positivity
  have hloc : ∀ γ ∈ Set.Icc (0 : ℝ) 1,
      (∫ α in (majorArcs H (Real.log X ^ B))ᶜ ∩ Set.Icc (γ - 1 / H) (γ + 1 / H),
        ‖roughSum (windowY X ε) (Real.log X ^ B) α‖ ^ 2) ≤
        4 * (π ^ 2 / 4 * (C0 + C1) / Real.log X ^ (A + 2)) :=
    fun γ _ => display31_shift _ _ H γ _ hHpos hM0 hG
  have hk := display30_subdivision (windowY X ε) (Real.log X ^ B) H β _ hH2 hβ hloc
  have hpow : Real.log X ^ (A + 2) = Real.log X ^ A * Real.log X ^ 2 := by
    rw [Real.rpow_add hLpos, Real.rpow_two]
  have hstep : 8 * H * (1 + Real.log H) *
      (4 * (π ^ 2 / 4 * (C0 + C1) / Real.log X ^ (A + 2))) ≤
      8 * H * (2 * Real.log X) *
      (4 * (π ^ 2 / 4 * (C0 + C1) / Real.log X ^ (A + 2))) := by
    gcongr
    linarith
  have heq : 8 * H * (2 * Real.log X) *
      (4 * (π ^ 2 / 4 * (C0 + C1) / Real.log X ^ (A + 2))) =
      16 * π ^ 2 * (C0 + C1) * H / Real.log X ^ A * (1 / Real.log X) := by
    rw [hpow]
    field_simp
    ring
  have hfin : 16 * π ^ 2 * (C0 + C1) * H / Real.log X ^ A * (1 / Real.log X) ≤
      16 * π ^ 2 * (C0 + C1) * H / Real.log X ^ A :=
    mul_le_of_le_one_right (by positivity) (by rw [div_le_one hLpos]; exact hL1)
  linarith

end LeanLab.KumchevLiu2007.Eq33RouteB
