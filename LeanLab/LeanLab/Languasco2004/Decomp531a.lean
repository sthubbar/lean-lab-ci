/-
Finite Fourier kernel support for PP1993 page 44 display 3.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
The six existing helpers move here with identical statements and names.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.CoefficientGlue489

namespace LeanLab.Languasco2004.Decomp489g
open Finset Real MeasureTheory Decomp279b Decomp413a
noncomputable section

/-- Page 44 display 3: the number of even frequencies in the open left
window is at most H once H is at least two. -/
theorem even_window_card {N H : ℝ} (hN : 0 ≤ N) (hH : 2 ≤ H) :
    (((Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even).card : ℝ) ≤ H := by
  classical
  let s := (Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even
  let t := Ioc ⌊N / 2⌋₊ ⌊(N + H) / 2⌋₊
  have hmaps : Set.MapsTo (fun n : ℕ => n / 2) s t := by
    intro n hn
    obtain ⟨hnI, heven⟩ := Finset.mem_filter.mp hn
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hnI
    obtain ⟨k, hk⟩ := heven
    have hn2 : 2 ≤ n := by omega
    have hnpos : 0 < n := by omega
    have hreal : N < (n : ℝ) := (Nat.floor_lt' hnpos.ne').mp hlo
    have hupper : (n : ℝ) ≤ N + H :=
      (show (n : ℝ) ≤ (⌊N + H⌋₊ : ℝ) by exact_mod_cast hhi).trans (Nat.floor_le (by linarith))
    have heq : (n : ℝ) = 2 * ((n / 2 : ℕ) : ℝ) := by
      exact_mod_cast (show n = 2 * (n / 2) by omega)
    apply Finset.mem_Ioc.mpr
    constructor
    · exact (Nat.floor_lt' (by omega : n / 2 ≠ 0)).mpr (by linarith)
    · exact (Nat.le_floor_iff (by linarith : 0 ≤ (N + H) / 2)).mpr (by linarith)
  have hinj : (s : Set ℕ).InjOn (fun n : ℕ => n / 2) := by
    intro n hn m hm heq
    change n / 2 = m / 2 at heq
    obtain ⟨k, hk⟩ := (Finset.mem_filter.mp hn).2
    obtain ⟨j, hj⟩ := (Finset.mem_filter.mp hm).2
    omega
  have hc := Finset.card_le_card_of_injOn (fun n : ℕ => n / 2) hmaps hinj
  have hmono : ⌊N / 2⌋₊ ≤ ⌊(N + H) / 2⌋₊ := Nat.floor_mono (by linarith)
  have ht : (t.card : ℝ) ≤ H := by
    dsimp [t]
    rw [Nat.card_Ioc, Nat.cast_sub hmono]
    have hu := Nat.floor_le (show 0 ≤ (N + H) / 2 by linarith)
    have hl := Nat.lt_floor_add_one (N / 2)
    linarith
  exact (show (s.card : ℝ) ≤ (t.card : ℝ) by exact_mod_cast hc).trans ht

/-- Page 43: each phase has norm one. -/
theorem phase_norm (x : ℝ) : ‖phase x‖ = 1 := by
  unfold phase
  rw [show (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I by
    push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

/-- Page 44 display 3: the finite even frequency sum satisfies the H cap,
including every integer pole. The reciprocal distance bound is separate. -/
theorem even_phase_cap {N H : ℝ} (hN : 0 ≤ N) (hH : 2 ≤ H) (x : ℝ) :
    ‖∑ m ∈ (Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even, phase ((m : ℝ) * x)‖ ≤ H := by
  calc ‖∑ m ∈ (Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even, phase ((m : ℝ) * x)‖ ≤
      ∑ m ∈ (Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even, ‖phase ((m : ℝ) * x)‖ := norm_sum_le _ _
    _ = (((Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even).card : ℝ) := by simp only [phase_norm, Finset.sum_const, nsmul_eq_mul, mul_one]
    _ ≤ H := even_window_card hN hH

#print axioms even_window_card
#print axioms phase_norm
#print axioms even_phase_cap

/-- Page 44 display 3: a finite unit circle geometric sum is bounded
by two divided by the chord to one. -/
theorem unit_geometric_sum_bound {z : ℂ} (hz : ‖z‖ = 1) (hne : z ≠ 1) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, z ^ k‖ ≤ 2 / ‖z - 1‖ := by
  rw [geom_sum_eq hne, norm_div]
  apply div_le_div_of_nonneg_right _ (norm_nonneg _)
  calc ‖z ^ n - 1‖ ≤ ‖z ^ n‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
    _ = 2 := by norm_num [hz]

/-- Page 44 display 3: Jordan's inequality controls the phase chord
on a nearest integer cell. -/
theorem phase_gap_lower {t : ℝ} (ht : |t| ≤ 1 / 2) :
    4 * |t| ≤ ‖phase t - 1‖ := by
  have hs := Real.mul_abs_le_abs_sin (x := Real.pi * t) (by
    rw [abs_mul, abs_of_pos Real.pi_pos]
    nlinarith [Real.pi_pos])
  have hcancel : (2 / Real.pi) * (Real.pi * |t|) = 2 * |t| := by
    field_simp
  rw [abs_mul, abs_of_pos Real.pi_pos, hcancel] at hs
  have heq : phase t = Complex.exp (Complex.I * ((2 * Real.pi * t : ℝ) : ℂ)) := by
    unfold phase
    congr 1
    push_cast
    ring
  rw [heq, Complex.norm_exp_I_mul_ofReal_sub_one]
  rw [show (2 * Real.pi * t) / 2 = Real.pi * t by ring]
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  linarith

/-- Page 44 display 3: the reciprocal distance bound for a finite
geometric progression on a punctured nearest integer cell. -/
theorem local_geometric_inverse_bound {t : ℝ} (ht : |t| ≤ 1 / 2) (ht0 : t ≠ 0) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, phase t ^ k‖ ≤ |t|⁻¹ := by
  have ha : 0 < |t| := abs_pos.mpr ht0
  have hgap := phase_gap_lower ht
  have hden : 0 < ‖phase t - 1‖ := by linarith
  have hne : phase t ≠ 1 := by
    intro h
    rw [h, sub_self, norm_zero] at hden
    exact (lt_irrefl 0) hden
  have hgeom := unit_geometric_sum_bound (phase_norm t) hne n
  have hfrac := div_le_div_of_nonneg_left (by norm_num : (0 : ℝ) ≤ 2)
    (show 0 < 4 * |t| by positivity) hgap
  have hlast : (2 : ℝ) / (4 * |t|) ≤ |t|⁻¹ := by
    rw [inv_eq_one_div]
    apply (div_le_div_iff₀ (by positivity : 0 < 4 * |t|) ha).mpr
    linarith
  exact hgeom.trans (hfrac.trans hlast)

#print axioms unit_geometric_sum_bound
#print axioms phase_gap_lower
#print axioms local_geometric_inverse_bound

end
end LeanLab.Languasco2004.Decomp489g

namespace LeanLab.Languasco2004.Decomp531a
open Finset Real MeasureTheory Decomp279b Decomp413a Decomp489g
noncomputable section

/-- Page 44 display 3 support: translating a phase by an integer changes nothing. -/
theorem phase_integer_translate (x : ℝ) (k : ℤ) : phase (x + k) = phase x := by
  unfold phase
  rw [show 2 * (Real.pi : ℂ) * Complex.I * ((x + k : ℝ) : ℂ) =
    2 * Real.pi * Complex.I * (x : ℂ) + (k : ℂ) * (2 * Real.pi * Complex.I) by
      push_cast; ring]
  rw [Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- Page 44 display 3 support: the denominator controls nearest integer distance. -/
theorem phase_nearest_gap (x : ℝ) :
    4 * |x - (round x : ℤ)| ≤ ‖phase x - 1‖ := by
  have h := phase_gap_lower (abs_sub_round x)
  rw [show phase (x - (round x : ℤ)) = phase x by
    simpa only [Int.cast_neg, sub_eq_add_neg] using phase_integer_translate x (-(round x))] at h
  exact h

/-- Page 44 display 3 support: the reciprocal distance bound holds on every cell. -/
theorem geometric_nearest_inverse {x : ℝ} (hx : x ≠ (round x : ℤ)) (n : ℕ) :
    ‖∑ k ∈ Finset.range n, phase x ^ k‖ ≤ |x - (round x : ℤ)|⁻¹ := by
  have h := local_geometric_inverse_bound (abs_sub_round x) (sub_ne_zero.mpr hx) n
  rw [show phase (x - (round x : ℤ)) = phase x by
    simpa only [Int.cast_neg, sub_eq_add_neg] using phase_integer_translate x (-(round x))] at h
  exact h

/-- Page 44 display 3 support: natural multiples of a phase are its powers. -/
theorem phase_nat_mul (n : ℕ) (x : ℝ) : phase ((n : ℝ) * x) = phase x ^ n := by
  unfold phase
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- Page 44 display 3 support: addition multiplies phases. -/
theorem phase_add (x y : ℝ) : phase (x + y) = phase x * phase y := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- Page 44 display 3 support: halving reindexes the even natural window exactly. -/
theorem even_window_reindex (a b : ℕ) (f : ℕ → ℂ) :
    (∑ m ∈ (Ioc a b).filter Even, f m) = ∑ k ∈ Ioc (a / 2) (b / 2), f (2 * k) := by
  classical
  symm
  apply Finset.sum_bij (fun k _ => 2 * k)
  · intro k hk
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hk
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Ioc.mpr (by omega), ⟨k, by omega⟩⟩
  · intro k hk j hj heq
    omega
  · intro m hm
    obtain ⟨hmI, k, hk⟩ := Finset.mem_filter.mp hm
    obtain ⟨hlo, hhi⟩ := Finset.mem_Ioc.mp hmI
    refine ⟨k, Finset.mem_Ioc.mpr (by omega), by omega⟩
  · intro k hk
    rfl

/-- Page 44 display 3 support: an offset phase interval is one geometric progression. -/
theorem phase_interval_geometric (a b : ℕ) (x : ℝ) :
    (∑ k ∈ Ico a b, phase ((k : ℝ) * x)) =
      phase ((a : ℝ) * x) * ∑ k ∈ range (b - a), phase x ^ k := by
  rw [Finset.sum_Ico_eq_sum_range]
  simp_rw [Nat.cast_add, add_mul, phase_add, phase_nat_mul]
  rw [Finset.mul_sum]

/-- Page 44 display 3 support: the even window satisfies the reciprocal distance bound. -/
theorem even_window_inverse (a b : ℕ) {x : ℝ}
    (hx : 2 * x ≠ (round (2 * x) : ℤ)) :
    ‖∑ m ∈ (Ioc a b).filter Even, phase ((m : ℝ) * x)‖ ≤
      |2 * x - (round (2 * x) : ℤ)|⁻¹ := by
  rw [even_window_reindex]
  simp_rw [Nat.cast_mul, Nat.cast_ofNat, mul_assoc,
    show ∀ k : ℕ, 2 * ((k : ℝ) * x) = (k : ℝ) * (2 * x) by intro k; ring]
  rw [← Ico_add_one_add_one_eq_Ioc, phase_interval_geometric, norm_mul, phase_norm, one_mul]
  exact geometric_nearest_inverse hx _

/-- Page 44 display 3 support: the cardinality cap also covers negative real N. -/
theorem even_window_card_any {N H : ℝ} (hH : 2 ≤ H) :
    (((Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even).card : ℝ) ≤ H := by
  classical
  by_cases hN : 0 ≤ N
  · exact even_window_card hN hH
  · have hfloor : ⌊N⌋₊ = 0 := Nat.floor_eq_zero.mpr (by linarith)
    have htop : (⌊N + H⌋₊ : ℝ) ≤ H := by
      by_cases hNH : 0 ≤ N + H
      · exact (Nat.floor_le hNH).trans (by linarith)
      · rw [Nat.floor_eq_zero.mpr (by linarith : N + H < 1)]
        norm_num only [Nat.cast_zero]
        linarith
    calc (((Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even).card : ℝ) ≤
        ((Ioc ⌊N⌋₊ ⌊N + H⌋₊).card : ℝ) := by
          exact_mod_cast Finset.card_filter_le (Ioc ⌊N⌋₊ ⌊N + H⌋₊) Even
      _ = (⌊N + H⌋₊ : ℝ) := by simp [hfloor]
      _ ≤ H := htop

/-- Page 44 display 3 support: the exact finite even Fourier kernel comparison. -/
theorem even_window_kernel {N H : ℝ} (hH : 2 ≤ H) (x : ℝ) :
    ‖∑ m ∈ (Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even, phase ((m : ℝ) * x)‖ ≤
      kernel H (2 * x) := by
  have hcap : ‖∑ m ∈ (Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even,
      phase ((m : ℝ) * x)‖ ≤ H := by
    calc _ ≤ ∑ m ∈ (Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even,
          ‖phase ((m : ℝ) * x)‖ := norm_sum_le _ _
      _ = (((Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even).card : ℝ) := by simp [phase_norm]
      _ ≤ H := even_window_card_any hH
  unfold kernel
  split_ifs with hx
  · exact hcap
  · exact le_min hcap (even_window_inverse _ _ hx)

/-- Page 44 display 3 support: a phase times a conjugate has difference argument. -/
theorem phase_mul_conj (u v : ℝ) :
    phase u * (starRingEnd ℂ) (phase v) = phase (u - v) := by
  unfold phase
  rw [← Complex.exp_conj, ← Complex.exp_add]
  congr 1
  push_cast
  norm_num
  rw [map_ofNat]
  ring

/-- Page 44 display 3 support: every continuous function is square integrable
on the minor part of the compact period. -/
theorem continuous_minor_memLp (N Y H B : ℝ) {f : ℝ → ℂ} (hf : Continuous f) :
    MemLp f 2 (volume.restrict (minorDomain N Y H B)) := by
  apply (memLp_two_iff_integrable_sq_norm hf.aestronglyMeasurable).mpr
  exact (hf.norm.pow 2).integrableOn_Icc.mono_set Set.sdiff_subset

/-- Page 44 display 3 support: the capped reciprocal kernel is measurable. -/
theorem capped_kernel_measurable (H : ℝ) : Measurable (kernel H) := by
  have habs : Measurable fun x : ℝ => |x - (round x : ℤ)| := by
    simp_rw [abs_sub_round_eq_min]
    exact measurable_fract.min (measurable_const.sub measurable_fract)
  have hset : MeasurableSet {x : ℝ | x = (round x : ℤ)} := by
    have heq : {x : ℝ | x = (round x : ℤ)} = {x : ℝ | |x - (round x : ℤ)| = 0} := by
      ext x
      simp [abs_eq_zero, sub_eq_zero]
    rw [heq]
    exact habs (measurableSet_singleton 0)
  exact Measurable.ite hset measurable_const (measurable_const.min habs.inv)

/-- Page 44 display 3 support: multiplying S2 by a capped kernel preserves L2. -/
theorem second_kernel_memLp (N Y H B ξ : ℝ) (hH : 0 ≤ H) :
    MemLp (fun y => ‖secondSum Y y‖ * kernel H (2 * (y - ξ))) 2
      (volume.restrict (minorDomain N Y H B)) := by
  have hg : Continuous (secondSum Y) := by unfold secondSum phase; fun_prop
  have hk0 (y : ℝ) : 0 ≤ kernel H (2 * (y - ξ)) := by
    unfold kernel
    split_ifs <;> positivity
  have hkle (y : ℝ) : kernel H (2 * (y - ξ)) ≤ H := by
    unfold kernel
    split_ifs
    · exact le_rfl
    · exact min_le_left _ _
  refine ((continuous_minor_memLp N Y H B hg).norm.const_mul H).mono' ?_ ?_
  · exact (hg.norm.measurable.mul ((capped_kernel_measurable H).comp (by fun_prop))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg _) (hk0 y))]
      calc _ ≤ ‖secondSum Y y‖ * H := mul_le_mul_of_nonneg_left (hkle y) (norm_nonneg _)
        _ = _ := by ring

/-- Page 44 display 3 support: finite coefficient energy is an iterated kernel integral.
The only hypotheses are integrability of the finitely many coefficient integrands. -/
theorem coefficient_double_integral {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ℕ) (f : α → ℂ) (p : ℕ → α → ℂ)
    (hf : ∀ m ∈ s, Integrable (fun x => f x * p m x) μ) :
    ((∑ m ∈ s, ‖∫ x, f x * p m x ∂μ‖ ^ 2 : ℝ) : ℂ) =
      ∫ x, f x * (∫ y, (starRingEnd ℂ) (f y) *
        (∑ m ∈ s, p m x * (starRingEnd ℂ) (p m y)) ∂μ) ∂μ := by
  classical
  have hinner (x : α) :
      (∫ y, (starRingEnd ℂ) (f y) *
        (∑ m ∈ s, p m x * (starRingEnd ℂ) (p m y)) ∂μ) =
        ∑ m ∈ s, p m x * (starRingEnd ℂ) (∫ y, f y * p m y ∂μ) := by
    calc _ = ∫ y, ∑ m ∈ s, p m x * (starRingEnd ℂ) (f y * p m y) ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun y => by
            dsimp only
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro m hm
            rw [map_mul]
            ring
      _ = ∑ m ∈ s, ∫ y, p m x * (starRingEnd ℂ) (f y * p m y) ∂μ :=
        integral_finsetSum s (fun m hm => ((Complex.conjCLE.integrable_comp_iff.mpr (hf m hm))).const_mul _)
      _ = _ := by
        apply Finset.sum_congr rfl
        intro m hm
        rw [integral_const_mul, integral_conj]
  simp_rw [hinner]
  rw [show (fun x => f x * ∑ m ∈ s, p m x *
      (starRingEnd ℂ) (∫ y, f y * p m y ∂μ)) =
      (fun x => ∑ m ∈ s, (f x * p m x) *
      (starRingEnd ℂ) (∫ y, f y * p m y ∂μ)) by
        funext x
        rw [Finset.mul_sum]
        simp_rw [mul_assoc]]
  rw [integral_finsetSum s (fun m hm => (hf m hm).mul_const _)]
  push_cast
  apply Finset.sum_congr rfl
  intro m hm
  rw [integral_mul_const]
  exact (Complex.mul_conj' _).symm

/-- Page 44 display 3 support: two integral Cauchy Schwarz steps bound finite energy.
The real kernel majorizes the finite phase kernel and its weighted square mass
has the explicit uniform bound K. No prime or density hypothesis occurs. -/
theorem finite_energy_of_kernel {α : Type*} [MeasurableSpace α]
    (μ : Measure α) (s : Finset ℕ) (f g : α → ℂ) (p : ℕ → α → ℂ)
    (k : α → α → ℝ) {K : ℝ} (hK : 0 ≤ K)
    (hf : MemLp f 2 μ) (hg : MemLp g 2 μ)
    (hc : ∀ m ∈ s, Integrable (fun x => (f x * g x) * p m x) μ)
    (hk : ∀ x y, ‖∑ m ∈ s, p m x * (starRingEnd ℂ) (p m y)‖ ≤ k x y)
    (hw : ∀ x, MemLp (fun y => ‖g y‖ * k x y) 2 μ)
    (hmass : ∀ x, (∫ y, ‖g y‖ ^ 2 * k x y ^ 2 ∂μ) ≤ K) :
    (∑ m ∈ s, ‖∫ x, (f x * g x) * p m x ∂μ‖ ^ 2) ^ 2 ≤
      (∫ x, ‖f x‖ ^ 2 ∂μ) ^ 2 * (∫ x, ‖g x‖ ^ 2 ∂μ) * K := by
  classical
  let E₁ := ∫ x, ‖f x‖ ^ 2 ∂μ
  let E₂ := ∫ x, ‖g x‖ ^ 2 ∂μ
  let I := ∫ x, ‖f x‖ * ‖g x‖ ∂μ
  let J := ∑ m ∈ s, ‖∫ x, (f x * g x) * p m x ∂μ‖ ^ 2
  have hE₁ : 0 ≤ E₁ := integral_nonneg (fun _ => sq_nonneg _)
  have hE₂ : 0 ≤ E₂ := integral_nonneg (fun _ => sq_nonneg _)
  have hI : 0 ≤ I := integral_nonneg (fun _ => mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hJ : 0 ≤ J := Finset.sum_nonneg (fun _ _ => sq_nonneg _)
  have houter : I ^ 2 ≤ E₁ * E₂ := CoefficientGlue489.integral_cauchy_squared μ
    (Filter.Eventually.of_forall fun _ => norm_nonneg _)
    (Filter.Eventually.of_forall fun _ => norm_nonneg _) hf.norm hg.norm
  have hinner (x : α) :
      ‖∫ y, (starRingEnd ℂ) (f y * g y) *
        (∑ m ∈ s, p m x * (starRingEnd ℂ) (p m y)) ∂μ‖ ≤ Real.sqrt (E₁ * K) := by
    have hk0 (y : α) : 0 ≤ k x y := (norm_nonneg _).trans (hk x y)
    have hcs := CoefficientGlue489.integral_cauchy_squared μ
      (Filter.Eventually.of_forall fun _ => norm_nonneg _)
      (Filter.Eventually.of_forall fun y => mul_nonneg (norm_nonneg _) (hk0 y)) hf.norm (hw x)
    have hcs' : (∫ y, ‖f y‖ * (‖g y‖ * k x y) ∂μ) ^ 2 ≤ E₁ * K := by
      calc _ ≤ E₁ * (∫ y, (‖g y‖ * k x y) ^ 2 ∂μ) := hcs
        _ = E₁ * (∫ y, ‖g y‖ ^ 2 * k x y ^ 2 ∂μ) := by simp_rw [mul_pow]
        _ ≤ E₁ * K := mul_le_mul_of_nonneg_left (hmass x) hE₁
    have hi0 : 0 ≤ ∫ y, ‖f y‖ * (‖g y‖ * k x y) ∂μ :=
      integral_nonneg (fun y => mul_nonneg (norm_nonneg _) (mul_nonneg (norm_nonneg _) (hk0 y)))
    calc _ ≤ ∫ y, ‖f y‖ * (‖g y‖ * k x y) ∂μ := by
          apply norm_integral_le_of_norm_le (hf.norm.integrable_mul (hw x))
          exact Filter.Eventually.of_forall fun y => by
            simp only [norm_mul, RCLike.norm_conj]
            calc ‖f y‖ * ‖g y‖ * ‖∑ m ∈ s, p m x * (starRingEnd ℂ) (p m y)‖ ≤
                ‖f y‖ * ‖g y‖ * k x y :=
                  mul_le_mul_of_nonneg_left (hk x y) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
              _ = _ := by dsimp only [Pi.mul_apply]; ring
      _ ≤ Real.sqrt (E₁ * K) := CoefficientGlue489.inner_bound_of_square hE₁ hK hi0 hcs'
  have hbilinear := coefficient_double_integral μ s (fun x => f x * g x) p hc
  have hbound : J ≤ I * Real.sqrt (E₁ * K) := by
    calc J = ‖∫ x, (f x * g x) * (∫ y, (starRingEnd ℂ) (f y * g y) *
          (∑ m ∈ s, p m x * (starRingEnd ℂ) (p m y)) ∂μ) ∂μ‖ := by
            rw [← hbilinear, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hJ]
      _ ≤ ∫ x, (‖f x‖ * ‖g x‖) * Real.sqrt (E₁ * K) ∂μ := by
        apply norm_integral_le_of_norm_le ((hf.norm.integrable_mul hg.norm).mul_const _)
        exact Filter.Eventually.of_forall fun x => by
          simp only [norm_mul]
          exact mul_le_mul_of_nonneg_left (hinner x) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
      _ = I * Real.sqrt (E₁ * K) := integral_mul_const _ _
  exact CoefficientGlue489.two_cauchy_bounds hE₁ hE₂ hK hI hJ houter hbound

/-- Page 44 display 3: the finite Fourier comparison before Parseval.
This is the integral energy form with all finite kernel and Cauchy Schwarz
steps supplied. It has no density or prime weight input. -/
theorem minor_energy_from_kernel :
    ∀ N Y H B K : ℝ, 16 ≤ H → 0 ≤ K →
      (∀ ξ : ℝ, kernelMass N Y H B ξ ≤ K) →
      (∑ m ∈ (Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even,
        ‖minorCoefficient N Y H B m‖ ^ 2) ^ 2 ≤
        (∫ x in minorDomain N Y H B, ‖firstSum N Y x‖ ^ 2) ^ 2 *
          (∫ x in minorDomain N Y H B, ‖secondSum Y x‖ ^ 2) * K := by
  intro N Y H B K hH hK hmass
  have hf : Continuous (firstSum N Y) := by unfold firstSum phase; fun_prop
  have hg : Continuous (secondSum Y) := by unfold secondSum phase; fun_prop
  apply finite_energy_of_kernel (volume.restrict (minorDomain N Y H B))
    ((Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even) (firstSum N Y) (secondSum Y)
    (fun m x => phase (-(m : ℝ) * x)) (fun x y => kernel H (2 * (y - x))) hK
    (continuous_minor_memLp N Y H B hf) (continuous_minor_memLp N Y H B hg)
  · intro m hm
    have hc : Continuous (fun x => (firstSum N Y x * secondSum Y x) * phase (-(m : ℝ) * x)) := by
      unfold firstSum secondSum phase
      fun_prop
    exact hc.integrableOn_Icc.mono_set Set.sdiff_subset
  · intro x y
    simp_rw [phase_mul_conj,
      show ∀ m : ℕ, -(m : ℝ) * x - (-(m : ℝ) * y) = (m : ℝ) * (y - x) by intro m; ring]
    exact even_window_kernel (by linarith) (y - x)
  · intro x
    exact second_kernel_memLp N Y H B x (by linarith)
  · exact hmass

/-- Page 44 display 3, first equality: the actual minor coefficient energy
is the iterated integral with the finite even difference phase kernel. -/
theorem minor_coefficient_double_integral (N Y H B : ℝ) :
    ((∑ m ∈ (Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even,
      ‖minorCoefficient N Y H B m‖ ^ 2 : ℝ) : ℂ) =
    ∫ ξ in minorDomain N Y H B, (firstSum N Y ξ * secondSum Y ξ) *
      (∫ α in minorDomain N Y H B,
        (starRingEnd ℂ) (firstSum N Y α * secondSum Y α) *
          (∑ m ∈ (Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even,
            phase ((m : ℝ) * (α - ξ)))) := by
  have hc (m : ℕ) : IntegrableOn
      (fun x => (firstSum N Y x * secondSum Y x) * phase (-(m : ℝ) * x))
      (minorDomain N Y H B) volume := by
    have hcont : Continuous
        (fun x => (firstSum N Y x * secondSum Y x) * phase (-(m : ℝ) * x)) := by
      unfold firstSum secondSum phase
      fun_prop
    exact hcont.integrableOn_Icc.mono_set Set.sdiff_subset
  have hid := coefficient_double_integral (volume.restrict (minorDomain N Y H B))
    ((Ioc ⌊N⌋₊ ⌊N + H⌋₊).filter Even)
    (fun x => firstSum N Y x * secondSum Y x) (fun m x => phase (-(m : ℝ) * x))
    (fun m _ => hc m)
  refine hid.trans ?_
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    dsimp only
    congr 1
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun α => by
      dsimp only
      congr 1
      apply Finset.sum_congr rfl
      intro m hm
      rw [phase_mul_conj]
      congr 1
      ring

/-- Page 44 display 3 support: the abstract integral hypotheses have a nonzero
rank one model with unit square mass, unit kernel and unit coefficient energy. -/
theorem rank_one_instance :
    MemLp (fun _ : ℝ => (1 : ℂ)) 2 (Measure.dirac (0 : ℝ)) ∧
    Integrable (fun _ : ℝ => (1 : ℂ)) (Measure.dirac (0 : ℝ)) ∧
    MemLp (fun _ : ℝ => (1 : ℝ)) 2 (Measure.dirac (0 : ℝ)) ∧
    ‖∑ m ∈ ({0} : Finset ℕ), (1 : ℂ) * (starRingEnd ℂ) (1 : ℂ)‖ = 1 ∧
    (∫ y : ℝ, ‖(1 : ℂ)‖ ^ 2 * (1 : ℝ) ^ 2 ∂Measure.dirac (0 : ℝ)) = 1 ∧
    ‖∫ y : ℝ, (1 : ℂ) ∂Measure.dirac (0 : ℝ)‖ ^ 2 = 1 := by
  refine ⟨memLp_const _, integrable_const _, memLp_const _, ?_, ?_, ?_⟩ <;> simp

/-- Page 44 display 3 support: the punctured cell, negative N window
and integer pole cases have concrete admissible instances. -/
theorem kernel_domain_instances :
    (1 / 4 : ℝ) ≠ (round (1 / 4 : ℝ) : ℤ) ∧
    ‖∑ k ∈ range 1, phase (1 / 4 : ℝ) ^ k‖ ≤ 4 ∧
    (((Ioc ⌊(-1 : ℝ)⌋₊ ⌊(-1 : ℝ) + 2⌋₊).filter Even).card : ℝ) = 0 ∧
    kernel 2 0 = 2 := by
  norm_num [round_eq, kernel]

/-- Page 44 display 3 support: the actual Fourier comparison has a nonzero
coefficient model. At N = Y = 2 and B = 1 the major set is empty. -/
theorem nonzero_minor_coefficient_instance :
    minorCoefficient 2 2 16 1 4 = (((Real.log 2) ^ 2 : ℝ) : ℂ) ∧
      0 < ‖minorCoefficient 2 2 16 1 4‖ := by
  have hlog : Real.log 2 < 1 := by
    have h := Real.log_lt_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (2 : ℝ) ≠ 1)
    linarith
  have hmajor : majorSet 2 2 1 = ∅ := by
    ext α
    simp only [majorSet, Set.mem_ofPred_eq, Set.notMem_empty, iff_false]
    rintro ⟨q, a, hq, hqlog, ha, haq, hcop, hdist⟩
    have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
    norm_num only [Real.rpow_one] at hqlog
    linarith
  have hIoc : Finset.Ioc (0 : ℕ) 2 = {1, 2} := by decide
  have hIcc : Finset.Icc (1 : ℕ) 2 = {1, 2} := by decide
  have hΛ := ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  have hfirst (x : ℝ) : firstSum 2 2 x = (Real.log 2 : ℂ) * phase (2 * x) := by
    norm_num [firstSum, hIoc, hΛ]
  have hsecond (x : ℝ) : secondSum 2 x = (Real.log 2 : ℂ) * phase (2 * x) := by
    norm_num [secondSum, hIcc, hΛ]
  have hpoint (x : ℝ) :
      firstSum 2 2 x * secondSum 2 x * phase (-(4 : ℝ) * x) =
        (((Real.log 2) ^ 2 : ℝ) : ℂ) := by
    rw [hfirst, hsecond]
    calc _ = (Real.log 2 : ℂ) ^ 2 *
        ((phase (2 * x) * phase (2 * x)) * phase (-(4 : ℝ) * x)) := by ring
      _ = (Real.log 2 : ℂ) ^ 2 * phase (2 * x + 2 * x + -(4 : ℝ) * x) := by
        rw [← phase_add, ← phase_add]
      _ = _ := by rw [show 2 * x + 2 * x + -(4 : ℝ) * x = 0 by ring]; simp [phase]
  have heq : minorCoefficient 2 2 16 1 4 = (((Real.log 2) ^ 2 : ℝ) : ℂ) := by
    unfold minorCoefficient
    rw [hmajor]
    simp only [Set.sdiff_empty, Nat.cast_ofNat]
    simp_rw [hpoint]
    norm_num [period]
  refine ⟨heq, ?_⟩
  rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_pos_of_pos (Real.log_pos (by norm_num))

#print axioms nonzero_minor_coefficient_instance
#print axioms kernel_domain_instances
#print axioms rank_one_instance
#print axioms minor_coefficient_double_integral
#print axioms phase_integer_translate
#print axioms phase_nearest_gap
#print axioms geometric_nearest_inverse
#print axioms phase_nat_mul
#print axioms phase_add
#print axioms even_window_reindex
#print axioms phase_interval_geometric
#print axioms even_window_inverse
#print axioms even_window_card_any
#print axioms even_window_kernel
#print axioms phase_mul_conj
#print axioms continuous_minor_memLp
#print axioms capped_kernel_measurable
#print axioms second_kernel_memLp
#print axioms coefficient_double_integral
#print axioms finite_energy_of_kernel
#print axioms minor_energy_from_kernel
end
end LeanLab.Languasco2004.Decomp531a
