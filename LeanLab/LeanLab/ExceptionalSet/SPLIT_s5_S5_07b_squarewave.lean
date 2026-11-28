/-
Split of the LEAF `leaf_s5_07_square_wave_truncation` of
`LeanLab.ExceptionalSet.SPLIT_s5_S5_07_smoothed`, KEEP GOING unit S5-07b, CLOUD S5 burst-20261127.
P0082 Bruedern and Perelli 1998, §7, p. 370, display (40): the smoothed square wave.

In the variable `y = F(n)` the parity weight is the square wave `(-1)^{⌊y⌋}`, of period `2`.
Its average over `[y - Δ, y + Δ]`, `s5AvgWave Δ y`, equals the wave when `y` is at distance at
least `Δ` from the integers and has modulus at most `1`.  Its Fourier coefficients at the
frequencies `h/2` are `s5SqCoeff Δ h = (2/(π h)) (sin(π h Δ)/(π h Δ)) (-i)` for odd `h` and `0`
for even `h`: the coefficient `2/(π i h)` of the square wave times the averaging factor.

Leaf, the only open piece:
* `leaf_s5_07b_fourier_hasSum`, HARD: the Fourier series of the average converges to it at
  every point, the coefficients being absolutely summable.

Proved here, axioms propext, Classical.choice, Quot.sound only: `s5_07b_avg_eq_wave`, the
average equals the wave away from the jumps; `s5_07b_avg_norm_le`, the average has modulus at
most `1`; `s5_07b_coeff_le`, the coefficient bound `‖s5SqCoeff Δ h‖ ≤ 2/(|h|+1)`;
`s5_07b_inv_sq_one_sign` and `s5_07b_tail`, `Σ_{|h| > H} ‖s5SqCoeff Δ h‖ ≤ 8/(9 H Δ) ≤ 1/(H Δ)`;
and the assembly `leaf_s5_07_square_wave_truncation_of_leaves`, the exact statement of the leaf
being split, CONDITIONAL ON the one leaf.

New definitions, for a reviewer: `s5SqCoeff` and `s5AvgWave`, both display (40).

AI wrote the Lean code.  Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.SPLIT_s5_S5_07_smoothed

namespace LeanLab.ExceptionalSet.U1539

open Filter Topology

/-- P0082 p. 370 display (40): the Fourier coefficient at frequency `h/2` of the square wave
`(-1)^{⌊y⌋}` averaged over a window of half width `Δ`, namely `2/(π i h)` times
`sin(π h Δ)/(π h Δ)` for odd `h`, and `0` for even `h`. -/
noncomputable def s5SqCoeff (Δ : ℝ) (h : ℤ) : ℂ :=
  if Odd h then
    ((2 / (Real.pi * h) * (Real.sin (Real.pi * h * Δ) / (Real.pi * h * Δ)) : ℝ) : ℂ) *
      (-Complex.I)
  else 0

/-- P0082 p. 370 display (40): the smoothed square wave, the average of `(-1)^{⌊t⌋}` over
`y - Δ ≤ t ≤ y + Δ`. -/
noncomputable def s5AvgWave (Δ y : ℝ) : ℂ :=
  ((1 / (2 * Δ) : ℝ) : ℂ) * ∫ t in (y - Δ)..(y + Δ), (-1 : ℂ) ^ ⌊t⌋

/-- Display (40), p. 370, the smoothing is exact away from the jumps. When `y` is at
distance at least `Δ` from the integers, `(-1)^{⌊t⌋}` is constant on `[y - Δ, y + Δ]` up to the
endpoint `⌊y⌋ + 1`, so the average is `(-1)^{⌊y⌋}`. -/
theorem s5_07b_avg_eq_wave (Δ y : ℝ) (hΔ : 0 < Δ) (h1 : Δ ≤ Int.fract y)
    (h2 : Int.fract y ≤ 1 - Δ) : s5AvgWave Δ y = (-1 : ℂ) ^ ⌊y⌋ := by
  have hfy := Int.floor_add_fract y
  have hae : ∀ᵐ t ∂MeasureTheory.volume, t ∈ Set.uIoc (y - Δ) (y + Δ) →
      (-1 : ℂ) ^ ⌊t⌋ = (fun _ : ℝ => (-1 : ℂ) ^ ⌊y⌋) t := by
    filter_upwards [(Set.countable_singleton (y + Δ)).ae_notMem MeasureTheory.volume] with t hne ht
    rw [Set.uIoc_of_le (by linarith)] at ht
    have hlt : t < y + Δ := lt_of_le_of_ne ht.2 (by simpa using hne)
    have hfl : ⌊t⌋ = ⌊y⌋ := by
      rw [Int.floor_eq_iff]; constructor <;> linarith [ht.1]
    simp only [hfl]
  unfold s5AvgWave
  rw [intervalIntegral.integral_congr_ae hae, intervalIntegral.integral_const]
  have h2Δ : (2 * Δ : ℝ) ≠ 0 := by positivity
  rw [show y + Δ - (y - Δ) = 2 * Δ by ring, Complex.real_smul, ← mul_assoc, ← Complex.ofReal_mul,
    one_div, inv_mul_cancel₀ h2Δ, Complex.ofReal_one, one_mul]

/-- LEAF: display (40), p. 370, the Fourier expansion of the smoothed square wave, HARD. The
average is continuous and `2`-periodic in `y`, its Fourier coefficients at frequency `h/2` are
`s5SqCoeff Δ h`, which are `O(1/(h² Δ))` and hence absolutely summable, so its Fourier series
converges to it at every point. -/
theorem leaf_s5_07b_fourier_hasSum (Δ : ℝ) (hΔ₀ : 0 < Δ) (hΔ₁ : Δ ≤ 1 / 4) (y : ℝ) :
    HasSum (fun h : ℤ => s5SqCoeff Δ h * eC (h / 2 * y)) (s5AvgWave Δ y) := by
  sorry

/-- `Σ 1/h²` over a finite set of integers `h` of one sign with `|h| > H` is at most `2/(H+1)`. -/
theorem s5_07b_inv_sq_one_sign (H : ℤ) (hH : 1 ≤ H) (t : Finset ℤ) (ht : ∀ h ∈ t, H < |h|)
    (hinj : Set.InjOn Int.natAbs t) :
    ∑ h ∈ t, ((h : ℝ) ^ 2)⁻¹ ≤ 2 / ((H : ℝ) + 1) := by
  set Hn := H.toNat with hHn
  have hHn' : (Hn : ℤ) = H := Int.toNat_of_nonneg (by omega)
  set M := t.sup Int.natAbs + 1 with hM
  have hcast : ∀ h ∈ t, ((h : ℝ) ^ 2)⁻¹ = (((h.natAbs : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro h _
    congr 1
    have : ((h.natAbs : ℤ) : ℝ) ^ 2 = (h : ℝ) ^ 2 := by
      rw [Int.natCast_natAbs, Int.cast_abs, sq_abs]
    rw [← this]; norm_cast
  rw [Finset.sum_congr rfl hcast, ← Finset.sum_image (f := fun k : ℕ => ((k : ℝ) ^ 2)⁻¹) hinj]
  have hsub : t.image Int.natAbs ⊆ Finset.Ioo Hn M := by
    intro k hk
    rw [Finset.mem_image] at hk
    obtain ⟨h, hh, rfl⟩ := hk
    rw [Finset.mem_Ioo]
    constructor
    · have := ht h hh
      have h2 : ((h.natAbs : ℕ) : ℤ) = |h| := Int.natCast_natAbs h
      omega
    · have := Finset.le_sup (f := Int.natAbs) hh
      omega
  refine (Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)).trans ?_
  have := sum_Ioo_inv_sq_le (α := ℝ) Hn M
  have hc : ((Hn : ℕ) : ℝ) = (H : ℝ) := by exact_mod_cast hHn'
  rw [hc] at this
  exact this

/-- Display (40), p. 370, the tail of the smoothed series, proved. For `H ≥ 1`
and every finite set of integers `h` with `|h| > H`, `Σ ‖s5SqCoeff Δ h‖ ≤ 1/(HΔ)`: each term is
at most `2/(π² h² Δ)` since `|sin z| ≤ 1`, and `Σ_{|h| > H} 1/h² ≤ 4/(H+1)`. -/
theorem s5_07b_tail (Δ : ℝ) (hΔ₀ : 0 < Δ) (H : ℤ) (hH : 1 ≤ H) (s : Finset ℤ)
    (hs : ∀ h ∈ s, H < |h|) :
    ∑ h ∈ s, ‖s5SqCoeff Δ h‖ ≤ 1 / (H * Δ) := by
  have hpi := Real.pi_gt_three
  have hterm : ∀ h ∈ s, ‖s5SqCoeff Δ h‖ ≤ (2 / (9 * Δ)) * ((h : ℝ) ^ 2)⁻¹ := by
    intro h hh
    have hHh := hs h hh
    have hh0 : (h : ℝ) ≠ 0 := by
      intro hz
      have : h = 0 := by exact_mod_cast hz
      rw [this] at hHh; simp at hHh; omega
    have hsq : 0 < (h : ℝ) ^ 2 := by positivity
    unfold s5SqCoeff
    split_ifs
    · rw [norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
      have hx0 : Real.pi * h * Δ ≠ 0 := by positivity
      have hval : 2 / (Real.pi * h) * (Real.sin (Real.pi * h * Δ) / (Real.pi * h * Δ))
          = Real.sin (Real.pi * h * Δ) * (2 / (Real.pi ^ 2 * Δ * (h : ℝ) ^ 2)) := by
        field_simp
      rw [hval, abs_mul]
      have hs1 : |Real.sin (Real.pi * h * Δ)| ≤ 1 := Real.abs_sin_le_one _
      have hpos : 0 < Real.pi ^ 2 * Δ * (h : ℝ) ^ 2 := by positivity
      rw [abs_of_pos (by positivity : (0 : ℝ) < 2 / (Real.pi ^ 2 * Δ * (h : ℝ) ^ 2))]
      have hpi2 : 9 < Real.pi ^ 2 := by nlinarith
      have hle : 2 / (Real.pi ^ 2 * Δ * (h : ℝ) ^ 2) ≤ 2 / (9 * Δ) * ((h : ℝ) ^ 2)⁻¹ := by
        rw [← div_eq_mul_inv, div_div]
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        have : 0 < Δ * (h : ℝ) ^ 2 := by positivity
        nlinarith
      calc |Real.sin (Real.pi * h * Δ)| * (2 / (Real.pi ^ 2 * Δ * (h : ℝ) ^ 2))
          ≤ 1 * (2 / (Real.pi ^ 2 * Δ * (h : ℝ) ^ 2)) :=
            mul_le_mul_of_nonneg_right hs1 (by positivity)
        _ ≤ 2 / (9 * Δ) * ((h : ℝ) ^ 2)⁻¹ := by rw [one_mul]; exact hle
    · rw [norm_zero]; positivity
  refine (Finset.sum_le_sum hterm).trans ?_
  rw [← Finset.mul_sum, ← Finset.sum_filter_add_sum_filter_not s (fun h : ℤ => 0 < h)]
  have hp := s5_07b_inv_sq_one_sign H hH (s.filter (fun h : ℤ => 0 < h))
    (fun h hh => hs h (Finset.mem_filter.mp hh).1)
    (by
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      omega)
  have hn := s5_07b_inv_sq_one_sign H hH (s.filter (fun h : ℤ => ¬ 0 < h))
    (fun h hh => hs h (Finset.mem_filter.mp hh).1)
    (by
      intro a ha b hb hab
      have ha' := (Finset.mem_filter.mp ha).2
      have hb' := (Finset.mem_filter.mp hb).2
      omega)
  have hHpos : (0 : ℝ) < H := by exact_mod_cast hH
  have hfin : 2 / (9 * Δ) * (2 / ((H : ℝ) + 1) + 2 / ((H : ℝ) + 1)) ≤ 1 / (H * Δ) := by
    rw [div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : 2 / ((H : ℝ) + 1) ≤ 2 / H := div_le_div_of_nonneg_left (by norm_num) hHpos (by linarith)
    have h2 : 2 * (2 / ((H : ℝ) + 1) + 2 / ((H : ℝ) + 1)) * (H * Δ) ≤ 2 * (2 / H + 2 / H) * (H * Δ) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
    have h3 : 2 * (2 / (H : ℝ) + 2 / H) * (H * Δ) = 8 * Δ := by field_simp; ring
    nlinarith
  have hsum0 : 0 ≤ 2 / (9 * Δ) := by positivity
  calc 2 / (9 * Δ) * (∑ h ∈ s.filter (fun h : ℤ => 0 < h), ((h : ℝ) ^ 2)⁻¹ +
        ∑ h ∈ s.filter (fun h : ℤ => ¬ 0 < h), ((h : ℝ) ^ 2)⁻¹)
      ≤ 2 / (9 * Δ) * (2 / ((H : ℝ) + 1) + 2 / ((H : ℝ) + 1)) :=
        mul_le_mul_of_nonneg_left (add_le_add hp hn) hsum0
    _ ≤ 1 / (H * Δ) := hfin

private theorem s5_07_norm_eC' (x : ℝ) : ‖eC x‖ = 1 := by
  unfold eC
  have : (2 * Real.pi * Complex.I * (x : ℂ)) = ((2 * Real.pi * x : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, Complex.norm_exp_ofReal_mul_I]

/-- The smoothed square wave has modulus at most `1`. -/
theorem s5_07b_avg_norm_le (Δ y : ℝ) (hΔ : 0 < Δ) : ‖s5AvgWave Δ y‖ ≤ 1 := by
  unfold s5AvgWave
  rw [norm_mul]
  have hb : ‖∫ t in (y - Δ)..(y + Δ), (-1 : ℂ) ^ ⌊t⌋‖ ≤ 1 * |(y + Δ) - (y - Δ)| := by
    apply intervalIntegral.norm_integral_le_of_norm_le_const
    intro t _
    rw [norm_zpow, norm_neg, norm_one, one_zpow]
  have hlen : |(y + Δ) - (y - Δ)| = 2 * Δ := by
    rw [show (y + Δ) - (y - Δ) = 2 * Δ by ring]; exact abs_of_pos (by linarith)
  rw [hlen, one_mul] at hb
  have hc : ‖((1 / (2 * Δ) : ℝ) : ℂ)‖ = 1 / (2 * Δ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  rw [hc]
  calc 1 / (2 * Δ) * ‖∫ t in (y - Δ)..(y + Δ), (-1 : ℂ) ^ ⌊t⌋‖
      ≤ 1 / (2 * Δ) * (2 * Δ) := mul_le_mul_of_nonneg_left hb (by positivity)
    _ = 1 := by field_simp

/-- The coefficient bound of display (40): `‖s5SqCoeff Δ h‖ ≤ 2/(|h|+1)`. -/
theorem s5_07b_coeff_le (Δ : ℝ) (hΔ : 0 < Δ) (h : ℤ) :
    ‖s5SqCoeff Δ h‖ ≤ 2 / (|(h : ℝ)| + 1) := by
  unfold s5SqCoeff
  split_ifs with ho
  · rw [norm_mul, norm_neg, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs]
    have hh0 : (h : ℝ) ≠ 0 := by
      intro hz
      have : h = 0 := by exact_mod_cast hz
      rw [this] at ho
      exact (by simp : ¬ Odd (0 : ℤ)) ho
    have hpi := Real.pi_gt_three
    have habs1 : 1 ≤ |(h : ℝ)| := by
      have : (1 : ℤ) ≤ |h| := Int.one_le_abs (by exact_mod_cast hh0)
      have h' : ((|h| : ℤ) : ℝ) = |(h : ℝ)| := by push_cast; rfl
      rw [← h']; exact_mod_cast this
    set x := Real.pi * h * Δ with hx
    have hx0 : x ≠ 0 := by rw [hx]; positivity
    have hsinc : |Real.sin x / x| ≤ 1 := by
      rw [abs_div, div_le_one (abs_pos.mpr hx0)]
      exact Real.abs_sin_le_abs
    rw [abs_mul]
    have hfirst : |2 / (Real.pi * h)| = 2 / (Real.pi * |(h : ℝ)|) := by
      rw [abs_div, abs_mul, abs_of_pos Real.pi_pos, abs_two]
    rw [hfirst]
    have hpos : 0 < Real.pi * |(h : ℝ)| := by positivity
    calc 2 / (Real.pi * |(h : ℝ)|) * |Real.sin x / x| ≤ 2 / (Real.pi * |(h : ℝ)|) * 1 :=
          mul_le_mul_of_nonneg_left hsinc (by positivity)
      _ = 2 / (Real.pi * |(h : ℝ)|) := mul_one _
      _ ≤ 2 / (|(h : ℝ)| + 1) := by
          apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
          nlinarith
  · simp only [norm_zero]; positivity

/-- `leaf_s5_07_square_wave_truncation`, exact statement, from the two leaves and the proved pieces. -/
theorem leaf_s5_07_square_wave_truncation_of_leaves (Δ : ℝ) (hΔ₀ : 0 < Δ) (hΔ₁ : Δ ≤ 1 / 4)
    (H : ℤ) (hH : 1 ≤ H) :
    ∃ b : ℤ → ℂ, (∀ h : ℤ, ‖b h‖ ≤ 2 / (|(h : ℝ)| + 1)) ∧ ∀ y : ℝ,
      ‖(-1 : ℂ) ^ ⌊y⌋ - ∑ h ∈ Finset.Icc (-H) H, b h * eC (h / 2 * y)‖
          ≤ 2 + 1 / (H * Δ) ∧
        (Δ ≤ Int.fract y → Int.fract y ≤ 1 - Δ →
          ‖(-1 : ℂ) ^ ⌊y⌋ - ∑ h ∈ Finset.Icc (-H) H, b h * eC (h / 2 * y)‖
            ≤ 1 / (H * Δ)) := by
  refine ⟨s5SqCoeff Δ, s5_07b_coeff_le Δ hΔ₀, fun y => ?_⟩
  set I := Finset.Icc (-H) H with hI
  set f : ℤ → ℂ := fun h => s5SqCoeff Δ h * eC (h / 2 * y) with hf
  have hsum := leaf_s5_07b_fourier_hasSum Δ hΔ₀ hΔ₁ y
  -- the tail bound for the limit
  have htail : ‖s5AvgWave Δ y - ∑ h ∈ I, f h‖ ≤ 1 / (H * Δ) := by
    have ht : Tendsto (fun t : Finset ℤ => ∑ h ∈ t, f h) atTop (𝓝 (s5AvgWave Δ y)) := hsum
    have ht2 : Tendsto (fun t : Finset ℤ => ‖∑ h ∈ t, f h - ∑ h ∈ I, f h‖) atTop
        (𝓝 ‖s5AvgWave Δ y - ∑ h ∈ I, f h‖) := (ht.sub_const _).norm
    apply le_of_tendsto ht2
    filter_upwards [eventually_ge_atTop I] with t hIt
    rw [← Finset.sum_sdiff hIt, add_sub_cancel_right]
    refine (norm_sum_le _ _).trans ?_
    have hle : ∀ h ∈ t \ I, ‖f h‖ ≤ ‖s5SqCoeff Δ h‖ := by
      intro h _
      rw [hf]; simp only
      rw [norm_mul, s5_07_norm_eC', mul_one]
    refine (Finset.sum_le_sum hle).trans ?_
    apply s5_07b_tail Δ hΔ₀ H hH
    intro h hh
    rw [Finset.mem_sdiff, hI, Finset.mem_Icc, not_and_or, not_le, not_le] at hh
    rcases hh.2 with h1 | h1
    · exact lt_abs.mpr (Or.inr (by omega))
    · exact lt_abs.mpr (Or.inl h1)
  have hpos : 0 ≤ 1 / (H * Δ) := by
    have : (0 : ℝ) < H := by exact_mod_cast hH
    positivity
  have hsplit : (-1 : ℂ) ^ ⌊y⌋ - ∑ h ∈ I, f h
      = ((-1 : ℂ) ^ ⌊y⌋ - s5AvgWave Δ y) + (s5AvgWave Δ y - ∑ h ∈ I, f h) := by ring
  have hw : ‖(-1 : ℂ) ^ ⌊y⌋‖ = 1 := by rw [norm_zpow, norm_neg, norm_one, one_zpow]
  refine ⟨?_, fun h1 h2 => ?_⟩
  · rw [hsplit]
    refine (norm_add_le _ _).trans ?_
    have := norm_sub_le ((-1 : ℂ) ^ ⌊y⌋) (s5AvgWave Δ y)
    have := s5_07b_avg_norm_le Δ y hΔ₀
    linarith
  · rw [← s5_07b_avg_eq_wave Δ y hΔ₀ h1 h2]
    exact htail

/-- Twin check: the assembly has the type of the leaf being split. -/
example : type_of% @leaf_s5_07_square_wave_truncation :=
  @leaf_s5_07_square_wave_truncation_of_leaves

end LeanLab.ExceptionalSet.U1539
