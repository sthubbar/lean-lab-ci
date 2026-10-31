/-
P0022, L. Kaniecki 1995, inequality (23), p. 372, with the sets A, B, C of p. 371.
AI-written Lean code, Claude, 2026-10-18, run 20261018T1903Z-4829, unit U-0967.
Checked only by the Lean kernel. Binary Goldbach is OPEN. Nothing here proves it.

The paper's measure argument: if `[x, x+h]` holds no sum of two odd primes, the set
`A` of `y ∈ [0, x]` with no odd prime in the window after `y` has measure at least `x/2`,
because `B` and its reflection `C` are disjoint; on `A` the theta difference vanishes,
so the integrand of `J` is `y^{1-2σ}/T²`, which gives (23).

Deviation from the paper, harmless: the windows are `(y, y + h/2]` instead of the open
`(y, y + h/2)`, so that `y = x` needs no separate null-set step. The disjointness of
`B` and `C` still forces a sum `p₁ + p₂ ∈ (x, x + h]`.
-/
import LeanLab.Kaniecki1995.Statements

namespace LeanLab.Kaniecki1995
open Real MeasureTheory Set

/-- `θ` is constant across an interval holding no prime. -/
theorem theta_eq_of_no_prime {y z : ℝ} (hy : 0 ≤ y) (hyz : y ≤ z)
    (hp : ∀ p : ℕ, p.Prime → y < p → (p : ℝ) ≤ z → False) :
    Chebyshev.theta z = Chebyshev.theta y := by
  unfold Chebyshev.theta
  congr 1
  ext p
  simp only [Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨h0, hpz⟩, hpr⟩
    refine ⟨⟨h0, ?_⟩, hpr⟩
    by_contra hlt
    push_neg at hlt
    have h1 : y < p := (Nat.floor_lt hy).1 hlt
    have hz0 : 0 ≤ z := hy.trans hyz
    have h2 : (p : ℝ) ≤ z := (Nat.le_floor_iff hz0).1 hpz
    exact hp p hpr h1 h2
  · rintro ⟨⟨h0, hpy⟩, hpr⟩
    exact ⟨⟨h0, hpy.trans (Nat.floor_le_floor hyz)⟩, hpr⟩

/-- The union of the windows: `y ∈ oddWin h` iff some odd prime lies in `(y, y + h/2]`. -/
def oddWin (h : ℝ) : Set ℝ := ⋃ p : ℕ, ⋃ (_ : p.Prime ∧ Odd p), Ico ((p : ℝ) - h / 2) p

theorem mem_oddWin {h y : ℝ} :
    y ∈ oddWin h ↔ ∃ p : ℕ, p.Prime ∧ Odd p ∧ (p : ℝ) - h / 2 ≤ y ∧ y < p := by
  simp only [oddWin, mem_iUnion, mem_Ico, exists_prop]
  constructor
  · rintro ⟨p, ⟨h1, h2⟩, h3, h4⟩; exact ⟨p, h1, h2, h3, h4⟩
  · rintro ⟨p, h1, h2, h3, h4⟩; exact ⟨p, ⟨h1, h2⟩, h3, h4⟩

theorem measurableSet_oddWin (h : ℝ) : MeasurableSet (oddWin h) :=
  MeasurableSet.iUnion fun _ => MeasurableSet.iUnion fun _ => measurableSet_Ico

/-- p. 371: `μ(A) ≥ x/2`. -/
theorem measure_A_ge {x h : ℝ} (hx : 0 ≤ x) (hno : ¬ HasOddPairSumIn x h) :
    ENNReal.ofReal (x / 2) ≤ volume (Icc 0 x \ oddWin h) := by
  set S := Icc (0 : ℝ) x
  set U := oddWin h
  set B := S ∩ U
  set C := (fun y => x - y) ⁻¹' B
  have hUm : MeasurableSet U := measurableSet_oddWin h
  have hBm : MeasurableSet B := measurableSet_Icc.inter hUm
  have hCm : MeasurableSet C := hBm.preimage (measurable_const.sub measurable_id)
  have hCB : volume C = volume B :=
    (volume.measurePreserving_sub_left x).measure_preimage hBm.nullMeasurableSet
  have hdisj : Disjoint B C := by
    rw [Set.disjoint_left]
    intro y hyB hyC
    obtain ⟨⟨hy0, hyx⟩, hyU⟩ := hyB
    obtain ⟨_, hyU'⟩ := hyC
    obtain ⟨p, hp, hpo, hp1, hp2⟩ := mem_oddWin.1 hyU
    obtain ⟨q, hq, hqo, hq1, hq2⟩ := mem_oddWin.1 hyU'
    apply hno
    refine ⟨p, q, hp, hq, hpo, hqo, ?_, ?_⟩ <;> push_cast <;> linarith
  have hCsub : C ⊆ S := by
    intro y hy
    obtain ⟨⟨h0, h1⟩, _⟩ := hy
    exact ⟨by linarith, by linarith⟩
  have hBC : volume B + volume C ≤ ENNReal.ofReal x := by
    rw [← measure_union hdisj hCm]
    calc volume (B ∪ C) ≤ volume S := measure_mono (union_subset inter_subset_left hCsub)
      _ = ENNReal.ofReal x := by simp [S, Real.volume_Icc]
  have hAB : volume (S \ U) + volume B = ENNReal.ofReal x := by
    rw [← measure_union (by
        rw [Set.disjoint_left]; intro y h1 h2; exact h1.2 h2.2) hBm, Set.sdiff_union_inter]
    simp [S, Real.volume_Icc]
  have hBfin : volume B ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (le_trans le_self_add hBC)
  have hAfin : volume (S \ U) ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (le_trans le_self_add hAB.le)
  rw [ENNReal.ofReal_le_iff_le_toReal hAfin]
  have e1 := congrArg ENNReal.toReal hAB
  rw [ENNReal.toReal_add hAfin hBfin, ENNReal.toReal_ofReal hx] at e1
  have e2 := ENNReal.toReal_mono ENNReal.ofReal_ne_top hBC
  rw [hCB, ENNReal.toReal_add hBfin hBfin, ENNReal.toReal_ofReal hx] at e2
  linarith

/-- On `A` the integrand of `J` is at least `x^{1-2σ}/T²`. -/
theorem integrand_ge {x h T σ y : ℝ} (hx : 0 < x) (hT : 0 < T) (hTh : T = 2 * x / h)
    (hh : 7 ≤ h) (hσ : 1 / 2 ≤ σ) (hy : y ∈ Icc 0 x \ oddWin h) :
    x ^ (1 - 2 * σ) / T ^ 2 ≤ thetaIntegrand T σ y ∧ 2 < y := by
  obtain ⟨⟨hy0, hyx⟩, hyU⟩ := hy
  have hy2 : 2 < y := by
    by_contra hle
    push_neg at hle
    exact hyU (mem_oddWin.2 ⟨3, Nat.prime_three, by decide, by push_cast; linarith,
      by push_cast; linarith⟩)
  refine ⟨?_, hy2⟩
  have hypos : 0 < y := by linarith
  have hh0 : 0 < h := by linarith
  have hyT : y / T ≤ h / 2 := by
    rw [hTh, div_div_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  have hth : Chebyshev.theta (y + y / T) = Chebyshev.theta y := by
    have hyT0 : 0 ≤ y / T := by positivity
    apply theta_eq_of_no_prime hy0 (by linarith)
    intro p hp h1 h2
    have hodd : Odd p := hp.odd_of_ne_two (by
      rintro rfl; push_cast at h1; linarith)
    exact hyU (mem_oddWin.2 ⟨p, hp, hodd, by linarith, h1⟩)
  have key : thetaIntegrand T σ y = y ^ (1 - 2 * σ) / T ^ 2 := by
    unfold thetaIntegrand
    rw [hth, show Chebyshev.theta y - Chebyshev.theta y - y / T = -(y / T) by ring, div_pow,
      neg_sq, div_pow, ← Real.rpow_natCast (y ^ (1 / 2 + σ)), ← Real.rpow_mul hypos.le]
    rw [show (1 / 2 + σ) * ((2 : ℕ) : ℝ) = 2 - (1 - 2 * σ) by push_cast; ring,
      Real.rpow_sub hypos, Real.rpow_two]
    field_simp
  rw [key]
  apply div_le_div_of_nonneg_right _ (by positivity)
  exact Real.rpow_le_rpow_of_nonpos hypos hyx (by linarith)

/-- Inequality (23), p. 372, PROVED from the definition of `J`. -/
theorem eq23 : Eq23 := by
  intro x h a c h7 hhx ha1 ha2 hc1 hc2 hno
  set T := 2 * x / h with hTdef
  set σ := sig a c T with hσdef
  have hh0 : 0 < h := by linarith
  have he : 0 < Real.exp (-12) := Real.exp_pos _
  have hx0 : 0 < x := by
    by_contra hle; push_neg at hle; nlinarith
  have hT12 : Real.exp 12 ≤ T := by
    rw [hTdef, le_div_iff₀ hh0]
    have : Real.exp 12 * Real.exp (-12) = 1 := by rw [← Real.exp_add]; norm_num
    nlinarith [Real.exp_pos 12]
  have hT1 : 1 < T := lt_of_lt_of_le (by simpa using Real.one_lt_exp_iff.2 (by norm_num : (0:ℝ) < 12)) hT12
  have hT0 : 0 < T := by linarith
  have hlog : 0 < Real.log T := Real.log_pos hT1
  have hσ : 1 / 2 ≤ σ := by
    rw [hσdef, sig]
    have : 0 ≤ a * c / Real.log T := div_nonneg (by nlinarith) hlog.le
    linarith
  set A := Icc (0 : ℝ) x \ oddWin h
  have hAm : MeasurableSet A := measurableSet_Icc.diff (measurableSet_oddWin h)
  have hA := measure_A_ge hx0.le hno
  have hc0 : 0 ≤ x ^ (1 - 2 * σ) / T ^ 2 := by positivity
  have hsplit : x ^ (2 * (1 - σ)) / (2 * T ^ 2) = x ^ (1 - 2 * σ) / T ^ 2 * (x / 2) := by
    rw [show 2 * (1 - σ) = (1 - 2 * σ) + 1 by ring, Real.rpow_add_one hx0.ne']
    field_simp
  calc ENNReal.ofReal (x ^ (2 * (1 - σ)) / (2 * T ^ 2))
      = ENNReal.ofReal (x ^ (1 - 2 * σ) / T ^ 2) * ENNReal.ofReal (x / 2) := by
        rw [hsplit, ENNReal.ofReal_mul hc0]
    _ ≤ ENNReal.ofReal (x ^ (1 - 2 * σ) / T ^ 2) * volume A := by gcongr
    _ = ∫⁻ _ in A, ENNReal.ofReal (x ^ (1 - 2 * σ) / T ^ 2) := (setLIntegral_const _ _).symm
    _ ≤ ∫⁻ y in A, ENNReal.ofReal (thetaIntegrand T σ y) := by
        apply setLIntegral_mono' hAm
        intro y hy
        exact ENNReal.ofReal_le_ofReal (integrand_ge hx0 hT0 rfl h7 hσ hy).1
    _ ≤ ∫⁻ y in Ioi (2 : ℝ), ENNReal.ofReal (thetaIntegrand T σ y) := by
        apply lintegral_mono_set
        intro y hy
        exact (integrand_ge hx0 hT0 rfl h7 hσ hy).2
    _ = JInt T σ := rfl

end LeanLab.Kaniecki1995
