/-
Unit Linnik1951/SPLIT-outer_tail_pointwise487.
Split of outer_tail_pointwise487 of Decomp487b into the absolute convergence of the
coefficient integral, the cut of the full contour at the moving radius, the norm estimate
on the cut off frequencies, the exponential mass of that remainder and its scalar absorption.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Repair493ContourData
import LeanLab.Linnik1951.Repair493PositiveKernel
import LeanLab.Linnik1951.SPLIT_outer_kernel_integrable442

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. Absolute convergence step. For large N the signed coefficient integral along the
line converges absolutely for every alpha, because the line bound is logarithmic in the
frequency and the Gamma factor decays exponentially. This is the finiteness estimate that
lets the full contour be cut. No inequality between the contour and its truncation occurs. -/
theorem outer_tail_integrable487 :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ B0 : ℝ, 0 < B0 → ∀ M : ℝ → ℂ,
      LineBound1622 N B0 M → ∀ α : ℝ,
        Integrable (fun t : ℝ => mellinKernel442 N α t * M t) := by
  refine ⟨2, ?_⟩
  intro N hN B0 hB0 M hM α
  have hN3 : 3 ≤ N := by omega
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  let z : ℂ := ((1 / (N : ℝ) : ℝ) : ℂ) + ((2 * Real.pi * α : ℝ) : ℂ) * Complex.I
  have hzre : z.re = 1 / (N : ℝ) := by simp [z]
  have harg : |z.arg| < Real.pi / 2 :=
    Complex.abs_arg_lt_pi_div_two_iff.mpr (Or.inl (by rw [hzre]; positivity))
  let δ : ℝ := Real.pi / 2 - |z.arg|
  have hδ : 0 < δ := by dsimp [δ]; linarith
  let A : ℝ := Real.exp 1 * Real.sqrt N * Real.sqrt (2 * Real.pi)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  obtain ⟨C, hC, hlog⟩ := log_weight_cubic442 N hN3
  have hK (t : ℝ) : ‖mellinKernel442 N α t‖ ≤
      A * (3 + |t|) * Real.exp (-(δ * |t|)) := by
    have hp := mellin_power_factor487 N (by omega) z hzre t
    have hg := gamma_mellin_line442 N hN3 t
    change ‖z ^ (-(mellinLine1622 N t)) * Complex.Gamma (mellinLine1622 N t)‖ ≤ _
    rw [norm_mul]
    calc
      _ ≤ (Real.exp 1 * Real.sqrt N * Real.exp (|t| * |z.arg|)) *
          (Real.sqrt (2 * Real.pi) * (3 + |t|) * Real.exp (-(Real.pi * |t| / 2))) :=
        mul_le_mul hp hg (norm_nonneg _) (by positivity)
      _ = _ := by
        rw [show -(δ * |t|) = |t| * |z.arg| + -(Real.pi * |t| / 2) by dsimp [δ]; ring,
          Real.exp_add]
        dsimp [A]
        ring
  have hk (k : ℕ) : IntegrableOn (fun t : ℝ => t ^ k * Real.exp (-(δ * t))) (Set.Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := (k : ℝ)) (p := 1) (b := δ)
        (by linarith [Nat.cast_nonneg (α := ℝ) k]) (by norm_num) hδ
  have hp : IntegrableOn (fun t : ℝ => Real.exp (-(δ * |t|)) * (1 + |t|) ^ 4) (Set.Ioi 0) := by
    apply ((((hk 4).add ((hk 3).const_mul 4)).add ((hk 2).const_mul 6)).add
      ((hk 1).const_mul 4)).add (hk 0) |>.congr_fun ?_ measurableSet_Ioi
    intro t ht
    dsimp only [Pi.add_apply]
    rw [abs_of_pos (show 0 < t from ht)]
    ring
  have hc : IntegrableOn (fun t : ℝ => Real.exp (-(δ * |t|)) * (1 + |t|) ^ 4) (Set.Ici 0) :=
    (integrableOn_Ici_iff_integrableOn_Ioi).mpr hp
  have hn : IntegrableOn (fun t : ℝ => Real.exp (-(δ * |t|)) * (1 + |t|) ^ 4) (Set.Iic 0) := by
    have hn := (show IntegrableOn (fun t : ℝ => Real.exp (-(δ * |t|)) * (1 + |t|) ^ 4)
      (Set.Ici (-0)) from by simpa using hc).comp_neg_Iic
    simpa only [abs_neg] using hn
  have hQ : Integrable (fun t : ℝ => Real.exp (-(δ * |t|)) * (1 + |t|) ^ 4) := by
    simpa only [Set.Iic_union_Ioi, integrableOn_univ] using hn.union hp
  have hpair : Continuous (fun t : ℝ => (α, t)) :=
    continuous_const.prodMk continuous_id
  have hcont : Continuous (fun t : ℝ => mellinKernel442 N α t * M t) := by
    simpa only [Function.comp_def] using
      (continuous_mellin_integrand487 N hN3 M hM.1).comp hpair
  apply (hQ.const_mul (3 * A * B0 * C)).mono' hcont.aestronglyMeasurable
  apply Filter.Eventually.of_forall
  intro t
  calc
    ‖mellinKernel442 N α t * M t‖ = ‖mellinKernel442 N α t‖ * ‖M t‖ := norm_mul _ _
    _ ≤ (A * (3 + |t|) * Real.exp (-(δ * |t|))) *
        (B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) :=
      mul_le_mul (hK t) (hM.2 t) (norm_nonneg _) (by positivity)
    _ ≤ (A * (3 + |t|) * Real.exp (-(δ * |t|))) *
        (B0 * (C * (1 + |t|) ^ 3)) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hlog t) hB0.le) (by positivity)
    _ ≤ (A * (3 * (1 + |t|)) * Real.exp (-(δ * |t|))) *
        (B0 * (C * (1 + |t|) ^ 3)) := by
      gcongr
      linarith [abs_nonneg t]
    _ = (3 * A * B0 * C) * (Real.exp (-(δ * |t|)) * (1 + |t|) ^ 4) := by ring

/-- LEAF. Cut identity step. The full signed contour minus its truncation at the radius
N over R times log cubed N is exactly the one over two pi times the two frequency tails,
the part above the radius and the part below minus the radius. Only the additivity of the
integral over the three pieces is used; no size estimate occurs. -/
theorem outer_tail_cut_identity487 (N : ℕ) (R α : ℝ) (M : ℝ → ℂ)
    (hT : 0 ≤ (N : ℝ) / R * Real.log N ^ 3)
    (hI : Integrable (fun t : ℝ => mellinKernel442 N α t * M t)) :
    mellinU1622 N M α - truncatedMellin487 N R M α =
      ((1 / (2 * Real.pi) : ℝ) : ℂ) *
        ∫ t in (Set.Ici ((N : ℝ) / R * Real.log N ^ 3) ∪
          Set.Iic (-((N : ℝ) / R * Real.log N ^ 3))),
          mellinKernel442 N α t * M t := by
  have horder : -((N : ℝ) / R * Real.log N ^ 3) ≤ (N : ℝ) / R * Real.log N ^ 3 := by linarith
  unfold mellinU1622 truncatedMellin487
  change _ * (∫ t : ℝ, mellinKernel442 N α t * M t) - _ = _
  rw [← mul_sub, intervalIntegral.integral_of_le horder, integral_Ioc_eq_integral_Ioo]
  have hset : (Set.Ioo (-((N : ℝ) / R * Real.log N ^ 3))
      ((N : ℝ) / R * Real.log N ^ 3))ᶜ =
      Set.Ici ((N : ℝ) / R * Real.log N ^ 3) ∪
        Set.Iic (-((N : ℝ) / R * Real.log N ^ 3)) := by
    ext t
    simp only [Set.mem_compl_iff, Set.mem_Ioo, Set.mem_union, Set.mem_Ici,
      Set.mem_Iic, not_and_or, not_lt]
    tauto
  rw [← setIntegral_compl measurableSet_Ioo hI, hset]

/-- LEAF. Triangle inequality step on the cut off frequencies. The norm of the two tail
integrals is at most the line bound constant B0 times the absolute kernel mass carrying the
logarithmic weight of the coefficient bound. No decay and no absorption occurs here. -/
theorem outer_tail_norm_estimate487 (N : ℕ) (R α B0 : ℝ) (M : ℝ → ℂ)
    (hB0 : 0 ≤ B0) (hM : LineBound1622 N B0 M) :
    ‖∫ t in (Set.Ici ((N : ℝ) / R * Real.log N ^ 3) ∪
        Set.Iic (-((N : ℝ) / R * Real.log N ^ 3))),
        mellinKernel442 N α t * M t‖ ≤
      B0 * ∫ t in (Set.Ici ((N : ℝ) / R * Real.log N ^ 3) ∪
        Set.Iic (-((N : ℝ) / R * Real.log N ^ 3))),
        ‖mellinKernel442 N α t‖ * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 := by
  let S : Set ℝ := Set.Ici ((N : ℝ) / R * Real.log N ^ 3) ∪
    Set.Iic (-((N : ℝ) / R * Real.log N ^ 3))
  change ‖∫ t in S, mellinKernel442 N α t * M t‖ ≤
    B0 * ∫ t in S, ‖mellinKernel442 N α t‖ * Real.log ((N : ℝ) * (|t| + 2)) ^ 3
  by_cases hzero : N = 0
  · subst N
    have hMzero (t : ℝ) : M t = 0 := by
      apply norm_eq_zero.mp
      exact le_antisymm (by simpa using hM.2 t) (norm_nonneg _)
    simp [hMzero]
  · have hN : 1 ≤ N := by omega
    have hw := weighted_kernel_integrable_positive493 N hN α
    have hpair : Continuous (fun t : ℝ => (α, t)) := continuous_const.prodMk continuous_id
    have hc : Continuous (fun t : ℝ => mellinKernel442 N α t * M t) := by
      simpa only [Function.comp_def] using
        (continuous_mellin_integrand_positive493 N hN M hM.1).comp hpair
    have hbound (t : ℝ) : ‖mellinKernel442 N α t * M t‖ ≤
        B0 * (‖mellinKernel442 N α t‖ * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) := by
      rw [norm_mul]
      calc
        _ ≤ ‖mellinKernel442 N α t‖ * (B0 * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) :=
          mul_le_mul_of_nonneg_left (hM.2 t) (norm_nonneg _)
        _ = _ := by ring
    have hi : Integrable (fun t : ℝ => mellinKernel442 N α t * M t) :=
      (hw.const_mul B0).mono' hc.aestronglyMeasurable (Filter.Eventually.of_forall hbound)
    calc
      _ ≤ ∫ t in S, ‖mellinKernel442 N α t * M t‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ t in S, B0 * (‖mellinKernel442 N α t‖ * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) :=
        integral_mono hi.norm.integrableOn (hw.const_mul B0).integrableOn hbound
      _ = _ := by rw [integral_const_mul]

set_option maxHeartbeats 800000 in
/-- LEAF. Exponential mass step on the cut off frequencies. On the outer alpha interval the
scaled kernel decay of the line at radius R gives the two tails the mass a fixed constant
times square root N times N over R cubed times log N to the sixth times the exponential of
minus log N cubed over twenty. This is the quantitative input on the moving complement. -/
theorem outer_tail_complement_mass487 :
    ∃ K : ℝ, 0 < K ∧ ∀ N : ℕ, 8 ≤ N → ∀ R α : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) → α ∈ Set.Icc (4 / (N : ℝ)) (1 / R) →
        ∫ t in (Set.Ici ((N : ℝ) / R * Real.log N ^ 3) ∪
          Set.Iic (-((N : ℝ) / R * Real.log N ^ 3))),
          ‖mellinKernel442 N α t‖ * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤
          K * Real.sqrt N * ((N : ℝ) / R) ^ 3 * Real.log N ^ 6 *
            Real.exp (-(Real.log N ^ 3 / 20)) := by
  let K : ℝ := 256 * Real.exp 1 * Real.sqrt (2 * Real.pi) * 48 * 20 ^ 5
  refine ⟨K, by dsimp [K]; positivity, ?_⟩
  intro N hN R α hR hpow hα
  have hNr : (8 : ℝ) ≤ N := by exact_mod_cast hN
  have hNp : (0 : ℝ) < N := by linarith
  have hRp : 0 < R := by linarith
  have hRN : R ≤ (N : ℝ) := by
    have hi := hα.1.trans hα.2
    rw [div_le_div_iff₀ hNp hRp] at hi
    linarith
  let L : ℝ := (N : ℝ) / R
  let T : ℝ := L * Real.log N ^ 3
  let c : ℝ := R / (10 * (N : ℝ))
  let A : ℝ := Real.exp 1 * Real.sqrt N * Real.sqrt (2 * Real.pi)
  let B : ℝ := 256 * A * Real.log N ^ 3 / L ^ 3
  let g : ℝ → ℝ := fun t => |t| ^ 4 * Real.exp (-(c * |t|))
  have hL : 1 ≤ L := (one_le_div hRp).mpr hRN
  have hLp : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hLN : L ≤ (N : ℝ) := div_le_self hNp.le hR
  have hlog : 1 ≤ Real.log N := by
    have he : Real.exp 1 ≤ (N : ℝ) := le_trans Real.exp_one_lt_three.le (by linarith)
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) he
  have hlog0 : 0 ≤ Real.log N := by linarith
  have hT : 1 ≤ T := one_le_mul_of_one_le_of_one_le hL (one_le_pow₀ hlog)
  have hTL : L ≤ T := le_mul_of_one_le_right hLp.le (one_le_pow₀ hlog)
  have hc : 0 < c := by dsimp [c]; positivity
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hlogbound (x : ℝ) (hx : T ≤ x) :
      Real.log ((N : ℝ) * (x + 2)) ≤ 4 * Real.log N * (x / L) := by
    have hx1 : 1 ≤ x := hT.trans hx
    have hux : 1 ≤ x / L := (one_le_div hLp).mpr (hTL.trans hx)
    have hp : 0 < x + 2 := by linarith
    have hup : 0 < x / L + 2 := by linarith
    have heq : L * (x / L) = x := mul_div_cancel₀ x hLp.ne'
    have hm : x + 2 ≤ L * (x / L + 2) := by nlinarith
    have hlogL : Real.log L ≤ Real.log N := Real.log_le_log hLp hLN
    have hh := Real.log_le_sub_one_of_pos hup
    calc
      _ ≤ Real.log ((N : ℝ) * (L * (x / L + 2))) :=
        Real.log_le_log (mul_pos hNp hp) (mul_le_mul_of_nonneg_left hm hNp.le)
      _ = Real.log N + Real.log L + Real.log (x / L + 2) := by
        rw [Real.log_mul hNp.ne' (mul_pos hLp hup).ne', Real.log_mul hLp.ne' hup.ne']
        ring
      _ ≤ 2 * Real.log N + (x / L + 1) := by linarith
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hlog) (sub_nonneg.mpr hux)]
  have hpoint (t : ℝ) (ht : t ∈ Set.Ici T ∪ Set.Iic (-T)) :
      ‖mellinKernel442 N α t‖ * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 ≤ B * g t := by
    have habs : T ≤ |t| := by
      rcases ht with ht | ht
      · exact ht.trans (le_abs_self t)
      · have hh := le_abs_self (-t)
        rw [abs_neg] at hh
        exact le_trans (by linarith [show t ≤ -T from ht]) hh
    have hx1 : 1 ≤ |t| := hT.trans habs
    have hweight : 0 ≤ Real.log ((N : ℝ) * (|t| + 2)) :=
      Real.log_nonneg (by nlinarith [abs_nonneg t])
    have hk := outer_kernel_scaled_decay487 N (by omega) R α t hRp hRN
      (le_trans (by positivity : 0 ≤ 4 / (N : ℝ)) hα.1) hα.2
    have hp := hlogbound |t| habs
    calc
      _ ≤ (A * (3 + |t|) * Real.exp (-(c * |t|))) *
          (4 * Real.log N * (|t| / L)) ^ 3 := by
        apply mul_le_mul
        · simpa only [A, c, neg_mul] using hk
        · exact pow_le_pow_left₀ hweight hp 3
        · positivity
        · positivity
      _ ≤ (A * (4 * |t|) * Real.exp (-(c * |t|))) *
          (4 * Real.log N * (|t| / L)) ^ 3 := by
        gcongr
        linarith
      _ = B * g t := by dsimp [B, g]; field_simp; ring
  have hbase : IntegrableOn (fun x : ℝ => x ^ 4 * Real.exp (-(c * x))) (Set.Ioi 0) := by
    simpa only [Real.rpow_natCast, Real.rpow_one, neg_mul] using
      integrableOn_rpow_mul_exp_neg_mul_rpow
        (s := ((4 : ℕ) : ℝ)) (p := 1) (b := c) (by norm_num) (by norm_num) hc
  have hpos : IntegrableOn g (Set.Ici T) := by
    apply ((integrableOn_Ici_iff_integrableOn_Ioi).mpr hbase).mono_set
      (Set.Ici_subset_Ici.mpr (by linarith : (0 : ℝ) ≤ T)) |>.congr_fun ?_ measurableSet_Ici
    intro t ht
    simp only [g, abs_of_nonneg (le_trans (by linarith : (0 : ℝ) ≤ T) ht)]
  have hneg : IntegrableOn g (Set.Iic (-T)) := by
    have hi := (show IntegrableOn g (Set.Ici (-(-T))) from by simpa only [neg_neg] using hpos).comp_neg_Iic
    simpa only [neg_neg, g, abs_neg] using hi
  have hunion := hpos.union hneg
  have hwi := weighted_kernel_integrable_positive493 N (by omega) α
  have hmass : (∫ t in Set.Ici T ∪ Set.Iic (-T),
      ‖mellinKernel442 N α t‖ * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ≤
      B * (2 * ((24 / (c / 2) ^ 5) * Real.exp (-(c / 2 * T)))) := by
    calc
      _ ≤ ∫ t in Set.Ici T ∪ Set.Iic (-T), B * g t :=
        setIntegral_mono_on hwi.integrableOn (hunion.const_mul B)
          (measurableSet_Ici.union measurableSet_Iic) hpoint
      _ = B * ∫ t in Set.Ici T ∪ Set.Iic (-T), g t := integral_const_mul _ _
      _ = B * (2 * ∫ t in Set.Ioi T, t ^ 4 * Real.exp (-(c * t))) := by
        have hd : Disjoint (Set.Ici T) (Set.Iic (-T)) := by
          apply Set.disjoint_left.mpr
          intro t ht hn
          have hp : T ≤ t := ht
          have hm : t ≤ -T := hn
          linarith
        rw [setIntegral_union hd measurableSet_Iic hpos hneg, integral_Ici_eq_integral_Ioi]
        have hnegative : (∫ t in Set.Iic (-T), g t) = ∫ t in Set.Ioi T, g t := by
          rw [← integral_comp_neg_Ioi T g]
          simp only [g, abs_neg]
        rw [hnegative]
        have hpositive : (∫ t in Set.Ioi T, g t) =
            ∫ t in Set.Ioi T, t ^ 4 * Real.exp (-(c * t)) := by
          apply setIntegral_congr_fun measurableSet_Ioi
          intro t ht
          simp only [g, abs_of_pos (lt_of_le_of_lt (by linarith : (0 : ℝ) ≤ T) ht)]
        rw [hpositive]
        ring
      _ ≤ _ := by
        apply mul_le_mul_of_nonneg_left _ hB
        exact mul_le_mul_of_nonneg_left (quartic_exponential_tail487 c T hc (by linarith)) (by norm_num)
  have heq : c / 2 * T = Real.log N ^ 3 / 20 := by
    dsimp [c, T, L]
    field_simp
    <;> ring
  change (∫ t in Set.Ici T ∪ Set.Iic (-T),
    ‖mellinKernel442 N α t‖ * Real.log ((N : ℝ) * (|t| + 2)) ^ 3) ≤ _
  calc
    _ ≤ B * (2 * ((24 / (c / 2) ^ 5) * Real.exp (-(c / 2 * T)))) := hmass
    _ = K * Real.sqrt N * L ^ 2 * Real.log N ^ 3 *
        Real.exp (-(Real.log N ^ 3 / 20)) := by
      rw [heq]
      dsimp [B, A, K, c, L]
      field_simp
      <;> ring
    _ ≤ _ := by
      have hLpow : L ^ 2 ≤ L ^ 3 := by nlinarith [sq_nonneg L]
      have hlpow : Real.log N ^ 3 ≤ Real.log N ^ 6 := by
        have hh : 1 ≤ Real.log N ^ 3 := one_le_pow₀ hlog
        nlinarith [sq_nonneg (Real.log N ^ 3 - 1)]
      change _ ≤ K * Real.sqrt N * L ^ 3 * Real.log N ^ 6 * _
      gcongr

/-- LEAF. Scalar absorption step. For every positive constant the displayed product, which is
a fixed power of N times log N to the sixth times the exponential of minus log N cubed over
twenty, is at most one once N is large, uniformly in the radius at least one. -/
theorem outer_tail_absorption487 (C : ℝ) (hC : 0 < C) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ R : ℝ, 1 ≤ R →
      R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        C * Real.sqrt N * ((N : ℝ) / R) ^ 3 * Real.log N ^ 6 *
          Real.exp (-(Real.log N ^ 3 / 20)) ≤ 1 := by
  obtain ⟨N0, hN0⟩ := outer_tail_polynomial_absorption487 C hC
  refine ⟨max 1 N0, ?_⟩
  intro N hN R hR hRN
  have h1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hs : Real.sqrt N ≤ (N : ℝ) := Real.sqrt_le_self_iff.mpr (Or.inr h1)
  have hd : (N : ℝ) / R ≤ (N : ℝ) := div_le_self (Nat.cast_nonneg N) hR
  have hl : Real.log N ≤ (N : ℝ) := Real.log_le_self (Nat.cast_nonneg N)
  have hl0 : 0 ≤ Real.log N := Real.log_nonneg h1
  calc
    _ ≤ C * (N : ℝ) * (N : ℝ) ^ 3 * (N : ℝ) ^ 6 * Real.exp (-(Real.log N ^ 3 / 20)) := by
      gcongr
    _ = C * (N : ℝ) ^ 10 * Real.exp (-(Real.log N ^ 3 / 20)) := by ring
    _ ≤ 1 := hN0 N (lt_of_le_of_lt (le_max_right _ _) hN)

/-- The pointwise truncation error of the signed contour at the radius N over R times log
cubed N is eventually at most one on the outer alpha interval, uniformly in the radius and in
every coefficient satisfying the line bound. Proved from the absolute convergence, the cut
identity, the triangle inequality on the cut off frequencies, the exponential mass of that
remainder and its scalar absorption; the two constants are multiplied. -/
theorem outer_tail_pointwise487_split (B0 : ℝ) (hB0 : 0 < B0) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        ∀ M : ℝ → ℂ, LineBound1622 N B0 M →
          ∀ α ∈ Set.Icc (4 / (N : ℝ)) (1 / R),
            ‖mellinU1622 N M α - truncatedMellin487 N R M α‖ ≤ 1 := by
  obtain ⟨K, hKpos, hmass⟩ := outer_tail_complement_mass487
  obtain ⟨Ni, hi⟩ := outer_tail_integrable487
  obtain ⟨Na, ha⟩ := outer_tail_absorption487 ((1 / (2 * Real.pi)) * B0 * K)
    (by positivity)
  refine ⟨max 8 (max Ni Na), ?_⟩
  intro N hN R hR1 hR M hM α hα
  have hN8 : 8 ≤ N := le_of_lt (lt_of_le_of_lt (le_max_left _ _) hN)
  have hNi : Ni < N := lt_of_le_of_lt
    (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hNa : Na < N := lt_of_le_of_lt
    (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hRp : (0 : ℝ) < R := by linarith
  have hl0 : (0 : ℝ) ≤ Real.log N :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))
  have hT0 : (0 : ℝ) ≤ (N : ℝ) / R * Real.log N ^ 3 :=
    mul_nonneg (by positivity) (pow_nonneg hl0 3)
  have hα0 : (0 : ℝ) ≤ α :=
    le_trans (by positivity : (0 : ℝ) ≤ 4 / (N : ℝ)) hα.1
  have hI := hi N hNi B0 hB0 M hM α
  have hcut := outer_tail_cut_identity487 N R α M hT0 hI
  have hnorm := outer_tail_norm_estimate487 N R α B0 M hB0.le hM
  have hm := hmass N hN8 R α hR1 hR hα
  set T : ℝ := (N : ℝ) / R * Real.log N ^ 3 with hT
  set I : ℝ := ∫ t in (Set.Ici T ∪ Set.Iic (-T)),
    ‖mellinKernel442 N α t‖ * Real.log ((N : ℝ) * (|t| + 2)) ^ 3 with hIdef
  change ‖∫ t in (Set.Ici T ∪ Set.Iic (-T)), mellinKernel442 N α t * M t‖ ≤ B0 * I at hnorm
  change I ≤ K * Real.sqrt N * ((N : ℝ) / R) ^ 3 * Real.log N ^ 6 *
    Real.exp (-(Real.log N ^ 3 / 20)) at hm
  have hstep : ‖mellinU1622 N M α - truncatedMellin487 N R M α‖ ≤
      (1 / (2 * Real.pi)) * B0 * I := by
    calc ‖mellinU1622 N M α - truncatedMellin487 N R M α‖
        = ‖((1 / (2 * Real.pi) : ℝ) : ℂ) *
            ∫ t in (Set.Ici T ∪ Set.Iic (-T)), mellinKernel442 N α t * M t‖ := by
          rw [hcut]
      _ = (1 / (2 * Real.pi)) *
            ‖∫ t in (Set.Ici T ∪ Set.Iic (-T)), mellinKernel442 N α t * M t‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_pos (by positivity)]
      _ ≤ (1 / (2 * Real.pi)) * (B0 * I) :=
          mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ = (1 / (2 * Real.pi)) * B0 * I := by ring
  have hstep2 : (1 / (2 * Real.pi)) * B0 * I ≤
      (1 / (2 * Real.pi)) * B0 *
        (K * Real.sqrt N * ((N : ℝ) / R) ^ 3 * Real.log N ^ 6 *
          Real.exp (-(Real.log N ^ 3 / 20))) :=
    mul_le_mul_of_nonneg_left hm (by positivity)
  have hflat : (1 / (2 * Real.pi)) * B0 *
        (K * Real.sqrt N * ((N : ℝ) / R) ^ 3 * Real.log N ^ 6 *
          Real.exp (-(Real.log N ^ 3 / 20))) =
      ((1 / (2 * Real.pi)) * B0 * K) * Real.sqrt N * ((N : ℝ) / R) ^ 3 *
        Real.log N ^ 6 * Real.exp (-(Real.log N ^ 3 / 20)) := by
    have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp
  have habs := ha N hNa R hR1 hR
  rw [hflat] at *
  linarith
