/-
P0095 W. C. Lu 2010, Section 9, the minor arc L² bound from a sup bound. Unit U-6847,
CLOUD MANUAL-M1, 2026-10-21, track T1.

p. 2391: "using a well-known result ... we can obtain as usual Σ_k |D₂(k)|² ≪ N^{3-c+0.00011}".
The "usual" step: if |S(N-td, N-td-d, α)| ≤ M for α on the minor arcs and t ∈ [a, b], then
  ∫_𝔪 |H|² ≤ M² (b-a)² (d+1) log²(2N),
by |H| ≤ M ∫|S₁| dt, Cauchy-Schwarz in t, Fubini, and the mean value ∫|S₁|² dα = Σ Λ².
This file PROVES that, `minorL2_of_sup`. With the sup bound of [12, p. 107] on the minor arcs,
M ≪ N^{1-c/2+ε}, this gives N^{0.0002 + 2 - c + 2ε + 0.9999} log²N, inside the printed
N^{3-c+0.00011}; `InputsS` cites the minor arc sup bound in that form.

AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel.
Binary Goldbach itself is OPEN.
-/
import Mathlib
import LeanLab.ExceptionalSet.Lu2010MeanValue

namespace LeanLab.ExceptionalSet.Lu2010Minor
open Real Filter Topology Finset ArithmeticFunction MeasureTheory Complex
  LeanLab.ExceptionalSet LeanLab.ExceptionalSet.Lu2010Assembly LeanLab.ExceptionalSet.Lu2010Lemma1
  LeanLab.ExceptionalSet.Lu2010Orth LeanLab.ExceptionalSet.Lu2010Arcs LeanLab.ExceptionalSet.Lu2010Sec9
  LeanLab.ExceptionalSet.Lu2010MeanValue

/-- `td < n ≤ td + d`. -/
def set1 (N n : ℕ) : Set ℝ := {t | t * dd N < n ∧ (n : ℝ) ≤ t * dd N + dd N}

/-- `N - td - d < m ≤ N - td`. -/
def set2 (N m : ℕ) : Set ℝ := {t | (N : ℝ) - t * dd N - dd N < m ∧ (m : ℝ) ≤ N - t * dd N}

theorem set1_meas (N n : ℕ) : MeasurableSet (set1 N n) := by
  have m1 : Measurable fun t : ℝ => t * dd N := by fun_prop
  have m2 : Measurable fun t : ℝ => t * dd N + dd N := by fun_prop
  exact (measurableSet_lt m1 measurable_const).inter (measurableSet_le measurable_const m2)

theorem set2_meas (N m : ℕ) : MeasurableSet (set2 N m) := by
  have m3 : Measurable fun t : ℝ => (N : ℝ) - t * dd N - dd N := by fun_prop
  have m4 : Measurable fun t : ℝ => (N : ℝ) - t * dd N := by fun_prop
  exact (measurableSet_lt m3 measurable_const).inter (measurableSet_le measurable_const m4)

/-- `S(td+d, td, α)` with a fixed range. -/
noncomputable def S1r (N : ℕ) (α t : ℝ) : ℂ :=
  ∑ n ∈ range (2 * N + 1), (set1 N n).indicator (fun _ => (Λ n : ℂ)) t * ee (n * α)

/-- `S(N-td, N-td-d, α)` with a fixed range. -/
noncomputable def S2r (N : ℕ) (α t : ℝ) : ℂ :=
  ∑ m ∈ range (2 * N + 1), (set2 N m).indicator (fun _ => (Λ m : ℂ)) t * ee (m * α)

/-- The window `t ∈ [a, b]` keeps `0 ≤ td`, `td + d ≤ 2N` and `1 ≤ d`. -/
theorem t_facts {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : t ∈ Set.Icc (aa N) (bb N)) :
    0 ≤ t * dd N ∧ t * dd N + dd N ≤ 2 * N ∧ 1 ≤ dd N := by
  have hd := dd_pos hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have ha0 : 0 ≤ aa N := by unfold aa; positivity
  have hba : (bb N - aa N) * dd N = N / 3 := bad_mul N hN
  have had : aa N * dd N = N / 3 := by
    unfold aa dd; rw [div_mul_eq_mul_div, ← rpow_add hN']; norm_num
  have hd1 : dd N ≤ N := by
    unfold dd
    calc (N : ℝ) ^ (0.9999 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = N := rpow_one _
  have hd1' : 1 ≤ dd N := Real.one_le_rpow hN1 (by norm_num)
  obtain ⟨hta, htb⟩ := ht
  refine ⟨mul_nonneg (ha0.trans hta) hd.le, ?_, hd1'⟩
  have : t * dd N ≤ bb N * dd N := mul_le_mul_of_nonneg_right htb hd.le
  nlinarith

theorem S1_eq {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : t ∈ Set.Icc (aa N) (bb N)) (α : ℝ) :
    Ssum (t * dd N + dd N) (t * dd N) α = S1r N α t := by
  obtain ⟨_, h2, _⟩ := t_facts hN ht
  rw [Ssum_eq_range (K := 2 * N) (by push_cast; linarith)]
  apply Finset.sum_congr rfl; intro n _
  simp only [Set.indicator, set1, Set.mem_setOf_eq]
  split_ifs <;> simp

theorem S2_eq {N : ℕ} (hN : 0 < N) {t : ℝ} (ht : t ∈ Set.Icc (aa N) (bb N)) (α : ℝ) :
    Ssum (N - t * dd N) (N - t * dd N - dd N) α = S2r N α t := by
  obtain ⟨h1, _, _⟩ := t_facts hN ht
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  rw [Ssum_eq_range (K := 2 * N) (by push_cast; linarith)]
  apply Finset.sum_congr rfl; intro m _
  simp only [Set.indicator, set2, Set.mem_setOf_eq]
  split_ifs <;> simp

/-- The bound `B = Σ_{n ≤ 2N} Λ(n)`. -/
noncomputable def B (N : ℕ) : ℝ := ∑ n ∈ range (2 * N + 1), Λ n

theorem S1r_le (N : ℕ) (α t : ℝ) : ‖S1r N α t‖ ≤ B N := by
  unfold S1r B
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, norm_ee, mul_one]
  by_cases h : t ∈ set1 N n
  · rw [Set.indicator_of_mem h, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
  · rw [Set.indicator_of_notMem h, norm_zero]; exact vonMangoldt_nonneg

theorem S1r_meas (N : ℕ) : Measurable fun p : ℝ × ℝ => S1r N p.1 p.2 := by
  unfold S1r
  refine Finset.measurable_sum _ (fun n _ => Measurable.mul ?_ ?_)
  · exact (measurable_const.indicator (set1_meas N n)).comp measurable_snd
  · exact (ee_continuous (n : ℝ)).measurable.comp measurable_fst

theorem S2r_meas (N : ℕ) : Measurable fun p : ℝ × ℝ => S2r N p.1 p.2 := by
  unfold S2r
  refine Finset.measurable_sum _ (fun n _ => Measurable.mul ?_ ?_)
  · exact (measurable_const.indicator (set2_meas N n)).comp measurable_snd
  · exact (ee_continuous (n : ℝ)).measurable.comp measurable_fst

theorem S1r_meas_t (N : ℕ) (α : ℝ) : Measurable fun t => S1r N α t := by
  unfold S1r
  exact Finset.measurable_sum _ (fun n _ =>
    (measurable_const.indicator (set1_meas N n)).mul measurable_const)

theorem S2r_meas_t (N : ℕ) (α : ℝ) : Measurable fun t => S2r N α t := by
  unfold S2r
  exact Finset.measurable_sum _ (fun n _ =>
    (measurable_const.indicator (set2_meas N n)).mul measurable_const)

theorem S2r_le (N : ℕ) (α t : ℝ) : ‖S2r N α t‖ ≤ B N := by
  unfold S2r B
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun n _ => ?_)
  rw [norm_mul, norm_ee, mul_one]
  by_cases h : t ∈ set2 N n
  · rw [Set.indicator_of_mem h, Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
  · rw [Set.indicator_of_notMem h, norm_zero]; exact vonMangoldt_nonneg

theorem B_nonneg (N : ℕ) : 0 ≤ B N := Finset.sum_nonneg fun n _ => vonMangoldt_nonneg

/-- A bounded measurable real function is integrable on `[a, b]`. -/
theorem intOn_Icc {f : ℝ → ℝ} (hf : Measurable f) {C : ℝ} (hC : ∀ x, ‖f x‖ ≤ C) (a b : ℝ) :
    IntegrableOn f (Set.Icc a b) :=
  Integrable.of_bound hf.aestronglyMeasurable C (Filter.Eventually.of_forall hC)

theorem vol_Icc_toReal {a b : ℝ} (h : a ≤ b) : (volume (Set.Icc a b)).toReal = b - a := by
  rw [Real.volume_Icc, ENNReal.toReal_ofReal (by linarith)]

/-- **The minor arc `(bb N - aa N)²` bound from a sup bound, PROVED**. -/
theorem minorL2_of_sup {N : ℕ} (hN : 0 < N) {M : ℝ} (hM0 : 0 ≤ M)
    (hM : ∀ α ∈ per N \ major N, α ≠ 1 - 1 / QQ N → ∀ t ∈ Set.Icc (aa N) (bb N),
      ‖Ssum (N - t * dd N) (N - t * dd N - dd N) α‖ ≤ M) :
    ∫ α in per N \ major N, ‖H N α‖ ^ 2 ≤
      M ^ 2 * (bb N - aa N) ^ 2 * ((dd N + 1) * Real.log (2 * N) ^ 2) := by
  have hd := dd_pos hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have hab : aa N ≤ bb N := by
    have hba := bad_mul N hN
    by_contra hc; push Not at hc
    have : (bb N - aa N) * dd N < 0 := mul_neg_of_neg_of_pos (by linarith) hd
    linarith
  have hL : 0 ≤ bb N - aa N := by linarith
  have hvol : (volume (Set.Icc (aa N) (bb N))).toReal = (bb N - aa N) := vol_Icc_toReal hab
  have hvolne : volume (Set.Icc (aa N) (bb N)) ≠ ⊤ := by
    rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top
  -- measurability in t for fixed α
  have m1 : ∀ α, Measurable fun t => S1r N α t := S1r_meas_t N
  have m2 : ∀ α, Measurable fun t => S2r N α t := S2r_meas_t N
  have hB := B_nonneg N
  -- (1) pointwise on the minor arcs
  have hpt : ∀ α ∈ per N \ major N, α ≠ 1 - 1 / QQ N →
      ‖H N α‖ ^ 2 ≤ M ^ 2 * (bb N - aa N) * ∫ t in (Set.Icc (aa N) (bb N)), ‖S1r N α t‖ ^ 2 := by
    intro α hα hαe
    have hH : H N α = ∫ t in (Set.Icc (aa N) (bb N)), S1r N α t * S2r N α t := by
      unfold H
      exact setIntegral_congr_fun measurableSet_Icc (fun t ht => by
        rw [S1_eq hN ht, S2_eq hN ht])
    have i1 : IntegrableOn (fun t => ‖S1r N α t‖ * ‖S2r N α t‖) (Set.Icc (aa N) (bb N)) :=
      intOn_Icc (f := fun t => ‖S1r N α t‖ * ‖S2r N α t‖) (((m1 α).norm).mul (m2 α).norm) (C := B N * B N) (fun t => by
        rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _))]
        exact mul_le_mul (S1r_le N α t) (S2r_le N α t) (norm_nonneg _) hB) _ _
    have i2 : IntegrableOn (fun t => M * ‖S1r N α t‖) (Set.Icc (aa N) (bb N)) :=
      intOn_Icc (f := fun t => M * ‖S1r N α t‖) (measurable_const.mul (m1 α).norm) (C := M * B N) (fun t => by
        rw [Real.norm_of_nonneg (mul_nonneg hM0 (norm_nonneg _))]
        exact mul_le_mul_of_nonneg_left (S1r_le N α t) hM0) _ _
    have i3 : IntegrableOn (fun t => ‖S1r N α t‖) (Set.Icc (aa N) (bb N)) :=
      intOn_Icc (f := fun t => ‖S1r N α t‖) (m1 α).norm (C := B N) (fun t => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact S1r_le N α t) _ _
    have i4 : IntegrableOn (fun t => ‖S1r N α t‖ ^ 2) (Set.Icc (aa N) (bb N)) :=
      intOn_Icc (f := fun t => ‖S1r N α t‖ ^ 2) ((m1 α).norm.pow_const 2) (C := B N ^ 2) (fun t => by
        rw [Real.norm_of_nonneg (by positivity)]
        exact pow_le_pow_left₀ (norm_nonneg _) (S1r_le N α t) 2) _ _
    have hle : ‖H N α‖ ≤ M * ∫ t in (Set.Icc (aa N) (bb N)), ‖S1r N α t‖ := by
      rw [hH]
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [← integral_const_mul]
      have : ∫ t in (Set.Icc (aa N) (bb N)), ‖S1r N α t * S2r N α t‖ = ∫ t in (Set.Icc (aa N) (bb N)), ‖S1r N α t‖ * ‖S2r N α t‖ := by
        simp_rw [norm_mul]
      rw [this]
      refine setIntegral_mono_on i1 i2 measurableSet_Icc (fun t ht => ?_)
      rw [mul_comm M]
      exact mul_le_mul_of_nonneg_left (by rw [← S2_eq hN ht]; exact hM α hα hαe t ht) (norm_nonneg _)
    have hcs := sq_setIntegral_le hvolne i3 i4
    rw [hvol] at hcs
    have h0 : 0 ≤ ‖H N α‖ := norm_nonneg _
    calc ‖H N α‖ ^ 2 ≤ (M * ∫ t in (Set.Icc (aa N) (bb N)), ‖S1r N α t‖) ^ 2 := pow_le_pow_left₀ h0 hle 2
      _ = M ^ 2 * (∫ t in (Set.Icc (aa N) (bb N)), ‖S1r N α t‖) ^ 2 := by ring
      _ ≤ M ^ 2 * ((bb N - aa N) * ∫ t in (Set.Icc (aa N) (bb N)), ‖S1r N α t‖ ^ 2) := by gcongr
      _ = M ^ 2 * (bb N - aa N) * ∫ t in (Set.Icc (aa N) (bb N)), ‖S1r N α t‖ ^ 2 := by ring
  -- product integrability
  set g : ℝ → ℝ → ℝ := fun α t => ‖S1r N α t‖ ^ 2
  haveI : IsFiniteMeasure (volume.restrict (per N)) := by unfold per; infer_instance
  have hprod : Integrable (Function.uncurry g) ((volume.restrict (per N)).prod (volume.restrict (Set.Icc (aa N) (bb N)))) := by
    refine Integrable.of_bound ((S1r_meas N).norm.pow_const 2).aestronglyMeasurable (B N ^ 2)
      (Filter.Eventually.of_forall fun p => ?_)
    simp only [Function.uncurry, g]
    rw [Real.norm_of_nonneg (by positivity)]
    exact pow_le_pow_left₀ (norm_nonneg _) (S1r_le N p.1 p.2) 2
  have hΦ : IntegrableOn (fun α => ∫ t in (Set.Icc (aa N) (bb N)), g α t) (per N) := hprod.integral_prod_left
  have hΨ : IntegrableOn (fun t => ∫ α in per N, g α t) (Set.Icc (aa N) (bb N)) := hprod.integral_prod_right
  -- (2) and (3)
  have hHc : Continuous (H N) := by rw [H_eq_F0]; exact F_continuous hN 0
  have hHint : IntegrableOn (fun α => ‖H N α‖ ^ 2) (per N \ major N) :=
    ((hHc.norm.pow 2).integrableOn_Icc (a := -1 / QQ N) (b := 1 - 1 / QQ N)).mono_set
      (Set.diff_subset.trans Set.Ioc_subset_Icc_self)
  have hΦc : IntegrableOn (fun α => M ^ 2 * (bb N - aa N) * ∫ t in (Set.Icc (aa N) (bb N)), g α t)
      (per N) := Integrable.const_mul hΦ _
  have step2 : ∫ α in per N \ major N, ‖H N α‖ ^ 2 ≤
      ∫ α in per N \ major N, M ^ 2 * (bb N - aa N) * ∫ t in (Set.Icc (aa N) (bb N)), g α t :=
    setIntegral_mono_on_ae hHint (hΦc.mono_set Set.diff_subset)
      ((measurableSet_Ioc).diff (major_measurable N))
      (by
        have hne : ∀ᵐ α ∂(volume : Measure ℝ), α ≠ 1 - 1 / QQ N := by
          rw [ae_iff]; simp [Real.volume_singleton]
        filter_upwards [hne] with α hαe hα using hpt α hα hαe)
  have hnn : ∀ α, 0 ≤ M ^ 2 * (bb N - aa N) * ∫ t in (Set.Icc (aa N) (bb N)), g α t := fun α =>
    mul_nonneg (by positivity) (setIntegral_nonneg measurableSet_Icc fun t _ => by positivity)
  have step3 : ∫ α in per N \ major N, M ^ 2 * (bb N - aa N) * ∫ t in (Set.Icc (aa N) (bb N)), g α t ≤
      ∫ α in per N, M ^ 2 * (bb N - aa N) * ∫ t in (Set.Icc (aa N) (bb N)), g α t :=
    setIntegral_mono_set hΦc (Filter.Eventually.of_forall hnn)
      (Filter.Eventually.of_forall fun α hα => Set.diff_subset hα)
  -- (4) swap
  have step4 : ∫ α in per N, M ^ 2 * (bb N - aa N) * ∫ t in (Set.Icc (aa N) (bb N)), g α t =
      M ^ 2 * (bb N - aa N) * ∫ t in (Set.Icc (aa N) (bb N)), ∫ α in per N, g α t := by
    rw [integral_const_mul, integral_integral_swap hprod]
  -- (5) mean value for each t
  have hmv : ∀ t ∈ (Set.Icc (aa N) (bb N)), ∫ α in per N, g α t ≤ (dd N + 1) * Real.log (2 * N) ^ 2 := by
    intro t ht
    obtain ⟨h1, h2, h3⟩ := t_facts hN ht
    have hcongr : ∫ α in per N, g α t = ∫ α in per N, ‖Ssum (t * dd N + dd N) (t * dd N) α‖ ^ 2 := by
      apply integral_congr_ae; filter_upwards with α
      simp only [g]; rw [S1_eq hN ht]
    rw [hcongr, per, ← intervalIntegral.integral_of_le (per_lt N).le,
      show 1 - 1 / QQ N = -1 / QQ N + 1 by ring]
    refine (meanValue_S_le h1 (by linarith) _).trans ?_
    have hx1 : 1 ≤ t * dd N + dd N := by linarith
    have hl0 : 0 ≤ Real.log (t * dd N + dd N) := Real.log_nonneg hx1
    have hl : Real.log (t * dd N + dd N) ≤ Real.log (2 * N) := Real.log_le_log (by linarith) h2
    have : t * dd N + dd N - t * dd N + 1 = dd N + 1 := by ring
    rw [this]
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hl0 hl 2) (by linarith)
  have step5 : ∫ t in (Set.Icc (aa N) (bb N)), ∫ α in per N, g α t ≤ (bb N - aa N) * ((dd N + 1) * Real.log (2 * N) ^ 2) := by
    have := setIntegral_mono_on hΨ (integrableOn_const hvolne) measurableSet_Icc hmv
    rw [setIntegral_const, smul_eq_mul] at this
    rw [show (volume.real (Set.Icc (aa N) (bb N))) = (bb N - aa N) from hvol] at this
    exact this
  calc ∫ α in per N \ major N, ‖H N α‖ ^ 2 ≤ _ := step2
    _ ≤ _ := step3
    _ = _ := step4
    _ ≤ M ^ 2 * (bb N - aa N) * ((bb N - aa N) * ((dd N + 1) * Real.log (2 * N) ^ 2)) := by gcongr
    _ = M ^ 2 * (bb N - aa N) ^ 2 * ((dd N + 1) * Real.log (2 * N) ^ 2) := by ring

/-- `(b - a) = N^{0.0001}/3`. -/
theorem ba_eq {N : ℕ} (hN : 0 < N) : bb N - aa N = (N : ℝ) ^ (0.0001 : ℝ) / 3 := by
  have hd := dd_pos hN
  have hN' : (0 : ℝ) < N := by exact_mod_cast hN
  have h := bad_mul N hN
  have hdN : (N : ℝ) = (N : ℝ) ^ (0.0001 : ℝ) * dd N := by
    unfold dd; rw [← rpow_add hN']; norm_num
  have : (bb N - aa N) * dd N = (N : ℝ) ^ (0.0001 : ℝ) / 3 * dd N := by
    rw [h]; nth_rewrite 1 [hdN]; ring
  exact mul_right_cancel₀ hd.ne' this

/-- The exponent bookkeeping of Section 9: with `M = C N^{1-c/2+4·10^{-6}}`, eventually
`M² (b-a)² (d+1) log²(2N) ≤ (2/9) C² N^{3-c+0.00011}`. -/
theorem sec9_exponent (C : ℝ) : ∃ N1 : ℕ, ∀ N, N1 ≤ N →
    (C * (N : ℝ) ^ (1 - c / 2 + 0.000004)) ^ 2 * (bb N - aa N) ^ 2 *
      ((dd N + 1) * Real.log (2 * N) ^ 2) ≤ 2 / 9 * C ^ 2 * (N : ℝ) ^ (3 - c + 0.00011) := by
  have hlo := (isLittleO_log_rpow_atTop (r := 0.000001) (by norm_num)).bound
    (c := 1 / 2) (by norm_num)
  have h2 : Tendsto (fun N : ℕ => (2 : ℝ) * N) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  obtain ⟨N1, hN1⟩ := Filter.eventually_atTop.mp (h2.eventually hlo)
  refine ⟨max N1 1, fun N hN => ?_⟩
  have hNpos : 0 < N := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hN)
  have hN' : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hN1r : (1 : ℝ) ≤ N := by exact_mod_cast hNpos
  have hl := hN1 N (le_trans (le_max_left _ _) hN)
  have hx1 : (1 : ℝ) ≤ 2 * N := by linarith
  rw [Real.norm_of_nonneg (Real.log_nonneg hx1),
    Real.norm_of_nonneg (rpow_nonneg (by linarith) _)] at hl
  have hlog2 : Real.log (2 * N) ^ 2 ≤ (N : ℝ) ^ (0.000002 : ℝ) := by
    have h0 : 0 ≤ Real.log (2 * N) := Real.log_nonneg hx1
    have hsq := pow_le_pow_left₀ h0 hl 2
    have hpw : ((2 * (N : ℝ)) ^ (0.000001 : ℝ)) ^ 2 = (2 : ℝ) ^ (0.000002 : ℝ) * (N : ℝ) ^ (0.000002 : ℝ) := by
      rw [← rpow_natCast, ← rpow_mul (by positivity), mul_rpow (by norm_num) hN'.le]; norm_num
    have h2p : (2 : ℝ) ^ (0.000002 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (0.000002 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := rpow_one 2
    have hNp : 0 ≤ (N : ℝ) ^ (0.000002 : ℝ) := by positivity
    calc Real.log (2 * N) ^ 2 ≤ (1 / 2 * (2 * (N : ℝ)) ^ (0.000001 : ℝ)) ^ 2 := hsq
      _ = 1 / 4 * ((2 * (N : ℝ)) ^ (0.000001 : ℝ)) ^ 2 := by ring
      _ = 1 / 4 * ((2 : ℝ) ^ (0.000002 : ℝ) * (N : ℝ) ^ (0.000002 : ℝ)) := by rw [hpw]
      _ ≤ (N : ℝ) ^ (0.000002 : ℝ) := by nlinarith
  have hdd1 : dd N + 1 ≤ 2 * (N : ℝ) ^ (0.9999 : ℝ) := by
    have : (1 : ℝ) ≤ (N : ℝ) ^ (0.9999 : ℝ) := Real.one_le_rpow hN1r (by norm_num)
    unfold dd; linarith
  rw [ba_eq hNpos]
  have hc : c = 0.1215 := rfl
  have hA : 0 ≤ (C * (N : ℝ) ^ (1 - c / 2 + 0.000004)) ^ 2 * ((N : ℝ) ^ (0.0001 : ℝ) / 3) ^ 2 := by
    positivity
  calc (C * (N : ℝ) ^ (1 - c / 2 + 0.000004)) ^ 2 * ((N : ℝ) ^ (0.0001 : ℝ) / 3) ^ 2 *
        ((dd N + 1) * Real.log (2 * N) ^ 2)
      ≤ (C * (N : ℝ) ^ (1 - c / 2 + 0.000004)) ^ 2 * ((N : ℝ) ^ (0.0001 : ℝ) / 3) ^ 2 *
        ((2 * (N : ℝ) ^ (0.9999 : ℝ)) * (N : ℝ) ^ (0.000002 : ℝ)) := by
        gcongr
    _ = 2 / 9 * C ^ 2 * (((N : ℝ) ^ (1 - c / 2 + 0.000004)) ^ 2 * ((N : ℝ) ^ (0.0001 : ℝ)) ^ 2 *
        (N : ℝ) ^ (0.9999 : ℝ) * (N : ℝ) ^ (0.000002 : ℝ)) := by ring
    _ = 2 / 9 * C ^ 2 * (N : ℝ) ^ (3 - c + 0.00011) := by
        congr 1
        rw [← rpow_natCast, ← rpow_mul hN'.le, ← rpow_natCast, ← rpow_mul hN'.le,
          ← rpow_add hN', ← rpow_add hN', ← rpow_add hN', hc]
        norm_num

/-- **Cited input**, as `InputsM` but with Section 9 as the minor arc sup bound. The endpoint
`α = 1 - 1/Q` of the printed 𝔪 = [-1/Q, 1 - 1/Q] \ 𝔐 is excluded: it is congruent to `-1/Q`, on the
major arc of `0/1`, where Dirichlet's theorem gives q = 1 and the [12, p. 107] route does not apply;
a falsifier subagent estimates |S| about N^{3/4} there, so the bound is not known false, only not
derivable. A null set, so the integrals are unchanged. The bound:
`|S(N-td, N-td-d, α)| ≤ C N^{1-c/2+4·10^{-6}}` for α ∈ 𝔪, t ∈ [a, b]. This is what the bound
of [12, p. 107], `(x^{1/2}q^{1/2} + x^{9/10} + xq^{-1/2})x^ε`, gives on the minor arcs, where
Dirichlet's theorem puts α near h/q with P < q ≤ Q, so `xq^{-1/2} ≤ N^{1-c/2}` dominates. -/
structure InputsS where
  D6 : ℕ → ℕ → ℂ
  S : ℕ → ℝ
  S_ge : ∀ k, Even k → 1 ≤ S k
  N0 : ℕ
  Cerr : ℝ
  c1 : ℝ
  c1_pos : 0 < c1
  Cs : ℝ
  C86 : ℝ
  lower : ∀ N, N0 ≤ N →
    (∀ k ∈ Win N, Even k →
      S k * (bb N - aa N) * dd N *
        ((Real.log (Real.log (Real.log N)))⁻¹ - Cerr * (Real.log (Real.log N)) ^ (-(1 / 2) : ℝ))
        - ‖D6 N k‖ < (D1c N k).re) ∨
    (∀ k ∈ Win N, Even k →
      S k * (bb N - aa N) * dd N * c1 * PP N ^ (-0.00001 : ℝ) * Real.log (PP N) *
        (2 * c⁻¹ - Cerr * (Real.log (Real.log (Real.log N))) ^ (-0.1 : ℝ))
        - ‖D6 N k‖ ≤ (D1c N k).re)
  minorSup : ∀ N, N0 ≤ N → ∀ α ∈ per N \ major N, α ≠ 1 - 1 / QQ N → ∀ t ∈ Set.Icc (aa N) (bb N),
    ‖Ssum (N - t * dd N) (N - t * dd N - dd N) α‖ ≤ Cs * (N : ℝ) ^ (1 - c / 2 + 0.000004)
  eq86 : ∀ N, N0 ≤ N →
    ∑ k ∈ Win N, ‖D6 N k‖ ^ 2 ≤ C86 * PP N ^ (-1 : ℝ) * dd N * (N : ℝ) ^ (2.0003 : ℝ)

/-- `InputsS` gives `InputsM`, by `minorL2_of_sup` and `sec9_exponent`. -/
noncomputable def InputsS.toInputsM (J : InputsS) : InputsM :=
  have hex := sec9_exponent |J.Cs|
  { D6 := J.D6, S := J.S, S_ge := J.S_ge, N0 := max (max J.N0 1) hex.choose, Cerr := J.Cerr,
    c1 := J.c1, c1_pos := J.c1_pos, C9 := 2 / 9 * |J.Cs| ^ 2, C86 := J.C86
    lower := fun N hN => J.lower N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN)
    minorL2 := fun N hN => by
      have hN0 : J.N0 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
      have hNpos : 0 < N :=
        lt_of_lt_of_le one_pos (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN)
      have hM0 : 0 ≤ |J.Cs| * (N : ℝ) ^ (1 - c / 2 + 0.000004) := by positivity
      refine (minorL2_of_sup hNpos hM0 (fun α hα hαe t ht => (J.minorSup N hN0 α hα hαe t ht).trans ?_)).trans
        (hex.choose_spec N (le_trans (le_max_right _ _) hN))
      exact mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
    eq86 := fun N hN => J.eq86 N (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN) }

/-- CONDITIONAL ON `InputsS`: the paper's Theorem `E(x) ≪ x^{0.879}`. -/
theorem lu_of_inputsS (J : InputsS) : PowerBound 0.879 := lu_of_inputsM J.toInputsM

/-- CONDITIONAL ON `InputsS`: `E X ≪ X^{0.8789126}`. -/
theorem lu_sharp_of_inputsS (J : InputsS) : PowerBound θ := lu_sharp_of_inputsM J.toInputsM

/-- CONDITIONAL ON `InputsS`: Pintz's eventual form `E X < X^{0.879}`. -/
theorem lu_eventually_of_inputsS (J : InputsS) : Lu2010.lu_eventually_stmt :=
  lu_eventually_of_inputsM J.toInputsM

end LeanLab.ExceptionalSet.Lu2010Minor

#print axioms LeanLab.ExceptionalSet.Lu2010Minor.set1_meas
#print axioms LeanLab.ExceptionalSet.Lu2010Minor.set2_meas
#print axioms LeanLab.ExceptionalSet.Lu2010Minor.t_facts
#print axioms LeanLab.ExceptionalSet.Lu2010Minor.S1_eq
#print axioms LeanLab.ExceptionalSet.Lu2010Minor.S2_eq
#print axioms LeanLab.ExceptionalSet.Lu2010Minor.S1r_le
#print axioms LeanLab.ExceptionalSet.Lu2010Minor.S1r_meas
#print axioms LeanLab.ExceptionalSet.Lu2010Minor.S1r_meas_t
#print axioms LeanLab.ExceptionalSet.Lu2010Minor.S2r_meas
#print axioms LeanLab.ExceptionalSet.Lu2010Minor.S2r_meas_t
#print axioms LeanLab.ExceptionalSet.Lu2010Minor.S2r_le
#print axioms LeanLab.ExceptionalSet.Lu2010Minor.B_nonneg
#print axioms LeanLab.ExceptionalSet.Lu2010Minor.intOn_Icc
#print axioms LeanLab.ExceptionalSet.Lu2010Minor.vol_Icc_toReal
#print axioms LeanLab.ExceptionalSet.Lu2010Minor.minorL2_of_sup
#print axioms LeanLab.ExceptionalSet.Lu2010Minor.ba_eq
#print axioms LeanLab.ExceptionalSet.Lu2010Minor.sec9_exponent
#print axioms LeanLab.ExceptionalSet.Lu2010Minor.InputsS.toInputsM
#print axioms LeanLab.ExceptionalSet.Lu2010Minor.lu_of_inputsS
#print axioms LeanLab.ExceptionalSet.Lu2010Minor.lu_sharp_of_inputsS
#print axioms LeanLab.ExceptionalSet.Lu2010Minor.lu_eventually_of_inputsS
