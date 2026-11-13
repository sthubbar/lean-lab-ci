/-
Elementary phase estimates for the four constant phase ranges.
Gallagher 1975 p.127 display 2 gives the arc width used here.
These estimates control variation within an arc. They do not estimate its prime mass.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.PNTPort.LargeSieve.Basic
import LeanLab.Linnik.LiLiuDisplay37PNT
import LeanLab.Linnik.Decomp1532c

namespace LeanLab.Linnik.Decomp495a

open Filter MeasureTheory
open scoped Topology
open LeanLab.Linnik.Decomp1532b (majorArcs)

/-- Gallagher 1975 p.127 display 2. A shift of size at most `N ^ s` changes its
linear phase by at most `N ^ (s + θ - 1)` between the center and a point of an arc. -/
theorem phase_travel_le {N q θ s d α a : ℝ} (hN : 0 < N) (hq : 1 ≤ q)
    (hd : |d| ≤ N ^ s) (hα : |α - a / q| ≤ N ^ θ / (q * N)) :
    |d * α - d * (a / q)| ≤ N ^ (s + θ - 1) := by
  have hw : N ^ θ / (q * N) ≤ N ^ θ / N :=
    div_le_div_of_nonneg_left (Real.rpow_nonneg hN.le _) hN (by nlinarith)
  calc
    |d * α - d * (a / q)| = |d| * |α - a / q| := by rw [← mul_sub, abs_mul]
    _ ≤ N ^ s * (N ^ θ / N) :=
      mul_le_mul hd (hα.trans hw) (abs_nonneg _) (Real.rpow_nonneg hN.le _)
    _ = N ^ (s + θ - 1) := by
      rw [Real.rpow_sub hN, Real.rpow_add hN, Real.rpow_one]
      ring

/-- Gallagher 1975 p.127 displays 1 and 2. The additive character varies by at
most `2π N ^ (s + θ - 1)` from the arc center. This uses the existing lab Lipschitz lemma. -/
theorem phase_character_le {N q θ s d α a : ℝ} (hN : 0 < N) (hq : 1 ≤ q)
    (hd : |d| ≤ N ^ s) (hα : |α - a / q| ≤ N ^ θ / (q * N)) :
    ‖LeanLab.PNTPort.LargeSieve.e (d * α) - LeanLab.PNTPort.LargeSieve.e (d * (a / q))‖ ≤ 2 * Real.pi * N ^ (s + θ - 1) := by
  exact (LiLiuDisplay37PNT.e_lip _ _).trans
    (mul_le_mul_of_nonneg_left (phase_travel_le hN hq hd hα) (by positivity))

/-- Gallagher 1975 p.127 displays 1 and 2, specialized to the largest constant
phase range. For `θ ≤ 1/4` and `s ≤ θ/2`, every smaller range has the common saving `N ^ (-5/8)`. -/
theorem phase_character_small_shift_le {N q θ s d α a : ℝ} (hN : 1 ≤ N)
    (hq : 1 ≤ q) (hθ : θ ≤ 1 / 4) (hs : s ≤ θ / 2)
    (hd : |d| ≤ N ^ s) (hα : |α - a / q| ≤ N ^ θ / (q * N)) :
    ‖LeanLab.PNTPort.LargeSieve.e (d * α) - LeanLab.PNTPort.LargeSieve.e (d * (a / q))‖ ≤ 2 * Real.pi * N ^ (-5 / 8 : ℝ) := by
  exact (phase_character_le (by linarith) hq hd hα).trans
    (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hN (by linarith)) (by positivity))

/-- Gallagher 1975 p.127 display 2. One can select a rational center measurably
on every major arc, including when the arcs overlap. No disjointness assumption is used. -/
theorem exists_measurable_arc_center (N : ℕ) (P : ℝ) :
    ∃ c : ℝ → ℝ, Measurable c ∧ ∀ α ∈ majorArcs N P,
      ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ P ∧ ∃ a : ℕ, a ≤ q ∧ Nat.Coprime a q ∧
        c α = (a : ℝ) / q ∧ |α - c α| ≤ P / (q * N) := by
  classical
  let A : ℕ → Set ℝ := fun n => {α | α ∉ majorArcs N P ∨
    1 ≤ (Nat.unpair n).1 ∧ ((Nat.unpair n).1 : ℝ) ≤ P ∧
      (Nat.unpair n).2 ≤ (Nat.unpair n).1 ∧
      Nat.Coprime (Nat.unpair n).2 (Nat.unpair n).1 ∧
      |α - ((Nat.unpair n).2 : ℝ) / (Nat.unpair n).1| ≤
        P / ((Nat.unpair n).1 * N)}
  have hm : ∀ n, MeasurableSet (A n) := by
    intro n
    simp only [A, Set.ofPred_or, Set.ofPred_and]
    exact (Decomp1532c.measurableSet_majorArcs N P).compl.union
      ((MeasurableSet.const _).inter ((MeasurableSet.const _).inter
        ((MeasurableSet.const _).inter ((MeasurableSet.const _).inter
          (isClosed_le (by fun_prop) continuous_const).measurableSet))))
  have hex : ∀ α : ℝ, ∃ n : ℕ, α ∈ A n := by
    intro α
    by_cases h : α ∈ majorArcs N P
    · obtain ⟨_, q, hq, hqP, a, haq, hcop, hwidth⟩ := h
      refine ⟨Nat.pair q a, ?_⟩
      simpa only [A, Set.mem_ofPred_eq, Nat.unpair_pair] using
        (Or.inr ⟨hq, hqP, haq, hcop, hwidth⟩ :
          α ∉ majorArcs N P ∨ 1 ≤ q ∧ (q : ℝ) ≤ P ∧ a ≤ q ∧
            Nat.Coprime a q ∧ |α - (a : ℝ) / q| ≤ P / (q * N))
    · exact ⟨0, Or.inl h⟩
  let c : ℝ → ℝ := fun α =>
    ((Nat.unpair (Nat.find (hex α))).2 : ℝ) / (Nat.unpair (Nat.find (hex α))).1
  have hc : Measurable c :=
    Measurable.find
      (f := fun n (_ : ℝ) => ((Nat.unpair n).2 : ℝ) / (Nat.unpair n).1)
      (p := fun n α => α ∈ A n) (fun _ => measurable_const) hm hex
  refine ⟨c, hc, ?_⟩
  intro α hα
  have hmem := Nat.find_spec (hex α)
  change α ∉ majorArcs N P ∨ _ at hmem
  rcases hmem with hnot | ⟨hq, hqP, haq, hcop, hwidth⟩
  · exact False.elim (hnot hα)
  · exact ⟨_, hq, hqP, _, haq, hcop, rfl, hwidth⟩

/-- Gallagher 1975 p.127 displays 1 and 2. A uniform character error integrates
against a nonnegative integrable weight with loss at most its total mass. -/
theorem weighted_phase_freeze_le {μ : Measure ℝ} {w : ℝ → ℝ} {d C : ℝ}
    (hw : Integrable w μ) (hw0 : ∀ᵐ α ∂μ, 0 ≤ w α) (c : ℝ → ℝ) (hc : Measurable c)
    (hphase : ∀ᵐ α ∂μ, ‖LeanLab.PNTPort.LargeSieve.e (d * α) - LeanLab.PNTPort.LargeSieve.e (d * c α)‖ ≤ C) :
    |(∫ α, w α * (LeanLab.PNTPort.LargeSieve.e (d * α)).re ∂μ) -
      (∫ α, w α * (LeanLab.PNTPort.LargeSieve.e (d * c α)).re ∂μ)| ≤ C * ∫ α, w α ∂μ := by
  have hb (t : ℝ) : ‖(LeanLab.PNTPort.LargeSieve.e t).re‖ ≤ 1 := by
    simpa only [Real.norm_eq_abs, LeanLab.PNTPort.LargeSieve.norm_e] using
      Complex.abs_re_le_norm (LeanLab.PNTPort.LargeSieve.e t)
  have hm : Measurable (fun α => (LeanLab.PNTPort.LargeSieve.e (d * c α)).re) := by
    unfold LeanLab.PNTPort.LargeSieve.e
    fun_prop
  have hn : Continuous (fun α : ℝ => (LeanLab.PNTPort.LargeSieve.e (d * α)).re) := by
    unfold LeanLab.PNTPort.LargeSieve.e
    fun_prop
  have hI := hw.mul_bdd hn.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun α => hb (d * α)))
  have hJ := hw.mul_bdd hm.aestronglyMeasurable
    (Filter.Eventually.of_forall (fun α => hb (d * c α)))
  have hbound : ∀ᵐ α ∂μ,
      ‖w α * (LeanLab.PNTPort.LargeSieve.e (d * α)).re - w α * (LeanLab.PNTPort.LargeSieve.e (d * c α)).re‖ ≤ C * w α := by
    filter_upwards [hw0, hphase] with α hα hp
    rw [← mul_sub, Real.norm_eq_abs, abs_mul, abs_of_nonneg hα]
    have he1 : |(LeanLab.PNTPort.LargeSieve.e (d * α)).re - (LeanLab.PNTPort.LargeSieve.e (d * c α)).re| ≤
        ‖LeanLab.PNTPort.LargeSieve.e (d * α) - LeanLab.PNTPort.LargeSieve.e (d * c α)‖ := by
      simpa only [Complex.sub_re] using
        (Complex.abs_re_le_norm (LeanLab.PNTPort.LargeSieve.e (d * α) - LeanLab.PNTPort.LargeSieve.e (d * c α)))
    have he := he1.trans hp
    nlinarith [mul_le_mul_of_nonneg_left he hα]
  have h := norm_integral_le_of_norm_le (hw.const_mul C) hbound
  rw [integral_sub hI hJ, integral_const_mul, Real.norm_eq_abs] at h
  exact h

/-- Gallagher 1975 p.127 displays 1 and 2, at the normalization of p.138 display 5.
The logarithmic square cannot offset the uniform phase saving `N ^ (-5/8)`. -/
theorem logarithmic_phase_error_tendsto :
    Tendsto (fun N : ℕ => Real.pi * Real.log N ^ 2 / (N : ℝ) ^ (5 / 8 : ℝ))
      atTop (𝓝 0) := by
  have h := (isLittleO_log_rpow_rpow_atTop (2 : ℝ)
    (by norm_num : (0 : ℝ) < 5 / 8)).tendsto_div_nhds_zero
  simpa only [Real.rpow_two, mul_zero, Function.comp_def, mul_div_assoc] using
    (h.comp (tendsto_natCast_atTop_atTop (R := ℝ))).const_mul Real.pi

/-- Gallagher 1975 p.127 displays 1 and 2. Freeze the phase at any measurable
choice of rational arc centers. Parseval bounds the cost by the prime counting function
and the common `N ^ (-5/8)` phase saving. This does not approximate the frozen masses. -/
theorem small_shift_phase_freeze_le (N : ℕ) (hN : 1 ≤ N) (θ : ℝ) (hθ : θ ≤ 1 / 4)
    (d : ℝ) (hd : |d| ≤ (N : ℝ) ^ (θ / 2)) (c : ℝ → ℝ) (hc : Measurable c)
    (hcenter : ∀ α ∈ majorArcs N ((N : ℝ) ^ θ),
      ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ (N : ℝ) ^ θ ∧ ∃ a : ℕ,
        a ≤ q ∧ Nat.Coprime a q ∧ c α = (a : ℝ) / q ∧
          |α - c α| ≤ (N : ℝ) ^ θ / (q * N)) :
    |(∫ α in majorArcs N ((N : ℝ) ^ θ),
        ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e (d * α)).re) -
      (∫ α in majorArcs N ((N : ℝ) ^ θ),
        ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e (d * c α)).re)| ≤
      (2 * Real.pi * (N : ℝ) ^ (-5 / 8 : ℝ)) * Nat.primeCounting N := by
  have hw : IntegrableOn (fun α => ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2)
      (majorArcs N ((N : ℝ) ^ θ)) :=
    ((U7206.continuous_Sg N).norm.pow 2).integrableOn_Icc.mono_set
      (fun _ h => h.1)
  have hphase : ∀ᵐ α ∂volume.restrict (majorArcs N ((N : ℝ) ^ θ)),
      ‖LeanLab.PNTPort.LargeSieve.e (d * α) - LeanLab.PNTPort.LargeSieve.e (d * c α)‖ ≤ 2 * Real.pi * (N : ℝ) ^ (-5 / 8 : ℝ) := by
    filter_upwards [ae_restrict_mem (Decomp1532c.measurableSet_majorArcs N _)] with α hα
    obtain ⟨q, hq, _, a, _, _, hca, hwidth⟩ := hcenter α hα
    rw [hca] at hwidth ⊢
    exact phase_character_small_shift_le (by exact_mod_cast hN)
      (by exact_mod_cast hq) hθ le_rfl hd hwidth
  exact (weighted_phase_freeze_le hw (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
    c hc hphase).trans
      (mul_le_mul_of_nonneg_left (Decomp1532c.major_arc_Sg_mean_le N _) (by positivity))

/-- The four range cuts in the task comments are nonvacuous. At `k = 2` and
`N = 2 ^ 32`, four exponent pairs have respective nonzero differences `2, 4, 8, 16`.
These are the four upper cut values when `θ = 1/4`. The source tuples are those of
Gallagher 1975 p.134 display 3. -/
theorem four_nonzero_shift_instances :
    ∃ x₁ x₂ x₃ x₄ : Decomp1532a.pairs 2 (Nat.log 2 (2 ^ 32)),
      Decomp1532a.dif x₁ = 2 ∧ Decomp1532a.dif x₂ = 4 ∧
        Decomp1532a.dif x₃ = 8 ∧ Decomp1532a.dif x₄ = 16 := by
  rw [Nat.log_pow (by norm_num : 1 < (2 : ℕ))]
  refine ⟨(![1, 0], ![0, 0]), (![1, 1], ![0, 0]),
    (![2, 1], ![0, 0]), (![3, 1], ![0, 0]), ?_⟩
  norm_num [Decomp1532a.dif, U1434Lemma21.sv, Fin.sum_univ_two]

/-- At the preceding concrete instance, the four real power thresholds are
exactly `2, 4, 8, 16`. These are the task's cuts of the p.127 display 2 phase range. -/
theorem four_cut_values_instance :
    (((2 ^ 32 : ℕ) : ℝ) ^ ((1 / 4 : ℝ) / 8) = 2) ∧
      (((2 ^ 32 : ℕ) : ℝ) ^ ((1 / 4 : ℝ) / 4) = 4) ∧
      (((2 ^ 32 : ℕ) : ℝ) ^ (3 * (1 / 4 : ℝ) / 8) = 8) ∧
      (((2 ^ 32 : ℕ) : ℝ) ^ ((1 / 4 : ℝ) / 2) = 16) := by
  have hp (r : ℝ) : ((2 ^ 32 : ℕ) : ℝ) ^ r = (2 : ℝ) ^ ((32 : ℝ) * r) := by
    rw [Nat.cast_pow, Nat.cast_ofNat, ← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) 32 r]
    norm_num
  simp only [hp]
  norm_num [show (2 : ℝ) ^ (2 : ℝ) = 4 by norm_num,
    show (2 : ℝ) ^ (3 : ℝ) = 8 by norm_num,
    show (2 : ℝ) ^ (4 : ℝ) = 16 by norm_num]

/-- Gallagher 1975 p.127 displays 1 and 2 and p.138 tuple expansion. The local
phase freezing error summed over any of the four task ranges is bounded by the full
number of exponent pairs times the single shift error. No singular series input is used. -/
theorem small_shift_filtered_freeze_le (k N : ℕ) (hN : 1 ≤ N) (θ : ℝ) (hθ : θ ≤ 1 / 4)
    (T : Finset (Decomp1532a.pairs k (Nat.log 2 N)))
    (hd : ∀ x ∈ T, |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2))
    (c : ℝ → ℝ) (hc : Measurable c)
    (hcenter : ∀ α ∈ majorArcs N ((N : ℝ) ^ θ),
      ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ (N : ℝ) ^ θ ∧ ∃ a : ℕ,
        a ≤ q ∧ Nat.Coprime a q ∧ c α = (a : ℝ) / q ∧
          |α - c α| ≤ (N : ℝ) ^ θ / (q * N)) :
    |(∑ x ∈ T, ∫ α in majorArcs N ((N : ℝ) ^ θ),
        ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * α)).re) -
      (∑ x ∈ T, ∫ α in majorArcs N ((N : ℝ) ^ θ),
        ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * c α)).re)| ≤
      (Nat.log 2 N : ℝ) ^ (2 * k) *
        (2 * Real.pi * (N : ℝ) ^ (-5 / 8 : ℝ)) * Nat.primeCounting N := by
  classical
  let I := fun x : Decomp1532a.pairs k (Nat.log 2 N) =>
    ∫ α in majorArcs N ((N : ℝ) ^ θ),
      ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * α)).re
  let F := fun x : Decomp1532a.pairs k (Nat.log 2 N) =>
    ∫ α in majorArcs N ((N : ℝ) ^ θ),
      ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * c α)).re
  let B : ℝ := (2 * Real.pi * (N : ℝ) ^ (-5 / 8 : ℝ)) * Nat.primeCounting N
  have hcard : (T.card : ℝ) ≤ (Nat.log 2 N : ℝ) ^ (2 * k) := by
    have h : T.card ≤ (Nat.log 2 N) ^ (2 * k) := by
      simpa [Decomp1532a.pairs, two_mul, pow_add] using Finset.card_le_univ T
    exact_mod_cast h
  change |T.sum I - T.sum F| ≤ _
  calc
    |T.sum I - T.sum F| = |∑ x ∈ T, (I x - F x)| := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ x ∈ T, |I x - F x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _x ∈ T, B := Finset.sum_le_sum (fun x hx =>
      small_shift_phase_freeze_le N hN θ hθ _ (hd x hx) c hc hcenter)
    _ = (T.card : ℝ) * B := by simp
    _ ≤ (Nat.log 2 N : ℝ) ^ (2 * k) * B :=
      mul_le_mul_of_nonneg_right hcard (by dsimp [B]; positivity)
    _ = _ := by dsimp [B]; ring

/-- Gallagher 1975 p.127 displays 1 and 2, measured against the p.138 display 5
normalization. The phase freezing cost is eventually below any prescribed fraction
of `2 N / log squared N`, independently of theta and the number of exponent tuples. -/
theorem phase_freeze_budget_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      (2 * Real.pi * (N : ℝ) ^ (-5 / 8 : ℝ)) * Nat.primeCounting N ≤
        (2 * N / Real.log N ^ 2) * (δ / 24) := by
  have hev : ∀ᶠ N : ℕ in atTop,
      Real.pi * Real.log N ^ 2 / (N : ℝ) ^ (5 / 8 : ℝ) ≤ δ / 48 :=
    logarithmic_phase_error_tendsto.eventually
      (ge_mem_nhds (by linarith : (0 : ℝ) < δ / 48))
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp hev
  refine ⟨max N₀ 2, fun N hN => ?_⟩
  have hN2 : 2 ≤ N := le_trans (le_max_right _ _) hN
  have hn : (2 : ℝ) ≤ N := by exact_mod_cast hN2
  have hNp : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlog : Real.log N ≠ 0 :=
    (Real.log_pos (by exact_mod_cast (by omega : 1 < N))).ne'
  have hp : (N : ℝ) ^ (5 / 8 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos hNp _).ne'
  have hpc : (Nat.primeCounting N : ℝ) ≤ 2 * N := by
    have hc : Nat.primeCounting N ≤ N + 1 := Nat.count_le Nat.Prime
    have hcr : (Nat.primeCounting N : ℝ) ≤ (N : ℝ) + 1 := by exact_mod_cast hc
    nlinarith
  have hsmall := hN₀ N (le_trans (le_max_left _ _) hN)
  calc
    (2 * Real.pi * (N : ℝ) ^ (-5 / 8 : ℝ)) * Nat.primeCounting N
      ≤ (2 * Real.pi * (N : ℝ) ^ (-5 / 8 : ℝ)) * (2 * N) := by gcongr
    _ = (2 * N / Real.log N ^ 2) *
        (2 * (Real.pi * Real.log N ^ 2 / (N : ℝ) ^ (5 / 8 : ℝ))) := by
      rw [show (-5 / 8 : ℝ) = -(5 / 8 : ℝ) by ring, Real.rpow_neg hNp.le]
      field_simp
    _ ≤ (2 * N / Real.log N ^ 2) * (δ / 24) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)

/-- Gallagher 1975 p.127 display 2 and the p.138 tuple expansion normalization.
The total phase freezing error on any of the four constant phase ranges is eventually
within its delta over 24 budget. The remaining analytic task is the frozen mass approximation. -/
theorem small_shift_filtered_freeze_eventually (δ : ℝ) (hδ : 0 < δ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ k : ℕ, ∀ θ : ℝ, θ ≤ 1 / 4 →
      ∀ T : Finset (Decomp1532a.pairs k (Nat.log 2 N)),
      (∀ x ∈ T, |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2)) →
      ∀ c : ℝ → ℝ, Measurable c →
      (∀ α ∈ majorArcs N ((N : ℝ) ^ θ),
        ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ (N : ℝ) ^ θ ∧ ∃ a : ℕ,
          a ≤ q ∧ Nat.Coprime a q ∧ c α = (a : ℝ) / q ∧
            |α - c α| ≤ (N : ℝ) ^ θ / (q * N)) →
      |(∑ x ∈ T, ∫ α in majorArcs N ((N : ℝ) ^ θ),
          ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * α)).re) -
        (∑ x ∈ T, ∫ α in majorArcs N ((N : ℝ) ^ θ),
          ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * c α)).re)| ≤
        (2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2) * (δ / 24) := by
  obtain ⟨N₁, hN₁⟩ := phase_freeze_budget_eventually δ hδ
  refine ⟨max N₁ 1, fun N hN k θ hθ T hd c hc hcenter => ?_⟩
  have hNpos : 1 ≤ N := le_trans (le_max_right _ _) hN
  have hbudget := hN₁ N (le_trans (le_max_left _ _) hN)
  calc
    _ ≤ (Nat.log 2 N : ℝ) ^ (2 * k) *
        ((2 * Real.pi * (N : ℝ) ^ (-5 / 8 : ℝ)) * Nat.primeCounting N) := by
      simpa only [mul_assoc] using
        small_shift_filtered_freeze_le k N hNpos θ hθ T hd c hc hcenter
    _ ≤ (Nat.log 2 N : ℝ) ^ (2 * k) *
        ((2 * N / Real.log N ^ 2) * (δ / 24)) :=
      mul_le_mul_of_nonneg_left hbudget (by positivity)
    _ = _ := by ring

/-- Gallagher 1975 p.134 display 3. Embed exponent pairs with entries below m
into a low shift box. Raise the first tuple by 2m and keep the second tuple below m.
Every resulting difference is positive and at most `2 ^ (3m + 1)`. -/
theorem small_shift_box_embedding (m L : ℕ) (hL : 3 * m ≤ L) :
    ∃ f : Decomp1532a.pairs 2 m → Decomp1532a.pairs 2 L,
      Function.Injective f ∧ ∀ x, 0 < Decomp1532a.dif (f x) ∧
        Decomp1532a.dif (f x) ≤ (2 : ℤ) ^ (3 * m + 1) := by
  let f : Decomp1532a.pairs 2 m → Decomp1532a.pairs 2 L := fun x =>
    ((fun i => ⟨(x.1 i : ℕ) + 2 * m, by have h := (x.1 i).isLt; omega⟩),
      fun i => ⟨(x.2 i : ℕ), by have h := (x.2 i).isLt; omega⟩)
  refine ⟨f, ?_, ?_⟩
  · intro x y h
    apply Prod.ext
    · funext i
      apply Fin.ext
      have hi := congrArg (fun z : Decomp1532a.pairs 2 L => (z.1 i : ℕ)) h
      dsimp [f] at hi
      omega
    · funext i
      apply Fin.ext
      exact congrArg (fun z : Decomp1532a.pairs 2 L => (z.2 i : ℕ)) h
  · intro x
    have hs2 : U1434Lemma21.sv (f x).2 = U1434Lemma21.sv x.2 := rfl
    have hlow : U1434Lemma21.sv (f x).2 ≤ 2 * 2 ^ m := by
      rw [hs2]
      exact U1434Lemma21.sv_le x.2
    have hfirst_low : 2 * 2 ^ (2 * m + 1) ≤ U1434Lemma21.sv (f x).1 := by
      change 2 * 2 ^ (2 * m + 1) ≤ ∑ i : Fin 2, 2 ^ ((x.1 i : ℕ) + 2 * m + 1)
      calc
        _ = ∑ _i : Fin 2, 2 ^ (2 * m + 1) := by simp [two_mul]
        _ ≤ _ := Finset.sum_le_sum fun i _ =>
          Nat.pow_le_pow_right (by norm_num) (by omega)
    have hfirst_up : U1434Lemma21.sv (f x).1 ≤ 2 * 2 ^ (3 * m) := by
      change (∑ i : Fin 2, 2 ^ ((x.1 i : ℕ) + 2 * m + 1)) ≤ 2 * 2 ^ (3 * m)
      calc
        _ ≤ ∑ _i : Fin 2, 2 ^ (3 * m) := Finset.sum_le_sum fun i _ =>
          Nat.pow_le_pow_right (by norm_num) (by have h := (x.1 i).isLt; omega)
        _ = _ := by simp [two_mul]
    have hpow : (2 : ℕ) ^ m < 2 ^ (2 * m + 1) :=
      Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hstrict : U1434Lemma21.sv (f x).2 < U1434Lemma21.sv (f x).1 := by omega
    constructor
    · exact sub_pos.mpr (by exact_mod_cast hstrict)
    · have hu : (U1434Lemma21.sv (f x).1 : ℤ) ≤ 2 * 2 ^ (3 * m) := by
        exact_mod_cast hfirst_up
      have hz : (0 : ℤ) ≤ U1434Lemma21.sv (f x).2 := by positivity
      change (U1434Lemma21.sv (f x).1 : ℤ) - U1434Lemma21.sv (f x).2 ≤ _
      rw [pow_succ]
      nlinarith

/-- Gallagher 1975 p.134 display 3 and the task's first range cut. At theta equal
to one quarter, the smallest range contains a fixed positive fraction of all exponent
pairs along an explicit sequence of N. Thus tuple counting alone gives no vanishing
fraction on this range. This is not a claim about the prime correlation error. -/
theorem first_range_box_density (m : ℕ) (hm : 1 ≤ m) :
    let L : ℕ := 32 * (3 * m + 1)
    let N : ℕ := 2 ^ L
    let T : Finset (Decomp1532a.pairs 2 L) := Finset.univ.filter (fun x =>
      Decomp1532a.dif x ≠ 0 ∧ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 32 : ℝ) ∧
        |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ) ∧
        |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ))
    m ^ 4 ≤ T.card ∧ L ^ 4 ≤ 128 ^ 4 * T.card := by
  classical
  let L : ℕ := 32 * (3 * m + 1)
  let N : ℕ := 2 ^ L
  let T : Finset (Decomp1532a.pairs 2 L) := Finset.univ.filter (fun x =>
    Decomp1532a.dif x ≠ 0 ∧ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 32 : ℝ) ∧
      |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ) ∧
      |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ))
  change m ^ 4 ≤ T.card ∧ L ^ 4 ≤ 128 ^ 4 * T.card
  have hL : 3 * m ≤ L := by dsimp [L]; omega
  obtain ⟨f, hf, hbox⟩ := small_shift_box_embedding m L hL
  have hN1 : (1 : ℝ) ≤ N := by
    have h : (1 : ℕ) ≤ N := by
      dsimp [N]
      exact Nat.one_le_pow _ _ (by norm_num)
    exact_mod_cast h
  have hcut : (N : ℝ) ^ (1 / 32 : ℝ) = (2 : ℝ) ^ (3 * m + 1) := by
    simp only [N, Nat.cast_pow, Nat.cast_ofNat]
    rw [← Real.rpow_natCast_mul (by norm_num : (0 : ℝ) ≤ 2) L (1 / 32 : ℝ),
      ← Real.rpow_natCast]
    congr 1
    dsimp [L]
    push_cast
    ring
  have hmaps : Set.MapsTo f (Finset.univ : Finset (Decomp1532a.pairs 2 m)) T := by
    intro x _hx
    have hp : (0 : ℝ) < Decomp1532a.dif (f x) := by exact_mod_cast (hbox x).1
    have hb : |(Decomp1532a.dif (f x) : ℝ)| ≤ (N : ℝ) ^ (1 / 32 : ℝ) := by
      rw [abs_of_pos hp, hcut]
      exact_mod_cast (hbox x).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (ne_of_gt (hbox x).1), hb,
      hb.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)),
      hb.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num))⟩
  have hcard : m ^ 4 ≤ T.card := by
    have h := Finset.card_le_card_of_injOn f hmaps hf.injOn
    simpa [Decomp1532a.pairs, ← pow_add] using h
  have hmax : L ≤ 128 * m := by dsimp [L]; omega
  refine ⟨hcard, ?_⟩
  calc
    L ^ 4 ≤ (128 * m) ^ 4 := Nat.pow_le_pow_left hmax 4
    _ = 128 ^ 4 * m ^ 4 := mul_pow _ _ _
    _ ≤ 128 ^ 4 * T.card := Nat.mul_le_mul_left _ hcard

/-- Gallagher 1975 p.134 display 3 and the task's first range cut. The number of
pairs in the eighth range at theta equal to one quarter and k equal to two is not little o
of the total number of pairs. This rules out a proof by a vanishing tuple fraction alone.
It does not refute the averaged prime correlation estimate. -/
theorem first_range_count_not_littleO :
    let R : ℕ → ℝ := fun N =>
      (((Finset.univ : Finset (Decomp1532a.pairs 2 (Nat.log 2 N))).filter (fun x =>
        Decomp1532a.dif x ≠ 0 ∧ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 32 : ℝ) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ) ∧
          |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ))).card : ℝ)
    ¬ Asymptotics.IsLittleO atTop R (fun N => (Nat.log 2 N : ℝ) ^ 4) := by
  classical
  let R : ℕ → ℝ := fun N =>
    (((Finset.univ : Finset (Decomp1532a.pairs 2 (Nat.log 2 N))).filter (fun x =>
      Decomp1532a.dif x ≠ 0 ∧ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 32 : ℝ) ∧
        |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ) ∧
        |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ))).card : ℝ)
  change ¬ Asymptotics.IsLittleO atTop R (fun N => (Nat.log 2 N : ℝ) ^ 4)
  intro h
  let ε : ℝ := 1 / (2 * 128 ^ 4)
  obtain ⟨Nk, hNk⟩ := eventually_atTop.mp (h.bound (by dsimp [ε]; positivity : 0 < ε))
  let m := max Nk 1
  let L := 32 * (3 * m + 1)
  let N : ℕ := 2 ^ L
  let T : Finset (Decomp1532a.pairs 2 L) := Finset.univ.filter (fun x =>
    Decomp1532a.dif x ≠ 0 ∧ |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 32 : ℝ) ∧
      |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 8 : ℝ) ∧
      |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (1 / 4 : ℝ))
  have hm : 1 ≤ m := le_max_right _ _
  have hmNk : Nk ≤ m := le_max_left _ _
  have hmL : m ≤ L := by dsimp [L]; omega
  have hNL : L < N := L.lt_two_pow_self
  have hNNk : Nk ≤ N := by omega
  have hlog : Nat.log 2 N = L := by
    dsimp [N]
    exact Nat.log_pow (by norm_num) L
  have hR : R N = (T.card : ℝ) := by
    dsimp [R]
    rw [hlog]
  have hdensity : L ^ 4 ≤ 128 ^ 4 * T.card := (first_range_box_density m hm).2
  have hd : (L : ℝ) ^ 4 ≤ (128 : ℝ) ^ 4 * (T.card : ℝ) := by exact_mod_cast hdensity
  have hb : (T.card : ℝ) ≤ ε * (L : ℝ) ^ 4 := by
    have hh := hNk N hNNk
    rw [hR, hlog, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Nat.cast_nonneg _), abs_of_nonneg (by positivity)] at hh
    exact hh
  have hLp : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hpos : (0 : ℝ) < (L : ℝ) ^ 4 := pow_pos hLp _
  have hcoeff : (128 : ℝ) ^ 4 * ε = 1 / 2 := by norm_num [ε]
  have hbd : (128 : ℝ) ^ 4 * (T.card : ℝ) ≤ (1 / 2 : ℝ) * (L : ℝ) ^ 4 := by
    calc
      _ ≤ (128 : ℝ) ^ 4 * (ε * (L : ℝ) ^ 4) :=
        mul_le_mul_of_nonneg_left hb (by positivity)
      _ = _ := by rw [← mul_assoc, hcoeff]
  have hf := hd.trans hbd
  linarith only [hf, hpos]

/-- Gallagher 1975 p.127 displays 1 and 2 and the p.138 tuple expansion.
For every small shift filter, phase freezing preserves the little o remainder relative
to any chosen main term W. This is a reduction, not a proof of either remainder estimate. -/
theorem frozen_remainder_isLittleO_iff (k : ℕ) (θ : ℝ) (hθ : θ ≤ 1 / 4)
    (T : ∀ N : ℕ, Finset (Decomp1532a.pairs k (Nat.log 2 N)))
    (hd : ∀ N, ∀ x ∈ T N, |(Decomp1532a.dif x : ℝ)| ≤ (N : ℝ) ^ (θ / 2))
    (c : ℕ → ℝ → ℝ) (hc : ∀ N, Measurable (c N))
    (hcenter : ∀ N, ∀ α ∈ majorArcs N ((N : ℝ) ^ θ),
      ∃ q : ℕ, 1 ≤ q ∧ (q : ℝ) ≤ (N : ℝ) ^ θ ∧ ∃ a : ℕ,
        a ≤ q ∧ Nat.Coprime a q ∧ c N α = (a : ℝ) / q ∧
          |α - c N α| ≤ (N : ℝ) ^ θ / (q * N)) (W : ℕ → ℝ) :
    let A : ℕ → ℝ := fun N => ∑ x ∈ T N, ∫ α in majorArcs N ((N : ℝ) ^ θ),
      ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * α)).re
    let F : ℕ → ℝ := fun N => ∑ x ∈ T N, ∫ α in majorArcs N ((N : ℝ) ^ θ),
      ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * c N α)).re
    let M : ℕ → ℝ := fun N => 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2
    Asymptotics.IsLittleO atTop (fun N => A N - W N) M ↔
      Asymptotics.IsLittleO atTop (fun N => F N - W N) M := by
  let A : ℕ → ℝ := fun N => ∑ x ∈ T N, ∫ α in majorArcs N ((N : ℝ) ^ θ),
    ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * α)).re
  let F : ℕ → ℝ := fun N => ∑ x ∈ T N, ∫ α in majorArcs N ((N : ℝ) ^ θ),
    ‖LeanLab.Linnik.U7204.Sg N α‖ ^ 2 * (LeanLab.PNTPort.LargeSieve.e ((Decomp1532a.dif x : ℝ) * c N α)).re
  let M : ℕ → ℝ := fun N => 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2
  change Asymptotics.IsLittleO atTop (fun N => A N - W N) M ↔
    Asymptotics.IsLittleO atTop (fun N => F N - W N) M
  have hphase : Asymptotics.IsLittleO atTop (fun N => A N - F N) M := by
    apply Asymptotics.IsLittleO.of_bound
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := small_shift_filtered_freeze_eventually (24 * ε) (by positivity)
    filter_upwards [eventually_ge_atTop N₀] with N hN
    have hb := hN₀ N hN k θ hθ (T N) (hd N) (c N) (hc N) (hcenter N)
    rw [show 24 * ε / 24 = ε by ring] at hb
    change |A N - F N| ≤ M N * ε at hb
    have hM : 0 ≤ M N := by dsimp [M]; positivity
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hM]
    simpa only [mul_comm] using hb
  have hshift : Asymptotics.IsLittleO atTop
      (fun N => (A N - W N) - (F N - W N)) M :=
    hphase.congr_left (fun N => by ring)
  exact hshift.congr_of_sub

/-- Gallagher 1975 p.134 display 3 and all four task range predicates. At k equal
to two, theta equal to one quarter and N equal to `2 ^ 32`, each original filter
contains a nonzero shift. This checks every retained upper bound and every strict cut. -/
theorem four_original_filters_nonempty :
    let Q : ℝ → ℝ := fun r => ((2 ^ 32 : ℕ) : ℝ) ^ r
    ∃ x₁ x₂ x₃ x₄ : Decomp1532a.pairs 2 (Nat.log 2 (2 ^ 32)),
      (Decomp1532a.dif x₁ ≠ 0 ∧ |(Decomp1532a.dif x₁ : ℝ)| ≤ Q (1 / 32) ∧
        |(Decomp1532a.dif x₁ : ℝ)| ≤ Q (1 / 8) ∧ |(Decomp1532a.dif x₁ : ℝ)| ≤ Q (1 / 4)) ∧
      (Decomp1532a.dif x₂ ≠ 0 ∧ ¬ |(Decomp1532a.dif x₂ : ℝ)| ≤ Q (1 / 32) ∧
        |(Decomp1532a.dif x₂ : ℝ)| ≤ Q (1 / 16) ∧
        |(Decomp1532a.dif x₂ : ℝ)| ≤ Q (1 / 8) ∧ |(Decomp1532a.dif x₂ : ℝ)| ≤ Q (1 / 4)) ∧
      (Decomp1532a.dif x₃ ≠ 0 ∧ ¬ |(Decomp1532a.dif x₃ : ℝ)| ≤ Q (1 / 32) ∧
        ¬ |(Decomp1532a.dif x₃ : ℝ)| ≤ Q (1 / 16) ∧
        |(Decomp1532a.dif x₃ : ℝ)| ≤ Q (3 / 32) ∧
        |(Decomp1532a.dif x₃ : ℝ)| ≤ Q (1 / 8) ∧ |(Decomp1532a.dif x₃ : ℝ)| ≤ Q (1 / 4)) ∧
      (Decomp1532a.dif x₄ ≠ 0 ∧ ¬ |(Decomp1532a.dif x₄ : ℝ)| ≤ Q (1 / 32) ∧
        ¬ |(Decomp1532a.dif x₄ : ℝ)| ≤ Q (1 / 16) ∧
        ¬ |(Decomp1532a.dif x₄ : ℝ)| ≤ Q (3 / 32) ∧
        |(Decomp1532a.dif x₄ : ℝ)| ≤ Q (1 / 8) ∧ |(Decomp1532a.dif x₄ : ℝ)| ≤ Q (1 / 4)) := by
  dsimp only
  obtain ⟨x₁, x₂, x₃, x₄, hd₁, hd₂, hd₃, hd₄⟩ := four_nonzero_shift_instances
  obtain ⟨c₁, c₂, c₃, c₄⟩ := four_cut_values_instance
  have h₁ : ((2 ^ 32 : ℕ) : ℝ) ^ (1 / 32 : ℝ) = 2 := by
    convert c₁ using 1 <;> norm_num
  have h₂ : ((2 ^ 32 : ℕ) : ℝ) ^ (1 / 16 : ℝ) = 4 := by
    convert c₂ using 1 <;> norm_num
  have h₃ : ((2 ^ 32 : ℕ) : ℝ) ^ (3 / 32 : ℝ) = 8 := by
    convert c₃ using 1 <;> norm_num
  have h₄ : ((2 ^ 32 : ℕ) : ℝ) ^ (1 / 8 : ℝ) = 16 := by
    convert c₄ using 1 <;> norm_num
  have hg : (16 : ℝ) ≤ ((2 ^ 32 : ℕ) : ℝ) ^ (1 / 4 : ℝ) := by
    rw [← h₄]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  refine ⟨x₁, x₂, x₃, x₄, ?_⟩
  norm_num [hd₁, hd₂, hd₃, hd₄, h₁, h₂, h₃, h₄]

end LeanLab.Linnik.Decomp495a

#print axioms LeanLab.Linnik.Decomp495a.phase_travel_le

#print axioms LeanLab.Linnik.Decomp495a.phase_character_le

#print axioms LeanLab.Linnik.Decomp495a.phase_character_small_shift_le

#print axioms LeanLab.Linnik.Decomp495a.exists_measurable_arc_center

#print axioms LeanLab.Linnik.Decomp495a.weighted_phase_freeze_le

#print axioms LeanLab.Linnik.Decomp495a.logarithmic_phase_error_tendsto

#print axioms LeanLab.Linnik.Decomp495a.small_shift_phase_freeze_le

#print axioms LeanLab.Linnik.Decomp495a.four_nonzero_shift_instances

#print axioms LeanLab.Linnik.Decomp495a.four_cut_values_instance

#print axioms LeanLab.Linnik.Decomp495a.small_shift_filtered_freeze_le

#print axioms LeanLab.Linnik.Decomp495a.phase_freeze_budget_eventually

#print axioms LeanLab.Linnik.Decomp495a.small_shift_filtered_freeze_eventually

#print axioms LeanLab.Linnik.Decomp495a.small_shift_box_embedding

#print axioms LeanLab.Linnik.Decomp495a.first_range_box_density

#print axioms LeanLab.Linnik.Decomp495a.first_range_count_not_littleO

#print axioms LeanLab.Linnik.Decomp495a.frozen_remainder_isLittleO_iff

#print axioms LeanLab.Linnik.Decomp495a.four_original_filters_nonempty
