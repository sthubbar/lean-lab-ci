/-
MMS https://arxiv.org/abs/1610.02017v2 page 11 bottom Buchstab display.
Split of the two open limits of Decomp581a into a cited short interval
prime number theorem, a deterministic layer cake transfer for the fixed smooth
weight, a uniform rough cofactor estimate, a prime sum to integral passage and
a change of variables. AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp581a

namespace LeanLab.Ternary.MMS.Task581
open Finset MeasureTheory

/-- LEAF: MMS page 11 bottom display, the prime number theorem in the reference
interval, uniformly over its subintervals. Class HARD for Codex.
CITED: this needs an error term beating x times exp of minus the square root of
log x, for example the Vinogradov Korobov zero free region or Huxley's short
interval theorem. The lab StrongPNT envelope is too weak, see
Task571.pnt_envelope_not_half_referenceLength. Open subintervals are used so
that the layer cake transfer applies directly. -/
theorem shortIntervalPNT_reference :
    ∀ ε : ℝ, 0 < ε → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ a b : ℝ, x ≤ a → a ≤ b →
      b ≤ x + Task379.referenceLength x →
      |Real.log x * (((ints x (x + Task379.referenceLength x)).filter
          (fun n : ℕ => n.Prime ∧ a < (n : ℝ) ∧ (n : ℝ) < b)).card : ℝ) - (b - a)| ≤
        ε * Task379.referenceLength x := by
  sorry

/-- Layer cake plan step one: the profile is symmetric about one half.
MMS page 11, the fixed smooth g1. -/
theorem profile_symm (s : ℝ) :
    expNegInvGlue (1 - s) * expNegInvGlue (1 - (1 - s)) = expNegInvGlue s * expNegInvGlue (1 - s) := by
  rw [sub_sub_cancel, mul_comm]

/-- Layer cake plan step one: the profile increases on the left half, so
superlevel sets are intervals. MMS page 11, the fixed smooth g1. -/
theorem profile_mono_left {s t : ℝ} (hst : s ≤ t) (ht : t ≤ 1 / 2) :
    expNegInvGlue s * expNegInvGlue (1 - s) ≤ expNegInvGlue t * expNegInvGlue (1 - t) := by
  rcases le_or_gt s 0 with hs | hs
  · rw [expNegInvGlue.zero_of_nonpos hs, zero_mul]
    exact mul_nonneg (expNegInvGlue.nonneg _) (expNegInvGlue.nonneg _)
  have ht0 : 0 < t := lt_of_lt_of_le hs hst
  have h1s : 0 < 1 - s := by linarith
  have h1t : 0 < 1 - t := by linarith
  simp only [expNegInvGlue, not_le.mpr hs, not_le.mpr ht0, not_le.mpr h1s, not_le.mpr h1t,
    ite_false, ← Real.exp_add]
  apply Real.exp_le_exp.mpr
  have key : s * (1 - s) ≤ t * (1 - t) := by nlinarith
  have e1 : -s⁻¹ + -(1 - s)⁻¹ = -(s * (1 - s))⁻¹ := by field_simp; ring
  have e2 : -t⁻¹ + -(1 - t)⁻¹ = -(t * (1 - t))⁻¹ := by field_simp; ring
  rw [e1, e2, neg_le_neg_iff]
  exact inv_anti₀ (by positivity) key

/-- Layer cake plan step one: the profile decreases on the right half.
MMS page 11, the fixed smooth g1. -/
theorem profile_anti_right {s t : ℝ} (hs : 1 / 2 ≤ s) (hst : s ≤ t) :
    expNegInvGlue t * expNegInvGlue (1 - t) ≤ expNegInvGlue s * expNegInvGlue (1 - s) := by
  have h := profile_mono_left (s := 1 - t) (t := 1 - s) (by linarith) (by linarith)
  rwa [profile_symm, profile_symm] at h

section S145_weightedPrime_layerCake_bound
open Finset MeasureTheory

/-- The fixed profile f of the reference weight. -/
noncomputable def s145_prof (s : ℝ) : ℝ := expNegInvGlue s * expNegInvGlue (1 - s)

theorem s145_prof_contDiff : ContDiff ℝ 1 s145_prof := by
  unfold s145_prof
  exact (expNegInvGlue.contDiff).mul (expNegInvGlue.contDiff.comp (contDiff_const.sub contDiff_id))

theorem s145_prof_deriv_cont : Continuous (deriv s145_prof) :=
  s145_prof_contDiff.continuous_deriv le_rfl

theorem s145_weight_hasDerivAt (x L t : ℝ) (hL : L = Task379.referenceLength x) :
    HasDerivAt (Task379.referenceWeight x)
      (deriv s145_prof ((t - x) / L) * (1 / L)) t := by
  have hw : Task379.referenceWeight x = fun t => s145_prof ((t - x) / L) := by
    funext t; subst hL; rfl
  rw [hw]
  have hin : HasDerivAt (fun t : ℝ => (t - x) / L) (1 / L) t :=
    ((hasDerivAt_id t).sub_const x).div_const L
  have hf : HasDerivAt s145_prof (deriv s145_prof ((t - x) / L)) ((t - x) / L) :=
    (s145_prof_contDiff.differentiable (by norm_num) _).hasDerivAt
  exact hf.comp t hin

theorem s145_absDeriv_integral (x L : ℝ) (hL : 0 < L) :
    (∫ t in x..(x + L), |deriv s145_prof ((t - x) / L) * (1 / L)|) =
      ∫ s in (0:ℝ)..1, |deriv s145_prof s| := by
  have e : ∀ t : ℝ, |deriv s145_prof ((t - x) / L) * (1 / L)| =
      (1 / L) * |deriv s145_prof (t / L - x / L)| := by
    intro t
    rw [abs_mul, abs_of_pos (by positivity : (0:ℝ) < 1 / L), mul_comm, sub_div]
  simp_rw [e]
  rw [intervalIntegral.integral_const_mul]
  have h := intervalIntegral.integral_comp_div_sub
    (fun s => |deriv s145_prof s|) (c := L) (d := x / L) hL.ne' (a := x) (b := x + L)
  rw [h]
  have e1 : x / L - x / L = 0 := sub_self _
  have e2 : (x + L) / L - x / L = 1 := by field_simp; ring
  rw [e1, e2, smul_eq_mul]
  field_simp

theorem weightedPrime_layerCake_bound_s145 :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 1 ≤ x → ∀ ε : ℝ, 0 ≤ ε →
      (∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
        |Real.log x * (((ints x (x + Task379.referenceLength x)).filter
          (fun n : ℕ => n.Prime ∧ a < (n : ℝ) ∧ (n : ℝ) < b)).card : ℝ) - (b - a)| ≤
          ε * Task379.referenceLength x) →
      |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
          Task379.referenceWeight x n * ρ n) -
        ∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t| ≤
        M * ε * Task379.referenceLength x := by
  set K := ∫ s in (0:ℝ)..1, |deriv s145_prof s| with hK
  have hK0 : 0 ≤ K := intervalIntegral.integral_nonneg zero_le_one (fun _ _ => abs_nonneg _)
  refine ⟨K + 1, by linarith, fun x hx ε hε hyp => ?_⟩
  have hx0 : (0:ℝ) < x := by linarith
  set L := Task379.referenceLength x with hLdef
  have hL : 0 < L := Task379.referenceLength_pos hx0
  set w := Task379.referenceWeight x with hwdef
  set wd : ℝ → ℝ := fun t => deriv s145_prof ((t - x) / L) * (1 / L) with hwd
  have hwD : ∀ t, HasDerivAt w (wd t) t := fun t => s145_weight_hasDerivAt x L t hLdef
  have hwdc : Continuous wd := by
    simp only [hwd]
    exact (s145_prof_deriv_cont.comp ((continuous_id.sub continuous_const).div_const L)).mul
      continuous_const
  have hwdi : ∀ a b : ℝ, IntervalIntegrable wd volume a b := fun a b => hwdc.intervalIntegrable a b
  have hw0 : ∀ t, t ≤ x ∨ x + L ≤ t → w t = 0 := fun t ht =>
    Task379.referenceWeight_zero_outside hx0 ht
  set I := ints x (x + L) with hI
  have hmem : ∀ n ∈ I, x ≤ (n : ℝ) ∧ (n : ℝ) ≤ x + L := by
    intro n hn
    simp only [hI, ints, Finset.mem_Icc] at hn
    exact ⟨(Nat.ceil_le).mp hn.1, (Nat.le_floor_iff (by linarith)).mp hn.2⟩
  set T := I.filter (fun n : ℕ => n.Prime ∧ x < (n : ℝ)) with hT
  -- step 1: the weighted sum is a sum over T
  have hsum1 : (∑ n ∈ I, w n * ρ n) = ∑ n ∈ T, w n := by
    rw [hT, Finset.sum_filter]
    refine Finset.sum_congr rfl fun n hn => ?_
    by_cases hp : n.Prime
    · by_cases hxn : x < (n : ℝ)
      · simp [ρ, hp, hxn]
      · have : (n : ℝ) = x := le_antisymm (not_lt.mp hxn) (hmem n hn).1
        simp [ρ, hp, hxn, hw0 n (Or.inl this.le)]
    · simp [ρ, hp]
  -- step 2: each term is minus an integral of the indicator of the derivative
  have hterm : ∀ n ∈ T, w n =
      -∫ t in x..(x + L), (Set.Ioi (n : ℝ)).indicator wd t := by
    intro n hn
    have hnI : n ∈ I := (Finset.mem_filter.mp hn).1
    have hxn : x < (n : ℝ) := (Finset.mem_filter.mp hn).2.2
    have hnL : (n : ℝ) ≤ x + L := (hmem n hnI).2
    have hii : ∀ a b : ℝ, IntervalIntegrable ((Set.Ioi (n : ℝ)).indicator wd) volume a b :=
      fun a b => by
        have := (hwdi a b)
        exact ⟨this.1.indicator measurableSet_Ioi, this.2.indicator measurableSet_Ioi⟩
    rw [← intervalIntegral.integral_add_adjacent_intervals (hii x n) (hii n (x + L))]
    have h1 : (∫ t in x..(n : ℝ), (Set.Ioi (n : ℝ)).indicator wd t) = 0 := by
      rw [← intervalIntegral.integral_zero (a := x) (b := (n:ℝ)) (μ := volume)]
      refine intervalIntegral.integral_congr fun t ht => ?_
      rw [Set.uIcc_of_le hxn.le] at ht
      simp [Set.indicator_of_notMem (show t ∉ Set.Ioi (n:ℝ) from fun h => absurd ht.2 (not_le.mpr h))]
    have h2 : (∫ t in (n : ℝ)..(x + L), (Set.Ioi (n : ℝ)).indicator wd t) =
        ∫ t in (n : ℝ)..(x + L), wd t := by
      refine intervalIntegral.integral_congr_ae (Filter.Eventually.of_forall fun t ht => ?_)
      rw [Set.uIoc_of_le hnL] at ht
      exact Set.indicator_of_mem (show t ∈ Set.Ioi (n:ℝ) from ht.1) wd
    have h3 : (∫ t in (n : ℝ)..(x + L), wd t) = w (x + L) - w n :=
      intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hwD t) (hwdi _ _)
    rw [h1, h2, h3, hw0 (x + L) (Or.inr le_rfl)]
    ring
  -- step 3: integration by parts for the weight integral
  have hibp : (∫ t in x..(x + L), w t) = -∫ t in x..(x + L), (t - x) * wd t := by
    have h := intervalIntegral.integral_mul_deriv_eq_deriv_mul (a := x) (b := x + L)
      (u := fun t => t - x) (u' := fun _ => (1:ℝ)) (v := w) (v' := wd)
      (fun t _ => (hasDerivAt_id t).sub_const x) (fun t _ => hwD t)
      intervalIntegrable_const (hwdi _ _)
    simp only [one_mul] at h
    rw [h, hw0 (x + L) (Or.inr le_rfl), hw0 x (Or.inl le_rfl)]
    ring
  -- step 4: combine into one integral
  set F : ℝ → ℝ := fun t => Real.log x * (∑ n ∈ T, (Set.Ioi (n : ℝ)).indicator wd t) -
    (t - x) * wd t with hF
  have hiiT : ∀ n ∈ T, IntervalIntegrable ((Set.Ioi (n : ℝ)).indicator wd) volume x (x + L) :=
    fun n _ => by
      have := (hwdi x (x + L))
      exact ⟨this.1.indicator measurableSet_Ioi, this.2.indicator measurableSet_Ioi⟩
  have hA : IntervalIntegrable (fun t => Real.log x * ∑ n ∈ T, (Set.Ioi (n : ℝ)).indicator wd t)
      volume x (x + L) := by
    have := (IntervalIntegrable.sum T hiiT).const_mul (Real.log x)
    simpa [Finset.sum_apply] using this
  have hB : IntervalIntegrable (fun t => (t - x) * wd t) volume x (x + L) :=
    ((continuous_id.sub continuous_const).mul hwdc).intervalIntegrable _ _
  have hs : (∫ t in x..(x + L), F t) = Real.log x * (∑ n ∈ T,
      ∫ t in x..(x + L), (Set.Ioi (n : ℝ)).indicator wd t) -
      ∫ t in x..(x + L), (t - x) * wd t := by
    simp only [hF]
    rw [intervalIntegral.integral_sub hA hB, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_finsetSum hiiT]
  have hcomb : Real.log x * (∑ n ∈ I, w n * ρ n) - ∫ t in x..(x + L), w t =
      -∫ t in x..(x + L), F t := by
    rw [hsum1, hibp, Finset.sum_congr rfl hterm, hs, Finset.sum_neg_distrib]
    ring
  -- step 5: pointwise bound
  have hpt : ∀ t ∈ Set.Ioc x (x + L), ‖F t‖ ≤ |wd t| * (ε * L) := by
    intro t ht
    have hP : (∑ n ∈ T, (Set.Ioi (n : ℝ)).indicator wd t) =
        wd t * ((I.filter (fun n : ℕ => n.Prime ∧ x < (n : ℝ) ∧ (n : ℝ) < t)).card : ℝ) := by
      have e : ∀ n ∈ T, (Set.Ioi (n : ℝ)).indicator wd t =
          wd t * (if (n : ℝ) < t then (1:ℝ) else 0) := by
        intro n _
        by_cases h : (n : ℝ) < t
        · simp [h]
        · simp [h]
      rw [Finset.sum_congr rfl e, ← Finset.mul_sum, Finset.sum_boole, hT, Finset.filter_filter]
      congr 3
      ext n
      simp only [Finset.mem_filter, and_assoc]
    have hb := hyp x t le_rfl ht.1.le ht.2
    simp only [hF, Real.norm_eq_abs]
    rw [hP]
    have : Real.log x * (wd t * ((I.filter (fun n : ℕ => n.Prime ∧ x < (n : ℝ) ∧
        (n : ℝ) < t)).card : ℝ)) - (t - x) * wd t =
        wd t * (Real.log x * ((I.filter (fun n : ℕ => n.Prime ∧ x < (n : ℝ) ∧
        (n : ℝ) < t)).card : ℝ) - (t - x)) := by ring
    rw [this, abs_mul]
    exact mul_le_mul_of_nonneg_left hb (abs_nonneg _)
  have hbound := intervalIntegral.norm_integral_le_of_norm_le (μ := volume) (f := F)
    (show x ≤ x + L by linarith) (Filter.Eventually.of_forall hpt)
    ((hwdc.abs.mul continuous_const).intervalIntegrable _ _)
  rw [intervalIntegral.integral_mul_const, hwd, s145_absDeriv_integral x L hL, ← hK] at hbound
  rw [hcomb, abs_neg]
  rw [Real.norm_eq_abs] at hbound
  have hεL : 0 ≤ ε * L := mul_nonneg hε hL.le
  nlinarith

end S145_weightedPrime_layerCake_bound

/-- LEAF: MMS page 11 bottom display, layer cake step for the weighted prime
sum. Class MEDIUM for Open Math OS. The profile is unimodal and vanishes at the
ends, so its superlevel sets are open subintervals; integrating the interval
hypothesis over levels bounds the weighted error by the profile maximum M. -/
theorem weightedPrime_layerCake_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ x : ℝ, 1 ≤ x → ∀ ε : ℝ, 0 ≤ ε →
      (∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
        |Real.log x * (((ints x (x + Task379.referenceLength x)).filter
          (fun n : ℕ => n.Prime ∧ a < (n : ℝ) ∧ (n : ℝ) < b)).card : ℝ) - (b - a)| ≤
          ε * Task379.referenceLength x) →
      |Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
          Task379.referenceWeight x n * ρ n) -
        ∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t| ≤
        M * ε * Task379.referenceLength x := by
  exact weightedPrime_layerCake_bound_s145

/-- Change of variables for the rescaled profile. MMS page 11, g1 in
Proposition 5.1 rescaled to the reference interval. -/
theorem profile_rescale_integral (x L : ℝ) (hL : 0 < L) :
    (∫ t in x..(x + L), expNegInvGlue ((t - x) / L) * expNegInvGlue (1 - (t - x) / L)) =
      L * ∫ s in (0:ℝ)..1, expNegInvGlue s * expNegInvGlue (1 - s) := by
  have h := intervalIntegral.integral_comp_div_sub
    (fun s => expNegInvGlue s * expNegInvGlue (1 - s)) (c := L) (d := x / L) hL.ne'
    (a := x) (b := x + L)
  simp only [sub_div] at *
  rw [h]
  have e1 : x / L - x / L = 0 := sub_self _
  have e2 : (x + L) / L - x / L = 1 := by field_simp; ring
  rw [e1, e2, smul_eq_mul]

/-- The fixed profile has positive integral. MMS page 11, g1 nonzero. -/
theorem profile_integral_pos :
    0 < ∫ s in (0:ℝ)..1, expNegInvGlue s * expNegInvGlue (1 - s) := by
  have hc : Continuous (fun s : ℝ => expNegInvGlue s * expNegInvGlue (1 - s)) := by
    fun_prop
  apply intervalIntegral.intervalIntegral_pos_of_pos_on (hc.intervalIntegrable _ _) _ zero_lt_one
  intro s hs
  exact mul_pos (expNegInvGlue.pos_of_pos hs.1) (expNegInvGlue.pos_of_pos (by linarith [hs.2]))

/-- The weight integral is the length times the fixed profile integral I.
MMS page 11, change of variables. Proved from the two lemmas above. -/
theorem weightIntegral_scaling :
    ∃ I : ℝ, 0 < I ∧ ∀ x : ℝ, 1 ≤ x →
      (∫ t in x..(x + Task379.referenceLength x), Task379.referenceWeight x t) =
        I * Task379.referenceLength x := by
  refine ⟨_, profile_integral_pos, fun x hx => ?_⟩
  have hL : 0 < Task379.referenceLength x := by
    unfold Task379.referenceLength
    have : (0 : ℝ) < x := by linarith
    positivity
  unfold Task379.referenceWeight
  rw [profile_rescale_integral x _ hL, mul_comm]

theorem referenceLength_pos_of_one_le {x : ℝ} (hx : 1 ≤ x) :
    0 < Task379.referenceLength x := by
  unfold Task379.referenceLength
  have : (0 : ℝ) < x := by linarith
  positivity

/-- primeMean_transfer from the layer cake bound and the integral scaling,
with C equal to M over I. CONDITIONAL ON weightedPrime_layerCake_bound and
weightIntegral_scaling. MMS page 11 bottom display. -/
theorem primeMean_transfer_of_leaves :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → ∀ ε : ℝ, 0 ≤ ε →
      (∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
        |Real.log x * (((ints x (x + Task379.referenceLength x)).filter
          (fun n : ℕ => n.Prime ∧ a < (n : ℝ) ∧ (n : ℝ) < b)).card : ℝ) - (b - a)| ≤
          ε * Task379.referenceLength x) →
      |primeMean x - 1| ≤ C * ε := by
  obtain ⟨M, hM, hB⟩ := weightedPrime_layerCake_bound
  obtain ⟨I, hI, hS⟩ := weightIntegral_scaling
  refine ⟨M / I, div_pos hM hI, fun x hx ε hε hyp => ?_⟩
  have hL := referenceLength_pos_of_one_le hx
  have hb := hB x hx ε hε hyp
  have hs := hS x hx
  rw [hs] at hb
  have hIL : 0 < I * Task379.referenceLength x := mul_pos hI hL
  have he : primeMean x - 1 =
      (Real.log x * (∑ n ∈ ints x (x + Task379.referenceLength x),
          Task379.referenceWeight x n * ρ n) - I * Task379.referenceLength x) /
        (I * Task379.referenceLength x) := by
    unfold primeMean
    rw [hs]
    field_simp
  rw [he, abs_div, abs_of_pos hIL, div_le_iff₀ hIL]
  calc _ ≤ M * ε * Task379.referenceLength x := hb
    _ = M / I * ε * (I * Task379.referenceLength x) := by field_simp

/-- MMS page 11 bottom display, passage from interval prime counts to the
smooth weighted prime sum. Pass 6: proved from primeMean_transfer_of_leaves,
CONDITIONAL ON the leaf weightedPrime_layerCake_bound.
Deterministic layer cake step: the reference weight is unimodal with value zero
at both ends, so each superlevel set is an open subinterval, and the weighted
sum and the weight integral are integrals over levels of counts and lengths.
One may take C equal to the maximum of the profile over its integral. -/
theorem primeMean_transfer :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, 1 ≤ x → ∀ ε : ℝ, 0 ≤ ε →
      (∀ a b : ℝ, x ≤ a → a ≤ b → b ≤ x + Task379.referenceLength x →
        |Real.log x * (((ints x (x + Task379.referenceLength x)).filter
          (fun n : ℕ => n.Prime ∧ a < (n : ℝ) ∧ (n : ℝ) < b)).card : ℝ) - (b - a)| ≤
          ε * Task379.referenceLength x) →
      |primeMean x - 1| ≤ C * ε :=
  primeMean_transfer_of_leaves

/-- The weighted prime limit from the two leaves above.
MMS page 11 bottom display. CONDITIONAL ON shortIntervalPNT_reference
and primeMean_transfer. -/
theorem primeMean_limit_of_leaves :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → |primeMean x - 1| ≤ δ := by
  intro δ hδ
  obtain ⟨C, hC, hT⟩ := primeMean_transfer
  obtain ⟨X, hX⟩ := shortIntervalPNT_reference (δ / C) (by positivity)
  refine ⟨max 1 X, fun x hx => ?_⟩
  have h := hT x ((le_max_left _ _).trans hx) (δ / C) (by positivity)
    (fun a b ha hab hb => hX x ((le_max_right _ _).trans hx) a b ha hab hb)
  have he : C * (δ / C) = δ := by field_simp
  linarith

/-- The frozen Buchstab main term of the composite rough numbers.
MMS page 11 bottom display: for each least prime factor p from x to the one
quarter up to the square root of x, the cofactors rough at p have density
buchstab of log of x over p divided by log p, over log p. New definition,
needed to separate the rough cofactor estimate from the prime sum. -/
noncomputable def compositeModelSum (x : ℝ) : ℝ :=
  Real.log x * ∑ p ∈ range (⌊x⌋₊ + 1),
    if p.Prime ∧ x ^ (1 / 4 : ℝ) ≤ p ∧ (p : ℝ) ^ 2 ≤ x then
      Task571.buchstabModel (Real.log (x / p) / Real.log p) / (p * Real.log p) else 0

/-- LEAF: MMS page 11 bottom display, Buchstab identity plus the prime number
theorem for the rough cofactors n over p in the rescaled reference interval,
uniformly in the least prime p. Class HARD for Codex. CITED short interval
input as in shortIntervalPNT_reference, applied to primes and to products of
two primes at least p. The finite bucket identity is compositeRough_buchstab. -/
theorem compositeMean_model :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |compositeMean x - compositeModelSum x| ≤ δ := by
  sorry

section S145_compositeModelSum_limit
open Finset MeasureTheory

/-- Legendre, log n factorial as a prime sum. Port of RSLogSum.log_factorial_eq. -/
theorem s145_log_factorial_eq (n : ℕ) :
    Real.log ((n.factorial : ℕ) : ℝ) =
      ∑ p ∈ Nat.primesLE n, ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
  rw [Real.log_nat_eq_sum_factorization]
  apply Finsupp.sum_of_support_subset
  · intro p hp
    rw [Nat.support_factorization] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hle : p ≤ n := (Nat.Prime.dvd_factorial hpp).1 (Nat.dvd_of_mem_primeFactors hp)
    rw [Nat.primesLE_eq_filter_Icc_zero, mem_filter, mem_Icc]
    exact ⟨⟨Nat.zero_le _, hle⟩, hpp⟩
  · intro p _; simp

/-- Upper half of Mertens' first theorem in a weak form. -/
theorem s145_C_le (n : ℕ) (hn : 1 ≤ n) :
    ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ Real.log n + 2 := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hleg := s145_log_factorial_eq n
  have hlow : ∀ p ∈ Nat.primesLE n,
      (n : ℝ) * (Real.log p / p) - Real.log p ≤
        ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p := by
    intro p hp
    rw [Nat.primesLE_eq_filter_Icc_zero, mem_filter] at hp
    have hpp := hp.2
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hpp.pos
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
    have hv : n / p ≤ n.factorial.factorization p := by
      rw [Nat.factorization_factorial hpp (b := Nat.log p n + 2) (by omega)]
      have hsub : ({1} : Finset ℕ) ⊆ Ico 1 (Nat.log p n + 2) := by
        intro i hi; simp at hi; simp; omega
      calc n / p = ∑ i ∈ ({1} : Finset ℕ), n / p ^ i := by simp
        _ ≤ _ := sum_le_sum_of_subset hsub
    have hv' : (n : ℝ) / p - 1 ≤ ((n.factorial.factorization p : ℕ) : ℝ) := by
      have h1 : ((n / p : ℕ) : ℝ) ≤ ((n.factorial.factorization p : ℕ) : ℝ) := by
        exact_mod_cast hv
      have h2 : (n : ℝ) / p - 1 ≤ ((n / p : ℕ) : ℝ) := by
        have := Nat.lt_div_mul_add (a := n) hpp.pos
        have h3 : (n : ℝ) < ((n / p : ℕ) : ℝ) * p + p := by exact_mod_cast this
        rw [div_sub_one hp0.ne', div_le_iff₀ hp0]
        linarith
      linarith
    have := mul_le_mul_of_nonneg_right hv' hl
    have e : ((n : ℝ) / p - 1) * Real.log p = (n : ℝ) * (Real.log p / p) - Real.log p := by
      field_simp
    linarith
  have hsum := sum_le_sum hlow
  rw [sum_sub_distrib, ← mul_sum, ← hleg] at hsum
  have hθ : ∑ p ∈ Nat.primesLE n, Real.log p ≤ Real.log 4 * n := by
    rw [← Chebyshev.theta_eq_sum_primesLE_log]; exact Chebyshev.theta_le_log4_mul_x hn0.le
  have hfac : Real.log ((n.factorial : ℕ) : ℝ) ≤ n * Real.log n := by
    have h1 : ((n.factorial : ℕ) : ℝ) ≤ (n : ℝ) ^ n := by exact_mod_cast Nat.factorial_le_pow n
    have h2 := Real.log_le_log (by exact_mod_cast Nat.factorial_pos n) h1
    rwa [Real.log_pow] at h2
  have hl4 : Real.log 4 < 2 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.exp_one_gt_d9
    have e2 : Real.exp 2 = Real.exp 1 * Real.exp 1 := by rw [← Real.exp_add]; norm_num
    nlinarith
  have : (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p ≤ (n : ℝ) * (Real.log n + 2) := by
    nlinarith
  exact le_of_mul_le_mul_left this hn0

theorem s145_inv_sqrt_tele (m : ℕ) (hm : 2 ≤ m) :
    1 / (Real.sqrt m * ((m : ℝ) - 1)) ≤ 3 * (1 / Real.sqrt ((m : ℝ) - 1) - 1 / Real.sqrt m) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  set a := Real.sqrt ((m : ℝ) - 1) with ha
  set b := Real.sqrt (m : ℝ) with hb
  have ha2 : a ^ 2 = (m : ℝ) - 1 := Real.sq_sqrt (by linarith)
  have hb2 : b ^ 2 = (m : ℝ) := Real.sq_sqrt (by linarith)
  have ha0 : 0 < a := Real.sqrt_pos.mpr (by linarith)
  have hb0 : 0 < b := Real.sqrt_pos.mpr (by linarith)
  have hab : a ≤ b := Real.sqrt_le_sqrt (by linarith)
  have hb2a : b ≤ 2 * a := by nlinarith
  rw [← ha2]
  rw [div_le_iff₀ (by positivity)]
  have key : 1 / a - 1 / b = 1 / (a * b * (a + b)) := by
    field_simp
    nlinarith
  rw [key]
  rw [show 3 * (1 / (a * b * (a + b))) * (b * a ^ 2) = 3 * a / (a + b) by field_simp]
  rw [le_div_iff₀ (by positivity)]
  linarith

theorem s145_log_term_le (m : ℕ) (hm : 2 ≤ m) :
    Real.log m / ((m : ℝ) * ((m : ℝ) - 1)) ≤
      6 * (1 / Real.sqrt ((m : ℝ) - 1) - 1 / Real.sqrt m) := by
  have hm' : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have hlog : Real.log m ≤ 2 * Real.sqrt m := by
    have := Real.log_le_rpow_div (x := (m : ℝ)) (by linarith) (show (0 : ℝ) < 1 / 2 by norm_num)
    rw [← Real.sqrt_eq_rpow] at this
    linarith
  have hs0 : 0 < Real.sqrt (m : ℝ) := Real.sqrt_pos.mpr (by linarith)
  have hss : Real.sqrt (m : ℝ) * Real.sqrt m = m := Real.mul_self_sqrt (by linarith)
  have h1 : Real.log m / ((m : ℝ) * ((m : ℝ) - 1)) ≤ 2 * (1 / (Real.sqrt m * ((m : ℝ) - 1))) := by
    have hm1 : (m : ℝ) - 1 ≠ 0 := by linarith
    rw [div_le_iff₀ (by nlinarith)]
    have e : 2 * (1 / (Real.sqrt m * ((m : ℝ) - 1))) * ((m : ℝ) * ((m : ℝ) - 1)) =
        2 * Real.sqrt m := by
      field_simp
      linarith [hss]
    rw [e]
    exact hlog
  have h2 := s145_inv_sqrt_tele m hm
  linarith

theorem s145_tele_Ioc (g : ℕ → ℝ) : ∀ n : ℕ, 1 ≤ n →
    ∑ m ∈ Ioc 1 n, (g (m - 1) - g m) = g 1 - g n := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base => simp
  | succ n hn ih =>
    rw [sum_Ioc_succ_top (by omega), ih]
    simp only [Nat.add_sub_cancel]
    ring

theorem s145_sum_log_div_pred_le (n : ℕ) :
    ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1)) ≤ 6 := by
  rcases Nat.lt_or_ge n 1 with h | h
  · have : n = 0 := by omega
    subst this
    rw [show Nat.primesLE 0 = ∅ by decide]
    simp
  have hsub : Nat.primesLE n ⊆ Ioc 1 n := by
    intro p hp
    rw [Nat.primesLE_eq_filter_Icc_zero, mem_filter, mem_Icc] at hp
    rw [mem_Ioc]; exact ⟨hp.2.one_lt, hp.1.2⟩
  have hnn : ∀ m ∈ Ioc 1 n, 0 ≤ Real.log m / ((m : ℝ) * ((m : ℝ) - 1)) := by
    intro m hm
    rw [mem_Ioc] at hm
    have : (2 : ℝ) ≤ m := by exact_mod_cast hm.1
    exact div_nonneg (Real.log_nonneg (by linarith)) (by nlinarith)
  calc ∑ p ∈ Nat.primesLE n, Real.log p / ((p : ℝ) * ((p : ℝ) - 1))
      ≤ ∑ m ∈ Ioc 1 n, Real.log m / ((m : ℝ) * ((m : ℝ) - 1)) :=
        sum_le_sum_of_subset_of_nonneg hsub (fun m hm _ => hnn m hm)
    _ ≤ ∑ m ∈ Ioc 1 n, 6 * ((fun k : ℕ => 1 / Real.sqrt (k : ℝ)) (m - 1) -
          (fun k : ℕ => 1 / Real.sqrt (k : ℝ)) m) := by
        apply sum_le_sum
        intro m hm
        rw [mem_Ioc] at hm
        have := s145_log_term_le m (by omega)
        simp only
        rw [Nat.cast_sub (by omega : 1 ≤ m)]
        simpa using this
    _ = 6 * (1 - 1 / Real.sqrt n) := by
        rw [← mul_sum, s145_tele_Ioc (fun k : ℕ => 1 / Real.sqrt (k : ℝ)) n h]
        simp
    _ ≤ 6 := by
        have : 0 ≤ 1 / Real.sqrt (n : ℝ) := by positivity
        linarith

theorem s145_log_factorial_ge (n : ℕ) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have hn : (0 : ℝ) < n := by exact_mod_cast h
  have hf : (0 : ℝ) < n.factorial := by exact_mod_cast Nat.factorial_pos n
  have h1 := Real.pow_div_factorial_le_exp (n : ℝ) hn.le n
  have h2 := Real.log_le_log (by positivity) h1
  rw [Real.log_div (by positivity) hf.ne', Real.log_pow, Real.log_exp] at h2
  linarith

/-- Lower half of Mertens' first theorem. Port of PNTSieve.Mertens.C_ge. -/
theorem s145_C_ge (n : ℕ) : Real.log n - 7 ≤ ∑ p ∈ Nat.primesLE n, Real.log p / p := by
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; simp
  have hn : (0 : ℝ) < n := by exact_mod_cast h
  have hleg := s145_log_factorial_eq n
  have hup : ∀ p ∈ Nat.primesLE n, ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p ≤
      (n : ℝ) * (Real.log p / p) + (n : ℝ) * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
    intro p hp
    rw [Nat.primesLE_eq_filter_Icc_zero, mem_filter] at hp
    have hpp := hp.2
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hv := Nat.factorization_factorial_le_div_pred hpp n
    have hv' : ((n.factorial.factorization p : ℕ) : ℝ) ≤ (n : ℝ) / ((p : ℝ) - 1) := by
      have h1 : ((n.factorial.factorization p : ℕ) : ℝ) ≤ ((n / (p - 1) : ℕ) : ℝ) := by
        exact_mod_cast hv
      refine h1.trans ?_
      have := Nat.cast_div_le (α := ℝ) (m := n) (n := p - 1)
      rwa [Nat.cast_sub hpp.one_le, Nat.cast_one] at this
    have hl : 0 ≤ Real.log p := Real.log_nonneg (by linarith)
    calc ((n.factorial.factorization p : ℕ) : ℝ) * Real.log p ≤
          (n : ℝ) / ((p : ℝ) - 1) * Real.log p :=
          mul_le_mul_of_nonneg_right hv' hl
      _ = (n : ℝ) * (Real.log p / p) + (n : ℝ) * (Real.log p / ((p : ℝ) * ((p : ℝ) - 1))) := by
          have hp1 : (p : ℝ) - 1 ≠ 0 := by linarith
          have hp0 : (p : ℝ) ≠ 0 := by linarith
          field_simp
          ring
  have hsum := sum_le_sum hup
  rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← hleg] at hsum
  have h6 := s145_sum_log_div_pred_le n
  have hlf := s145_log_factorial_ge n
  have : (n : ℝ) * (Real.log n - 7) ≤ (n : ℝ) * ∑ p ∈ Nat.primesLE n, Real.log p / p := by
    nlinarith
  exact le_of_mul_le_mul_left this hn


theorem s145_primesLE_split (g : ℕ → ℝ) {y w : ℕ} (hyw : y ≤ w) :
    ∑ p ∈ Nat.primesLE w, g p =
      ∑ p ∈ Nat.primesLE y, g p + ∑ p ∈ (Ioc y w).filter Nat.Prime, g p := by
  classical
  rw [Nat.primesLE_eq_filter_Icc_zero, Nat.primesLE_eq_filter_Icc_zero, ← sum_union]
  · congr 1
    ext n
    simp only [mem_union, mem_filter, mem_Icc, mem_Ioc]
    constructor
    · rintro ⟨⟨_, h⟩, hp⟩
      by_cases hny : n ≤ y
      · exact Or.inl ⟨⟨Nat.zero_le _, hny⟩, hp⟩
      · exact Or.inr ⟨⟨by omega, h⟩, hp⟩
    · rintro (⟨⟨_, h⟩, hp⟩ | ⟨⟨_, h⟩, hp⟩)
      · exact ⟨⟨Nat.zero_le _, by omega⟩, hp⟩
      · exact ⟨⟨Nat.zero_le _, h⟩, hp⟩
  · apply disjoint_left.mpr
    intro n h₁ h₂
    have h₁' := (mem_filter.mp h₁).1
    have h₂' := (mem_filter.mp h₂).1
    rw [mem_Icc] at h₁'
    rw [mem_Ioc] at h₂'
    omega

theorem s145_block_error (y w : ℕ) (hy : 1 ≤ y) (hyw : y ≤ w) :
    |(∑ p ∈ (Ioc y w).filter Nat.Prime, Real.log p / p) -
      (Real.log w - Real.log y)| ≤ 9 := by
  have hs := s145_primesLE_split (fun p : ℕ => Real.log p / p) hyw
  have h1 := s145_C_le w (hy.trans hyw)
  have h2 := s145_C_ge w
  have h3 := s145_C_le y hy
  have h4 := s145_C_ge y
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem s145_log_floor_lower {r : ℝ} (hr : 2 ≤ r) :
    Real.log r - Real.log 2 ≤ Real.log (⌊r⌋₊ : ℝ) := by
  have hf := Nat.lt_floor_add_one r
  have hhalf : r / 2 ≤ (⌊r⌋₊ : ℝ) := by linarith
  have hpos : 0 < r / 2 := by linarith
  have hl := Real.log_le_log hpos hhalf
  rwa [Real.log_div (by linarith : r ≠ 0) (by norm_num : (2 : ℝ) ≠ 0)] at hl

theorem s145_window_error {x a b : ℝ} (hx : 1 < x) (_ha : 0 < a)
    (hab : a ≤ b) (hsize : 2 ≤ x ^ a) :
    |(∑ p ∈ (Ioc ⌊x ^ a⌋₊ ⌊x ^ b⌋₊).filter Nat.Prime,
      Real.log p / p) / Real.log x - (b - a)| ≤
        (9 + 2 * Real.log 2) / Real.log x := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hpow : x ^ a ≤ x ^ b := Real.rpow_le_rpow_of_exponent_le hx.le hab
  have hy : 1 ≤ ⌊x ^ a⌋₊ := (Nat.one_le_floor_iff _).mpr (by linarith)
  have hyw := Nat.floor_mono hpow
  have herr := s145_block_error ⌊x ^ a⌋₊ ⌊x ^ b⌋₊ hy hyw
  have hloA := s145_log_floor_lower hsize
  have hloB := s145_log_floor_lower (hsize.trans hpow)
  have hfloorA : (0 : ℝ) < ⌊x ^ a⌋₊ := by exact_mod_cast (show 0 < ⌊x ^ a⌋₊ by omega)
  have hfloorB : (0 : ℝ) < ⌊x ^ b⌋₊ := by exact_mod_cast (show 0 < ⌊x ^ b⌋₊ by omega)
  have hhiA := Real.log_le_log hfloorA (Nat.floor_le (Real.rpow_nonneg hx0.le a))
  have hhiB := Real.log_le_log hfloorB (Nat.floor_le (Real.rpow_nonneg hx0.le b))
  rw [Real.log_rpow hx0] at hloA hloB hhiA hhiB
  have hlog2 := Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)
  have hb : |(∑ p ∈ (Ioc ⌊x ^ a⌋₊ ⌊x ^ b⌋₊).filter Nat.Prime,
      Real.log p / p) - (b - a) * Real.log x| ≤ 9 + 2 * Real.log 2 := by
    rcases abs_le.mp herr with ⟨h₁, h₂⟩
    exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩
  have he : (∑ p ∈ (Ioc ⌊x ^ a⌋₊ ⌊x ^ b⌋₊).filter Nat.Prime,
      Real.log p / p) / Real.log x - (b - a) =
      ((∑ p ∈ (Ioc ⌊x ^ a⌋₊ ⌊x ^ b⌋₊).filter Nat.Prime,
        Real.log p / p) - (b - a) * Real.log x) / Real.log x := by
    field_simp
  rw [he, abs_div, abs_of_pos hlx]
  exact div_le_div_of_nonneg_right hb hlx.le

theorem s145_mertens_window_limit (a b : ℝ) (ha : 0 < a) (hab : a ≤ b) :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |(∑ p ∈ (Ioc ⌊x ^ a⌋₊ ⌊x ^ b⌋₊).filter Nat.Prime,
        Real.log p / p) / Real.log x - (b - a)| ≤ δ := by
  intro δ hδ
  apply Filter.eventually_atTop.mp
  filter_upwards [Filter.eventually_ge_atTop (2 : ℝ),
    (tendsto_rpow_atTop ha).eventually_ge_atTop 2,
    Real.tendsto_log_atTop.eventually_ge_atTop ((9 + 2 * Real.log 2) / δ)]
    with x hx hp hl
  have hx1 : 1 < x := by linarith
  apply (s145_window_error hx1 ha hab hp).trans
  apply (div_le_iff₀ (Real.log_pos hx1)).mpr
  have h := (div_le_iff₀ hδ).mp hl
  linarith


theorem s145_endpoint_bound (f : ℝ → ℝ) {x : ℝ} (hx : 1 < x) :
    |(∑ p ∈ range (⌊x⌋₊ + 1),
        if p.Prime ∧ x ^ (1 / 4 : ℝ) ≤ p ∧ (p : ℝ) ^ 2 ≤ x then
          f (Real.log p / Real.log x) * ((Real.log p / p) / Real.log x) else 0) -
      ∑ p ∈ (Ioc ⌊x ^ (1 / 4 : ℝ)⌋₊ ⌊x ^ (1 / 2 : ℝ)⌋₊).filter Nat.Prime,
        f (Real.log p / Real.log x) * ((Real.log p / p) / Real.log x)| ≤
      |f (1 / 4)| / x ^ (1 / 4 : ℝ) := by
  classical
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  have hq : 0 < x ^ (1 / 4 : ℝ) := Real.rpow_pos_of_pos hx0 _
  have hsq : x ^ (1 / 2 : ℝ) = √x := (Real.sqrt_eq_rpow x).symm
  rw [hsq, ← sum_filter]
  set g : ℕ → ℝ := fun p => f (Real.log p / Real.log x) * ((Real.log p / p) / Real.log x)
  set A := (range (⌊x⌋₊ + 1)).filter
    (fun p : ℕ => p.Prime ∧ x ^ (1 / 4 : ℝ) ≤ p ∧ (p : ℝ) ^ 2 ≤ x)
  set B := (Ioc ⌊x ^ (1 / 4 : ℝ)⌋₊ ⌊√x⌋₊).filter Nat.Prime
  have hBA : B ⊆ A := by
    intro p hp
    obtain ⟨hI, hpr⟩ := mem_filter.mp hp
    obtain ⟨h1, h2⟩ := mem_Ioc.mp hI
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    have hps : (p : ℝ) ≤ √x := (Nat.le_floor_iff (Real.sqrt_nonneg x)).mp h2
    have hp2 : (p : ℝ) ^ 2 ≤ x := (Real.le_sqrt hp0 hx0.le).mp hps
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hpr.one_lt.le
    have hpx : (p : ℝ) ≤ x := by nlinarith
    refine mem_filter.mpr ⟨mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hpx)), hpr, ?_, hp2⟩
    exact (Nat.lt_of_floor_lt h1).le
  have hdiff : ∀ p ∈ A \ B, (p : ℝ) = x ^ (1 / 4 : ℝ) := by
    intro p hp
    obtain ⟨hA, hB⟩ := mem_sdiff.mp hp
    obtain ⟨_, hpr, h1, h2⟩ := mem_filter.mp hA
    by_contra hne
    apply hB
    have hlt : x ^ (1 / 4 : ℝ) < p := lt_of_le_of_ne h1 (Ne.symm hne)
    have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
    refine mem_filter.mpr ⟨mem_Ioc.mpr ⟨(Nat.floor_lt hq.le).mpr hlt, ?_⟩, hpr⟩
    exact Nat.le_floor ((Real.le_sqrt hp0 hx0.le).mpr h2)
  have hcard : (A \ B).card ≤ 1 := by
    apply card_le_one.mpr
    intro a ha b hb
    have := (hdiff a ha).trans (hdiff b hb).symm
    exact_mod_cast this
  have hterm : ∀ p ∈ A \ B, |g p| ≤ |f (1 / 4)| / x ^ (1 / 4 : ℝ) := by
    intro p hp
    have he := hdiff p hp
    have hl : Real.log p = (1 / 4) * Real.log x := by
      rw [he, Real.log_rpow hx0]
    have ha : Real.log p / Real.log x = 1 / 4 := by
      rw [hl]; field_simp
    simp only [g]
    rw [ha, hl, he]
    have e : f (1 / 4) * ((1 / 4 * Real.log x / x ^ (1 / 4 : ℝ)) / Real.log x) =
        (1 / 4) * (f (1 / 4) / x ^ (1 / 4 : ℝ)) := by
      field_simp
    rw [e, abs_mul, abs_div (f (1 / 4)), abs_of_pos hq,
      abs_of_pos (by norm_num : (0 : ℝ) < 1 / 4)]
    have h0 : 0 ≤ |f (1 / 4)| / x ^ (1 / 4 : ℝ) := by positivity
    linarith
  rw [← sum_sdiff hBA, add_sub_cancel_right]
  calc |∑ p ∈ A \ B, g p| ≤ ∑ p ∈ A \ B, |g p| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ A \ B, |f (1 / 4)| / x ^ (1 / 4 : ℝ) := sum_le_sum hterm
    _ = (A \ B).card * (|f (1 / 4)| / x ^ (1 / 4 : ℝ)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ 1 * (|f (1 / 4)| / x ^ (1 / 4 : ℝ)) := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      exact_mod_cast hcard
    _ = _ := one_mul _

theorem s145_window_term (f : ℝ → ℝ) {x s t ε : ℝ} (hx : 1 < x)
    (hunif : ∀ a : ℝ, s < a → a ≤ t → |f a - f s| ≤ ε) :
    |(∑ p ∈ (Ioc ⌊x ^ s⌋₊ ⌊x ^ t⌋₊).filter Nat.Prime,
        f (Real.log p / Real.log x) * ((Real.log p / p) / Real.log x)) -
      f s * ((∑ p ∈ (Ioc ⌊x ^ s⌋₊ ⌊x ^ t⌋₊).filter Nat.Prime, Real.log p / p) /
        Real.log x)| ≤
      ε * ((∑ p ∈ (Ioc ⌊x ^ s⌋₊ ⌊x ^ t⌋₊).filter Nat.Prime, Real.log p / p) /
        Real.log x) := by
  have hx0 : 0 < x := by linarith
  have hlx : 0 < Real.log x := Real.log_pos hx
  rw [sum_div, mul_sum, mul_sum, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun p hp => ?_)
  obtain ⟨hI, hpr⟩ := mem_filter.mp hp
  obtain ⟨h1, h2⟩ := mem_Ioc.mp hI
  have hp1 : (1 : ℝ) < p := by exact_mod_cast hpr.one_lt
  have hp0 : (0 : ℝ) < p := by linarith
  have hlp : 0 < Real.log p := Real.log_pos hp1
  have hw : 0 ≤ (Real.log p / p) / Real.log x := by positivity
  have hlt : x ^ s < p := Nat.lt_of_floor_lt h1
  have hle : (p : ℝ) ≤ x ^ t := (Nat.le_floor_iff (Real.rpow_nonneg hx0.le t)).mp h2
  have ha1 : s < Real.log p / Real.log x := by
    rw [lt_div_iff₀ hlx]
    have := Real.log_lt_log (Real.rpow_pos_of_pos hx0 s) hlt
    rwa [Real.log_rpow hx0] at this
  have ha2 : Real.log p / Real.log x ≤ t := by
    rw [div_le_iff₀ hlx]
    have := Real.log_le_log hp0 hle
    rwa [Real.log_rpow hx0] at this
  rw [← sub_mul, abs_mul, abs_of_nonneg hw]
  exact mul_le_mul_of_nonneg_right (hunif _ ha1 ha2) hw

theorem s145_integral_term (f : ℝ → ℝ) {s t ε : ℝ} (hf : Continuous f) (hst : s ≤ t)
    (hunif : ∀ a : ℝ, s < a → a ≤ t → |f a - f s| ≤ ε) :
    |(∫ a in s..t, f a) - f s * (t - s)| ≤ ε * (t - s) := by
  have h : (∫ a in s..t, f a) - f s * (t - s) = ∫ a in s..t, (f a - f s) := by
    rw [intervalIntegral.integral_sub (hf.intervalIntegrable _ _) intervalIntegrable_const]
    simp [intervalIntegral.integral_const, smul_eq_mul, mul_comm]
  rw [h]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := s) (b := t) (C := ε)
    (f := fun a => f a - f s) (fun a ha => by
      rw [Set.uIoc_of_le hst] at ha
      exact hunif a ha.1 ha.2)
  simpa [abs_of_nonneg (sub_nonneg.mpr hst)] using this

theorem s145_sum_Ioc_split (g : ℕ → ℝ) (F : ℕ → ℕ) (hF : Monotone F) (N : ℕ) :
    ∑ p ∈ Ioc (F 0) (F N), g p = ∑ k ∈ range N, ∑ p ∈ Ioc (F k) (F (k + 1)), g p := by
  induction N with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ← ih, sum_Ioc_consecutive _ (hF (Nat.zero_le n)) (hF (Nat.le_succ n))]


/-- Partition nodes of the interval from one quarter to one half. -/
noncomputable def s145_node (N k : ℕ) : ℝ := 1 / 4 + k / (4 * N)

theorem s145_window_quadrature
    (hW : ∀ a b : ℝ, 0 < a → a ≤ b → ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |(∑ p ∈ (Ioc ⌊x ^ a⌋₊ ⌊x ^ b⌋₊).filter Nat.Prime,
        Real.log p / p) / Real.log x - (b - a)| ≤ δ)
    (f : ℝ → ℝ) (hf : Continuous f) :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |(∑ p ∈ (Ioc ⌊x ^ (1 / 4 : ℝ)⌋₊ ⌊x ^ (1 / 2 : ℝ)⌋₊).filter Nat.Prime,
          f (Real.log p / Real.log x) * ((Real.log p / p) / Real.log x)) -
        ∫ a in (1 / 4 : ℝ)..(1 / 2 : ℝ), f a| ≤ δ := by
  classical
  intro δ hδ
  obtain ⟨C, hC⟩ := (isCompact_Icc (a := (1 / 4 : ℝ)) (b := 1 / 2)).exists_bound_of_continuousOn
    hf.continuousOn
  have hC0 : 0 ≤ C := (norm_nonneg _).trans (hC (1 / 4) ⟨le_refl _, by norm_num⟩)
  set ε := δ / 4 with hε
  have hε0 : 0 < ε := by positivity
  obtain ⟨η, hη, hU⟩ := Metric.uniformContinuousOn_iff.mp
    ((isCompact_Icc (a := (1 / 4 : ℝ)) (b := 1 / 2)).uniformContinuousOn_of_continuous
      hf.continuousOn) ε hε0
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (4 * η))
  have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (by positivity) hN
  set h : ℝ := 1 / (4 * N) with hh
  have hh0 : 0 < h := by positivity
  have hhη : h < η := by
    rw [hh, div_lt_iff₀ (by positivity)]
    rw [div_lt_iff₀ (by positivity)] at hN
    linarith
  have hstep : ∀ k : ℕ, s145_node N (k + 1) - s145_node N k = h := by
    intro k; unfold s145_node; rw [hh]; push_cast; field_simp; ring
  have hnode0 : s145_node N 0 = 1 / 4 := by unfold s145_node; simp
  have hnodeN : s145_node N N = 1 / 2 := by unfold s145_node; field_simp; norm_num
  have hnode_ge : ∀ k : ℕ, 1 / 4 ≤ s145_node N k := by
    intro k; unfold s145_node; have : (0 : ℝ) ≤ k / (4 * N) := by positivity
    linarith
  have hnode_le : ∀ k : ℕ, k ≤ N → s145_node N k ≤ 1 / 2 := by
    intro k hk; unfold s145_node
    have hk' : (k : ℝ) ≤ N := by exact_mod_cast hk
    have : (k : ℝ) / (4 * N) ≤ 1 / 4 := by
      rw [div_le_iff₀ (by positivity)]; linarith
    linarith
  have hmono : Monotone (s145_node N) := by
    intro i j hij; unfold s145_node
    have : (i : ℝ) ≤ j := by exact_mod_cast hij
    have := div_le_div_of_nonneg_right this (by positivity : (0 : ℝ) ≤ 4 * N)
    linarith
  set δ' := δ / (4 * N * (C + ε + 1)) with hδ'
  have hδ'0 : 0 < δ' := by positivity
  have hev : ∀ᶠ x in Filter.atTop, (∀ k ∈ range N,
      |(∑ p ∈ (Ioc ⌊x ^ s145_node N k⌋₊ ⌊x ^ s145_node N (k + 1)⌋₊).filter Nat.Prime,
        Real.log p / p) / Real.log x - (s145_node N (k + 1) - s145_node N k)| ≤ δ') ∧ 1 < x := by
    refine Filter.Eventually.and ((Filter.eventually_all_finset _).2 fun k _ => ?_)
      (Filter.eventually_gt_atTop 1)
    exact Filter.eventually_atTop.2 (hW _ _ (by linarith [hnode_ge k])
      (hmono (Nat.le_succ k)) δ' hδ'0)
  obtain ⟨X, hX⟩ := Filter.eventually_atTop.1 hev
  refine ⟨X, fun x hx => ?_⟩
  obtain ⟨hm, hx1⟩ := hX x hx
  have hx0 : 0 < x := by linarith
  set g : ℕ → ℝ := fun p => f (Real.log p / Real.log x) * ((Real.log p / p) / Real.log x)
    with hg
  have hFmono : Monotone (fun k => ⌊x ^ s145_node N k⌋₊) := fun i j hij =>
    Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hx1.le (hmono hij))
  have hsum : (∑ p ∈ (Ioc ⌊x ^ (1 / 4 : ℝ)⌋₊ ⌊x ^ (1 / 2 : ℝ)⌋₊).filter Nat.Prime, g p) =
      ∑ k ∈ range N, ∑ p ∈ (Ioc ⌊x ^ s145_node N k⌋₊
        ⌊x ^ s145_node N (k + 1)⌋₊).filter Nat.Prime, g p := by
    rw [← hnode0, ← hnodeN, sum_filter,
      s145_sum_Ioc_split _ (fun k => ⌊x ^ s145_node N k⌋₊) hFmono N]
    simp only [sum_filter]
  have hint : (∫ a in (1 / 4 : ℝ)..(1 / 2 : ℝ), f a) =
      ∑ k ∈ range N, ∫ a in s145_node N k..s145_node N (k + 1), f a := by
    rw [← hnode0, ← hnodeN,
      intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hf.intervalIntegrable _ _)]
  rw [hsum, hint, ← sum_sub_distrib]
  have hk : ∀ k ∈ range N,
      |(∑ p ∈ (Ioc ⌊x ^ s145_node N k⌋₊ ⌊x ^ s145_node N (k + 1)⌋₊).filter Nat.Prime, g p) -
        ∫ a in s145_node N k..s145_node N (k + 1), f a| ≤ ε * (2 * h + δ') + C * δ' := by
    intro k hkN
    have hkN' : k + 1 ≤ N := mem_range.mp hkN
    have hunif : ∀ a : ℝ, s145_node N k < a → a ≤ s145_node N (k + 1) →
        |f a - f (s145_node N k)| ≤ ε := by
      intro a h1 h2
      have hd := hU a ⟨by linarith [hnode_ge k], h2.trans (hnode_le _ hkN')⟩
        (s145_node N k) ⟨hnode_ge k, (hmono (Nat.le_succ k)).trans (hnode_le _ hkN')⟩
        (by rw [Real.dist_eq, abs_of_pos (by linarith)]; linarith [hstep k])
      rw [Real.dist_eq] at hd
      exact hd.le
    have hw := s145_window_term f hx1 hunif
    have hi := s145_integral_term f hf (hmono (Nat.le_succ k)) hunif
    have hmk := hm k hkN
    rw [hstep k] at hi hmk
    have hfC : |f (s145_node N k)| ≤ C := by
      have := hC (s145_node N k) ⟨hnode_ge k, (hnode_le _ (Nat.le_of_succ_le hkN'))⟩
      rwa [Real.norm_eq_abs] at this
    set m := (∑ p ∈ (Ioc ⌊x ^ s145_node N k⌋₊ ⌊x ^ s145_node N (k + 1)⌋₊).filter Nat.Prime,
        Real.log p / p) / Real.log x
    have hprod : |f (s145_node N k) * (m - h)| ≤ C * δ' := by
      rw [abs_mul]; exact mul_le_mul hfC hmk (abs_nonneg _) hC0
    have hexp : f (s145_node N k) * (m - h) = f (s145_node N k) * m - f (s145_node N k) * h := by
      ring
    rw [hexp] at hprod
    have hmle : m ≤ h + δ' := by linarith [(abs_le.mp hmk).2]
    have hεm : ε * m ≤ ε * (h + δ') := mul_le_mul_of_nonneg_left hmle hε0.le
    rcases abs_le.mp hw with ⟨w1, w2⟩
    rcases abs_le.mp hi with ⟨i1, i2⟩
    rcases abs_le.mp hprod with ⟨p1, p2⟩
    apply abs_le.mpr
    constructor <;> nlinarith
  refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hk).trans ?_)
  rw [sum_const, card_range, nsmul_eq_mul]
  have hNh : (N : ℝ) * h = 1 / 4 := by rw [hh]; field_simp
  have hNd : (N : ℝ) * δ' = δ / (4 * (C + ε + 1)) := by rw [hδ']; field_simp
  have hlast : δ / (4 * (C + ε + 1)) * (ε + C) ≤ δ / 4 := by
    calc δ / (4 * (C + ε + 1)) * (ε + C) ≤ δ / (4 * (C + ε + 1)) * (C + ε + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) (by positivity)
      _ = δ / 4 := by field_simp
  have e : (N : ℝ) * (ε * (2 * h + δ') + C * δ') =
      2 * ε * ((N : ℝ) * h) + ((N : ℝ) * δ') * (ε + C) := by ring
  rw [e, hNh, hNd]
  rw [hε] at hlast ⊢
  linarith


/-- MMS page 11 bottom display, the prime sum to integral passage in the coordinate
a equal to log p over log x, for a continuous kernel, from the window limits. -/
theorem s145_prime_quadrature
    (hW : ∀ a b : ℝ, 0 < a → a ≤ b → ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |(∑ p ∈ (Ioc ⌊x ^ a⌋₊ ⌊x ^ b⌋₊).filter Nat.Prime,
        Real.log p / p) / Real.log x - (b - a)| ≤ δ)
    (f : ℝ → ℝ) (hf : Continuous f) :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |(∑ p ∈ range (⌊x⌋₊ + 1),
          if p.Prime ∧ x ^ (1 / 4 : ℝ) ≤ p ∧ (p : ℝ) ^ 2 ≤ x then
            f (Real.log p / Real.log x) * ((Real.log p / p) / Real.log x) else 0) -
        ∫ a in (1 / 4 : ℝ)..(1 / 2 : ℝ), f a| ≤ δ := by
  intro δ hδ
  obtain ⟨X₁, h₁⟩ := s145_window_quadrature hW f hf (δ / 2) (by linarith)
  obtain ⟨X₂, h₂⟩ := Filter.eventually_atTop.1
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).eventually_ge_atTop
      (2 * |f (1 / 4)| / δ + 1))
  refine ⟨max (max X₁ X₂) 2, fun x hx => ?_⟩
  have hx1 : 1 < x := by linarith [le_max_right (max X₁ X₂) 2]
  have hA := h₁ x ((le_max_left X₁ X₂).trans ((le_max_left _ _).trans hx))
  have hB := h₂ x ((le_max_right X₁ X₂).trans ((le_max_left _ _).trans hx))
  have hE := s145_endpoint_bound f hx1
  have hq : 0 < x ^ (1 / 4 : ℝ) := by linarith [div_nonneg (mul_nonneg (by norm_num : (0:ℝ) ≤ 2) (abs_nonneg (f (1 / 4)))) hδ.le]
  have hE' : |f (1 / 4)| / x ^ (1 / 4 : ℝ) ≤ δ / 2 := by
    rw [div_le_iff₀ hq]
    have h3 : 2 * |f (1 / 4)| / δ ≤ x ^ (1 / 4 : ℝ) := by linarith
    rw [div_le_iff₀ hδ] at h3
    nlinarith
  have ha := abs_add_le
    ((∑ p ∈ range (⌊x⌋₊ + 1),
          if p.Prime ∧ x ^ (1 / 4 : ℝ) ≤ p ∧ (p : ℝ) ^ 2 ≤ x then
            f (Real.log p / Real.log x) * ((Real.log p / p) / Real.log x) else 0) -
      ∑ p ∈ (Ioc ⌊x ^ (1 / 4 : ℝ)⌋₊ ⌊x ^ (1 / 2 : ℝ)⌋₊).filter Nat.Prime,
        f (Real.log p / Real.log x) * ((Real.log p / p) / Real.log x))
    ((∑ p ∈ (Ioc ⌊x ^ (1 / 4 : ℝ)⌋₊ ⌊x ^ (1 / 2 : ℝ)⌋₊).filter Nat.Prime,
        f (Real.log p / Real.log x) * ((Real.log p / p) / Real.log x)) -
      ∫ a in (1 / 4 : ℝ)..(1 / 2 : ℝ), f a)
  rw [sub_add_sub_cancel] at ha
  linarith

/-- The logarithmic coordinate clamped to the interval from one quarter to one half. -/
noncomputable def s145_clamp (a : ℝ) : ℝ := max (1 / 4 : ℝ) (min (1 / 2) a)

/-- A globally continuous extension of the kernel B of 1 minus a over a, over a squared,
from the interval from one quarter to one half. MMS page 11 bottom display. -/
noncomputable def s145_kernel (a : ℝ) : ℝ :=
  Task571.buchstabStage 8 (max 1 ((1 - s145_clamp a) / s145_clamp a)) / s145_clamp a ^ 2

theorem s145_clamp_pos (a : ℝ) : 0 < s145_clamp a :=
  lt_of_lt_of_le (by norm_num) (le_max_left _ _)

theorem s145_clamp_continuous : Continuous s145_clamp := by
  unfold s145_clamp; fun_prop

theorem s145_kernel_continuous : Continuous s145_kernel := by
  have h1 : Continuous (fun a => (1 - s145_clamp a) / s145_clamp a) :=
    (continuous_const.sub s145_clamp_continuous).div s145_clamp_continuous
      (fun a => (s145_clamp_pos a).ne')
  have h2 := (Task571.buchstabStage_continuous_clamp 8).comp h1
  exact h2.div (s145_clamp_continuous.pow 2) (fun a => pow_ne_zero 2 (s145_clamp_pos a).ne')

theorem s145_clamp_eq {a : ℝ} (h1 : 1 / 4 ≤ a) (h2 : a ≤ 1 / 2) : s145_clamp a = a := by
  unfold s145_clamp
  rw [min_eq_right h2, max_eq_right h1]

theorem s145_kernel_eq {a : ℝ} (h1 : 1 / 4 ≤ a) (h2 : a ≤ 1 / 2) :
    s145_kernel a = Task571.buchstabModel ((1 - a) / a) / a ^ 2 := by
  unfold s145_kernel Task571.buchstabModel
  rw [s145_clamp_eq h1 h2]
  have ha : 0 < a := by linarith
  have : 1 ≤ (1 - a) / a := by rw [le_div_iff₀ ha]; linarith
  rw [max_eq_right this]

/-- The composite model sum is the prime sum of the continuous kernel against the
logarithmic prime measure. MMS page 11 bottom display, Jacobian identity. -/
theorem s145_compositeModelSum_eq {x : ℝ} (hx : 1 < x) :
    compositeModelSum x = ∑ p ∈ range (⌊x⌋₊ + 1),
      if p.Prime ∧ x ^ (1 / 4 : ℝ) ≤ p ∧ (p : ℝ) ^ 2 ≤ x then
        s145_kernel (Real.log p / Real.log x) * ((Real.log p / p) / Real.log x) else 0 := by
  unfold compositeModelSum
  rw [mul_sum]
  refine sum_congr rfl (fun p _ => ?_)
  split_ifs with h
  · obtain ⟨hp, h1, h2⟩ := h
    have hx0 : 0 < x := by linarith
    have hlx : 0 < Real.log x := Real.log_pos hx
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hp.one_lt
    have hp0 : (0 : ℝ) < p := by linarith
    have hlp : 0 < Real.log p := Real.log_pos hp1
    have hA : (1 / 4) * Real.log x ≤ Real.log p := by
      have := Real.log_le_log (Real.rpow_pos_of_pos hx0 _) h1
      rwa [Real.log_rpow hx0] at this
    have hB : Real.log p ≤ (1 / 2) * Real.log x := by
      have := Real.log_le_log (by positivity) h2
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    have ha1 : 1 / 4 ≤ Real.log p / Real.log x := by rw [le_div_iff₀ hlx]; linarith
    have ha2 : Real.log p / Real.log x ≤ 1 / 2 := by rw [div_le_iff₀ hlx]; linarith
    rw [s145_kernel_eq ha1 ha2, Real.log_div hx0.ne' hp0.ne']
    have e : (1 - Real.log p / Real.log x) / (Real.log p / Real.log x) =
        (Real.log x - Real.log p) / Real.log p := by
      field_simp
    rw [e]
    field_simp
  · simp

/-- compositeModelSum_limit from the proved Mertens window limit and the prime quadrature. -/
theorem compositeModelSum_limit_of_s145_leaves :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |compositeModelSum x -
        ∫ a in (1 / 4 : ℝ)..(1 / 2 : ℝ), Task571.buchstabModel ((1 - a) / a) / a ^ 2| ≤ δ := by
  intro δ hδ
  obtain ⟨X, hX⟩ := s145_prime_quadrature s145_mertens_window_limit s145_kernel
    s145_kernel_continuous δ hδ
  refine ⟨max X 2, fun x hx => ?_⟩
  have hx1 : 1 < x := by linarith [le_max_right X 2]
  have hI : (∫ a in (1 / 4 : ℝ)..(1 / 2 : ℝ), Task571.buchstabModel ((1 - a) / a) / a ^ 2) =
      ∫ a in (1 / 4 : ℝ)..(1 / 2 : ℝ), s145_kernel a := by
    apply intervalIntegral.integral_congr
    intro a ha
    rw [Set.uIcc_of_le (by norm_num)] at ha
    exact (s145_kernel_eq ha.1 ha.2).symm
  rw [hI, s145_compositeModelSum_eq hx1]
  exact hX x ((le_max_left _ _).trans hx)


theorem compositeModelSum_limit_s145 :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |compositeModelSum x -
        ∫ a in (1 / 4 : ℝ)..(1 / 2 : ℝ), Task571.buchstabModel ((1 - a) / a) / a ^ 2| ≤ δ :=
  compositeModelSum_limit_of_s145_leaves

end S145_compositeModelSum_limit

/-- LEAF: MMS page 11 bottom display, the prime sum to integral passage in the
logarithmic coordinate a equal to log p over log x, from one quarter to one half.
Class MEDIUM for Open Math OS. Partial summation with the prime number theorem;
the lab Mertens estimates of Decomp581b handle the analogous triple sums. -/
theorem compositeModelSum_limit :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |compositeModelSum x -
        ∫ a in (1 / 4 : ℝ)..(1 / 2 : ℝ), Task571.buchstabModel ((1 - a) / a) / a ^ 2| ≤ δ := by
  exact compositeModelSum_limit_s145

/-- MMS page 11 bottom display, the substitution u equal to one over a minus
one, mapping one quarter to three and one half to one. Derived, no cited input. -/
theorem compositeIntegral_substitution :
    (∫ a in (1 / 4 : ℝ)..(1 / 2 : ℝ), Task571.buchstabModel ((1 - a) / a) / a ^ 2) =
      ∫ t in (1 : ℝ)..3, Task571.buchstabModel t := by
  set g := Task571.buchstabModel
  have hgc : ContinuousOn g (Set.Ici 1) := by
    have hc := (Task571.buchstabStage_continuous_clamp 8).continuousOn
      (s := Set.Ici (1 : ℝ))
    refine hc.congr fun u hu => ?_
    simp only [g, Task571.buchstabModel, max_eq_right (Set.mem_Ici.mp hu)]
  have hsub := intervalIntegral.integral_comp_mul_deriv' (a := (1 / 4 : ℝ)) (b := 1 / 2)
    (f := fun a : ℝ => (1 - a) / a) (f' := fun a : ℝ => -1 / a ^ 2) (g := g)
    (fun a ha => by
      have ha0 : a ≠ 0 := by
        rw [Set.uIcc_of_le (by norm_num)] at ha; linarith [ha.1]
      have h1 : HasDerivAt (fun a : ℝ => 1 - a) (-1) a := by
        simpa using (hasDerivAt_id a).const_sub 1
      have h3 : HasDerivAt (fun a : ℝ => (1 - a) / a)
          ((-1 * a - (1 - a) * 1) / a ^ 2) a := h1.div (hasDerivAt_id a) ha0
      refine h3.congr_deriv ?_
      field_simp
      ring)
    (by
      apply ContinuousOn.div continuousOn_const (continuousOn_id.pow 2)
      intro a ha
      rw [Set.uIcc_of_le (by norm_num)] at ha
      have : 0 < a := by linarith [ha.1]
      exact pow_ne_zero 2 this.ne')
    (by
      apply hgc.mono
      rintro _ ⟨a, ha, rfl⟩
      rw [Set.uIcc_of_le (by norm_num)] at ha
      have h0 : 0 < a := by linarith [ha.1]
      show 1 ≤ (1 - a) / a
      rw [le_div_iff₀ h0]; linarith [ha.2])
  simp only [Function.comp_apply] at hsub
  rw [show ((1 : ℝ) - 1 / 4) / (1 / 4) = 3 by norm_num,
    show ((1 : ℝ) - 1 / 2) / (1 / 2) = 1 by norm_num,
    intervalIntegral.integral_symm 1 3] at hsub
  have hneg : (∫ a in (1 / 4 : ℝ)..(1 / 2 : ℝ), g ((1 - a) / a) / a ^ 2) =
      -∫ a in (1 / 4 : ℝ)..(1 / 2 : ℝ), g ((1 - a) / a) * (-1 / a ^ 2) := by
    rw [← intervalIntegral.integral_neg]
    congr 1; funext a; ring
  rw [hneg]
  linarith [hsub]

/-- The composite rough limit from the three leaves above.
MMS page 11 bottom display. CONDITIONAL ON compositeMean_model,
compositeModelSum_limit and compositeIntegral_substitution. -/
theorem compositeMean_limit_of_leaves :
    ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |compositeMean x - (∫ t in (1 : ℝ)..3, Task571.buchstabModel t)| ≤ δ := by
  intro δ hδ
  obtain ⟨X₁, h₁⟩ := compositeMean_model (δ / 2) (by linarith)
  obtain ⟨X₂, h₂⟩ := compositeModelSum_limit (δ / 2) (by linarith)
  refine ⟨max X₁ X₂, fun x hx => ?_⟩
  have a₁ := h₁ x ((le_max_left _ _).trans hx)
  have a₂ := h₂ x ((le_max_right _ _).trans hx)
  rw [compositeIntegral_substitution] at a₂
  have ha := abs_add_le (compositeMean x - compositeModelSum x)
    (compositeModelSum x - ∫ t in (1 : ℝ)..3, Task571.buchstabModel t)
  rw [sub_add_sub_cancel] at ha
  linarith

end LeanLab.Ternary.MMS.Task581
