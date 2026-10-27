/-
Generalised converse: an average Goldbach bound with exponent 1 + θ forces a zero-free
half plane. If Σ_{n ≤ N} G(n) = N²/2 + O(N^{1+θ+ε}) for every ε > 0, with 1/2 ≤ θ < 1,
then ζ has no zero with Re s > θ, hence by symmetry every nontrivial zero lies in
1 − θ ≤ Re s ≤ θ. θ = 1/2 is rh_of_avgRH. Same route as Converse.lean.
Connection sweep 2026-10-19, PC run 20261019T1107Z-17600, unit U-1059: links P0098's average
form to the zero-free strip, quasi Riemann, hypotheses that P0057 and P0051 Corollary 2 take.
AI-written Lean code, Claude, 2026-10-19. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.GoldbachAverage.Converse

open Finset Real
open scoped ArithmeticFunction.vonMangoldt

noncomputable section
namespace LeanLab.GoldbachAverage.Converse

variable {θ : ℝ}

/-- `Σ_{n ≤ N} G(n) = N²/2 + O(N^{1+θ+ε})` for every `ε > 0`. -/
def AvgTheta (θ : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
    |∑ n ∈ range (N + 1), G n - (N : ℝ) ^ 2 / 2| ≤ K * (N : ℝ) ^ (1 + θ + ε)

theorem abelianT (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (H : AvgTheta θ) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ (1 - θ) / 2) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 →
      |∑' n : ℕ, G n * Real.exp (-t) ^ n - 1 / t ^ 2| ≤ C * t ^ (-(1 + θ + ε)) := by
  obtain ⟨K, hK⟩ := H ε hε
  set a : ℝ := 1 + θ + ε with ha
  have ha0 : 0 ≤ a := by linarith
  have ha1 : 1 ≤ a := by linarith
  have ha2 : a ≤ 2 := by linarith
  have hK0 : 0 ≤ K := by
    have h := hK 1 le_rfl
    simp only [Nat.cast_one, Real.one_rpow, mul_one] at h
    exact (abs_nonneg _).trans h
  set e : ℕ → ℝ := fun N => S N - (N : ℝ) * (N + 1) / 2 with he_def
  have he : ∀ N : ℕ, |e N| ≤ (K + 1) * (N : ℝ) ^ a := by
    intro N
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp only [e, S_zero, Nat.cast_zero]
      norm_num
      exact mul_nonneg (by linarith) (Real.rpow_nonneg le_rfl _)
    · have h1 : |S N - (N : ℝ) ^ 2 / 2| ≤ K * (N : ℝ) ^ a := hK N hN
      have hNa : (N : ℝ) ≤ (N : ℝ) ^ a := by
        have := Real.rpow_le_rpow_of_exponent_le (x := (N : ℝ)) (by exact_mod_cast hN) ha1
        rwa [Real.rpow_one] at this
      have e1 : e N = (S N - (N : ℝ) ^ 2 / 2) - (N : ℝ) / 2 := by simp only [e]; ring
      rw [e1]
      have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
      calc |S N - (N : ℝ) ^ 2 / 2 - (N : ℝ) / 2| ≤ |S N - (N : ℝ) ^ 2 / 2| + |(N : ℝ) / 2| :=
            abs_sub _ _
        _ ≤ K * (N : ℝ) ^ a + (N : ℝ) ^ a := by
            have h2 : |(N : ℝ) / 2| = (N : ℝ) / 2 := abs_of_nonneg (by positivity)
            linarith
        _ = (K + 1) * (N : ℝ) ^ a := by ring
  refine ⟨1 / 2 + 48 * (K + 1), fun t ht ht1 => ?_⟩
  set q := Real.exp (-t) with hq
  have hq0 : 0 ≤ q := (Real.exp_pos _).le
  have hq1 : q < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have hgeo := summable_rpow_geom ha0 ha2 ht
  have hbound : ∀ N : ℕ, ‖e N * q ^ N‖ ≤ (K + 1) * ((N : ℝ) ^ a * q ^ N) := by
    intro N
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hq0 N), ← mul_assoc]
    exact mul_le_mul_of_nonneg_right (he N) (pow_nonneg hq0 N)
  have hsum_e : Summable fun N : ℕ => e N * q ^ N :=
    Summable.of_norm_bounded (hgeo.mul_left (K + 1)) hbound
  have hT := tri_sum hq0 hq1
  have hS : ∑' N : ℕ, S N * q ^ N = q / (1 - q) ^ 3 + ∑' N : ℕ, e N * q ^ N := by
    rw [← hT.tsum_eq, ← Summable.tsum_add hT.summable hsum_e]
    refine tsum_congr fun N => ?_
    simp only [e]; ring
  rw [G_eq_S hq0 hq1, hS]
  set E := ∑' N : ℕ, e N * q ^ N with hE_def
  have hE : |E| ≤ (K + 1) * (48 * t ^ (-a) / t) := by
    calc |E| = ‖E‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∑' N : ℕ, (K + 1) * ((N : ℝ) ^ a * q ^ N) :=
          tsum_of_norm_bounded (hgeo.mul_left (K + 1)).hasSum hbound
      _ = (K + 1) * ∑' N : ℕ, (N : ℝ) ^ a * q ^ N := tsum_mul_left
      _ ≤ (K + 1) * (48 * t ^ (-a) / t) := by
          gcongr; exact rpow_geom ha0 ha2 ht ht1
  have h1q : 1 - q ≤ t := by have := Real.add_one_le_exp (-t); linarith
  have h1q0 : 0 < 1 - q := by linarith
  have hgm := geom_main ht ht1
  rw [← hq] at hgm
  have expand : (1 - q) * (q / (1 - q) ^ 3 + E) - 1 / t ^ 2 =
      (q / (1 - q) ^ 2 - 1 / t ^ 2) + (1 - q) * E := by
    field_simp; ring
  rw [expand]
  have hta : 1 ≤ t ^ (-a) := Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht ht1 (by linarith)
  have hta0 : 0 ≤ t ^ (-a) := by linarith
  have h2 : |(1 - q) * E| ≤ 48 * (K + 1) * t ^ (-a) := by
    rw [abs_mul, abs_of_pos h1q0]
    calc (1 - q) * |E| ≤ t * ((K + 1) * (48 * t ^ (-a) / t)) :=
          mul_le_mul h1q hE (abs_nonneg _) ht.le
      _ = 48 * (K + 1) * t ^ (-a) := by field_simp
  calc |q / (1 - q) ^ 2 - 1 / t ^ 2 + (1 - q) * E|
      ≤ |q / (1 - q) ^ 2 - 1 / t ^ 2| + |(1 - q) * E| := abs_add_le _ _
    _ ≤ 1 / 2 + 48 * (K + 1) * t ^ (-a) := add_le_add hgm h2
    _ ≤ (1 / 2 + 48 * (K + 1)) * t ^ (-a) := by nlinarith

/-- **AvgRH ⇒ φ(t) = 1/t + O(t^{-1/2-ε})** on `(0, 1]`. -/
theorem phi_near_zeroT (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (H : AvgTheta θ) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ (1 - θ) / 2) :
    ∃ C : ℝ, ∀ t : ℝ, 0 < t → t ≤ 1 → |phi t - 1 / t| ≤ C * t ^ (-(θ + ε)) := by
  obtain ⟨C, hC⟩ := abelianT hθ hθ1 H hε hε2
  refine ⟨C, fun t ht ht1 => ?_⟩
  have hq0 : 0 ≤ Real.exp (-t) := (Real.exp_pos _).le
  have hq1 : Real.exp (-t) < 1 := Real.exp_lt_one_iff.mpr (by linarith)
  have h := hC t ht ht1
  rw [← Lq_sq hq0 hq1] at h
  have hφ0 : 0 ≤ phi t := Lq_nonneg hq0
  have hX : 0 ≤ C * t ^ (-(1 + θ + ε)) := (abs_nonneg _).trans h
  have hpos : 0 < phi t + 1 / t := by positivity
  have hfac : |phi t - 1 / t| * (phi t + 1 / t) = |Lq (Real.exp (-t)) ^ 2 - 1 / t ^ 2| := by
    rw [← abs_of_pos hpos, ← abs_mul]; congr 1; simp only [phi]; ring
  have h1 : |phi t - 1 / t| ≤ C * t ^ (-(1 + θ + ε)) / (phi t + 1 / t) := by
    rw [le_div_iff₀ hpos, hfac]; exact h
  have h2 : C * t ^ (-(1 + θ + ε)) / (phi t + 1 / t) ≤ C * t ^ (-(1 + θ + ε)) / (1 / t) :=
    div_le_div_of_nonneg_left hX (by positivity) (by linarith)
  have h3 : C * t ^ (-(1 + θ + ε)) / (1 / t) = C * t ^ (-(θ + ε)) := by
    rw [one_div, div_inv_eq_mul, mul_assoc, ← Real.rpow_add_one ht.ne']; congr 2; ring
  linarith


open Complex MeasureTheory Filter Asymptotics Topology Set

lemma Fc_botT (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (H : AvgTheta θ) {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ (1 - θ) / 2) :
    Fc =O[𝓝[>] 0] fun t => t ^ (-(θ + ε)) := by
  obtain ⟨C, hC⟩ := phi_near_zeroT hθ hθ1 H hε hε2
  refine IsBigO.of_bound (|C| + 1) ?_
  filter_upwards [self_mem_nhdsWithin, nhdsWithin_le_nhds (Iio_mem_nhds (show (0 : ℝ) < 1 by norm_num))]
    with t ht ht1
  have ht' : 0 < t := ht
  have ht1' : t ≤ 1 := le_of_lt ht1
  rw [Fc, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg ht'.le _)]
  have hb : 1 ≤ t ^ (-(θ + ε)) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos ht' ht1' (by linarith)
  have h1 := hC t ht' ht1'
  have h2 : |1 / t - Real.exp (-t) / t| ≤ 1 := by
    have hx : 1 / t - Real.exp (-t) / t = (1 - Real.exp (-t)) / t := by ring
    have hle : 1 - Real.exp (-t) ≤ t := by have := Real.add_one_le_exp (-t); linarith
    have hge : 0 ≤ 1 - Real.exp (-t) := by
      have := Real.exp_le_one_iff.mpr (show -t ≤ 0 by linarith); linarith
    rw [hx, abs_of_nonneg (div_nonneg hge ht'.le), div_le_one ht']; exact hle
  have h3 : C * t ^ (-(θ + ε)) ≤ |C| * t ^ (-(θ + ε)) :=
    mul_le_mul_of_nonneg_right (le_abs_self C) (by linarith)
  calc |phi t - Real.exp (-t) / t| ≤ |phi t - 1 / t| + |1 / t - Real.exp (-t) / t| := abs_sub_le _ _ _
    _ ≤ (|C| + 1) * t ^ (-(θ + ε)) := by nlinarith

/-- `mellin F` is holomorphic on `Re s > 1/2`. -/
theorem mellin_Fc_diffT (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (H : AvgTheta θ) {s : ℂ} (hs : θ < s.re) :
    DifferentiableAt ℂ (mellin Fc) s := by
  set ε := min ((s.re - θ) / 2) ((1 - θ) / 2) with hε
  have hε0 : 0 < ε := lt_min (by linarith) (by linarith)
  have hε2 : ε ≤ (1 - θ) / 2 := min_le_right _ _
  have hεs : θ + ε < s.re := by
    have := min_le_left ((s.re - θ) / 2) ((1 - θ) / 2); linarith
  exact mellin_differentiableAt_of_isBigO_rpow_exp one_pos Fc_loc Fc_top
    ((Fc_botT hθ hθ1 H hε0 hε2).congr_right fun t => by rw [neg_neg]) (by simpa using hεs)

/-- For `Re s > 1`: `mellin F (s) = Γ(s) L(Λ, s) − Γ(s − 1)`. -/
theorem mellin_Fc_eqT (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (H : AvgTheta θ) {s : ℂ} (hs : 1 < s.re) :
    mellin Fc s = Gamma s * LSeries (fun n => ((Λ n : ℝ) : ℂ)) s - Gamma (s - 1) := by
  have hεs : θ + (1 - θ) / 2 < s.re := by linarith
  have hconvF : MellinConvergent Fc s :=
    mellinConvergent_of_isBigO_rpow_exp one_pos Fc_loc Fc_top
      ((Fc_botT hθ hθ1 H (ε := (1 - θ) / 2) (by linarith) le_rfl).congr_right fun t => by rw [neg_neg])
      (by simpa using hεs)
  have hconvE := mellinConvergent_E hs
  have hsplit : mellin (fun t => ((phi t : ℝ) : ℂ)) s =
      mellin Fc s + mellin (fun t => ((Real.exp (-t) / t : ℝ) : ℂ)) s := by
    unfold mellin
    rw [← integral_add hconvF hconvE]
    refine setIntegral_congr_fun measurableSet_Ioi (fun t ht => ?_)
    simp only [Fc, smul_eq_mul, ← mul_add, ← Complex.ofReal_add]
    congr 2; ring
  rw [mellin_phi hs, mellin_E hs] at hsplit
  rw [hsplit]; ring

/-- The slit half plane `Re s > 1/2` minus the real ray `[1, ∞)`. -/
def VT (θ : ℝ) : Set ℂ := {s | θ < s.re} \ {s | s.im = 0 ∧ 1 ≤ s.re}

lemma V_eqT : (VT θ) = (({s : ℂ | θ < s.re} ∩ {s | 0 < s.im}) ∪
    ({s : ℂ | θ < s.re} ∩ {s | s.re < 1})) ∪ ({s : ℂ | θ < s.re} ∩ {s | s.im < 0}) := by
  ext s
  simp only [VT, mem_diff, mem_setOf_eq, mem_union, mem_inter_iff, not_and, not_le]
  constructor
  · rintro ⟨h1, h2⟩
    rcases lt_trichotomy s.im 0 with h | h | h
    · right; exact ⟨h1, h⟩
    · left; right; exact ⟨h1, h2 h⟩
    · left; left; exact ⟨h1, h⟩
  · rintro ((⟨h1, h⟩ | ⟨h1, h⟩) | ⟨h1, h⟩)
    · exact ⟨h1, fun h' => absurd h' (ne_of_gt h)⟩
    · exact ⟨h1, fun _ => h⟩
    · exact ⟨h1, fun h' => absurd h' (ne_of_lt h)⟩

lemma V_openT : IsOpen (VT θ) := by
  refine IsOpen.sdiff (isOpen_lt continuous_const Complex.continuous_re) ?_
  exact (isClosed_eq Complex.continuous_im continuous_const).inter
    (isClosed_le continuous_const Complex.continuous_re)

lemma V_preconnT (hθ1 : θ < 1) : IsPreconnected (VT θ) := by
  rw [V_eqT]
  have hA := ((convex_halfSpace_re_gt θ).inter (convex_halfSpace_im_gt 0)).isPreconnected
  have hC := ((convex_halfSpace_re_gt θ).inter (convex_halfSpace_re_lt 1)).isPreconnected
  have hB := ((convex_halfSpace_re_gt θ).inter (convex_halfSpace_im_lt 0)).isPreconnected
  have h1 : θ < (θ + 1) / 2 := by linarith
  have h2 : (θ + 1) / 2 < 1 := by linarith
  have hAC := hA.union (⟨(θ + 1) / 2, 1⟩ : ℂ) (show θ < (θ + 1) / 2 ∧ (0 : ℝ) < 1 from ⟨h1, one_pos⟩)
    (show θ < (θ + 1) / 2 ∧ (θ + 1) / 2 < 1 from ⟨h1, h2⟩) hC
  exact hAC.union (⟨(θ + 1) / 2, -1⟩ : ℂ)
    (Or.inr (show θ < (θ + 1) / 2 ∧ (θ + 1) / 2 < 1 from ⟨h1, h2⟩))
    (show θ < (θ + 1) / 2 ∧ (-1 : ℝ) < 0 from ⟨h1, by norm_num⟩) hB

lemma Hf_diffT (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (H : AvgTheta θ) : DifferentiableOn ℂ Hf (VT θ) := by
  intro s hs
  have hre : θ < s.re := hs.1
  have hs2 := hs.2
  simp only [mem_setOf_eq, not_and, not_le] at hs2
  have hs1 : s ≠ 1 := by intro h; have := hs2 (by rw [h]; simp); rw [h] at this; simp at this
  have hG1 : ∀ m : ℕ, s - 1 ≠ -m := by
    intro m hm
    have him : s.im = 0 := by have := congrArg Complex.im hm; simpa using this
    have hre' : s.re = 1 - m := by have := congrArg Complex.re hm; simp at this; linarith
    have hlt := hs2 him
    have hm0 : (m : ℝ) < 1 / 2 := by linarith
    have : (0 : ℝ) ≤ m := Nat.cast_nonneg m
    have hm' : m = 0 := by
      by_contra hne
      have : (1 : ℝ) ≤ m := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr hne
      linarith
    rw [hm'] at hre'; simp at hre'; linarith
  have hζ : AnalyticAt ℂ riemannZeta s := analyticAt_riemannZeta hs1
  apply DifferentiableAt.differentiableWithinAt
  have h1 : DifferentiableAt ℂ (fun z => Complex.Gamma (z - 1)) s :=
    (Complex.differentiableAt_Gamma _ hG1).comp s (differentiableAt_id.sub_const 1)
  have h2 : DifferentiableAt ℂ Complex.Gamma s :=
    Complex.differentiableAt_Gamma _ (ne_neg_nat_of_re_pos (by linarith))
  exact (((mellin_Fc_diffT hθ hθ1 H hre).add h1).mul hζ.differentiableAt).add
    (h2.mul hζ.deriv.differentiableAt)

lemma Hf_zero_rightT {s : ℂ} (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (H : AvgTheta θ) (hs : 1 < s.re) : Hf s = 0 := by
  have hζ : riemannZeta s ≠ 0 := riemannZeta_ne_zero_of_one_lt_re hs
  rw [Hf, mellin_Fc_eqT hθ hθ1 H hs, sub_add_cancel,
    ArithmeticFunction.LSeries_vonMangoldt_eq_deriv_riemannZeta_div hs]
  field_simp
  ring

lemma Hf_eqOnT (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (H : AvgTheta θ) : EqOn Hf 0 (VT θ) := by
  have hA : AnalyticOnNhd ℂ Hf (VT θ) := (Hf_diffT hθ hθ1 H).analyticOnNhd V_openT
  have hz0 : (⟨2, 1⟩ : ℂ) ∈ VT θ := by
    refine ⟨show θ < 2 by linarith, ?_⟩
    simp
  refine hA.eqOn_zero_of_preconnected_of_eventuallyEq_zero (V_preconnT hθ1) hz0 ?_
  have hopen : IsOpen {s : ℂ | 1 < s.re} := isOpen_lt continuous_const Complex.continuous_re
  filter_upwards [hopen.mem_nhds (show (1 : ℝ) < (⟨2, 1⟩ : ℂ).re by norm_num)] with s hs
  exact Hf_zero_rightT hθ hθ1 H hs

/-- **AvgRH ⇒ no zero of ζ with `1/2 < Re ρ < 1`.** -/
theorem no_zero_rightT (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (H : AvgTheta θ) {ρ : ℂ} (h0 : θ < ρ.re) (h1 : ρ.re < 1)
    (hz : riemannZeta ρ = 0) : False := by
  have hρ1 : ρ ≠ 1 := by intro h; rw [h] at h1; simp at h1
  have hρV : ρ ∈ VT θ := by
    refine ⟨h0, ?_⟩
    simp only [mem_setOf_eq, not_and, not_le]
    intro _; exact h1
  have hζ : AnalyticAt ℂ riemannZeta ρ := analyticAt_riemannZeta hρ1
  -- the order is finite and at least 1
  have hU : AnalyticOnNhd ℂ riemannZeta ({1}ᶜ : Set ℂ) := fun z hz => analyticAt_riemannZeta hz
  have hconn : IsPreconnected ({1}ᶜ : Set ℂ) :=
    (isConnected_compl_singleton_of_one_lt_rank (by rw [Complex.rank_real_complex]; norm_num)
      (1 : ℂ)).isPreconnected
  have h2 : analyticOrderAt riemannZeta 2 ≠ ⊤ := by
    rw [analyticOrderAt_eq_zero.mpr (Or.inr (riemannZeta_ne_zero_of_one_lt_re (by norm_num)))]
    simp
  have htop : analyticOrderAt riemannZeta ρ ≠ ⊤ :=
    hU.analyticOrderAt_ne_top_of_isPreconnected hconn (x := 2) (y := ρ)
      (by simp) (by simpa using hρ1) h2
  obtain ⟨m, hm⟩ := ENat.ne_top_iff_exists.mp htop
  have hm0 : m ≠ 0 := by
    intro h
    rw [h] at hm
    have : analyticOrderAt riemannZeta ρ = 0 := by rw [← hm]; rfl
    rw [analyticOrderAt_eq_zero] at this
    rcases this with h' | h'
    · exact h' hζ
    · exact h' hz
  have hlim := LeanLab.PNTPort.ZetaZeros.tendsto_mul_logDeriv hζ hm.symm
  -- ζ is nonzero near ρ, off ρ
  have hne : ∀ᶠ s in 𝓝[≠] ρ, riemannZeta s ≠ 0 := by
    rcases hζ.eventually_eq_zero_or_eventually_ne_zero with h | h
    · exact absurd (analyticOrderAt_eq_top.mpr h) htop
    · exact h
  -- but by `H = 0`, `(s − ρ) ζ'/ζ = −(s − ρ)(mellin F + Γ(s − 1))/Γ(s)` near `ρ`
  set g : ℂ → ℂ := fun s => -((s - ρ) * (mellin Fc s + Gamma (s - 1)) / Gamma s) with hg
  have hVn : VT θ ∈ 𝓝 ρ := V_openT.mem_nhds hρV
  have hev : ∀ᶠ s in 𝓝[≠] ρ, (s - ρ) * (deriv riemannZeta s / riemannZeta s) = g s := by
    filter_upwards [hne, nhdsWithin_le_nhds hVn] with s hs hsV
    have hH := Hf_eqOnT hθ hθ1 H hsV
    simp only [Hf, Pi.zero_apply] at hH
    have hΓ : Gamma s ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by have : θ < s.re := hsV.1; linarith)
    simp only [hg]
    field_simp
    linear_combination (s - ρ) * hH
  have hgc : ContinuousAt g ρ := by
    have hΓ : Gamma ρ ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hGd : DifferentiableAt ℂ (fun z => Complex.Gamma (z - 1)) ρ := by
      have := (Hf_diffT hθ hθ1 H)
      have hG1 : ∀ k : ℕ, ρ - 1 ≠ -k := by
        intro k hk
        have hr := congrArg Complex.re hk
        simp at hr
        have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
        rcases Nat.eq_zero_or_pos k with hk0 | hk0
        · rw [hk0] at hr; simp at hr; linarith
        · have : (1 : ℝ) ≤ k := by exact_mod_cast hk0
          linarith
      exact (Complex.differentiableAt_Gamma _ hG1).comp ρ (differentiableAt_id.sub_const 1)
    have hGa : DifferentiableAt ℂ Complex.Gamma ρ :=
      Complex.differentiableAt_Gamma _ (ne_neg_nat_of_re_pos (by linarith))
    exact (((continuousAt_id.sub continuousAt_const).mul
      ((mellin_Fc_diffT hθ hθ1 H h0).continuousAt.add hGd.continuousAt)).div hGa.continuousAt hΓ).neg
  have hg0 : g ρ = 0 := by simp [hg]
  have hlim2 : Tendsto g (𝓝[≠] ρ) (𝓝 0) := by
    rw [← hg0]; exact hgc.tendsto.mono_left nhdsWithin_le_nhds
  have := tendsto_nhds_unique (hlim.congr' hev) hlim2
  exact hm0 (by exact_mod_cast this)


open LeanLab.PNTPort.ZetaZeros in
/-- **An average Goldbach bound with exponent `1 + θ` confines the zeros**: if
`Σ_{n ≤ N} G(n) = N²/2 + O(N^{1+θ+ε})` for every `ε > 0`, `1/2 ≤ θ < 1`, then every zero of `ζ`
with `Re ρ > 0` has `1 − θ ≤ Re ρ ≤ θ`. -/
theorem zeros_in_strip_of_avgTheta (hθ : 1 / 2 ≤ θ) (hθ1 : θ < 1) (H : AvgTheta θ) {ρ : ℂ}
    (hz : riemannZeta ρ = 0) (h0 : 0 < ρ.re) : 1 - θ ≤ ρ.re ∧ ρ.re ≤ θ := by
  have hlt1 : ρ.re < 1 := by
    by_contra h; exact riemannZeta_ne_zero_of_one_le_re (not_lt.mp h) hz
  constructor
  · by_contra h
    push_neg at h
    exact no_zero_rightT hθ hθ1 H (ρ := 1 - ρ) (by simp; linarith) (by simp; linarith)
      (zeta_one_sub_eq_zero h0 hlt1 hz)
  · by_contra h
    push_neg at h
    exact no_zero_rightT hθ hθ1 H h hlt1 hz

/-- The case `θ = 1/2` is AvgRH. -/
lemma avgTheta_half_iff : AvgTheta (1 / 2) ↔ AvgRH := by
  unfold AvgTheta AvgRH
  constructor <;> intro h ε hε <;> obtain ⟨K, hK⟩ := h ε hε <;> refine ⟨K, fun N hN => ?_⟩ <;>
    have := hK N hN <;> ring_nf at this ⊢ <;> exact this

end LeanLab.GoldbachAverage.Converse
