/-
MMS https://arxiv.org/abs/1610.02017v2, page 12, unsmoothing and normalization.
Separate the uniform Fourier estimate with the actual reference mean
from the elementary replacement of that mean by its limiting value.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp420c
import LeanLab.Ternary.MMSBohrSmoothing
import LeanLab.Halupczok2012.U1439Combin
import LeanLab.PNTPort.LargeSieve.Basic
import LeanLab.PNTSieve.BrunTitchmarshAP
import LeanLab.Ternary.Decomp581b
import LeanLab.Ternary.Decomp678b

namespace LeanLab.Ternary.MMS.Task420
open Finset Filter Topology

/-- The MMS wheel is the standard primorial at its stated logarithmic cutoff.
MMS page 12 definition of W. -/
theorem wheel_eq_primorial (x : ℝ) :
    wheel x = primorial ⌊(0.1 : ℝ) * Real.log (Real.log x)⌋₊ := rfl

/-- The wheel modulus is positive at every real x.
MMS page 12 definition of W and Mathlib primorial_pos. -/
theorem wheel_pos (x : ℝ) : 0 < wheel x := by
  rw [wheel_eq_primorial]
  exact primorial_pos _

/-- The wheel is at most log x once x is at least exp one.
Derived elementary size bound for the normalization on MMS page 12. -/
theorem wheel_le_log {x : ℝ} (hx : Real.exp 1 ≤ x) : (wheel x : ℝ) ≤ Real.log x := by
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hx
  have hlx : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hx
    simpa only [Real.log_exp] using h
  have hll : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hlx
  have hf := Nat.floor_le (mul_nonneg (by norm_num : (0 : ℝ) ≤ 0.1) hll)
  have hfour : Real.log 4 ≤ 2 := by
    rw [show (4 : ℝ) = 2 ^ (2 : ℕ) by norm_num, Real.log_pow]
    norm_num
    linarith [Real.log_two_lt_d9]
  have hpow : (wheel x : ℝ) ≤ (4 : ℝ) ^ ⌊(0.1 : ℝ) * Real.log (Real.log x)⌋₊ := by
    rw [wheel_eq_primorial]
    exact_mod_cast primorial_le_four_pow ⌊(0.1 : ℝ) * Real.log (Real.log x)⌋₊
  calc
    _ ≤ (4 : ℝ) ^ ⌊(0.1 : ℝ) * Real.log (Real.log x)⌋₊ := hpow
    _ = Real.exp (Real.log 4 * (⌊(0.1 : ℝ) * Real.log (Real.log x)⌋₊ : ℝ)) := by
      rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    _ ≤ Real.exp (Real.log (Real.log x)) := by
      apply Real.exp_le_exp.mpr
      have hmul := mul_le_mul_of_nonneg_left hf
        (Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4))
      have hmul' := mul_le_mul_of_nonneg_right hfour hll
      nlinarith
    _ = Real.log x := Real.exp_log (by linarith)

/-- Every positive power of x eventually dominates the wheel.
Derived growth bound for the limiting mean replacement on MMS page 12. -/
theorem eventual_wheel_le_rpow (θ : ℝ) (hθ : 0 < θ) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → Real.exp 1 ≤ x ∧ (wheel x : ℝ) ≤ x ^ θ := by
  have hsmall := (isLittleO_log_rpow_atTop hθ).bound (by norm_num : (0 : ℝ) < 1)
  apply eventually_atTop.mp
  filter_upwards [hsmall, eventually_ge_atTop (Real.exp 1)] with x hx hxe
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hxe
  have hlog : 0 ≤ Real.log x := (wheel_le_log hxe).trans' (by positivity : 0 ≤ (wheel x : ℝ))
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlog,
    abs_of_nonneg (Real.rpow_nonneg hx0.le _), one_mul] at hx
  exact ⟨hxe, (wheel_le_log hxe).trans hx⟩

/-- One reduced wheel class contains at most four x to power theta divided by W integers.
The factor four absorbs the two closed endpoints. MMS page 12 normalization.
The proved general residue class count from Halupczok2012 is reused. -/
theorem class_card_mul_wheel_le {θ x : ℝ} (hx : 1 ≤ x)
    (hW : (wheel x : ℝ) ≤ x ^ θ) (c : ℕ) :
    (wheel x : ℝ) *
      (((ints (x - x ^ θ / 3) (x + x ^ θ)).filter
        (fun n => n ≡ c [MOD wheel x])).card : ℝ) ≤ 4 * x ^ θ := by
  let S := (ints (x - x ^ θ / 3) (x + x ^ θ)).filter
    (fun n => n ≡ c [MOD wheel x])
  have hx0 : 0 < x := by linarith
  have hp : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 _
  have hw0 : (0 : ℝ) < wheel x := by exact_mod_cast wheel_pos x
  have hw1 : (1 : ℝ) ≤ wheel x := by exact_mod_cast wheel_pos x
  have hcount := LeanLab.Halupczok2012.card_cong_le (S := S)
    (x := x - x ^ θ / 3 - 1) (y := 4 * x ^ θ / 3 + 1) (l := wheel x)
    (wheel_pos x) (by positivity) ?_ ?_
  · have hm : ((S.card : ℝ) - 1) * wheel x ≤ 4 * x ^ θ / 3 + 1 :=
      (le_div_iff₀ hw0).mp (by linarith)
    change (wheel x : ℝ) * (S.card : ℝ) ≤ 4 * x ^ θ
    nlinarith
  · intro n hn
    obtain ⟨hn, hnc⟩ := mem_filter.mp hn
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp hn
    have hnlo : x - x ^ θ / 3 ≤ n :=
      (Nat.le_ceil _).trans (by exact_mod_cast hlo)
    have hnhi : (n : ℝ) ≤ x + x ^ θ :=
      (show (n : ℝ) ≤ (⌊x + x ^ θ⌋₊ : ℝ) by exact_mod_cast hhi).trans
        (Nat.floor_le (by linarith))
    exact ⟨by linarith, by linarith⟩
  · intro n hn m hm
    have hn' := (mem_filter.mp hn).2
    have hm' := (mem_filter.mp hm).2
    exact Int.natCast_modEq_iff.mpr (hn'.trans hm'.symm)

/-- The unweighted exponential sum in a wheel class has the same cardinality bound.
MMS page 12, the coefficient replacement after unsmoothing. -/
theorem class_fourier_mul_wheel_le {θ x : ℝ} (hx : 1 ≤ x)
    (hW : (wheel x : ℝ) ≤ x ^ θ) (c : ℕ) (γ : ℝ) :
    (wheel x : ℝ) *
      ‖∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter
        (fun n => n ≡ c [MOD wheel x]), e (n * γ)‖ ≤ 4 * x ^ θ := by
  have hn := norm_sum_le
    ((ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]))
    (fun n => e (n * γ))
  simp only [norm_e, sum_const, nsmul_eq_mul, mul_one] at hn
  exact (mul_le_mul_of_nonneg_left hn (by positivity : (0 : ℝ) ≤ wheel x)).trans
    (class_card_mul_wheel_le hx hW c)

/-- Replacing a Fourier mean costs four times its scalar error.
MMS page 12, the limiting coefficient replacement. The normalization denominator
is written as the positive product of the totient and log x. -/
theorem mean_replacement_norm {A Z : ℂ} {W φ L r α β η : ℝ}
    (hW : 0 ≤ W) (hφ : 0 < φ) (hL : 0 < L)
    (hZ : W * ‖Z‖ ≤ 4 * r)
    (hA : ‖A - ((α / L * (W / φ) : ℝ) : ℂ) * Z‖ ≤ η * r / (φ * L)) :
    ‖A - ((β / L * (W / φ) : ℝ) : ℂ) * Z‖ ≤
      (η + 4 * |α - β|) * r / (φ * L) := by
  have hd : 0 < φ * L := mul_pos hφ hL
  have hc : α / L * (W / φ) - β / L * (W / φ) = (α - β) * W / (φ * L) := by
    field_simp
  have he : A - ((β / L * (W / φ) : ℝ) : ℂ) * Z =
      (A - ((α / L * (W / φ) : ℝ) : ℂ) * Z) +
        (((α - β) * W / (φ * L) : ℝ) : ℂ) * Z := by
    rw [← hc]
    push_cast
    ring
  have hterm : ‖(((α - β) * W / (φ * L) : ℝ) : ℂ) * Z‖ ≤
      4 * |α - β| * r / (φ * L) := by
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_mul,
      abs_of_nonneg hW, abs_of_pos hd]
    calc
      _ = (|α - β| * (W * ‖Z‖)) / (φ * L) := by ring
      _ ≤ (|α - β| * (4 * r)) / (φ * L) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hZ (abs_nonneg _)) hd.le
      _ = _ := by ring
  rw [he]
  calc
    _ ≤ ‖A - ((α / L * (W / φ) : ℝ) : ℂ) * Z‖ +
        ‖(((α - β) * W / (φ * L) : ℝ) : ℂ) * Z‖ := norm_add_le _ _
    _ ≤ η * r / (φ * L) + 4 * |α - β| * r / (φ * L) := add_le_add hA hterm
    _ = _ := by ring

/-- Hyp1 is stable when its mean changes by a controlled amount.
MMS page 12 coefficient replacement. CONDITIONAL ON the explicit Hyp1 input. -/
theorem hyp1_change_mean {θ x α β η : ℝ} {ρp : ℕ → ℝ} (hx : 1 < x)
    (hW : (wheel x : ℝ) ≤ x ^ θ) (H : Hyp1 θ x α η ρp) :
    Hyp1 θ x β (η + 4 * |α - β|) ρp := by
  intro c hc γ
  have hφ : (0 : ℝ) < (wheel x).totient := by
    exact_mod_cast Nat.totient_pos.mpr (wheel_pos x)
  exact mean_replacement_norm (by positivity) hφ (Real.log_pos hx)
    (class_fourier_mul_wheel_le hx.le hW c γ) (H c hc γ)

/-- Increasing the allowed Fourier error preserves Hyp1.
MMS page 12, choosing the mean and Fourier tolerances before x.
CONDITIONAL ON the explicit Hyp1 input. -/
theorem hyp1_mono_error {θ x α η η' : ℝ} {ρp : ℕ → ℝ}
    (hx : 1 < x) (hη : η ≤ η') (H : Hyp1 θ x α η ρp) :
    Hyp1 θ x α η' ρp := by
  intro c hc γ
  apply (H c hc γ).trans
  apply div_le_div_of_nonneg_right
  · exact mul_le_mul_of_nonneg_right hη (Real.rpow_nonneg (by linarith) _)
  · exact mul_nonneg (by positivity) (Real.log_pos hx).le

/-- LEAF. The actual reference mean normalizes the uniform short interval Fourier estimate.
MMS page 11 Proposition 5.1 and page 12 unsmoothing displays, before replacing
the long reference mean by its limiting coefficient. The written cancellation
proof is in sections 5.1 to 5.3, pages 13 to 27. No limiting mean value or
numerical Buchstab integral bound is assumed or concluded here. -/
theorem harman_fourier_reference_input (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      Hyp1 θ x (Task379.referenceMean x) η (Task361.harmanMajorant x) := by
  sorry

/-- The exact existing Fourier transfer statement from the reference mean estimate.
MMS page 12 last normalization step. The limiting mean hypothesis stays explicit.
CONDITIONAL ON harman_fourier_reference_input and the stated convergence input. -/
theorem harman_fourier_of_reference_mean_decomposed
    (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) (αp : ℝ)
    (hmean : ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |Task379.referenceMean x - αp| ≤ δ) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      Hyp1 θ x αp η (Task361.harmanMajorant x) := by
  intro η hη
  obtain ⟨X₁, hX₁⟩ := harman_fourier_reference_input θ hθ hθ1 (η / 2) (by linarith)
  obtain ⟨X₂, hX₂⟩ := hmean (η / 8) (by linarith)
  obtain ⟨X₃, hX₃⟩ := eventual_wheel_le_rpow θ (by linarith)
  refine ⟨max X₁ (max X₂ X₃), ?_⟩
  intro x hx
  have hx₁ := (le_max_left X₁ (max X₂ X₃)).trans hx
  have hx₂ := (le_max_left X₂ X₃).trans ((le_max_right X₁ (max X₂ X₃)).trans hx)
  have hx₃ := (le_max_right X₂ X₃).trans ((le_max_right X₁ (max X₂ X₃)).trans hx)
  obtain ⟨hxe, hw⟩ := hX₃ x hx₃
  have hx1 : 1 < x := lt_of_lt_of_le (by linarith [Real.exp_one_gt_d9]) hxe
  have h := hyp1_change_mean (β := αp) hx1 hw (hX₁ x hx₁)
  exact hyp1_mono_error hx1 (by have := hX₂ x hx₂; linarith) h

/-- The exact existing fixed mean Fourier input follows from the two refined analytic leaves.
MMS pages 11 and 12. The numerical envelope is now proved.
CONDITIONAL ON harman_reference_mean_enveloped and harman_fourier_reference_input. -/
theorem harman_fourier_input_decomposed (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) :
    ∃ αp : ℝ, 0 < αp ∧ αp < 2.9 ∧
      ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        Hyp1 θ x αp η (Task361.harmanMajorant x) := by
  obtain ⟨αp, hp, hp29, hmean⟩ := harman_reference_mean_decomposed
  exact ⟨αp, hp, hp29, harman_fourier_of_reference_mean_decomposed θ hθ hθ1 αp hmean⟩

/-! The proved cutoff and edge bookkeeping from Claude S107 is reused below.
Source branch claude/Ternary-feed1122-Decomp420d at 45b70d77de. -/
namespace Task704

/-- The smooth cutoff g of MMS page 12 second paragraph, transported to the
interval x minus x to the theta over three, x plus x to the theta of Hyp1.
For positive x and eps it vanishes off that interval and equals one at distance
at least eps x to the theta from both ends. Its j th derivative is of size at most
a constant depending on positive eps and j times x to the minus j theta. Built from Mathlib
smoothTransition. This particular profile is our choice of the paper g. -/
noncomputable def edgeCutoff (ε θ x t : ℝ) : ℝ :=
  Real.smoothTransition ((t - (x - x ^ θ / 3)) / (ε * x ^ θ)) *
    Real.smoothTransition ((x + x ^ θ - t) / (ε * x ^ θ))

/-- The cutoff is nonnegative. Derived from Mathlib smoothTransition.nonneg. -/
theorem edgeCutoff_nonneg (ε θ x t : ℝ) : 0 ≤ edgeCutoff ε θ x t :=
  mul_nonneg (Real.smoothTransition.nonneg _) (Real.smoothTransition.nonneg _)

/-- The cutoff is at most one. Derived from Mathlib smoothTransition.le_one. -/
theorem edgeCutoff_le_one (ε θ x t : ℝ) : edgeCutoff ε θ x t ≤ 1 := by
  unfold edgeCutoff
  have h1 := Real.smoothTransition.le_one ((t - (x - x ^ θ / 3)) / (ε * x ^ θ))
  have h2 := Real.smoothTransition.le_one ((x + x ^ θ - t) / (ε * x ^ θ))
  have h3 := Real.smoothTransition.nonneg ((x + x ^ θ - t) / (ε * x ^ θ))
  nlinarith [Real.smoothTransition.nonneg ((t - (x - x ^ θ / 3)) / (ε * x ^ θ))]

/-- Proved step toward edge_sieve_upper, MMS page 12 second paragraph: the weight
one minus g vanishes at distance at least eps x to the theta from both ends, so only
the two edge pieces carry the sieve sum. From Mathlib smoothTransition.one_of_one_le. -/
theorem one_sub_edgeCutoff_eq_zero_of_inner (ε θ x t : ℝ) (hw : 0 < ε * x ^ θ)
    (h1 : ε * x ^ θ ≤ t - (x - x ^ θ / 3)) (h2 : ε * x ^ θ ≤ x + x ^ θ - t) :
    1 - edgeCutoff ε θ x t = 0 := by
  unfold edgeCutoff
  rw [Real.smoothTransition.one_of_one_le ((one_le_div hw).mpr h1),
    Real.smoothTransition.one_of_one_le ((one_le_div hw).mpr h2)]
  ring

/-- Proved step toward edge_sieve_upper, MMS page 12 second paragraph: the edge
weight one minus g lies between zero and one, so the edge sum is at most the
plain sieve sum over the two edge pieces. From edgeCutoff_nonneg and edgeCutoff_le_one. -/
theorem one_sub_edgeCutoff_mem_Icc (ε θ x t : ℝ) :
    0 ≤ 1 - edgeCutoff ε θ x t ∧ 1 - edgeCutoff ε θ x t ≤ 1 :=
  ⟨sub_nonneg.mpr (edgeCutoff_le_one ε θ x t),
    sub_le_self _ (edgeCutoff_nonneg ε θ x t)⟩

/-- Proved leaf, MMS page 12 second paragraph, replacing g by one in the main term.
The weight one minus g lives on two intervals of length eps x to the theta, and each
meets one class modulo W in at most eps x to the theta over W plus one integers.
Originally class EASY, now proved. -/
theorem edge_count_bound (θ : ℝ) (hθ : 0 < θ) :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∀ c : ℕ, ∀ γ : ℝ,
      (wheel x : ℝ) *
        ‖∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
          ((1 - edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ ≤ 8 * ε * x ^ θ := by
  intro ε hε hε1
  have hsmall := (isLittleO_log_rpow_atTop hθ).bound hε
  obtain ⟨X₀, hX₀⟩ := Filter.eventually_atTop.mp
    (hsmall.and (Filter.eventually_ge_atTop (Real.exp 1)))
  refine ⟨X₀, fun x hx c γ => ?_⟩
  obtain ⟨hlog, hxe⟩ := hX₀ x hx
  have hx0 : 0 < x := (Real.exp_pos 1).trans_le hxe
  have hxθ : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 _
  have hlx : 0 ≤ Real.log x := Real.log_nonneg (by linarith [Real.add_one_le_exp (1 : ℝ)])
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg hlx, abs_of_pos hxθ] at hlog
  have hWlog := wheel_le_log hxe
  have hW1 : (1 : ℝ) ≤ wheel x := by exact_mod_cast wheel_pos x
  set δ := ε * x ^ θ with hδ
  have hδ0 : 0 < δ := mul_pos hε hxθ
  have hWδ : (wheel x : ℝ) ≤ δ := hWlog.trans hlog
  set S := (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]) with hS
  set S₁ := S.filter (fun n : ℕ => (n : ℝ) < x - x ^ θ / 3 + δ)
  set S₂ := S.filter (fun n : ℕ => x + x ^ θ - δ < (n : ℝ))
  have hmem : ∀ n ∈ S, x - x ^ θ / 3 ≤ n ∧ (n : ℝ) ≤ x + x ^ θ := by
    intro n hn
    obtain ⟨hlo, hhi⟩ := mem_Icc.mp (mem_filter.mp hn).1
    exact ⟨(Nat.le_ceil _).trans (by exact_mod_cast hlo),
      (show (n : ℝ) ≤ (⌊x + x ^ θ⌋₊ : ℝ) by exact_mod_cast hhi).trans
        (Nat.floor_le (by linarith))⟩
  have hcong : ∀ T ⊆ S, ∀ m ∈ T, ∀ m' ∈ T, (m : ℤ) ≡ (m' : ℤ) [ZMOD (wheel x)] := by
    intro T hT m hm m' hm'
    have h1 := (mem_filter.mp (hT hm)).2
    have h2 := (mem_filter.mp (hT hm')).2
    exact Int.natCast_modEq_iff.mpr (h1.trans h2.symm)
  have hc₁ : (S₁.card : ℝ) ≤ (δ + 1) / wheel x + 1 := by
    apply LeanLab.Halupczok2012.card_cong_le (x := x - x ^ θ / 3 - 1) (wheel_pos x)
      (by linarith) _ (hcong S₁ (filter_subset _ _))
    intro m hm
    obtain ⟨hmS, hm1⟩ := mem_filter.mp hm
    have := hmem m hmS
    constructor <;> linarith
  have hc₂ : (S₂.card : ℝ) ≤ δ / wheel x + 1 := by
    apply LeanLab.Halupczok2012.card_cong_le (x := x + x ^ θ - δ) (wheel_pos x)
      hδ0.le _ (hcong S₂ (filter_subset _ _))
    intro m hm
    obtain ⟨hmS, hm1⟩ := mem_filter.mp hm
    have := hmem m hmS
    constructor <;> linarith
  have hpt : ∀ n ∈ S, 1 - edgeCutoff ε θ x n ≤
      (if (n : ℝ) < x - x ^ θ / 3 + δ then 1 else 0) +
        (if x + x ^ θ - δ < (n : ℝ) then 1 else 0) := by
    intro n hn
    have hg0 := edgeCutoff_nonneg ε θ x n
    split_ifs with h1 h2 h2
    · linarith
    · linarith
    · linarith
    · push_neg at h1 h2
      have e1 : 1 ≤ ((n : ℝ) - (x - x ^ θ / 3)) / (ε * x ^ θ) :=
        (one_le_div hδ0).mpr (by linarith)
      have e2 : 1 ≤ (x + x ^ θ - (n : ℝ)) / (ε * x ^ θ) :=
        (one_le_div hδ0).mpr (by linarith)
      unfold edgeCutoff
      rw [Real.smoothTransition.one_of_one_le e1, Real.smoothTransition.one_of_one_le e2]
      norm_num
  have hnorm : ‖∑ n ∈ S, ((1 - edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ ≤
      (S₁.card : ℝ) + S₂.card := by
    apply (norm_sum_le _ _).trans
    have hle : ∑ n ∈ S, ‖((1 - edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ ≤
        ∑ n ∈ S, ((if (n : ℝ) < x - x ^ θ / 3 + δ then (1 : ℝ) else 0) +
          (if x + x ^ θ - δ < (n : ℝ) then 1 else 0)) := by
      apply sum_le_sum
      intro n hn
      rw [norm_mul, norm_e, mul_one, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [edgeCutoff_le_one ε θ x n])]
      exact hpt n hn
    refine hle.trans (le_of_eq ?_)
    rw [sum_add_distrib, ← sum_filter, ← sum_filter]
    simp [S₁, S₂]
  have hW0 : (0 : ℝ) < wheel x := by linarith
  calc
    _ ≤ (wheel x : ℝ) * ((δ + 1) / wheel x + 1 + (δ / wheel x + 1)) :=
      mul_le_mul_of_nonneg_left (hnorm.trans (add_le_add hc₁ hc₂)) hW0.le
    _ = 2 * δ + 1 + 2 * wheel x := by field_simp; ring
    _ ≤ 8 * ε * x ^ θ := by rw [hδ] at hWδ ⊢; nlinarith

/-- The unsmoothing algebra of MMS page 12 for one class and one frequency.
Derived triangle inequality step. -/
theorem unsmoothing_norm_bound {s : Finset ℕ} (ρp g : ℕ → ℝ) (f : ℕ → ℂ) (m : ℝ)
    (hρ : ∀ n ∈ s, 0 ≤ ρp n) (_hg0 : ∀ n ∈ s, 0 ≤ g n) (hg1 : ∀ n ∈ s, g n ≤ 1)
    (hf : ∀ n ∈ s, ‖f n‖ = 1) :
    ‖∑ n ∈ s, ((ρp n : ℝ) : ℂ) * f n - (m : ℂ) * ∑ n ∈ s, f n‖ ≤
      ‖∑ n ∈ s, ((ρp n * g n : ℝ) : ℂ) * f n - (m : ℂ) * ∑ n ∈ s, ((g n : ℝ) : ℂ) * f n‖ +
        ∑ n ∈ s, ρp n * (1 - g n) +
        |m| * ‖∑ n ∈ s, ((1 - g n : ℝ) : ℂ) * f n‖ := by
  have he : ∑ n ∈ s, ((ρp n : ℝ) : ℂ) * f n - (m : ℂ) * ∑ n ∈ s, f n =
      (∑ n ∈ s, ((ρp n * g n : ℝ) : ℂ) * f n - (m : ℂ) * ∑ n ∈ s, ((g n : ℝ) : ℂ) * f n) +
        ∑ n ∈ s, ((ρp n * (1 - g n) : ℝ) : ℂ) * f n -
        (m : ℂ) * ∑ n ∈ s, ((1 - g n : ℝ) : ℂ) * f n := by
    have h1 : ∑ n ∈ s, ((ρp n : ℝ) : ℂ) * f n =
        ∑ n ∈ s, ((ρp n * g n : ℝ) : ℂ) * f n + ∑ n ∈ s, ((ρp n * (1 - g n) : ℝ) : ℂ) * f n := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro n _
      push_cast
      ring
    have h2 : ∑ n ∈ s, f n =
        ∑ n ∈ s, ((g n : ℝ) : ℂ) * f n + ∑ n ∈ s, ((1 - g n : ℝ) : ℂ) * f n := by
      rw [← sum_add_distrib]
      apply sum_congr rfl
      intro n _
      push_cast
      ring
    rw [h1, h2]
    ring
  have hB : ‖∑ n ∈ s, ((ρp n * (1 - g n) : ℝ) : ℂ) * f n‖ ≤ ∑ n ∈ s, ρp n * (1 - g n) := by
    apply (norm_sum_le _ _).trans
    apply le_of_eq
    apply sum_congr rfl
    intro n hn
    rw [norm_mul, hf n hn, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (hρ n hn) (by linarith [hg1 n hn]))]
  rw [he]
  calc
    _ ≤ ‖(∑ n ∈ s, ((ρp n * g n : ℝ) : ℂ) * f n - (m : ℂ) * ∑ n ∈ s, ((g n : ℝ) : ℂ) * f n) +
          ∑ n ∈ s, ((ρp n * (1 - g n) : ℝ) : ℂ) * f n‖ +
        ‖(m : ℂ) * ∑ n ∈ s, ((1 - g n : ℝ) : ℂ) * f n‖ := norm_sub_le _ _
    _ ≤ _ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      linarith [norm_add_le
        (∑ n ∈ s, ((ρp n * g n : ℝ) : ℂ) * f n - (m : ℂ) * ∑ n ∈ s, ((g n : ℝ) : ℂ) * f n)
        (∑ n ∈ s, ((ρp n * (1 - g n) : ℝ) : ℂ) * f n)]

/-- The unit scale profile for the chosen short interval cutoff.
Derived rescaling of g on MMS page 12. -/
noncomputable def edgeProfile704 (ε u : ℝ) : ℝ :=
  Real.smoothTransition (u / ε) * Real.smoothTransition (((4 / 3 : ℝ) - u) / ε)

/-- The unit scale cutoff profile is smooth at every finite order.
Derived verification of the g hypothesis on MMS page 11 Proposition 5.1. -/
theorem edgeProfile704_contDiff (ε : ℝ) (j : ℕ) :
    ContDiff ℝ j (edgeProfile704 ε) := by
  exact (Real.smoothTransition.contDiff.comp (contDiff_id.div_const ε)).mul
    (Real.smoothTransition.contDiff.comp ((contDiff_const.sub contDiff_id).div_const ε))

/-- The unit profile vanishes outside its closed support interval for positive epsilon.
Derived support verification of the chosen g on MMS page 12. -/
theorem edgeProfile704_zero_outside {ε : ℝ} (hε : 0 < ε) {u : ℝ}
    (hu : u ≤ 0 ∨ (4 / 3 : ℝ) ≤ u) : edgeProfile704 ε u = 0 := by
  rcases hu with hu | hu
  · simp [edgeProfile704, Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg hu hε.le)]
  · simp [edgeProfile704, Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith : (4 / 3 : ℝ) - u ≤ 0) hε.le)]

/-- The unit scale profile has compact support for positive epsilon.
Derived support verification for MMS page 11 Proposition 5.1. -/
theorem edgeProfile704_hasCompactSupport {ε : ℝ} (hε : 0 < ε) :
    HasCompactSupport (edgeProfile704 ε) := by
  apply HasCompactSupport.intro (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) (4 / 3)))
  intro u hu
  simp only [Set.mem_Icc, not_and_or, not_le] at hu
  exact edgeProfile704_zero_outside hε (hu.imp le_of_lt le_of_lt)

/-- Every iterated derivative of the unit scale profile has compact support.
Derived regularity step for the g derivative bounds on MMS page 11. -/
theorem edgeProfile704_deriv_hasCompactSupport {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    HasCompactSupport (iteratedDeriv j (edgeProfile704 ε)) := by
  induction j with
  | zero => simpa using edgeProfile704_hasCompactSupport hε
  | succ j ih => rw [iteratedDeriv_succ]; exact ih.deriv

/-- A derivative of the unit scale profile is uniformly bounded in its argument.
The constant depends on epsilon and the derivative order, as allowed on MMS page 12. -/
theorem edgeProfile704_deriv_bound {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : ℝ, |iteratedDeriv j (edgeProfile704 ε) u| ≤ C := by
  obtain ⟨C, hC⟩ := ((edgeProfile704_contDiff ε j).continuous_iteratedDeriv' j).bounded_above_of_compact_support (edgeProfile704_deriv_hasCompactSupport hε j)
  refine ⟨max 1 C, lt_of_lt_of_le (by norm_num) (le_max_left _ _), fun u => ?_⟩
  exact (hC u).trans (le_max_right _ _)

/-- The actual cutoff is the unit profile transported to its short interval.
Derived affine identity for the g used on MMS page 12. -/
theorem edgeCutoff_eq_profile704 {ε θ x : ℝ} (hx : 0 < x) (t : ℝ) :
    edgeCutoff ε θ x t = edgeProfile704 ε ((t - (x - x ^ θ / 3)) / x ^ θ) := by
  have hp : x ^ θ ≠ 0 := (Real.rpow_pos_of_pos hx θ).ne'
  by_cases hε : ε = 0
  · simp [edgeCutoff, edgeProfile704, hε]
  · unfold edgeCutoff edgeProfile704
    congr 1 <;> congr 1 <;> field_simp [hp, hε] <;> ring

/-- Derivatives of the actual cutoff have the inverse short interval scale.
Derived chain rule for the g hypothesis on MMS page 11 Proposition 5.1. -/
theorem edgeCutoff_iteratedDeriv704 {ε θ x : ℝ} (hx : 0 < x) (j : ℕ) (t : ℝ) :
    iteratedDeriv j (edgeCutoff ε θ x) t = (x ^ θ)⁻¹ ^ j *
      iteratedDeriv j (edgeProfile704 ε) ((t - (x - x ^ θ / 3)) / x ^ θ) := by
  have he : edgeCutoff ε θ x =
      fun t => (fun u => edgeProfile704 ε ((x ^ θ)⁻¹ * u)) (t - (x - x ^ θ / 3)) := by
    funext t
    rw [edgeCutoff_eq_profile704 hx]
    simp only [div_eq_inv_mul]
  rw [he, iteratedDeriv_comp_sub_const j
    (fun u : ℝ => edgeProfile704 ε ((x ^ θ)⁻¹ * u)) (x - x ^ θ / 3),
    iteratedDeriv_comp_const_mul (edgeProfile704_contDiff ε j)]
  simp only [div_eq_inv_mul]

/-- The chosen g satisfies the uniform derivative size required by Proposition 5.1.
The constant is fixed before theta, x and t. MMS pages 11 and 12. -/
theorem edgeCutoff_deriv_bound704 {ε : ℝ} (hε : 0 < ε) (j : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ θ x : ℝ, 0 < x → ∀ t : ℝ,
      |iteratedDeriv j (edgeCutoff ε θ x) t| ≤ C / (x ^ θ) ^ j := by
  obtain ⟨C, hC, hb⟩ := edgeProfile704_deriv_bound hε j
  refine ⟨C, hC, fun θ x hx t => ?_⟩
  have hp := Real.rpow_pos_of_pos hx θ
  rw [edgeCutoff_iteratedDeriv704 hx, abs_mul, abs_pow,
    abs_of_pos (inv_pos.mpr hp)]
  calc
    _ ≤ (x ^ θ)⁻¹ ^ j * C :=
      mul_le_mul_of_nonneg_left (hb _) (pow_nonneg (inv_nonneg.mpr hp.le) j)
    _ = _ := by rw [inv_pow, div_eq_mul_inv, mul_comm]

/-- The actual cutoff is smooth at every finite order for positive x.
Derived verification of the g hypothesis on MMS pages 11 and 12. -/
theorem edgeCutoff_contDiff704 {ε θ x : ℝ} (hx : 0 < x) (j : ℕ) :
    ContDiff ℝ j (edgeCutoff ε θ x) := by
  have he : edgeCutoff ε θ x =
      fun t => edgeProfile704 ε ((t - (x - x ^ θ / 3)) / x ^ θ) :=
    funext (edgeCutoff_eq_profile704 hx)
  rw [he]
  exact (edgeProfile704_contDiff ε j).comp
    ((contDiff_id.sub contDiff_const).div_const _)

/-- The actual cutoff vanishes at and outside the short interval endpoints.
Derived verification of the support condition for g on MMS page 12. -/
theorem edgeCutoff_zero_outside704 {ε θ x : ℝ} (hε : 0 < ε) (hx : 0 < x) {t : ℝ}
    (ht : t ≤ x - x ^ θ / 3 ∨ x + x ^ θ ≤ t) : edgeCutoff ε θ x t = 0 := by
  have hden : 0 ≤ ε * x ^ θ := mul_nonneg hε.le (Real.rpow_nonneg hx.le θ)
  rcases ht with ht | ht
  · simp [edgeCutoff, Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (sub_nonpos.mpr ht) hden)]
  · simp [edgeCutoff, Real.smoothTransition.zero_of_nonpos
      (div_nonpos_of_nonpos_of_nonneg (by linarith : x + x ^ θ - t ≤ 0) hden)]

/-- The actual cutoff has compact support inside the required short interval.
Derived support verification for MMS page 11 Proposition 5.1. -/
theorem edgeCutoff_hasCompactSupport704 {ε θ x : ℝ} (hε : 0 < ε) (hx : 0 < x) :
    HasCompactSupport (edgeCutoff ε θ x) := by
  apply HasCompactSupport.intro
    (isCompact_Icc : IsCompact (Set.Icc (x - x ^ θ / 3) (x + x ^ θ)))
  intro t ht
  simp only [Set.mem_Icc, not_and_or, not_le] at ht
  exact edgeCutoff_zero_outside704 hε hx (ht.imp le_of_lt le_of_lt)

/-- Explicit analytic hypotheses suffice for the page 12 unsmoothing step.
For a nonnegative coefficient family, the smoothed Fourier bound, weighted edge
sieve bound and bounded reference mean
remain hypotheses. No convergence or cited theorem is used in this implication.
MMS page 12 three unsmoothing displays. CONDITIONAL ON the three explicit inputs. -/
theorem hyp1_of_unsmoothing_estimates704 (θ : ℝ) (hθ : 0 < θ)
    (ρp : ℝ → ℕ → ℝ) (μ : ℝ → ℝ) (hρ : ∀ x n, 0 ≤ ρp x n)
    (hSmooth : ∀ ε : ℝ, 0 < ε → ε < 1 →
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ c : ℕ, Nat.Coprime c (wheel x) → ∀ γ : ℝ,
        ‖∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
            ((ρp x n * edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ) -
          ((μ x / Real.log x * (wheel x / (wheel x).totient) : ℝ) : ℂ) *
          ∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
            ((edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ ≤
          η * x ^ θ / ((wheel x).totient * Real.log x))
    (hEdge :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ c : ℕ, Nat.Coprime c (wheel x) →
        ∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
            ρp x n * (1 - edgeCutoff ε θ x n) ≤
          C * ε * x ^ θ / ((wheel x).totient * Real.log x))
    (hMean : ∃ M : ℝ, 0 ≤ M ∧ ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      |μ x| ≤ M) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      Hyp1 θ x (μ x) η (ρp x) := by
  intro η hη
  obtain ⟨C, hC, hE⟩ := hEdge
  obtain ⟨M, hM, XM, hXM⟩ := hMean
  set ε : ℝ := min (1 / 2) (η / (3 * (C + 8 * M + 1))) with hεdef
  have hden : 0 < 3 * (C + 8 * M + 1) := by positivity
  have hε : 0 < ε := lt_min (by norm_num) (div_pos hη hden)
  have hε1 : ε < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hεη : ε * (3 * (C + 8 * M + 1)) ≤ η :=
    (le_div_iff₀ hden).mp (min_le_right _ _)
  obtain ⟨X₁, hX₁⟩ := hSmooth ε hε hε1 (η / 3) (by linarith)
  obtain ⟨X₂, hX₂⟩ := hE ε hε hε1
  obtain ⟨X₃, hX₃⟩ := edge_count_bound θ (by linarith) ε hε hε1
  refine ⟨max (max X₁ X₂) (max X₃ (max XM 2)), fun x hx => ?_⟩
  have hx₁ : X₁ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx₂ : X₂ ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx₃ : X₃ ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxM : XM ≤ x := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hx
  intro c hc γ
  have hφ : (0 : ℝ) < (wheel x).totient := by
    exact_mod_cast Nat.totient_pos.mpr (wheel_pos x)
  have hL : 0 < Real.log x := Real.log_pos (by linarith)
  have hD : 0 < ((wheel x).totient : ℝ) * Real.log x := mul_pos hφ hL
  have hW : (0 : ℝ) < wheel x := by exact_mod_cast wheel_pos x
  have hxθ : 0 < x ^ θ := Real.rpow_pos_of_pos (by linarith) _
  have hmain := unsmoothing_norm_bound
    (s := (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]))
    (ρp x) (fun n => edgeCutoff ε θ x n) (fun n => e (n * γ))
    (μ x / Real.log x * (wheel x / (wheel x).totient))
    (fun n _ => hρ x n) (fun n _ => edgeCutoff_nonneg _ _ _ _)
    (fun n _ => edgeCutoff_le_one _ _ _ _) (fun n _ => norm_e _)
  have h1 := hX₁ x hx₁ c hc γ
  have h2 := hX₂ x hx₂ c hc
  have h3 := hX₃ x hx₃ c γ
  have hm := hXM x hxM
  set N := ‖∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
          ((1 - edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ with hN
  have hmabs : |μ x / Real.log x * (wheel x / (wheel x).totient)| * N =
      |μ x| * ((wheel x : ℝ) * N) /
        (((wheel x).totient : ℝ) * Real.log x) := by
    rw [abs_mul, abs_div, abs_div, abs_of_pos hL, abs_of_pos hW, abs_of_pos hφ]
    field_simp
  have h3' : |μ x| * ((wheel x : ℝ) * N) ≤ M * (8 * ε * x ^ θ) :=
    mul_le_mul hm h3 (by positivity) hM
  have hfin : η / 3 * x ^ θ + C * ε * x ^ θ + M * (8 * ε * x ^ θ) ≤ η * x ^ θ := by
    have : C * ε + 8 * M * ε ≤ 2 * η / 3 := by nlinarith
    nlinarith
  calc
    _ ≤ _ := hmain
    _ ≤ η / 3 * x ^ θ / (((wheel x).totient : ℝ) * Real.log x) +
          C * ε * x ^ θ / (((wheel x).totient : ℝ) * Real.log x) +
          M * (8 * ε * x ^ θ) / (((wheel x).totient : ℝ) * Real.log x) := by
      rw [hmabs]
      gcongr
    _ = (η / 3 * x ^ θ + C * ε * x ^ θ + M * (8 * ε * x ^ θ)) /
          (((wheel x).totient : ℝ) * Real.log x) := by ring
    _ ≤ η * x ^ θ / (((wheel x).totient : ℝ) * Real.log x) := by gcongr

/-- Every rough indicator is at most one.
Derived for MMS page 11 equation 5.1. -/
theorem roughIndicator_le_one704 (n : ℕ) (y : ℝ) : Task361.roughIndicator n y ≤ 1 := by
  classical
  unfold Task361.roughIndicator
  split_ifs <;> norm_num

/-- Increasing the cutoff can only decrease the rough indicator.
Derived for MMS page 11 equation 5.1. -/
theorem roughIndicator_antitone704 (n : ℕ) {y z : ℝ} (hyz : y ≤ z) :
    Task361.roughIndicator n z ≤ Task361.roughIndicator n y := by
  classical
  unfold Task361.roughIndicator
  split_ifs with hz hy hy
  · norm_num
  · exact False.elim (hy fun p hp hpy => hz p hp (hpy.trans_le hyz))
  · norm_num
  · norm_num

/-- The rough indicator of a product is the product of the two rough indicators at the same cutoff.
Derived for MMS page 11 equation 5.1. -/
theorem roughIndicator_mul704 (a b : ℕ) (y : ℝ) :
    Task361.roughIndicator (a * b) y =
      Task361.roughIndicator a y * Task361.roughIndicator b y := by
  classical
  have he : (∀ p : ℕ, p.Prime → (p : ℝ) < y → ¬p ∣ a * b) ↔
      (∀ p : ℕ, p.Prime → (p : ℝ) < y → ¬p ∣ a) ∧
      (∀ p : ℕ, p.Prime → (p : ℝ) < y → ¬p ∣ b) := by
    constructor
    · intro h
      exact ⟨fun p hp hpy hd => h p hp hpy (dvd_mul_of_dvd_left hd b),
        fun p hp hpy hd => h p hp hpy (dvd_mul_of_dvd_right hd a)⟩
    · rintro ⟨ha, hb⟩ p hp hpy hd
      rcases hp.dvd_mul.mp hd with hd | hd
      · exact ha p hp hpy hd
      · exact hb p hp hpy hd
  unfold Task361.roughIndicator
  rw [he]
  split_ifs <;> simp_all

/-- For x at least one, failure of roughness at the tenth root cutoff forces the explicit Harman majorant to vanish.
Derived for MMS page 11 equation 5.1. -/
theorem harmanMajorant_zero_of_rough_zero704 {x : ℝ} (hx : 1 ≤ x) (n : ℕ)
    (hz : Task361.roughIndicator n (x ^ (1 / 10 : ℝ)) = 0) :
    Task361.harmanMajorant x n = 0 := by
  classical
  have hcut : x ^ (1 / 10 : ℝ) ≤ x ^ (1 / 4 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hx (by norm_num)
  have hfirst : Task361.roughIndicator n (x ^ (1 / 4 : ℝ)) = 0 :=
    le_antisymm ((roughIndicator_antitone704 n hcut).trans_eq hz)
      (Task361.roughIndicator_nonneg _ _)
  unfold Task361.harmanMajorant
  rw [hfirst, zero_add]
  apply sum_eq_zero
  intro p₁ hp₁
  apply sum_eq_zero
  intro p₂ hp₂
  apply sum_eq_zero
  intro p₃ hp₃
  split_ifs with h
  · obtain ⟨hp1, hp2, hp3, hlo, h12, h23, hhi, hd⟩ := h
    have h12r : (p₁ : ℝ) < p₂ := by exact_mod_cast h12
    have h23r : (p₂ : ℝ) < p₃ := by exact_mod_cast h23
    have hprod : Task361.roughIndicator (p₁ * p₂ * p₃) (x ^ (1 / 10 : ℝ)) = 1 := by
      rw [roughIndicator_mul704, roughIndicator_mul704,
        Task361.roughIndicator_prime hp1 hlo.le,
        Task361.roughIndicator_prime hp2 (hlo.trans h12r).le,
        Task361.roughIndicator_prime hp3 ((hlo.trans h12r).trans h23r).le]
      norm_num
    have hfactor : (p₁ * p₂ * p₃) * (n / (p₁ * p₂ * p₃)) = n := Nat.mul_div_cancel' hd
    have hnz : Task361.roughIndicator (n / (p₁ * p₂ * p₃)) (x ^ (1 / 10 : ℝ)) = 0 := by
      have he := roughIndicator_mul704 (p₁ * p₂ * p₃) (n / (p₁ * p₂ * p₃))
        (x ^ (1 / 10 : ℝ))
      rw [hfactor, hz, hprod, one_mul] at he
      exact he.symm
    exact le_antisymm ((roughIndicator_antitone704 _ hlo.le).trans_eq hnz)
      (Task361.roughIndicator_nonneg _ _)
  · rfl

/-- For x at least exp one hundred, a positive integer at most twice x that is rough at the tenth root cutoff has at most ten distinct prime factors.
Derived for MMS page 11 equation 5.1, derived multiplicity bound. -/
theorem rough_primeFactors_card_le704 {x : ℝ} (hx : Real.exp 100 ≤ x) {n : ℕ}
    (hn : 0 < n) (hxn : (n : ℝ) ≤ 2 * x)
    (hr : Task361.roughIndicator n (x ^ (1 / 10 : ℝ)) = 1) : n.primeFactors.card ≤ 10 := by
  classical
  have hx0 : 0 < x := (Real.exp_pos 100).trans_le hx
  have hx1 : 1 ≤ x := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hb : 2 < x ^ (1 / 10 : ℝ) := by
    have h := Real.rpow_le_rpow (Real.exp_pos 100).le hx (by norm_num : (0 : ℝ) ≤ 1 / 10)
    rw [← Real.exp_mul] at h
    norm_num at h
    linarith [Real.add_one_le_exp (10 : ℝ)]
  have hall : ∀ p : ℕ, p.Prime → (p : ℝ) < x ^ (1 / 10 : ℝ) → ¬p ∣ n := by
    unfold Task361.roughIndicator at hr
    split_ifs at hr with h
    · exact h
    · norm_num at hr
  have hp : ∀ p ∈ n.primeFactors, x ^ (1 / 10 : ℝ) ≤ (p : ℝ) := by
    intro p hp
    obtain ⟨hpp, hpd, hn0⟩ := Nat.mem_primeFactors.mp hp
    by_contra h
    exact hall p hpp (lt_of_not_ge h) hpd
  have hprod : (x ^ (1 / 10 : ℝ)) ^ n.primeFactors.card ≤ (n : ℝ) := by
    calc
      _ ≤ ∏ p ∈ n.primeFactors, (p : ℝ) := by
        rw [← prod_const]
        exact prod_le_prod₀ (fun _ _ => by positivity) hp
      _ = ((∏ p ∈ n.primeFactors, p : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ n := by exact_mod_cast Nat.le_of_dvd hn (Nat.prod_primeFactors_dvd n)
  have hten : (x ^ (1 / 10 : ℝ)) ^ (10 : ℕ) = x := by
    rw [← Real.rpow_mul_natCast hx0.le]
    norm_num
  by_contra h
  have hcard : 11 ≤ n.primeFactors.card := by omega
  have hpow := pow_le_pow_right₀ (by linarith : (1 : ℝ) ≤ x ^ (1 / 10 : ℝ)) hcard
  rw [pow_succ, hten] at hpow
  nlinarith

/-- At positive n the majorant is at most one plus the cube of the number of distinct prime factors of n. The candidate ordered triples are a subset of the cube of that factor set.
Derived for MMS page 11 equation 5.1. -/
theorem harmanMajorant_le_card_cube704 (x : ℝ) {n : ℕ} (hn : 0 < n) :
    Task361.harmanMajorant x n ≤ 1 + (n.primeFactors.card : ℝ) ^ 3 := by
  classical
  let R := range (n + 1)
  let F := n.primeFactors
  have hsub : F ⊆ R := by
    intro p hp
    exact mem_range.mpr (Nat.lt_succ_of_le (Nat.le_of_mem_primeFactors hp))
  have hsingle : (∑ p ∈ R, if p ∈ F then (1 : ℝ) else 0) = (F.card : ℝ) := by
    rw [← sum_filter]
    rw [filter_mem_eq_inter, inter_eq_right.mpr hsub]
    simp
  have htriple : ∑ p₁ ∈ R, ∑ p₂ ∈ R, ∑ p₃ ∈ R,
      (if p₁ ∈ F ∧ p₂ ∈ F ∧ p₃ ∈ F then (1 : ℝ) else 0) =
      (F.card : ℝ) ^ 3 := by
    have hid : ∀ a b c : ℕ,
        (if a ∈ F ∧ b ∈ F ∧ c ∈ F then (1 : ℝ) else 0) =
        (if a ∈ F then (1 : ℝ) else 0) *
        (if b ∈ F then (1 : ℝ) else 0) * (if c ∈ F then (1 : ℝ) else 0) := by
      intro a b c
      split_ifs <;> simp_all
    calc
      _ = (∑ p ∈ R, if p ∈ F then (1 : ℝ) else 0) *
          (∑ p ∈ R, if p ∈ F then (1 : ℝ) else 0) *
          (∑ p ∈ R, if p ∈ F then (1 : ℝ) else 0) := by
        simp only [sum_mul, mul_sum]
        apply sum_congr rfl
        intro a ha
        apply sum_congr rfl
        intro b hb
        apply sum_congr rfl
        intro c hc
        rw [hid]
        ring
      _ = _ := by rw [hsingle]; ring
  have hsum :
      (∑ p₁ ∈ range (n + 1), ∑ p₂ ∈ range (n + 1), ∑ p₃ ∈ range (n + 1),
        if p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ x ^ (1 / 10 : ℝ) < p₁ ∧
            p₁ < p₂ ∧ p₂ < p₃ ∧ (p₃ : ℝ) < x ^ (1 / 4 : ℝ) ∧ p₁ * p₂ * p₃ ∣ n then
          Task361.roughIndicator (n / (p₁ * p₂ * p₃)) p₁ else 0) ≤
        ∑ p₁ ∈ R, ∑ p₂ ∈ R, ∑ p₃ ∈ R,
          if p₁ ∈ F ∧ p₂ ∈ F ∧ p₃ ∈ F then (1 : ℝ) else 0 := by
    apply sum_le_sum
    intro p₁ hp₁
    apply sum_le_sum
    intro p₂ hp₂
    apply sum_le_sum
    intro p₃ hp₃
    by_cases h : p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ x ^ (1 / 10 : ℝ) < p₁ ∧
        p₁ < p₂ ∧ p₂ < p₃ ∧ (p₃ : ℝ) < x ^ (1 / 4 : ℝ) ∧ p₁ * p₂ * p₃ ∣ n
    · obtain ⟨hp1, hp2, hp3, hlo, h12, h23, hhi, hd⟩ := h
      have hf1 : p₁ ∈ F := hp1.mem_primeFactors
        ((dvd_mul_of_dvd_left (dvd_mul_right p₁ p₂) p₃).trans hd) hn.ne'
      have hf2 : p₂ ∈ F := hp2.mem_primeFactors
        ((dvd_mul_of_dvd_left (dvd_mul_left p₂ p₁) p₃).trans hd) hn.ne'
      have hf3 : p₃ ∈ F := hp3.mem_primeFactors ((dvd_mul_left p₃ (p₁ * p₂)).trans hd) hn.ne'
      rw [if_pos ⟨hp1, hp2, hp3, hlo, h12, h23, hhi, hd⟩,
        if_pos ⟨hf1, hf2, hf3⟩]
      exact roughIndicator_le_one704 _ _
    · rw [if_neg h]
      split_ifs <;> norm_num
  unfold Task361.harmanMajorant
  rw [htriple] at hsum
  exact add_le_add (roughIndicator_le_one704 _ _) hsum

/-- For x at least exp one hundred and positive n at most twice x, the majorant is at most 1001 times the rough indicator at the tenth root cutoff.
Derived for MMS page 11 equation 5.1, derived bound for page 12. -/
theorem harmanMajorant_le_rough704 {x : ℝ} (hx : Real.exp 100 ≤ x) {n : ℕ}
    (hn : 0 < n) (hxn : (n : ℝ) ≤ 2 * x) :
    Task361.harmanMajorant x n ≤ 1001 * Task361.roughIndicator n (x ^ (1 / 10 : ℝ)) := by
  have hx1 : 1 ≤ x := by linarith [Real.add_one_le_exp (100 : ℝ)]
  by_cases hr : Task361.roughIndicator n (x ^ (1 / 10 : ℝ)) = 0
  · rw [hr, mul_zero, harmanMajorant_zero_of_rough_zero704 hx1 n hr]
  · have hr1 : Task361.roughIndicator n (x ^ (1 / 10 : ℝ)) = 1 := by
      unfold Task361.roughIndicator at hr ⊢
      split_ifs at hr ⊢ with h
      · rfl
      · exact False.elim (hr rfl)
    have hc : (n.primeFactors.card : ℝ) ≤ 10 := by
      exact_mod_cast rough_primeFactors_card_le704 hx hn hxn hr1
    have hpow := pow_le_pow_left₀ (Nat.cast_nonneg n.primeFactors.card) hc 3
    rw [hr1, mul_one]
    have hh := harmanMajorant_le_card_cube704 x hn
    norm_num at hpow
    linarith

open LeanLab.PNTSieve.Sieve SelbergSieve LeanLab.PNTSieve.SelbergSieve BoundingSieve
open LeanLab.PNTSieve.BrunTitchmarshAP
open scoped ArithmeticFunction.zeta

/-- The number of integers in a positive interval of length y in one class modulo positive q and coprime to the product of primes at most z that do not divide q is at most twice y divided by phi q log z plus three z times one plus log z cubed, for z above one. This reuses the lab AP Selberg proof and its Apache 2.0 port.
Derived for MMS page 12 simple upper sieve, derived from PNTSieve.BrunTitchmarshAP. -/
theorem ap_sifted_card_upper704 (x y z : ℝ) (q a : ℕ)
    (hx : 0 < x) (hy : 0 < y) (hz : 1 < z) (hq : 0 < q) :
    (((Icc ⌈x⌉₊ ⌊x + y⌋₊).filter (fun n =>
      Nat.Coprime (∏ p ∈ coprimePrimes q z, p) n ∧ n % q = a % q)).card : ℝ) ≤
      2 * y / (q.totient * Real.log z) + 3 * z * (1 + Real.log z) ^ 3 := by
  classical
  set s := apSieve x y z q a hz.le with hs
  have hz0 : 0 < z := by linarith
  have hlz : 0 < Real.log z := Real.log_pos hz
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  set P := ∏ p ∈ coprimePrimes q z, p with hPdef
  have hsift : siftedSum (s := s.toBoundingSieve) =
      (((Icc ⌈x⌉₊ ⌊x + y⌋₊).filter (fun n => Nat.Coprime P n ∧ n % q = a % q)).card : ℝ) := by
    unfold siftedSum
    rw [card_eq_sum_ones, Nat.cast_sum, sum_filter]
    refine sum_congr rfl (fun n _ => ?_)
    simp only [hs, apSieve]
    by_cases h1 : Nat.Coprime P n <;> by_cases h2 : n % q = a % q <;> simp_all [hPdef]
  -- (ii) the Selberg bound
  have hsel := LeanLab.PNTSieve.SelbergSieve.selberg_bound_simple s
  -- (iii) the bounding sum
  have hnu : s.nu = (ζ : ArithmeticFunction ℝ).pdiv .id := rfl
  have hbs := LeanLab.PNTSieve.Sieve.boundingSum_ge_sum_filter s
    (fun m => 1 ≤ m ∧ Nat.Coprime m q ∧ m ≤ ⌊Real.sqrt z⌋₊)
    (by
      intro m hm p hp hpm
      have hm1 : 1 ≤ m := hm.1
      replace hm := hm.2
      have hpm' : p ≤ m := Nat.le_of_dvd hm1 hpm
      have hmz : (m : ℝ) ≤ z := by
        have : (m : ℝ) ≤ ⌊Real.sqrt z⌋₊ := by exact_mod_cast hm.2
        exact this.trans ((Nat.floor_le (Real.sqrt_nonneg z)).trans
          (LeanLab.PNTSieve.Sieve.sqrt_le_self z hz.le))
      have hpz : p ≤ ⌊z⌋₊ := Nat.le_floor (by exact_mod_cast (show (p : ℝ) ≤ z by
        exact (by exact_mod_cast hpm' : (p : ℝ) ≤ m).trans hmz))
      have hpq : ¬ p ∣ q := by
        intro h
        exact (Nat.Prime.coprime_iff_not_dvd hp).mp (Nat.Coprime.coprime_dvd_left hpm hm.1) h
      exact dvd_prod_of_mem _ (mem_filter.mpr ⟨mem_range.mpr (by omega), hp, hpq⟩))
    (by rw [hnu]; exact CompletelyMultiplicative.zeta.pdiv CompletelyMultiplicative.id)
    (by
      intro n; rw [hnu]
      apply div_nonneg
      · by_cases h : n = 0 <;> simp [h]
      simp)
    (by
      intro p hpp _
      rw [hnu]
      simp only [ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply, Nat.cast_ite, CharP.cast_eq_zero, Nat.cast_one,
        ArithmeticFunction.id_apply]
      rw [ite_eq_right, one_div]
      · apply inv_lt_one_of_one_lt₀; norm_cast
        exact hpp.one_lt
      exact hpp.ne_zero)
  have hfilt : ∑ m ∈ (Icc 1 ⌊Real.sqrt s.level⌋₊).filter
        (fun m => 1 ≤ m ∧ Nat.Coprime m q ∧ m ≤ ⌊Real.sqrt z⌋₊), s.nu m =
      ∑ m ∈ (Icc 1 ⌊Real.sqrt z⌋₊).filter (fun m => Nat.Coprime m q), (1 : ℝ) / m := by
    have hl : s.level = z := rfl
    rw [hl]
    apply sum_congr
    · ext m; simp only [mem_filter, mem_Icc]; constructor
      · rintro ⟨⟨h1, h2⟩, _, h3, _⟩; exact ⟨⟨h1, h2⟩, h3⟩
      · rintro ⟨⟨h1, h2⟩, h3⟩; exact ⟨⟨h1, h2⟩, h1, h3, h2⟩
    · intro m hm
      simp only [mem_filter, mem_Icc] at hm
      rw [hnu]
      simp only [one_div, ArithmeticFunction.pdiv_apply, ArithmeticFunction.natCoe_apply,
        ArithmeticFunction.zeta_apply_ne (show m ≠ 0 by omega), Nat.cast_one,
        ArithmeticFunction.id_apply]
  have hharm := LeanLab.PNTPort.BVMax.coprime_harm_ge q ⌊Real.sqrt z⌋₊ hq
  have hlogsq : Real.log z / 2 ≤ Real.log ((⌊Real.sqrt z⌋₊ : ℝ) + 1) := by
    rw [← Real.log_sqrt hz0.le]
    exact Real.log_le_log (Real.sqrt_pos.mpr hz0) (Nat.lt_floor_add_one _).le
  have hS : (q.totient : ℝ) / q * (Real.log z / 2) ≤ selbergBoundingSum s := by
    have h1 : (q.totient : ℝ) / q * (Real.log z / 2) ≤
        (q.totient : ℝ) / q * Real.log ((⌊Real.sqrt z⌋₊ : ℝ) + 1) :=
      mul_le_mul_of_nonneg_left hlogsq (by positivity)
    have h2 : ∑ m ∈ (Icc 1 ⌊Real.sqrt z⌋₊).filter (fun m => Nat.Coprime m q), (1 : ℝ) / m ≤
        selbergBoundingSum s := by
      have := hbs
      rw [ge_iff_le] at this
      convert this using 1
      convert hfilt.symm using 3
    linarith
  have hSpos : 0 < (q.totient : ℝ) / q * (Real.log z / 2) := by positivity
  have hmain : s.totalMass / selbergBoundingSum s ≤ 2 * y / (q.totient * Real.log z) := by
    have hX : s.totalMass = y / q := rfl
    rw [hX]
    calc y / q / selbergBoundingSum s ≤ y / q / ((q.totient : ℝ) / q * (Real.log z / 2)) :=
          div_le_div_of_nonneg_left (by positivity) hSpos hS
      _ = 2 * y / (q.totient * Real.log z) := by field_simp
  -- (iv) the remainders
  have herr := LeanLab.PNTSieve.Sieve.rem_sum_le_of_const_dvd s 3
    (fun d hd => abs_rem_le x y z q a hx hy hz.le hq hd)
  have hl : s.level = z := rfl
  rw [hl] at herr
  have hsel' : siftedSum (s := s.toBoundingSieve) ≤ s.totalMass / selbergBoundingSum s +
      3 * z * (1 + Real.log z) ^ 3 := hsel.trans (add_le_add le_rfl herr)
  rw [← hsift]
  exact hsel'.trans (add_le_add hmain le_rfl)

/-- For a roughness cutoff r strictly above z above one, the rough count in any positive interval and class modulo positive q has the same AP Selberg upper bound.
Derived for MMS page 12 simple upper sieve. -/
theorem rough_ap_sum_upper704 (u v z r : ℝ) (q c : ℕ)
    (hu : 0 < u) (hv : 0 < v) (hz : 1 < z) (hqr : 0 < q) (hzr : z < r) :
    (∑ n ∈ (ints u (u + v)).filter (fun n => n ≡ c [MOD q]),
      Task361.roughIndicator n r) ≤
      2 * v / (q.totient * Real.log z) + 3 * z * (1 + Real.log z) ^ 3 := by
  classical
  let P : ℕ := ∏ p ∈ coprimePrimes q z, p
  let S := (ints u (u + v)).filter (fun n => n ≡ c [MOD q])
  have hpoint : ∀ n : ℕ, Task361.roughIndicator n r ≤
      if Nat.Coprime P n then (1 : ℝ) else 0 := by
    intro n
    unfold Task361.roughIndicator
    split_ifs with hR hC hC
    · exact le_rfl
    · apply False.elim
      apply hC
      apply Nat.coprime_prod_left_iff.mpr
      intro p hp
      have hpp := coprimePrimes_prime hp
      have hpFloor : p ≤ ⌊z⌋₊ := Nat.lt_succ_iff.mp
        (mem_range.mp (mem_filter.mp hp).1)
      have hpz : (p : ℝ) ≤ z :=
        (show (p : ℝ) ≤ (⌊z⌋₊ : ℝ) by exact_mod_cast hpFloor).trans
          (Nat.floor_le (by linarith))
      exact (hpp.coprime_iff_not_dvd).mpr (hR p hpp (hpz.trans_lt hzr))
    · norm_num
    · norm_num
  have he : S.filter (fun n => Nat.Coprime P n) =
      (Icc ⌈u⌉₊ ⌊u + v⌋₊).filter (fun n => Nat.Coprime P n ∧ n % q = c % q) := by
    ext n
    constructor
    · intro hn
      obtain ⟨hnS, hcop⟩ := Finset.mem_filter.mp hn
      obtain ⟨hnI, hmod⟩ := Finset.mem_filter.mp hnS
      exact Finset.mem_filter.mpr ⟨hnI, hcop, hmod⟩
    · intro hn
      obtain ⟨hnI, hcop, hmod⟩ := Finset.mem_filter.mp hn
      exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr ⟨hnI, hmod⟩, hcop⟩
  calc
    _ ≤ ∑ n ∈ S, if Nat.Coprime P n then (1 : ℝ) else 0 :=
      sum_le_sum (fun n hn => hpoint n)
    _ = ((S.filter (fun n => Nat.Coprime P n)).card : ℝ) := by
      simp only [card_eq_sum_ones, Nat.cast_sum, sum_filter, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
    _ ≤ _ := by
      rw [he]
      exact ap_sifted_card_upper704 u v z q c hu hv hz hqr

/-- For x at least exp one hundred, theta at most one and positive epsilon, the weighted cutoff loss in every wheel class is at most 1001 times the sum of the rough counts on the two closed edge intervals of length epsilon x to power theta.
Derived for MMS page 12 unsmoothing displays. -/
theorem harman_edge_mass_le_rough704 {θ x ε : ℝ} (hx : Real.exp 100 ≤ x)
    (hθ : θ ≤ 1) (hε : 0 < ε) (c : ℕ) :
    (∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter
        (fun n => n ≡ c [MOD wheel x]),
      Task361.harmanMajorant x n * (1 - edgeCutoff ε θ x n)) ≤
      1001 * ((∑ n ∈ (ints (x - x ^ θ / 3) (x - x ^ θ / 3 + ε * x ^ θ)).filter
        (fun n => n ≡ c [MOD wheel x]), Task361.roughIndicator n (x ^ (1 / 10 : ℝ))) +
      ∑ n ∈ (ints (x + x ^ θ - ε * x ^ θ) (x + x ^ θ)).filter
        (fun n => n ≡ c [MOD wheel x]), Task361.roughIndicator n (x ^ (1 / 10 : ℝ))) := by
  classical
  have hx0 : 0 < x := (Real.exp_pos 100).trans_le hx
  have hx1 : 1 ≤ x := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hr0 : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 θ
  have hrx : x ^ θ ≤ x := Real.rpow_le_self_of_one_le hx1 hθ
  let L := x - x ^ θ / 3
  let U := x + x ^ θ
  let δ := ε * x ^ θ
  have hδ0 : 0 < δ := mul_pos hε hr0
  let S := (ints L U).filter (fun n => n ≡ c [MOD wheel x])
  let S₁ := S.filter (fun n : ℕ => (n : ℝ) < L + δ)
  let S₂ := S.filter (fun n : ℕ => U - δ < (n : ℝ))
  have hmem : ∀ n ∈ S, L ≤ (n : ℝ) ∧ (n : ℝ) ≤ U := by
    intro n hn
    obtain ⟨hnlo, hnhi⟩ := mem_Icc.mp (mem_filter.mp hn).1
    exact ⟨(Nat.le_ceil L).trans (by exact_mod_cast hnlo),
      (show (n : ℝ) ≤ (⌊U⌋₊ : ℝ) by exact_mod_cast hnhi).trans
        (Nat.floor_le (by dsimp [U]; positivity))⟩
  have hpt : ∀ n ∈ S, 1 - edgeCutoff ε θ x n ≤
      (if (n : ℝ) < L + δ then 1 else 0) +
        (if U - δ < (n : ℝ) then 1 else 0) := by
    intro n hn
    have hg := edgeCutoff_nonneg ε θ x n
    split_ifs with h1 h2 h2
    · linarith
    · linarith
    · linarith
    · have h1' := le_of_not_gt h1
      have h2' := le_of_not_gt h2
      have hz := one_sub_edgeCutoff_eq_zero_of_inner ε θ x n hδ0
        (by dsimp [L, δ] at h1'; linarith)
        (by dsimp [U, δ] at h2'; linarith)
      rw [hz]
      norm_num
  have hsub₁ : S₁ ⊆ (ints L (L + δ)).filter (fun n => n ≡ c [MOD wheel x]) := by
    intro n hn
    obtain ⟨hnS, hnlo⟩ := mem_filter.mp hn
    obtain ⟨hnI, hnc⟩ := mem_filter.mp hnS
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp hnI).1, Nat.le_floor hnlo.le⟩, hnc⟩
  have hsub₂ : S₂ ⊆ (ints (U - δ) U).filter (fun n => n ≡ c [MOD wheel x]) := by
    intro n hn
    obtain ⟨hnS, hnhi⟩ := mem_filter.mp hn
    obtain ⟨hnI, hnc⟩ := mem_filter.mp hnS
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨Nat.ceil_le.mpr hnhi.le, (mem_Icc.mp hnI).2⟩, hnc⟩
  have hb₁ := sum_le_sum_of_subset_of_nonneg hsub₁
    (fun n _ _ => Task361.roughIndicator_nonneg n (x ^ (1 / 10 : ℝ)))
  have hb₂ := sum_le_sum_of_subset_of_nonneg hsub₂
    (fun n _ _ => Task361.roughIndicator_nonneg n (x ^ (1 / 10 : ℝ)))
  have hsum : (∑ n ∈ S, Task361.harmanMajorant x n * (1 - edgeCutoff ε θ x n)) ≤
      1001 * (∑ n ∈ S₁, Task361.roughIndicator n (x ^ (1 / 10 : ℝ))) +
        1001 * ∑ n ∈ S₂, Task361.roughIndicator n (x ^ (1 / 10 : ℝ)) := by
    calc
      _ ≤ ∑ n ∈ S, 1001 * Task361.roughIndicator n (x ^ (1 / 10 : ℝ)) *
          ((if (n : ℝ) < L + δ then 1 else 0) +
            (if U - δ < (n : ℝ) then 1 else 0)) := by
        apply sum_le_sum
        intro n hn
        obtain ⟨hnlo, hnhi⟩ := hmem n hn
        have hn0 : 0 < n := by exact_mod_cast (show (0 : ℝ) < n by dsimp [L] at hnlo; linarith)
        have hn2x : (n : ℝ) ≤ 2 * x := by dsimp [U] at hnhi; linarith
        have hm := harmanMajorant_le_rough704 hx hn0 hn2x
        exact (mul_le_mul_of_nonneg_right hm
          (sub_nonneg.mpr (edgeCutoff_le_one _ _ _ _))).trans
          (mul_le_mul_of_nonneg_left (hpt n hn)
            (mul_nonneg (by norm_num) (Task361.roughIndicator_nonneg _ _)))
      _ = _ := by
        simp_rw [mul_add, mul_ite, mul_one, mul_zero]
        rw [sum_add_distrib, ← sum_filter, ← sum_filter]
        simp only [S₁, S₂, mul_sum]
  change (∑ n ∈ S, Task361.harmanMajorant x n * (1 - edgeCutoff ε θ x n)) ≤
    1001 * ((∑ n ∈ (ints L (L + δ)).filter (fun n => n ≡ c [MOD wheel x]),
      Task361.roughIndicator n (x ^ (1 / 10 : ℝ))) +
      (∑ n ∈ (ints (U - δ) U).filter (fun n => n ≡ c [MOD wheel x]),
        Task361.roughIndicator n (x ^ (1 / 10 : ℝ))))
  nlinarith

/-- For theta greater than one twentieth and positive epsilon, the AP sieve error with level x to power one twentieth is eventually at most epsilon x to power theta divided by phi W log x. The threshold is chosen after epsilon.
Derived for MMS page 12 simple upper sieve, derived error absorption. -/
theorem eventual_edge_sieve_budget704 (θ : ℝ) (hθ : (1 / 20 : ℝ) < θ)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ X : ℝ, ∀ x : ℝ, X ≤ x → Real.exp 100 ≤ x ∧
      3 * x ^ (1 / 20 : ℝ) * (1 + Real.log (x ^ (1 / 20 : ℝ))) ^ 3 ≤
        ε * x ^ θ / ((wheel x).totient * Real.log x) := by
  have hgap : 0 < θ - 1 / 20 := by linarith
  have hs := (isLittleO_log_rpow_rpow_atTop (5 : ℝ) hgap).bound
    (div_pos hε (by norm_num : (0 : ℝ) < 24))
  obtain ⟨X, hX⟩ := eventually_atTop.mp (hs.and (eventually_ge_atTop (Real.exp 100)))
  refine ⟨X, fun x hx => ?_⟩
  obtain ⟨hh, hxe⟩ := hX x hx
  refine ⟨hxe, ?_⟩
  have hx0 : 0 < x := (Real.exp_pos 100).trans_le hxe
  have hlx : 100 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 100) hxe
    simpa only [Real.log_exp] using h
  have hL : 0 ≤ Real.log x := by linarith
  have hφ : (0 : ℝ) < (wheel x).totient := by
    exact_mod_cast Nat.totient_pos.mpr (wheel_pos x)
  have hφL : 0 < ((wheel x).totient : ℝ) * Real.log x := mul_pos hφ (by linarith)
  have hW : (wheel x : ℝ) ≤ Real.log x :=
    wheel_le_log ((Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 100)).trans hxe)
  have hφb : ((wheel x).totient : ℝ) ≤ Real.log x :=
    (show ((wheel x).totient : ℝ) ≤ wheel x by exact_mod_cast Nat.totient_le _).trans hW
  have hφLb : ((wheel x).totient : ℝ) * Real.log x ≤ Real.log x ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_right hφb hL]
  have hlogz : Real.log (x ^ (1 / 20 : ℝ)) = (1 / 20 : ℝ) * Real.log x :=
    Real.log_rpow hx0 _
  have hcoef : (1 + Real.log (x ^ (1 / 20 : ℝ))) ^ 3 ≤ (2 * Real.log x) ^ 3 := by
    apply pow_le_pow_left₀
    · rw [hlogz]; positivity
    · rw [hlogz]; linarith
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hL _),
    abs_of_pos (Real.rpow_pos_of_pos hx0 _)] at hh
  have hh' : Real.log x ^ (5 : ℕ) ≤ (ε / 24) * x ^ (θ - 1 / 20) := by
    simpa only [Real.rpow_ofNat] using hh
  have hpow : x ^ (1 / 20 : ℝ) * x ^ (θ - 1 / 20) = x ^ θ := by
    rw [← Real.rpow_add hx0]
    congr 1
    ring
  apply (le_div_iff₀ hφL).mpr
  calc
    _ ≤ (3 * x ^ (1 / 20 : ℝ) * (2 * Real.log x) ^ 3) * Real.log x ^ 2 :=
      mul_le_mul (mul_le_mul_of_nonneg_left hcoef (by positivity)) hφLb
        (by positivity) (by positivity)
    _ = 24 * x ^ (1 / 20 : ℝ) * Real.log x ^ (5 : ℕ) := by ring
    _ ≤ 24 * x ^ (1 / 20 : ℝ) * ((ε / 24) * x ^ (θ - 1 / 20)) :=
      mul_le_mul_of_nonneg_left hh' (by positivity)
    _ = ε * x ^ θ := by rw [← hpow]; ring

/-- For each theta strictly between 11 over 20 and one, the weighted cutoff loss has a constant uniform in epsilon strictly between zero and one. The proof supplies C equal to 82082. Every sufficiently large x and every reduced wheel class satisfy the bound C epsilon x to power theta divided by phi W log x. No prime distribution or reference mean hypothesis is used.
Derived for MMS page 12 second paragraph and unsmoothing displays. -/
theorem harman_edge_sieve_upper704 (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ c : ℕ, Nat.Coprime c (wheel x) →
        ∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
            Task361.harmanMajorant x n * (1 - edgeCutoff ε θ x n) ≤
          C * ε * x ^ θ / ((wheel x).totient * Real.log x) := by
  refine ⟨82082, by norm_num, ?_⟩
  intro ε hε hε1
  obtain ⟨X, hX⟩ := eventual_edge_sieve_budget704 θ (by linarith) ε hε
  refine ⟨X, fun x hx c hc => ?_⟩
  obtain ⟨hxe, herr⟩ := hX x hx
  have hx0 : 0 < x := (Real.exp_pos 100).trans_le hxe
  have hx1 : 1 < x := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hr0 : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 _
  have hrx : x ^ θ ≤ x := Real.rpow_le_self_of_one_le hx1.le hθ1.le
  have hz : 1 < x ^ (1 / 20 : ℝ) := Real.one_lt_rpow hx1 (by norm_num)
  have hzr : x ^ (1 / 20 : ℝ) < x ^ (1 / 10 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hx1 (by norm_num)
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hφ : (0 : ℝ) < (wheel x).totient := by
    exact_mod_cast Nat.totient_pos.mpr (wheel_pos x)
  have hlogz : Real.log (x ^ (1 / 20 : ℝ)) = (1 / 20 : ℝ) * Real.log x :=
    Real.log_rpow hx0 _
  let L := x - x ^ θ / 3
  let U := x + x ^ θ
  let δ := ε * x ^ θ
  have hδ : 0 < δ := mul_pos hε hr0
  have hL : 0 < L := by dsimp [L]; linarith
  have hR : 0 < U - δ := by
    have h := mul_lt_mul_of_pos_right hε1 hr0
    dsimp [U, δ]
    linarith
  have hleft := rough_ap_sum_upper704 L δ (x ^ (1 / 20 : ℝ))
    (x ^ (1 / 10 : ℝ)) (wheel x) c hL hδ hz (wheel_pos x) hzr
  have hright := rough_ap_sum_upper704 (U - δ) δ (x ^ (1 / 20 : ℝ))
    (x ^ (1 / 10 : ℝ)) (wheel x) c hR hδ hz (wheel_pos x) hzr
  simp only [sub_add_cancel] at hright
  have hmain : 2 * δ / ((wheel x).totient * Real.log (x ^ (1 / 20 : ℝ))) =
      40 * δ / ((wheel x).totient * Real.log x) := by
    rw [hlogz]
    field_simp
    ring
  rw [hmain] at hleft hright
  have htwo : (∑ n ∈ (ints L (L + δ)).filter (fun n => n ≡ c [MOD wheel x]),
      Task361.roughIndicator n (x ^ (1 / 10 : ℝ))) +
      (∑ n ∈ (ints (U - δ) U).filter (fun n => n ≡ c [MOD wheel x]),
        Task361.roughIndicator n (x ^ (1 / 10 : ℝ))) ≤
      82 * ε * x ^ θ / ((wheel x).totient * Real.log x) := by
    dsimp [δ] at hleft hright ⊢
    have h40 : 40 * (ε * x ^ θ) / ((wheel x).totient * Real.log x) =
        40 * (ε * x ^ θ / ((wheel x).totient * Real.log x)) := by ring
    rw [h40] at hleft hright
    calc
      _ ≤ 82 * (ε * x ^ θ / ((wheel x).totient * Real.log x)) := by
        linarith only [hleft, hright, herr]
      _ = _ := by ring
  have hm := harman_edge_mass_le_rough704 hxe hθ1.le hε c
  change (∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter
      (fun n => n ≡ c [MOD wheel x]),
      Task361.harmanMajorant x n * (1 - edgeCutoff ε θ x n)) ≤ _
  refine hm.trans ?_
  calc
    _ ≤ 1001 * (82 * ε * x ^ θ / ((wheel x).totient * Real.log x)) :=
      mul_le_mul_of_nonneg_left htwo (by norm_num)
    _ = _ := by ring

/-- The actual reference mean is eventually bounded by the upper sieve alone.
MMS pages 11 and 12. This uses the positive fixed profile mass and no mean limit. -/
theorem referenceMean_bounded_by_sieve704 :
    ∃ M : ℝ, 0 ≤ M ∧ ∃ X : ℝ, ∀ x : ℝ, X ≤ x → |Task379.referenceMean x| ≤ M := by
  obtain ⟨B, hB, hWeight⟩ := Task678.referenceWeight_deriv_bound 0
  let J : ℝ := ∫ u in (0 : ℝ)..1, Task678.referenceProfile u
  have hJ : 0 < J := by
    have h := Task379.referenceWeight_integral_pos (x := 1) (by norm_num)
    rw [Task678.referenceWeight_integral_scale (x := 1) (by norm_num)] at h
    simpa [J, Task379.referenceLength] using h
  obtain ⟨X, hX⟩ := eventual_edge_sieve_budget704 (3 / 4) (by norm_num) 1 one_pos
  refine ⟨B * 1001 * 41 / J, by positivity, max X (Real.exp 256), fun x hx => ?_⟩
  have hxX : X ≤ x := (le_max_left _ _).trans hx
  have hx256 : Real.exp 256 ≤ x := (le_max_right _ _).trans hx
  obtain ⟨hxe, herr⟩ := hX x hxX
  simp only [one_mul] at herr
  have hx0 : 0 < x := (Real.exp_pos 256).trans_le hx256
  have hx1 : 1 < x := by linarith [Real.add_one_le_exp (256 : ℝ)]
  have hlog : 0 < Real.log x := Real.log_pos hx1
  let H := Task379.referenceLength x
  have hH : 0 < H := Task379.referenceLength_pos hx0
  have hHle : H ≤ x := by
    change x * Real.exp (-Real.sqrt (Real.log x)) ≤ x
    have he : Real.exp (-Real.sqrt (Real.log x)) ≤ 1 :=
      Real.exp_le_one_iff.mpr (neg_nonpos.mpr (Real.sqrt_nonneg _))
    simpa using mul_le_mul_of_nonneg_left he hx0.le
  have hHlo : x ^ (3 / 4 : ℝ) ≤ H := by
    have h := Task581.reference_rescaled_length_ge_three_quarters (d := 1)
      hx256 (by norm_num) (Real.one_le_rpow hx1.le (by norm_num))
    simpa using h
  have hφ1 : (1 : ℝ) ≤ (wheel x).totient := by
    have h : 1 ≤ (wheel x).totient := Nat.totient_pos.mpr (wheel_pos x)
    exact_mod_cast h
  have hden : Real.log x ≤ ((wheel x).totient : ℝ) * Real.log x :=
    le_mul_of_one_le_left hlog.le hφ1
  have hE : 3 * x ^ (1 / 20 : ℝ) * (1 + Real.log (x ^ (1 / 20 : ℝ))) ^ 3 ≤
      H / Real.log x := by
    exact herr.trans ((div_le_div_of_nonneg_left
      (Real.rpow_nonneg hx0.le _) hlog hden).trans
        (div_le_div_of_nonneg_right hHlo hlog.le))
  have hz : 1 < x ^ (1 / 20 : ℝ) := Real.one_lt_rpow hx1 (by norm_num)
  have hzr : x ^ (1 / 20 : ℝ) < x ^ (1 / 10 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hx1 (by norm_num)
  have hcount0 := rough_ap_sum_upper704 x H (x ^ (1 / 20 : ℝ))
    (x ^ (1 / 10 : ℝ)) 1 0 hx0 hH hz (by norm_num) hzr
  have hcount : (∑ n ∈ ints x (x + H), Task361.roughIndicator n (x ^ (1 / 10 : ℝ))) ≤
      41 * (H / Real.log x) := by
    have hc : (∑ n ∈ ints x (x + H), Task361.roughIndicator n (x ^ (1 / 10 : ℝ))) ≤
        2 * H / Real.log (x ^ (1 / 20 : ℝ)) +
          3 * x ^ (1 / 20 : ℝ) * (1 + Real.log (x ^ (1 / 20 : ℝ))) ^ 3 := by
      have he : (ints x (x + H)).filter (fun n => n ≡ 0 [MOD 1]) = ints x (x + H) := by
        apply Finset.filter_eq_self.mpr
        intro n hn
        change n % 1 = 0 % 1
        omega
      rw [he] at hcount0
      simpa using hcount0
    have hm : 2 * H / Real.log (x ^ (1 / 20 : ℝ)) = 40 * (H / Real.log x) := by
      rw [Real.log_rpow hx0]
      field_simp
      ring
    rw [hm] at hc
    linarith only [hc, hE]
  have hnum : (∑ n ∈ ints x (x + H), Task379.referenceWeight x n *
      Task361.harmanMajorant x n) ≤
      (B * 1001) * ∑ n ∈ ints x (x + H), Task361.roughIndicator n (x ^ (1 / 10 : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro n hn
    obtain ⟨hnlo, hnhi⟩ := Finset.mem_Icc.mp hn
    have hnlo' : x ≤ n := (Nat.le_ceil x).trans (by exact_mod_cast hnlo)
    have hnhi' : (n : ℝ) ≤ x + H :=
      (show (n : ℝ) ≤ (⌊x + H⌋₊ : ℝ) by exact_mod_cast hnhi).trans
        (Nat.floor_le (by positivity))
    have hn0 : 0 < n := by exact_mod_cast hx0.trans_le hnlo'
    have hn2x : (n : ℝ) ≤ 2 * x := by linarith
    have hm := harmanMajorant_le_rough704 hxe hn0 hn2x
    have hw : Task379.referenceWeight x n ≤ B :=
      (le_abs_self _).trans (by simpa using hWeight x hx0 n)
    calc
      _ ≤ Task379.referenceWeight x n *
          (1001 * Task361.roughIndicator n (x ^ (1 / 10 : ℝ))) :=
        mul_le_mul_of_nonneg_left hm (Task379.referenceWeight_nonneg _ _)
      _ ≤ B * (1001 * Task361.roughIndicator n (x ^ (1 / 10 : ℝ))) :=
        mul_le_mul_of_nonneg_right hw
          (mul_nonneg (by norm_num) (Task361.roughIndicator_nonneg _ _))
      _ = _ := by ring
  have hnum' := hnum.trans (mul_le_mul_of_nonneg_left hcount (by positivity : 0 ≤ B * 1001))
  rw [abs_of_nonneg (Task379.referenceMean_nonneg hx1.le)]
  unfold Task379.referenceMean
  rw [Task678.referenceWeight_integral_scale hx0]
  change Real.log x * (∑ n ∈ ints x (x + H),
    Task379.referenceWeight x n * Task361.harmanMajorant x n) / (H * J) ≤ B * 1001 * 41 / J
  apply (div_le_iff₀ (mul_pos hH hJ)).mpr
  calc
    _ ≤ Real.log x * ((B * 1001) * (41 * (H / Real.log x))) :=
      mul_le_mul_of_nonneg_left hnum' hlog.le
    _ = _ := by field_simp [hlog.ne', hJ.ne']

/-- For a complex sequence of norm at most one with shift W multiplying every term by z, the norm of z minus one times its first N term sum is at most twice W.
Derived for MMS page 12. -/
lemma shifted_range_character_bound704 (f : ℕ → ℂ) (z : ℂ) (W N : ℕ)
    (hs : ∀ n, f (W + n) = z * f n) (hf : ∀ n, ‖f n‖ ≤ 1) :
    ‖(z - 1) * ∑ n ∈ range N, f n‖ ≤ 2 * W := by
  have h₁ := sum_range_add f W N
  have h₂ := sum_range_add f N W
  rw [Nat.add_comm W N] at h₁
  simp_rw [hs] at h₁
  rw [← mul_sum] at h₁
  have he : (z - 1) * (∑ n ∈ range N, f n) =
      (∑ n ∈ range W, f (N + n)) - ∑ n ∈ range W, f n := by
    linear_combination h₂ - h₁
  rw [he]
  have hb : ∀ k, ‖∑ n ∈ range W, f (k + n)‖ ≤ W := by
    intro k
    exact (norm_sum_le _ _).trans (by simpa using sum_le_sum (fun n (_ : n ∈ range W) => hf (k + n)))
  have hb₀ : ‖∑ n ∈ range W, f n‖ ≤ W := by simpa using hb 0
  exact (norm_sub_le _ _).trans (by linarith [hb N])

/-- For positive delta at most the norm of e of W gamma minus one, every initial sum of the character in one residue class modulo W has norm at most twice W divided by delta.
Derived for MMS page 12. -/
lemma ap_partial_sum_bound704 (W c N : ℕ) (γ δ : ℝ) (hδ : 0 < δ)
    (hphase : δ ≤ ‖e ((W : ℝ) * γ) - 1‖) :
    ‖∑ n ∈ range N, if n ≡ c [MOD W] then e ((n : ℝ) * γ) else 0‖ ≤ 2 * W / δ := by
  classical
  let f : ℕ → ℂ := fun n => if n ≡ c [MOD W] then e ((n : ℝ) * γ) else 0
  have hs : ∀ n, f (W + n) = e ((W : ℝ) * γ) * f n := by
    intro n
    have hm : W + n ≡ c [MOD W] ↔ n ≡ c [MOD W] := by
      simp only [Nat.ModEq, Nat.add_mod, Nat.mod_self, zero_add, Nat.mod_mod]
    by_cases hn : n ≡ c [MOD W]
    · simp only [f, hm, hn, ite_true, Nat.cast_add, add_mul]
      exact e_add _ _
    · simp only [f, hm, hn, ite_false, mul_zero]
  have hf : ∀ n, ‖f n‖ ≤ 1 := by
    intro n
    dsimp [f]
    split_ifs
    · simp [norm_e]
    · norm_num
  have hb := shifted_range_character_bound704 f (e ((W : ℝ) * γ)) W N hs hf
  rw [norm_mul] at hb
  apply (le_div_iff₀ hδ).mpr
  have hl := mul_le_mul_of_nonneg_right hphase (norm_nonneg (∑ n ∈ range N, f n))
  change ‖∑ n ∈ range N, f n‖ * δ ≤ _
  nlinarith

/-- If a complex sequence has all initial sums through N bounded by nonnegative B and a real weight has absolute value at most one with consecutive differences at most nonnegative D, the weighted N term sum has norm at most B times one plus N D.
Derived for MMS page 12. -/
lemma smoothed_range_norm_bound704 (f : ℕ → ℂ) (g : ℕ → ℝ) (N : ℕ) (B D : ℝ)
    (hB : 0 ≤ B) (hD : 0 ≤ D) (hg : ∀ n, |g n| ≤ 1)
    (hpart : ∀ k ≤ N, ‖∑ n ∈ range k, f n‖ ≤ B)
    (hdiff : ∀ n, |g (n + 1) - g n| ≤ D) :
    ‖∑ n ∈ range N, (g n : ℂ) * f n‖ ≤ B * (1 + N * D) := by
  have hid := Finset.sum_range_by_parts g f N
  have hterm : ‖g (N - 1) • ∑ n ∈ range N, f n‖ ≤ B := by
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul (hg _) (hpart N le_rfl) (norm_nonneg _) (by norm_num)).trans (by simp)
  have htail : ‖∑ n ∈ range (N - 1), (g (n + 1) - g n) • ∑ i ∈ range (n + 1), f i‖ ≤
      (N : ℝ) * D * B := by
    calc
      _ ≤ ∑ n ∈ range (N - 1), D * B := by
        apply (norm_sum_le _ _).trans
        apply sum_le_sum
        intro n hn
        rw [norm_smul, Real.norm_eq_abs]
        exact mul_le_mul (hdiff n) (hpart (n + 1) (by have := mem_range.mp hn; omega))
          (norm_nonneg _) hD
      _ = ((N - 1 : ℕ) : ℝ) * (D * B) := by simp
      _ ≤ (N : ℝ) * D * B := by
        have hh : ((N - 1 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast Nat.sub_le N 1
        simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hh (mul_nonneg hD hB)
  change ‖∑ n ∈ range N, g n • f n‖ ≤ _
  rw [hid]
  exact (norm_sub_le _ _).trans (by nlinarith)

/-- For positive epsilon there is a positive constant D fixed before theta, x, W, c, q and gamma. For x at least exp one hundred, theta at most one and positive q, a phase norm at least two divided by q bounds the smoothed progression sum by W q times one plus three x D divided by x to power theta.
Derived for MMS page 12. -/
theorem cutoff_ap_sum_bound704 (ε : ℝ) (hε : 0 < ε) :
    ∃ D : ℝ, 0 < D ∧ ∀ θ x : ℝ, Real.exp 100 ≤ x → θ ≤ 1 →
      ∀ W c q : ℕ, 0 < q → ∀ γ : ℝ,
      2 / (q : ℝ) ≤ ‖e ((W : ℝ) * γ) - 1‖ →
      ‖∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD W]),
        ((edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ ≤
        (W : ℝ) * q * (1 + 3 * x * D / x ^ θ) := by
  classical
  obtain ⟨D, hD, hDb⟩ := edgeCutoff_deriv_bound704 hε 1
  refine ⟨D, hD, ?_⟩
  intro θ x hx hθ W c q hq γ hphase
  have hx0 : 0 < x := (Real.exp_pos 100).trans_le hx
  have hx1 : 1 ≤ x := by linarith [Real.add_one_le_exp (100 : ℝ)]
  have hpow : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 _
  have hpowx : x ^ θ ≤ x := Real.rpow_le_self_of_one_le hx1 hθ
  let L := x - x ^ θ / 3
  let U := x + x ^ θ
  let N := ⌊2 * x⌋₊ + 1
  let S := (ints L U).filter (fun n => n ≡ c [MOD W])
  let R := (range N).filter (fun n => n ≡ c [MOD W])
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hsub : S ⊆ R := by
    intro n hn
    obtain ⟨hnI, hnc⟩ := mem_filter.mp hn
    have hnle : (n : ℝ) ≤ 2 * x := by
      have hh := (Nat.floor_le hU)
      have hh' : (n : ℝ) ≤ (⌊U⌋₊ : ℝ) := by exact_mod_cast (mem_Icc.mp hnI).2
      dsimp [U] at hh
      linarith
    exact mem_filter.mpr ⟨mem_range.mpr (by dsimp [N]; exact Nat.lt_succ_of_le (Nat.le_floor hnle)), hnc⟩
  have hz : ∀ n ∈ R, n ∉ S → edgeCutoff ε θ x n = 0 := by
    intro n hn hns
    have hnc := (mem_filter.mp hn).2
    have hnI : n ∉ ints L U := by
      intro hh
      exact hns (mem_filter.mpr ⟨hh, hnc⟩)
    have hout : (n : ℝ) ≤ L ∨ U ≤ n := by
      by_cases hlo : n < ⌈L⌉₊
      · exact Or.inl (Nat.lt_ceil.mp hlo).le
      · have hhi : ⌊U⌋₊ < n := by
          by_contra hh
          exact hnI (mem_Icc.mpr ⟨by omega, by omega⟩)
        exact Or.inr (Nat.lt_of_floor_lt hhi).le
    exact edgeCutoff_zero_outside704 hε hx0 hout
  have heq : (∑ n ∈ range N, ((edgeCutoff ε θ x n : ℝ) : ℂ) *
        (if n ≡ c [MOD W] then e ((n : ℝ) * γ) else 0)) =
      ∑ n ∈ S, ((edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ) := by
    simp_rw [mul_ite, mul_zero]
    rw [← sum_filter]
    symm
    apply sum_subset hsub
    intro n hn hns
    rw [hz n hn hns]
    simp
  have hpart : ∀ k ≤ N, ‖∑ n ∈ range k,
      if n ≡ c [MOD W] then e ((n : ℝ) * γ) else 0‖ ≤ (W : ℝ) * q := by
    intro k hk
    have hh := ap_partial_sum_bound704 W c k γ (2 / q) (by positivity) hphase
    convert hh using 1 <;> field_simp
  have hdiff : ∀ n : ℕ, |edgeCutoff ε θ x (n + 1 : ℕ) - edgeCutoff ε θ x n| ≤ D / x ^ θ := by
    intro n
    have hf : Differentiable ℝ (edgeCutoff ε θ x) :=
      (edgeCutoff_contDiff704 hx0 1).differentiable (by norm_num)
    have hb : ∀ t : ℝ, ‖deriv (edgeCutoff ε θ x) t‖ ≤ D / x ^ θ := by
      intro t
      simpa only [iteratedDeriv_one, pow_one, Real.norm_eq_abs] using hDb θ x hx0 t
    have hl := Convex.norm_image_sub_le_of_norm_deriv_le (s := Set.univ)
      (fun t _ => hf t) (fun t _ => hb t) convex_univ
      (Set.mem_univ (n : ℝ)) (Set.mem_univ ((n + 1 : ℕ) : ℝ))
    simpa only [Real.norm_eq_abs, Nat.cast_add, Nat.cast_one, add_sub_cancel_left,
      abs_one, mul_one] using hl
  have hg : ∀ n : ℕ, |edgeCutoff ε θ x n| ≤ 1 := by
    intro n
    rw [abs_of_nonneg (edgeCutoff_nonneg _ _ _ _)]
    exact edgeCutoff_le_one _ _ _ _
  have hb := smoothed_range_norm_bound704
    (fun n => if n ≡ c [MOD W] then e ((n : ℝ) * γ) else 0)
    (fun n => edgeCutoff ε θ x n) N ((W : ℝ) * q) (D / x ^ θ)
    (by positivity) (by positivity) hg hpart hdiff
  rw [heq] at hb
  have hN : (N : ℝ) ≤ 3 * x := by
    have hh := Nat.floor_le (show (0 : ℝ) ≤ 2 * x by positivity)
    dsimp [N]
    push_cast
    linarith
  change ‖∑ n ∈ S, ((edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ ≤ _
  apply hb.trans
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  have hh := mul_le_mul_of_nonneg_right hN (show 0 ≤ D / x ^ θ by positivity)
  convert add_le_add_left hh 1 using 1 <;> ring

/-- For positive W below q, a coprime rational a over q, Q at least twice W and absolute q gamma minus a below one over Q, the norm of e of W gamma minus one is at least two divided by q.
Derived for MMS page 12. -/
theorem rational_spacing_lower704 (W q : ℕ) (a : ℤ) (γ Q : ℝ) (hW : 0 < W) (hq : W < q)
    (hc : Int.gcd a q = 1) (hQ : 2 * W ≤ Q)
    (ha : |(q : ℝ) * γ - a| < 1 / Q) :
    2 / (q : ℝ) ≤ ‖e ((W : ℝ) * γ) - 1‖ := by
  have hqp : 0 < q := lt_trans hW hq
  have hqr : (0 : ℝ) < q := by exact_mod_cast hqp
  have hWr : (0 : ℝ) < W := by exact_mod_cast hW
  have hQp : 0 < Q := by linarith
  let k : ℤ := round ((W : ℝ) * γ)
  have hne : (q : ℤ) * k - (W : ℤ) * a ≠ 0 := by
    intro hz
    have hd : (q : ℤ) ∣ a * (W : ℤ) := ⟨k, by linarith⟩
    have hd' : (q : ℤ) ∣ (W : ℤ) :=
      (Int.isCoprime_iff_gcd_eq_one.mpr hc).symm.dvd_of_dvd_mul_left hd
    have hdN : q ∣ W := by exact_mod_cast hd'
    exact (not_le_of_gt hq) (Nat.le_of_dvd hW hdN)
  have hone : (1 : ℝ) ≤ |(q : ℝ) * k - (W : ℝ) * a| := by
    exact_mod_cast Int.one_le_abs hne
  have heq : (q : ℝ) * k - (W : ℝ) * a =
      (q : ℝ) * (k - (W : ℝ) * γ) + (W : ℝ) * ((q : ℝ) * γ - a) := by ring
  rw [heq] at hone
  have hdist : |(q : ℝ) * (k - (W : ℝ) * γ) + (W : ℝ) * ((q : ℝ) * γ - a)| ≤
      (q : ℝ) * LeanLab.PNTPort.LargeSieve.dist0 ((W : ℝ) * γ) + (W : ℝ) / Q := by
    calc
      _ ≤ |(q : ℝ) * (k - (W : ℝ) * γ)| + |(W : ℝ) * ((q : ℝ) * γ - a)| := abs_add_le _ _
      _ ≤ (q : ℝ) * LeanLab.PNTPort.LargeSieve.dist0 ((W : ℝ) * γ) + (W : ℝ) / Q := by
        rw [abs_mul, abs_mul, abs_of_pos hqr, abs_of_pos hWr]
        have hk : |(k : ℝ) - (W : ℝ) * γ| =
            LeanLab.PNTPort.LargeSieve.dist0 ((W : ℝ) * γ) := by
          exact abs_sub_comm _ _
        rw [hk]
        apply add_le_add le_rfl
        simpa only [div_eq_mul_inv, one_mul] using (mul_le_mul_of_nonneg_left ha.le hWr.le)
  have hhalf : (W : ℝ) / Q ≤ 1 / 2 := (div_le_iff₀ hQp).mpr (by linarith)
  have hb : 1 / (2 * (q : ℝ)) ≤ LeanLab.PNTPort.LargeSieve.dist0 ((W : ℝ) * γ) := by
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * q)).mpr
    nlinarith
  have hfour := LeanLab.PNTPort.LargeSieve.four_dist0_le ((W : ℝ) * γ)
  have he (t : ℝ) : LeanLab.PNTPort.LargeSieve.e t = e t := by
    unfold LeanLab.PNTPort.LargeSieve.e e
    congr 1
    push_cast
    ring
  rw [he] at hfour
  have hh : 2 / (q : ℝ) = 4 * (1 / (2 * (q : ℝ))) := by field_simp; ring
  rw [hh]
  linarith

set_option maxHeartbeats 800000 in
/-- For theta strictly between eleven twentieths and one, epsilon strictly between zero and one and A at least one, the actual normalized reference main term times the cutoff character sum in any reduced wheel class is eventually at most eta x to power theta divided by phi W log x. The estimate is uniform over coprime numerators and denominators with denominator at least log x to power five A and at most Q. It assumes absolute q gamma minus a below one over Q. This proves the unweighted minor arc main term from the burst. It supplies no weighted Harman cancellation.
Derived for MMS page 12. -/
theorem minor_arc_main704 (θ : ℝ) (hθ : 11 / 20 < θ) (hθ1 : θ < 1)
    (ε : ℝ) (hε : 0 < ε) (_hε1 : ε < 1) (A : ℝ) (hA : 1 ≤ A) :
    ∀ η : ℝ, 0 < η → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      ∀ c : ℕ, Nat.Coprime c (wheel x) → ∀ γ : ℝ, ∀ a : ℤ, ∀ q : ℕ, 0 < q →
        Int.gcd a q = 1 → Real.log x ^ (5 * A) ≤ q →
        (q : ℝ) ≤ x ^ (2 * θ - 1) / Real.log x ^ (5 * A) →
        |(q : ℝ) * γ - a| < 1 / (x ^ (2 * θ - 1) / Real.log x ^ (5 * A)) →
        ‖((Task379.referenceMean x / Real.log x * (wheel x / (wheel x).totient) : ℝ) : ℂ) *
          ∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
            ((edgeCutoff ε θ x n : ℝ) : ℂ) * e (n * γ)‖ ≤
          η * x ^ θ / ((wheel x).totient * Real.log x) := by
  obtain ⟨D, hD, hDb⟩ := cutoff_ap_sum_bound704 ε hε
  obtain ⟨M, hM, Xm, hXm⟩ := referenceMean_bounded_by_sieve704
  intro η hη
  have hgap : 0 < 2 * θ - 1 := by linarith only [hθ]
  have hs := (isLittleO_log_rpow_rpow_atTop (5 * A + 1) hgap).bound
    (by norm_num : (0 : ℝ) < 1 / 2)
  obtain ⟨Xq, hXq⟩ := eventually_atTop.mp (hs.and (eventually_ge_atTop (Real.exp 100)))
  let C := M * (1 + 3 * D)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨max Xm (max Xq (Real.exp (C / η + 100))), ?_⟩
  intro x hx c _hc γ a q hq hcop hqlo hqhi happrox
  have hxm : Xm ≤ x := (le_max_left _ _).trans hx
  have hxq : Xq ≤ x := (le_max_left _ _).trans ((le_max_right _ _).trans hx)
  have hxe : Real.exp (C / η + 100) ≤ x :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hx)
  obtain ⟨hh, hx100⟩ := hXq x hxq
  have hx0 : 0 < x := (Real.exp_pos 100).trans_le hx100
  have hx1 : 1 ≤ x := by linarith only [hx100, Real.add_one_le_exp (100 : ℝ)]
  have hlog100 : 100 ≤ Real.log x := by
    have ht := Real.log_le_log (Real.exp_pos 100) hx100
    simpa only [Real.log_exp] using ht
  have hlog : 0 < Real.log x := by linarith only [hlog100]
  have hlog1 : 1 ≤ Real.log x := by linarith only [hlog100]
  have hpow : 0 < x ^ θ := Real.rpow_pos_of_pos hx0 _
  have hgapx : 0 < x ^ (2 * θ - 1) := Real.rpow_pos_of_pos hx0 _
  have hlogA : 0 < Real.log x ^ (5 * A) := Real.rpow_pos_of_pos hlog _
  have hW := wheel_le_log ((Real.exp_le_exp.mpr (by norm_num : (1 : ℝ) ≤ 100)).trans hx100)
  have hWp : (0 : ℝ) < wheel x := by exact_mod_cast wheel_pos x
  have hφ : (0 : ℝ) < (wheel x).totient := by exact_mod_cast Nat.totient_pos.mpr (wheel_pos x)
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg hlog.le _), abs_of_pos hgapx] at hh
  have hlogAdd : Real.log x ^ (5 * A + 1) = Real.log x ^ (5 * A) * Real.log x := by
    rw [Real.rpow_add hlog, Real.rpow_one]
  rw [hlogAdd] at hh
  have hQ : 2 * (wheel x : ℝ) ≤ x ^ (2 * θ - 1) / Real.log x ^ (5 * A) := by
    apply (le_div_iff₀ hlogA).mpr
    have hw := mul_le_mul_of_nonneg_right hW hlogA.le
    nlinarith only [hw, hh]
  have hqW : wheel x < q := by
    have ht := Real.rpow_lt_rpow_of_exponent_lt (by linarith only [hlog100] : 1 < Real.log x)
      (by linarith only [hA] : (1 : ℝ) < 5 * A)
    rw [Real.rpow_one] at ht
    exact_mod_cast hW.trans_lt (ht.trans_le hqlo)
  have hphase := rational_spacing_lower704 (wheel x) q a γ
    (x ^ (2 * θ - 1) / Real.log x ^ (5 * A)) (wheel_pos x) hqW hcop hQ happrox
  have hsum := hDb θ x hx100 hθ1.le (wheel x) c q hq γ hphase
  have hp5 : Real.log x ^ (5 : ℕ) ≤ Real.log x ^ (5 * A) := by
    have ht := Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith only [hA] : (5 : ℝ) ≤ 5 * A)
    simpa only [Real.rpow_ofNat] using ht
  have hq5 : (q : ℝ) ≤ x ^ (2 * θ - 1) / Real.log x ^ (5 : ℕ) :=
    hqhi.trans (div_le_div_of_nonneg_left hgapx.le (by positivity) hp5)
  have hgaple : x ^ (2 * θ - 1) ≤ x ^ θ :=
    Real.rpow_le_rpow_of_exponent_le hx1 (by linarith only [hθ1])
  have hid : x ^ (2 * θ - 1) * x = x ^ θ * x ^ θ := by
    calc
      _ = x ^ (2 * θ - 1) * x ^ (1 : ℝ) := by rw [Real.rpow_one]
      _ = x ^ ((2 * θ - 1) + 1) := (Real.rpow_add hx0 _ _).symm
      _ = x ^ (θ + θ) := by congr 1; ring
      _ = _ := Real.rpow_add hx0 _ _
  have hcombine : x ^ (2 * θ - 1) * (1 + 3 * x * D / x ^ θ) ≤ (1 + 3 * D) * x ^ θ := by
    have heq : x ^ (2 * θ - 1) * (1 + 3 * x * D / x ^ θ) =
        x ^ (2 * θ - 1) + 3 * D * x ^ θ := by
      rw [mul_add, mul_one]
      congr 1
      calc
        _ = 3 * D * (x ^ (2 * θ - 1) * x) / x ^ θ := by ring
        _ = 3 * D * (x ^ θ * x ^ θ) / x ^ θ := by rw [hid]
        _ = _ := by field_simp
    rw [heq]
    nlinarith only [hgaple]
  have hqw : (q : ℝ) * (1 + 3 * x * D / x ^ θ) ≤
      (1 + 3 * D) * x ^ θ / Real.log x ^ (5 : ℕ) := by
    calc
      _ ≤ (x ^ (2 * θ - 1) / Real.log x ^ (5 : ℕ)) * (1 + 3 * x * D / x ^ θ) :=
        mul_le_mul_of_nonneg_right hq5 (by positivity)
      _ = (x ^ (2 * θ - 1) * (1 + 3 * x * D / x ^ θ)) / Real.log x ^ (5 : ℕ) := by ring
      _ ≤ _ := div_le_div_of_nonneg_right hcombine (by positivity)
  have hlogC : C / η + 100 ≤ Real.log x := by
    have ht := Real.log_le_log (Real.exp_pos _) hxe
    simpa only [Real.log_exp] using ht
  have hCLog : C ≤ η * Real.log x := by
    have ht := (div_le_iff₀ hη).mp (show C / η ≤ Real.log x by linarith only [hlogC])
    linarith only [ht]
  have hlogCube : Real.log x ≤ Real.log x ^ (3 : ℕ) := by
    have ht : 0 ≤ Real.log x ^ (2 : ℕ) - 1 := by nlinarith only [hlog1]
    nlinarith only [mul_nonneg hlog.le ht]
  have hWsq : (wheel x : ℝ) ^ 2 ≤ Real.log x ^ (2 : ℕ) := by
    simpa only [pow_two] using mul_self_le_mul_self hWp.le hW
  have hbudget : C * (wheel x : ℝ) ^ 2 ≤ η * Real.log x ^ (5 : ℕ) := by
    calc
      _ ≤ C * Real.log x ^ (2 : ℕ) := mul_le_mul_of_nonneg_left hWsq hC
      _ ≤ (η * Real.log x ^ (3 : ℕ)) * Real.log x ^ (2 : ℕ) :=
        mul_le_mul_of_nonneg_right (hCLog.trans (mul_le_mul_of_nonneg_left hlogCube hη.le)) (by positivity)
      _ = _ := by ring
  have hscalar : ‖((Task379.referenceMean x / Real.log x *
      (wheel x / (wheel x).totient) : ℝ) : ℂ)‖ ≤
      M / Real.log x * ((wheel x : ℝ) / (wheel x).totient) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_pos hlog, abs_div, abs_of_pos hWp, abs_of_pos hφ]
    exact mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right (hXm x hxm) hlog.le) (by positivity)
  apply (norm_mul _ _).le.trans
  apply (mul_le_mul hscalar hsum (norm_nonneg _) (by positivity)).trans
  apply (le_div_iff₀ (mul_pos hφ hlog)).mpr
  have halg : (M / Real.log x * ((wheel x : ℝ) / (wheel x).totient)) *
      ((wheel x : ℝ) * q * (1 + 3 * x * D / x ^ θ)) *
        ((wheel x).totient * Real.log x) =
      M * (wheel x : ℝ) ^ 2 * ((q : ℝ) * (1 + 3 * x * D / x ^ θ)) := by
    field_simp
  rw [halg]
  calc
    _ ≤ M * (wheel x : ℝ) ^ 2 * ((1 + 3 * D) * x ^ θ / Real.log x ^ (5 : ℕ)) :=
      mul_le_mul_of_nonneg_left hqw (by positivity)
    _ = (C * (wheel x : ℝ) ^ 2 / Real.log x ^ (5 : ℕ)) * x ^ θ := by dsimp [C]; ring
    _ ≤ η * x ^ θ := mul_le_mul_of_nonneg_right
      ((div_le_iff₀ (by positivity : (0 : ℝ) < Real.log x ^ (5 : ℕ))).mpr hbudget) hpow.le

end Task704

end LeanLab.Ternary.MMS.Task420
