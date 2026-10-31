/-
P0086 Basak, Bhat, Dong, Zaharescu 2024, arXiv 2409.08968 v1, Section 6, pages 8 to 10,
displays (6.1)-(6.18).

`Major618 A B` of MajorArcs.lean is reduced to the smaller input `Arc613 A B`, display (6.13):
the major arc integral equals `𝔖_P(m) · ∫_{-1/Q}^{1/Q} T(β)³ e(-mβ) dβ` up to
`u² (log u)^{12A - B + ε}`. This is exactly the part of Section 6 that uses Siegel-Walfisz,
(6.1)-(6.13); the paper proves it with error `u² exp(-c₃ √log u)`, far below what we assume.
Everything else in (6.13)-(6.18) is PROVED here, with no input:

1. `integral_count`, (6.15): `∫₀¹ T(β)³ e(-mβ) dβ = #{(k₁,k₂,k₃) ∈ [u,2u]³ : k₁+k₂+k₃ = m}`.
2. `singInt_eq`, (6.14) first half: by 1-periodicity,
   `∫_{-1/Q}^{1/Q} = ∫₀¹ - ∫_{1/Q}^{1-1/Q}`.
3. `tail_bound`, (6.14) second half: `|∫_{1/Q}^{1-1/Q} T³ e(-mβ)| ≤ Q²/8`, from the geometric
   series `|T(β)| ≤ 1/(2 min(β, 1-β))`, `|e(β) - 1| = 2|sin πβ| ≥ 4 min(β, 1-β)` (Jordan).
4. `count_near_H`, (6.15)-(6.16): `|#triples - H(m,u)| ≤ 5u + 1` for `4u ≤ m ≤ 5u`, `u ≥ 1`;
   for fixed `k₁` the `k₂`-count is within 1 of `φ(k₁) = u - |k₁ - (m - 3u)|`, and
   `∫_u^{2u} φ = H(m,u)`, sum against integral for the 1-Lipschitz `φ`.
5. `singInt_approx`, (6.17): `|∫_{-1/Q}^{1/Q} T³ e(-mβ) - H(m,u)| ≤ Q²/8 + 5u + 1`, for
   `Q ≥ 2`, `u ≥ 1`, `4u ≤ m ≤ 5u`.
6. `norm_SingP_le`: `|𝔖_P(m)| ≤ 2e⁴ q₀⁵` for every `P`, from Tail72.lean.
7. `major618_of_arc613`: `Major618 A B` for `B ≥ 15A`, CONDITIONAL ON `Arc613 A B` only;
   `arc613_of_major618`: conversely, so `Arc613` is no stronger than `Major618`.
8. `repProp_of_arc613`: `RepProp A`, CONDITIONAL ON `Minor516W A B` and `Arc613 A B` only.

Paper slip noticed, (6.15)-(6.17): the count of triples is `H(m,u) + O(u)` and (6.17) prints
only `O(u² (log u)^{-2B})`; the `O(u)` is smaller once `u ≥ (log u)^{2B}`, so (6.17) is
right but silently absorbs it. We keep both terms: `Q²/8 + 5u + 1`.

AI-written Lean code, Claude, run 20261021T0903Z-24128, unit U-1383. Checked only by the Lean
kernel. Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.SparseTernary.Tail72
import LeanLab.SparseTernary.Identity412
import LeanLab.SparseTernary.SWInput

open Finset Filter Real MeasureTheory
open scoped Classical

noncomputable section
namespace LeanLab.SparseTernary.Major618SW

open LeanLab.SparseTernary LeanLab.SparseTernary.Section4 LeanLab.SparseTernary.MajorArcs
open LeanLab.SparseTernary.LocalFactors LeanLab.SparseTernary.Tail72Proof
open LeanLab.SparseTernary.Identity

/-! ### Definitions -/

/-- The integer window `[⌈u⌉, ⌊2u⌋]`, the `k` range `u ≤ k ≤ 2u` of (6.7). -/
def Iw (u : ℝ) : Finset ℕ := Icc ⌈u⌉₊ ⌊2 * u⌋₊

/-- (6.7) `T(β) = Σ_{u ≤ k ≤ 2u} e(kβ)`. -/
def Tsum (u β : ℝ) : ℂ := ∑ k ∈ Iw u, ee (k * β)

/-- The integrand `T(β)³ e(-mβ)` of (6.14). -/
def gInt (u : ℝ) (m : ℕ) (β : ℝ) : ℂ := Tsum u β ^ 3 * ee (-(m * β))

/-- (6.14)-(6.17) left side: `∫_{-1/Q}^{1/Q} T(β)³ e(-mβ) dβ`. -/
def SingInt (u Q : ℝ) (m : ℕ) : ℂ := ∫ β in (-(1 / Q))..(1 / Q), gInt u m β

/-- (6.15) right side: the number of `(k₁, k₂, k₃) ∈ [u, 2u]³` with `k₁ + k₂ + k₃ = m`. -/
def count3 (u : ℝ) (m : ℕ) : ℕ :=
  ∑ k₁ ∈ Iw u, ∑ k₂ ∈ Iw u, ∑ k₃ ∈ Iw u, if k₁ + k₂ + k₃ = m then 1 else 0

/-- **(6.13) as a named input**: the major arc integral equals `𝔖_P(m)` times the singular
integral over `[-1/Q, 1/Q]`, up to `u² (log u)^{12A - B + ε}`, for `4u ≤ m ≤ 5u`,
`P = (log u)^B`, `Q = u (log u)^{-B}`, `Z = ⌈3A log log u⌉`. The paper derives it from
Siegel-Walfisz with the much smaller error `u² exp(-c₃ √log u)`. Cited, NOT proved. -/
def Arc613 (A B : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C u0 : ℝ, ∀ u : ℝ, u0 ≤ u → ∀ m : ℕ, 4 * u ≤ m → (m : ℝ) ≤ 5 * u →
    ‖(∫ α in majorArcs (Real.log u ^ B) (u / Real.log u ^ B),
        Sexp (Zof A u) u α ^ 3 * ee (-(m * α))) -
      SingP (Zof A u) m (Real.log u ^ B) * SingInt u (u / Real.log u ^ B) m‖ ≤
      C * u ^ 2 * Real.log u ^ (12 * (A : ℝ) - B + ε)

/-! ### Step 1: orthogonality, (6.15) -/

theorem continuous_gInt (u : ℝ) (m : ℕ) : Continuous (gInt u m) := by
  unfold gInt Tsum; fun_prop

theorem ee_nat_shift (k : ℕ) (β : ℝ) : ee (k * (β + 1)) = ee (k * β) := by
  rw [show (k : ℝ) * (β + 1) = k * β + ((k : ℤ) : ℝ) by push_cast; ring, ee_add, ee_int, mul_one]

theorem gInt_periodic (u : ℝ) (m : ℕ) (β : ℝ) : gInt u m (β + 1) = gInt u m β := by
  unfold gInt Tsum
  simp_rw [ee_nat_shift]
  rw [show -((m : ℝ) * (β + 1)) = -(m * β) + ((-(m : ℤ) : ℤ) : ℝ) by push_cast; ring,
    ee_add, ee_int, mul_one]

theorem expandT (u : ℝ) (m : ℕ) (β : ℝ) :
    gInt u m β = ∑ k₁ ∈ Iw u, ∑ k₂ ∈ Iw u, ∑ k₃ ∈ Iw u,
      ee ((((k₁ + k₂ + k₃ : ℤ) - m : ℤ) : ℝ) * β) := by
  unfold gInt Tsum
  rw [pow_three]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine sum_congr rfl fun k₁ _ => sum_congr rfl fun k₂ _ => sum_congr rfl fun k₃ _ => ?_
  unfold ee; simp only [← Complex.exp_add]; congr 1; push_cast; ring

/-- **(6.15)**: `∫₀¹ T(β)³ e(-mβ) dβ` is the number of triples. PROVED. -/
theorem integral_count (u : ℝ) (m : ℕ) :
    ∫ β in (0 : ℝ)..1, gInt u m β = (count3 u m : ℂ) := by
  have hfun : (fun β => gInt u m β) = fun β => ∑ k₁ ∈ Iw u, ∑ k₂ ∈ Iw u, ∑ k₃ ∈ Iw u,
      ee ((((k₁ + k₂ + k₃ : ℤ) - m : ℤ) : ℝ) * β) := funext (expandT u m)
  rw [hfun, intervalIntegral.integral_finset_sum fun k₁ _ =>
    (by fun_prop : Continuous _).intervalIntegrable _ _]
  unfold count3
  simp only [Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  refine sum_congr rfl fun k₁ _ => ?_
  rw [intervalIntegral.integral_finset_sum fun k₂ _ =>
    (by fun_prop : Continuous _).intervalIntegrable _ _]
  refine sum_congr rfl fun k₂ _ => ?_
  rw [intervalIntegral.integral_finset_sum fun k₃ _ =>
    (by fun_prop : Continuous _).intervalIntegrable _ _]
  refine sum_congr rfl fun k₃ _ => ?_
  rw [integral_ee_int]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; apply h2; omega
  · exfalso; apply h1; omega
  · rfl

/-! ### Step 2: periodicity, (6.14) first half -/

/-- `∫_{-1/Q}^{1/Q} = ∫₀¹ - ∫_{1/Q}^{1-1/Q}`. PROVED. -/
theorem singInt_eq (u Q : ℝ) (m : ℕ) :
    SingInt u Q m = (count3 u m : ℂ) - ∫ β in (1 / Q)..(1 - 1 / Q), gInt u m β := by
  have hc := continuous_gInt u m
  have hi : ∀ a b : ℝ, IntervalIntegrable (gInt u m) volume a b :=
    fun a b => hc.intervalIntegrable a b
  have h1 : ∫ β in (-(1 / Q))..0, gInt u m β = ∫ β in (1 - 1 / Q)..1, gInt u m β := by
    have := intervalIntegral.integral_comp_add_right (gInt u m) (1 : ℝ) (a := -(1 / Q)) (b := 0)
    simp only [gInt_periodic] at this
    rw [this, show -(1 / Q) + 1 = 1 - 1 / Q by ring, zero_add]
  unfold SingInt
  rw [← intervalIntegral.integral_add_adjacent_intervals (hi _ 0) (hi 0 _), h1,
    ← integral_count,
    ← intervalIntegral.integral_add_adjacent_intervals (hi 0 (1 / Q)) (hi (1 / Q) 1),
    ← intervalIntegral.integral_add_adjacent_intervals (hi (1 / Q) (1 - 1 / Q)) (hi (1 - 1 / Q) 1)]
  ring

/-! ### Step 3: the tail, (6.14) second half -/

theorem Tsum_mul (u β : ℝ) (hu : 0 ≤ u) :
    Tsum u β * (ee β - 1) = ee β ^ (⌊2 * u⌋₊ + 1) - ee β ^ ⌈u⌉₊ := by
  have hLU : ⌈u⌉₊ ≤ ⌊2 * u⌋₊ + 1 := by
    have h1 : (⌈u⌉₊ : ℝ) < u + 1 := Nat.ceil_lt_add_one hu
    have h2 : 2 * u < (⌊2 * u⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h3 : (⌈u⌉₊ : ℝ) < ((⌊2 * u⌋₊ + 2 : ℕ) : ℝ) := by push_cast; linarith
    have h4 : ⌈u⌉₊ < ⌊2 * u⌋₊ + 2 := by exact_mod_cast h3
    omega
  unfold Tsum Iw
  have e : Icc ⌈u⌉₊ ⌊2 * u⌋₊ = Ico ⌈u⌉₊ (⌊2 * u⌋₊ + 1) := by
    ext k; simp only [mem_Icc, mem_Ico]; omega
  rw [e, ← geom_sum_Ico_mul _ hLU]
  congr 1
  exact sum_congr rfl fun k _ => ee_nat_mul k β

theorem norm_ee_sub_one (β : ℝ) : ‖ee β - 1‖ = |2 * Real.sin (Real.pi * β)| := by
  have h : ee β = Complex.exp (Complex.I * ((2 * Real.pi * β : ℝ) : ℂ)) := by
    unfold ee; congr 1; push_cast; ring
  rw [h, Complex.norm_exp_I_mul_ofReal_sub_one, Real.norm_eq_abs]
  congr 3; ring

theorem ee_sub_one_ge (β : ℝ) (h0 : 0 < β) (h1 : β < 1) :
    4 * min β (1 - β) ≤ ‖ee β - 1‖ := by
  rw [norm_ee_sub_one]
  have hpi := Real.pi_pos
  rcases le_total β (1 / 2) with hb | hb
  · have hs := Real.mul_le_sin (x := Real.pi * β) (by positivity) (by nlinarith)
    have e : 2 / Real.pi * (Real.pi * β) = 2 * β := by field_simp
    rw [e] at hs
    rw [abs_of_nonneg (by linarith)]
    linarith [min_le_left β (1 - β)]
  · have hs := Real.mul_le_sin (x := Real.pi * (1 - β)) (by nlinarith) (by nlinarith)
    have e : 2 / Real.pi * (Real.pi * (1 - β)) = 2 * (1 - β) := by field_simp
    rw [e] at hs
    have e2 : Real.sin (Real.pi * β) = Real.sin (Real.pi * (1 - β)) := by
      rw [show Real.pi * (1 - β) = Real.pi - Real.pi * β by ring, Real.sin_pi_sub]
    rw [e2, abs_of_nonneg (by linarith)]
    linarith [min_le_right β (1 - β)]

/-- Pointwise: `|T(β)³ e(-mβ)| ≤ (β⁻³ + (1-β)⁻³)/8` on `(0, 1)`. -/
theorem norm_gInt_le (u : ℝ) (m : ℕ) (hu : 0 ≤ u) (β : ℝ) (h0 : 0 < β) (h1 : β < 1) :
    ‖gInt u m β‖ ≤ 1 / 8 * (β ^ (-3 : ℤ) + (1 - β) ^ (-3 : ℤ)) := by
  set μ := min β (1 - β) with hμ
  have hμ0 : 0 < μ := lt_min h0 (by linarith)
  have hd := ee_sub_one_ge β h0 h1
  have hprod : ‖Tsum u β‖ * ‖ee β - 1‖ ≤ 2 := by
    rw [← norm_mul, Tsum_mul u β hu]
    calc ‖ee β ^ (⌊2 * u⌋₊ + 1) - ee β ^ ⌈u⌉₊‖
        ≤ ‖ee β ^ (⌊2 * u⌋₊ + 1)‖ + ‖ee β ^ ⌈u⌉₊‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_pow, norm_pow, norm_ee, one_pow, one_pow]; norm_num
  have hT : ‖Tsum u β‖ ≤ 1 / (2 * μ) := by
    rw [le_div_iff₀ (by positivity)]
    have : ‖Tsum u β‖ * (4 * μ) ≤ 2 :=
      le_trans (mul_le_mul_of_nonneg_left hd (norm_nonneg _)) hprod
    linarith
  have hg : ‖gInt u m β‖ = ‖Tsum u β‖ ^ 3 := by
    unfold gInt; rw [norm_mul, norm_pow, norm_ee, mul_one]
  rw [hg]
  have h3 : ‖Tsum u β‖ ^ 3 ≤ (1 / (2 * μ)) ^ 3 := pow_le_pow_left₀ (norm_nonneg _) hT 3
  refine h3.trans ?_
  have hz1 : β ^ (-3 : ℤ) = 1 / β ^ 3 := by rw [zpow_neg, zpow_ofNat, one_div]
  have hz2 : (1 - β) ^ (-3 : ℤ) = 1 / (1 - β) ^ 3 := by rw [zpow_neg, zpow_ofNat, one_div]
  rw [hz1, hz2]
  have hb1 : 0 < 1 - β := by linarith
  have p1 : 0 ≤ 1 / β ^ 3 := by positivity
  have p2 : 0 ≤ 1 / (1 - β) ^ 3 := by positivity
  rcases min_choice β (1 - β) with hm | hm
  · rw [← hμ, hm] at *
    have : (1 / (2 * β)) ^ 3 = 1 / 8 * (1 / β ^ 3) := by field_simp; ring
    rw [this]; nlinarith
  · rw [← hμ, hm] at *
    have : (1 / (2 * (1 - β))) ^ 3 = 1 / 8 * (1 / (1 - β) ^ 3) := by field_simp; ring
    rw [this]; nlinarith

theorem integral_inv_cube (Q : ℝ) (hQ : 2 ≤ Q) :
    ∫ β in (1 / Q)..(1 - 1 / Q), β ^ (-3 : ℤ) ≤ Q ^ 2 / 2 := by
  have hQ0 : 0 < Q := by linarith
  have ha : 0 < 1 / Q := by positivity
  have hb : 0 < 1 - 1 / Q := by
    have : 1 / Q ≤ 1 / 2 := by rw [div_le_div_iff₀ hQ0 two_pos]; linarith
    linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc (1 / Q) (1 - 1 / Q) := by
    rw [Set.mem_uIcc]; push Not
    exact ⟨fun h => absurd h (not_le.mpr ha), fun h => absurd h (not_le.mpr hb)⟩
  rw [integral_zpow (Or.inr ⟨by norm_num, h0⟩)]
  have e1 : (1 / Q) ^ ((-3 : ℤ) + 1) = Q ^ 2 := by
    rw [show (-3 : ℤ) + 1 = -2 by norm_num, zpow_neg, one_div, inv_zpow', zpow_neg, inv_inv]
    norm_cast
  rw [e1]
  have hpos : 0 ≤ (1 - 1 / Q) ^ ((-3 : ℤ) + 1) := zpow_nonneg hb.le _
  have e2 : (((-3 : ℤ) : ℝ) + 1) = -2 := by norm_num
  rw [e2]
  linarith

/-- **(6.14), the tail**: `|∫_{1/Q}^{1-1/Q} T³ e(-mβ)| ≤ Q²/8`. PROVED. -/
theorem tail_bound (u Q : ℝ) (m : ℕ) (hu : 0 ≤ u) (hQ : 2 ≤ Q) :
    ‖∫ β in (1 / Q)..(1 - 1 / Q), gInt u m β‖ ≤ Q ^ 2 / 8 := by
  have hQ0 : 0 < Q := by linarith
  have ha : 0 < 1 / Q := by positivity
  have hhalf : 1 / Q ≤ 1 / 2 := by rw [div_le_div_iff₀ hQ0 two_pos]; linarith
  have hab : 1 / Q ≤ 1 - 1 / Q := by linarith
  have hb : 0 < 1 - 1 / Q := by linarith
  have h0 : (0 : ℝ) ∉ Set.uIcc (1 / Q) (1 - 1 / Q) := by
    rw [Set.mem_uIcc]; push Not
    exact ⟨fun h => absurd h (not_le.mpr ha), fun h => absurd h (not_le.mpr hb)⟩
  have hi1 : IntervalIntegrable (fun β : ℝ => β ^ (-3 : ℤ)) volume (1 / Q) (1 - 1 / Q) :=
    intervalIntegral.intervalIntegrable_zpow (Or.inr h0)
  have hi2 : IntervalIntegrable (fun β : ℝ => (1 - β) ^ (-3 : ℤ)) volume (1 / Q) (1 - 1 / Q) := by
    have := hi1.comp_sub_left 1
    rw [show (1 : ℝ) - 1 / Q = 1 - 1 / Q from rfl, show (1 : ℝ) - (1 - 1 / Q) = 1 / Q by ring]
      at this
    exact this.symm
  have hint : IntervalIntegrable (fun β : ℝ => 1 / 8 * (β ^ (-3 : ℤ) + (1 - β) ^ (-3 : ℤ)))
      volume (1 / Q) (1 - 1 / Q) := (hi1.add hi2).const_mul _
  refine (intervalIntegral.norm_integral_le_of_norm_le hab
    (Eventually.of_forall fun β hβ => ?_) hint).trans ?_
  · exact norm_gInt_le u m hu β (lt_trans ha hβ.1) (by linarith [hβ.2])
  · rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_add hi1 hi2]
    have hsub : ∫ β in (1 / Q)..(1 - 1 / Q), (1 - β) ^ (-3 : ℤ) =
        ∫ β in (1 / Q)..(1 - 1 / Q), β ^ (-3 : ℤ) := by
      rw [intervalIntegral.integral_comp_sub_left (fun β : ℝ => β ^ (-3 : ℤ)) (1 : ℝ)]
      rw [show (1 : ℝ) - (1 - 1 / Q) = 1 / Q by ring]
    rw [hsub]
    have := integral_inv_cube Q hQ
    linarith

/-! ### Step 4: counting triples, (6.15)-(6.16) -/

/-- The tent `φ(x) = u - |x - (m - 3u)|`, whose integral over `[u, 2u]` is `H(m, u)`. -/
def phi (u : ℝ) (m : ℕ) (x : ℝ) : ℝ := u - |x - ((m : ℝ) - 3 * u)|

theorem continuous_phi (u : ℝ) (m : ℕ) : Continuous (phi u m) := by
  unfold phi; fun_prop

theorem integral_phi (u : ℝ) (m : ℕ) (hu : 0 ≤ u) (h4 : 4 * u ≤ m) (h5 : (m : ℝ) ≤ 5 * u) :
    ∫ x in u..(2 * u), phi u m x = Hmu m u := by
  set t : ℝ := (m : ℝ) - 3 * u with ht
  have hut : u ≤ t := by linarith
  have ht2 : t ≤ 2 * u := by linarith
  have hc := continuous_phi u m
  rw [← intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable u t)
    (hc.intervalIntegrable t (2 * u))]
  have e1 : ∫ x in u..t, phi u m x = ∫ x in u..t, ((u - t) + x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le hut] at hx
    simp only [phi]; rw [← ht, abs_of_nonpos (by linarith [hx.2])]; ring
  have e2 : ∫ x in t..(2 * u), phi u m x = ∫ x in t..(2 * u), ((u + t) - x) := by
    refine intervalIntegral.integral_congr fun x hx => ?_
    rw [Set.uIcc_of_le ht2] at hx
    simp only [phi]; rw [← ht, abs_of_nonneg (by linarith [hx.1])]; ring
  rw [e1, e2, intervalIntegral.integral_add (continuous_const.intervalIntegrable _ _)
      (continuous_id'.intervalIntegrable _ _),
    intervalIntegral.integral_sub (continuous_const.intervalIntegrable _ _)
      (continuous_id'.intervalIntegrable _ _),
    intervalIntegral.integral_const, intervalIntegral.integral_const, integral_id, integral_id]
  simp only [smul_eq_mul]
  unfold Hmu
  rw [ht]; ring

/-- The real-arithmetic core of the per-`k₁` count. -/
theorem count_core (u m k L U a b c : ℝ) (hu : 1 ≤ u) (hL1 : u ≤ L) (hL2 : L < u + 1)
    (hU1 : U ≤ 2 * u) (hU2 : 2 * u < U + 1)
    (ha1 : L ≤ a) (ha2 : m - k - U ≤ a) (ha : a = L ∨ a = m - k - U)
    (hb1 : b ≤ U) (hb2 : b ≤ m - k - L) (hb : b = U ∨ b = m - k - L)
    (hc : c = b + 1 - a) : |c - (u - |k - (m - 3 * u)|)| ≤ 1 := by
  rw [abs_le]
  rcases abs_cases (k - (m - 3 * u)) with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [h] <;>
    rcases ha with ha | ha <;> rcases hb with hb | hb <;> constructor <;> linarith

/-- For fixed `k₁ ∈ [u, 2u]` the number of `(k₂, k₃)` is within 1 of `φ(k₁)`. -/
theorem inner_count (u : ℝ) (m k : ℕ) (hu : 1 ≤ u) (h4 : 4 * u ≤ m) (h5 : (m : ℝ) ≤ 5 * u)
    (hk : k ∈ Iw u) :
    |((∑ k₂ ∈ Iw u, ∑ k₃ ∈ Iw u, if k + k₂ + k₃ = m then 1 else 0 : ℕ) : ℝ) -
      phi u m k| ≤ 1 := by
  set L := ⌈u⌉₊ with hLdef
  set U := ⌊2 * u⌋₊ with hUdef
  have hL1 : u ≤ (L : ℝ) := Nat.le_ceil u
  have hL2 : (L : ℝ) < u + 1 := Nat.ceil_lt_add_one (by linarith)
  have hU1 : (U : ℝ) ≤ 2 * u := Nat.floor_le (by linarith)
  have hU2 : 2 * u < (U : ℝ) + 1 := Nat.lt_floor_add_one _
  rw [Iw, mem_Icc] at hk
  have hk1 : (L : ℝ) ≤ k := by exact_mod_cast hk.1
  have hk2 : (k : ℝ) ≤ U := by exact_mod_cast hk.2
  -- natural number facts
  have nA : k + U ≤ m := by
    have : (k : ℝ) + U ≤ m := by linarith
    exact_mod_cast this
  have nB : k + L ≤ m := by
    have : (k : ℝ) + L ≤ m := by linarith
    exact_mod_cast this
  have nC : k + 2 * L ≤ m + 1 := by
    have : (k : ℝ) + 2 * L < m + 2 := by linarith
    have : k + 2 * L < m + 2 := by exact_mod_cast this
    omega
  have nD : m ≤ k + 2 * U + 1 := by
    have : (m : ℝ) < k + 2 * U + 2 := by linarith
    have : m < k + 2 * U + 2 := by exact_mod_cast this
    omega
  -- the inner sums
  have hin : ∀ k₂ : ℕ, (∑ k₃ ∈ Icc L U, if k + k₂ + k₃ = m then 1 else 0 : ℕ) =
      if k + k₂ + L ≤ m ∧ m ≤ k + k₂ + U then 1 else 0 := by
    intro k₂
    rw [sum_boole, Nat.cast_id]
    split_ifs with hc
    · rw [card_eq_one]
      refine ⟨m - k - k₂, ?_⟩
      ext k₃; simp only [mem_filter, mem_Icc, mem_singleton]; omega
    · rw [card_eq_zero, filter_eq_empty_iff]
      intro k₃ hk₃; rw [mem_Icc] at hk₃; omega
  set a := max L (m - k - U) with ha
  set b := min U (m - k - L) with hb
  have hcount : (∑ k₂ ∈ Iw u, ∑ k₃ ∈ Iw u, if k + k₂ + k₃ = m then 1 else 0 : ℕ) =
      b + 1 - a := by
    unfold Iw
    rw [← hLdef, ← hUdef]
    simp_rw [hin]
    rw [sum_boole, Nat.cast_id]
    have e : (Icc L U).filter (fun k₂ => k + k₂ + L ≤ m ∧ m ≤ k + k₂ + U) = Icc a b := by
      ext k₂; simp only [mem_filter, mem_Icc, ha, hb]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3, h4⟩
        exact ⟨max_le h1 (by omega), le_min h2 (by omega)⟩
      · rintro ⟨h1, h2⟩
        have h1a := le_trans (le_max_left _ _) h1
        have h1b := le_trans (le_max_right _ _) h1
        have h2a := le_trans h2 (min_le_left _ _)
        have h2b := le_trans h2 (min_le_right _ _)
        omega
    rw [e, Nat.card_Icc]
  have nLU : L ≤ U := by
    have h3 : (L : ℝ) < ((U + 1 : ℕ) : ℝ) := by push_cast; linarith
    have h4 : L < U + 1 := by exact_mod_cast h3
    omega
  have hab : a ≤ b + 1 := by
    rcases le_total L (m - k - U) with h1 | h1 <;> rcases le_total U (m - k - L) with h2 | h2
    · rw [ha, hb, max_eq_right h1, min_eq_left h2]; omega
    · rw [ha, hb, max_eq_right h1, min_eq_right h2]; omega
    · rw [ha, hb, max_eq_left h1, min_eq_left h2]; omega
    · rw [ha, hb, max_eq_left h1, min_eq_right h2]; omega
  rw [hcount]
  -- real values of a and b
  have hra : (a : ℝ) = L ∨ (a : ℝ) = m - k - U := by
    rcases le_total L (m - k - U) with h | h
    · right
      rw [ha, max_eq_right h, Nat.cast_sub (by omega : U ≤ m - k), Nat.cast_sub (by omega : k ≤ m)]
    · left; rw [ha, max_eq_left h]
  have hrb : (b : ℝ) = U ∨ (b : ℝ) = m - k - L := by
    rcases le_total U (m - k - L) with h | h
    · left; rw [hb, min_eq_left h]
    · right
      rw [hb, min_eq_right h, Nat.cast_sub (by omega : L ≤ m - k), Nat.cast_sub (by omega : k ≤ m)]
  have na1 : L ≤ a := by rw [ha]; exact le_max_left _ _
  have na2 : m - k - U ≤ a := by rw [ha]; exact le_max_right _ _
  have nb1 : b ≤ U := by rw [hb]; exact min_le_left _ _
  have nb2 : b ≤ m - k - L := by rw [hb]; exact min_le_right _ _
  have ra1 : (L : ℝ) ≤ a := by exact_mod_cast na1
  have ra2 : (m : ℝ) - k - U ≤ a := by
    have : m ≤ a + k + U := by omega
    have : (m : ℝ) ≤ a + k + U := by exact_mod_cast this
    linarith
  have rb1 : (b : ℝ) ≤ U := by exact_mod_cast nb1
  have rb2 : (b : ℝ) ≤ m - k - L := by
    have : b + k + L ≤ m := by omega
    have : (b : ℝ) + k + L ≤ m := by exact_mod_cast this
    linarith
  have hc : ((b + 1 - a : ℕ) : ℝ) = b + 1 - a := by
    rw [Nat.cast_sub hab]; push_cast; ring
  rw [hc]
  unfold phi
  exact count_core u m k L U a b _ hu hL1 hL2 hU1 hU2 ra1 ra2 hra rb1 rb2 hrb rfl

/-- `|∫_x^{x+1} φ - φ(x)| ≤ 1`, `φ` being 1-Lipschitz. -/
theorem unit_step (u : ℝ) (m : ℕ) (x : ℝ) :
    |(∫ y in x..(x + 1), phi u m y) - phi u m x| ≤ 1 := by
  have hc := continuous_phi u m
  have e : (∫ y in x..(x + 1), phi u m y) - phi u m x =
      ∫ y in x..(x + 1), (phi u m y - phi u m x) := by
    rw [intervalIntegral.integral_sub (hc.intervalIntegrable _ _)
      (continuous_const.intervalIntegrable _ _), intervalIntegral.integral_const]
    simp
  rw [e, ← Real.norm_eq_abs]
  have := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := x + 1) (C := 1)
    (f := fun y => phi u m y - phi u m x) (fun y hy => by
      rw [Set.uIoc_of_le (by linarith)] at hy
      rw [Real.norm_eq_abs]; unfold phi
      have := abs_abs_sub_abs_le_abs_sub (y - ((m : ℝ) - 3 * u)) (x - ((m : ℝ) - 3 * u))
      have h2 : |(y - ((m : ℝ) - 3 * u)) - (x - ((m : ℝ) - 3 * u))| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hy.1, hy.2]
      rw [show u - |y - (↑m - 3 * u)| - (u - |x - (↑m - 3 * u)|) =
        -(|y - (↑m - 3 * u)| - |x - (↑m - 3 * u)|) by ring, abs_neg]
      linarith)
  simpa using this

/-- `|φ(y)| ≤ u` near `[u, 2u]`. -/
theorem abs_phi_le (u : ℝ) (m : ℕ) (hu : 1 ≤ u) (h4 : 4 * u ≤ m) (h5 : (m : ℝ) ≤ 5 * u)
    (y : ℝ) (hy1 : u - 1 ≤ y) (hy2 : y ≤ 2 * u + 1) : |phi u m y| ≤ u := by
  unfold phi
  have : |y - ((m : ℝ) - 3 * u)| ≤ 2 * u := by rw [abs_le]; constructor <;> linarith
  rw [abs_le]; constructor <;> linarith [abs_nonneg (y - ((m : ℝ) - 3 * u))]

/-- **(6.15)-(6.16)**: `|#triples - H(m, u)| ≤ 5u + 1` for `u ≥ 1`, `4u ≤ m ≤ 5u`. PROVED. -/
theorem count_near_H (u : ℝ) (m : ℕ) (hu : 1 ≤ u) (h4 : 4 * u ≤ m) (h5 : (m : ℝ) ≤ 5 * u) :
    |(count3 u m : ℝ) - Hmu m u| ≤ 5 * u + 1 := by
  set L := ⌈u⌉₊ with hLdef
  set U := ⌊2 * u⌋₊ with hUdef
  have hL1 : u ≤ (L : ℝ) := Nat.le_ceil u
  have hL2 : (L : ℝ) < u + 1 := Nat.ceil_lt_add_one (by linarith)
  have hU1 : (U : ℝ) ≤ 2 * u := Nat.floor_le (by linarith)
  have hU2 : 2 * u < (U : ℝ) + 1 := Nat.lt_floor_add_one _
  have hLU : L ≤ U := by
    have : (L : ℝ) < U + 1 := by linarith
    have : L < U + 1 := by exact_mod_cast this
    omega
  set N := U - L with hN
  have hNr : (N : ℝ) = U - L := by rw [hN, Nat.cast_sub hLU]
  have hc := continuous_phi u m
  -- (a) count vs Σ φ
  have hA : |(count3 u m : ℝ) - ∑ k ∈ Iw u, phi u m k| ≤ N + 1 := by
    unfold count3
    rw [Nat.cast_sum, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ k ∈ Iw u, |((∑ k₂ ∈ Iw u, ∑ k₃ ∈ Iw u, if k + k₂ + k₃ = m then 1 else 0 : ℕ) : ℝ) -
          phi u m k| ≤ ∑ k ∈ Iw u, (1 : ℝ) :=
          sum_le_sum fun k hk => inner_count u m k hu h4 h5 hk
      _ = N + 1 := by
          rw [sum_const, Iw, Nat.card_Icc, nsmul_eq_mul, mul_one, ← hLdef, ← hUdef]
          have : U + 1 - L = N + 1 := by omega
          rw [this]; push_cast; ring
  -- (b) Σ φ vs ∫_L^U φ
  have hsum : ∑ k ∈ Iw u, phi u m k = ∑ j ∈ range N, phi u m ((L : ℝ) + j) + phi u m U := by
    unfold Iw
    rw [← hLdef, ← hUdef]
    have e : Icc L U = Ico L (N + 1 + L) := by ext; simp only [mem_Icc, mem_Ico]; omega
    rw [e, sum_Ico_eq_sum_range, show N + 1 + L - L = N + 1 by omega, sum_range_succ]
    push_cast
    congr 1
    rw [hNr]; ring_nf
  have hint : ∑ j ∈ range N, ∫ x in ((L : ℝ) + j)..((L : ℝ) + (j + 1 : ℕ)), phi u m x =
      ∫ x in (L : ℝ)..(U : ℝ), phi u m x := by
    have := intervalIntegral.sum_integral_adjacent_intervals (μ := volume) (f := phi u m)
      (a := fun j : ℕ => (L : ℝ) + j) (n := N) (fun k _ => hc.intervalIntegrable _ _)
    rw [this]; congr 1
    · simp
    · rw [hNr]; ring
  have hB : |∑ j ∈ range N, phi u m ((L : ℝ) + j) - ∫ x in (L : ℝ)..(U : ℝ), phi u m x| ≤ N := by
    rw [← hint, ← sum_sub_distrib]
    refine (abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ range N, |phi u m ((L : ℝ) + j) -
          ∫ x in ((L : ℝ) + j)..((L : ℝ) + (j + 1 : ℕ)), phi u m x|
        ≤ ∑ j ∈ range N, (1 : ℝ) := by
          refine sum_le_sum fun j _ => ?_
          rw [abs_sub_comm]
          have := unit_step u m ((L : ℝ) + j)
          rw [show (L : ℝ) + ((j + 1 : ℕ) : ℝ) = (L : ℝ) + j + 1 by push_cast; ring]
          exact this
      _ = N := by simp
  -- (c) the end pieces
  have hend1 : |∫ x in u..(L : ℝ), phi u m x| ≤ u := by
    rw [← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := u) fun y hy => ?_).trans ?_
    · rw [Set.uIoc_of_le hL1] at hy
      rw [Real.norm_eq_abs]
      exact abs_phi_le u m hu h4 h5 y (by linarith [hy.1]) (by linarith [hy.2])
    · rw [abs_of_nonneg (by linarith)]; nlinarith
  have hend2 : |∫ x in (U : ℝ)..(2 * u), phi u m x| ≤ u := by
    rw [← Real.norm_eq_abs]
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := u) fun y hy => ?_).trans ?_
    · rw [Set.uIoc_of_le hU1] at hy
      rw [Real.norm_eq_abs]
      exact abs_phi_le u m hu h4 h5 y (by linarith [hy.1]) (by linarith [hy.2])
    · rw [abs_of_nonneg (by linarith)]; nlinarith
  have hU : |phi u m U| ≤ u := abs_phi_le u m hu h4 h5 U (by linarith) (by linarith)
  have hsplit : ∫ x in u..(2 * u), phi u m x = (∫ x in u..(L : ℝ), phi u m x) +
      (∫ x in (L : ℝ)..(U : ℝ), phi u m x) + ∫ x in (U : ℝ)..(2 * u), phi u m x := by
    rw [intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _),
      intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _)
        (hc.intervalIntegrable _ _)]
  have hH := integral_phi u m (by linarith) h4 h5
  rw [← hH, hsplit]
  rw [hsum] at hA
  have hNu : (N : ℝ) ≤ u := by rw [hNr]; linarith
  rw [abs_le] at hA hB hend1 hend2 hU ⊢
  constructor <;> linarith [hA.1, hA.2, hB.1, hB.2, hend1.1, hend1.2, hend2.1, hend2.2,
    hU.1, hU.2]

/-! ### Step 5: (6.17) -/

/-- **(6.17)**: `|∫_{-1/Q}^{1/Q} T(β)³ e(-mβ) dβ - H(m, u)| ≤ Q²/8 + 5u + 1`
for `Q ≥ 2`, `u ≥ 1`, `4u ≤ m ≤ 5u`. PROVED. -/
theorem singInt_approx (u Q : ℝ) (m : ℕ) (hu : 1 ≤ u) (hQ : 2 ≤ Q) (h4 : 4 * u ≤ m)
    (h5 : (m : ℝ) ≤ 5 * u) :
    ‖SingInt u Q m - (Hmu m u : ℂ)‖ ≤ Q ^ 2 / 8 + 5 * u + 1 := by
  rw [singInt_eq]
  have e : (count3 u m : ℂ) - (∫ β in (1 / Q)..(1 - 1 / Q), gInt u m β) - (Hmu m u : ℂ) =
      (((count3 u m : ℝ) - Hmu m u : ℝ) : ℂ) - ∫ β in (1 / Q)..(1 - 1 / Q), gInt u m β := by
    push_cast; ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [Complex.norm_real, Real.norm_eq_abs]
  have h1 := count_near_H u m hu h4 h5
  have h2 := tail_bound u Q m (by linarith) hQ
  linarith

/-! ### Step 6: a crude bound for `𝔖_P(m)` -/

/-- `|𝔖_P(m)| ≤ 2e⁴ q₀⁵` for every `P`. PROVED, from Tail72.lean. -/
theorem norm_SingP_le (Z m : ℕ) (P : ℝ) : ‖SingP Z m P‖ ≤ 2 * Real.exp 4 * (q0 Z : ℝ) ^ 5 := by
  unfold SingP
  rw [sum_fq_split]
  calc _ ≤ ∑ w ∈ (q0 Z).divisors, ‖fq Z m w * ∑ v ∈ Icc 1 (⌊P⌋₊ / w), hv Z m v‖ :=
        norm_sum_le _ _
    _ ≤ ∑ w ∈ (q0 Z).divisors, (q0 Z : ℝ) ^ 4 * (2 * Real.exp 4) := by
        refine sum_le_sum fun w hw => ?_
        rw [norm_mul]
        refine mul_le_mul (norm_fq_le Z m w (Nat.divisor_le hw)) ?_ (norm_nonneg _)
          (by positivity)
        refine (norm_sum_le _ _).trans ?_
        have e : Icc 1 (⌊P⌋₊ / w) = Ioc 0 (⌊P⌋₊ / w) := by
          ext; simp only [mem_Icc, mem_Ioc]; omega
        rw [e]
        have := tail_hv Z m 0 (⌊P⌋₊ / w)
        simpa using this
    _ = (#(q0 Z).divisors : ℝ) * ((q0 Z : ℝ) ^ 4 * (2 * Real.exp 4)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (q0 Z : ℝ) * ((q0 Z : ℝ) ^ 4 * (2 * Real.exp 4)) := by
        gcongr; exact_mod_cast Nat.card_divisors_le_self _
    _ = 2 * Real.exp 4 * (q0 Z : ℝ) ^ 5 := by ring

/-! ### Step 7: `Major618` from `Arc613` and back -/

/-- The deterministic core: `|𝔖_P (I - H)| ≤ 8e⁴ u² (log u)^{12A - B}` under explicit size
conditions on `u`. -/
theorem core_bound (A B : ℕ) (hB : 15 * A ≤ B) (u : ℝ) (hL : 1 ≤ Real.log u) (hu : 1 ≤ u)
    (hQ : 2 ≤ u / Real.log u ^ B) (hsmall : Real.log u ^ (15 * A + B) ≤ u / 2)
    (m : ℕ) (h4 : 4 * u ≤ m) (h5 : (m : ℝ) ≤ 5 * u) :
    ‖SingP (Zof A u) m (Real.log u ^ B) * SingInt u (u / Real.log u ^ B) m -
      (Hmu m u : ℂ) * SingP (Zof A u) m (Real.log u ^ B)‖ ≤
      8 * Real.exp 4 * u ^ 2 * Real.log u ^ (12 * (A : ℝ) - B) := by
  set Lg := Real.log u with hLg
  have hL0 : 0 < Lg := by linarith
  set S := SingP (Zof A u) m (Lg ^ B)
  set Q := u / Lg ^ B with hQdef
  have e : S * SingInt u Q m - (Hmu m u : ℂ) * S = S * (SingInt u Q m - (Hmu m u : ℂ)) := by ring
  rw [e, norm_mul]
  have hS : ‖S‖ ≤ 2 * Real.exp 4 * Lg ^ (27 * (A : ℝ)) := by
    refine (norm_SingP_le _ _ _).trans ?_
    have hq1 : (1 : ℝ) ≤ q0 (Zof A u) := by exact_mod_cast q0_pos (Zof A u)
    have hq := q0_sq_le A u hL
    have h6 : (q0 (Zof A u) : ℝ) ^ 6 ≤ Lg ^ (27 * (A : ℝ)) := by
      have e6 : (q0 (Zof A u) : ℝ) ^ 6 = ((q0 (Zof A u) : ℝ) ^ 2) ^ 3 := by ring
      rw [e6]
      calc ((q0 (Zof A u) : ℝ) ^ 2) ^ 3 ≤ (Lg ^ (9 * (A : ℝ))) ^ 3 :=
            pow_le_pow_left₀ (by positivity) hq 3
        _ = Lg ^ (27 * (A : ℝ)) := by
            rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; push_cast; ring
    have h5' : (q0 (Zof A u) : ℝ) ^ 5 ≤ (q0 (Zof A u) : ℝ) ^ 6 :=
      pow_le_pow_right₀ hq1 (by norm_num)
    gcongr
    exact h5'.trans h6
  have hI : ‖SingInt u Q m - (Hmu m u : ℂ)‖ ≤ Q ^ 2 + 6 * u := by
    have := singInt_approx u Q m hu hQ h4 h5
    nlinarith
  set X := Lg ^ (12 * (A : ℝ) - B) with hX
  have hXpos : 0 < X := Real.rpow_pos_of_pos hL0 _
  have hY1 : Lg ^ (27 * (A : ℝ)) * Q ^ 2 ≤ u ^ 2 * X := by
    have e1 : Lg ^ (27 * (A : ℝ)) * Q ^ 2 = u ^ 2 * Lg ^ (27 * (A : ℝ) - ((2 * B : ℕ) : ℝ)) := by
      rw [Real.rpow_sub hL0, Real.rpow_natCast, hQdef, div_pow, ← pow_mul]
      ring
    rw [e1]
    refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL ?_) (by positivity)
    have : (15 * A : ℝ) ≤ B := by exact_mod_cast hB
    push_cast; linarith
  have hY2 : Lg ^ (27 * (A : ℝ)) ≤ X * (u / 2) := by
    have e1 : Lg ^ (27 * (A : ℝ)) = X * Lg ^ (((15 * A + B : ℕ) : ℝ)) := by
      rw [hX, ← Real.rpow_add hL0]; congr 1; push_cast; ring
    rw [e1, Real.rpow_natCast]
    exact mul_le_mul_of_nonneg_left hsmall hXpos.le
  have hE : 0 ≤ 2 * Real.exp 4 := by positivity
  calc ‖S‖ * ‖SingInt u Q m - (Hmu m u : ℂ)‖
      ≤ (2 * Real.exp 4 * Lg ^ (27 * (A : ℝ))) * (Q ^ 2 + 6 * u) :=
        mul_le_mul hS hI (norm_nonneg _) (by positivity)
    _ = 2 * Real.exp 4 * (Lg ^ (27 * (A : ℝ)) * Q ^ 2 + 6 * u * Lg ^ (27 * (A : ℝ))) := by ring
    _ ≤ 2 * Real.exp 4 * (u ^ 2 * X + 6 * u * (X * (u / 2))) := by
        gcongr
    _ = 8 * Real.exp 4 * u ^ 2 * X := by ring

/-- The size conditions of `core_bound` hold for all large `u`. -/
theorem eventually_sizes (A B : ℕ) : ∀ᶠ u : ℝ in atTop,
    1 ≤ Real.log u ∧ 1 ≤ u ∧ 2 ≤ u / Real.log u ^ B ∧ Real.log u ^ (15 * A + B) ≤ u / 2 := by
  have h1 := RepAssembly.arcs_ok B
  have h2 := (isLittleO_pow_log_id_atTop (n := 15 * A + B)).bound (by norm_num : (0 : ℝ) < 1 / 2)
  filter_upwards [h1, h2, eventually_ge_atTop (Real.exp 1)] with u hu1 hu2 hu3
  have hu : 1 ≤ u := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hu3
  have hL : 1 ≤ Real.log u := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hu3
  refine ⟨hL, hu, ?_, ?_⟩
  · have hP1 : 1 ≤ Real.log u ^ B := one_le_pow₀ hL
    linarith [hu1.2]
  · simp only [Real.norm_eq_abs, id_eq] at hu2
    rw [abs_of_pos (by linarith : (0 : ℝ) < u)] at hu2
    have : 0 ≤ Real.log u ^ (15 * A + B) := by positivity
    rw [abs_of_nonneg this] at hu2
    linarith

/-- **`Major618 A B`, CONDITIONAL ON `Arc613 A B`** only, for `B ≥ 15A`. -/
theorem major618_of_arc613 (A B : ℕ) (hB : 15 * A ≤ B) (h : Arc613 A B) : Major618 A B := by
  intro ε hε
  obtain ⟨C, u0, hC⟩ := h ε hε
  obtain ⟨u1, hu1⟩ := Filter.eventually_atTop.mp
    ((eventually_sizes A B).and (eventually_ge_atTop u0))
  refine ⟨C + 8 * Real.exp 4, u1, fun u hu m h4 h5 => ?_⟩
  obtain ⟨⟨hL, hu1', hQ, hsm⟩, hu0⟩ := hu1 u hu
  have hcore := core_bound A B hB u hL hu1' hQ hsm m h4 h5
  have harc := hC u hu0 m h4 h5
  have hXY : Real.log u ^ (12 * (A : ℝ) - B) ≤ Real.log u ^ (12 * (A : ℝ) - B + ε) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  set I := ∫ α in majorArcs (Real.log u ^ B) (u / Real.log u ^ B),
    Sexp (Zof A u) u α ^ 3 * ee (-(m * α))
  set S := SingP (Zof A u) m (Real.log u ^ B)
  set J := SingInt u (u / Real.log u ^ B) m
  have e : I - (Hmu m u : ℂ) * S = (I - S * J) + (S * J - (Hmu m u : ℂ) * S) := by ring
  rw [e]
  refine (norm_add_le _ _).trans ?_
  have hE : 0 ≤ 8 * Real.exp 4 * u ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hXY hE]

/-- **Converse**: `Arc613 A B` follows from `Major618 A B` for `B ≥ 15A`, so the new input is
no stronger than the old one. PROVED from the same core bound. -/
theorem arc613_of_major618 (A B : ℕ) (hB : 15 * A ≤ B) (h : Major618 A B) : Arc613 A B := by
  intro ε hε
  obtain ⟨C, u0, hC⟩ := h ε hε
  obtain ⟨u1, hu1⟩ := Filter.eventually_atTop.mp
    ((eventually_sizes A B).and (eventually_ge_atTop u0))
  refine ⟨C + 8 * Real.exp 4, u1, fun u hu m h4 h5 => ?_⟩
  obtain ⟨⟨hL, hu1', hQ, hsm⟩, hu0⟩ := hu1 u hu
  have hcore := core_bound A B hB u hL hu1' hQ hsm m h4 h5
  have hmaj := hC u hu0 m h4 h5
  have hXY : Real.log u ^ (12 * (A : ℝ) - B) ≤ Real.log u ^ (12 * (A : ℝ) - B + ε) :=
    Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  set I := ∫ α in majorArcs (Real.log u ^ B) (u / Real.log u ^ B),
    Sexp (Zof A u) u α ^ 3 * ee (-(m * α))
  set S := SingP (Zof A u) m (Real.log u ^ B)
  set J := SingInt u (u / Real.log u ^ B) m
  have e : I - S * J = (I - (Hmu m u : ℂ) * S) - (S * J - (Hmu m u : ℂ) * S) := by ring
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  have hE : 0 ≤ 8 * Real.exp 4 * u ^ 2 := by positivity
  nlinarith [mul_le_mul_of_nonneg_left hXY hE]

/-- **RepProp A, CONDITIONAL ON `Minor516W A B` and `Arc613 A B`** only, for `A ≥ 1`,
`B ≥ 36A + 3`, `B ≥ 28A + 13`. -/
theorem repProp_of_arc613 (A B : ℕ) (hA : 1 ≤ A) (hB1 : 36 * A + 3 ≤ B)
    (hB2 : 28 * A + 13 ≤ B) (hmin : RepAssembly.Minor516W A B) (harc : Arc613 A B) :
    RepProp A :=
  repProp_of_two A B hA hB1 hB2 hmin (major618_of_arc613 A B (by omega) harc)

/-! ### Vacuity tests -/

/-- `singInt_approx` at `u = 1`, `Q = 2`, `m = 4`: a genuine instance, `H(4, 1) = 1/2`. -/
example : ‖SingInt 1 2 4 - (Hmu 4 1 : ℂ)‖ ≤ (2 : ℝ) ^ 2 / 8 + 5 * 1 + 1 :=
  singInt_approx 1 2 4 le_rfl le_rfl (by norm_num) (by norm_num)

/-- `count3 1 4`: the window is `{1, 2}` and the triples summing to 4 are the three
permutations of `(1, 1, 2)`. -/
example : count3 1 4 = 3 := by
  have : Iw 1 = {1, 2} := by
    unfold Iw; norm_num
    decide
  rw [count3, this]; decide

/-- The side conditions of `repProp_of_arc613` hold at `A = 1`, `B = 41`. -/
example : 1 ≤ (1 : ℕ) ∧ 36 * 1 + 3 ≤ (41 : ℕ) ∧ 28 * 1 + 13 ≤ (41 : ℕ) ∧ 15 * 1 ≤ (41 : ℕ) := by
  norm_num

end LeanLab.SparseTernary.Major618SW
