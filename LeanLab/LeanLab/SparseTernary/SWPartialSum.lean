/-
P0086 Basak, Bhat, Dong, Zaharescu 2024, arXiv 2409.08968 v1, Section 6, page 9,
displays (6.5)-(6.9): partial summation from Siegel-Walfisz to the exponential sum.

`swExp`, CONDITIONAL ON `SW (N + 1)` only: for `K ≥ 0` there are `D, u₀` with
  `|Σ_{u ≤ p ≤ 2u, p ≡ b mod q} log p · e(pβ) - T(β)/φ(q)| ≤ D (1 + |β| u) u / (log u)^K`
for all `u ≥ u₀`, all `1 ≤ q ≤ (log u)^N`, all `b` coprime to `q`, all real `β`, where
`T(β) = Σ_{u ≤ k ≤ 2u} e(kβ)` is (6.7).

This is the residue class form of (6.5)-(6.9): the paper splits by characters and applies
Siegel-Walfisz to `ψ(t, χ)`; we apply it directly to `θ(t; q, b)` and sum by parts
(Mathlib `Finset.sum_range_by_parts`), with `|e((k+1)β) - e(kβ)| ≤ 2π|β|`. The modulus range
`(log u)^N` is met at the left end `t = ⌈u⌉ - 1` through `SW (N + 1)`, since
`(log u)^N ≤ (log(u - 1))^{N+1}` once `log u ≥ 2^{N+1}`.

AI-written Lean code, Claude, run 20261021T0903Z-24128, unit U-1383. Checked only by the Lean
kernel. Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.SparseTernary.Major618FromSW

open Finset Filter Real
open scoped Classical

noncomputable section
namespace LeanLab.SparseTernary.SWPartial

open LeanLab.SparseTernary LeanLab.SparseTernary.Section4 LeanLab.SparseTernary.MajorArcs
open LeanLab.SparseTernary.LocalFactors LeanLab.SparseTernary.Tail72Proof
open LeanLab.SparseTernary.Major618SW LeanLab.SparseTernary.SWInput

/-- `Σ_{u ≤ p ≤ 2u, p ≡ b mod q} log p · e(pβ)`. -/
def thetaE (u β : ℝ) (q b : ℕ) : ℂ :=
  ∑ p ∈ (Iw u).filter (fun p => p.Prime ∧ p ≡ b [MOD q]), (Real.log p : ℂ) * ee (p * β)

/-- The weight `log k · [k prime, k ≡ b mod q]`. -/
def wt (q b k : ℕ) : ℝ := if k.Prime ∧ k ≡ b [MOD q] then Real.log k else 0

theorem thetaAP_nat (n q b : ℕ) : thetaAP n q b = ∑ k ∈ range (n + 1), wt q b k := by
  unfold thetaAP wt; rw [Nat.floor_natCast, sum_filter]

theorem sum_wt_shift (L k q b : ℕ) :
    ∑ j ∈ range k, wt q b (L + j) =
      ∑ i ∈ range (L + k), wt q b i - ∑ i ∈ range L, wt q b i := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [sum_range_succ, ih, show L + (k + 1) = (L + k) + 1 by ring, sum_range_succ]; ring

theorem norm_ee_sub_one_le (β : ℝ) : ‖ee β - 1‖ ≤ 2 * Real.pi * |β| := by
  have h : ee β = Complex.exp (Complex.I * ((2 * Real.pi * β : ℝ) : ℂ)) := by
    unfold ee; congr 1; push_cast; ring
  rw [h]
  refine (Real.norm_exp_I_mul_ofReal_sub_one_le).trans ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]

theorem log_sub_one_ge (u : ℝ) (hu : 3 ≤ u) : Real.log u / 2 ≤ Real.log (u - 1) := by
  have : Real.log u ≤ Real.log ((u - 1) ^ 2) := Real.log_le_log (by linarith) (by nlinarith)
  rw [Real.log_pow] at this; push_cast at this; linarith

/-- **(6.5)-(6.9), residue class form, CONDITIONAL ON `SW (N + 1)`.** -/
theorem swExp (N : ℕ) (hSW : SW (N + 1)) (K : ℝ) (hK : 0 ≤ K) :
    ∃ D u0 : ℝ, ∀ u : ℝ, u0 ≤ u → ∀ q b : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log u ^ N →
      b.Coprime q → ∀ β : ℝ,
      ‖thetaE u β q b - (1 / (q.totient : ℂ)) * Tsum u β‖ ≤
        D * (1 + |β| * u) * u / Real.log u ^ K := by
  obtain ⟨C, x0, hC⟩ := hSW K
  set E0 : ℝ := |C| * 2 * 2 ^ K with hE0
  have hE0n : 0 ≤ E0 := by positivity
  refine ⟨4 * Real.pi * E0, max (x0 + 1) (max 3 (Real.exp (2 ^ (N + 1)))), ?_⟩
  intro u hu q b hq hqu hco β
  have hux0 : x0 + 1 ≤ u := le_trans (le_max_left _ _) hu
  have hu3 : 3 ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hu
  have hue : Real.exp (2 ^ (N + 1)) ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hu
  have hlogu : (2 : ℝ) ^ (N + 1) ≤ Real.log u := by
    rw [← Real.log_exp ((2 : ℝ) ^ (N + 1))]; exact Real.log_le_log (Real.exp_pos _) hue
  set Lg := Real.log u with hLg
  have hLg0 : 0 < Lg := lt_of_lt_of_le (by positivity) hlogu
  have hLgK : 0 < Lg ^ K := Real.rpow_pos_of_pos hLg0 K
  set E : ℝ := E0 * u / Lg ^ K with hE
  have hEn : 0 ≤ E := by positivity
  -- the Siegel-Walfisz bound at every natural point of `[u - 1, 2u]`
  have hpt : ∀ x : ℕ, u - 1 ≤ x → (x : ℝ) ≤ 2 * u →
      |thetaAP x q b - x / (q.totient : ℝ)| ≤ E := by
    intro x hx1 hx2
    have hx0 : 0 < (x : ℝ) := by linarith
    have hlogx : Lg / 2 ≤ Real.log x :=
      le_trans (log_sub_one_ge u hu3) (Real.log_le_log (by linarith) hx1)
    have hLg2 : 0 < Lg / 2 := by positivity
    have hqx : (q : ℝ) ≤ Real.log x ^ (N + 1) := by
      have h1 : 1 ≤ Lg / 2 ^ (N + 1) := by rw [le_div_iff₀ (by positivity)]; linarith
      calc (q : ℝ) ≤ Lg ^ N := hqu
        _ ≤ Lg ^ N * (Lg / 2 ^ (N + 1)) := le_mul_of_one_le_right (by positivity) h1
        _ = (Lg / 2) ^ (N + 1) := by rw [div_pow]; ring
        _ ≤ Real.log x ^ (N + 1) := pow_le_pow_left₀ hLg2.le hlogx _
    have h := hC x (by linarith) q b hq hqx hco
    have hden : (Lg / 2) ^ K ≤ Real.log x ^ K := Real.rpow_le_rpow hLg2.le hlogx hK
    have hden' : (Lg / 2) ^ K = Lg ^ K / 2 ^ K := Real.div_rpow hLg0.le (by norm_num) K
    have hpos2 : 0 < (Lg / 2) ^ K := Real.rpow_pos_of_pos hLg2 K
    have hCx : C * x ≤ |C| * (2 * u) := by
      have a1 := mul_le_mul_of_nonneg_right (le_abs_self C) hx0.le
      have a2 := mul_le_mul_of_nonneg_left hx2 (abs_nonneg C)
      linarith
    calc |thetaAP x q b - x / (q.totient : ℝ)| ≤ C * x / Real.log x ^ K := h
      _ ≤ |C| * (2 * u) / Real.log x ^ K :=
          div_le_div_of_nonneg_right hCx (le_trans hpos2.le hden)
      _ ≤ |C| * (2 * u) / (Lg / 2) ^ K :=
          div_le_div_of_nonneg_left (by positivity) hpos2 hden
      _ = E := by
          rw [hden', hE, hE0]
          have h2K : 0 < (2 : ℝ) ^ K := by positivity
          field_simp
  -- the window
  set L := ⌈u⌉₊ with hLdef
  set U := ⌊2 * u⌋₊ with hUdef
  have hL1 : u ≤ (L : ℝ) := Nat.le_ceil u
  have hL2 : (L : ℝ) < u + 1 := Nat.ceil_lt_add_one (by linarith)
  have hU1 : (U : ℝ) ≤ 2 * u := Nat.floor_le (by linarith)
  have hU2 : 2 * u < (U : ℝ) + 1 := Nat.lt_floor_add_one _
  have hLU : L ≤ U := by
    have : (L : ℝ) < ((U + 1 : ℕ) : ℝ) := by push_cast; linarith
    have : L < U + 1 := by exact_mod_cast this
    omega
  have hL1n : 1 ≤ L := by
    have : (1 : ℝ) ≤ L := by linarith
    exact_mod_cast this
  set n := U + 1 - L with hn
  have hn1 : 1 ≤ n := by omega
  have hnu : ((n - 1 : ℕ) : ℝ) ≤ u := by
    have e : n - 1 = U - L := by omega
    rw [e, Nat.cast_sub hLU]; linarith
  -- rewrite the difference as one sum over `range n`
  set f : ℕ → ℂ := fun j => ee (((L + j : ℕ) : ℝ) * β) with hf
  set g : ℕ → ℂ := fun j => ((wt q b (L + j) - 1 / (q.totient : ℝ) : ℝ) : ℂ) with hg
  have hrw : thetaE u β q b - (1 / (q.totient : ℂ)) * Tsum u β =
      ∑ j ∈ range n, f j • g j := by
    have e1 : thetaE u β q b - (1 / (q.totient : ℂ)) * Tsum u β =
        ∑ k ∈ Iw u, ee (k * β) * ((wt q b k - 1 / (q.totient : ℝ) : ℝ) : ℂ) := by
      unfold thetaE Tsum
      rw [sum_filter, mul_sum, ← sum_sub_distrib]
      refine sum_congr rfl fun k _ => ?_
      unfold wt
      split_ifs <;> push_cast <;> ring
    rw [e1]
    have e2 : Iw u = Ico L (U + 1) := by
      unfold Iw; ext k; simp only [mem_Icc, mem_Ico]; omega
    rw [e2, sum_Ico_eq_sum_range]
    refine sum_congr rfl fun j _ => ?_
    simp only [hf, hg, smul_eq_mul]
  rw [hrw, Finset.sum_range_by_parts f g n]
  -- the partial sums `A k = Σ_{j<k} g j`
  have hA : ∀ k, 1 ≤ k → k ≤ n → ‖∑ i ∈ range k, g i‖ ≤ 2 * E := by
    intro k hk1 hkn
    have hreal : ∑ i ∈ range k, g i =
        (((thetaAP ((L + k - 1 : ℕ) : ℝ) q b - ((L + k - 1 : ℕ) : ℝ) / (q.totient : ℝ)) -
          (thetaAP ((L - 1 : ℕ) : ℝ) q b - ((L - 1 : ℕ) : ℝ) / (q.totient : ℝ)) : ℝ) : ℂ) := by
      simp only [hg]
      rw [← Complex.ofReal_sum]
      congr 1
      rw [sum_sub_distrib, sum_wt_shift, thetaAP_nat, thetaAP_nat,
        show L + k - 1 + 1 = L + k by omega, show L - 1 + 1 = L by omega, sum_const,
        card_range, nsmul_eq_mul, Nat.cast_sub (by omega : 1 ≤ L + k),
        Nat.cast_sub (by omega : 1 ≤ L)]
      push_cast; ring
    rw [hreal, Complex.norm_real, Real.norm_eq_abs]
    have h1 := hpt (L + k - 1) (by rw [Nat.cast_sub (by omega)]; push_cast
                                   have : (1 : ℝ) ≤ k := by exact_mod_cast hk1
                                   linarith)
      (by
        have : L + k - 1 ≤ U := by omega
        have : ((L + k - 1 : ℕ) : ℝ) ≤ U := by exact_mod_cast this
        linarith)
    have h2 := hpt (L - 1) (by rw [Nat.cast_sub hL1n]; push_cast; linarith)
      (by rw [Nat.cast_sub hL1n]; push_cast; linarith)
    calc |(thetaAP ((L + k - 1 : ℕ) : ℝ) q b - ((L + k - 1 : ℕ) : ℝ) / (q.totient : ℝ)) -
          (thetaAP ((L - 1 : ℕ) : ℝ) q b - ((L - 1 : ℕ) : ℝ) / (q.totient : ℝ))|
        ≤ |thetaAP ((L + k - 1 : ℕ) : ℝ) q b - ((L + k - 1 : ℕ) : ℝ) / (q.totient : ℝ)| +
          |thetaAP ((L - 1 : ℕ) : ℝ) q b - ((L - 1 : ℕ) : ℝ) / (q.totient : ℝ)| := abs_sub _ _
      _ ≤ E + E := add_le_add h1 h2
      _ = 2 * E := by ring
  have hdf : ∀ i, ‖f (i + 1) - f i‖ ≤ 2 * Real.pi * |β| := by
    intro i
    have e : f (i + 1) - f i = f i * (ee β - 1) := by
      simp only [hf]
      rw [show (((L + (i + 1) : ℕ) : ℝ) * β) = ((L + i : ℕ) : ℝ) * β + β by push_cast; ring,
        ee_add]
      ring
    rw [e, norm_mul, hf]
    simp only [norm_ee, one_mul]
    exact norm_ee_sub_one_le β
  have hpi : 1 ≤ 2 * Real.pi := by linarith [Real.pi_gt_three]
  calc ‖f (n - 1) • ∑ i ∈ range n, g i -
        ∑ i ∈ range (n - 1), (f (i + 1) - f i) • ∑ j ∈ range (i + 1), g j‖
      ≤ ‖f (n - 1) • ∑ i ∈ range n, g i‖ +
        ‖∑ i ∈ range (n - 1), (f (i + 1) - f i) • ∑ j ∈ range (i + 1), g j‖ := norm_sub_le _ _
    _ ≤ 2 * E + ∑ i ∈ range (n - 1), (2 * Real.pi * |β|) * (2 * E) := by
        gcongr
        · rw [smul_eq_mul, norm_mul, hf]; simp only [norm_ee, one_mul]
          exact hA n hn1 le_rfl
        · refine (norm_sum_le _ _).trans (sum_le_sum fun i hi => ?_)
          rw [smul_eq_mul, norm_mul]
          rw [mem_range] at hi
          exact mul_le_mul (hdf i) (hA (i + 1) (by omega) (by omega)) (norm_nonneg _)
            (by positivity)
    _ = 2 * E * (1 + 2 * Real.pi * |β| * ((n - 1 : ℕ) : ℝ)) := by
        rw [sum_const, card_range, nsmul_eq_mul]; ring
    _ ≤ 2 * E * (2 * Real.pi * (1 + |β| * u)) := by
        gcongr
        have : |β| * ((n - 1 : ℕ) : ℝ) ≤ |β| * u := mul_le_mul_of_nonneg_left hnu (abs_nonneg β)
        nlinarith [abs_nonneg β, Real.pi_pos]
    _ = 4 * Real.pi * E0 * (1 + |β| * u) * u / Lg ^ K := by rw [hE]; ring

/-! ### Vacuity tests -/

/-- `thetaE` at `u = 1`, `q = 1`, `b = 0`, `β = 0` is `log 2`: the only prime in `[1, 2]`. -/
example : thetaE 1 0 1 0 = (Real.log 2 : ℂ) := by
  have : Iw 1 = {1, 2} := by unfold Iw; norm_num; decide
  unfold thetaE; rw [this]
  rw [Finset.filter_insert, Finset.filter_singleton]
  simp [Nat.not_prime_one, Nat.prime_two, Nat.ModEq, ee]

end LeanLab.SparseTernary.SWPartial
