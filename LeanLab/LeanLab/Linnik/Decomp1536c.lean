/-
Unit U-1536, run 20261026T0403Z-9802, DECOMPOSE, track T1.
P0026: J. Pintz and I. Z. Ruzsa, On Linnik's approximation to Goldbach's problem, I,
Acta Arith. 109.2 (2003), 169-194.

AI wrote this Lean code, Claude, checked only by the Lean kernel. Binary Goldbach is OPEN.

File c, Section 7, p. 185, Corollary 1, in the form the proof of Theorem 1 needs, with `d = 3/4`
in place of the printed `d = 0.7163435444776661`, and its use in Section 10, pp. 190-193.

Why `d = 3/4` is enough: in (10.5) the paper uses Corollary 1 as `|G| ≤ (1-η)L` outside `E`,
`1 - η = 0.716344`; the bound then enters (10.2) and (10.15) through `(1-η)^4` and `(1-η)^6`,
and (10.15) has room: with `3/4` the product in (10.14) is below `0.88 < 1`, `k7_with_34`.
Certifying the printed `d` would need the inf in (7.1) to about 15 digits, since the printed `d`
is that inf at `c = (log 2)/2`; numerics/u1536_cert.py finds the margin there below `10⁻⁵`.

This is the lab's weakening of Corollary 1, faithful to the method of Sections 4 to 7, not the
printed constant.

Assemblies, CONDITIONAL ON the leaves of files a, b, c: `devSet_34`, `cor1_34`, `cor1_N`.
Proved outright: `k7_with_34`, `paper_d_lt`.
-/
import Mathlib
import LeanLab.Linnik.Decomp1536b

namespace LeanLab.Linnik.Decomp1536c

open Real MeasureTheory Finset
open LeanLab.Linnik.Decomp1536a (Gpow Spow EL devSet devSet_le)
open LeanLab.Linnik.Decomp1536b (EL_one_le)

/-- The paper's `G(α) = Σ_{m=1}^{L} e(2^m α)`, Section 8, p. 186; it equals `G_L(2α)`. -/
noncomputable def Gpaper (L : ℕ) (α : ℝ) : ℂ :=
  ∑ m ∈ range L, Complex.exp (2 * π * Complex.I * ((2 : ℂ) ^ (m + 1) * α))

/-- LEAF. Unit U-1536. Numerical input for `λ = 1`, `d = 3/4`:
`1.454 · e^{-3/4} ≤ 0.98/√2`, that is `ψ(1) - 3/4 < -(log 2)/2` with room, (7.1), p. 184.
Equivalent to `2 · 1.454² ≤ 0.98² e^{3/2}`, `4.2283 ≤ 4.3042`. -/
theorem ratio_num : (1454 / 1000 : ℝ) * Real.exp (-(3 / 4)) ≤ (98 / 100) / Real.sqrt 2 := by
  sorry

/-- LEAF. Unit U-1536. A polynomial times a geometric factor is bounded:
for every `B` there is `C` with `11 (1 + L) 0.98^L L^B ≤ C` for all `L`. -/
theorem poly_geom (B : ℕ) :
    ∃ C : ℝ, ∀ L : ℕ, 11 * (1 + (L : ℝ)) * (98 / 100 : ℝ) ^ L * (L : ℝ) ^ B ≤ C := by
  sorry

/-- LEAF. Unit U-1536. Change of variable between the paper's `G(α) = G_L(2α)` of Section 8, p. 186,
and `G_L` of Section 4, p. 172: `α ↦ 2α` is two to one on `[0,1]` onto `[0,2]` and `G_L` has period
1, so the two large deviation sets have the same measure. -/
theorem measure_transfer (L : ℕ) (d : ℝ) :
    volume {α : ℝ | α ∈ Set.Icc (0 : ℝ) 1 ∧ d * L < ‖Gpaper L α‖} = volume (devSet L d) := by
  sorry

/-! ### Assemblies -/

/-- `|{x ∈ [0,1] : |G_L(x)| > 3L/4}| ≤ 11 (1 + L) 0.98^L / (√2)^L`.
CONDITIONAL ON the leaves of files a and b and on `ratio_num`. -/
theorem devSet_34 (L : ℕ) :
    volume (devSet L (3 / 4)) ≤
      ENNReal.ofReal (11 * (1 + (L : ℝ)) * (98 / 100 : ℝ) ^ L / Real.sqrt 2 ^ L) := by
  refine (devSet_le L (3 / 4) zero_le_one).trans (ENNReal.ofReal_le_ofReal ?_)
  have hE := EL_one_le L
  have hr := ratio_num
  have hs : 0 < Real.sqrt 2 := by positivity
  have hexp : Real.exp (-(1 * (3 / 4) * (L : ℝ))) = Real.exp (-(3 / 4)) ^ L := by
    rw [← Real.exp_nat_mul]; ring_nf
  have hpos : 0 ≤ Real.exp (-(3 / 4 : ℝ)) := (Real.exp_pos _).le
  have key : Real.exp (-(3 / 4 : ℝ)) ^ L * EL L 1 ≤ ((98 / 100) / Real.sqrt 2) ^ L := by
    calc Real.exp (-(3 / 4 : ℝ)) ^ L * EL L 1
        ≤ Real.exp (-(3 / 4 : ℝ)) ^ L * (1454 / 1000 : ℝ) ^ L :=
          mul_le_mul_of_nonneg_left hE (pow_nonneg hpos _)
      _ = ((1454 / 1000 : ℝ) * Real.exp (-(3 / 4))) ^ L := by rw [mul_pow]; ring
      _ ≤ ((98 / 100) / Real.sqrt 2) ^ L :=
          pow_le_pow_left₀ (by positivity) hr L
  have h11 : (0 : ℝ) ≤ 11 * (1 + 1 * (L : ℝ)) := by positivity
  calc 11 * (1 + 1 * (L : ℝ)) * Real.exp (-(1 * (3 / 4) * (L : ℝ))) * EL L 1
      = 11 * (1 + 1 * (L : ℝ)) * (Real.exp (-(3 / 4 : ℝ)) ^ L * EL L 1) := by
        rw [hexp]; ring
    _ ≤ 11 * (1 + 1 * (L : ℝ)) * ((98 / 100) / Real.sqrt 2) ^ L :=
        mul_le_mul_of_nonneg_left key h11
    _ = 11 * (1 + (L : ℝ)) * (98 / 100 : ℝ) ^ L / Real.sqrt 2 ^ L := by
        rw [div_pow]; ring

/-- Corollary 1 of p. 185 with `d = 3/4`, in terms of `L`: for every `B` there is `C` with
`|{x ∈ [0,1] : |G_L(x)| > 3L/4}| ≤ C / ((√2)^L L^B)` for `L ≥ 1`.
CONDITIONAL ON the leaves of files a, b and c. -/
theorem cor1_34 (B : ℕ) : ∃ C : ℝ, ∀ L : ℕ, 1 ≤ L →
    volume (devSet L (3 / 4)) ≤ ENNReal.ofReal (C / (Real.sqrt 2 ^ L * (L : ℝ) ^ B)) := by
  obtain ⟨C, hC⟩ := poly_geom B
  refine ⟨C, fun L hL => (devSet_34 L).trans (ENNReal.ofReal_le_ofReal ?_)⟩
  have hLpos : (0 : ℝ) < (L : ℝ) ^ B := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    positivity
  have hs : (0 : ℝ) < Real.sqrt 2 ^ L := by positivity
  rw [le_div_iff₀ (mul_pos hs hLpos)]
  have := hC L
  calc 11 * (1 + (L : ℝ)) * (98 / 100 : ℝ) ^ L / Real.sqrt 2 ^ L * (Real.sqrt 2 ^ L * (L : ℝ) ^ B)
      = 11 * (1 + (L : ℝ)) * (98 / 100 : ℝ) ^ L * (L : ℝ) ^ B := by
        field_simp
    _ ≤ C := this

/-- Corollary 1 of p. 185 with `d = 3/4`, in the paper's form: with `L = [log₂ N]` and the paper's
`G(α) = Σ_{m=1}^{L} e(2^m α)`, for every `B` there is `C` with
`|{α ∈ [0,1] : |G(α)| > 3L/4}| ≤ C N^{-1/2} L^{-B}` for `N ≥ 2`.
CONDITIONAL ON the leaves of files a, b and c. -/
theorem cor1_N (B : ℕ) : ∃ C : ℝ, ∀ N : ℕ, 2 ≤ N →
    volume {α : ℝ | α ∈ Set.Icc (0 : ℝ) 1 ∧ (3 / 4 : ℝ) * (Nat.log 2 N : ℕ) <
        ‖Gpaper (Nat.log 2 N) α‖} ≤
      ENNReal.ofReal (C / (Real.sqrt N * ((Nat.log 2 N : ℕ) : ℝ) ^ B)) := by
  obtain ⟨C, hC⟩ := cor1_34 B
  refine ⟨Real.sqrt 2 * |C|, fun N hN => ?_⟩
  set L := Nat.log 2 N with hLdef
  have hL : 1 ≤ L := Nat.log_pos (by norm_num) hN
  rw [measure_transfer]
  refine (hC L hL).trans (ENNReal.ofReal_le_ofReal ?_)
  have hNlt : N < 2 ^ (L + 1) := Nat.lt_pow_succ_log_self (by norm_num) N
  have hNlt' : (N : ℝ) ≤ 2 ^ (L + 1) := by exact_mod_cast hNlt.le
  have hs2 : (0 : ℝ) < Real.sqrt 2 := by positivity
  have hsqN : Real.sqrt N ≤ Real.sqrt 2 * Real.sqrt 2 ^ L := by
    calc Real.sqrt N ≤ Real.sqrt (2 ^ (L + 1)) := Real.sqrt_le_sqrt hNlt'
      _ = Real.sqrt 2 ^ (L + 1) := by
          rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow,
            Real.mul_self_sqrt (by norm_num)]
      _ = Real.sqrt 2 * Real.sqrt 2 ^ L := by ring
  have hNpos : (0 : ℝ) < Real.sqrt N := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < N))
  have hLB : (0 : ℝ) < (L : ℝ) ^ B := by
    have : (0 : ℝ) < L := by exact_mod_cast hL
    positivity
  have hsL : (0 : ℝ) < Real.sqrt 2 ^ L := by positivity
  calc C / (Real.sqrt 2 ^ L * (L : ℝ) ^ B) ≤ |C| / (Real.sqrt 2 ^ L * (L : ℝ) ^ B) :=
        div_le_div_of_nonneg_right (le_abs_self C) (by positivity)
    _ = Real.sqrt 2 * |C| / (Real.sqrt 2 * Real.sqrt 2 ^ L * (L : ℝ) ^ B) := by
        field_simp
    _ ≤ Real.sqrt 2 * |C| / (Real.sqrt N * (L : ℝ) ^ B) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right hsqN hLB.le

/-- The printed constant of Corollary 1 is below `3/4`, and so is `1 - η` of Lemma 13, p. 190.
Proved. -/
theorem paper_d_lt : (0.7163435444776661 : ℝ) < 3 / 4 ∧ (1 - 0.283656 : ℝ) < 3 / 4 := by
  constructor <;> norm_num

/-- (10.2) and (10.15), pp. 191-193, with `d = 3/4` in place of `1 - η`: for `0 ≤ A(3) < 0.0136`,
`0 ≤ A(4) < 0.004`, `0 ≤ C₂' < 3.9095`, the product in (10.14) with `K = 7`, `i = 4`, `j = 3`, is
`(A(4) + C₂' d^6)(A(3) + C₂' d^4) < 0.88 < 1`.  Proved; no leaf. -/
theorem k7_with_34 {A3 A4 C : ℝ} (h3 : 0 ≤ A3) (h3' : A3 < 0.0136) (h4 : 0 ≤ A4)
    (h4' : A4 < 0.004) (hC : 0 ≤ C) (hC' : C < 3.9095) :
    (A4 + C * (3 / 4 : ℝ) ^ 6) * (A3 + C * (3 / 4 : ℝ) ^ 4) < 0.88 ∧
      Real.sqrt ((A4 + C * (3 / 4 : ℝ) ^ 6) * (A3 + C * (3 / 4 : ℝ) ^ 4)) < 1 := by
  have e1 : A4 + C * (3 / 4 : ℝ) ^ 6 < 0.6999 := by norm_num at *; nlinarith
  have e2 : A3 + C * (3 / 4 : ℝ) ^ 4 < 1.2506 := by norm_num at *; nlinarith
  have p1 : 0 ≤ A4 + C * (3 / 4 : ℝ) ^ 6 := by positivity
  have p2 : 0 ≤ A3 + C * (3 / 4 : ℝ) ^ 4 := by positivity
  have hprod : (A4 + C * (3 / 4 : ℝ) ^ 6) * (A3 + C * (3 / 4 : ℝ) ^ 4) < 0.88 := by
    calc (A4 + C * (3 / 4 : ℝ) ^ 6) * (A3 + C * (3 / 4 : ℝ) ^ 4)
        ≤ 0.6999 * (A3 + C * (3 / 4 : ℝ) ^ 4) := mul_le_mul_of_nonneg_right e1.le p2
      _ < 0.6999 * 1.2506 := by linarith
      _ < 0.88 := by norm_num
  refine ⟨hprod, ?_⟩
  rw [Real.sqrt_lt' one_pos]
  linarith

end LeanLab.Linnik.Decomp1536c
