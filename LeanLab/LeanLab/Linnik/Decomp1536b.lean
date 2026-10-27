/-
Unit U-1536, run 20261026T0403Z-9802, DECOMPOSE, track T1.
P0026: J. Pintz and I. Z. Ruzsa, On Linnik's approximation to Goldbach's problem, I,
Acta Arith. 109.2 (2003), 169-194.

AI wrote this Lean code, Claude, checked only by the Lean kernel. Binary Goldbach is OPEN.

File b, Sections 5 and 6 of the paper, pp. 177-184, with `g = 2`, rescaled from `[0, 2π]` to
`[0, 1]`: the moment recurrence for products `∏_{j<L} φ(2^j x)` of a cosine polynomial
`φ(y) = Σ_{j ≤ k} b_j cos(2π j y)`, and an explicit certificate bounding `E_L(1)`.

* `vcoef k b n L = ∫_0^1 cos(2π n x) ∏_{j<L} φ(2^j x) dx`, the `v_{n,L}` of p. 177, case (a).
* `Umat k b`, the `k × k` matrix of Lemma 6, p. 179, `m = k - 1`, with entries
  `u_{nl} = ½ (b_{2l-n} + b_{2l+n} + b_{n-2l})` for `l ≥ 1` and `u_{n0} = ½ (b_{-n} + b_n)`.
  QUESTION, not a finding: the printed formula of Lemma 6 also adds `b_{n-gl}` at `l = 0`, which
  counts the term `j = n` of Lemma 5 twice; with it, `v_{0,1}` would be `3 b_0 / 2` instead of
  `b_0`.  The corrected matrix reproduces the direct integral numerically, see PROGRESS.md.
* The certificate: degree `k = 6`, `λ = 1`, `φ = b6` the degree 6 Taylor polynomial of `e^t` at
  `t = cos 2πy` plus `2.719/7!`, Perron vector `w6`, `ρ = 1.454`.  The paper uses the extremal
  polynomials of Theorem 3, degree 19; a cruder certificate suffices for `d = 3/4`.

Assemblies, CONDITIONAL ON the leaves: `lemma5`, `lemma7`, `up_b6`, `EL_one_le`.
Proved outright: `bz_nonneg`, `Umat_nonneg`, `b6_nonneg`, `w6_pos`.
-/
import Mathlib
import LeanLab.Linnik.Decomp1536a

namespace LeanLab.Linnik.Decomp1536b

open Real MeasureTheory Finset
open LeanLab.Linnik.Decomp1536a (Spow EL)
open scoped Matrix

/-- `φ(y) = Σ_{j=0}^{k} b_j cos(2π j y)`, (5.1), p. 177, rescaled to period 1. -/
noncomputable def cosPoly (k : ℕ) (b : ℕ → ℝ) (y : ℝ) : ℝ :=
  ∑ j ∈ range (k + 1), b j * Real.cos (2 * π * ((j : ℝ) * y))

/-- `∏_{j=0}^{L-1} φ(2^j x)`, p. 177. -/
noncomputable def Fprod (k : ℕ) (b : ℕ → ℝ) (L : ℕ) (x : ℝ) : ℝ :=
  ∏ j ∈ range L, cosPoly k b ((2 : ℝ) ^ j * x)

/-- `v_{n,L} = ∫_0^1 cos(2π n x) ∏_{j<L} φ(2^j x) dx`, p. 177, Lebesgue case (a). -/
noncomputable def vcoef (k : ℕ) (b : ℕ → ℝ) (n L : ℕ) : ℝ :=
  ∫ x in (0 : ℝ)..1, Real.cos (2 * π * ((n : ℝ) * x)) * Fprod k b L x

/-- `b_j` extended by `0` outside `0 ≤ j ≤ k`, Lemma 6, p. 179. -/
noncomputable def bz (k : ℕ) (b : ℕ → ℝ) (j : ℤ) : ℝ :=
  if 0 ≤ j ∧ j ≤ k then b j.toNat else 0

/-- The matrix `U` of Lemma 6, p. 179, `g = 2`, `m = k - 1`, with the `l = 0` column corrected,
see the file header. -/
noncomputable def Umat (k : ℕ) (b : ℕ → ℝ) : Matrix (Fin k) (Fin k) ℝ :=
  fun n l => (1 / 2) * (bz k b (2 * ((l : ℕ) : ℤ) - ((n : ℕ) : ℤ)) +
    bz k b (2 * ((l : ℕ) : ℤ) + ((n : ℕ) : ℤ)) +
    if (l : ℕ) = 0 then 0 else bz k b (((n : ℕ) : ℤ) - 2 * ((l : ℕ) : ℤ)))

/-- The halving term of Lemma 5, p. 177: `V(|r|/2)` when `2 ∣ r`, else `0`. -/
noncomputable def hterm (V : ℕ → ℝ) (r : ℤ) : ℝ :=
  if 2 ∣ r then V (r.natAbs / 2) else 0

/-- LEAF. Unit U-1536. `∏_{j<L+1} φ(2^j x) = φ(x) ∏_{j<L} φ(2^j (2x))`, first line of the proof of
Lemma 5, p. 178. -/
theorem Fprod_succ (k : ℕ) (b : ℕ → ℝ) (L : ℕ) (x : ℝ) :
    Fprod k b (L + 1) x = cosPoly k b x * Fprod k b L (2 * x) := by
  sorry

/-- LEAF. Unit U-1536. The product has period 1, p. 178, "the product has period 2π/g", rescaled. -/
theorem Fprod_periodic (k : ℕ) (b : ℕ → ℝ) (L : ℕ) (x : ℝ) :
    Fprod k b L (x + 1) = Fprod k b L x := by
  sorry

/-- LEAF. Unit U-1536. The product is continuous. -/
theorem Fprod_continuous (k : ℕ) (b : ℕ → ℝ) (L : ℕ) : Continuous (Fprod k b L) := by
  sorry

/-- LEAF. Unit U-1536. Product to sum, the expansion of `h(x) = φ(x) cos nx` in the proof of
Lemma 5, p. 178: `cos(2πnx) φ(x) = ½ Σ_j b_j (cos(2π(j+n)x) + cos(2π(j-n)x))`. -/
theorem cos_mul_cosPoly (k : ℕ) (b : ℕ → ℝ) (n : ℕ) (x : ℝ) :
    Real.cos (2 * π * ((n : ℝ) * x)) * cosPoly k b x =
      (1 / 2) * ∑ j ∈ range (k + 1), b j *
        (Real.cos (2 * π * ((((j : ℤ) + (n : ℤ) : ℤ) : ℝ) * x)) +
          Real.cos (2 * π * ((((j : ℤ) - (n : ℤ) : ℤ) : ℝ) * x))) := by
  sorry

/-- LEAF. Unit U-1536. The halving step of Lemma 5, p. 178, the averaging over `ν` and the change of
variable `x → x/g`, `g = 2`: for continuous `F` of period 1 and integer `r`,
`∫_0^1 cos(2π r x) F(2x) dx` is `∫_0^1 cos(2π (|r|/2) y) F(y) dy` if `2 ∣ r` and `0` otherwise. -/
theorem halving {F : ℝ → ℝ} (hF : Continuous F) (hper : ∀ x, F (x + 1) = F x) (r : ℤ) :
    ∫ x in (0 : ℝ)..1, Real.cos (2 * π * ((r : ℝ) * x)) * F (2 * x) =
      hterm (fun m => ∫ y in (0 : ℝ)..1, Real.cos (2 * π * ((m : ℝ) * y)) * F y) r := by
  sorry

/-- LEAF. Unit U-1536. Initial values, p. 179, continuous case: `v_{0,0} = 1`, `v_{n,0} = 0` for
`n ≥ 1`. -/
theorem vcoef_zero (k : ℕ) (b : ℕ → ℝ) (n : ℕ) :
    vcoef k b n 0 = if n = 0 then 1 else 0 := by
  sorry

/-- LEAF. Unit U-1536. The index restriction behind Lemma 6, p. 179, `g = 2`, `m = k - 1`:
for `n ≤ k - 1` the right side of Lemma 5 involves only `V l` with `l ≤ k - 1`, and equals
`Σ_l u_{nl} V l` with the matrix `Umat`.  Pure finite algebra. -/
theorem lemma6_reindex {k : ℕ} (hk : 1 ≤ k) (b : ℕ → ℝ) (V : ℕ → ℝ) (n : Fin k) :
    (1 / 2) * ∑ j ∈ range (k + 1), b j *
        (hterm V ((j : ℤ) + ((n : ℕ) : ℤ)) + hterm V ((j : ℤ) - ((n : ℕ) : ℤ))) =
      ∑ l : Fin k, Umat k b n l * V l := by
  sorry

/-- LEAF. Unit U-1536. Perron bound, used after Lemma 7, p. 179, "the asymptotic behaviour depends
on the largest eigenvalue of U": if `U ≥ 0` entrywise, `w > 0` and `U w ≤ ρ w` entrywise, then
`(U^L)_{ii} ≤ ρ^L`. -/
theorem perron {k : ℕ} (U : Matrix (Fin k) (Fin k) ℝ) (hU : ∀ i j, 0 ≤ U i j)
    (w : Fin k → ℝ) (hw : ∀ i, 0 < w i) (ρ : ℝ) (h : ∀ i, (U *ᵥ w) i ≤ ρ * w i)
    (L : ℕ) (i : Fin k) : (U ^ L) i i ≤ ρ ^ L := by
  sorry

/-- LEAF. Unit U-1536. Comparison, (5.2), p. 177: if `e^{λ cos 2πy} ≤ φ(y)` for all `y`, then
`E_L(λ) = ∫_0^1 ∏_j e^{λ cos(2π 2^j x)} ≤ ∫_0^1 ∏_j φ(2^j x) = v_{0,L}`. -/
theorem EL_le_vcoef {k : ℕ} {b : ℕ → ℝ} {lam : ℝ}
    (hup : ∀ y, Real.exp (lam * Real.cos (2 * π * y)) ≤ cosPoly k b y) (L : ℕ) :
    EL L lam ≤ vcoef k b 0 L := by
  sorry

/-! ### Assemblies for Lemmas 5 and 7 -/

/-- Lemma 5, p. 177, `g = 2`, continuous case:
`v_{n,L+1} = ½ Σ_j b_j (v_{(j+n)/2, L} [2 ∣ j+n] + v_{|j-n|/2, L} [2 ∣ j-n])`.
CONDITIONAL ON `Fprod_succ`, `Fprod_periodic`, `Fprod_continuous`, `cos_mul_cosPoly`, `halving`. -/
theorem lemma5 (k : ℕ) (b : ℕ → ℝ) (n L : ℕ) :
    vcoef k b n (L + 1) = (1 / 2) * ∑ j ∈ range (k + 1), b j *
      (hterm (fun m => vcoef k b m L) ((j : ℤ) + (n : ℤ)) +
        hterm (fun m => vcoef k b m L) ((j : ℤ) - (n : ℤ))) := by
  have hF := Fprod_continuous k b L
  have hP := Fprod_periodic k b L
  have hc : ∀ r : ℤ, Continuous fun x : ℝ =>
      Real.cos (2 * π * ((r : ℝ) * x)) * Fprod k b L (2 * x) := by
    intro r
    exact (Real.continuous_cos.comp (by fun_prop)).mul (hF.comp (by fun_prop))
  have hpt : ∀ x : ℝ, Real.cos (2 * π * ((n : ℝ) * x)) * Fprod k b (L + 1) x =
      ∑ j ∈ range (k + 1),
        ((1 / 2) * b j * (Real.cos (2 * π * ((((j : ℤ) + (n : ℤ) : ℤ) : ℝ) * x)) *
            Fprod k b L (2 * x)) +
          (1 / 2) * b j * (Real.cos (2 * π * ((((j : ℤ) - (n : ℤ) : ℤ) : ℝ) * x)) *
            Fprod k b L (2 * x))) := by
    intro x
    rw [Fprod_succ, ← mul_assoc, cos_mul_cosPoly, Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  have hL : vcoef k b n (L + 1) = ∫ x in (0 : ℝ)..1, ∑ j ∈ range (k + 1),
        ((1 / 2) * b j * (Real.cos (2 * π * ((((j : ℤ) + (n : ℤ) : ℤ) : ℝ) * x)) *
            Fprod k b L (2 * x)) +
          (1 / 2) * b j * (Real.cos (2 * π * ((((j : ℤ) - (n : ℤ) : ℤ) : ℝ) * x)) *
            Fprod k b L (2 * x))) := by
    unfold vcoef
    exact intervalIntegral.integral_congr fun x _ => hpt x
  rw [hL, intervalIntegral.integral_finsetSum]
  · rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [intervalIntegral.integral_add (((hc _).intervalIntegrable 0 1).const_mul _)
        (((hc _).intervalIntegrable 0 1).const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      halving hF hP, halving hF hP]
    unfold vcoef
    ring
  · intro j _
    exact (((hc _).intervalIntegrable 0 1).const_mul _).add
      (((hc _).intervalIntegrable 0 1).const_mul _)

/-- The vector form of Lemmas 6 and 7: `(v_{0,L}, ..., v_{k-1,L}) = U^L e_0`.
CONDITIONAL ON `lemma5`'s leaves, `vcoef_zero`, `lemma6_reindex`. -/
theorem vvec_eq {k : ℕ} (hk : 1 ≤ k) (b : ℕ → ℝ) (L : ℕ) :
    (fun n : Fin k => vcoef k b n L) = (Umat k b ^ L) *ᵥ (Pi.single ⟨0, hk⟩ 1) := by
  induction L with
  | zero =>
    funext n
    rw [pow_zero, Matrix.one_mulVec, vcoef_zero, Pi.single_apply]
    simp [Fin.ext_iff]
  | succ L ih =>
    funext n
    rw [pow_succ', ← Matrix.mulVec_mulVec, ← ih, lemma5, lemma6_reindex hk]
    rfl

/-- Lemma 7, p. 179, continuous case: `∫_0^1 ∏_{j<L} φ(2^j x) dx = (U^L)_{00}`.
CONDITIONAL ON the leaves behind `vvec_eq`. -/
theorem lemma7 {k : ℕ} (hk : 1 ≤ k) (b : ℕ → ℝ) (L : ℕ) :
    vcoef k b 0 L = (Umat k b ^ L) ⟨0, hk⟩ ⟨0, hk⟩ := by
  have := congrFun (vvec_eq hk b L) ⟨0, hk⟩
  simp only at this
  rw [this]
  simp [Matrix.mulVec, dotProduct, Pi.single_apply]

/-- `b_j ≥ 0` gives `bz ≥ 0`. Proved. -/
theorem bz_nonneg {k : ℕ} {b : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j) (j : ℤ) : 0 ≤ bz k b j := by
  unfold bz
  split_ifs
  · exact hb _
  · exact le_refl 0

/-- `b_j ≥ 0` gives `U ≥ 0` entrywise, as needed for `perron`. Proved. -/
theorem Umat_nonneg {k : ℕ} {b : ℕ → ℝ} (hb : ∀ j, 0 ≤ b j) (n l : Fin k) :
    0 ≤ Umat k b n l := by
  unfold Umat
  have h1 := bz_nonneg (k := k) hb (2 * ((l : ℕ) : ℤ) - ((n : ℕ) : ℤ))
  have h2 := bz_nonneg (k := k) hb (2 * ((l : ℕ) : ℤ) + ((n : ℕ) : ℤ))
  have h3 := bz_nonneg (k := k) hb (((n : ℕ) : ℤ) - 2 * ((l : ℕ) : ℤ))
  split_ifs <;> positivity

/-! ### The explicit certificate, `k = 6`, `λ = 1` -/

/-- Cosine coefficients of `Σ_{n ≤ 6} cos(2πy)^n / n! + 2719/5040000`; the constant
`2719/5040000 = 2.719/7!` bounds the Taylor remainder `e/7!`. -/
noncomputable def b6 : ℕ → ℝ
  | 0 => 4255771 / 3360000
  | 1 => 217 / 192
  | 2 => 139 / 512
  | 3 => 17 / 384
  | 4 => 7 / 1280
  | 5 => 1 / 1920
  | 6 => 1 / 23040
  | _ => 0

/-- The Perron vector, rounded. -/
noncomputable def w6 : Fin 6 → ℝ := ![1, 3361 / 5000, 7519 / 10000, 5781 / 10000, 1551 / 2000, 1079 / 2000]

/-- Proved. -/
theorem b6_nonneg (j : ℕ) : 0 ≤ b6 j := by
  unfold b6
  split <;> norm_num

/-- Proved. -/
theorem w6_pos (i : Fin 6) : 0 < w6 i := by
  fin_cases i <;> simp [w6]

/-- LEAF. Unit U-1536. The cosine expansion of the upper polynomial, Section 6, p. 180, "a cosine
polynomial can be written as `φ(x) = f(cos x)`": with `t = cos 2πy`,
`Σ_{j ≤ 6} b6_j cos(2π j y) = Σ_{n ≤ 6} t^n/n! + 2719/5040000`.  Multiple angle identities. -/
theorem cosPoly_b6 (y : ℝ) :
    cosPoly 6 b6 y =
      ∑ n ∈ range 7, Real.cos (2 * π * y) ^ n / (n.factorial : ℝ) + 2719 / 5040000 := by
  sorry

/-- LEAF. Unit U-1536. An upper approximation as in (6.2), p. 180, `λ = 1`, degree 6:
for `|t| ≤ 1`, `e^t ≤ Σ_{n ≤ 6} t^n/n! + 2719/5040000`; the Taylor remainder is at most
`e/7! < 2.719/5040`. -/
theorem exp_le_taylor6 {t : ℝ} (h1 : -1 ≤ t) (h2 : t ≤ 1) :
    Real.exp t ≤ ∑ n ∈ range 7, t ^ n / (n.factorial : ℝ) + 2719 / 5040000 := by
  sorry

/-- LEAF. Unit U-1536. The Perron certificate for the matrix of Lemma 6 built from `b6`:
`(U w6)_i ≤ 1.454 (w6)_i` for every `i`, exact rational arithmetic; the margins are between
`3.9·10⁻⁴` and `7.8·10⁻⁴`, numerics/u1536_cert.py.  The spectral radius is about `1.45322`. -/
theorem cert6 (i : Fin 6) : (Umat 6 b6 *ᵥ w6) i ≤ 1454 / 1000 * w6 i := by
  sorry

/-- `e^{cos 2πy} ≤ φ(y)` for `φ = b6`, the upper approximation of (5.2) with `λ = 1`.
CONDITIONAL ON `cosPoly_b6`, `exp_le_taylor6`. -/
theorem up_b6 (y : ℝ) : Real.exp (1 * Real.cos (2 * π * y)) ≤ cosPoly 6 b6 y := by
  rw [one_mul, cosPoly_b6]
  exact exp_le_taylor6 (Real.neg_one_le_cos _) (Real.cos_le_one _)

/-- `E_L(1) ≤ 1.454^L`, so `ψ(1) ≤ log 1.454 < 0.3744`, the numerical input of Section 7, p. 184,
from Sections 5 and 6.  CONDITIONAL ON the leaves of this file. -/
theorem EL_one_le (L : ℕ) : EL L 1 ≤ (1454 / 1000 : ℝ) ^ L := by
  have hk : 1 ≤ 6 := by norm_num
  calc EL L 1 ≤ vcoef 6 b6 0 L := EL_le_vcoef up_b6 L
    _ = (Umat 6 b6 ^ L) ⟨0, hk⟩ ⟨0, hk⟩ := lemma7 hk b6 L
    _ ≤ (1454 / 1000 : ℝ) ^ L :=
        perron _ (Umat_nonneg b6_nonneg) w6 w6_pos _ cert6 L _

end LeanLab.Linnik.Decomp1536b
