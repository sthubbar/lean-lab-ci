/-
# U-1441, T3 MOONSHOT: the Katai-Bourgain-Sarnak-Ziegler criterion on the reflected prime weight

PC run 20261021T1603Z-28836, unit U-1441. AI wrote this Lean code.

Route: apply Katai's orthogonality criterion, in the Bourgain-Sarnak-Ziegler form, to
`G(n) = Λ(N - n)` to get the parity sensitive statement `Σ_{p<N} μ(N - p) log p = o(N)`.
The criterion has three steps: the Turan-Kubilius weight `w(n) = #{p ∈ P : p ∣ n}`, the
multiplicativity `μ(p m) = -μ(m)`, and Cauchy-Schwarz over `m`, which trades the Mobius sum for
the dilated correlations `Σ_m G(p m) G(q m)`.  For `p ≠ q` these count `k` with `N - p k` and
`N - q k` both prime, points of the binary prime equation `q a - p b = (q - p) N`.

PROVED here, unconditional:
* `weight_swap`: `Σ_{n ∈ s} F n * w(n) = Σ_{p ∈ P} Σ_{n ∈ s, p ∣ n} F n`.
* `moebius_prime_mul`: `μ(p m) = -μ(m)` for `p` prime, `p ∤ m`.
* `bilinear_cs`: `(Σ_m a_m Σ_p b_p G p m)^2 ≤ (Σ_m a_m^2) Σ_m (Σ_p b_p G p m)^2`.
* `bilinear_expand`: `Σ_m (Σ_p b_p G p m)^2 = Σ_p Σ_q b_p b_q Σ_m G p m G q m`.
* `diag_floor`: for nonnegative `b` and `G` the square sum is at least its diagonal part
  `Σ_p b_p^2 Σ_m (G p m)^2`, so the Cauchy-Schwarz output cannot fall below the diagonal.
* `katai_output_ge_floor`: the method's output `sqrt(M · Σ_m (Σ_p b_p G p m)^2)` is at least
  `sqrt(M · Σ_p b_p^2 Σ_m (G p m)^2)`, the sparsity floor.
* `dilation_line`: `N - p n = a`, `N - q n = b` give `q a - p b = (q - p) N`.
* vacuity examples.
-/
import Mathlib

namespace LeanLab.Routes.U1441

open Finset

/-- The Turan-Kubilius weight swap: summing `F` against `w(n) = #{p ∈ P : p ∣ n}` is the same
as summing `F` over the multiples of each `p ∈ P`. -/
theorem weight_swap (s P : Finset ℕ) (F : ℕ → ℝ) :
    ∑ n ∈ s, F n * ((P.filter (· ∣ n)).card : ℝ) =
      ∑ p ∈ P, ∑ n ∈ s.filter (p ∣ ·), F n := by
  simp_rw [Finset.card_eq_sum_ones, Nat.cast_sum, Nat.cast_one, Finset.mul_sum, mul_one,
    Finset.sum_filter]
  exact Finset.sum_comm

/-- `μ(p m) = -μ(m)` for a prime `p` not dividing `m`. -/
theorem moebius_prime_mul {p m : ℕ} (hp : p.Prime) (hm : ¬ p ∣ m) :
    ArithmeticFunction.moebius (p * m) = - ArithmeticFunction.moebius m := by
  have hc : Nat.Coprime p m := (Nat.Prime.coprime_iff_not_dvd hp).2 hm
  rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc,
    ArithmeticFunction.moebius_apply_prime hp]
  ring

/-- Cauchy-Schwarz over the outer variable, the Katai step. -/
theorem bilinear_cs {ι κ : Type*} (S : Finset ι) (P : Finset κ) (a : ι → ℝ) (b : κ → ℝ)
    (G : κ → ι → ℝ) :
    (∑ m ∈ S, a m * ∑ p ∈ P, b p * G p m) ^ 2 ≤
      (∑ m ∈ S, a m ^ 2) * ∑ m ∈ S, (∑ p ∈ P, b p * G p m) ^ 2 :=
  Finset.sum_mul_sq_le_sq_mul_sq S a (fun m => ∑ p ∈ P, b p * G p m)

/-- Expanding the square: the dilated correlations `Σ_m G p m G q m` appear. -/
theorem bilinear_expand {ι κ : Type*} (S : Finset ι) (P : Finset κ) (b : κ → ℝ)
    (G : κ → ι → ℝ) :
    ∑ m ∈ S, (∑ p ∈ P, b p * G p m) ^ 2 =
      ∑ p ∈ P, ∑ q ∈ P, b p * b q * ∑ m ∈ S, G p m * G q m := by
  simp_rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun q _ => ?_
  refine Finset.sum_congr rfl fun m _ => ?_
  ring

/-- The diagonal floor: with nonnegative coefficients and weights the square sum is at least
its diagonal `p = q` part. -/
theorem diag_floor {ι κ : Type*} [DecidableEq κ] (S : Finset ι) (P : Finset κ) (b : κ → ℝ)
    (G : κ → ι → ℝ) (hb : ∀ p ∈ P, 0 ≤ b p) (hG : ∀ p ∈ P, ∀ m ∈ S, 0 ≤ G p m) :
    ∑ p ∈ P, b p ^ 2 * ∑ m ∈ S, G p m ^ 2 ≤ ∑ m ∈ S, (∑ p ∈ P, b p * G p m) ^ 2 := by
  rw [bilinear_expand]
  refine Finset.sum_le_sum fun p hp => ?_
  have hnn : ∀ q ∈ P, 0 ≤ b p * b q * ∑ m ∈ S, G p m * G q m := fun q hq =>
    mul_nonneg (mul_nonneg (hb p hp) (hb q hq))
      (Finset.sum_nonneg fun m hm => mul_nonneg (hG p hp m hm) (hG q hq m hm))
  have h1 := Finset.single_le_sum hnn hp
  have h2 : b p * b p * ∑ m ∈ S, G p m * G p m = b p ^ 2 * ∑ m ∈ S, G p m ^ 2 := by
    simp_rw [sq]
  linarith

/-- The Katai output `sqrt(M · Σ_m (Σ_p b_p G p m)^2)` never drops below the sparsity floor
`sqrt(M · Σ_p b_p^2 Σ_m (G p m)^2)`, whatever the off-diagonal correlations are. -/
theorem katai_output_ge_floor {ι κ : Type*} [DecidableEq κ] (S : Finset ι) (P : Finset κ)
    (b : κ → ℝ) (G : κ → ι → ℝ) (M : ℝ) (hM : 0 ≤ M) (hb : ∀ p ∈ P, 0 ≤ b p)
    (hG : ∀ p ∈ P, ∀ m ∈ S, 0 ≤ G p m) :
    Real.sqrt (M * ∑ p ∈ P, b p ^ 2 * ∑ m ∈ S, G p m ^ 2) ≤
      Real.sqrt (M * ∑ m ∈ S, (∑ p ∈ P, b p * G p m) ^ 2) :=
  Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left (diag_floor S P b G hb hG) hM)

/-- The dilated pair `(N - p n, N - q n)` lies on the line `q a - p b = (q - p) N`. -/
theorem dilation_line (N p q n a b : ℤ) (ha : N - p * n = a) (hb : N - q * n = b) :
    q * a - p * b = (q - p) * N := by
  subst ha hb; ring

/-! Vacuity checks. -/

/-- `N = 100`, `p = 3`, `q = 7`, `n = 2`: `94` and `86`, and `7 · 94 - 3 · 86 = 4 · 100`. -/
example : (7 : ℤ) * 94 - 3 * 86 = (7 - 3) * 100 := dilation_line 100 3 7 2 94 86 rfl rfl

/-- `μ(3 · 2) = -μ(2)`, an instance of `moebius_prime_mul`. -/
example : ArithmeticFunction.moebius (3 * 2) = - ArithmeticFunction.moebius 2 :=
  moebius_prime_mul Nat.prime_three (by norm_num)

/-- The weight swap at `s = {6}`, `P = {2, 3}`, `F = 1`: both sides are `2`. -/
example : ∑ n ∈ ({6} : Finset ℕ), (1 : ℝ) * (((({2, 3} : Finset ℕ)).filter (· ∣ n)).card : ℝ) =
    ∑ p ∈ ({2, 3} : Finset ℕ), ∑ n ∈ ({6} : Finset ℕ).filter (p ∣ ·), (1 : ℝ) :=
  weight_swap {6} {2, 3} (fun _ => 1)

/-- The floor hypotheses hold for a concrete nonnegative instance. -/
example : ∑ p ∈ ({0, 1} : Finset ℕ), (1 : ℝ) ^ 2 * ∑ m ∈ ({0} : Finset ℕ), (1 : ℝ) ^ 2 ≤
    ∑ m ∈ ({0} : Finset ℕ), (∑ p ∈ ({0, 1} : Finset ℕ), (1 : ℝ) * 1) ^ 2 :=
  diag_floor {0} {0, 1} (fun _ => 1) (fun _ _ => 1) (fun _ _ => zero_le_one)
    (fun _ _ _ _ => zero_le_one)

end LeanLab.Routes.U1441

#print axioms LeanLab.Routes.U1441.weight_swap
#print axioms LeanLab.Routes.U1441.moebius_prime_mul
#print axioms LeanLab.Routes.U1441.bilinear_cs
#print axioms LeanLab.Routes.U1441.bilinear_expand
#print axioms LeanLab.Routes.U1441.diag_floor
#print axioms LeanLab.Routes.U1441.katai_output_ge_floor
#print axioms LeanLab.Routes.U1441.dilation_line
