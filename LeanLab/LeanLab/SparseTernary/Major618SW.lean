/-
P0086 Basak, Bhat, Dong, Zaharescu 2024, arXiv 2409.08968 v1, Section 6, displays (6.1)-(6.22).
Unit U-1383, PC run 20261021T1203Z-6472. AI-written Lean code, Claude. Checked only by the
Lean kernel. Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.

Goal: `Major618 A B` of `MajorArcs.lean` from Siegel-Walfisz.

Named Props, NOT axioms, NOT proved here:
* `SW N`: Siegel-Walfisz for `θ(x; q, a)`, moduli `q ≤ (log x)^N`; the paper uses
  `N = B + 3A + 1`, since `q_ℓ ≤ q q_0 ≤ (log u)^{B + 3A}` up to the factor of (4.3).
  The textbook theorem, cited.
* `Expand613 A B`: `SW (B + 3A + 1) → MajorExpand A B`, the paper's derivation (6.1)-(6.13)
  together with the bookkeeping (6.18)-(6.21): on the major arcs the integral is
  `𝔖_P(m) · J(m,u,1/Q)` up to `u² (log u)^{12A - B + ε}`, `J` the truncated singular integral.
* `SingInt617 B`: (6.14)-(6.17), `|J(m,u,1/Q) - H(m,u)| ≪ u² (log u)^{-2B}` on `4u ≤ m ≤ 5u`.

PROVED here, unconditional:
* `sexp_detect`: the additive-character expansion that opens (6.2): for every `α`,
  `S(α) = q_0⁻¹ Σ_{ℓ < q_0} Σ_{r ∈ R_0} e(-ℓ r/q_0) S̃(α + ℓ/q_0)`, `S̃` the full sum over
  `u ≤ k ≤ 2u` with weight `Λ(k)`.
* `norm_SingP_le`: `|𝔖_P(m)| ≤ 2e⁴ q_0⁵` for every `P`, from `fq_split` and `tail_hv`.
* `major618_of_SW`: `Major618 A B` for `15A ≤ B`, CONDITIONAL ON `SW (B + 3A + 1)`,
  `Expand613 A B` and `SingInt617 B`.
-/
import Mathlib
import LeanLab.SparseTernary.Tail72

open Finset Filter Real MeasureTheory
open scoped Classical

noncomputable section
namespace LeanLab.SparseTernary.Major618SW

open LeanLab.SparseTernary LeanLab.SparseTernary.Section4 LeanLab.SparseTernary.MajorArcs
open LeanLab.SparseTernary.LocalFactors LeanLab.SparseTernary.Lemma82Proof
open LeanLab.SparseTernary.Tail72Proof

/-! ### Definitions -/

/-- The integers `u ≤ k ≤ 2u`. -/
def Iu (u : ℝ) : Finset ℕ := Icc ⌈u⌉₊ ⌊2 * u⌋₊

/-- `S̃(β) = Σ_{u ≤ k ≤ 2u} Λ(k) e(kβ)`, no congruence condition, as in (6.2). -/
def Stil (u β : ℝ) : ℂ := ∑ k ∈ Iu u, (ArithmeticFunction.vonMangoldt k : ℂ) * ee (k * β)

/-- (6.7) `T(β) = Σ_{u ≤ k ≤ 2u} e(kβ)`. -/
def Tsum (u β : ℝ) : ℂ := ∑ k ∈ Iu u, ee (k * β)

/-- The truncated singular integral `J(m, u, δ) = ∫_{-δ}^{δ} T(β)³ e(-mβ) dβ` of (6.13)-(6.14). -/
def Jint (m : ℕ) (u δ : ℝ) : ℂ := ∫ β in (-δ)..δ, Tsum u β ^ 3 * ee (-(m * β))

/-- `θ(x; q, a) = Σ_{p ≤ x, p ≡ a (q)} log p`. -/
def thetaAP (x : ℝ) (q a : ℕ) : ℝ :=
  ∑ p ∈ (Icc 1 ⌊x⌋₊).filter (fun p => p.Prime ∧ p ≡ a [MOD q]), Real.log p

/-! ### The cited Props -/

/-- **Siegel-Walfisz**, moduli up to `(log x)^N`: there are `c > 0` and `C` with
`|θ(x; q, a) - x/φ(q)| ≤ C x exp(-c √(log x))` for `x ≥ 2`, `1 ≤ q ≤ (log x)^N`, `(a, q) = 1`.
Plain math: for every fixed N, θ(x;q,a) = x/φ(q) + O_N(x exp(-c_N √log x)) uniformly in
q ≤ (log x)^N. Cited textbook theorem, e.g. Davenport, Chapter 22; NOT proved. -/
def SW (N : ℝ) : Prop :=
  ∃ c C : ℝ, 0 < c ∧ ∀ x : ℝ, 2 ≤ x → ∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ N →
    a.Coprime q →
      |thetaAP x q a - x / q.totient| ≤ C * x * Real.exp (-c * Real.sqrt (Real.log x))

/-- The output of (6.1)-(6.13) with (6.18)-(6.21), before the singular integral is evaluated:
`∫_𝔐 S³ e(-mα) = 𝔖_P(m) J(m, u, 1/Q) + O_ε(u² (log u)^{12A - B + ε})`, where
`1/Q = (log u)^B / u`. -/
def MajorExpand (A B : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C u0 : ℝ, ∀ u : ℝ, u0 ≤ u → ∀ m : ℕ, 4 * u ≤ m → (m : ℝ) ≤ 5 * u →
    ‖(∫ α in majorArcs (Real.log u ^ B) (u / Real.log u ^ B),
        Sexp (Zof A u) u α ^ 3 * ee (-(m * α))) -
      SingP (Zof A u) m (Real.log u ^ B) * Jint m u (Real.log u ^ B / u)‖ ≤
      C * u ^ 2 * Real.log u ^ (12 * (A : ℝ) - B + ε)

/-- **(6.1)-(6.13), (6.18)-(6.21) as an implication from Siegel-Walfisz.** Plain math: SW with
moduli up to (log u)^{B+3A+1} gives, through (6.4) characters, (6.5)-(6.9) partial summation
and (6.10) `S̃(α_ℓ) = μ(q_ℓ)/φ(q_ℓ) T(β) + O(u exp(-c₁√log u))`, the expansion `MajorExpand`.
NOT proved. -/
def Expand613 (A B : ℕ) : Prop := SW ((B : ℝ) + 3 * A + 1) → MajorExpand A B

/-- **(6.14)-(6.17)**: `|J(m, u, 1/Q) - H(m, u)| ≤ C u² (log u)^{-2B}` for `4u ≤ m ≤ 5u`.
Plain math: the singular integral over |β| ≤ 1/Q is H(m,u) + O(u²(log u)^{-2B}).
NOT proved here. -/
def SingInt617 (B : ℕ) : Prop :=
  ∃ C u0 : ℝ, ∀ u : ℝ, u0 ≤ u → ∀ m : ℕ, 4 * u ≤ m → (m : ℝ) ≤ 5 * u →
    ‖Jint m u (Real.log u ^ B / u) - (Hmu m u : ℂ)‖ ≤ C * u ^ 2 * Real.log u ^ (-(2 * (B : ℝ)))

/-! ### (6.2): detecting `k mod q_0 ∈ R_0` by additive characters. PROVED. -/

theorem R0_unique {Z r r' : ℕ} (hr : r ∈ R0 Z) (hr' : r' ∈ R0 Z)
    (h : (q0 Z : ℤ) ∣ (r : ℤ) - r') : r = r' := by
  have h1 := (mem_Icc.mp (mem_filter.mp hr).1)
  have h2 := (mem_Icc.mp (mem_filter.mp hr').1)
  have hlt : |(r : ℤ) - r'| < (q0 Z : ℤ) := by
    rw [abs_lt]; constructor <;> omega
  have := Int.eq_zero_of_abs_lt_dvd h hlt
  omega

/-- `Σ_{r ∈ R_0} [q_0 ∣ k - r] = [k mod q_0 ∈ R_0]`. -/
theorem count_R0 (Z k : ℕ) :
    ∑ r ∈ R0 Z, (if (q0 Z : ℤ) ∣ (k : ℤ) - r then (1 : ℂ) else 0) =
      if (∃ r ∈ R0 Z, k ≡ r [MOD q0 Z]) then 1 else 0 := by
  split_ifs with hex
  · obtain ⟨r0, hr0, hk⟩ := hex
    have hk' : (q0 Z : ℤ) ∣ (k : ℤ) - r0 := by
      rw [dvd_sub_comm]; exact (Nat.modEq_iff_dvd).mp hk
    have hiff : ∀ r ∈ R0 Z, ((q0 Z : ℤ) ∣ (k : ℤ) - r ↔ r0 = r) := by
      intro r hr; constructor
      · intro h
        have : (q0 Z : ℤ) ∣ (r0 : ℤ) - r := by
          have := dvd_sub h hk'; rw [show (k : ℤ) - r - (k - r0) = r0 - r by ring] at this
          exact this
        exact R0_unique hr0 hr this
      · rintro rfl; exact hk'
    rw [sum_congr rfl (fun r hr => if_congr (hiff r hr) rfl rfl), sum_ite_eq]
    simp [hr0]
  · refine sum_eq_zero fun r hr => ?_
    rw [if_neg]
    intro h
    exact hex ⟨r, hr, (Nat.modEq_iff_dvd).mpr (by rw [dvd_sub_comm]; exact h)⟩

theorem key_detect (Z k : ℕ) (α : ℝ) :
    (1 / (q0 Z : ℂ)) * ∑ ℓ ∈ range (q0 Z), ∑ r ∈ R0 Z,
        ee (-((ℓ : ℝ) * r / q0 Z)) * ee (k * (α + ℓ / q0 Z)) =
      if (∃ r ∈ R0 Z, k ≡ r [MOD q0 Z]) then ee (k * α) else 0 := by
  have hq := q0_pos Z
  have hq0 : (q0 Z : ℂ) ≠ 0 := by exact_mod_cast hq.ne'
  have hqr : (q0 Z : ℝ) ≠ 0 := by exact_mod_cast hq.ne'
  have hterm : ∀ ℓ r : ℕ, ee (-((ℓ : ℝ) * r / q0 Z)) * ee (k * (α + ℓ / q0 Z)) =
      ee (k * α) * ee ((ℓ : ℝ) * (((k : ℤ) - r : ℤ) : ℝ) / q0 Z) := by
    intro ℓ r
    rw [← ee_add, ← ee_add]; congr 1; push_cast; field_simp; ring
  simp_rw [hterm]
  rw [sum_comm]
  simp_rw [← mul_sum, sum_range_ee (q0 Z) hq]
  have : ee (k * α) * ∑ r ∈ R0 Z, (if (q0 Z : ℤ) ∣ ((k : ℤ) - r) then (q0 Z : ℂ) else 0) =
      ee (k * α) * (q0 Z : ℂ) *
        ∑ r ∈ R0 Z, (if (q0 Z : ℤ) ∣ (k : ℤ) - r then (1 : ℂ) else 0) := by
    rw [mul_assoc, mul_sum (a := (q0 Z : ℂ))]; congr 1; refine sum_congr rfl fun r _ => ?_
    split_ifs <;> ring
  rw [this, count_R0]
  split_ifs
  · field_simp
  · simp

/-- **The expansion opening (6.2), PROVED**: for every `α`,
`S(α) = q_0⁻¹ Σ_{ℓ < q_0} Σ_{r ∈ R_0} e(-ℓr/q_0) S̃(α + ℓ/q_0)`.
Plain math: the indicator of k mod q_0 in R_0 equals q_0^{-1} Σ_ℓ Σ_r e(ℓ(k - r)/q_0). -/
theorem sexp_detect (Z : ℕ) (u α : ℝ) :
    Sexp Z u α = (1 / (q0 Z : ℂ)) * ∑ ℓ ∈ range (q0 Z), ∑ r ∈ R0 Z,
      ee (-((ℓ : ℝ) * r / q0 Z)) * Stil u (α + ℓ / q0 Z) := by
  symm
  have h1 : ∀ ℓ r : ℕ, ee (-((ℓ : ℝ) * r / q0 Z)) * Stil u (α + ℓ / q0 Z) =
      ∑ k ∈ Iu u, (ArithmeticFunction.vonMangoldt k : ℂ) *
        (ee (-((ℓ : ℝ) * r / q0 Z)) * ee (k * (α + ℓ / q0 Z))) := by
    intro ℓ r; unfold Stil; rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
  simp_rw [h1]
  rw [sum_congr rfl (fun ℓ _ => sum_comm), sum_comm, mul_sum]
  have h2 : ∀ k ∈ Iu u, (1 / (q0 Z : ℂ)) * ∑ ℓ ∈ range (q0 Z), ∑ r ∈ R0 Z,
      (ArithmeticFunction.vonMangoldt k : ℂ) *
        (ee (-((ℓ : ℝ) * r / q0 Z)) * ee (k * (α + ℓ / q0 Z))) =
      (ArithmeticFunction.vonMangoldt k : ℂ) * ((1 / (q0 Z : ℂ)) * ∑ ℓ ∈ range (q0 Z),
        ∑ r ∈ R0 Z, ee (-((ℓ : ℝ) * r / q0 Z)) * ee (k * (α + ℓ / q0 Z))) := by
    intro k _; simp_rw [← mul_sum]; ring
  rw [sum_congr rfl h2]
  simp_rw [key_detect]
  unfold Sexp Aset
  rw [sum_filter]
  refine sum_congr rfl fun k _ => ?_
  split_ifs <;> simp

/-! ### (6.15): the full singular integral counts triples. PROVED. -/

theorem tsum_expand (u : ℝ) (m : ℕ) (β : ℝ) :
    Tsum u β ^ 3 * ee (-(m * β)) =
      ∑ k₁ ∈ Iu u, ∑ k₂ ∈ Iu u, ∑ k₃ ∈ Iu u, ee ((((k₁ + k₂ + k₃ : ℤ) - m : ℤ) : ℝ) * β) := by
  unfold Tsum
  rw [pow_three]
  simp only [Finset.sum_mul, Finset.mul_sum]
  refine sum_congr rfl fun k₁ _ => sum_congr rfl fun k₂ _ => sum_congr rfl fun k₃ _ => ?_
  unfold ee; simp only [← Complex.exp_add]; congr 1; push_cast; ring

/-- **(6.15), PROVED**: `∫₀¹ T(β)³ e(-mβ) dβ` is the number of `k₁ + k₂ + k₃ = m` with
every `kᵢ ∈ [u, 2u]`. Plain math: orthogonality of e(nβ) on [0, 1]. -/
theorem tint_count (u : ℝ) (m : ℕ) :
    ∫ β in (0 : ℝ)..1, Tsum u β ^ 3 * ee (-(m * β)) =
      ∑ k₁ ∈ Iu u, ∑ k₂ ∈ Iu u, ∑ k₃ ∈ Iu u, (if k₁ + k₂ + k₃ = m then (1 : ℂ) else 0) := by
  have hfun : (fun β : ℝ => Tsum u β ^ 3 * ee (-(m * β))) = fun β : ℝ =>
      ∑ k₁ ∈ Iu u, ∑ k₂ ∈ Iu u, ∑ k₃ ∈ Iu u, ee ((((k₁ + k₂ + k₃ : ℤ) - m : ℤ) : ℝ) * β) :=
    funext (tsum_expand u m)
  rw [hfun]
  rw [intervalIntegral.integral_finset_sum fun k₁ _ =>
    (by fun_prop : Continuous _).intervalIntegrable _ _]
  refine sum_congr rfl fun k₁ _ => ?_
  rw [intervalIntegral.integral_finset_sum fun k₂ _ =>
    (by fun_prop : Continuous _).intervalIntegrable _ _]
  refine sum_congr rfl fun k₂ _ => ?_
  rw [intervalIntegral.integral_finset_sum fun k₃ _ =>
    (by fun_prop : Continuous _).intervalIntegrable _ _]
  refine sum_congr rfl fun k₃ _ => ?_
  rw [Identity.integral_ee_int]
  split_ifs with h1 h2 h2
  · rfl
  · exfalso; apply h2; omega
  · exfalso; apply h1; omega
  · rfl

/-! ### A bound for the partial singular series. PROVED. -/

/-- **`|𝔖_P(m)| ≤ 2e⁴ q_0⁵`** for every `P`: `𝔖_P = Σ_{w ∣ q_0} f(w) Σ_{v ≤ P/w} h(v)`,
`|f(w)| ≤ q_0⁴`, `Σ |h(v)| ≤ 2e⁴`. -/
theorem norm_SingP_le (Z m : ℕ) (P : ℝ) :
    ‖SingP Z m P‖ ≤ 2 * Real.exp 4 * (q0 Z : ℝ) ^ 5 := by
  unfold SingP
  rw [sum_fq_split]
  have hterm : ∀ w ∈ (q0 Z).divisors,
      ‖fq Z m w * ∑ v ∈ Icc 1 (⌊P⌋₊ / w), hv Z m v‖ ≤ (q0 Z : ℝ) ^ 4 * (2 * Real.exp 4) := by
    intro w hw
    rw [norm_mul]
    refine mul_le_mul (norm_fq_le Z m w (Nat.divisor_le hw)) ?_ (norm_nonneg _) (by positivity)
    have e : Icc 1 (⌊P⌋₊ / w) = Ioc 0 (⌊P⌋₊ / w) := by
      ext x; simp only [mem_Icc, mem_Ioc]; omega
    rw [e]
    refine le_trans (norm_sum_le _ _) ?_
    have := tail_hv Z m 0 (⌊P⌋₊ / w)
    simpa using this
  calc ‖∑ w ∈ (q0 Z).divisors, fq Z m w * ∑ v ∈ Icc 1 (⌊P⌋₊ / w), hv Z m v‖
      ≤ ∑ w ∈ (q0 Z).divisors, ‖fq Z m w * ∑ v ∈ Icc 1 (⌊P⌋₊ / w), hv Z m v‖ :=
        norm_sum_le _ _
    _ ≤ ∑ w ∈ (q0 Z).divisors, (q0 Z : ℝ) ^ 4 * (2 * Real.exp 4) := sum_le_sum hterm
    _ = (#(q0 Z).divisors : ℝ) * ((q0 Z : ℝ) ^ 4 * (2 * Real.exp 4)) := by
        rw [sum_const, nsmul_eq_mul]
    _ ≤ (q0 Z : ℝ) * ((q0 Z : ℝ) ^ 4 * (2 * Real.exp 4)) := by
        gcongr; exact_mod_cast Nat.card_divisors_le_self _
    _ = 2 * Real.exp 4 * (q0 Z : ℝ) ^ 5 := by ring

theorem q0_pow5_le (A : ℕ) (u : ℝ) (hL : 1 ≤ Real.log u) :
    (q0 (Zof A u) : ℝ) ^ 5 ≤ Real.log u ^ (27 * (A : ℝ)) := by
  have hL0 : 0 < Real.log u := by linarith
  have hq := q0_sq_le A u hL
  have h1 : (1 : ℝ) ≤ q0 (Zof A u) := by exact_mod_cast q0_pos (Zof A u)
  calc (q0 (Zof A u) : ℝ) ^ 5 ≤ (q0 (Zof A u) : ℝ) ^ 6 := pow_le_pow_right₀ h1 (by norm_num)
    _ = ((q0 (Zof A u) : ℝ) ^ 2) ^ 3 := by ring
    _ ≤ (Real.log u ^ (9 * (A : ℝ))) ^ 3 := pow_le_pow_left₀ (by positivity) hq 3
    _ = Real.log u ^ (27 * (A : ℝ)) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; push_cast; ring

/-! ### Major618 from Siegel-Walfisz, CONDITIONAL -/

/-- **`Major618 A B` for `15A ≤ B`, CONDITIONAL ON `SW (B + 3A + 1)`, `Expand613 A B` and
`SingInt617 B`.** Plain math: ∫_𝔐 - H 𝔖_P = (∫_𝔐 - 𝔖_P J) + 𝔖_P (J - H), the first part is
O(u²(log u)^{12A-B+ε}) by (6.13)-(6.21), the second at most 2e⁴ q_0⁵ · C u²(log u)^{-2B}
≤ C' u²(log u)^{27A-2B}, and 27A - 2B ≤ 12A - B once B ≥ 15A. -/
theorem major618_of_SW (A B : ℕ) (hB : 15 * A ≤ B) (hSW : SW ((B : ℝ) + 3 * A + 1))
    (hE : Expand613 A B) (hJ : SingInt617 B) : Major618 A B := by
  intro ε hε
  obtain ⟨C1, u1, h1⟩ := hE hSW ε hε
  obtain ⟨C2, u2, h2⟩ := hJ
  refine ⟨|C1| + 2 * Real.exp 4 * |C2|, max (max u1 u2) (Real.exp 1),
    fun u hu m hm1 hm2 => ?_⟩
  have hu1 : u1 ≤ u := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hu
  have hu2 : u2 ≤ u := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hu
  have hue : Real.exp 1 ≤ u := le_trans (le_max_right _ _) hu
  have hL : 1 ≤ Real.log u := by
    have := Real.log_le_log (Real.exp_pos 1) hue
    rwa [Real.log_exp] at this
  have hL0 : 0 < Real.log u := by linarith
  set I := ∫ α in majorArcs (Real.log u ^ B) (u / Real.log u ^ B),
    Sexp (Zof A u) u α ^ 3 * ee (-(m * α)) with hI
  set Sg := SingP (Zof A u) m (Real.log u ^ B) with hSg
  set J := Jint m u (Real.log u ^ B / u) with hJdef
  set X := Real.log u ^ (12 * (A : ℝ) - B + ε) with hX
  have hX0 : 0 ≤ X := by positivity
  have hu2' : 0 ≤ u ^ 2 := by positivity
  have hE1 : ‖I - Sg * J‖ ≤ |C1| * u ^ 2 * X :=
    le_trans (h1 u hu1 m hm1 hm2)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hu2') hX0)
  have hJ2 : ‖J - (Hmu m u : ℂ)‖ ≤ |C2| * u ^ 2 * Real.log u ^ (-(2 * (B : ℝ))) :=
    le_trans (h2 u hu2 m hm1 hm2)
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_abs_self _) hu2')
        (by positivity))
  have hS : ‖Sg‖ ≤ 2 * Real.exp 4 * Real.log u ^ (27 * (A : ℝ)) :=
    le_trans (norm_SingP_le _ _ _)
      (mul_le_mul_of_nonneg_left (q0_pow5_le A u hL) (by positivity))
  have hexp : Real.log u ^ (27 * (A : ℝ)) * Real.log u ^ (-(2 * (B : ℝ))) ≤ X := by
    rw [← Real.rpow_add hL0, hX]
    apply Real.rpow_le_rpow_of_exponent_le hL
    have : (15 : ℝ) * A ≤ B := by exact_mod_cast hB
    linarith
  have hprod : ‖Sg * (J - (Hmu m u : ℂ))‖ ≤ 2 * Real.exp 4 * |C2| * u ^ 2 * X := by
    rw [norm_mul]
    calc ‖Sg‖ * ‖J - (Hmu m u : ℂ)‖
        ≤ (2 * Real.exp 4 * Real.log u ^ (27 * (A : ℝ))) *
            (|C2| * u ^ 2 * Real.log u ^ (-(2 * (B : ℝ)))) :=
          mul_le_mul hS hJ2 (norm_nonneg _) (by positivity)
      _ = 2 * Real.exp 4 * |C2| * u ^ 2 *
            (Real.log u ^ (27 * (A : ℝ)) * Real.log u ^ (-(2 * (B : ℝ)))) := by ring
      _ ≤ 2 * Real.exp 4 * |C2| * u ^ 2 * X :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
  have hsplit : I - (Hmu m u : ℂ) * Sg = (I - Sg * J) + Sg * (J - (Hmu m u : ℂ)) := by ring
  rw [hsplit]
  calc ‖(I - Sg * J) + Sg * (J - (Hmu m u : ℂ))‖
      ≤ ‖I - Sg * J‖ + ‖Sg * (J - (Hmu m u : ℂ))‖ := norm_add_le _ _
    _ ≤ |C1| * u ^ 2 * X + 2 * Real.exp 4 * |C2| * u ^ 2 * X := add_le_add hE1 hprod
    _ = (|C1| + 2 * Real.exp 4 * |C2|) * u ^ 2 * X := by ring

/-- **RepProp A, CONDITIONAL ON `Minor516W A B`, `SW (B + 3A + 1)`, `Expand613 A B`,
`SingInt617 B`**, for `A ≥ 1`, `B ≥ 36A + 3`, `B ≥ 28A + 13`. -/
theorem repProp_of_SW (A B : ℕ) (hA : 1 ≤ A) (hB1 : 36 * A + 3 ≤ B) (hB2 : 28 * A + 13 ≤ B)
    (hmin : RepAssembly.Minor516W A B) (hSW : SW ((B : ℝ) + 3 * A + 1))
    (hE : Expand613 A B) (hJ : SingInt617 B) : RepProp A :=
  repProp_of_two A B hA hB1 hB2 hmin (major618_of_SW A B (by omega) hSW hE hJ)

/-! ### Vacuity tests -/

/-- The antecedent of `SW N` is met at `x = e`, `q = a = 1`, for every `N`. -/
example (N : ℝ) : (2 : ℝ) ≤ Real.exp 1 ∧ ((1 : ℕ) : ℝ) ≤ Real.log (Real.exp 1) ^ N ∧
    (1 : ℕ).Coprime 1 := by
  refine ⟨?_, ?_, by norm_num⟩
  · have := Real.add_one_le_exp (1 : ℝ); linarith
  · rw [Real.log_exp, Real.one_rpow]; norm_num

/-- `sexp_detect` at `Z = 4`, `q_0 = 6`: a genuine instance with six additive characters. -/
example (u α : ℝ) : Sexp 4 u α = (1 / (q0 4 : ℂ)) * ∑ ℓ ∈ range (q0 4), ∑ r ∈ R0 4,
    ee (-((ℓ : ℝ) * r / q0 4)) * Stil u (α + ℓ / q0 4) := sexp_detect 4 u α

/-- The side conditions of `repProp_of_SW` hold at `A = 1`, `B = 41`, and `15A ≤ B`. -/
example : 1 ≤ (1 : ℕ) ∧ 36 * 1 + 3 ≤ (41 : ℕ) ∧ 28 * 1 + 13 ≤ (41 : ℕ) ∧ 15 * 1 ≤ (41 : ℕ) := by
  norm_num

end LeanLab.SparseTernary.Major618SW

#print axioms LeanLab.SparseTernary.Major618SW.R0_unique
#print axioms LeanLab.SparseTernary.Major618SW.count_R0
#print axioms LeanLab.SparseTernary.Major618SW.key_detect
#print axioms LeanLab.SparseTernary.Major618SW.sexp_detect
#print axioms LeanLab.SparseTernary.Major618SW.tsum_expand
#print axioms LeanLab.SparseTernary.Major618SW.tint_count
#print axioms LeanLab.SparseTernary.Major618SW.norm_SingP_le
#print axioms LeanLab.SparseTernary.Major618SW.q0_pow5_le
#print axioms LeanLab.SparseTernary.Major618SW.major618_of_SW
#print axioms LeanLab.SparseTernary.Major618SW.repProp_of_SW
