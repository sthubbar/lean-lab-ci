/-
P0054 J. Pintz 2021, Lemma 1, display (1.10): the minor arc bound for `S(α)`.
Unit U-1369, PC run 20261021T0604Z-1697, track T2.

Lemma 1, (1.10), as P0054 prints it and as the lab already uses it in `Lemma1On`:
for `α` on the minor arcs `𝔪` of (1.3), `|S(α)| ≪ (X/√P + X^{4/5}) L⁴`, `L = log X`.
Plain math: if `α` is not within `1/(qQ)` of any fraction `a/q` with `q ≤ P`, `Q = X/P`,
then the prime sum `S(α) = ∑_{X₁<p≤X} log p e(pα)` has size at most a constant times
`(X/√P + X^{4/5}) (log X)⁴`. Pin2, arXiv 1804.09084, does not number a Lemma 1; it quotes the
same bound before (2.6) as "the estimate of Vinogradov, reproved in a simpler way by Vaughan".

* `majorArcs P Q`: the major arcs `𝔐` of (1.3), all `a ∈ ℤ`, so the set is 1-periodic; without
  the coprimality of `a, q`, which gives the same set.
* `VaughanThm31`: the classical input, NAMED and CONDITIONAL: Vaughan, The Hardy-Littlewood
  method, Theorem 3.1; Davenport, Multiplicative Number Theory, chapter 25: for
  `|α - a/q| ≤ 1/q²`, `(a, q) = 1`, `∑_{n≤x} Λ(n) e(nα) ≪ (x/√q + x^{4/5} + √(xq)) (log x)⁴`.
  The lab has Vaughan's identity pointwise, `LeanLab.PNTPort.BV.vaughan_identity`, and Type I
  and Type II bounds for character sums only, not for `e(nα)`.
* `lemma1_of_vaughan`: PROVED reduction, CONDITIONAL ON `VaughanThm31`: Lemma 1 (1.10) with
  `A = 4C + 4`, through Dirichlet's theorem with lowest terms, and the prime power bound
  `|ψ - θ| ≤ 2 √x log x` of Mathlib.
* `minor31_of_vaughan`: (3.1) at `P = X^{7/25}`, CONDITIONAL ON `VaughanThm31` only.
* Vacuity test `inv_notMem_majorArcs`: `1/q` with `P < q < Q` lies on the minor arcs.
Binary Goldbach is OPEN. AI-written Lean code, Claude, 2026-10-21.
-/
import Mathlib
import LeanLab.Pintz2021.MinorArcs

namespace LeanLab.Pintz2021.Lemma1U1369

open Real Finset MeasureTheory Chebyshev
open LeanLab.PNTPort.LargeSieve LeanLab.Pintz2021.MinorArcs
open ArithmeticFunction hiding log

attribute [local instance] Classical.propDecidable

/-- The major arcs `𝔐` of (1.3) of P0054, periodic form: `α` within `1/(qQ)` of some `a/q`,
`1 ≤ q ≤ P`, `a ∈ ℤ`. -/
def majorArcs (P Q : ℝ) : Set ℝ :=
  {α | ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ P ∧ ∃ a : ℤ, |α - a / q| ≤ 1 / (q * Q)}

/-- The minor arcs `𝔪` of (1.3): `[1/Q, 1 + 1/Q] \ 𝔐`. -/
def minorArcs (P Q : ℝ) : Set ℝ := Set.Icc (1 / Q) (1 + 1 / Q) \ majorArcs P Q

/-- The sum `∑_{n ≤ x} Λ(n) e(nα)`. -/
noncomputable def VS (x α : ℝ) : ℂ := ∑ n ∈ Icc 0 ⌊x⌋₊, ((Λ n : ℝ) : ℂ) * e (n * α)

/-- CITED classical input, NAMED: Vaughan, The Hardy-Littlewood Method, Theorem 3.1;
Davenport, chapter 25. Plain math: if `(a, q) = 1` and `|α - a/q| ≤ 1/q²` then
`|∑_{n≤x} Λ(n) e(nα)| ≤ C (x q^{-1/2} + x^{4/5} + x^{1/2} q^{1/2}) (log x)⁴` for `x ≥ 2`. -/
def VaughanThm31 : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 2 ≤ x → ∀ α : ℝ, ∀ a : ℤ, ∀ q : ℕ, 0 < q → Int.gcd a q = 1 →
    |α - a / q| ≤ 1 / (q : ℝ) ^ 2 →
      ‖VS x α‖ ≤ C * (x / Real.sqrt q + x ^ (4 / 5 : ℝ) + Real.sqrt (x * q)) * Real.log x ^ 4

/-- Lemma 1, display (1.10) of P0054, with the constant `A`: for `2 ≤ X₁ ≤ X`, `3 ≤ X`,
`1 ≤ P ≤ X` and `α` off the major arcs at `Q = X/P`,
`|S(α)| ≤ A (X/√P + X^{4/5}) (log X)⁴`. -/
def Lemma1_110 (A : ℝ) : Prop :=
  ∀ X1 X P : ℝ, 2 ≤ X1 → X1 ≤ X → 3 ≤ X → 1 ≤ P → P ≤ X → ∀ α, α ∉ majorArcs P (X / P) →
    ‖S X1 X α‖ ≤ A * (X / Real.sqrt P + X ^ (4 / 5 : ℝ)) * Real.log X ^ 4

/-! ### Dirichlet's theorem in lowest terms -/

/-- HELPER: off the major arcs, Dirichlet gives `a/q` in lowest terms, `P < q ≤ Q`,
`|α - a/q| ≤ 1/(qQ)`. -/
theorem dirichlet_minor {P Q α : ℝ} (hQ : 1 ≤ Q) (hα : α ∉ majorArcs P Q) :
    ∃ a : ℤ, ∃ q : ℕ, 0 < q ∧ Int.gcd a q = 1 ∧ P < q ∧ (q : ℝ) ≤ Q ∧
      |α - a / q| ≤ 1 / (q * Q) := by
  have hn : 0 < ⌊Q⌋₊ := Nat.floor_pos.mpr hQ
  obtain ⟨j, k, hk0, hkn, hjk⟩ := Real.exists_int_int_abs_mul_sub_le α hn
  have hg : 0 < Int.gcd j k := Int.gcd_pos_of_ne_zero_right j hk0.ne'
  obtain ⟨g, a, q', hg0, hcop, rfl, rfl⟩ := Int.exists_gcd_one' hg
  have hq'0 : 0 < q' := by
    by_contra h
    push Not at h
    have : q' * (g : ℤ) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg h (by positivity)
    omega
  set q : ℕ := q'.toNat with hq
  have hqq : (q : ℤ) = q' := Int.toNat_of_nonneg hq'0.le
  have hq0 : 0 < q := by omega
  have hqr : (q : ℝ) = (q' : ℝ) := by exact_mod_cast hqq
  have hgr : (1 : ℝ) ≤ g := by exact_mod_cast hg0
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq0
  have hQpos : (0 : ℝ) < Q := by linarith
  have hfl : Q < (⌊Q⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one Q
  have hkQ : ((q' * g : ℤ) : ℝ) ≤ Q := by
    have : ((q' * g : ℤ) : ℝ) ≤ (⌊Q⌋₊ : ℝ) := by exact_mod_cast hkn
    exact this.trans (Nat.floor_le hQpos.le)
  have hk : ((q' * g : ℤ) : ℝ) = (q : ℝ) * g := by push_cast; rw [hqr]
  have hqk : (q : ℝ) ≤ q * g := le_mul_of_one_le_right hqpos.le hgr
  have happrox : |α - a / q| ≤ 1 / (q * Q) := by
    have e1 : α - a / q = (((q' * g : ℤ) : ℝ) * α - ((a * g : ℤ) : ℝ)) / ((q : ℝ) * g) := by
      rw [hk]; push_cast; rw [hqr]; field_simp
    rw [e1, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * g)]
    have h1 : |((q' * g : ℤ) : ℝ) * α - ((a * g : ℤ) : ℝ)| ≤ 1 / Q :=
      hjk.trans (one_div_le_one_div_of_le hQpos hfl.le)
    calc |((q' * g : ℤ) : ℝ) * α - ((a * g : ℤ) : ℝ)| / (q * g) ≤ (1 / Q) / (q * g) :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ (1 / Q) / q := div_le_div_of_nonneg_left (by positivity) hqpos hqk
      _ = 1 / (q * Q) := by field_simp
  refine ⟨a, q, hq0, ?_, ?_, ?_, happrox⟩
  · rw [hqq]; exact hcop
  · by_contra h
    push Not at h
    exact hα ⟨q, hq0, h, a, happrox⟩
  · exact hqk.trans (hk ▸ hkQ)

/-! ### From the prime sum to the von Mangoldt sum -/

/-- The prime part: `∑_{p ≤ x} log p e(pα)`. -/
noncomputable def Uθ (x α : ℝ) : ℂ :=
  ∑ n ∈ Icc 0 ⌊x⌋₊, (((if n.Prime then Real.log n else 0 : ℝ)) : ℂ) * e (n * α)

/-- HELPER: truncating a sum at `x ≤ X`. -/
theorem sum_trunc {M : Type*} [AddCommMonoid M] (f : ℕ → M) {x X : ℝ} (hx : 0 ≤ x)
    (hxX : x ≤ X) :
    ∑ n ∈ range (⌊X⌋₊ + 1), (if (n : ℝ) ≤ x then f n else 0) = ∑ n ∈ Icc 0 ⌊x⌋₊, f n := by
  rw [← sum_filter]
  congr 1
  ext n
  simp only [mem_filter, mem_range, mem_Icc, Nat.zero_le, true_and]
  constructor
  · rintro ⟨_, h⟩; exact Nat.le_floor h
  · intro h
    have h1 : (n : ℝ) ≤ x := (Nat.le_floor_iff hx).mp h
    exact ⟨Nat.lt_succ_of_le (Nat.le_floor (h1.trans hxX)), h1⟩

/-- HELPER: `S = Uθ(X) - Uθ(X₁)` for `0 ≤ X₁ ≤ X`. -/
theorem S_eq {X1 X : ℝ} (h0 : 0 ≤ X1) (h1 : X1 ≤ X) (α : ℝ) :
    S X1 X α = Uθ X α - Uθ X1 α := by
  have hpt : ∀ n : ℕ, aS X1 X n * e (n * α) =
      (if (n : ℝ) ≤ X then (((if n.Prime then Real.log n else 0 : ℝ)) : ℂ) * e (n * α) else 0) -
      (if (n : ℝ) ≤ X1 then (((if n.Prime then Real.log n else 0 : ℝ)) : ℂ) * e (n * α)
        else 0) := by
    intro n
    unfold aS
    by_cases hp : n.Prime <;> by_cases ha : (n : ℝ) ≤ X1 <;> by_cases hb : (n : ℝ) ≤ X <;>
      simp [hp, ha, hb] <;> (exfalso; linarith)
  unfold S Uθ
  simp_rw [hpt]
  rw [sum_sub_distrib, sum_trunc _ (h0.trans h1) le_rfl, sum_trunc _ h0 h1]

/-- HELPER: `‖Uθ(x) - VS(x)‖ ≤ ψ(x) - θ(x)`. -/
theorem norm_Uθ_sub_le (x α : ℝ) : ‖Uθ x α - VS x α‖ ≤ ψ x - θ x := by
  unfold Uθ VS
  rw [← sum_sub_distrib, psi_eq_sum_Icc, theta_eq_sum_Icc, sum_filter, ← sum_sub_distrib]
  refine (norm_sum_le _ _).trans (sum_le_sum fun n _ => ?_)
  rw [← sub_mul, norm_mul, norm_e, mul_one, ← Complex.ofReal_sub, Complex.norm_real,
    Real.norm_eq_abs]
  by_cases hp : n.Prime
  · simp [hp, vonMangoldt_apply_prime hp]
  · simp only [hp, ite_false, zero_sub, abs_neg, sub_zero]
    exact (abs_of_nonneg vonMangoldt_nonneg).le

/-- HELPER: `‖Uθ(x)‖ ≤ ‖VS(x)‖ + 2 √x log x` for `x ≥ 1`. -/
theorem norm_Uθ_le {x : ℝ} (hx : 1 ≤ x) (α : ℝ) :
    ‖Uθ x α‖ ≤ ‖VS x α‖ + 2 * Real.sqrt x * Real.log x := by
  have h1 := norm_Uθ_sub_le x α
  have h2 := le_of_abs_le (abs_psi_sub_theta_le_sqrt_mul_log hx)
  have h3 : ‖Uθ x α‖ ≤ ‖Uθ x α - VS x α‖ + ‖VS x α‖ := by
    simpa using norm_add_le (Uθ x α - VS x α) (VS x α)
  linarith

/-! ### The reduction -/

/-- HELPER: the Vaughan bound at `x ≤ X`, with `P < q ≤ X/P`, is at most
`C (2X/√P + X^{4/5}) (log X)⁴`. -/
theorem vaughan_term_le {C x X P : ℝ} {q : ℕ} (hC : 0 ≤ C) (hx : 2 ≤ x) (hxX : x ≤ X)
    (hP : 1 ≤ P) (hPq : P < q) (hqQ : (q : ℝ) ≤ X / P) :
    C * (x / Real.sqrt q + x ^ (4 / 5 : ℝ) + Real.sqrt (x * q)) * Real.log x ^ 4 ≤
      C * (2 * (X / Real.sqrt P) + X ^ (4 / 5 : ℝ)) * Real.log X ^ 4 := by
  have hx0 : 0 < x := by linarith
  have hX0 : 0 < X := by linarith
  have hP0 : 0 < P := by linarith
  have hsP : 0 < Real.sqrt P := Real.sqrt_pos.mpr hP0
  have h1 : x / Real.sqrt q ≤ X / Real.sqrt P :=
    div_le_div₀ hX0.le hxX hsP (Real.sqrt_le_sqrt hPq.le)
  have h2 : x ^ (4 / 5 : ℝ) ≤ X ^ (4 / 5 : ℝ) := rpow_le_rpow hx0.le hxX (by norm_num)
  have h3 : Real.sqrt (x * q) ≤ X / Real.sqrt P := by
    have hxq : x * q ≤ X ^ 2 / P := by
      have : x * q ≤ X * (X / P) :=
        mul_le_mul hxX hqQ (Nat.cast_nonneg _) hX0.le
      calc x * q ≤ X * (X / P) := this
        _ = X ^ 2 / P := by ring
    calc Real.sqrt (x * q) ≤ Real.sqrt (X ^ 2 / P) := Real.sqrt_le_sqrt hxq
      _ = X / Real.sqrt P := by rw [Real.sqrt_div (sq_nonneg X), Real.sqrt_sq hX0.le]
  have h4 : Real.log x ^ 4 ≤ Real.log X ^ 4 :=
    pow_le_pow_left₀ (Real.log_nonneg (by linarith)) (Real.log_le_log hx0 hxX) 4
  have hL0 : 0 ≤ Real.log x ^ 4 := pow_nonneg (Real.log_nonneg (by linarith)) 4
  have hin : x / Real.sqrt q + x ^ (4 / 5 : ℝ) + Real.sqrt (x * q) ≤
      2 * (X / Real.sqrt P) + X ^ (4 / 5 : ℝ) := by linarith
  have hB0 : 0 ≤ 2 * (X / Real.sqrt P) + X ^ (4 / 5 : ℝ) := by positivity
  calc C * (x / Real.sqrt q + x ^ (4 / 5 : ℝ) + Real.sqrt (x * q)) * Real.log x ^ 4
      ≤ C * (2 * (X / Real.sqrt P) + X ^ (4 / 5 : ℝ)) * Real.log x ^ 4 :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hin hC) hL0
    _ ≤ _ := mul_le_mul_of_nonneg_left h4 (mul_nonneg hC hB0)

/-- CONDITIONAL ON `VaughanThm31`: Lemma 1, display (1.10) of P0054, with `A = 4C + 4`. -/
theorem lemma1_of_vaughan (hV : VaughanThm31) : ∃ A : ℝ, 0 ≤ A ∧ Lemma1_110 A := by
  obtain ⟨C, hC, hV⟩ := hV
  refine ⟨4 * C + 4, by linarith, fun X1 X P h2 h1X h3 hP hPX α hα => ?_⟩
  have hX0 : 0 < X := by linarith
  have hP0 : 0 < P := by linarith
  have hQ : 1 ≤ X / P := (one_le_div hP0).mpr hPX
  obtain ⟨a, q, hq0, hcop, hPq, hqQ, happ⟩ := dirichlet_minor hQ hα
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq0
  have happ2 : |α - a / q| ≤ 1 / (q : ℝ) ^ 2 := by
    refine happ.trans (one_div_le_one_div_of_le (by positivity) ?_)
    rw [sq]; exact mul_le_mul_of_nonneg_left hqQ hqpos.le
  have vX := (hV X (by linarith) α a q hq0 hcop happ2).trans
    (vaughan_term_le hC (by linarith) le_rfl hP hPq hqQ)
  have vX1 := (hV X1 h2 α a q hq0 hcop happ2).trans
    (vaughan_term_le hC h2 h1X hP hPq hqQ)
  have uX := norm_Uθ_le (by linarith : (1 : ℝ) ≤ X) α
  have uX1 := norm_Uθ_le (by linarith : (1 : ℝ) ≤ X1) α
  -- the prime power error
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    exact (Real.exp_one_lt_d9.trans (by norm_num)).le.trans h3
  have hL0 : 0 ≤ Real.log X := by linarith
  have hpp : Real.sqrt X1 * Real.log X1 ≤ Real.sqrt X * Real.log X :=
    mul_le_mul (Real.sqrt_le_sqrt h1X) (Real.log_le_log (by linarith) h1X)
      (Real.log_nonneg (by linarith)) (Real.sqrt_nonneg _)
  have hsq : Real.sqrt X ≤ X ^ (4 / 5 : ℝ) := by
    rw [Real.sqrt_eq_rpow]; exact rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
  have hL4 : Real.log X ≤ Real.log X ^ 4 := by
    calc Real.log X = Real.log X ^ 1 := (pow_one _).symm
      _ ≤ Real.log X ^ 4 := pow_le_pow_right₀ hL1 (by norm_num)
  have hppX : Real.sqrt X * Real.log X ≤ X ^ (4 / 5 : ℝ) * Real.log X ^ 4 :=
    mul_le_mul hsq hL4 hL0 (by positivity)
  have hS := S_eq (by linarith : (0 : ℝ) ≤ X1) h1X α
  have hnorm : ‖S X1 X α‖ ≤ ‖Uθ X α‖ + ‖Uθ X1 α‖ := by rw [hS]; exact norm_sub_le _ _
  have hsP : 0 ≤ X / Real.sqrt P := by positivity
  have hX45 : 0 ≤ X ^ (4 / 5 : ℝ) := by positivity
  have hLL : 0 ≤ Real.log X ^ 4 := by positivity
  have key : C * (2 * (X / Real.sqrt P) + X ^ (4 / 5 : ℝ)) * Real.log X ^ 4 ≤
      2 * C * (X / Real.sqrt P + X ^ (4 / 5 : ℝ)) * Real.log X ^ 4 := by
    have : C * (2 * (X / Real.sqrt P) + X ^ (4 / 5 : ℝ)) ≤
        2 * C * (X / Real.sqrt P + X ^ (4 / 5 : ℝ)) := by nlinarith
    exact mul_le_mul_of_nonneg_right this hLL
  have key2 : X ^ (4 / 5 : ℝ) * Real.log X ^ 4 ≤
      (X / Real.sqrt P + X ^ (4 / 5 : ℝ)) * Real.log X ^ 4 :=
    mul_le_mul_of_nonneg_right (by linarith) hLL
  nlinarith

/-- HELPER: the major arcs are measurable. -/
theorem measurableSet_majorArcs (P Q : ℝ) : MeasurableSet (majorArcs P Q) := by
  have : majorArcs P Q = ⋃ q : ℕ, ⋃ a : ℤ,
      ({_α : ℝ | 0 < q ∧ (q : ℝ) ≤ P} ∩ {α : ℝ | |α - a / q| ≤ 1 / (q * Q)}) := by
    ext α
    simp only [majorArcs, Set.mem_setOf_eq, Set.mem_iUnion, Set.mem_inter_iff]
    constructor
    · rintro ⟨q, h0, hP, a, ha⟩; exact ⟨q, a, ⟨h0, hP⟩, ha⟩
    · rintro ⟨q, a, ⟨h0, hP⟩, ha⟩; exact ⟨q, h0, hP, a, ha⟩
  rw [this]
  refine MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun a => ?_
  exact (MeasurableSet.const _).inter (measurableSet_le (by fun_prop) measurable_const)

/-- CONDITIONAL ON `VaughanThm31`: `Lemma1On` holds on every set `mi` off the major arcs. -/
theorem lemma1On_of_vaughan (hV : VaughanThm31) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ X1 X P : ℝ, 2 ≤ X1 → X1 ≤ X → 3 ≤ X → 1 ≤ P → P ≤ X →
      ∀ mi : Set ℝ, mi ⊆ (majorArcs P (X / P))ᶜ → Lemma1On A X1 X P mi := by
  obtain ⟨A, hA, h⟩ := lemma1_of_vaughan hV
  exact ⟨A, hA, fun X1 X P h2 h1 h3 hP hPX mi hmi β hβ => h X1 X P h2 h1 h3 hP hPX β (hmi hβ)⟩

/-- CONDITIONAL ON `VaughanThm31` only: (3.1) of P0054 at `P = X^{7/25}` on the minor arcs
`mi = [-1/2, 1/2] \ 𝔐`: `∑_{m < M} ‖R₂(m)‖² ≤ 8 A² X³ L^{10} / P`. -/
theorem minor31_of_vaughan (hV : VaughanThm31) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ X1 X : ℝ, 2 ≤ X1 → X1 ≤ X → 3 ≤ X → ∀ M : ℕ,
      ∑ m ∈ range M, ‖R2 (S X1 X)
          (Set.Icc (-(1 / 2)) (1 / 2) \ majorArcs (X ^ (7 / 25 : ℝ)) (X / X ^ (7 / 25 : ℝ)))
          m‖ ^ 2 ≤ 8 * A ^ 2 * X ^ 3 * Real.log X ^ 10 / X ^ (7 / 25 : ℝ) := by
  obtain ⟨A, hA, h⟩ := lemma1On_of_vaughan hV
  refine ⟨A, hA, fun X1 X h2 h1 h3 M => ?_⟩
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hP1 : 1 ≤ X ^ (7 / 25 : ℝ) := one_le_rpow hX1 (by norm_num)
  have hPX : X ^ (7 / 25 : ℝ) ≤ X := by
    calc X ^ (7 / 25 : ℝ) ≤ X ^ (1 : ℝ) := rpow_le_rpow_of_exponent_le hX1 (by norm_num)
      _ = X := rpow_one X
  refine minor31_of_lemma1 hA hX1 _
    (measurableSet_Icc.diff (measurableSet_majorArcs _ _))
    (h X1 X _ h2 h1 h3 hP1 hPX _ (fun β hβ => hβ.2)) M

/-! ### Vacuity tests -/

/-- Vacuity test: `1/q` with `P < q < Q` is off the major arcs, so the minor arc hypothesis
of Lemma 1 is met by actual points whenever `P + 1 < Q`. -/
theorem inv_notMem_majorArcs {P Q : ℝ} {q : ℕ} (hPq : P < q) (hqQ : (q : ℝ) < Q) :
    (1 / (q : ℝ)) ∉ majorArcs P Q := by
  rintro ⟨q', hq'0, hq'P, a, ha⟩
  have hq'r : (0 : ℝ) < q' := by exact_mod_cast hq'0
  have hq'q : (q' : ℝ) < q := lt_of_le_of_lt hq'P hPq
  have hqr : (0 : ℝ) < q := lt_trans hq'r hq'q
  have hne : (q' : ℤ) - a * q ≠ 0 := by
    intro h
    have h' : (q' : ℤ) = a * q := by linarith
    have ha1 : 1 ≤ a := by
      by_contra hc
      push Not at hc
      have : a * (q : ℤ) ≤ 0 := Int.mul_nonpos_of_nonpos_of_nonneg (by omega) (by positivity)
      omega
    have : (q : ℤ) ≤ q' := by nlinarith
    have : (q : ℝ) ≤ q' := by exact_mod_cast this
    linarith
  have h1 : (1 : ℝ) ≤ |(((q' : ℤ) - a * q : ℤ) : ℝ)| := by
    exact_mod_cast Int.one_le_abs hne
  have e1 : 1 / (q : ℝ) - a / q' = (((q' : ℤ) - a * q : ℤ) : ℝ) / (q * q') := by
    push_cast; field_simp
  rw [e1, abs_div, abs_of_pos (by positivity : (0 : ℝ) < q * q')] at ha
  have h2 : 1 / ((q : ℝ) * q') ≤ 1 / (q' * Q) := by
    calc 1 / ((q : ℝ) * q') ≤ |(((q' : ℤ) - a * q : ℤ) : ℝ)| / (q * q') :=
          div_le_div_of_nonneg_right h1 (by positivity)
      _ ≤ _ := ha
  rw [div_le_div_iff₀ (by positivity) (by nlinarith)] at h2
  nlinarith

/-- Vacuity test: the major arcs do not cover everything; at `P = 2`, `Q = 10`, the point
`1/3` is on the minor arcs `minorArcs 2 10`. -/
theorem minorArcs_nonempty : (1 / (3 : ℝ)) ∈ minorArcs 2 10 := by
  refine ⟨⟨by norm_num, by norm_num⟩, ?_⟩
  have := inv_notMem_majorArcs (P := 2) (Q := 10) (q := 3) (by norm_num) (by norm_num)
  simpa using this

end LeanLab.Pintz2021.Lemma1U1369

#print axioms LeanLab.Pintz2021.Lemma1U1369.dirichlet_minor
#print axioms LeanLab.Pintz2021.Lemma1U1369.sum_trunc
#print axioms LeanLab.Pintz2021.Lemma1U1369.S_eq
#print axioms LeanLab.Pintz2021.Lemma1U1369.norm_Uθ_sub_le
#print axioms LeanLab.Pintz2021.Lemma1U1369.norm_Uθ_le
#print axioms LeanLab.Pintz2021.Lemma1U1369.vaughan_term_le
#print axioms LeanLab.Pintz2021.Lemma1U1369.lemma1_of_vaughan
#print axioms LeanLab.Pintz2021.Lemma1U1369.measurableSet_majorArcs
#print axioms LeanLab.Pintz2021.Lemma1U1369.lemma1On_of_vaughan
#print axioms LeanLab.Pintz2021.Lemma1U1369.minor31_of_vaughan
#print axioms LeanLab.Pintz2021.Lemma1U1369.inv_notMem_majorArcs
#print axioms LeanLab.Pintz2021.Lemma1U1369.minorArcs_nonempty
