/-
Unit U-1529, run 20261025T2003Z-426, DECOMPOSE of the GRH inputs of P0011,
Deshouillers, Effinger, te Riele, Zinoviev 1997, ERA-AMS 3, 99-104.

File c: the assembly of P0011's GRH input on page 101 from the leaves of Decomp1529a and
Decomp1529b, and the leaves of the major-arc side of the GRH circle method (the progression
form of the GRH bound, characters and Gauss sums, the weighted sum `S(α)` of page 100).

Assemblies, zero sorry in their own proofs:
* `psi_uniform_of_GRH`: GRH gives `|ψ(x) - x| ≤ 2.6 · 10^12` on `[10^11, 10^20]`, with
  `T = 10^5 √x` in `explicit_formula_zeta` and `zero_recip_sum`;
* `theta_uniform_of_GRH`: `|θ(x) - x| ≤ 2.62 · 10^12` there, by `psi_sub_theta_upper`;
* `derz_lemma_of_GRH_decomp`: P0011's intermediate lemma with gap `6 · 10^12` in place of the
  printed `1.615 · 10^12`, by `gap_of_theta`;
* `derz_main_of_decomp`: GRH implies ternary Goldbach, CONDITIONAL ON Zinoviev's `10^20` theorem
  and the `10^13` even check as hypotheses, and on the leaves `zetaZeros_finite`,
  `zero_recip_sum`, `explicit_formula_zeta`. No Schoenfeld input.
The printed constant `1.615 · 10^12` needs Schoenfeld's sharp `1/(8π)`; the generous leaf
constants give `6 · 10^12`, still below the `10^13` even check, so the main theorem stands.

Source when the original is not at hand: Davenport, Multiplicative Number Theory, 3rd ed.,
ch. 4, 9, 20, 25, 26. P0011 page 100 for `S(α)`.
AI-written Lean code, Claude, 2026-10-25. Checked only by the Lean kernel.
Ternary Goldbach is Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.DERZ1997.Decomp1529b
import LeanLab.DERZ1997.LemmaPsi
import LeanLab.PerelliPintz1992.Decomp1519

namespace LeanLab.DERZ1997.Decomp1529c
open Complex LeanLab.DERZ1997 LeanLab.DERZ1997.Decomp1529a LeanLab.DERZ1997.Decomp1529b
open Chebyshev

/-! ### Assembly: P0011's page 101 input from the leaves -/

/-- **GRH bound for `ψ` on P0011's range**: `|ψ(x) - x| ≤ 2.6 · 10^12` for
`10^11 ≤ x ≤ 10^20`. PROVED from the leaves with `T = 10^5 √x`, zero sorry in this proof;
CONDITIONAL ON GRH (through `zeta_strip_of_GRH`) and the leaves `zetaZeros_finite`,
`zero_recip_sum`, `explicit_formula_zeta`. -/
theorem psi_uniform_of_GRH (hG : GRH) (x : ℝ) (h1 : 10 ^ 11 ≤ x) (h2 : x ≤ 10 ^ 20) :
    |ψ x - x| ≤ 26 * 10 ^ 11 := by
  have hx0 : 0 < x := by linarith
  have hs := sqrt_le_1e10 h2
  have hsx : √x * √x = x := Real.mul_self_sqrt hx0.le
  have hs1 : (3 : ℝ) * 10 ^ 5 ≤ √x := by
    rw [Real.le_sqrt (by norm_num) hx0.le]; nlinarith
  set T : ℝ := 10 ^ 5 * √x with hTdef
  have hT15 : 15 ≤ T := by nlinarith
  have hTx : T ≤ x := by nlinarith
  have hfin := zetaZeros_finite T
  have hE := explicit_formula_zeta (by linarith) (by linarith) hTx hfin
  have hZ := zero_recip_sum hT15 hfin
  set S := ∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℂ) * (x : ℂ) ^ ρ / ρ with hSdef
  set R := ∑ ρ ∈ hfin.toFinset, (zetaMult ρ : ℝ) / ‖ρ‖ with hRdef
  have hS : ‖S‖ ≤ √x * R := by
    refine (norm_sum_le _ _).trans ?_
    rw [hRdef, Finset.mul_sum]
    refine le_of_eq (Finset.sum_congr rfl fun ρ hρ => ?_)
    exact norm_zero_term hx0
      (re_eq_half_of_GRH hG ((Set.Finite.mem_toFinset hfin).mp hρ)) _
  -- logarithms
  have hlx : Real.log x ≤ 46.0522 := (Real.log_le_log hx0 h2).trans log_1e20_lt.le
  have hlx0 : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  have hlogT : Real.log T = 5 * Real.log 10 + Real.log x / 2 := by
    rw [hTdef, Real.log_mul (by norm_num) (by positivity), Real.log_pow, Real.log_sqrt hx0.le]
    push_cast; ring
  have hl10 := log_ten_lt'
  have hlT : Real.log T ≤ 34.54 := by rw [hlogT]; linarith
  have hlT0 : 0 ≤ Real.log T := Real.log_nonneg (by linarith)
  have hlT2 : Real.log T ^ 2 ≤ 1193.1 := by nlinarith
  have hlx2 : Real.log x ^ 2 ≤ 2120.81 := by nlinarith
  have hR : R ≤ 238.62 := by rw [hRdef]; nlinarith
  have hSb : ‖S‖ ≤ 238.62 * 10 ^ 10 := by
    have hR0 : 0 ≤ R := Finset.sum_nonneg fun ρ _ => by positivity
    have : √x * R ≤ 10 ^ 10 * 238.62 := mul_le_mul hs hR hR0 (by norm_num)
    linarith
  have hxT : x * Real.log x ^ 2 / T ≤ 2.12081 * 10 ^ 8 := by
    have hT0 : 0 < T := by linarith
    rw [div_le_iff₀ hT0, hTdef]
    have : x * Real.log x ^ 2 ≤ 10 ^ 10 * √x * 2120.81 := by
      have hx' : x ≤ 10 ^ 10 * √x := by nlinarith
      have := mul_le_mul hx' hlx2 (sq_nonneg _) (by positivity)
      linarith
    nlinarith
  have hEb : ‖(ψ x : ℂ) - x + S‖ ≤ 1000 * (2.12081 * 10 ^ 8 + 46.0522) := by
    refine hE.trans ?_
    have := add_le_add hxT hlx
    linarith
  have key : ‖((ψ x - x : ℝ) : ℂ)‖ ≤ ‖(ψ x : ℂ) - x + S‖ + ‖S‖ := by
    have := norm_sub_le ((ψ x : ℂ) - x + S) S
    push_cast
    simpa using this
  rw [Complex.norm_real, Real.norm_eq_abs] at key
  linarith

/-- `|θ(x) - x| ≤ 2.62 · 10^12` for `10^11 ≤ x ≤ 10^20` under GRH, from
`psi_uniform_of_GRH` and `ψ - θ ≤ θ(√x) + 4.2 · 10^8`. Same conditions as
`psi_uniform_of_GRH`. -/
theorem theta_uniform_of_GRH (hG : GRH) (x : ℝ) (h1 : 10 ^ 11 ≤ x) (h2 : x ≤ 10 ^ 20) :
    |θ x - x| ≤ 262 * 10 ^ 10 := by
  have hψ := psi_uniform_of_GRH hG x h1 h2
  have hup := psi_sub_theta_upper (by linarith : (2 : ℝ) ≤ x) h2
  have hle := theta_le_psi x
  have hs := sqrt_le_1e10 h2
  have hθs := theta_le_log4_mul_x (Real.sqrt_nonneg x)
  have h4 := log_four_lt
  have hθs' : θ (√x) ≤ 1.3863 * 10 ^ 10 := by
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    nlinarith [Real.sqrt_nonneg x]
  rw [abs_le] at hψ ⊢
  constructor <;> linarith [hψ.1, hψ.2]

/-- **P0011 intermediate lemma with gap `6 · 10^12`** under GRH: for `6 ≤ n ≤ 10^20` there is a
prime `p` with `4 ≤ n - p ≤ 6 · 10^12`. The printed lemma has `1.615 · 10^12`. Same conditions
as `psi_uniform_of_GRH`. -/
theorem derz_lemma_of_GRH_decomp (hG : GRH) :
    ∀ n : ℕ, 6 ≤ n → n ≤ 10 ^ 20 → ∃ p : ℕ, p.Prime ∧ 4 ≤ n - p ∧ n - p ≤ 6 * 10 ^ 12 :=
  gap_of_theta (10 ^ 11) (262 * 10 ^ 10) (6 * 10 ^ 12) le_rfl
    (fun x h1 h2 => theta_uniform_of_GRH hG x h1 h2)
    (by have := log_1e20_lt; norm_num; linarith) (by norm_num)

/-- **P0011 main theorem through the decomposition**: GRH implies every odd `n ≥ 7` is a sum of
three primes, CONDITIONAL ON Zinoviev's theorem above `10^20` and the `10^13` even check as
hypotheses, and on the leaves `zetaZeros_finite`, `zero_recip_sum`, `explicit_formula_zeta`
in place of Schoenfeld (6.1). Zero sorry in this proof. -/
theorem derz_main_of_decomp
    (hZ : GRH → ∀ n : ℕ, Odd n → 10 ^ 20 < n → IsTernarySum n)
    (hD : EvenGoldbachUpTo (10 ^ 13)) : GRH → TernaryGoldbach :=
  derz_main_of_gap (6 * 10 ^ 12) (by norm_num) hZ derz_lemma_of_GRH_decomp hD

/-! ### Leaves: the major-arc side under GRH -/

/-- The weighted exponential sum of P0011 page 100,
`S(α) = ∑_{n ≥ 1} Λ(n) e^{-2πiαn} e^{-n/N}`. -/
noncomputable def SW (N α : ℝ) : ℂ :=
  ∑' n : ℕ, (ArithmeticFunction.vonMangoldt n : ℂ) *
    Complex.exp (-(2 * Real.pi * I * α * n)) * (Real.exp (-n / N) : ℂ)

/-- LEAF. Orthogonality for progressions: for a unit `a` mod `q`,
`ψ(x; q, a) = (1/φ(q)) ∑_χ χ(a⁻¹) ψ(x, χ)`. From Mathlib's
`DirichletCharacter.sum_char_inv_mul_char_eq`. Davenport ch. 4 and ch. 20, p. 121.
Unit U-1529. -/
theorem psi_progression_eq {q : ℕ} [NeZero q] {a : ZMod q} (ha : IsUnit a) (x : ℝ) :
    (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => ((n : ℕ) : ZMod q) = a),
        (ArithmeticFunction.vonMangoldt n : ℂ)) =
      (1 / (q.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * psiChi χ x := by
  unfold psiChi
  have h_inner : ∀ χ : DirichletCharacter ℂ q,
    χ a⁻¹ * ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ) =
    ∑ n ∈ Finset.Ioc 0 ⌊x⌋₊, χ a⁻¹ * (χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) := by
    intro χ
    rw [Finset.mul_sum]
  simp_rw [h_inner]
  rw [Finset.sum_comm]
  have h_sum : ∀ n : ℕ,
      ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) =
      (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ (n : ZMod q)) * (ArithmeticFunction.vonMangoldt n : ℂ) := by
    intro n
    have : (fun χ : DirichletCharacter ℂ q => χ a⁻¹ * (χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))) = (fun χ : DirichletCharacter ℂ q => (χ a⁻¹ * χ (n : ZMod q)) * (ArithmeticFunction.vonMangoldt n : ℂ)) := by
      ext χ
      rw [mul_assoc]
    rw [this, Finset.sum_mul]
  simp_rw [h_sum]
  have h_char_sum : ∀ n : ℕ, ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * χ (n : ZMod q) = if a = (n : ZMod q) then (q.totient : ℂ) else 0 := by
    intro n
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ ha]
  simp_rw [h_char_sum]
  have h_filter : ∀ n ∈ Finset.Ioc 0 ⌊x⌋₊,
      (if a = (n : ZMod q) then (q.totient : ℂ) else 0) * (ArithmeticFunction.vonMangoldt n : ℂ) =
      if ((n : ℕ) : ZMod q) = a then (q.totient : ℂ) * (ArithmeticFunction.vonMangoldt n : ℂ) else 0 := by
    intro n _
    split_ifs with h1 h2 h3
    · rfl
    · rw [eq_comm] at h1; contradiction
    · rw [eq_comm] at h3; contradiction
    · exact zero_mul _
  rw [Finset.sum_congr rfl h_filter]
  rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
  have h_filter_sum : (∑ x_1 ∈ Finset.filter (fun x_1 => ((x_1 : ℕ) : ZMod q) = a) (Finset.Ioc 0 ⌊x⌋₊), (q.totient : ℂ) * (ArithmeticFunction.vonMangoldt x_1 : ℂ)) =
      (q.totient : ℂ) * ∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => ((n : ℕ) : ZMod q) = a), (ArithmeticFunction.vonMangoldt n : ℂ) := by
    rw [Finset.mul_sum]
  rw [h_filter_sum]
  rw [← mul_assoc]
  have h_div : (1 / (q.totient : ℂ)) * (q.totient : ℂ) = 1 := by
    rw [one_div, inv_mul_cancel₀]
    have h_totient_pos : 0 < q.totient := Nat.totient_pos.mpr (NeZero.pos q)
    exact_mod_cast ne_of_gt h_totient_pos
  rw [h_div, one_mul]

/-- LEAF. GRH bound in progressions: under GRH there is an absolute `c` with
`|ψ(x; q, a) - x/φ(q)| ≤ c √x log²(qx)` for every `q`, every unit `a` mod `q`, and `x ≥ 2`.
From `psi_progression_eq` and `psiChi_bound_of_GRH`, with `|χ(a⁻¹)| ≤ 1` and `φ(q)`
characters. Davenport ch. 20, (14), p. 125. Unit U-1529. -/
theorem psi_progression_GRH : GRH → ∃ c : ℝ, ∀ (q : ℕ) [NeZero q] (a : ZMod q), IsUnit a →
    ∀ x : ℝ, 2 ≤ x →
      |(∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => ((n : ℕ) : ZMod q) = a),
          ArithmeticFunction.vonMangoldt n) - x / q.totient| ≤
        c * √x * Real.log (q * x) ^ 2 := by
  intro hG
  obtain ⟨c, hc⟩ := psiChi_bound_of_GRH hG
  use c
  intro q hq a ha x hx
  have h_eq := psi_progression_eq ha x
  have h_abs_eq : (∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => ((n : ℕ) : ZMod q) = a),
          (ArithmeticFunction.vonMangoldt n : ℂ)) - (x : ℂ) / (q.totient : ℂ) =
      (1 / (q.totient : ℂ)) * ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (psiChi χ x - if χ = 1 then (x : ℂ) else 0) := by
    rw [h_eq]
    have h_sum : (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (psiChi χ x - if χ = 1 then (x : ℂ) else 0)) =
        (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * psiChi χ x) - ∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (if χ = 1 then (x : ℂ) else 0) := by
      have : ∀ χ : DirichletCharacter ℂ q, χ a⁻¹ * (psiChi χ x - if χ = 1 then (x : ℂ) else 0) = χ a⁻¹ * psiChi χ x - χ a⁻¹ * (if χ = 1 then (x : ℂ) else 0) := fun χ => mul_sub _ _ _
      rw [Finset.sum_congr rfl (fun χ _ => this χ)]
      rw [Finset.sum_sub_distrib]
    rw [h_sum, mul_sub]
    congr 1
    have h_trivial_eval : (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (if χ = 1 then (x : ℂ) else 0)) = (x : ℂ) := by
      have h_eval : ∀ χ : DirichletCharacter ℂ q, χ a⁻¹ * (if χ = 1 then (x : ℂ) else 0) = if χ = 1 then (x : ℂ) else 0 := by
        intro χ
        split_ifs with h
        · have ⟨u, hu⟩ := ha
          have h_inv : a⁻¹ = ↑u⁻¹ := by
            apply ZMod.inv_eq_of_mul_eq_one
            rw [← hu]
            exact Units.mul_inv u
          rw [h, h_inv, MulChar.one_apply (Units.isUnit u⁻¹), one_mul]
        · rw [mul_zero]
      rw [Finset.sum_congr rfl (fun χ _ => h_eval χ)]
      rw [Finset.sum_ite, Finset.sum_const_zero, add_zero]
      have h_filter : (Finset.filter (fun χ : DirichletCharacter ℂ q => χ = 1) Finset.univ) = {1} := by
        ext χ
        simp
      rw [h_filter, Finset.sum_singleton]
    rw [h_trivial_eval]
    rw [div_eq_mul_one_div]
    ring
  have h_bound : ‖(∑ n ∈ (Finset.Ioc 0 ⌊x⌋₊).filter (fun n : ℕ => ((n : ℕ) : ZMod q) = a),
          (ArithmeticFunction.vonMangoldt n : ℂ)) - (x : ℂ) / (q.totient : ℂ)‖ ≤
        c * √x * Real.log (q * x) ^ 2 := by
    rw [h_abs_eq]
    have h_norm := norm_mul (1 / (q.totient : ℂ)) (∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (psiChi χ x - if χ = 1 then (x : ℂ) else 0))
    rw [h_norm]
    have h_norm_div : ‖(1 / (q.totient : ℂ) : ℂ)‖ = 1 / (q.totient : ℝ) := by
      rw [norm_div, norm_one, norm_natCast]
    rw [h_norm_div]
    have h_sum_le : ‖∑ χ : DirichletCharacter ℂ q, χ a⁻¹ * (psiChi χ x - if χ = 1 then (x : ℂ) else 0)‖ ≤
        (q.totient : ℝ) * (c * √x * Real.log (q * x) ^ 2) := by
      have h_le := norm_sum_le Finset.univ (fun χ : DirichletCharacter ℂ q => χ a⁻¹ * (psiChi χ x - if χ = 1 then (x : ℂ) else 0))
      have h_le2 : ∑ x_1 ∈ Finset.univ, ‖x_1 a⁻¹ * (psiChi x_1 x - if x_1 = 1 then ↑x else 0)‖ ≤
          ∑ x_1 : DirichletCharacter ℂ q, (c * √x * Real.log (q * x) ^ 2) := by
        apply Finset.sum_le_sum
        intro χ _
        rw [norm_mul]
        have h_char_norm : ‖χ a⁻¹‖ ≤ 1 := DirichletCharacter.norm_le_one χ a⁻¹
        have h_bound_χ := hc q χ x hx
        have h_mul_le : ‖χ a⁻¹‖ * ‖psiChi χ x - if χ = 1 then ↑x else 0‖ ≤ 1 * ‖psiChi χ x - if χ = 1 then ↑x else 0‖ := by
          apply mul_le_mul_of_nonneg_right h_char_norm (norm_nonneg _)
        rw [one_mul] at h_mul_le
        exact le_trans h_mul_le h_bound_χ
      have h_card : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
        have h := DirichletCharacter.sum_char_inv_mul_char_eq ℂ (isUnit_one : IsUnit (1 : ZMod q)) (1 : ZMod q)
        have h1 : (1 : ZMod q)⁻¹ = 1 := by
          apply ZMod.inv_eq_of_mul_eq_one
          rw [mul_one]
        rw [h1] at h
        have h2 : ∀ χ : DirichletCharacter ℂ q, χ 1 * χ 1 = 1 := by
          intro χ
          have : χ 1 = 1 := map_one χ
          rw [this, mul_one]
        rw [Finset.sum_congr rfl (fun χ _ => h2 χ)] at h
        have h3 : (∑ χ : DirichletCharacter ℂ q, (1 : ℂ)) = (Finset.univ : Finset (DirichletCharacter ℂ q)).card := by
          simp
        rw [h3] at h
        split_ifs at h with h_if
        · exact_mod_cast h
        · contradiction
      have h_sum_const : (∑ x_1 : DirichletCharacter ℂ q, c * √x * Real.log (q * x) ^ 2) = (q.totient : ℝ) * (c * √x * Real.log (q * x) ^ 2) := by
        rw [Finset.sum_const, h_card]
        exact nsmul_eq_mul (q.totient) (c * √x * Real.log (q * x) ^ 2)
      rw [← h_sum_const]
      exact le_trans h_le h_le2
    have h_totient_pos : 0 < (q.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
    rw [one_div, ← div_eq_inv_mul]
    have h_rw : c * √x * Real.log (↑q * x) ^ 2 = (q.totient : ℝ) * (c * √x * Real.log (q * x) ^ 2) / (q.totient : ℝ) := by
      have : (q.totient : ℝ) * (c * √x * Real.log (q * x) ^ 2) / (q.totient : ℝ) = (c * √x * Real.log (q * x) ^ 2) * (q.totient : ℝ) / (q.totient : ℝ) := by rw [mul_comm]
      rw [this]
      rw [mul_div_cancel_right₀ _ (ne_of_gt h_totient_pos)]
    rw [h_rw]
    exact div_le_div_of_nonneg_right h_sum_le (le_of_lt h_totient_pos)
  have h_bound_r : ‖(∑ n ∈ Finset.filter (fun n => ((n : ℕ) : ZMod q) = a) (Finset.Ioc 0 ⌊x⌋₊), (ArithmeticFunction.vonMangoldt n : ℂ)) - ↑x / ↑q.totient‖ = |(∑ n ∈ Finset.filter (fun n => ((n : ℕ) : ZMod q) = a) (Finset.Ioc 0 ⌊x⌋₊), ArithmeticFunction.vonMangoldt n) - x / ↑q.totient| := by
    have h_sum_cast : (∑ n ∈ Finset.filter (fun n => ((n : ℕ) : ZMod q) = a) (Finset.Ioc 0 ⌊x⌋₊), (ArithmeticFunction.vonMangoldt n : ℂ)) =
        ↑(∑ n ∈ Finset.filter (fun n => ((n : ℕ) : ZMod q) = a) (Finset.Ioc 0 ⌊x⌋₊), (ArithmeticFunction.vonMangoldt n : ℝ)) := by
      push_cast
      rfl
    have h_div_cast : (↑x : ℂ) / (q.totient : ℂ) = ↑(x / q.totient) := by
      push_cast
      rfl
    rw [h_sum_cast, h_div_cast]
    have h_sub_cast : ↑(∑ n ∈ Finset.filter (fun n => ((n : ℕ) : ZMod q) = a) (Finset.Ioc 0 ⌊x⌋₊), (ArithmeticFunction.vonMangoldt n : ℝ)) - ↑(x / q.totient) = (↑((∑ n ∈ Finset.filter (fun n => ((n : ℕ) : ZMod q) = a) (Finset.Ioc 0 ⌊x⌋₊), (ArithmeticFunction.vonMangoldt n : ℝ)) - (x / q.totient)) : ℂ) := by
      push_cast
      rfl
    rw [h_sub_cast]
    exact Complex.norm_real _
  rw [← h_bound_r]
  exact h_bound


namespace L1Num

open Real

set_option maxHeartbeats 1000000

/-- `log (1+x) ≤ 2 √x` for `x ≥ 0`. -/
lemma log_one_add_le_two_sqrt {x : ℝ} (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ 2 * Real.sqrt x := by
  have hx1 : (0 : ℝ) < 1 + x := by linarith
  rw [Real.log_le_iff_le_exp hx1]
  have ht : 0 ≤ Real.sqrt x := Real.sqrt_nonneg x
  have hsq : Real.sqrt x * Real.sqrt x = x := Real.mul_self_sqrt hx
  have hexp : Real.exp (2 * Real.sqrt x) = (Real.exp (Real.sqrt x)) ^ 2 := by
    rw [show 2 * Real.sqrt x = Real.sqrt x + Real.sqrt x by ring, Real.exp_add]
    ring
  rw [hexp]
  have h1 : 1 + Real.sqrt x ≤ Real.exp (Real.sqrt x) := by
    have := Real.add_one_le_exp (Real.sqrt x); linarith
  have h2 : (1 + Real.sqrt x) ^ 2 ≤ (Real.exp (Real.sqrt x)) ^ 2 := by
    nlinarith [Real.exp_pos (Real.sqrt x)]
  have h3 : 1 + x ≤ (1 + Real.sqrt x) ^ 2 := by nlinarith
  linarith

/-- `log (1+x)^2 ≤ 4x` for `x ≥ 0`. -/
lemma log_one_add_sq_le {x : ℝ} (hx : 0 ≤ x) : Real.log (1 + x) ^ 2 ≤ 4 * x := by
  have h := log_one_add_le_two_sqrt hx
  have h0 : 0 ≤ Real.log (1 + x) := Real.log_nonneg (by linarith)
  have h1 : 0 ≤ 2 * Real.sqrt x := by positivity
  have h2 : (2 * Real.sqrt x) ^ 2 = 4 * x := by
    have hs := Real.sq_sqrt hx
    nlinarith [Real.sqrt_nonneg x]
  nlinarith

/-- `exp (-x) ≤ 1/(1+x)` for `x ≥ 0`. -/
lemma exp_neg_le_inv_one_add {x : ℝ} (hx : 0 ≤ x) :
    Real.exp (-x) ≤ 1 / (1 + x) := by
  have hx1 : (0 : ℝ) < 1 + x := by linarith
  have hlog : Real.log (1 + x) ≤ x := by
    have h := Real.log_le_sub_one_of_pos hx1
    linarith
  have h2 : 1 + x ≤ Real.exp x := by
    have h := Real.exp_le_exp.mpr hlog
    rwa [Real.exp_log hx1] at h
  have hmul : (1 + x) * Real.exp (-x) ≤ 1 := by
    have h := mul_le_mul_of_nonneg_right h2 (le_of_lt (Real.exp_pos (-x)))
    have h1 : Real.exp x * Real.exp (-x) = 1 := by
      rw [← Real.exp_add, add_neg_cancel, Real.exp_zero]
    linarith
  rw [le_div_iff₀ hx1]
  linarith

/-- `1 - exp(-x) ≥ x/2` for `0 ≤ x ≤ 1`. -/
lemma half_le_one_sub_exp_neg {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    x / 2 ≤ 1 - Real.exp (-x) := by
  have h := exp_neg_le_inv_one_add hx0
  have hx : (0 : ℝ) < 1 + x := by linarith
  have h2 : 1 / (1 + x) ≤ 1 - x / 2 := by
    rw [div_le_iff₀ hx]
    nlinarith
  linarith

/-- `√(n+1) exp(-n/(2N)) ≤ √N` for `N ≥ 1`. -/
lemma sqrt_succ_mul_exp_half_le {N : ℝ} (hN : 1 ≤ N) (n : ℕ) :
    Real.sqrt ((n : ℝ) + 1) * Real.exp (-(n : ℝ) / (2 * N)) ≤ Real.sqrt N := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hs : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hexp : Real.exp (-(n : ℝ) / (2 * N)) = Real.sqrt (Real.exp (-(n : ℝ) / N)) := by
    rw [← Real.exp_half]
    congr 1
    field_simp
  rw [hexp, ← Real.sqrt_mul (le_of_lt hs)]
  apply Real.sqrt_le_sqrt
  have hlog : Real.log (((n : ℝ) + 1) / N) ≤ (n : ℝ) / N := by
    have h1 : Real.log (((n : ℝ) + 1) / N) ≤ ((n : ℝ) + 1) / N - 1 :=
      Real.log_le_sub_one_of_pos (by positivity)
    have h2 : ((n : ℝ) + 1) / N ≤ (n : ℝ) / N + 1 := by
      rw [div_le_iff₀ hN0]
      field_simp
      linarith
    linarith
  have hkey : Real.log (((n : ℝ) + 1) * Real.exp (-(n : ℝ) / N)) ≤ Real.log N := by
    rw [Real.log_mul (ne_of_gt hs) (ne_of_gt (Real.exp_pos _)), Real.log_exp]
    have h3 : Real.log ((n : ℝ) + 1) = Real.log (((n : ℝ) + 1) / N) + Real.log N := by
      rw [Real.log_div (ne_of_gt hs) hN0.ne']
      ring
    have h4 : -(n : ℝ) / N = -((n : ℝ) / N) := by ring
    rw [h4]
    linarith
  exact (Real.log_le_log_iff (by positivity) hN0).mp hkey

/-- `1 - exp(-1/(2N)) ≥ 1/(4N)` for `N ≥ 1`. -/
lemma one_sub_exp_ge {N : ℝ} (hN : 1 ≤ N) :
    1 / (4 * N) ≤ 1 - Real.exp (-(1 / (2 * N))) := by
  have hx0 : 0 ≤ 1 / (2 * N) := by positivity
  have hx1 : 1 / (2 * N) ≤ 1 := by
    rw [div_le_one (by linarith : (0:ℝ) < 2 * N)]
    linarith
  have h := half_le_one_sub_exp_neg hx0 hx1
  have heq : (1 / (2 * N)) / 2 = 1 / (4 * N) := by
    field_simp
    ring
  linarith

lemma exp_neg_half_lt_one {N : ℝ} (hN : 1 ≤ N) :
    ‖Real.exp (-(1 / (2 * N)))‖ < 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (le_of_lt (Real.exp_pos _)), Real.exp_lt_one_iff]
  have : (0 : ℝ) < 1 / (2 * N) := by positivity
  linarith

/-- Geometric sum bound. -/
lemma tsum_pow_le {N : ℝ} (hN : 1 ≤ N) :
    (∑' n : ℕ, Real.exp (-(1 / (2 * N))) ^ n) ≤ 4 * N := by
  set r : ℝ := Real.exp (-(1 / (2 * N))) with hr
  have hr1 : ‖r‖ < 1 := exp_neg_half_lt_one hN
  have hge : 1 / (4 * N) ≤ 1 - r := by
    rw [hr]; exact one_sub_exp_ge hN
  have hpos : (0 : ℝ) < 1 / (4 * N) := by positivity
  have hd : (0 : ℝ) < 1 - r := by linarith
  rw [tsum_geometric_of_norm_lt_one hr1, ← one_div]
  calc 1 / (1 - r) ≤ 1 / (1 / (4 * N)) := one_div_le_one_div_of_le hpos hge
    _ = 4 * N := by field_simp

/-- First-moment geometric sum bound. -/
lemma tsum_n_mul_le {N : ℝ} (hN : 1 ≤ N) :
    (∑' n : ℕ, (n : ℝ) * Real.exp (-(1 / (2 * N))) ^ n) ≤ 16 * N ^ 2 := by
  set r : ℝ := Real.exp (-(1 / (2 * N))) with hr
  have hr0 : 0 ≤ r := le_of_lt (Real.exp_pos _)
  have hr1 : ‖r‖ < 1 := exp_neg_half_lt_one hN
  have hrle : r ≤ 1 := by
    rw [hr]
    calc Real.exp (-(1 / (2 * N))) ≤ Real.exp 0 := by
          apply Real.exp_le_exp.mpr
          have : (0 : ℝ) < 1 / (2 * N) := by positivity
          linarith
      _ = 1 := Real.exp_zero
  have hge : 1 / (4 * N) ≤ 1 - r := by
    rw [hr]; exact one_sub_exp_ge hN
  have hpos : (0 : ℝ) < 1 / (4 * N) := by positivity
  have hd : (0 : ℝ) < 1 - r := by linarith
  rw [tsum_coe_mul_geometric_of_norm_lt_one hr1]
  have hstep1 : r / (1 - r) ^ 2 ≤ 1 / (1 - r) ^ 2 := by
    apply div_le_div_of_nonneg_right hrle
    positivity
  have hsq : (1 / (4 * N)) ^ 2 ≤ (1 - r) ^ 2 := by
    apply pow_le_pow_left₀ (le_of_lt hpos) hge
  have hstep2 : 1 / (1 - r) ^ 2 ≤ 1 / (1 / (4 * N)) ^ 2 :=
    one_div_le_one_div_of_le (by positivity) hsq
  have hfin : 1 / (1 / (4 * N)) ^ 2 = 16 * N ^ 2 := by
    field_simp
    ring
  linarith

/-- The final numeric step of the assembly. -/
lemma final_bound {M X s : ℝ} (hM : 0 ≤ M) (hX : 0 ≤ X)
    (h1 : 128 * M * s ≤ 268.8 * M * X) (h2 : 1 ≤ 1.5 * X) :
    1 + (8 * M * X + 128 * M * s) ≤ (300 * M + 3) * X := by
  have hpos : (0 : ℝ) ≤ (23.2 * M + 1.5) * X := by
    apply mul_nonneg _ hX
    linarith
  linarith [h1, h2, hpos]


/-- Summability of the weighted square-root sum. -/
lemma main_sum_summable {N : ℝ} (hN : 1 ≤ N) {q : ℕ} (hq : 1 ≤ q) :
    Summable (fun n : ℕ => Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 *
      Real.exp (-(n : ℝ) / N)) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  set r : ℝ := Real.exp (-(1 / (2 * N))) with hr
  set L : ℝ := Real.log ((q : ℝ) * N) with hL
  have hL0 : 0 ≤ L := by rw [hL]; exact Real.log_nonneg (by nlinarith)
  have hr1 : ‖r‖ < 1 := exp_neg_half_lt_one hN
  have hrn : ∀ n : ℕ, Real.exp (-(n : ℝ) / (2 * N)) = r ^ n := by
    intro n
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hsumm1 : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_norm_lt_one hr1
  have hsumm2 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr1).summable
  have hterm : ∀ n : ℕ,
      Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 *
        Real.exp (-(n : ℝ) / N) ≤
      (2 * L ^ 2 + 8 * ((n : ℝ) / N)) * (Real.sqrt N * r ^ n) := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hs1 : Real.sqrt ((n : ℝ) + 1) * Real.exp (-(n : ℝ) / (2 * N)) ≤ Real.sqrt N :=
      sqrt_succ_mul_exp_half_le hN n
    have hpos2 : (0 : ℝ) ≤ Real.exp (-(n : ℝ) / (2 * N)) := le_of_lt (Real.exp_pos _)
    have hA0 : 0 ≤ Real.log ((q : ℝ) * ((n : ℝ) + 1)) :=
      Real.log_nonneg (by nlinarith)
    have hnN : (0 : ℝ) ≤ (n : ℝ) / N := by positivity
    have hB0 : 0 ≤ Real.log (1 + (n : ℝ) / N) := Real.log_nonneg (by linarith)
    have hlog : Real.log ((q : ℝ) * ((n : ℝ) + 1)) ≤ L + Real.log (1 + (n : ℝ) / N) := by
      have h1 : (q : ℝ) * ((n : ℝ) + 1) = ((q : ℝ) * N) * (((n : ℝ) + 1) / N) := by
        field_simp
      rw [h1, Real.log_mul (by positivity) (by positivity), hL]
      have h2 : Real.log (((n : ℝ) + 1) / N) ≤ Real.log (1 + (n : ℝ) / N) := by
        apply Real.log_le_log (by positivity)
        rw [div_le_iff₀ hN0]
        have h3 : (1 + (n : ℝ) / N) * N = N + (n : ℝ) := by
          field_simp
        linarith [h3]
      linarith
    have hBsq := log_one_add_sq_le (show (0 : ℝ) ≤ (n : ℝ) / N by positivity)
    have hL2 : Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 ≤ 2 * L ^ 2 + 8 * ((n : ℝ) / N) := by
      have h5 : 0 ≤ L + Real.log (1 + (n : ℝ) / N) := by linarith
      have h6 : Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 ≤
          (L + Real.log (1 + (n : ℝ) / N)) ^ 2 := by nlinarith
      have h7 : (L + Real.log (1 + (n : ℝ) / N)) ^ 2 ≤
          2 * L ^ 2 + 2 * Real.log (1 + (n : ℝ) / N) ^ 2 := by
        nlinarith [sq_nonneg (L - Real.log (1 + (n : ℝ) / N))]
      linarith [h6, h7, hBsq]
    have hs2 : Real.exp (-(n : ℝ) / N) =
        Real.exp (-(n : ℝ) / (2 * N)) * Real.exp (-(n : ℝ) / (2 * N)) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    have h2 : Real.exp (-(n : ℝ) / (2 * N)) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 ≤
        r ^ n * (2 * L ^ 2 + 8 * ((n : ℝ) / N)) := by
      rw [← hrn n]
      exact mul_le_mul_of_nonneg_left hL2 hpos2
    calc Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 *
          Real.exp (-(n : ℝ) / N)
        = (Real.sqrt ((n : ℝ) + 1) * Real.exp (-(n : ℝ) / (2 * N))) *
            (Real.exp (-(n : ℝ) / (2 * N)) *
              Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2) := by
          rw [hs2]; ring
      _ ≤ Real.sqrt N * (r ^ n * (2 * L ^ 2 + 8 * ((n : ℝ) / N))) :=
          mul_le_mul hs1 h2 (mul_nonneg hpos2 (sq_nonneg _)) (Real.sqrt_nonneg N)
      _ = (2 * L ^ 2 + 8 * ((n : ℝ) / N)) * (Real.sqrt N * r ^ n) := by ring
  have hsplit : (fun n : ℕ => (2 * L ^ 2 + 8 * ((n : ℝ) / N)) * (Real.sqrt N * r ^ n))
      = (fun n : ℕ => (2 * L ^ 2 * Real.sqrt N) * r ^ n +
          (8 * Real.sqrt N / N) * ((n : ℝ) * r ^ n)) := by
    funext n
    ring
  have hsumm3 : Summable (fun n : ℕ => (2 * L ^ 2 * Real.sqrt N) * r ^ n) :=
    hsumm1.mul_left _
  have hsumm4 : Summable (fun n : ℕ => (8 * Real.sqrt N / N) * ((n : ℝ) * r ^ n)) :=
    hsumm2.mul_left _
  have hg : Summable (fun n : ℕ => (2 * L ^ 2 + 8 * ((n : ℝ) / N)) * (Real.sqrt N * r ^ n)) := by
    rw [hsplit]
    exact hsumm3.add hsumm4
  exact Summable.of_nonneg_of_le (fun n => by positivity) hterm hg

/-- The geometric main term is at most `N`. -/
lemma geom_main_le {N : ℝ} (hN : 1 ≤ N) :
    Real.exp (-(1 / N)) / (1 - Real.exp (-(1 / N))) ≤ N := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hx0 : 0 ≤ 1 / N := by positivity
  have hrle : Real.exp (-(1 / N)) ≤ 1 / (1 + 1 / N) := exp_neg_le_inv_one_add hx0
  have hrpos : 0 < Real.exp (-(1 / N)) := Real.exp_pos _
  have hrlt1 : Real.exp (-(1 / N)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : (0 : ℝ) < 1 / N := by positivity
    linarith
  have hpos : 0 < 1 - Real.exp (-(1 / N)) := by linarith
  have h2 : Real.exp (-(1 / N)) ≤ N / (N + 1) := by
    refine hrle.trans_eq ?_
    field_simp
  rw [div_le_iff₀ hpos]
  have h2' : Real.exp (-(1 / N)) * (N + 1) ≤ N := by
    have hm := mul_le_mul_of_nonneg_right h2 (by linarith : (0 : ℝ) ≤ N + 1)
    rw [div_mul_cancel₀ _ (by linarith : N + 1 ≠ 0)] at hm
    exact hm
  nlinarith [h2', hrpos, hpos, hN0]

/-- The geometric main term is at least `N - 1`. -/
lemma geom_main_ge {N : ℝ} (hN : 1 ≤ N) :
    N - 1 ≤ Real.exp (-(1 / N)) / (1 - Real.exp (-(1 / N))) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hrpos : 0 < Real.exp (-(1 / N)) := Real.exp_pos _
  have hrlt1 : Real.exp (-(1 / N)) < 1 := by
    rw [Real.exp_lt_one_iff]
    have : (0 : ℝ) < 1 / N := by positivity
    linarith
  have hpos : 0 < 1 - Real.exp (-(1 / N)) := by linarith
  have h1 : 1 - 1 / N ≤ Real.exp (-(1 / N)) := by
    have := Real.add_one_le_exp (-(1 / N))
    linarith
  rw [le_div_iff₀ hpos]
  have h2 : (1 - 1 / N) * N = N - 1 := by
    field_simp
  nlinarith [h1, h2, hN0]

/-- The weighted square-root sum estimate. -/
lemma main_sum_le {N : ℝ} (hN : 2 ≤ N) {q : ℕ} (hq : 1 ≤ q) :
    (∑' n : ℕ, Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 *
        Real.exp (-(n : ℝ) / N)) ≤
      8 * N * Real.sqrt N * Real.log ((q : ℝ) * N) ^ 2 + 128 * N * Real.sqrt N := by
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hN0 : (0 : ℝ) < N := by linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
  set r : ℝ := Real.exp (-(1 / (2 * N))) with hr
  set L : ℝ := Real.log ((q : ℝ) * N) with hL
  have hqN : (1 : ℝ) ≤ (q : ℝ) * N := by nlinarith
  have hL0 : 0 ≤ L := by rw [hL]; exact Real.log_nonneg hqN
  have hr1 : ‖r‖ < 1 := exp_neg_half_lt_one hN1
  have hrn : ∀ n : ℕ, Real.exp (-(n : ℝ) / (2 * N)) = r ^ n := by
    intro n
    rw [hr, ← Real.exp_nat_mul]
    congr 1
    push_cast
    field_simp
  have hsumm1 : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_norm_lt_one hr1
  have hsumm2 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) :=
    (hasSum_coe_mul_geometric_of_norm_lt_one hr1).summable
  have hterm : ∀ n : ℕ,
      Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 *
        Real.exp (-(n : ℝ) / N) ≤
      (2 * L ^ 2 + 8 * ((n : ℝ) / N)) * (Real.sqrt N * r ^ n) := by
    intro n
    have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    have hs1 : Real.sqrt ((n : ℝ) + 1) * Real.exp (-(n : ℝ) / (2 * N)) ≤ Real.sqrt N :=
      sqrt_succ_mul_exp_half_le hN1 n
    have hpos2 : (0 : ℝ) ≤ Real.exp (-(n : ℝ) / (2 * N)) := le_of_lt (Real.exp_pos _)
    have hA0 : 0 ≤ Real.log ((q : ℝ) * ((n : ℝ) + 1)) :=
      Real.log_nonneg (by nlinarith [hq1, hn0])
    have hnN : (0 : ℝ) ≤ (n : ℝ) / N := by positivity
    have hB0 : 0 ≤ Real.log (1 + (n : ℝ) / N) := Real.log_nonneg (by linarith)
    have hlog : Real.log ((q : ℝ) * ((n : ℝ) + 1)) ≤ L + Real.log (1 + (n : ℝ) / N) := by
      have h1 : (q : ℝ) * ((n : ℝ) + 1) = ((q : ℝ) * N) * (((n : ℝ) + 1) / N) := by
        field_simp
      rw [h1, Real.log_mul (by positivity) (by positivity), hL]
      have h2 : Real.log (((n : ℝ) + 1) / N) ≤ Real.log (1 + (n : ℝ) / N) := by
        apply Real.log_le_log (by positivity)
        rw [div_le_iff₀ hN0]
        have h3 : (1 + (n : ℝ) / N) * N = N + (n : ℝ) := by
          field_simp
        linarith [h3]
      linarith
    have hBsq := log_one_add_sq_le (show (0 : ℝ) ≤ (n : ℝ) / N by positivity)
    have hL2 : Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 ≤ 2 * L ^ 2 + 8 * ((n : ℝ) / N) := by
      have h5 : 0 ≤ L + Real.log (1 + (n : ℝ) / N) := by linarith
      have h6 : Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 ≤
          (L + Real.log (1 + (n : ℝ) / N)) ^ 2 := by nlinarith
      have h7 : (L + Real.log (1 + (n : ℝ) / N)) ^ 2 ≤
          2 * L ^ 2 + 2 * Real.log (1 + (n : ℝ) / N) ^ 2 := by
        nlinarith [sq_nonneg (L - Real.log (1 + (n : ℝ) / N))]
      linarith [h6, h7, hBsq]
    have hs2 : Real.exp (-(n : ℝ) / N) =
        Real.exp (-(n : ℝ) / (2 * N)) * Real.exp (-(n : ℝ) / (2 * N)) := by
      rw [← Real.exp_add]
      congr 1
      field_simp
      ring
    have h2 : Real.exp (-(n : ℝ) / (2 * N)) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 ≤
        r ^ n * (2 * L ^ 2 + 8 * ((n : ℝ) / N)) := by
      rw [← hrn n]
      exact mul_le_mul_of_nonneg_left hL2 hpos2
    calc Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 *
          Real.exp (-(n : ℝ) / N)
        = (Real.sqrt ((n : ℝ) + 1) * Real.exp (-(n : ℝ) / (2 * N))) *
            (Real.exp (-(n : ℝ) / (2 * N)) *
              Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2) := by
          rw [hs2]; ring
      _ ≤ Real.sqrt N * (r ^ n * (2 * L ^ 2 + 8 * ((n : ℝ) / N))) :=
          mul_le_mul hs1 h2 (mul_nonneg hpos2 (sq_nonneg _)) (Real.sqrt_nonneg N)
      _ = (2 * L ^ 2 + 8 * ((n : ℝ) / N)) * (Real.sqrt N * r ^ n) := by ring
  have hsplit : (fun n : ℕ => (2 * L ^ 2 + 8 * ((n : ℝ) / N)) * (Real.sqrt N * r ^ n))
      = (fun n : ℕ => (2 * L ^ 2 * Real.sqrt N) * r ^ n +
          (8 * Real.sqrt N / N) * ((n : ℝ) * r ^ n)) := by
    funext n
    ring
  have hsumm3 : Summable (fun n : ℕ => (2 * L ^ 2 * Real.sqrt N) * r ^ n) :=
    hsumm1.mul_left _
  have hsumm4 : Summable (fun n : ℕ => (8 * Real.sqrt N / N) * ((n : ℝ) * r ^ n)) :=
    hsumm2.mul_left _
  have hg : Summable (fun n : ℕ => (2 * L ^ 2 + 8 * ((n : ℝ) / N)) * (Real.sqrt N * r ^ n)) := by
    rw [hsplit]
    exact hsumm3.add hsumm4
  have hf : Summable (fun n : ℕ => Real.sqrt ((n : ℝ) + 1) *
      Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 * Real.exp (-(n : ℝ) / N)) :=
    main_sum_summable hN1 hq
  have hle : (∑' n : ℕ, Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 *
        Real.exp (-(n : ℝ) / N)) ≤
      ∑' n : ℕ, (2 * L ^ 2 + 8 * ((n : ℝ) / N)) * (Real.sqrt N * r ^ n) :=
    Summable.tsum_le_tsum hterm hf hg
  have hval : (∑' n : ℕ, (2 * L ^ 2 + 8 * ((n : ℝ) / N)) * (Real.sqrt N * r ^ n)) =
      (2 * L ^ 2 * Real.sqrt N) * (∑' n : ℕ, r ^ n) +
        (8 * Real.sqrt N / N) * (∑' n : ℕ, (n : ℝ) * r ^ n) := by
    rw [hsplit, hsumm3.tsum_add hsumm4, tsum_mul_left, tsum_mul_left]
  have hp := tsum_pow_le hN1
  have hn := tsum_n_mul_le hN1
  have hfac1 : 0 ≤ 2 * L ^ 2 * Real.sqrt N := by positivity
  have hfac2 : 0 ≤ 8 * Real.sqrt N / N := by positivity
  have hstep : (2 * L ^ 2 * Real.sqrt N) * (∑' n : ℕ, r ^ n) +
      (8 * Real.sqrt N / N) * (∑' n : ℕ, (n : ℝ) * r ^ n) ≤
      (2 * L ^ 2 * Real.sqrt N) * (4 * N) + (8 * Real.sqrt N / N) * (16 * N ^ 2) :=
    add_le_add (mul_le_mul_of_nonneg_left hp hfac1) (mul_le_mul_of_nonneg_left hn hfac2)
  have h1 : (2 * L ^ 2 * Real.sqrt N) * (4 * N) = 8 * N * Real.sqrt N * L ^ 2 := by ring
  have h2 : (8 * Real.sqrt N / N) * (16 * N ^ 2) = 128 * N * Real.sqrt N := by
    field_simp
    ring
  have h3 : (0:ℝ) ≤ 128 * N * Real.sqrt N := by positivity
  linarith [hle, hval, hstep, h1, h2, h3]

end L1Num

section smoothed_psiChi_GRH_proof

open Real Filter Topology

set_option maxHeartbeats 1000000




/-- Partial summation: the partial sums of `χ Λ` against a decreasing weight. -/
private lemma abel_summation {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (f : ℕ → ℝ) :
    ∀ M : ℕ,
      (∑ n ∈ Finset.range (M + 1),
          χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ) * (f n : ℂ))
        = (∑ n ∈ Finset.range (M + 1),
            χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) * (f M : ℂ)
          + ∑ n ∈ Finset.range M,
              (∑ k ∈ Finset.range (n + 1),
                χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)) *
                ((f n : ℂ) - (f (n + 1) : ℂ)) := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ
            (f := fun k => χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ) * (f k : ℂ)),
          Finset.sum_range_succ
            (f := fun k => χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)),
          ih,
          Finset.sum_range_succ
            (f := fun k => (∑ j ∈ Finset.range (k + 1),
              χ (j : ZMod q) * (ArithmeticFunction.vonMangoldt j : ℂ)) *
                ((f k : ℂ) - (f (k + 1) : ℂ)))]
      ring

/-- The telescoping identity `∑_{n<M} n (f n - f (n+1)) + M f M = ∑_{n<M} f (n+1)`. -/
private lemma telescope_identity (f : ℕ → ℝ) :
    ∀ M : ℕ,
      (∑ n ∈ Finset.range M, (n : ℂ) * ((f n : ℂ) - (f (n + 1) : ℂ)))
        + (M : ℂ) * (f M : ℂ) = ∑ n ∈ Finset.range M, (f (n + 1) : ℂ) := by
  intro M
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ
            (f := fun n => (n : ℂ) * ((f n : ℂ) - (f (n + 1) : ℂ))),
          Finset.sum_range_succ (f := fun n => (f (n + 1) : ℂ))]
      push_cast
      linear_combination ih

/-- The partial sums of `χ Λ` over `range (M+1)` are `ψ (M, χ)`. -/
private lemma range_eq_psiChi {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ∀ M : ℕ,
      (∑ n ∈ Finset.range (M + 1),
          χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ)) = psiChi χ (M : ℝ) := by
  intro M
  induction M with
  | zero => simp [psiChi]
  | succ M ih =>
      rw [Finset.sum_range_succ, ih]
      have h1 : psiChi χ ((M : ℝ) + 1) =
          psiChi χ (M : ℝ) +
            χ (((M + 1 : ℕ)) : ZMod q) * (ArithmeticFunction.vonMangoldt (M + 1) : ℂ) := by
        simp only [psiChi]
        rw [show ⌊(M : ℝ) + 1⌋₊ = M + 1 by
              rw [Nat.floor_add_one (by positivity), Nat.floor_natCast],
            Nat.floor_natCast]
        rw [Finset.sum_Ioc_succ_top (Nat.zero_le M)]
      rw [show (((M + 1 : ℕ)) : ℝ) = (M : ℝ) + 1 by push_cast; ring]
      exact h1.symm



/-! ### Proof of `smoothed_psiChi_GRH` -/

/-- Boundary term of the partial summation tends to zero. -/
private lemma tendsto_boundary {q : ℕ} (hq : 1 ≤ q) {N : ℝ} (hN : 1 ≤ N) {c : ℝ} (hc : 0 ≤ c)
    (E : ℕ → ℂ)
    (hE : ∀ n : ℕ, ‖E n‖ ≤
      c * Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2) :
    Tendsto (fun M : ℕ => E M * (Real.exp (-(M : ℝ) / N) : ℂ)) atTop (𝓝 0) := by
  have hN0 : (0 : ℝ) < N := by linarith
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  rw [tendsto_zero_iff_norm_tendsto_zero]
  have hbd : ∀ M : ℕ, 1 ≤ M → ‖E M * (Real.exp (-(M : ℝ) / N) : ℂ)‖ ≤
      c * (q : ℝ) ^ 2 * 8 * N ^ 3 * (((M : ℝ) / N) ^ 3 * Real.exp (-((M : ℝ) / N))) := by
    intro M hM
    have hx1 : (1 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hM
    have hM0 : (0 : ℝ) < (M : ℝ) := by linarith
    have hexp : (0 : ℝ) < Real.exp (-(M : ℝ) / N) := Real.exp_pos _
    have hfM : ‖(Real.exp (-(M : ℝ) / N) : ℂ)‖ = Real.exp (-(M : ℝ) / N) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hexp]
    -- `√(M+1) ≤ 2M`
    have hsq : Real.sqrt ((M : ℝ) + 1) ≤ 2 * (M : ℝ) := by
      have h1 : Real.sqrt ((M : ℝ) + 1) ≤ (M : ℝ) + 1 := by
        have hx : (0 : ℝ) ≤ (M : ℝ) + 1 := by positivity
        have hs : Real.sqrt ((M : ℝ) + 1) * Real.sqrt ((M : ℝ) + 1) = (M : ℝ) + 1 :=
          Real.mul_self_sqrt hx
        have hge1 : (1 : ℝ) ≤ Real.sqrt ((M : ℝ) + 1) := by
          nlinarith [hs, Real.sqrt_nonneg ((M : ℝ) + 1)]
        nlinarith [hs, Real.sqrt_nonneg ((M : ℝ) + 1)]
      linarith
    -- `log (q (M+1)) ≤ q (M+1) ≤ 2qM`
    have hy1 : (1 : ℝ) ≤ (q : ℝ) * ((M : ℝ) + 1) := by nlinarith
    have hlogy : Real.log ((q : ℝ) * ((M : ℝ) + 1)) ≤ (q : ℝ) * ((M : ℝ) + 1) := by
      have h := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < (q : ℝ) * ((M : ℝ) + 1))
      linarith
    have hlog0 : 0 ≤ Real.log ((q : ℝ) * ((M : ℝ) + 1)) := Real.log_nonneg hy1
    have hlogM : Real.log ((q : ℝ) * ((M : ℝ) + 1)) ^ 2 ≤ (2 * (q : ℝ) * (M : ℝ)) ^ 2 := by
      have hq0 : (0 : ℝ) < (q : ℝ) := by linarith
      have h1 : (q : ℝ) * ((M : ℝ) + 1) ≤ 2 * (q : ℝ) * (M : ℝ) := by nlinarith
      have h2 : (0 : ℝ) ≤ (q : ℝ) * ((M : ℝ) + 1) := by linarith
      have h3 : ((q : ℝ) * ((M : ℝ) + 1)) ^ 2 ≤ (2 * (q : ℝ) * (M : ℝ)) ^ 2 :=
        pow_le_pow_left₀ h2 h1 2
      nlinarith
    have hpool : Real.sqrt ((M : ℝ) + 1) * Real.log ((q : ℝ) * ((M : ℝ) + 1)) ^ 2 ≤
        (2 * (M : ℝ)) * (2 * (q : ℝ) * (M : ℝ)) ^ 2 :=
      mul_le_mul hsq hlogM (by positivity) (by positivity)
    have hA : ‖E M‖ ≤ c * ((2 * (M : ℝ)) * (2 * (q : ℝ) * (M : ℝ)) ^ 2) := by
      refine (hE M).trans ?_
      calc c * Real.sqrt ((M : ℝ) + 1) * Real.log ((q : ℝ) * ((M : ℝ) + 1)) ^ 2
          = c * (Real.sqrt ((M : ℝ) + 1) * Real.log ((q : ℝ) * ((M : ℝ) + 1)) ^ 2) := by ring
        _ ≤ c * ((2 * (M : ℝ)) * (2 * (q : ℝ) * (M : ℝ)) ^ 2) :=
            mul_le_mul_of_nonneg_left hpool hc
    rw [norm_mul, hfM]
    refine (mul_le_mul_of_nonneg_right hA (le_of_lt hexp)).trans (le_of_eq ?_)
    field_simp
    ring
  have hlim : Tendsto (fun x : ℝ => x ^ 3 * Real.exp (-x)) atTop (𝓝 0) :=
    tendsto_pow_mul_exp_neg_atTop_nhds_zero 3
  have hlim2 : Tendsto (fun M : ℕ => (M : ℝ) / N) atTop atTop := by
    have h1 : Tendsto (fun M : ℕ => (1 / N) * (M : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.const_mul_atTop (by positivity)
    simpa [div_eq_inv_mul] using h1
  have hlim3 : Tendsto (fun M : ℕ => ((M : ℝ) / N) ^ 3 * Real.exp (-((M : ℝ) / N)))
      atTop (𝓝 0) := hlim.comp hlim2
  have hlim4 : Tendsto (fun M : ℕ =>
      c * (q : ℝ) ^ 2 * 8 * N ^ 3 * (((M : ℝ) / N) ^ 3 * Real.exp (-((M : ℝ) / N))))
      atTop (𝓝 0) := by
    have h := hlim3.const_mul (c * (q : ℝ) ^ 2 * 8 * N ^ 3)
    simpa [mul_assoc] using h
  refine squeeze_zero' ?_ ?_ hlim4
  · filter_upwards with M
    exact norm_nonneg _
  · filter_upwards [Filter.eventually_ge_atTop 1] with M hM
    exact hbd M hM

/-- `∑_{n} f (n+1)` equals the geometric main term. -/
private lemma tsum_shift_exp (N : ℝ) (hN : 0 < N) :
    (∑' n : ℕ, (Real.exp (-(((n + 1 : ℕ)) : ℝ) / N) : ℂ)) =
      ((Real.exp (-(1 / N)) / (1 - Real.exp (-(1 / N)))) : ℂ) := by
  have hr1c : ‖(Real.exp (-(1 / N)) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    have : (0 : ℝ) < 1 / N := by positivity
    linarith
  have h1 : (fun n : ℕ => (Real.exp (-(((n + 1 : ℕ)) : ℝ) / N) : ℂ)) =
      (fun n : ℕ => (Real.exp (-(1 / N)) : ℂ) * (Real.exp (-(1 / N)) : ℂ) ^ n) := by
    funext n
    have h2 : Real.exp (-(((n + 1 : ℕ)) : ℝ) / N) = Real.exp (-(1 / N)) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      field_simp
    rw [h2]
    push_cast
    ring
  rw [h1, tsum_mul_left, tsum_geometric_of_norm_lt_one hr1c]
  have h4 : ((Real.exp (-(1 / N)) : ℂ) * (1 - (Real.exp (-(1 / N)) : ℂ))⁻¹) =
      ((Real.exp (-(1 / N)) / (1 - Real.exp (-(1 / N)))) : ℂ) := by
    push_cast
    ring
  rw [h4]


/-- LEAF. Smoothed twisted sum under GRH: there is an absolute `c` with
`|∑_n χ(n) Λ(n) e^{-n/N} - δ_χ N| ≤ c √N log²(qN)` for every `χ` mod `q` and `N ≥ 2`.
Partial summation `∑ χ(n)Λ(n) e^{-n/N} = ∫_0^∞ ψ(t, χ) e^{-t/N} dt/N` with
`psiChi_bound_of_GRH` and `∫_0^∞ t e^{-t/N} dt/N = N`. Zinoviev 1997, J. Number Theory 65,
Section 1; Davenport ch. 26, p. 146. Unit U-1529. -/
theorem smoothed_psiChi_GRH : GRH → ∃ c : ℝ, ∀ (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (N : ℝ), 2 ≤ N →
      ‖(∑' n : ℕ, χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ) *
          (Real.exp (-n / N) : ℂ)) - (if χ = 1 then (N : ℂ) else 0)‖ ≤
        c * √N * Real.log (q * N) ^ 2 := by
  intro hG
  obtain ⟨c₀, hc₀⟩ := psiChi_bound_of_GRH hG
  refine ⟨300 * (max c₀ 0 + 2) + 3, ?_⟩
  intro q hq χ N hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hq1' : (1 : ℕ) ≤ q := Nat.one_le_iff_ne_zero.mpr (NeZero.ne q)
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1'
  set f : ℕ → ℝ := fun n => Real.exp (-(n : ℝ) / N) with hfdef
  set d : ℂ := if χ = 1 then 1 else 0 with hddef
  set E : ℕ → ℂ := fun n =>
    (∑ k ∈ Finset.range (n + 1),
      χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)) - d * (n : ℂ) with hEdef
  set C : ℝ := max c₀ 0 + 2 with hCdef
  have hC2 : (2 : ℝ) ≤ C := by rw [hCdef]; linarith [le_max_right c₀ 0]
  have hC0 : (0 : ℝ) ≤ C := by linarith
  have hc0C : c₀ ≤ C := by rw [hCdef]; linarith [le_max_left c₀ 0]
  have hdN : d * (N : ℂ) = (if χ = 1 then (N : ℂ) else 0) := by
    rw [hddef]; split_ifs <;> simp
  have hdnorm : ‖d‖ ≤ 1 := by
    rw [hddef]; split_ifs <;> simp
  -- the identity for the partial sums
  have hSM : ∀ M : ℕ,
      (∑ n ∈ Finset.range (M + 1), χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ))
        = d * (M : ℂ) + E M := by
    intro M
    simp only [hEdef]
    ring
  have hTM : ∀ M : ℕ,
      (∑ n ∈ Finset.range (M + 1),
          χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ) * (f n : ℂ))
        = d * (∑ n ∈ Finset.range M, (f (n + 1) : ℂ)) + E M * (f M : ℂ)
          + ∑ n ∈ Finset.range M, E n * ((f n : ℂ) - (f (n + 1) : ℂ)) := by
    intro M
    have hsplit : (∑ n ∈ Finset.range M,
        (d * (n : ℂ) + E n) * ((f n : ℂ) - (f (n + 1) : ℂ)))
        = d * (∑ n ∈ Finset.range M, (n : ℂ) * ((f n : ℂ) - (f (n + 1) : ℂ)))
          + ∑ n ∈ Finset.range M, E n * ((f n : ℂ) - (f (n + 1) : ℂ)) := by
      have hpt : ∀ n : ℕ, (d * (n : ℂ) + E n) * ((f n : ℂ) - (f (n + 1) : ℂ))
          = d * ((n : ℂ) * ((f n : ℂ) - (f (n + 1) : ℂ)))
            + E n * ((f n : ℂ) - (f (n + 1) : ℂ)) := by
        intro n
        ring
      simp only [hpt]
      rw [Finset.sum_add_distrib, Finset.mul_sum]
    have htel := telescope_identity f M
    rw [abel_summation χ f M, hSM M,
      Finset.sum_congr rfl (fun n (_ : n ∈ Finset.range M) => by rw [hSM n]),
      hsplit, ← htel, mul_add]
    ring
  -- the bound on `E`
  have hEbound : ∀ n : ℕ, ‖E n‖ ≤
      C * Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 := by
    intro n
    rcases lt_or_ge n 2 with hn | hn
    · interval_cases n
      · have h0 : E 0 = 0 := by simp [hEdef]
        rw [h0, norm_zero]
        positivity
      · have h1 : ‖E 1‖ ≤ 1 := by
          have h0 : E 1 = -d := by
            simp only [hEdef, Finset.sum_range_succ]
            simp
          rw [h0, norm_neg]
          exact hdnorm
        have hlog2 : Real.log 2 ≤ Real.log ((q : ℝ) * 2) := by
          apply Real.log_le_log (by norm_num)
          nlinarith
        have hl2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
        have hR : (1 : ℝ) ≤ C * Real.sqrt ((1 : ℝ) + 1) * Real.log ((q : ℝ) * ((1 : ℝ) + 1)) ^ 2 := by
          have hs2 : (1.4 : ℝ) ≤ Real.sqrt 2 := by
            nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
          have hsq2 : ((1 : ℝ) + 1) = 2 := by norm_num
          rw [hsq2]
          have hspos : (0 : ℝ) ≤ Real.log ((q : ℝ) * 2) := Real.log_nonneg (by nlinarith)
          have hprod : (1.4 : ℝ) * (0.6931471803) ^ 2 ≤
              Real.sqrt 2 * Real.log ((q : ℝ) * 2) ^ 2 := by
            apply mul_le_mul hs2 (by nlinarith) (by norm_num) (Real.sqrt_nonneg 2)
          nlinarith
        have hcast : C * Real.sqrt (((1 : ℕ) : ℝ) + 1) * Real.log ((q : ℝ) * (((1 : ℕ) : ℝ) + 1)) ^ 2
            = C * Real.sqrt ((1 : ℝ) + 1) * Real.log ((q : ℝ) * ((1 : ℝ) + 1)) ^ 2 := by
          norm_num
        rw [hcast]
        linarith
    · have hx2 : (2 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      have hb := hc₀ q χ (n : ℝ) hx2
      have hEn : E n = psiChi χ (n : ℝ) - (if χ = 1 then ((n : ℝ) : ℂ) else 0) := by
        have h0 : E n = (∑ k ∈ Finset.range (n + 1),
            χ (k : ZMod q) * (ArithmeticFunction.vonMangoldt k : ℂ)) - d * (n : ℂ) := by
          simp only [hEdef]
        rw [h0, range_eq_psiChi χ n, hddef]
        split_ifs <;> simp
      rw [hEn]
      have hb' : ‖psiChi χ (n : ℝ) - (if χ = 1 then ((n : ℝ) : ℂ) else 0)‖ ≤
          c₀ * Real.sqrt (n : ℝ) * Real.log ((q : ℝ) * (n : ℝ)) ^ 2 := hb
      refine hb'.trans ?_
      have hsn : Real.sqrt (n : ℝ) ≤ Real.sqrt ((n : ℝ) + 1) := Real.sqrt_le_sqrt (by linarith)
      have hlogs : Real.log ((q : ℝ) * (n : ℝ)) ≤ Real.log ((q : ℝ) * ((n : ℝ) + 1)) := by
        apply Real.log_le_log (by positivity)
        nlinarith
      have hl0 : (0 : ℝ) ≤ Real.log ((q : ℝ) * (n : ℝ)) := Real.log_nonneg (by nlinarith)
      have hl1 : (0 : ℝ) ≤ Real.log ((q : ℝ) * ((n : ℝ) + 1)) := Real.log_nonneg (by nlinarith)
      have hA : (0 : ℝ) ≤ Real.sqrt (n : ℝ) * Real.log ((q : ℝ) * (n : ℝ)) ^ 2 := by positivity
      have hlogsq : Real.log ((q : ℝ) * (n : ℝ)) ^ 2 ≤
          Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 :=
        pow_le_pow_left₀ hl0 hlogs 2
      have hB : Real.sqrt (n : ℝ) * Real.log ((q : ℝ) * (n : ℝ)) ^ 2 ≤
          Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 :=
        mul_le_mul hsn hlogsq (sq_nonneg _) (Real.sqrt_nonneg _)
      calc c₀ * Real.sqrt (n : ℝ) * Real.log ((q : ℝ) * (n : ℝ)) ^ 2
          = c₀ * (Real.sqrt (n : ℝ) * Real.log ((q : ℝ) * (n : ℝ)) ^ 2) := by ring
        _ ≤ C * (Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2) :=
            mul_le_mul hc0C hB hA hC0
        _ = C * Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 := by ring
  -- the weight differences
  have hΔ : ∀ n : ℕ, ‖(f n : ℂ) - (f (n + 1) : ℂ)‖ ≤ f n / N := by
    intro n
    have hfn : (0 : ℝ) < f n := by simp only [hfdef]; positivity
    have hf1 : (0 : ℝ) < f (n + 1) := by simp only [hfdef]; positivity
    have hdec : f (n + 1) ≤ f n := by
      simp only [hfdef]
      apply Real.exp_le_exp.mpr
      rw [show -(((n + 1 : ℕ)) : ℝ) / N = -((n : ℝ) + 1) / N by push_cast; ring]
      apply div_le_div_of_nonneg_right _ hN0.le
      linarith
    have hreal : ‖(f n : ℂ) - (f (n + 1) : ℂ)‖ = f n - f (n + 1) := by
      rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    rw [hreal]
    have hsp : f n * (1 - Real.exp (-(1 / N))) = f n - f (n + 1) := by
      simp only [hfdef]
      have he : Real.exp (-(((n + 1 : ℕ)) : ℝ) / N) =
          Real.exp (-(1 / N)) * Real.exp (-(n : ℝ) / N) := by
        rw [← Real.exp_add]
        congr 1
        push_cast
        field_simp
        ring
      rw [he]; ring
    rw [← hsp]
    have h1 : 1 - Real.exp (-(1 / N)) ≤ 1 / N := by
      have h := Real.add_one_le_exp (-(1 / N))
      linarith
    have h2 : (0 : ℝ) ≤ 1 - Real.exp (-(1 / N)) := by
      have h : Real.exp (-(1 / N)) < 1 := by
        rw [Real.exp_lt_one_iff]
        have : (0 : ℝ) < 1 / N := by positivity
        linarith
      linarith
    calc f n * (1 - Real.exp (-(1 / N))) ≤ f n * (1 / N) :=
          mul_le_mul_of_nonneg_left h1 (le_of_lt hfn)
      _ = f n / N := by ring
  -- the error term is bounded by the weighted sum
  have hErr_pt : ∀ n : ℕ, ‖E n * ((f n : ℂ) - (f (n + 1) : ℂ))‖ ≤
      C / N * (Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 * f n) := by
    intro n
    have hfn : (0 : ℝ) < f n := by simp only [hfdef]; positivity
    have h1 : ‖E n‖ * ‖(f n : ℂ) - (f (n + 1) : ℂ)‖ ≤
        (C * Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2) * (f n / N) := by
      apply mul_le_mul (hEbound n) (hΔ n) (norm_nonneg _) (by positivity)
    rw [norm_mul]
    calc ‖E n‖ * ‖(f n : ℂ) - (f (n + 1) : ℂ)‖
        ≤ (C * Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2) * (f n / N) := h1
      _ = C / N * (Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 * f n) := by
          ring
  have hsumm_maj : Summable (fun n : ℕ =>
      Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 * f n) := by
    have h := L1Num.main_sum_summable hN1 hq1'
    simpa [hfdef] using h
  have hsumm_majK : Summable (fun n : ℕ => C / N *
      (Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 * f n)) :=
    hsumm_maj.mul_left _
  have hsumm_err : Summable (fun n : ℕ => E n * ((f n : ℂ) - (f (n + 1) : ℂ))) := by
    apply Summable.of_norm
    exact Summable.of_nonneg_of_le (fun n => norm_nonneg _) hErr_pt hsumm_majK
  have hErr_bd : ‖∑' n : ℕ, E n * ((f n : ℂ) - (f (n + 1) : ℂ))‖ ≤
      C / N * (8 * N * Real.sqrt N * Real.log ((q : ℝ) * N) ^ 2 + 128 * N * Real.sqrt N) := by
    have h1 : ‖∑' n : ℕ, E n * ((f n : ℂ) - (f (n + 1) : ℂ))‖ ≤
        ∑' n : ℕ, ‖E n * ((f n : ℂ) - (f (n + 1) : ℂ))‖ :=
      norm_tsum_le_tsum_norm hsumm_err.norm
    have h2 : (∑' n : ℕ, ‖E n * ((f n : ℂ) - (f (n + 1) : ℂ))‖) ≤
        ∑' n : ℕ, C / N *
          (Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 * f n) :=
      Summable.tsum_le_tsum hErr_pt hsumm_err.norm hsumm_majK
    have h3 : (∑' n : ℕ, C / N *
        (Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 * f n)) =
        C / N * (∑' n : ℕ,
          Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 *
            Real.exp (-(n : ℝ) / N)) := by
      rw [tsum_mul_left]
    have h4 : (∑' n : ℕ, Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 *
        Real.exp (-(n : ℝ) / N)) ≤
        8 * N * Real.sqrt N * Real.log ((q : ℝ) * N) ^ 2 + 128 * N * Real.sqrt N :=
      L1Num.main_sum_le hN hq1'
    have h5 : (0 : ℝ) ≤ C / N := by positivity
    calc ‖∑' n : ℕ, E n * ((f n : ℂ) - (f (n + 1) : ℂ))‖
        ≤ ∑' n : ℕ, ‖E n * ((f n : ℂ) - (f (n + 1) : ℂ))‖ := h1
      _ ≤ ∑' n : ℕ, C / N *
            (Real.sqrt ((n : ℝ) + 1) * Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 * f n) := h2
      _ = C / N * (∑' n : ℕ, Real.sqrt ((n : ℝ) + 1) *
            Real.log ((q : ℝ) * ((n : ℝ) + 1)) ^ 2 * Real.exp (-(n : ℝ) / N)) := h3
      _ ≤ C / N * (8 * N * Real.sqrt N * Real.log ((q : ℝ) * N) ^ 2 + 128 * N * Real.sqrt N) :=
          mul_le_mul_of_nonneg_left h4 h5
  -- the main term
  have hmain : ‖(∑' n : ℕ, (Real.exp (-(((n + 1 : ℕ)) : ℝ) / N) : ℂ)) - (N : ℂ)‖ ≤ 1 := by
    rw [tsum_shift_exp N hN0]
    have h1 : ((Real.exp (-(1 / N)) / (1 - Real.exp (-(1 / N)))) : ℂ) - (N : ℂ) =
        ((Real.exp (-(1 / N)) / (1 - Real.exp (-(1 / N))) - N : ℝ) : ℂ) := by
      push_cast
      ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_le]
    constructor
    · have := L1Num.geom_main_ge hN1; linarith
    · have := L1Num.geom_main_le hN1; linarith
  -- summability of the two remaining series
  have hr1 : ‖(Real.exp (-(1 / N)) : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    have : (0 : ℝ) < 1 / N := by positivity
    linarith
  have hsumm_f1 : Summable (fun n : ℕ => (f (n + 1) : ℂ)) := by
    have hgeom : Summable (fun n : ℕ => (Real.exp (-(1 / N)) : ℂ) ^ n) :=
      summable_geometric_of_norm_lt_one hr1
    have hmul : Summable (fun n : ℕ => (Real.exp (-(1 / N)) : ℂ) *
        (Real.exp (-(1 / N)) : ℂ) ^ n) := hgeom.mul_left _
    refine hmul.congr ?_
    intro n
    simp only [hfdef]
    have he : Real.exp (-(((n + 1 : ℕ)) : ℝ) / N) = Real.exp (-(1 / N)) ^ (n + 1) := by
      rw [← Real.exp_nat_mul]
      congr 1
      push_cast
      field_simp
    rw [he, pow_succ]
    push_cast
    exact mul_comm _ _
  have hΛ1 : ∀ n : ℕ, ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) + 1 := by
    intro n
    rcases Nat.eq_zero_or_pos n with h | h
    · subst h; simp
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
      have h1 := ArithmeticFunction.vonMangoldt_le_log (n := n)
      have h2 : Real.log (n : ℝ) ≤ (n : ℝ) - 1 := Real.log_le_sub_one_of_pos (by linarith)
      linarith
  have hsumm_af : Summable (fun n : ℕ =>
      χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ) * (f n : ℂ)) := by
    set r : ℝ := Real.exp (-(1 / N)) with hrdef
    have hr0 : 0 ≤ r := le_of_lt (Real.exp_pos _)
    have hr1 : ‖r‖ < 1 := by
      rw [hrdef, Real.norm_eq_abs, abs_of_nonneg hr0, Real.exp_lt_one_iff]
      have : (0 : ℝ) < 1 / N := by positivity
      linarith
    have h2 : Summable (fun n : ℕ => (n : ℝ) * r ^ n) :=
      (hasSum_coe_mul_geometric_of_norm_lt_one hr1).summable
    have h3 : Summable (fun n : ℕ => r ^ n) := summable_geometric_of_norm_lt_one hr1
    refine Summable.of_norm_bounded (h2.add h3) ?_
    intro n
    have hfn : f n = r ^ n := by
      rw [hfdef, hrdef, ← Real.exp_nat_mul]
      congr 1
      push_cast
      field_simp
    have hfnpos : (0 : ℝ) < f n := by rw [hfn]; positivity
    have hχ : ‖χ (n : ZMod q)‖ ≤ 1 := DirichletCharacter.norm_le_one χ _
    have hΛn : (0 : ℝ) ≤ ArithmeticFunction.vonMangoldt n := ArithmeticFunction.vonMangoldt_nonneg
    have hΛ1n : ArithmeticFunction.vonMangoldt n ≤ (n : ℝ) + 1 := hΛ1 n
    have hnorm : ‖χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ) * (f n : ℂ)‖ =
        ‖χ (n : ZMod q)‖ * ArithmeticFunction.vonMangoldt n * f n := by
      rw [norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hΛn,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos hfnpos]
    rw [hnorm]
    have hstep : ‖χ (n : ZMod q)‖ * ArithmeticFunction.vonMangoldt n * f n ≤
        1 * ((n : ℝ) + 1) * f n := by
      have h4 : ‖χ (n : ZMod q)‖ * ArithmeticFunction.vonMangoldt n ≤ 1 * ((n : ℝ) + 1) :=
        mul_le_mul hχ hΛ1n hΛn (by norm_num)
      exact mul_le_mul_of_nonneg_right h4 (le_of_lt hfnpos)
    refine hstep.trans (le_of_eq ?_)
    rw [hfn]
    ring
  -- limits
  have hTendT : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range (M + 1),
      χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ) * (f n : ℂ))
      atTop (𝓝 (∑' n : ℕ, χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ) * (f n : ℂ))) :=
    hsumm_af.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have hTendG : Tendsto (fun M : ℕ => d * (∑ n ∈ Finset.range M, (f (n + 1) : ℂ)) +
      E M * (f M : ℂ) + ∑ n ∈ Finset.range M, E n * ((f n : ℂ) - (f (n + 1) : ℂ)))
      atTop (𝓝 (d * (∑' n : ℕ, (f (n + 1) : ℂ)) +
        ∑' n : ℕ, E n * ((f n : ℂ) - (f (n + 1) : ℂ)))) := by
    have h1 : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M, (f (n + 1) : ℂ))
        atTop (𝓝 (∑' n : ℕ, (f (n + 1) : ℂ))) := hsumm_f1.hasSum.tendsto_sum_nat
    have h2 : Tendsto (fun M : ℕ => ∑ n ∈ Finset.range M, E n * ((f n : ℂ) - (f (n + 1) : ℂ)))
        atTop (𝓝 (∑' n : ℕ, E n * ((f n : ℂ) - (f (n + 1) : ℂ)))) :=
      hsumm_err.hasSum.tendsto_sum_nat
    have h3 : Tendsto (fun M : ℕ => E M * (f M : ℂ)) atTop (𝓝 0) := by
      have h := tendsto_boundary hq1' hN1 hC0 E hEbound
      simpa [hfdef] using h
    have h4 := ((h1.const_mul d).add h3).add h2
    simpa [add_assoc] using h4
  have hfin : (∑' n : ℕ, χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ) * (f n : ℂ)) =
      d * (∑' n : ℕ, (f (n + 1) : ℂ)) +
        ∑' n : ℕ, E n * ((f n : ℂ) - (f (n + 1) : ℂ)) :=
    tendsto_nhds_unique hTendT (hTendG.congr' (Filter.Eventually.of_forall (fun M => (hTM M).symm)))
  -- final assembly
  have hlog2 : Real.log 2 ≤ Real.log ((q : ℝ) * N) := by
    apply Real.log_le_log (by norm_num)
    nlinarith
  have hlog2' : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have hLpos : (0 : ℝ) ≤ Real.log ((q : ℝ) * N) := by linarith
  have hbase : (2 : ℝ) / 3 ≤ Real.sqrt N * Real.log ((q : ℝ) * N) ^ 2 := by
    have h1 : (1.4 : ℝ) ≤ Real.sqrt 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
    have h2 : Real.sqrt 2 ≤ Real.sqrt N := Real.sqrt_le_sqrt (by linarith)
    nlinarith [Real.sqrt_nonneg N]
  have hspl : d * (∑' n : ℕ, (f (n + 1) : ℂ)) +
        (∑' n : ℕ, E n * ((f n : ℂ) - (f (n + 1) : ℂ))) - d * (N : ℂ) =
      d * ((∑' n : ℕ, (f (n + 1) : ℂ)) - (N : ℂ)) +
        (∑' n : ℕ, E n * ((f n : ℂ) - (f (n + 1) : ℂ))) := by ring
  have hgoal_f : ‖d * (∑' n : ℕ, (f (n + 1) : ℂ)) +
        (∑' n : ℕ, E n * ((f n : ℂ) - (f (n + 1) : ℂ))) - d * (N : ℂ)‖ ≤
      (300 * (max c₀ 0 + 2) + 3) * Real.sqrt N * Real.log ((q : ℝ) * N) ^ 2 := by
    rw [hspl]
    have hA : ‖d * ((∑' n : ℕ, (f (n + 1) : ℂ)) - (N : ℂ))‖ ≤ 1 := by
      rw [norm_mul]
      calc ‖d‖ * ‖(∑' n : ℕ, (f (n + 1) : ℂ)) - (N : ℂ)‖ ≤ 1 * 1 := by
            apply mul_le_mul hdnorm hmain (norm_nonneg _) (by norm_num)
        _ = 1 := by norm_num
    have hB : ‖∑' n : ℕ, E n * ((f n : ℂ) - (f (n + 1) : ℂ))‖ ≤
        C / N * (8 * N * Real.sqrt N * Real.log ((q : ℝ) * N) ^ 2 + 128 * N * Real.sqrt N) :=
      hErr_bd
    have hX : (0 : ℝ) ≤ Real.sqrt N * Real.log ((q : ℝ) * N) ^ 2 := by positivity
    have hCN : C / N * (8 * N * Real.sqrt N * Real.log ((q : ℝ) * N) ^ 2 + 128 * N * Real.sqrt N) =
        8 * C * (Real.sqrt N * Real.log ((q : ℝ) * N) ^ 2) + 128 * C * Real.sqrt N := by
      field_simp
    have hCs : C = max c₀ 0 + 2 := hCdef
    have hLsq : (0.4804 : ℝ) ≤ Real.log ((q : ℝ) * N) ^ 2 := by
      have h1 : (0.6931471803 : ℝ) ≤ Real.log ((q : ℝ) * N) := le_trans hlog2'.le hlog2
      have h2 : (0 : ℝ) ≤ Real.log ((q : ℝ) * N) := hLpos
      nlinarith
    have hsqN : Real.sqrt N ≤ 2.1 * (Real.sqrt N * Real.log ((q : ℝ) * N) ^ 2) := by
      nlinarith [hX, hLsq, Real.sqrt_nonneg N]
    have hone : (1 : ℝ) ≤ 1.5 * (Real.sqrt N * Real.log ((q : ℝ) * N) ^ 2) := by
      linarith [hbase, hX]
    calc ‖d * ((∑' n : ℕ, (f (n + 1) : ℂ)) - (N : ℂ)) +
          (∑' n : ℕ, E n * ((f n : ℂ) - (f (n + 1) : ℂ)))‖
        ≤ ‖d * ((∑' n : ℕ, (f (n + 1) : ℂ)) - (N : ℂ))‖ +
          ‖∑' n : ℕ, E n * ((f n : ℂ) - (f (n + 1) : ℂ))‖ := norm_add_le _ _
      _ ≤ 1 + C / N * (8 * N * Real.sqrt N * Real.log ((q : ℝ) * N) ^ 2 +
            128 * N * Real.sqrt N) := add_le_add hA hB
      _ ≤ (300 * (max c₀ 0 + 2) + 3) * Real.sqrt N * Real.log ((q : ℝ) * N) ^ 2 := by
          rw [hCN, hCs]
          rw [show (300 * (max c₀ 0 + 2) + 3) * Real.sqrt N * Real.log ((q : ℝ) * N) ^ 2
              = (300 * (max c₀ 0 + 2) + 3) *
                (Real.sqrt N * Real.log ((q : ℝ) * N) ^ 2) by ring]
          have hM0 : (0 : ℝ) ≤ max c₀ 0 + 2 := by positivity
          have hX0 : (0 : ℝ) ≤ Real.sqrt N * Real.log ((q : ℝ) * N) ^ 2 := by positivity
          have hS1 : 128 * (max c₀ 0 + 2) * Real.sqrt N ≤
              268.8 * (max c₀ 0 + 2) * (Real.sqrt N * Real.log ((q : ℝ) * N) ^ 2) := by
            nlinarith [hsqN]
          have hS2 : (1 : ℝ) ≤ 1.5 * (Real.sqrt N * Real.log ((q : ℝ) * N) ^ 2) := hone
          exact L1Num.final_bound hM0 hX0 hS1 hS2
  have hgoal2 : ‖(∑' n : ℕ, χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ) *
        (Real.exp (-n / N) : ℂ)) - (if χ = 1 then (N : ℂ) else 0)‖ ≤
      (300 * (max c₀ 0 + 2) + 3) * Real.sqrt N * Real.log ((q : ℝ) * N) ^ 2 := by
    rw [← hdN]
    have hf1 : (∑' n : ℕ, χ (n : ZMod q) * (ArithmeticFunction.vonMangoldt n : ℂ) *
          (Real.exp (-n / N) : ℂ)) =
        d * (∑' n : ℕ, (Real.exp (-(n + 1) / N) : ℂ)) +
          ∑' n : ℕ, E n * ((Real.exp (-n / N) : ℂ) - (Real.exp (-(n + 1) / N) : ℂ)) := by
      simpa [hfdef] using hfin
    rw [hf1]
    simpa [hfdef] using hgoal_f
  exact hgoal2
end smoothed_psiChi_GRH_proof

/-- LEAF. Gauss sum bound: `|τ(χ)| ≤ √q` for every Dirichlet character mod `q`, with
`τ(χ) = ∑_b χ(b) e(b/q)`. For `χ` induced by primitive `χ*` mod `d`,
`τ(χ) = μ(q/d) χ*(q/d) τ(χ*)` and `|τ(χ*)| = √d`. Montgomery-Vaughan, Multiplicative Number
Theory I, Theorem 9.10; Davenport ch. 9, p. 66. Unit U-1529. -/
theorem gaussSum_norm_le {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    ‖gaussSum χ ZMod.stdAddChar‖ ≤ √q := by
  classical
  let e136 : AddChar (ZMod q) ℂ := ZMod.stdAddChar
  let G : ZMod q → ℂ := fun a => gaussSum χ (e136.mulShift a)
  have hortho (t : ZMod q) : ∑ a : ZMod q, e136 (t * a) = if t = 0 then (q : ℂ) else 0 := by
    by_cases ht : t = 0
    · simp [ht, e136]
    · rw [ite_eq_right ht]
      exact AddChar.sum_eq_zero_of_ne_one (ZMod.isPrimitive_stdAddChar q ht)
  have hstar (x : ZMod q) : star (e136 x) = e136 (-x) := by
    simpa [e136, ZMod.stdAddChar_apply, AddChar.map_neg_eq_inv] using
      (Complex.inv_eq_conj (Circle.norm_coe (ZMod.toCircle x))).symm
  have henergy : (∑ a : ZMod q, G a * star (G a)) =
      q * ∑ x : ZMod q, χ x * star (χ x) := by
    simp only [G, gaussSum, star_sum, star_mul, AddChar.mulShift_apply]
    simp_rw [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm]
    have hterm (a y : ZMod q) :
        χ x * e136 (a * x) * (star (e136 (a * y)) * star (χ y)) =
          (χ x * star (χ y)) * e136 ((x - y) * a) := by
      rw [hstar]
      calc
        _ = (χ x * star (χ y)) * (e136 (a * x) * e136 (-(a * y))) := by ring
        _ = _ := by rw [← AddChar.map_add_eq_mul]; congr 2 <;> ring
    simp_rw [hterm]
    simp_rw [← Finset.mul_sum, hortho]
    simp [sub_eq_zero, mul_ite]
    ring
  have hchars : (∑ x : ZMod q, χ x * star (χ x)) = (q.totient : ℂ) := by
    have ht (x : ZMod q) : χ x * star (χ x) = (1 : DirichletCharacter ℂ q) x := by
      by_cases hx : IsUnit x
      · change χ x * (starRingEnd ℂ) (χ x) = _
        rw [Complex.mul_conj', ← hx.unit_spec, χ.unit_norm_eq_one]
        simp [MulChar.one_apply hx]
      · simp [MulChar.map_nonunit _ hx]
    simp_rw [ht]
    rw [MulChar.sum_one_eq_card_units, ZMod.card_units_eq_totient]
  rw [hchars] at henergy
  change (∑ a : ZMod q, G a * (starRingEnd ℂ) (G a)) = _ at henergy
  simp_rw [Complex.mul_conj'] at henergy
  have hreal : (∑ a : ZMod q, ‖G a‖ ^ 2) = (q : ℝ) * q.totient := by
    exact_mod_cast henergy
  have hunit (u : (ZMod q)ˣ) : ‖G u‖ = ‖gaussSum χ e136‖ := by
    dsimp [G]
    rw [gaussSum_mulShift_eq, norm_mul, DirichletCharacter.unit_norm_eq_one, one_mul]
  have htriv : (∑ a : ZMod q, ((1 : DirichletCharacter ℂ q) a).re) = (q.totient : ℝ) := by
    have h := MulChar.sum_one_eq_card_units (R := ZMod q) (R' := ℂ)
    rw [ZMod.card_units_eq_totient] at h
    have hh := congrArg (fun z : ℂ => Complex.reCLM z) h
    rw [map_sum] at hh
    simpa using hh
  have hlow : (q.totient : ℝ) * ‖gaussSum χ e136‖ ^ 2 ≤ ∑ a : ZMod q, ‖G a‖ ^ 2 := by
    calc
      _ = ∑ a : ZMod q, ((1 : DirichletCharacter ℂ q) a).re * ‖gaussSum χ e136‖ ^ 2 := by
        rw [← Finset.sum_mul, htriv]
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro a _
        by_cases ha : IsUnit a
        · rw [← ha.unit_spec, MulChar.one_apply (Units.isUnit ha.unit), Complex.one_re, one_mul,
            hunit]
        · rw [MulChar.map_nonunit _ ha, Complex.zero_re, zero_mul]
          positivity
  have hpos : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  rw [Real.le_sqrt (norm_nonneg _) (by positivity)]
  change ‖gaussSum χ e136‖ ^ 2 ≤ (q : ℝ)
  rw [hreal] at hlow
  nlinarith

/-- LEAF. Additive characters through multiplicative ones: for a unit `m` mod `q`,
`e(m/q) = (1/φ(q)) ∑_χ χ(m⁻¹) τ(χ)`. Orthogonality, `sum_char_inv_mul_char_eq`.
Davenport ch. 9, (1), p. 65. Unit U-1529. -/
theorem stdAddChar_eq_sum_gauss {q : ℕ} [NeZero q] {m : ZMod q} (hm : IsUnit m) :
    ZMod.stdAddChar m = (1 / (q.totient : ℂ)) *
      ∑ χ : DirichletCharacter ℂ q, χ m⁻¹ * gaussSum χ ZMod.stdAddChar := by
  unfold gaussSum
  have h_inner : ∀ χ : DirichletCharacter ℂ q,
      χ m⁻¹ * ∑ a : ZMod q, χ a * ZMod.stdAddChar a =
      ∑ a : ZMod q, χ m⁻¹ * (χ a * ZMod.stdAddChar a) := by
    intro χ
    rw [Finset.mul_sum]
  simp_rw [h_inner]
  rw [Finset.sum_comm]
  have h_sum : ∀ a : ZMod q,
      ∑ χ : DirichletCharacter ℂ q, χ m⁻¹ * (χ a * ZMod.stdAddChar a) =
      (∑ χ : DirichletCharacter ℂ q, χ m⁻¹ * χ a) * ZMod.stdAddChar a := by
    intro a
    have : (fun χ : DirichletCharacter ℂ q => χ m⁻¹ * (χ a * ZMod.stdAddChar a)) = (fun χ : DirichletCharacter ℂ q => (χ m⁻¹ * χ a) * ZMod.stdAddChar a) := by
      ext χ
      rw [mul_assoc]
    rw [this, Finset.sum_mul]
  simp_rw [h_sum]
  have h_char_sum : ∀ a : ZMod q, ∑ χ : DirichletCharacter ℂ q, χ m⁻¹ * χ a = if m = a then (q.totient : ℂ) else 0 := by
    intro a
    rw [DirichletCharacter.sum_char_inv_mul_char_eq ℂ hm]
  simp_rw [h_char_sum]
  have h_eval : ∑ a : ZMod q, (if m = a then (q.totient : ℂ) else 0) * ZMod.stdAddChar a = (q.totient : ℂ) * ZMod.stdAddChar m := by
    rw [Finset.sum_eq_single m]
    · split_ifs with h_if
      · rfl
      · contradiction
    · intro b _ hb
      split_ifs with h_if
      · exact False.elim (hb h_if.symm)
      · rw [zero_mul]
    · intro h
      exfalso
      exact h (Finset.mem_univ m)
  rw [h_eval, ← mul_assoc]
  have h_div : (1 / (q.totient : ℂ)) * (q.totient : ℂ) = 1 := by
    rw [one_div, inv_mul_cancel₀]
    have h_totient_pos : 0 < q.totient := Nat.totient_pos.mpr (NeZero.pos q)
    exact_mod_cast ne_of_gt h_totient_pos
  rw [h_div, one_mul]

/-- LEAF. The Gauss sum of the trivial character is the Ramanujan sum `c_q(1) = μ(q)`.
Hardy-Wright, Theorem 271; Davenport ch. 26, p. 147. Unit U-1529. -/
theorem gaussSum_one {q : ℕ} [NeZero q] :
    gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar = (ArithmeticFunction.moebius q : ℂ) := by
  classical
  have hsum : gaussSum (1 : DirichletCharacter ℂ q) ZMod.stdAddChar =
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        LeanLab.PerelliPintz1992.e ((1 : ℝ) * a / q) := by
    unfold gaussSum
    rw [Finset.sum_filter]
    apply Finset.sum_bij (fun a _ => a.val)
    · intro a _
      exact Finset.mem_range.mpr a.val_lt
    · intro a _ b _ h
      exact ZMod.val_injective q h
    · intro b hb
      refine ⟨(b : ZMod q), Finset.mem_univ _, ?_⟩
      rw [ZMod.val_natCast, Nat.mod_eq_of_lt (Finset.mem_range.mp hb)]
    · intro a _
      have hcop : IsUnit a ↔ Nat.Coprime a.val q := by
        rw [← ZMod.isUnit_iff_coprime, ZMod.natCast_zmod_val]
      by_cases ha : IsUnit a
      · rw [MulChar.one_apply ha, one_mul, if_pos (hcop.mp ha)]
        have he := ZMod.stdAddChar_coe (N := q) (a.val : ℤ)
        simp only [Int.cast_natCast, ZMod.natCast_zmod_val] at he
        rw [he]
        unfold LeanLab.PerelliPintz1992.e
        congr 1
        push_cast
        ring
      · rw [MulChar.map_nonunit _ ha, zero_mul, if_neg (fun h => ha (hcop.mpr h))]
  rw [hsum]
  simpa only [Nat.cast_one] using LeanLab.PerelliPintz1992.Decomp1519.ramanujan_coprime (q := q) (a := 1) (NeZero.pos q) (Nat.coprime_one_left q)

/-- LEAF. Major arcs under GRH: there is an absolute `c` such that for `q ≥ 1`, `a` coprime
to `q`, real `β` and `N ≥ 2`,
`|S(a/q + β) - (μ(q)/φ(q)) ∑_{n ≥ 0} e^{-2πiβn} e^{-n/N}| ≤ c √q (1 + |β| N) √N log²(qN)`.
Expand `e(-an/q)` by `stdAddChar_eq_sum_gauss`, bound each non-trivial `χ` by
`smoothed_psiChi_GRH` and partial summation against `e^{-2πiβt}` (total variation
`≪ 1 + |β| N`), `gaussSum_norm_le`, and `gaussSum_one` for the main term.
P0011 page 100 (major arcs `E₁'`); Zinoviev 1997, J. Number Theory 65, Lemma 2.1;
Davenport ch. 26, p. 147. Unit U-1529. -/
theorem major_arc_GRH : GRH → ∃ c : ℝ, ∀ (q : ℕ) (a : ℤ), 1 ≤ q → Int.gcd a q = 1 →
    ∀ β N : ℝ, 2 ≤ N →
      ‖SW N (a / q + β) - ((ArithmeticFunction.moebius q : ℂ) / (q.totient : ℂ)) *
          ∑' n : ℕ, Complex.exp (-(2 * Real.pi * I * β * n)) * (Real.exp (-n / N) : ℂ)‖ ≤
        c * √q * (1 + |β| * N) * √N * Real.log (q * N) ^ 2 := by
  sorry

/-- LEAF. Vinogradov-Vaughan minor arc bound, unconditional: there is an absolute `c` such
that for `N ≥ 2`, `q ≥ 1`, `a` coprime to `q`, `|α - a/q| ≤ 1/q²`,
`|∑_{n ≤ N} Λ(n) e(αn)| ≤ c (N/√q + N^{4/5} + √(Nq)) log⁴ N`. Vaughan's identity.
Davenport ch. 25, Theorem, p. 143. Unit U-1529. -/
theorem vaughan_minor_arc : ∃ c : ℝ, ∀ N : ℕ, 2 ≤ N → ∀ (α : ℝ) (a : ℤ) (q : ℕ), 1 ≤ q →
    Int.gcd a q = 1 → |α - a / q| ≤ 1 / (q : ℝ) ^ 2 →
      ‖∑ n ∈ Finset.Icc 1 N, (ArithmeticFunction.vonMangoldt n : ℂ) *
          Complex.exp (2 * Real.pi * I * α * n)‖ ≤
        c * ((N : ℝ) / √q + (N : ℝ) ^ ((4 : ℝ) / 5) + √(N * q)) * Real.log N ^ 4 := by
  sorry

/-! ### Vacuity -/

/-- The range of `psi_uniform_of_GRH` is not empty, and `q = 1`, `a = 0` satisfy the
coprimality hypothesis of `major_arc_GRH`, `|α - a/q| ≤ 1/q²` holds at `α = 0`. -/
example : ((10 : ℝ) ^ 11 ≤ 10 ^ 20) ∧ Int.gcd 0 1 = 1 ∧
    |(0 : ℝ) - ((0 : ℤ) : ℝ) / ((1 : ℕ) : ℝ)| ≤ 1 / ((1 : ℕ) : ℝ) ^ 2 := by
  norm_num

/-- `IsUnit (1 : ZMod 5)`: the unit hypothesis of the progression leaves can hold. -/
example : IsUnit (1 : ZMod 5) := isUnit_one

end LeanLab.DERZ1997.Decomp1529c
