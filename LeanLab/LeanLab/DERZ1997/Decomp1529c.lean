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
  sorry

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
