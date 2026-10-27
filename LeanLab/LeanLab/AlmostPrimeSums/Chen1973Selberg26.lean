/-
AI-written Lean code, Claude, 2026-10-21, session 20261021T0217Z-cloud56, unit U-6814, track T1.
P0002 J.-R. Chen 1973, Sci. Sinica 16, 157-176, p. 171, (24) and (25) combined into the Selberg
factor of (26), read from the lab copy papers/P0002.pdf, page image rendered with pdftoppm.

`chen_display24` gives the Selberg quadratic form `= 1/S`, with `S = ∑ μ²(d)/ψ(d)` over squarefree
`d ≤ D` prime to `x`; `S_eq_Sv` identifies this `S` with the `S` of (25) in `Chen1973V`; and
`chen26_inv_S` bounds `1/S`. Together: for fixed `0 < ε < 1/6` and large even `x`, Chen's
quadratic form at `D = ⌊(x^{1/2-ε})^{1/2}⌋` is at most `(8 + 24ε) C_x / log x`, the factor in (26).
The sum over `p₁, p₂, n` with `Φ` in (26), and its error terms, are not here.
Binary Goldbach is OPEN.
-/
import LeanLab.AlmostPrimeSums.Chen1973Display24
import LeanLab.AlmostPrimeSums.Chen1973Display26

open Finset ArithmeticFunction
open scoped ArithmeticFunction.Moebius

noncomputable section
namespace LeanLab.AlmostPrimeSums.Chen1973Selberg26

open LeanLab.AlmostPrimeSums.Chen1973V LeanLab.AlmostPrimeSums.Chen1973Display24
  LeanLab.AlmostPrimeSums.Chen1973Display25 LeanLab.AlmostPrimeSums.Chen1973Display26

/-- The two forms of Chen's `S` agree for even `x`: `S(x, z) = ∑_{d ∈ sv x ⌊z⌋} μ²(d)/ψ(d)`. -/
theorem S_eq_Sv {x : ℕ} (hx : Even x) (z : ℝ) : S x z = Sv x ⌊z⌋₊ := by
  unfold S Sv sv
  rw [sum_filter]
  refine sum_congr rfl fun k _ => ?_
  split_ifs with hc
  · have hmu : ((μ k : ℤ) : ℝ) ^ 2 = 1 := by
      exact_mod_cast moebius_sq_eq_one_of_squarefree hc.1
    rw [hmu, ψ, one_div, ← prod_inv_distrib]
    refine prod_congr rfl fun p hp => ?_
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp2 : p ≠ 2 := by
      rintro rfl
      have := Nat.Coprime.coprime_dvd_left (Nat.dvd_of_mem_primeFactors hp) hc.2
      rw [Nat.prime_two.coprime_iff_not_dvd] at this
      exact this (even_iff_two_dvd.mp hx)
    have h3 : (3 : ℝ) ≤ p := by exact_mod_cast (show 3 ≤ p by have := hpp.two_le; omega)
    have e1 : (p : ℝ) - 2 ≠ 0 := by linarith
    have e2 : (p : ℝ) - 1 ≠ 0 := by linarith
    field_simp
    ring
  · rfl

/-- **Chen 1973, the Selberg factor of (26), PROVED**: for fixed `0 < ε < 1/6` there is `x₀` with,
for every even `x ≥ x₀` and `D = ⌊(x^{1/2-ε})^{1/2}⌋`,
`∑_{d₁,d₂ ≤ D, (d₁d₂,x)=1} λ_{d₁}λ_{d₂}/φ(d₁d₂/(d₁,d₂)) ≤ (8 + 24ε) C_x / log x`. -/
theorem chen26_selberg {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1 / 6) :
    ∃ x₀ : ℕ, ∀ x : ℕ, Even x → x₀ ≤ x →
      ∑ d₁ ∈ sv x ⌊zC x ε⌋₊, ∑ d₂ ∈ sv x ⌊zC x ε⌋₊,
        lamC x ⌊zC x ε⌋₊ d₁ * lamC x ⌊zC x ε⌋₊ d₂ / ((d₁ * d₂ / d₁.gcd d₂).totient : ℝ) ≤
        (8 + 24 * ε) * LeanLab.ChenDoubleSieve.CN x / Real.log x := by
  obtain ⟨x₀, h⟩ := chen26_inv_S hε0 hε1
  refine ⟨x₀ + 1, fun x he hx => ?_⟩
  obtain ⟨-, hb⟩ := h x he (by omega)
  have hxpos : 0 < x := by omega
  have hD : 1 ≤ ⌊zC x ε⌋₊ := Nat.le_floor (by
    have h1 : (1 : ℝ) ≤ x := by exact_mod_cast hxpos
    unfold zC
    exact_mod_cast Real.one_le_rpow (Real.one_le_rpow h1 (by linarith)) (by norm_num))
  rw [chen_display24 he hD, ← S_eq_Sv he]
  exact hb

end LeanLab.AlmostPrimeSums.Chen1973Selberg26
