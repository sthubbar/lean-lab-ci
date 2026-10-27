import Mathlib

/-!
# R-0010, the Goldbach Dirichlet series and the invisibility of finitely many exceptions

T3 MOONSHOT route, unit U-1066, PC run 20261019T1403Z-32628. AI wrote this Lean code.
KNOWN mathematics; this file is a map entry, not progress on Goldbach, which is open.

Route: study `Φ(s) = Σ G(n) n^{-s}`, `G(n) = Σ_{a+b=n} Λ(a) Λ(b)`, by analytic continuation,
in the line of Egami-Matsumoto 2007 and Brüdern-Kaczorowski-Perelli 2019, and read binary
Goldbach off its analytic behaviour to the left of `Re s = 2`.

What this file proves.
* `finite_change_entire`: if two coefficient sequences differ only on a finite set, the
  difference of their L-series is a finite Dirichlet polynomial, an entire function, and the two
  L-series differ by it wherever one converges. So every statement about continuation, poles,
  growth in vertical strips or a natural boundary is the SAME for `G` and for `G` with any
  finite set of values replaced by `0`. No such property can prove `G(N) > 0` for a given `N`.
* `injective_contrast`: on the half-plane of absolute convergence the L-series does determine
  every coefficient, Mathlib's `LSeries_eq_iff_of_abscissaOfAbsConv_lt_top`. So a route through
  `Φ` must extract coefficients in the region of convergence, by Perron's formula, which is the
  circle method again and meets the R-0001 barrier.
* `goldbach_exception_invisible`: the special case `G` against `G` with `G(N₀)` set to `0`.
-/

namespace LeanLab.Routes.R0010

open Finset

/-- the binary Goldbach count with von Mangoldt weights, `G(n) = Σ_{a+b=n} Λ(a) Λ(b)` -/
noncomputable def G (n : ℕ) : ℂ :=
  ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)),
    ((ArithmeticFunction.vonMangoldt x.1 : ℝ) : ℂ) * ((ArithmeticFunction.vonMangoldt x.2 : ℝ) : ℂ)

/-- a finitely supported coefficient sequence has an everywhere convergent L-series -/
theorem summable_of_finite {h : ℕ → ℂ} {S : Finset ℕ} (hS : ∀ n, n ∉ S → h n = 0) (s : ℂ) :
    LSeriesSummable h s := by
  unfold LSeriesSummable
  apply summable_of_ne_finset_zero (s := S)
  intro n hn
  simp [LSeries.term_def, hS n hn]

/-- the L-series of a finitely supported sequence is the finite Dirichlet polynomial -/
theorem LSeries_finite {h : ℕ → ℂ} {S : Finset ℕ} (hS : ∀ n, n ∉ S → h n = 0) (s : ℂ) :
    LSeries h s = ∑ n ∈ S, LSeries.term h s n := by
  unfold LSeries
  apply tsum_eq_sum
  intro n hn
  simp [LSeries.term_def, hS n hn]

/-- each term `n ↦ term h s n` is entire in `s` -/
theorem term_differentiable (h : ℕ → ℂ) (n : ℕ) :
    Differentiable ℂ (fun s => LSeries.term h s n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [LSeries.term_zero]
  · have : (fun s => LSeries.term h s n) = fun s => h n * ((n : ℂ) ^ s)⁻¹ := by
      funext s
      rw [LSeries.term_of_ne_zero hn.ne', div_eq_mul_inv]
    rw [this]
    apply Differentiable.const_mul
    have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
    intro s
    apply DifferentiableAt.inv
    · exact (differentiableAt_id.const_cpow (Or.inl hn'))
    · exact Complex.cpow_ne_zero_iff.mpr (Or.inl hn')

/-- a finitely supported L-series is entire -/
theorem LSeries_finite_differentiable {h : ℕ → ℂ} {S : Finset ℕ} (hS : ∀ n, n ∉ S → h n = 0) :
    Differentiable ℂ (LSeries h) := by
  have : LSeries h = fun s => ∑ n ∈ S, LSeries.term h s n := funext (LSeries_finite hS)
  rw [this]
  exact Differentiable.fun_sum (fun n _ => term_differentiable h n)

/-- **finite change is entire.** If `f` and `g` differ only on the finite set `S`, there is an
entire `P` with `LSeries f s = LSeries g s + P s` at every `s` where `g`'s series converges
absolutely; `f`'s then converges there too. -/
theorem finite_change_entire {f g : ℕ → ℂ} {S : Finset ℕ} (hS : ∀ n, n ∉ S → f n = g n) :
    ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
      ∀ s, LSeriesSummable g s → LSeriesSummable f s ∧ LSeries f s = LSeries g s + P s := by
  have hd : ∀ n, n ∉ S → (f - g) n = 0 := fun n hn => by simp [hS n hn]
  refine ⟨LSeries (f - g), LSeries_finite_differentiable hd, fun s hg => ?_⟩
  have hfg : LSeriesSummable (f - g) s := summable_of_finite hd s
  have hf : LSeriesSummable f s := by
    have := hfg.add hg
    simpa using this
  refine ⟨hf, ?_⟩
  rw [LSeries_sub hf hg]
  ring

/-- **contrast: injectivity in the half-plane of convergence.** Two sequences with `f 0 = g 0 = 0`
and finite abscissa whose L-series agree everywhere are equal; so in the region of convergence
the series does see every coefficient. This is Mathlib's theorem, restated for the map. -/
theorem injective_contrast {f g : ℕ → ℂ} (hf0 : f 0 = 0) (hg0 : g 0 = 0)
    (hf : LSeries.abscissaOfAbsConv f < ⊤) (hg : LSeries.abscissaOfAbsConv g < ⊤)
    (h : LSeries f = LSeries g) : f = g :=
  LSeries_injOn ⟨hf0, hf⟩ ⟨hg0, hg⟩ h

/-- `G` with the single value at `N₀` replaced by `0`: a sequence with one Goldbach exception -/
noncomputable def Gwithout (N₀ : ℕ) (n : ℕ) : ℂ := if n = N₀ then 0 else G n

/-- **a Goldbach exception is invisible to every continuation property of `Φ`.** -/
theorem goldbach_exception_invisible (N₀ : ℕ) :
    ∃ P : ℂ → ℂ, Differentiable ℂ P ∧
      ∀ s, LSeriesSummable (Gwithout N₀) s →
        LSeriesSummable G s ∧ LSeries G s = LSeries (Gwithout N₀) s + P s := by
  apply finite_change_entire (S := {N₀})
  intro n hn
  simp only [Finset.mem_singleton] at hn
  simp [Gwithout, hn]

/-- vacuity check: the exception really changes a coefficient, `G 4 = (log 2)² ≠ 0` -/
theorem G_four : G 4 = ((Real.log 2 : ℝ) : ℂ) ^ 2 := by
  have hA : (Finset.HasAntidiagonal.antidiagonal 4 : Finset (ℕ × ℕ)) = {(0, 4), (1, 3), (2, 2), (3, 1), (4, 0)} := by decide
  have h2 : ArithmeticFunction.vonMangoldt 2 = Real.log 2 :=
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two
  have h3 : ArithmeticFunction.vonMangoldt 3 = Real.log 3 :=
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_three
  simp [G, hA, h2, h3, sq, ArithmeticFunction.vonMangoldt_apply_one]

theorem G_four_ne_zero : G 4 ≠ 0 := by
  rw [G_four]
  have : Real.log 2 ≠ 0 := by
    have := Real.log_pos (by norm_num : (1:ℝ) < 2); linarith
  exact pow_ne_zero 2 (by exact_mod_cast this)

theorem Gwithout_ne : Gwithout 4 ≠ G := by
  intro h
  have := congrFun h 4
  simp [Gwithout] at this
  exact G_four_ne_zero this.symm

end LeanLab.Routes.R0010
