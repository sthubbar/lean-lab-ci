/-
Heath-Brown and Puchta 2002, Integers represented as a sum of primes and powers of two,
arXiv math/0201299. Unit U-1530, run 20261026T0004Z-24325, type DECOMPOSE, file c of three.

Two open inputs of Assembly.lean, split into leaves:

1. Lemma 1's explicit exponents, Section 7, displays 43 to 45 and the choice `h = 16`:
   `E(0.863665) > 109/154` at `ξ = 1.181` and `E(0.722428) > 1/2` at `ξ = 0.905`, with
   `E = ξλ/log 2 - log F(ξ, h)/(h log 2)`. Display 44 says the supremum in `F` is attained at
   `β = 0`, `ρ = 1`, via the moments of display 45.
2. The circle method identity, Section 2: `R(N) = ∫₀¹ S(α)² T(α)^K e(-αN) dα` counts the
   representations `N = p + p' + 2^{ν₁} + ... + 2^{ν_K}`, so `Re R(N) > 0` gives one. In
   Assembly.lean this is the hypothesis `circle` of `theorem1_conditional` and
   `theorem2_conditional`.

Numerics, numpy double precision over all `2^16` residues: `F(1.181, 16) = 4770.13773`,
`log F = 8.4701305`, `E(0.863665) = 0.70779371`, margin over `109/154` is `1.50e-6`;
`F(0.905, 16) = 136.397401`, `E(0.722428) = 0.50000066`, margin over `1/2` is `6.6e-7`.
With the rounded bounds `F ≤ 4770.15` and `F ≤ 136.398` the margins are `2.66e-7` over
`109/154 + 10^-6` and `1.63e-7` over `1/2 + 10^-7`. These agree with the lab's gen/half78.out.
A random test of display 44, `h ≤ 6`, 300 random `β, ρ` per case, found no `avg` above the
value at `β = 0, ρ = 1`.

Page numbers are not visible in the arXiv text read for this unit; Section and display numbers
are given. The paper copy was NOT FOUND in either lab location; the text used is arXiv
math/0201299 through WebFetch, 2026-10-26.

ASSEMBLY, real proofs, CONDITIONAL ON the leaves: `F_eq_Fzero`, `lemma1_E_uncond`,
`lemma1_E_grh`, `circle_positive`.

AI-written Lean code, Claude, 2026-10-26. Binary Goldbach is OPEN; nothing here is progress on it.
-/
import LeanLab.HeathBrownPuchta.Decomp1530b
import LeanLab.Linnik.Statements

namespace LeanLab.HeathBrownPuchta.Decomp1530c

open Finset Real LeanLab.HeathBrownPuchta.Decomp1530a LeanLab.HeathBrownPuchta.Decomp1530b
open LeanLab.Linnik
attribute [local instance] Classical.propDecidable
set_option maxHeartbeats 2000000

/-- Display 44: `F(ξ, h)` at `β = 0`, `ρ = 1`, written with cosines,
`2^{-h} Σ_{0 ≤ r < 2^h} exp(ξ Σ_{0 ≤ n < h} cos(2π r 2^n / 2^h))`. -/
noncomputable def Fzero (ξ : ℝ) (hh : ℕ) : ℝ :=
  (1 / 2 ^ hh) * ∑ r ∈ range (2 ^ hh),
    Real.exp (ξ * ∑ n ∈ range hh, Real.cos (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh)))

/-- The Section 7 exponent `E = ξλ/log 2 - log F/(h log 2)`. -/
noncomputable def Emodel (ξ lam F0 : ℝ) (hh : ℕ) : ℝ :=
  ξ * lam / Real.log 2 - Real.log F0 / (hh * Real.log 2)

/-- `Σ 2^{a_i} - Σ 2^{b_j}` for exponent tuples `a`, `b`, display 45. -/
def Dsum {m k : ℕ} (ab : (Fin m → ℕ) × (Fin k → ℕ)) : ℤ :=
  ∑ i, (2 : ℤ) ^ ab.1 i - ∑ j, (2 : ℤ) ^ ab.2 j

/-- The moment `Σ_{0 ≤ r < 2^h} T_h(x_r)^m conj(T_h(x_r))^k`, `x_r = (β + r)/2^h`, display 45. -/
noncomputable def moment (hh m k : ℕ) (β : ℝ) : ℂ :=
  ∑ r ∈ range (2 ^ hh), TL hh ((β + r) / 2 ^ hh) ^ m *
    (starRingEnd ℂ) (TL hh ((β + r) / 2 ^ hh)) ^ k

/-- The representations `N = p + p' + 2^{ν₁} + ... + 2^{ν_K}`, `ϖN < p, p' ≤ N`,
`1 ≤ ν_i ≤ L`, Section 2. -/
noncomputable def reps (N : ℕ) (w : ℝ) (L K : ℕ) : Finset (ℕ × ℕ × (Fin K → ℕ)) :=
  (primesIn N w ×ˢ (primesIn N w ×ˢ Fintype.piFinset fun _ => Icc 1 L)).filter
    fun x => x.1 + x.2.1 + ∑ i, 2 ^ (x.2.2 i) = N

/-- `R(N) = ∫₀¹ S(α)² T(α)^K e(-αN) dα`, Section 2. -/
noncomputable def Rint (N : ℕ) (w : ℝ) (L K : ℕ) : ℂ :=
  ∫ α in (0 : ℝ)..1, Sp N w α ^ 2 * Tp L α ^ K * ee (-(α * N))

/-! ### Leaves: display 44 -/

/-- LEAF. Unit U-1530. At `α = r/2^h`, `Re T_h(α) = Σ_{0 ≤ n < h} cos(2π r 2^n/2^h)`;
Section 7, display 44. -/
theorem TL_re_at (hh r : ℕ) :
    (TL hh ((r : ℝ) / 2 ^ hh)).re =
      ∑ n ∈ range hh, Real.cos (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh)) := by
  unfold TL ee
  simp only [Complex.re_sum]
  apply sum_congr rfl
  intro n hn
  rw [Complex.exp_re]
  simp [-Complex.ofReal_pow]
  congr 1
  ring

/-- The finite character orthogonality used in paper page 31, display 45. -/
theorem ee_grid_sum (d : ℕ) (hd : 0 < d) (D : ℤ) (β : ℝ) :
    ∑ r ∈ range d, ee ((β + r) * D / d) =
      if (d : ℤ) ∣ D then (d : ℂ) * ee (β * D / d) else 0 := by
  have hdr : (d : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  have hadd (x y : ℝ) : ee (x + y) = ee x * ee y := by
    unfold ee
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
  have hn (x : ℝ) (n : ℕ) : ee ((n : ℝ) * x) = ee x ^ n := by
    unfold ee
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  have hint (n : ℤ) : ee (n : ℝ) = 1 := by simpa [ee] using ee_int_shift 0 n
  have hone : ee ((D : ℝ) / d) = 1 ↔ (d : ℤ) ∣ D := by
    constructor
    · intro h
      obtain ⟨k, hk⟩ := Complex.exp_eq_one_iff.mp h
      have hi := congrArg Complex.im hk
      norm_num [Complex.mul_im, Complex.mul_re] at hi
      have hh : (D : ℝ) = (d : ℝ) * k := by
        field_simp at hi
        nlinarith [Real.pi_pos]
      exact ⟨k, by exact_mod_cast hh⟩
    · rintro ⟨k, hk⟩
      rw [hk]
      push_cast
      rw [mul_div_cancel_left₀ _ hdr]
      exact hint k
  have hroot : ee ((D : ℝ) / d) ^ d = 1 := by
    rw [← hn, mul_div_cancel₀ _ hdr]
    exact hint D
  have heq : ∑ r ∈ range d, ee ((β + r) * D / d) =
      ee (β * D / d) * ∑ r ∈ range d, ee ((D : ℝ) / d) ^ r := by
    rw [mul_sum]
    apply sum_congr rfl
    intro r hr
    rw [← hn, ← hadd]
    congr 1
    ring
  rw [heq]
  by_cases hdiv : (d : ℤ) ∣ D
  · rw [if_pos hdiv, hone.mpr hdiv]
    simp [mul_comm]
  · rw [if_neg hdiv]
    have hne := mt hone.mp hdiv
    have hg := geom_sum_mul (ee ((D : ℝ) / d)) d
    rw [hroot, sub_self] at hg
    have hzero := (mul_eq_zero.mp hg).resolve_right (sub_ne_zero.mpr hne)
    rw [hzero, mul_zero]

/-- LEAF. Unit U-1530. The moment formula: the moment at `β` equals `2^h` times the sum of
`e(β D/2^h)` over the exponent tuples `a ∈ [0,h)^m`, `b ∈ [0,h)^k` whose difference
`D = Σ 2^{a_i} - Σ 2^{b_j}` is divisible by `2^h`; Section 7, display 45. -/
theorem moment_formula (hh m k : ℕ) (β : ℝ) :
    moment hh m k β = 2 ^ hh * ∑ ab ∈ ((Fintype.piFinset fun _ : Fin m => range hh) ×ˢ
        (Fintype.piFinset fun _ : Fin k => range hh)).filter (fun ab => (2 : ℤ) ^ hh ∣ Dsum ab),
      ee (β * (Dsum ab : ℝ) / 2 ^ hh) := by
  classical
  have hadd (x y : ℝ) : ee (x + y) = ee x * ee y := by
    unfold ee
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
  have hc (x : ℝ) : (starRingEnd ℂ) (ee x) = ee (-x) := by
    unfold ee
    rw [← Complex.exp_conj]
    congr 1
    simp [map_ofNat]
  have hprod (α : ℝ) (j : ℕ) (a : Fin j → ℕ) :
      (∏ i, ee (α * 2 ^ (a i))) = ee (α * ∑ i, (2 : ℝ) ^ (a i)) := by
    unfold ee
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    simp only [mul_sum]
  have point (r : ℕ) :
      TL hh ((β + r) / 2 ^ hh) ^ m * (starRingEnd ℂ) (TL hh ((β + r) / 2 ^ hh)) ^ k =
      ∑ a ∈ Fintype.piFinset (fun _ : Fin m => range hh),
        ∑ b ∈ Fintype.piFinset (fun _ : Fin k => range hh),
          ee ((β + r) * (Dsum (a, b) : ℝ) / 2 ^ hh) := by
    unfold TL
    simp only [map_sum, Finset.sum_pow', map_prod, hc, sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    apply sum_congr rfl
    intro b hb
    have hneg : (∏ i, ee (-(((β + r) / 2 ^ hh) * 2 ^ (b i)))) =
        ee (-((β + r) / 2 ^ hh) * ∑ i, (2 : ℝ) ^ (b i)) := by
      convert hprod (-((β + r) / 2 ^ hh)) k b using 1
      apply prod_congr rfl
      intro i hi
      congr 1
      ring
    rw [hprod, hneg, ← hadd]
    congr 1
    unfold Dsum
    push_cast
    ring
  unfold moment
  simp_rw [point]
  calc
    _ = ∑ a ∈ Fintype.piFinset (fun _ : Fin m => range hh),
        ∑ b ∈ Fintype.piFinset (fun _ : Fin k => range hh),
          ∑ r ∈ range (2 ^ hh), ee ((β + r) * (Dsum (a, b) : ℝ) / 2 ^ hh) := by
      rw [sum_comm]
      apply sum_congr rfl
      intro a ha
      rw [sum_comm]
    _ = ∑ ab ∈ (Fintype.piFinset (fun _ : Fin m => range hh)) ×ˢ
        (Fintype.piFinset (fun _ : Fin k => range hh)),
          if (2 : ℤ) ^ hh ∣ Dsum ab then (2 : ℂ) ^ hh * ee (β * (Dsum ab : ℝ) / 2 ^ hh) else 0 := by
      rw [sum_product]
      apply sum_congr rfl
      intro a ha
      apply sum_congr rfl
      intro b hb
      simpa using ee_grid_sum (2 ^ hh) (by positivity) (Dsum (a, b)) β
    _ = _ := by rw [sum_filter, mul_sum]; apply sum_congr rfl; intro ab hab; split_ifs <;> simp_all

/-- LEAF. Unit U-1530. Every moment is at most the moment at `β = 0` in absolute value, and that
one is real: `|S(n, m, h, β)| ≤ S(n, m, h, 0)`; Section 7, after display 45. -/
theorem moment_abs_le (hh m k : ℕ) (β : ℝ) :
    ‖moment hh m k β‖ ≤ (moment hh m k 0).re ∧ (moment hh m k 0).im = 0 := by
  classical
  let s := ((Fintype.piFinset fun _ : Fin m => range hh) ×ˢ
    (Fintype.piFinset fun _ : Fin k => range hh)).filter (fun ab => (2 : ℤ) ^ hh ∣ Dsum ab)
  have hzero : moment hh m k 0 = ((2 ^ hh * s.card : ℕ) : ℂ) := by
    rw [moment_formula]
    change (2 : ℂ) ^ hh * (∑ ab ∈ s, ee (0 * (Dsum ab : ℝ) / 2 ^ hh)) = _
    simp [ee]
  rw [hzero]
  constructor
  · rw [moment_formula, Complex.natCast_re]
    change ‖(2 : ℂ) ^ hh * ∑ ab ∈ s, ee (β * (Dsum ab : ℝ) / 2 ^ hh)‖ ≤ _
    have hnorm (x : ℝ) : ‖ee x‖ = 1 := by simp [ee, Complex.norm_exp]
    calc
      _ = (2 : ℝ) ^ hh * ‖∑ ab ∈ s, ee (β * (Dsum ab : ℝ) / 2 ^ hh)‖ := by simp [norm_mul]
      _ ≤ (2 : ℝ) ^ hh * ∑ ab ∈ s, ‖ee (β * (Dsum ab : ℝ) / 2 ^ hh)‖ :=
        mul_le_mul_of_nonneg_left (norm_sum_le _ _) (by positivity)
      _ = ((2 ^ hh * s.card : ℕ) : ℝ) := by simp [hnorm]
  · simp only [Complex.natCast_im]

/-- The real power moment comparison used on paper pages 30 and 31, displays 45 and 46. -/
theorem re_power_sum_le (hh n : ℕ) (β : ℝ) {ρ : ℂ} (hρ : ‖ρ‖ = 1) :
    ∑ r ∈ range (2 ^ hh), (ρ * TL hh ((β + r) / 2 ^ hh)).re ^ n ≤
      ∑ r ∈ range (2 ^ hh), (TL hh ((r : ℝ) / 2 ^ hh)).re ^ n := by
  have htwo (z : ℂ) : (2 : ℂ) * (z.re : ℂ) = z + (starRingEnd ℂ) z := by
    simpa only [Complex.ofReal_mul, Complex.ofReal_ofNat] using (Complex.add_conj z).symm
  have hpoly (ρ : ℂ) (β : ℝ) :
      (2 : ℂ) ^ n * ((∑ r ∈ range (2 ^ hh), (ρ * TL hh ((β + r) / 2 ^ hh)).re ^ n : ℝ) : ℂ) =
        ∑ j ∈ range (n + 1), (n.choose j : ℂ) * ρ ^ j * (starRingEnd ℂ) ρ ^ (n - j) *
          moment hh j (n - j) β := by
    push_cast
    rw [mul_sum]
    simp_rw [← mul_pow, htwo, map_mul, add_pow, mul_pow]
    rw [sum_comm]
    apply sum_congr rfl
    intro j hj
    unfold moment
    rw [mul_sum]
    apply sum_congr rfl
    intro r hr
    ring
  have hleft := congrArg Complex.re (hpoly ρ β)
  have hright := congrArg Complex.re (hpoly 1 0)
  have hterm (j : ℕ) :
      ((n.choose j : ℂ) * ρ ^ j * (starRingEnd ℂ) ρ ^ (n - j) * moment hh j (n - j) β).re ≤
        (n.choose j : ℝ) * (moment hh j (n - j) 0).re := by
    calc
      _ ≤ ‖(n.choose j : ℂ) * ρ ^ j * (starRingEnd ℂ) ρ ^ (n - j) * moment hh j (n - j) β‖ :=
        Complex.re_le_norm _
      _ = (n.choose j : ℝ) * ‖moment hh j (n - j) β‖ := by simp [norm_mul, norm_pow, hρ]
      _ ≤ _ := mul_le_mul_of_nonneg_left (moment_abs_le hh j (n - j) β).1 (Nat.cast_nonneg _)
  have hsum := sum_le_sum (s := range (n + 1)) (fun j hj => hterm j)
  have hnr : (0 : ℝ) < 2 ^ n := by positivity
  have hcast : (2 : ℂ) ^ n = Complex.ofReal ((2 : ℝ) ^ n) := by norm_cast
  rw [hcast, Complex.re_ofReal_mul, Complex.ofReal_re, Complex.re_sum] at hleft
  rw [hcast, Complex.re_ofReal_mul, Complex.ofReal_re, Complex.re_sum] at hright
  simp only [map_one, one_pow, mul_one, one_mul, zero_add,
    Complex.mul_re, Complex.natCast_re, Complex.natCast_im, zero_mul, sub_zero] at hright
  nlinarith

/-- LEAF. Unit U-1530. For `ξ ≥ 0` and `|ρ| = 1` the inner average of display 43 is at most its
value at `β = 0`, `ρ = 1`; proof by the power series of `exp`, `Re w = (w + conj w)/2` and
`moment_abs_le`; Section 7, display 44. -/
theorem avg_le_avg_zero (ξ : ℝ) (hξ : 0 ≤ ξ) {ρ : ℂ} (hρ : ‖ρ‖ = 1) (hh : ℕ) (β : ℝ) :
    avg ξ ρ hh β ≤ avg ξ 1 hh 0 := by
  have hs (f : ℕ → ℝ) :
      HasSum (fun n : ℕ => ∑ r ∈ range (2 ^ hh), (ξ * f r) ^ n / n.factorial)
        (∑ r ∈ range (2 ^ hh), Real.exp (ξ * f r)) := by
    apply hasSum_sum
    intro r hr
    simpa only [Real.exp_eq_exp_ℝ] using NormedSpace.expSeries_div_hasSum_exp (ξ * f r)
  have hfactor (f : ℕ → ℝ) (n : ℕ) :
      (∑ r ∈ range (2 ^ hh), (ξ * f r) ^ n / n.factorial) =
        (ξ ^ n / n.factorial) * ∑ r ∈ range (2 ^ hh), f r ^ n := by
    rw [mul_sum]
    apply sum_congr rfl
    intro r hr
    rw [mul_pow]
    ring
  have ht (n : ℕ) :
      (∑ r ∈ range (2 ^ hh), (ξ * (ρ * TL hh ((β + r) / 2 ^ hh)).re) ^ n / n.factorial) ≤
      ∑ r ∈ range (2 ^ hh), (ξ * (TL hh ((r : ℝ) / 2 ^ hh)).re) ^ n / n.factorial := by
    rw [hfactor, hfactor]
    exact mul_le_mul_of_nonneg_left (re_power_sum_le hh n β hρ) (by positivity)
  have he := hasSum_le ht (hs (fun r => (ρ * TL hh ((β + r) / 2 ^ hh)).re))
    (hs (fun r => (TL hh ((r : ℝ) / 2 ^ hh)).re))
  unfold avg
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [one_mul, zero_add] using he

/-- LEAF. Unit U-1530. `F(ξ, h) ≥ 1` at `β = 0`, `ρ = 1`: the cosines average to `0` over `r`
for each `n < h`, so Jensen gives the bound; Section 7, display 44. -/
theorem Fzero_ge_one (ξ : ℝ) (hh : ℕ) : 1 ≤ Fzero ξ hh := by
  have hd : (0 : ℝ) < 2 ^ hh := by positivity
  have hcos (n : ℕ) (hn : n < hh) :
      ∑ r ∈ range (2 ^ hh), Real.cos (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh)) = 0 := by
    let a : ℝ := 2 * π * 2 ^ n / 2 ^ hh
    have hlt : (2 : ℝ) ^ n < 2 ^ hh := (pow_lt_pow_right₀ (by norm_num) hn)
    have ha0 : 0 < a / 2 := by dsimp [a]; positivity
    have hapi : a / 2 < π := by
      dsimp [a]
      rw [div_div, div_lt_iff₀ (by positivity : (0 : ℝ) < 2 ^ hh * 2)]
      nlinarith [Real.pi_pos]
    have hs : Real.sin ((2 : ℝ) ^ n * π) = 0 := by
      exact_mod_cast Real.sin_nat_mul_pi (2 ^ n)
    have hangle : ((2 ^ hh : ℕ) : ℝ) * a / 2 = (2 : ℝ) ^ n * π := by
      dsimp [a]
      push_cast
      field_simp
    have hformula := Real.sin_mul_sum_cos (2 ^ hh) a 0
    rw [hangle, hs, zero_mul] at hformula
    have hsin : Real.sin (a / 2) ≠ 0 := (Real.sin_pos_of_pos_of_lt_pi ha0 hapi).ne'
    have hsum := (mul_eq_zero.mp hformula).resolve_left hsin
    simp only [add_zero] at hsum
    convert hsum using 1
    apply sum_congr rfl
    intro r hr
    congr 1
    dsimp [a]
    ring
  have hzero : ∑ r ∈ range (2 ^ hh), ∑ n ∈ range hh,
      Real.cos (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh)) = 0 := by
    rw [sum_comm]
    exact sum_eq_zero fun n hn => hcos n (mem_range.mp hn)
  have he : (2 : ℝ) ^ hh ≤ ∑ r ∈ range (2 ^ hh),
      Real.exp (ξ * ∑ n ∈ range hh, Real.cos (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh))) := by
    calc
      _ = ∑ r ∈ range (2 ^ hh), (1 + ξ * ∑ n ∈ range hh,
          Real.cos (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh))) := by
        rw [sum_add_distrib, ← mul_sum, hzero]
        simp
      _ ≤ _ := sum_le_sum fun r hr => by
        have hx := Real.add_one_le_exp (ξ * ∑ n ∈ range hh, Real.cos (2 * π * ((r : ℝ) * 2 ^ n / 2 ^ hh)))
        linarith
  unfold Fzero
  rw [one_div_mul_eq_div, le_div_iff₀ hd, one_mul]
  exact he

/-! ### Leaves: the explicit values at `h = 16` -/

/-- LEAF. Unit U-1530. `F(1.181, 16) ≤ 4770.15`, a finite sum over `2^16` residues, numpy value
`4770.13773`; Section 7, the choice `h = 16`, `ξ = 1.181`. -/
theorem Fzero_uncond : Fzero (1181 / 1000) 16 ≤ 477015 / 100 := by
  sorry

/-- LEAF. Unit U-1530. `F(0.905, 16) ≤ 136.398`, a finite sum over `2^16` residues, numpy value
`136.397401`; Section 7, the choice `h = 16`, `ξ = 0.905`. -/
theorem Fzero_grh : Fzero (905 / 1000) 16 ≤ 136398 / 1000 := by
  sorry

/-- LEAF. Unit U-1530. `1.181 · 0.863665/log 2 - log 4770.15/(16 log 2) > 109/154 + 10^-6`,
double precision margin `2.66e-7`; Section 7, `E(0.863665) > 109/154`. -/
theorem E_num_uncond :
    109 / 154 + 1 / 10 ^ 6 < Emodel (1181 / 1000) (863665 / 1000000) (477015 / 100) 16 := by
  unfold Emodel
  norm_num only [Nat.cast_ofNat]
  have hl : Real.log (477015 / 100) < (8470135 / 1000000 : ℝ) := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    have hh := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 8470135 / 1000000 by norm_num) 42
    have hsum : (477015 / 100 : ℝ) < ∑ i ∈ range 42, (8470135 / 1000000 : ℝ) ^ i / i.factorial := by
      norm_num [sum_range_succ, Nat.factorial]
    exact hsum.trans_le hh
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb := Real.log_two_lt_d9
  have he : (109 / 154 + 1 / 10 ^ 6 : ℝ) * (16 * Real.log 2) < 16 * (1181 / 1000) * (863665 / 1000000) - Real.log (477015 / 100) := by nlinarith
  have hd := (lt_div_iff₀ (show 0 < 16 * Real.log 2 by positivity)).mpr he
  convert hd using 1 <;> norm_num <;> field_simp <;> ring

/-- LEAF. Unit U-1530. `0.905 · 0.722428/log 2 - log 136.398/(16 log 2) > 1/2 + 10^-7`,
double precision margin `1.63e-7`; Section 7, `E(0.722428) > 1/2`. -/
theorem E_num_grh :
    1 / 2 + 1 / 10 ^ 7 < Emodel (905 / 1000) (722428 / 1000000) (136398 / 1000) 16 := by
  unfold Emodel
  norm_num only [Nat.cast_ofNat]
  have hl : Real.log (136398 / 1000) < (4915578 / 1000000 : ℝ) := by
    apply (Real.log_lt_iff_lt_exp (by norm_num)).mpr
    have hh := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 4915578 / 1000000 by norm_num) 32
    have hsum : (136398 / 1000 : ℝ) < ∑ i ∈ range 32, (4915578 / 1000000 : ℝ) ^ i / i.factorial := by
      norm_num [sum_range_succ, Nat.factorial]
    exact hsum.trans_le hh
  have h2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hb := Real.log_two_lt_d9
  have he : (1 / 2 + 1 / 10 ^ 7 : ℝ) * (16 * Real.log 2) < 16 * (905 / 1000) * (722428 / 1000000) - Real.log (136398 / 1000) := by nlinarith
  have hd := (lt_div_iff₀ (show 0 < 16 * Real.log 2 by positivity)).mpr he
  convert hd using 1 <;> norm_num <;> field_simp <;> ring

/-! ### Leaf: the circle method identity -/

/-- LEAF. Unit U-1530. `R(N) = ∫₀¹ S(α)² T(α)^K e(-αN) dα` equals the number of
representations `N = p + p' + 2^{ν₁} + ... + 2^{ν_K}` with `ϖN < p, p' ≤ N`, `1 ≤ ν_i ≤ L`;
Section 2, by orthogonality. -/
theorem circle_count (N : ℕ) (w : ℝ) (L K : ℕ) : Rint N w L K = ((reps N w L K).card : ℂ) := by
  classical
  have hadd (x y : ℝ) : ee (x + y) = ee x * ee y := by
    unfold ee
    rw [Complex.ofReal_add, mul_add, Complex.exp_add]
  have hprod (α : ℝ) (ν : Fin K → ℕ) :
      (∏ i, ee (α * 2 ^ (ν i))) = ee (α * ∑ i, (2 : ℝ) ^ (ν i)) := by
    unfold ee
    rw [← Complex.exp_sum]
    congr 1
    push_cast
    simp only [mul_sum]
  have hexp (n : ℤ) : Continuous (fun α : ℝ => ee (α * n)) := by unfold ee; fun_prop
  have heq (α : ℝ) : Sp N w α ^ 2 * Tp L α ^ K * ee (-(α * N)) =
      ∑ p ∈ primesIn N w, ∑ q ∈ primesIn N w,
        ∑ ν ∈ Fintype.piFinset (fun _ : Fin K => Icc 1 L),
          ee (α * (((p : ℤ) + q + ∑ i, (2 : ℤ) ^ (ν i) - N : ℤ) : ℝ)) := by
    unfold Sp Tp
    rw [pow_two, Finset.sum_pow']
    simp only [sum_mul, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro p hp
    rw [sum_comm]
    apply sum_congr rfl
    intro q hq
    apply sum_congr rfl
    intro ν hν
    rw [hprod, ← hadd, ← hadd, ← hadd]
    congr 1
    push_cast
    ring
  have hν (p q : ℕ) :
      (∫ α in (0 : ℝ)..1, ∑ ν ∈ Fintype.piFinset (fun _ : Fin K => Icc 1 L),
        ee (α * (((p : ℤ) + q + ∑ i, (2 : ℤ) ^ (ν i) - N : ℤ) : ℝ))) =
      ∑ ν ∈ Fintype.piFinset (fun _ : Fin K => Icc 1 L),
        ∫ α in (0 : ℝ)..1, ee (α * (((p : ℤ) + q + ∑ i, (2 : ℤ) ^ (ν i) - N : ℤ) : ℝ)) :=
    intervalIntegral.integral_finsetSum (fun ν hν => (hexp _).intervalIntegrable 0 1)
  have hq (p : ℕ) :
      (∫ α in (0 : ℝ)..1, ∑ q ∈ primesIn N w,
        ∑ ν ∈ Fintype.piFinset (fun _ : Fin K => Icc 1 L),
          ee (α * (((p : ℤ) + q + ∑ i, (2 : ℤ) ^ (ν i) - N : ℤ) : ℝ))) =
      ∑ q ∈ primesIn N w, ∫ α in (0 : ℝ)..1,
        ∑ ν ∈ Fintype.piFinset (fun _ : Fin K => Icc 1 L),
          ee (α * (((p : ℤ) + q + ∑ i, (2 : ℤ) ^ (ν i) - N : ℤ) : ℝ)) := by
    apply intervalIntegral.integral_finsetSum
    intro q hq
    apply Continuous.intervalIntegrable
    unfold ee
    fun_prop
  unfold Rint
  simp_rw [heq]
  rw [intervalIntegral.integral_finsetSum (fun p hp => by
    apply Continuous.intervalIntegrable
    unfold ee
    fun_prop)]
  simp_rw [hq, hν, orth]
  have hz (p q : ℕ) (ν : Fin K → ℕ) :
      ((p : ℤ) + q + ∑ i, (2 : ℤ) ^ ν i - N = 0) ↔ p + q + ∑ i, 2 ^ ν i = N := by
    rw [sub_eq_zero]
    exact_mod_cast (Iff.rfl : p + q + ∑ i, 2 ^ ν i = N ↔ p + q + ∑ i, 2 ^ ν i = N)
  simp_rw [hz]
  unfold reps
  simp only [Finset.card_eq_sum_ones, sum_filter, sum_product, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]

/-! ### Assemblies -/

/-- ASSEMBLY, CONDITIONAL ON `TL_re_at`, `avg_le_avg_zero` and `avg_le_F` of file a: display 44,
`F(ξ, h)` equals its value at `β = 0`, `ρ = 1`, for `ξ ≥ 0`. -/
theorem F_eq_Fzero {ξ : ℝ} (hξ : 0 ≤ ξ) (hh : ℕ) : F ξ hh = Fzero ξ hh := by
  have h0 : avg ξ 1 hh 0 = Fzero ξ hh := by
    unfold avg Fzero
    congr 1
    refine sum_congr rfl fun r _ => ?_
    rw [one_mul, zero_add, TL_re_at]
  rw [← h0]
  apply le_antisymm
  · haveI : Nonempty {p : ℝ × ℂ // p.1 ∈ Set.Icc (0 : ℝ) 1 ∧ ‖p.2‖ = 1} :=
      ⟨⟨(0, 1), ⟨le_rfl, zero_le_one⟩, by simp⟩⟩
    exact ciSup_le fun p => avg_le_avg_zero ξ hξ p.2.2 hh p.1.1
  · exact avg_le_F ξ hh ⟨le_rfl, zero_le_one⟩ (by simp)

theorem Emodel_anti {ξ lam F0 F1 : ℝ} {hh : ℕ} (hhp : 0 < hh) (hF0 : 0 < F0) (hF : F0 ≤ F1) :
    Emodel ξ lam F1 hh ≤ Emodel ξ lam F0 hh := by
  unfold Emodel
  have hl : 0 < (hh : ℝ) * Real.log 2 :=
    mul_pos (by exact_mod_cast hhp) (Real.log_pos (by norm_num))
  have := Real.log_le_log hF0 hF
  have : Real.log F0 / (hh * Real.log 2) ≤ Real.log F1 / (hh * Real.log 2) :=
    div_le_div_of_nonneg_right this hl.le
  linarith

/-- ASSEMBLY, CONDITIONAL ON the leaves of `F_eq_Fzero` and on `Fzero_ge_one`, `Fzero_uncond`,
`E_num_uncond`: Lemma 1's unconditional exponent, `E(0.863665) > 109/154 + 10^-6` at
`ξ = 1.181`, `h = 16`, Section 7. -/
theorem lemma1_E_uncond :
    109 / 154 + 1 / 10 ^ 6 < Emodel (1181 / 1000) (863665 / 1000000) (F (1181 / 1000) 16) 16 := by
  rw [F_eq_Fzero (by norm_num)]
  have h1 := Fzero_ge_one (1181 / 1000) 16
  exact lt_of_lt_of_le E_num_uncond
    (Emodel_anti (by norm_num) (by linarith) Fzero_uncond)

/-- ASSEMBLY, CONDITIONAL ON the leaves of `F_eq_Fzero` and on `Fzero_ge_one`, `Fzero_grh`,
`E_num_grh`: Lemma 1's GRH exponent, `E(0.722428) > 1/2 + 10^-7` at `ξ = 0.905`, `h = 16`,
Section 7. -/
theorem lemma1_E_grh :
    1 / 2 + 1 / 10 ^ 7 < Emodel (905 / 1000) (722428 / 1000000) (F (905 / 1000) 16) 16 := by
  rw [F_eq_Fzero (by norm_num)]
  have h1 := Fzero_ge_one (905 / 1000) 16
  exact lt_of_lt_of_le E_num_grh
    (Emodel_anti (by norm_num) (by linarith) Fzero_grh)

/-- ASSEMBLY, CONDITIONAL ON `circle_count`: if `Re R(N) > 0` then `N` is two primes plus
exactly `K` powers of 2 with exponents at least 1, the identity used in Section 6 and the
`circle` hypothesis of Assembly.lean. -/
theorem circle_positive {N : ℕ} {w : ℝ} {L K : ℕ} (hR : 0 < (Rint N w L K).re) :
    LinnikExact K N := by
  rw [circle_count, Complex.natCast_re] at hR
  have hc : 0 < (reps N w L K).card := by exact_mod_cast hR
  obtain ⟨x, hx⟩ := Finset.card_pos.1 hc
  unfold reps at hx
  simp only [Finset.mem_filter, Finset.mem_product, Fintype.mem_piFinset] at hx
  obtain ⟨⟨hp, hq, hν⟩, hsum⟩ := hx
  unfold primesIn at hp hq
  simp only [Finset.mem_filter] at hp hq
  exact ⟨x.1, x.2.1, hp.2.1, hq.2.1, x.2.2, fun i => (Finset.mem_Icc.1 (hν i)).1, hsum.symm⟩

end LeanLab.HeathBrownPuchta.Decomp1530c
