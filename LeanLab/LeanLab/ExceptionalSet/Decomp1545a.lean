/-
P0095 W. C. Lu 2010, Exceptional set of Goldbach number, J. Number Theory 130, 2359-2392.
Unit U-1545, run 20261026T0808Z-17522, ARCHITECT DECOMPOSE, track T1.

File a of three: equation (39) on p. 2369,
  `Σ_{q ≤ P} W₀(q, 4πN/(qQ), N) ≪ 1`,  `W₀(q, T, x) = Σ*_{χ mod q} Σ_{|γ| ≤ T} x^{β-1}`,
with `P = N^c`, `c = 0.1215` from p. 2360 and `Q = N^{3/4}` from p. 2361. Lu derives it in one line,
"using the last inequality and the usual method", from the density estimate (38) of Huxley and
Jutila, `Σ_{q ≤ x} N*(α, T, q) ≪ (x² T)^{(12/5+ε)(1-α)}` for `1/2 ≤ α ≤ 1`, `T ≥ 1`.
The lab's `Lu2010Formula63.Mass39` is the restriction of (39) to the finite exponents of (63).

This file writes the usual method out as LEAF lemmas over a finite family of zeros `i ∈ Z`, each
with a modulus `q i`, real part `β i` and ordinate `γ i`, and proves two assemblies:
* `eq39_of_region`: `Σ_Z N^{β-1} ≤ C` CONDITIONAL ON the leaves and on `HypRegion`, a density
  count `#{β ≥ α} ≤ A Y^{1-α}` for the whole region `q ≤ P`, `q |γ| ≤ 4π N^{1/4}`, with
  `Y = (8 P K)^κ`, `K = 4π N^{1/4}`, `κ = 12/5 + 1/100`, and a Riemann-von Mangoldt total count.
* `eq39_of_dyadic`: `Σ_Z N^{β-1} ≤ C log N` CONDITIONAL ON the leaves and on `HypDyadic`, which
  takes (38) itself for the family, the zero-free region `β ≤ 1 - c₁/log N` off at most one
  exceptional zero, and the same total count. Splitting `q` into dyadic blocks loses a factor
  `1/(1-α)` near `α = 1`, and the result is `≪ log N`, not `≪ 1`. See QUESTION Q-1545a in
  STATEMENTS.md: (38) as printed seems to need the region form to give (39) as printed.

The exponent margin: `κ (c + 1/4) = 2.41 · 0.3715 = 0.895315 < 1`, so `δ = 0.104685 > 0`.

Reuses the PROVED `layer_cake_sum` and `count_integral_le` of Decomp1524c; no leaf of Decomp1524*,
Decomp1539a or Li2000Lemmas is restated here.

AI wrote this Lean code, Claude, unit U-1545. Checked only by the Lean kernel.
KNOWN mathematics. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.ExceptionalSet.Decomp1524c

namespace LeanLab.ExceptionalSet.Decomp1545a

open Real MeasureTheory Finset

attribute [local instance] Classical.propDecidable

/-! ### Parameters, pp. 2360, 2361, 2369 -/

/-- `c = 0.1215`, p. 2360. -/
noncomputable def cLu : ℝ := 0.1215

/-- `κ = 12/5 + ε` of (37) and (38) with `ε = 1/100`. -/
noncomputable def kap : ℝ := 12 / 5 + 1 / 100

/-- The saving `δ = 1 - κ (c + 1/4) = 0.104685`. -/
noncomputable def del : ℝ := 1 - kap * (cLu + 1 / 4)

/-- `P = N^c`. -/
noncomputable def PP (N : ℝ) : ℝ := N ^ cLu

/-- `Q = N^{3/4}`, p. 2361. -/
noncomputable def QQ (N : ℝ) : ℝ := N ^ (3 / 4 : ℝ)

/-- `K = 4π N^{1/4}`, so that the height `4πN/(qQ)` of (39) is `K/q`. -/
noncomputable def KK (N : ℝ) : ℝ := 4 * π * N ^ (1 / 4 : ℝ)

/-- The height `4πN/(qQ)` in (39). -/
noncomputable def TT (N : ℝ) (q : ℕ) : ℝ := 4 * π * N / (q * QQ N)

/-- `Y = (8 P K)^κ`, the size of the region in the density count. -/
noncomputable def YY (N : ℝ) : ℝ := (8 * PP N * KK N) ^ kap

theorem kap_pos : 0 < kap := by norm_num [kap]

theorem del_pos : 0 < del := by norm_num [del, kap, cLu]

/-! ### The hypothesis bundles -/

/-- Display (38) of p. 2369 for a finite family of zeros: for `x ≥ 1`, `T ≥ 1`, `1/2 ≤ α ≤ 1`,
the zeros with `q ≤ x`, `|γ| ≤ T`, `β ≥ α` number at most `A (x² T)^{κ(1-α)}`, with `ε = 1/100`.
For the zeros of `L(s, χ)`, `χ` primitive, this is Huxley and Jutila, CITED, not proved in the
lab; Lu p. 2369 gives [7,13], [6, p. 269], Theorem 1 of [4], Theorem 12.2 of [9]. -/
def Density38 {ι : Type*} (Z : Finset ι) (q : ι → ℕ) (β γ : ι → ℝ) (A : ℝ) : Prop :=
  ∀ x T α : ℝ, 1 ≤ x → 1 ≤ T → 1 / 2 ≤ α → α ≤ 1 →
    ((Z.filter (fun i => (q i : ℝ) ≤ x ∧ |γ i| ≤ T ∧ α ≤ β i)).card : ℝ) ≤
      A * (x ^ 2 * T) ^ (kap * (1 - α))

/-- The region form of the density count used by `eq39_of_region`: `β ≤ 1` and, for
`1/2 ≤ α ≤ 1`, `#{β ≥ α} ≤ A Y^{1-α}` with `Y = (8PK)^κ`, plus the total count
`#Z ≤ A₀ N^{c+1/4} log N`, which for the zeros with `q ≤ P`, `|γ| ≤ K/q` is the
Riemann-von Mangoldt count summed over `q`. For the actual zeros the density field is the form of
(38) for the region `q |γ| ≤ K`; it is an assumption here, CITED, not proved in the lab, see
QUESTION Q-1545a. -/
structure HypRegion {ι : Type*} (N : ℝ) (Z : Finset ι) (β : ι → ℝ) (A A0 : ℝ) : Prop where
  beta_le : ∀ i ∈ Z, β i ≤ 1
  density : ∀ α : ℝ, 1 / 2 ≤ α → α ≤ 1 →
    ((Z.filter (fun i => α ≤ β i)).card : ℝ) ≤ A * YY N ^ (1 - α)
  count : (Z.card : ℝ) ≤ A0 * N ^ (cLu + 1 / 4) * Real.log N

/-- The inputs of the dyadic route: moduli `1 ≤ q ≤ P`, heights `q |γ| ≤ K`, `β ≤ 1`, the
zero-free region `β ≤ 1 - c₁/log N` off an exceptional set `E` of at most one zero, the density
estimate (38) for the family and the total count. The zero-free region with one exceptional zero
is [12, p. 257] with Page's theorem, and (38) is Huxley and Jutila, both CITED, not proved in the
lab; Lu p. 2391 and p. 2369. -/
structure HypDyadic {ι : Type*} (N : ℝ) (Z : Finset ι) (q : ι → ℕ) (β γ : ι → ℝ) (E : Finset ι)
    (A A0 c1 : ℝ) : Prop where
  q_pos : ∀ i ∈ Z, 1 ≤ q i
  q_le : ∀ i ∈ Z, (q i : ℝ) ≤ PP N
  height : ∀ i ∈ Z, (q i : ℝ) * |γ i| ≤ KK N
  beta_le : ∀ i ∈ Z, β i ≤ 1
  exc_card : E.card ≤ 1
  zero_free : ∀ i ∈ Z, i ∉ E → β i ≤ 1 - c1 / Real.log N
  density : Density38 Z q β γ A
  count : (Z.card : ℝ) ≤ A0 * N ^ (cLu + 1 / 4) * Real.log N

/-! ### Leaves on the parameters -/

/-- LEAF. Unit U-1545. The height of (39), p. 2369: with `Q = N^{3/4}`, `4πN/(qQ) = 4π N^{1/4}/q`
for `N > 0` and `q ≥ 1`. -/
theorem TT_eq {N : ℝ} (hN : 0 < N) {q : ℕ} (hq : 1 ≤ q) : TT N q = KK N / q := by
  unfold TT KK QQ
  have h1 : N = N ^ (1 / 4 : ℝ) * N ^ (3 / 4 : ℝ) := by
    nth_rw 1 [←Real.rpow_one N]
    rw [←Real.rpow_add hN]
    congr 1
    norm_num
  calc 4 * π * N / (q * N ^ (3 / 4 : ℝ))
    _ = 4 * π * (N ^ (1 / 4 : ℝ) * N ^ (3 / 4 : ℝ)) / (q * N ^ (3 / 4 : ℝ)) := by nth_rw 1 [h1]
    _ = (4 * π * N ^ (1 / 4 : ℝ)) * N ^ (3 / 4 : ℝ) / (q * N ^ (3 / 4 : ℝ)) := by ring
    _ = 4 * π * N ^ (1 / 4 : ℝ) / q := by
      rw [mul_div_mul_right _ _ (Real.rpow_pos_of_pos hN _).ne']

/-- LEAF. Unit U-1545. For `N ≥ 1` and `1 ≤ q ≤ P = N^{0.1215}`, the height `4πN/(qQ)` is at
least 1, so (38) with `T = 4πN/(qQ)` applies, p. 2369. -/
theorem TT_ge_one {N : ℝ} (hN : 1 ≤ N) {q : ℕ} (hq : 1 ≤ q) (hqP : (q : ℝ) ≤ PP N) :
    1 ≤ TT N q := by
  unfold TT QQ PP at *
  have hN0 : 0 < N := by linarith
  have h1 : (q:ℝ) * N ^ (3 / 4 : ℝ) ≤ N ^ cLu * N ^ (3 / 4 : ℝ) := mul_le_mul_of_nonneg_right hqP (by positivity)
  have h2 : N ^ cLu * N ^ (3 / 4 : ℝ) = N ^ (cLu + 3 / 4 : ℝ) := by rw [←Real.rpow_add hN0]
  have h3 : cLu + 3 / 4 ≤ 1 := by norm_num [cLu]
  have h4 : N ^ (cLu + 3 / 4 : ℝ) ≤ N ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN h3
  rw [Real.rpow_one] at h4
  have h5 : (q:ℝ) * N ^ (3 / 4 : ℝ) ≤ N := le_trans h1 (by linarith [h2, h4])
  have h6 : 1 * ((q:ℝ) * N ^ (3 / 4 : ℝ)) ≤ 4 * π * N := by
    calc 1 * ((q:ℝ) * N ^ (3 / 4 : ℝ))
      _ = (q:ℝ) * N ^ (3 / 4 : ℝ) := by ring
      _ ≤ N := h5
      _ = 1 * N := by ring
      _ ≤ 4 * π * N := mul_le_mul_of_nonneg_right (by have := Real.pi_gt_three; linarith) (by positivity)
  have h7 : 0 < (q:ℝ) * N ^ (3 / 4 : ℝ) := by positivity
  rw [le_div_iff₀ h7]
  exact h6

/-- LEAF. Unit U-1545. For `N ≥ 1`, `1 ≤ P ≤ K`: `N^{0.1215} ≤ N^{1/4} ≤ 4π N^{1/4}`. -/
theorem PP_le_KK {N : ℝ} (hN : 1 ≤ N) : 1 ≤ PP N ∧ PP N ≤ KK N := by
  unfold PP KK
  have hN0 : 0 < N := by linarith
  have h1 : 1 ≤ N ^ cLu := by
    calc (1:ℝ)
      _ = (1:ℝ) ^ cLu := by rw [Real.one_rpow]
      _ ≤ N ^ cLu := Real.rpow_le_rpow (by linarith) hN (by norm_num [cLu])
  have h2 : N ^ cLu ≤ N ^ (1 / 4 : ℝ) := Real.rpow_le_rpow_of_exponent_le hN (by norm_num [cLu])
  have h3 : N ^ (1 / 4 : ℝ) ≤ 4 * π * N ^ (1 / 4 : ℝ) := by
    have hpi : 1 ≤ 4 * π := by have := Real.pi_gt_three; linarith
    have : N ^ (1 / 4 : ℝ) = 1 * N ^ (1 / 4 : ℝ) := by ring
    nth_rw 1 [this]
    exact mul_le_mul_of_nonneg_right hpi (by positivity)
  exact ⟨h1, le_trans h2 h3⟩

/-- LEAF. Unit U-1545. For `N > 0`, `Y = (8 N^c · 4π N^{1/4})^κ = (32π)^κ N^{κ(c+1/4)}`. -/
theorem YY_eq {N : ℝ} (hN : 0 < N) :
    YY N = (32 * π) ^ kap * N ^ (kap * (cLu + 1 / 4)) := by
  unfold YY PP KK
  have h1 : 8 * N ^ cLu * (4 * π * N ^ (1 / 4 : ℝ)) = (32 * π) * N ^ (cLu + 1 / 4 : ℝ) := by
    calc 8 * N ^ cLu * (4 * π * N ^ (1 / 4 : ℝ))
      _ = (8 * 4 * π) * (N ^ cLu * N ^ (1 / 4 : ℝ)) := by ring
      _ = (32 * π) * (N ^ (cLu + 1 / 4 : ℝ)) := by
        rw [←Real.rpow_add hN]
        ring
  rw [h1]
  rw [Real.mul_rpow (by positivity) (by positivity)]
  congr 1
  rw [←Real.rpow_mul (by linarith)]
  congr 1
  ring

/-- LEAF. Unit U-1545. The saving: for large `N`, `0 < Y < N` and `log(N/Y) ≥ (δ/2) log N`,
since `N/Y = (32π)^{-κ} N^δ`. -/
theorem log_N_div_YY : ∃ N0 : ℝ, ∀ N : ℝ, N0 ≤ N →
    0 < YY N ∧ YY N < N ∧ del / 2 * Real.log N ≤ Real.log (N / YY N) := by
  sorry

/-- LEAF. Unit U-1545. For `c₁ > 0` and large `N`: `log N ≥ 1` and `η = c₁/log N ≤ 1/2`. -/
theorem eta_small_eventually {c1 : ℝ} (hc1 : 0 < c1) : ∃ N0 : ℝ, ∀ N : ℝ, N0 ≤ N →
    1 ≤ Real.log N ∧ c1 / Real.log N ≤ 1 / 2 := by
  sorry

/-- LEAF. Unit U-1545. The zeros with `β < 1/2` are negligible: for `A₀ ≥ 0` and large `N`,
`N^{-1/2} A₀ N^{c+1/4} log N ≤ 1`, since `c + 1/4 = 0.3715 < 1/2`. -/
theorem low_count_eventually {A0 : ℝ} (hA0 : 0 ≤ A0) : ∃ N0 : ℝ, ∀ N : ℝ, N0 ≤ N →
    N ^ (-(1 / 2) : ℝ) * (A0 * N ^ (cLu + 1 / 4) * Real.log N) ≤ 1 := by
  sorry

/-! ### Leaves on the zero sums -/

/-- LEAF. Unit U-1545. The zeros left of `1/2`: for `x ≥ 1`,
`Σ_{i ∈ Z, β_i < 1/2} x^{β_i - 1} ≤ x^{-1/2} #Z`. -/
theorem low_sum_le {ι : Type*} (Z : Finset ι) (β : ι → ℝ) {x : ℝ} (hx : 1 ≤ x) :
    ∑ i ∈ Z.filter (fun i => β i < 1 / 2), x ^ (β i - 1) ≤ x ^ (-(1 / 2) : ℝ) * Z.card := by
  sorry

/-- LEAF. Unit U-1545. The exceptional zero `β̃` of p. 2368 contributes at most 1: if `#E ≤ 1`,
`β ≤ 1` on `E` and `x ≥ 1`, then `Σ_{i ∈ E} x^{β_i - 1} ≤ 1`. -/
theorem exc_sum_le {ι : Type*} (E : Finset ι) (β : ι → ℝ) {x : ℝ} (hx : 1 ≤ x)
    (hE : E.card ≤ 1) (hβ : ∀ i ∈ E, β i ≤ 1) :
    ∑ i ∈ E, x ^ (β i - 1) ≤ 1 := by
  have h_cases : E.card = 0 ∨ E.card = 1 := by omega
  rcases h_cases with h_zero | h_one
  · have h_empty : E = ∅ := card_eq_zero.mp h_zero
    rw [h_empty]
    simp
  · obtain ⟨i, hi⟩ := card_eq_one.mp h_one
    rw [hi]
    simp only [sum_singleton]
    have h1 : β i - 1 ≤ 0 := by
      have : β i ≤ 1 := hβ i (hi.symm ▸ mem_singleton_self i)
      linarith
    have h2 : x ^ (β i - 1) ≤ x ^ (0:ℝ) := Real.rpow_le_rpow_of_exponent_le hx h1
    rw [Real.rpow_zero] at h2
    exact h2

/-- LEAF. Unit U-1545. The closed form without the restriction `Y ≤ √x` of Decomp1524c: for
`x > 1`, `0 < Y < x`, `η ≥ 0`, `σ₀ ≤ 1 - η`,
`∫_{σ₀}^{1-η} log x (Y/x)^{1-α} dα ≤ (log x / log(x/Y)) (Y/x)^η`. -/
theorem integral_ratio_le_gen {σ₀ η x Y : ℝ} (hx : 1 < x) (hY : 0 < Y) (hYx : Y < x)
    (hη : 0 ≤ η) (hσ : σ₀ ≤ 1 - η) :
    ∫ α in σ₀..(1 - η), Real.log x * (Y / x) ^ (1 - α) ≤
      Real.log x / Real.log (x / Y) * (Y / x) ^ η := by
  sorry

/-- LEAF. Unit U-1545. The same with the dyadic loss `1/(1-α)`: for `x > 1`, `0 < Y < x`,
`η > 0`, `σ₀ ≤ 1 - η`,
`∫_{σ₀}^{1-η} log x (Y/x)^{1-α} / (1-α) dα ≤ (log x / (η log(x/Y))) (Y/x)^η`. -/
theorem integral_ratio_inv_le {σ₀ η x Y : ℝ} (hx : 1 < x) (hY : 0 < Y) (hYx : Y < x)
    (hη : 0 < η) (hσ : σ₀ ≤ 1 - η) :
    ∫ α in σ₀..(1 - η), Real.log x * (Y / x) ^ (1 - α) / (1 - α) ≤
      Real.log x / (η * Real.log (x / Y)) * (Y / x) ^ η := by
  sorry

/-- LEAF. Unit U-1545. Inserting a density count with the loss `1/(1-α)`: if
`σ₀ ≤ β_i ≤ 1 - η`, `η > 0`, `x > 1`, `Y > 0`, `A ≥ 0` and `#{β_i ≥ α} ≤ A Y^{1-α}/(1-α)` for
`σ₀ ≤ α < 1`, then `∫_{σ₀}^{1} log x · x^{α-1} #{β_i ≥ α} dα ≤
A ∫_{σ₀}^{1-η} log x (Y/x)^{1-α}/(1-α) dα`; for `α > 1 - η` the count is 0. -/
theorem count_integral_inv_le {ι : Type*} (I : Finset ι) (β : ι → ℝ) {σ₀ η x Y A : ℝ}
    (hx : 1 < x) (hY : 0 < Y) (hA : 0 ≤ A) (hη : 0 < η) (hσ : σ₀ ≤ 1 - η)
    (hβ : ∀ i ∈ I, σ₀ ≤ β i ∧ β i ≤ 1 - η)
    (hcount : ∀ α ∈ Set.Ico σ₀ 1,
      ((I.filter (fun i => α ≤ β i)).card : ℝ) ≤ A * Y ^ (1 - α) / (1 - α)) :
    ∫ α in σ₀..1, Real.log x * x ^ (α - 1) * ((I.filter (fun i => α ≤ β i)).card : ℝ) ≤
      A * ∫ α in σ₀..(1 - η), Real.log x * (Y / x) ^ (1 - α) / (1 - α) := by
  sorry

/-! ### Leaves on the dyadic blocks -/

/-- LEAF. Unit U-1545. Each modulus `1 ≤ q ≤ P` lies in a dyadic block `2^j ≤ q < 2^{j+1}` with
`j = log₂ q ≤ log₂ ⌊P⌋`. -/
theorem block_mem {q : ℕ} (hq : 1 ≤ q) {P : ℝ} (hqP : (q : ℝ) ≤ P) :
    Nat.log 2 q ≤ Nat.log 2 ⌊P⌋₊ ∧ 2 ^ Nat.log 2 q ≤ q ∧ q < 2 ^ (Nat.log 2 q + 1) := by
  have hP_nat : q ≤ ⌊P⌋₊ := Nat.le_floor hqP
  have h1 : Nat.log 2 q ≤ Nat.log 2 ⌊P⌋₊ := Nat.log_mono_right hP_nat
  have h_pos : 0 < q := hq
  have h2 : 2 ^ Nat.log 2 q ≤ q := Nat.pow_log_le_self 2 h_pos.ne'
  have h3 : q < 2 ^ (Nat.log 2 q + 1) := Nat.lt_pow_succ_log_self (by norm_num) q
  exact ⟨h1, h2, h3⟩

/-- LEAF. Unit U-1545. In the block `2^j ≤ q < 2^{j+1}` a zero with `q |γ| ≤ K` has
`q ≤ 2^{j+1}` and `|γ| ≤ K/2^j`, so (38) applies with `x = 2^{j+1}`, `T = K/2^j`. -/
theorem block_params {j q : ℕ} (hj : 2 ^ j ≤ q) (hq : q < 2 ^ (j + 1)) {K γ : ℝ}
    (h : (q : ℝ) * |γ| ≤ K) :
    (q : ℝ) ≤ 2 ^ (j + 1) ∧ |γ| ≤ K / 2 ^ j := by
  have h1 : (q : ℝ) ≤ 2 ^ (j + 1) := by exact_mod_cast le_of_lt hq
  have h2 : |γ| ≤ K / 2 ^ j := by
    have h_pow_pos : (0:ℝ) < 2 ^ j := by positivity
    have h_pow_le_q : (2 ^ j : ℝ) ≤ q := by exact_mod_cast hj
    calc |γ|
      _ = (2 ^ j : ℝ) * |γ| / 2 ^ j := by rw [mul_div_cancel_left₀ _ h_pow_pos.ne']
      _ ≤ (q : ℝ) * |γ| / 2 ^ j := by
        apply div_le_div_of_nonneg_right
        · apply mul_le_mul_of_nonneg_right h_pow_le_q (abs_nonneg γ)
        · positivity
      _ ≤ K / 2 ^ j := by
        apply div_le_div_of_nonneg_right h h_pow_pos.le
  exact ⟨h1, h2⟩

/-- LEAF. Unit U-1545. `2^J ≤ P` for `J = log₂ ⌊P⌋` and `P ≥ 1`. -/
theorem two_pow_log_le {P : ℝ} (hP : 1 ≤ P) : (2 : ℝ) ^ Nat.log 2 ⌊P⌋₊ ≤ P := by
  have h_floor_pos : 0 < ⌊P⌋₊ := Nat.floor_pos.mpr hP
  have h1 : 2 ^ Nat.log 2 ⌊P⌋₊ ≤ ⌊P⌋₊ := Nat.pow_log_le_self 2 h_floor_pos.ne'
  have h2 : (⌊P⌋₊ : ℝ) ≤ P := Nat.floor_le (by linarith)
  calc (2 : ℝ) ^ Nat.log 2 ⌊P⌋₊
    _ = ( (2 ^ Nat.log 2 ⌊P⌋₊ : ℕ) : ℝ) := by simp
    _ ≤ (⌊P⌋₊ : ℝ) := by exact_mod_cast h1
    _ ≤ P := h2

/-- LEAF. Unit U-1545. `2^s - 1 ≥ s log 2` for `s ≥ 0`. -/
theorem two_rpow_sub_one_ge {s : ℝ} (hs : 0 ≤ s) : s * Real.log 2 ≤ (2 : ℝ) ^ s - 1 := by
  have : Real.exp (Real.log 2 * s) = (2:ℝ) ^ s := by
    rw [←Real.rpow_def_of_pos (by norm_num)]
  have h2 : s * Real.log 2 + 1 ≤ Real.exp (s * Real.log 2) := Real.add_one_le_exp (s * Real.log 2)
  have h3 : Real.exp (s * Real.log 2) = Real.exp (Real.log 2 * s) := by
    congr 1
    ring
  rw [h3, this] at h2
  linarith

/-- LEAF. Unit U-1545. The geometric sum over the blocks: for `s > 0`, `B > 0`,
`Σ_{j ≤ J} (B 2^j)^s ≤ (2 B 2^J)^s / (s log 2)`. -/
theorem geom_rpow_sum_le {s B : ℝ} (hs : 0 < s) (hB : 0 < B) (J : ℕ) :
    ∑ j ∈ range (J + 1), (B * 2 ^ j) ^ s ≤ (2 * B * 2 ^ J) ^ s / (s * Real.log 2) := by
  sorry

/-- LEAF. Unit U-1545. The union bound over the dyadic blocks: with `1 ≤ q_i ≤ P`, `1 ≤ P ≤ K`,
`q_i |γ_i| ≤ K` and (38) for the family, for `1/2 ≤ α ≤ 1`,
`#{β_i ≥ α} ≤ A Σ_{j ≤ log₂ ⌊P⌋} (4 · 2^j K)^{κ(1-α)}`, the block `j` being counted by (38) with
`x = 2^{j+1}`, `T = K/2^j`, `x² T = 4 · 2^j K`. -/
theorem dyadic_count {ι : Type*} (Z : Finset ι) (q : ι → ℕ) (β γ : ι → ℝ) {P K A : ℝ}
    (hP : 1 ≤ P) (hPK : P ≤ K) (hA : 0 ≤ A)
    (hq1 : ∀ i ∈ Z, 1 ≤ q i) (hqP : ∀ i ∈ Z, (q i : ℝ) ≤ P)
    (hreg : ∀ i ∈ Z, (q i : ℝ) * |γ i| ≤ K) (hD : Density38 Z q β γ A)
    {α : ℝ} (hα1 : 1 / 2 ≤ α) (hα2 : α ≤ 1) :
    ((Z.filter (fun i => α ≤ β i)).card : ℝ) ≤
      A * ∑ j ∈ range (Nat.log 2 ⌊P⌋₊ + 1), (4 * 2 ^ j * K) ^ (kap * (1 - α)) := by
  sorry

/-! ### Assemblies, CONDITIONAL ON the leaves above -/

/-- ASSEMBLY, CONDITIONAL ON `integral_ratio_le_gen`; uses the PROVED `layer_cake_sum` and
`count_integral_le` of Decomp1524c. A density count over one region gives a bounded zero sum:
for `x > 1`, `0 < Y < x`, `A ≥ 0`, `1/2 ≤ β_i ≤ 1` and `#{β_i ≥ α} ≤ A Y^{1-α}` on `[1/2, 1]`,
`Σ_i x^{β_i - 1} ≤ A + A log x / log(x/Y)`. -/
theorem region_sum_le {ι : Type*} (H : Finset ι) (β : ι → ℝ) {x Y A : ℝ} (hx : 1 < x)
    (hY : 0 < Y) (hYx : Y < x) (hA : 0 ≤ A) (hβ : ∀ i ∈ H, 1 / 2 ≤ β i ∧ β i ≤ 1)
    (hcount : ∀ α ∈ Set.Icc (1 / 2 : ℝ) 1,
      ((H.filter (fun i => α ≤ β i)).card : ℝ) ≤ A * Y ^ (1 - α)) :
    ∑ i ∈ H, x ^ (β i - 1) ≤ A + A * (Real.log x / Real.log (x / Y)) := by
  have hx0 : 0 < x := by linarith
  have hlc := LeanLab.ExceptionalSet.Decomp1524c.layer_cake_sum H β (σ₀ := 1 / 2) hx hβ
  have hci := LeanLab.ExceptionalSet.Decomp1524c.count_integral_le H β (σ₀ := 1 / 2) (η := 0)
    hx hY hA le_rfl (by norm_num) (fun i hi => ⟨(hβ i hi).1, by simpa using (hβ i hi).2⟩) hcount
  have hir := integral_ratio_le_gen (σ₀ := 1 / 2) (η := 0) hx hY hYx le_rfl (by norm_num)
  -- the first term
  have hcardH : (H.card : ℝ) ≤ A * Y ^ (1 - (1 / 2 : ℝ)) := by
    have h := hcount (1 / 2) ⟨le_rfl, by norm_num⟩
    have hf : H.filter (fun i => (1 / 2 : ℝ) ≤ β i) = H :=
      Finset.filter_true_of_mem (fun i hi => (hβ i hi).1)
    rw [hf] at h
    exact h
  have hfirst : x ^ ((1 / 2 : ℝ) - 1) * (H.card : ℝ) ≤ A := by
    have hxpow : 0 ≤ x ^ ((1 / 2 : ℝ) - 1) := by positivity
    have hYx' : Y ^ (1 - (1 / 2 : ℝ)) ≤ x ^ (1 - (1 / 2 : ℝ)) :=
      Real.rpow_le_rpow hY.le hYx.le (by norm_num)
    have hprod : x ^ ((1 / 2 : ℝ) - 1) * x ^ (1 - (1 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hx0]; norm_num
    calc x ^ ((1 / 2 : ℝ) - 1) * (H.card : ℝ)
        ≤ x ^ ((1 / 2 : ℝ) - 1) * (A * Y ^ (1 - (1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hcardH hxpow
      _ ≤ x ^ ((1 / 2 : ℝ) - 1) * (A * x ^ (1 - (1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hYx' hA) hxpow
      _ = A * (x ^ ((1 / 2 : ℝ) - 1) * x ^ (1 - (1 / 2 : ℝ))) := by ring
      _ = A := by rw [hprod, mul_one]
  have hsecond : A * ∫ α in (1 / 2 : ℝ)..(1 - 0), Real.log x * (Y / x) ^ (1 - α) ≤
      A * (Real.log x / Real.log (x / Y)) := by
    apply mul_le_mul_of_nonneg_left _ hA
    simpa using hir
  rw [hlc]
  linarith

/-- ASSEMBLY. Equation (39), p. 2369, CONDITIONAL ON the leaves `log_N_div_YY`,
`low_count_eventually`, `low_sum_le`, `integral_ratio_le_gen` and on the region density
`HypRegion`: there are `C` and `N₀` with `Σ_{i ∈ Z} N^{β_i - 1} ≤ C` for every `N ≥ N₀` and every
family satisfying `HypRegion N Z β A A₀`. The constant is `C = 1 + A + 2A/δ`. -/
theorem eq39_of_region {A A0 : ℝ} (hA : 0 ≤ A) (hA0 : 0 ≤ A0) :
    ∃ C N0 : ℝ, ∀ N : ℝ, N0 ≤ N → ∀ {ι : Type} (Z : Finset ι) (β : ι → ℝ),
      HypRegion N Z β A A0 → ∑ i ∈ Z, N ^ (β i - 1) ≤ C := by
  obtain ⟨N1, hN1⟩ := log_N_div_YY
  obtain ⟨N2, hN2⟩ := low_count_eventually hA0
  refine ⟨1 + A + A * (2 / del), max (max N1 N2) 2, ?_⟩
  intro N hN ι Z β hZ
  have hNN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN2 : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN2' : (2 : ℝ) ≤ N := le_trans (le_max_right _ _) hN
  have hN1' : (1 : ℝ) < N := by linarith
  obtain ⟨hY0, hYN, hlog⟩ := hN1 N hNN1
  have hlogN : 0 < Real.log N := Real.log_pos hN1'
  -- split into β < 1/2 and β ≥ 1/2
  rw [← Finset.sum_filter_add_sum_filter_not Z (fun i => β i < 1 / 2)]
  have hlow : ∑ i ∈ Z.filter (fun i => β i < 1 / 2), N ^ (β i - 1) ≤ 1 := by
    calc ∑ i ∈ Z.filter (fun i => β i < 1 / 2), N ^ (β i - 1)
        ≤ N ^ (-(1 / 2) : ℝ) * Z.card := low_sum_le Z β hN1'.le
      _ ≤ N ^ (-(1 / 2) : ℝ) * (A0 * N ^ (cLu + 1 / 4) * Real.log N) :=
          mul_le_mul_of_nonneg_left hZ.count (by positivity)
      _ ≤ 1 := hN2 N hNN2
  set H := Z.filter (fun i => ¬ β i < 1 / 2) with hHdef
  have hβH : ∀ i ∈ H, 1 / 2 ≤ β i ∧ β i ≤ 1 := by
    intro i hi
    rw [hHdef, Finset.mem_filter] at hi
    exact ⟨not_lt.mp hi.2, hZ.beta_le i hi.1⟩
  have hcountH : ∀ α ∈ Set.Icc (1 / 2 : ℝ) 1,
      ((H.filter (fun i => α ≤ β i)).card : ℝ) ≤ A * YY N ^ (1 - α) := by
    intro α hα
    have hsub : H.filter (fun i => α ≤ β i) ⊆ Z.filter (fun i => α ≤ β i) := by
      intro i hi
      simp only [hHdef, Finset.mem_filter] at hi ⊢
      exact ⟨hi.1.1, hi.2⟩
    exact le_trans (by exact_mod_cast Finset.card_le_card hsub) (hZ.density α hα.1 hα.2)
  have hhigh := region_sum_le H β hN1' hY0 hYN hA hβH hcountH
  have hratio : Real.log N / Real.log (N / YY N) ≤ 2 / del := by
    have hpos : 0 < del / 2 * Real.log N := by
      have := del_pos; positivity
    have hL : 0 < Real.log (N / YY N) := lt_of_lt_of_le hpos hlog
    rw [div_le_div_iff₀ hL del_pos]
    nlinarith [del_pos]
  have hhigh' : ∑ i ∈ H, N ^ (β i - 1) ≤ A + A * (2 / del) :=
    le_trans hhigh (by nlinarith [mul_le_mul_of_nonneg_left hratio hA])
  linarith

/-- ASSEMBLY, CONDITIONAL ON `dyadic_count`, `geom_rpow_sum_le`, `two_pow_log_le`: the density
count of the region `q ≤ P`, `q|γ| ≤ K` that (38) gives through dyadic blocks, with the loss
`1/(1-α)`: for `1/2 ≤ α < 1`,
`#{β ≥ α} ≤ (A/(κ log 2)) · ((8PK)^κ)^{1-α} / (1-α)`. -/
theorem count_dyadic_closed {ι : Type*} (Z : Finset ι) (q : ι → ℕ) (β γ : ι → ℝ) {P K A : ℝ}
    (hP : 1 ≤ P) (hPK : P ≤ K) (hA : 0 ≤ A)
    (hq1 : ∀ i ∈ Z, 1 ≤ q i) (hqP : ∀ i ∈ Z, (q i : ℝ) ≤ P)
    (hreg : ∀ i ∈ Z, (q i : ℝ) * |γ i| ≤ K) (hD : Density38 Z q β γ A)
    {α : ℝ} (hα1 : 1 / 2 ≤ α) (hα2 : α < 1) :
    ((Z.filter (fun i => α ≤ β i)).card : ℝ) ≤
      A / (kap * Real.log 2) * ((8 * P * K) ^ kap) ^ (1 - α) / (1 - α) := by
  have hK : 0 < K := by linarith
  have hs : 0 < kap * (1 - α) := mul_pos kap_pos (by linarith)
  have h1 := dyadic_count Z q β γ hP hPK hA hq1 hqP hreg hD hα1 hα2.le
  set J := Nat.log 2 ⌊P⌋₊
  have hB : (0 : ℝ) < 4 * K := by positivity
  have h2 := geom_rpow_sum_le hs hB J
  have hsum_eq : ∑ j ∈ range (J + 1), (4 * 2 ^ j * K) ^ (kap * (1 - α)) =
      ∑ j ∈ range (J + 1), (4 * K * 2 ^ j) ^ (kap * (1 - α)) := by
    apply Finset.sum_congr rfl; intro j _; ring_nf
  have h3 : (2 * (4 * K) * 2 ^ J) ^ (kap * (1 - α)) ≤ (8 * P * K) ^ (kap * (1 - α)) := by
    apply Real.rpow_le_rpow (by positivity) _ hs.le
    have := two_pow_log_le hP
    nlinarith
  have h4 : (8 * P * K) ^ (kap * (1 - α)) = ((8 * P * K) ^ kap) ^ (1 - α) := by
    rw [← Real.rpow_mul (by positivity)]
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hden : 0 < kap * (1 - α) * Real.log 2 := by positivity
  calc ((Z.filter (fun i => α ≤ β i)).card : ℝ)
      ≤ A * ∑ j ∈ range (J + 1), (4 * 2 ^ j * K) ^ (kap * (1 - α)) := h1
    _ ≤ A * ((2 * (4 * K) * 2 ^ J) ^ (kap * (1 - α)) / (kap * (1 - α) * Real.log 2)) := by
        rw [hsum_eq]; exact mul_le_mul_of_nonneg_left h2 hA
    _ ≤ A * ((8 * P * K) ^ (kap * (1 - α)) / (kap * (1 - α) * Real.log 2)) := by
        apply mul_le_mul_of_nonneg_left _ hA
        exact div_le_div_of_nonneg_right h3 hden.le
    _ = A / (kap * Real.log 2) * ((8 * P * K) ^ kap) ^ (1 - α) / (1 - α) := by
        rw [h4]
        have h1a : (1 - α) ≠ 0 := by linarith
        have hk : kap ≠ 0 := kap_pos.ne'
        field_simp

/-- ASSEMBLY. What (38) and the usual zero-free region give for (39), CONDITIONAL ON the leaves
of this file and on `HypDyadic`: there are `C` and `N₀` with
`Σ_{i ∈ Z} N^{β_i - 1} ≤ C log N` for `N ≥ N₀`. Compare `eq39_of_region` and QUESTION Q-1545a. -/
theorem eq39_of_dyadic {A A0 c1 : ℝ} (hA : 0 ≤ A) (hA0 : 0 ≤ A0) (hc1 : 0 < c1) :
    ∃ C N0 : ℝ, ∀ N : ℝ, N0 ≤ N → ∀ {ι : Type} (Z : Finset ι) (q : ι → ℕ) (β γ : ι → ℝ)
      (E : Finset ι), HypDyadic N Z q β γ E A A0 c1 →
      ∑ i ∈ Z, N ^ (β i - 1) ≤ C * Real.log N := by
  obtain ⟨N1, hN1⟩ := log_N_div_YY
  obtain ⟨N2, hN2⟩ := low_count_eventually hA0
  obtain ⟨N3, hN3⟩ := eta_small_eventually hc1
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set A' := A / (kap * Real.log 2) with hA'def
  have hA' : 0 ≤ A' := by have := kap_pos; positivity
  refine ⟨2 + 2 * A' + A' * (2 / (c1 * del)), max (max N1 N2) (max N3 2), ?_⟩
  intro N hN ι Z q β γ E hZ
  have hNN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNN2 : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNN3 : N3 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN2' : (2 : ℝ) ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hN1' : (1 : ℝ) < N := by linarith
  obtain ⟨hY0, hYN, hlog⟩ := hN1 N hNN1
  obtain ⟨hlog1, heta⟩ := hN3 N hNN3
  have hlogN : 0 < Real.log N := by linarith
  set η := c1 / Real.log N with hηdef
  have hη : 0 < η := div_pos hc1 hlogN
  obtain ⟨hP1, hPK⟩ := PP_le_KK hN1'.le
  -- the exceptional part
  rw [← Finset.sum_filter_add_sum_filter_not Z (fun i => i ∈ E)]
  have hexc : ∑ i ∈ Z.filter (fun i => i ∈ E), N ^ (β i - 1) ≤ 1 := by
    apply exc_sum_le _ β hN1'.le
    · exact le_trans (Finset.card_le_card (fun i hi => (Finset.mem_filter.mp hi).2)) hZ.exc_card
    · intro i hi; exact hZ.beta_le i (Finset.mem_filter.mp hi).1
  set Z' := Z.filter (fun i => ¬ i ∈ E) with hZ'def
  rw [← Finset.sum_filter_add_sum_filter_not Z' (fun i => β i < 1 / 2)]
  have hlow : ∑ i ∈ Z'.filter (fun i => β i < 1 / 2), N ^ (β i - 1) ≤ 1 := by
    have hcZ' : (Z'.card : ℝ) ≤ Z.card := by
      exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    calc ∑ i ∈ Z'.filter (fun i => β i < 1 / 2), N ^ (β i - 1)
        ≤ N ^ (-(1 / 2) : ℝ) * Z'.card := low_sum_le Z' β hN1'.le
      _ ≤ N ^ (-(1 / 2) : ℝ) * (A0 * N ^ (cLu + 1 / 4) * Real.log N) :=
          mul_le_mul_of_nonneg_left (le_trans hcZ' hZ.count) (by positivity)
      _ ≤ 1 := hN2 N hNN2
  set H := Z'.filter (fun i => ¬ β i < 1 / 2) with hHdef
  have hmemH : ∀ i ∈ H, i ∈ Z ∧ i ∉ E ∧ 1 / 2 ≤ β i := by
    intro i hi
    simp only [hHdef, hZ'def, Finset.mem_filter] at hi
    exact ⟨hi.1.1, hi.1.2, not_lt.mp hi.2⟩
  have hβH : ∀ i ∈ H, 1 / 2 ≤ β i ∧ β i ≤ 1 - η := by
    intro i hi
    obtain ⟨h1, h2, h3⟩ := hmemH i hi
    exact ⟨h3, hZ.zero_free i h1 h2⟩
  have hσ : (1 / 2 : ℝ) ≤ 1 - η := by linarith
  have hYYeq : YY N = (8 * PP N * KK N) ^ kap := rfl
  have hcountH : ∀ α ∈ Set.Ico (1 / 2 : ℝ) 1,
      ((H.filter (fun i => α ≤ β i)).card : ℝ) ≤ A' * YY N ^ (1 - α) / (1 - α) := by
    intro α hα
    have hsub : H.filter (fun i => α ≤ β i) ⊆ Z.filter (fun i => α ≤ β i) := by
      intro i hi
      rw [Finset.mem_filter] at hi ⊢
      exact ⟨(hmemH i hi.1).1, hi.2⟩
    have hc := count_dyadic_closed Z q β γ hP1 hPK hA hZ.q_pos hZ.q_le hZ.height hZ.density
      hα.1 hα.2
    rw [← hYYeq] at hc
    exact le_trans (by exact_mod_cast Finset.card_le_card hsub) hc
  have hlc := LeanLab.ExceptionalSet.Decomp1524c.layer_cake_sum H β (σ₀ := 1 / 2) hN1'
    (fun i hi => ⟨(hβH i hi).1, by linarith [(hβH i hi).2]⟩)
  have hci := count_integral_inv_le H β hN1' hY0 hA' hη hσ hβH hcountH
  have hir := integral_ratio_inv_le (σ₀ := 1 / 2) hN1' hY0 hYN hη hσ
  -- first term
  have hcardH : (H.card : ℝ) ≤ A' * YY N ^ (1 - (1 / 2 : ℝ)) / (1 - 1 / 2) := by
    have h := hcountH (1 / 2) ⟨le_rfl, by norm_num⟩
    have hf : H.filter (fun i => (1 / 2 : ℝ) ≤ β i) = H :=
      Finset.filter_true_of_mem (fun i hi => (hβH i hi).1)
    rw [hf] at h
    exact h
  have hN0 : 0 < N := by linarith
  have hfirst : N ^ ((1 / 2 : ℝ) - 1) * (H.card : ℝ) ≤ 2 * A' := by
    have hxpow : 0 ≤ N ^ ((1 / 2 : ℝ) - 1) := by positivity
    have hYx' : YY N ^ (1 - (1 / 2 : ℝ)) ≤ N ^ (1 - (1 / 2 : ℝ)) :=
      Real.rpow_le_rpow hY0.le hYN.le (by norm_num)
    have hprod : N ^ ((1 / 2 : ℝ) - 1) * N ^ (1 - (1 / 2 : ℝ)) = 1 := by
      rw [← Real.rpow_add hN0]; norm_num
    have hc2 : (H.card : ℝ) ≤ 2 * A' * YY N ^ (1 - (1 / 2 : ℝ)) := by
      have : A' * YY N ^ (1 - (1 / 2 : ℝ)) / (1 - 1 / 2) = 2 * A' * YY N ^ (1 - (1 / 2 : ℝ)) := by
        ring
      linarith
    calc N ^ ((1 / 2 : ℝ) - 1) * (H.card : ℝ)
        ≤ N ^ ((1 / 2 : ℝ) - 1) * (2 * A' * YY N ^ (1 - (1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left hc2 hxpow
      _ ≤ N ^ ((1 / 2 : ℝ) - 1) * (2 * A' * N ^ (1 - (1 / 2 : ℝ))) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hYx' (by positivity)) hxpow
      _ = 2 * A' * (N ^ ((1 / 2 : ℝ) - 1) * N ^ (1 - (1 / 2 : ℝ))) := by ring
      _ = 2 * A' := by rw [hprod, mul_one]
  -- second term
  have hL : 0 < Real.log (N / YY N) := by
    have : 0 < del / 2 * Real.log N := by have := del_pos; positivity
    linarith
  have hpow1 : (YY N / N) ^ η ≤ 1 :=
    Real.rpow_le_one (by positivity) (by rw [div_le_one hN0]; exact hYN.le) hη.le
  have hbound : Real.log N / (η * Real.log (N / YY N)) * (YY N / N) ^ η ≤
      2 / (c1 * del) * Real.log N := by
    have hq0 : 0 ≤ Real.log N / (η * Real.log (N / YY N)) := by positivity
    have hstep : Real.log N / (η * Real.log (N / YY N)) ≤ 2 / (c1 * del) * Real.log N := by
      rw [div_le_iff₀ (by positivity)]
      have hηL : η * Real.log N = c1 := by
        rw [hηdef]; field_simp
      have hdp := del_pos
      have : 2 / (c1 * del) * Real.log N * (η * Real.log (N / YY N)) ≥
          2 / (c1 * del) * Real.log N * (η * (del / 2 * Real.log N)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_left hlog hη.le
      have heq : 2 / (c1 * del) * Real.log N * (η * (del / 2 * Real.log N)) = Real.log N := by
        have : 2 / (c1 * del) * Real.log N * (η * (del / 2 * Real.log N)) =
            (η * Real.log N) * Real.log N / c1 := by
          field_simp
        rw [this, hηL]; field_simp
      linarith
    calc Real.log N / (η * Real.log (N / YY N)) * (YY N / N) ^ η
        ≤ Real.log N / (η * Real.log (N / YY N)) * 1 := mul_le_mul_of_nonneg_left hpow1 hq0
      _ ≤ 2 / (c1 * del) * Real.log N := by rw [mul_one]; exact hstep
  have hsecond : A' * ∫ α in (1 / 2 : ℝ)..(1 - η), Real.log N * (YY N / N) ^ (1 - α) / (1 - α) ≤
      A' * (2 / (c1 * del) * Real.log N) :=
    mul_le_mul_of_nonneg_left (le_trans hir hbound) hA'
  have hhigh : ∑ i ∈ H, N ^ (β i - 1) ≤ 2 * A' + A' * (2 / (c1 * del) * Real.log N) := by
    rw [hlc]; linarith
  have hfin : 1 + (1 + (2 * A' + A' * (2 / (c1 * del) * Real.log N))) ≤
      (2 + 2 * A' + A' * (2 / (c1 * del))) * Real.log N := by
    have h0 : 0 ≤ 2 + 2 * A' := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlog1 h0]
  linarith

/-! ### Vacuity instances, PROVED -/

/-- The one-zero family `β = 1/2`, `q = 1`, `γ = 0` satisfies (38) with `A = 1`. -/
theorem vacuity_density38 :
    Density38 ({0} : Finset ℕ) (fun _ => 1) (fun _ => 1 / 2) (fun _ => 0) 1 := by
  intro x T α hx hT hα1 hα2
  have hbase : 1 ≤ x ^ 2 * T := by nlinarith
  have hexp : 0 ≤ kap * (1 - α) := mul_nonneg kap_pos.le (by linarith)
  have h1 : (1 : ℝ) ≤ (x ^ 2 * T) ^ (kap * (1 - α)) := Real.one_le_rpow hbase hexp
  refine le_trans (b := 1) ?_ (by linarith)
  calc _ ≤ ((({0} : Finset ℕ)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)
    _ = 1 := by simp

/-- `HypRegion` holds at `N = 3` for the one-zero family `β = 1/2`, with `A = A₀ = 1`. -/
theorem vacuity_hypRegion :
    HypRegion (3 : ℝ) ({0} : Finset ℕ) (fun _ => 1 / 2) 1 1 := by
  have hYY : 1 ≤ YY 3 := by
    unfold YY PP KK
    apply Real.one_le_rpow _ kap_pos.le
    have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ cLu := Real.one_le_rpow (by norm_num) (by norm_num [cLu])
    have h2 : (1 : ℝ) ≤ (3 : ℝ) ^ (1 / 4 : ℝ) := Real.one_le_rpow (by norm_num) (by norm_num)
    have hpi : 3 < π := Real.pi_gt_three
    nlinarith [mul_le_mul h1 h2 (by norm_num) (by linarith)]
  refine ⟨fun _ _ => by norm_num, ?_, ?_⟩
  · intro α hα1 hα2
    have hcard : (({0} : Finset ℕ).filter (fun _ => α ≤ 1 / 2)).card ≤ 1 := by
      calc _ ≤ ({0} : Finset ℕ).card := Finset.card_le_card (Finset.filter_subset _ _)
        _ = 1 := by simp
    have h1 : (1 : ℝ) ≤ YY 3 ^ (1 - α) := Real.one_le_rpow hYY (by linarith)
    calc ((({0} : Finset ℕ).filter _).card : ℝ) ≤ 1 := by exact_mod_cast hcard
      _ ≤ 1 * YY 3 ^ (1 - α) := by linarith
  · have hl : 1 ≤ Real.log 3 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
    have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (cLu + 1 / 4) := Real.one_le_rpow (by norm_num) (by norm_num [cLu])
    simp only [Finset.card_singleton, Nat.cast_one, one_mul]
    nlinarith

/-- `HypDyadic` holds at `N = 3` for the one-zero family `q = 1`, `β = 1/2`, `γ = 0`, no
exceptional zero, with `A = A₀ = 1`, `c₁ = 1/10`. -/
theorem vacuity_hypDyadic :
    HypDyadic (3 : ℝ) ({0} : Finset ℕ) (fun _ => 1) (fun _ => 1 / 2) (fun _ => 0) ∅ 1 1
      (1 / 10) := by
  have hl : 1 ≤ Real.log 3 := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have := Real.exp_one_lt_d9; norm_num at this ⊢; linarith
  refine ⟨fun _ _ => le_rfl, ?_, ?_, fun _ _ => by norm_num, by simp, ?_, vacuity_density38, ?_⟩
  · intro _ _
    simp only [Nat.cast_one]
    exact Real.one_le_rpow (by norm_num) (by norm_num [cLu])
  · intro _ _
    simp only [Nat.cast_one, abs_zero, mul_zero]
    unfold KK; positivity
  · intro _ _ _
    have : (1 / 10 : ℝ) / Real.log 3 ≤ 1 / 10 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    linarith
  · have h1 : (1 : ℝ) ≤ (3 : ℝ) ^ (cLu + 1 / 4) := Real.one_le_rpow (by norm_num) (by norm_num [cLu])
    simp only [Finset.card_singleton, Nat.cast_one, one_mul]
    nlinarith

end LeanLab.ExceptionalSet.Decomp1545a
