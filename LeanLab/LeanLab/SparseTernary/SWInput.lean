/-
P0086 Basak, Bhat, Dong, Zaharescu 2024, arXiv 2409.08968 v1, Section 6, page 9, the sentence
before (6.6): "Applying the Siegel-Walfisz theorem (see [8, Ch. 22]) ...".

The cited input `SW N`: the Siegel-Walfisz theorem for `θ(x; q, a)`, in the weakest textbook
form, a saving of an arbitrary power of `log x`:

  for every `N` and every `K`, there are `C, x₀` with
  `|θ(x; q, a) - x/φ(q)| ≤ C x / (log x)^K`
  for all `x ≥ x₀`, all `1 ≤ q ≤ (log x)^N` and all `a` coprime to `q`.

Davenport, Multiplicative Number Theory, Ch. 22, and Montgomery-Vaughan Cor. 11.21 state the
stronger saving `exp(-c √log x)` for `ψ`; `ψ - θ ≪ √x log x` gives the same for `θ`. We prove
here that the `exp(-c √log x)` form implies `SW N` (`sw_of_swExp`), so `SW N` is no stronger
than the textbook theorem. The constants `C, x₀` depend on `N` and `K`, as in the textbook
(ineffective through Siegel's theorem). The modulus range the paper needs on page 9 is
`q_ℓ ≤ q q_0 ≤ P q_0`, which it records as `(log u)^{B + 3A + 1}`: `SWfor A B`.

NOT proved here: `SW N` is a cited theorem, a `Prop`, never an axiom.

AI-written Lean code, Claude, run 20261021T0903Z-24128, unit U-1383. Checked only by the Lean
kernel. Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib

open Finset Filter Real

noncomputable section
namespace LeanLab.SparseTernary.SWInput

/-- `θ(x; q, a) = Σ_{p ≤ x, p ≡ a mod q} log p`. -/
def thetaAP (x : ℝ) (q a : ℕ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter (fun p => p.Prime ∧ p ≡ a [MOD q]), Real.log p

/-- **Siegel-Walfisz, `θ` form, power-of-log saving**, moduli up to `(log x)^N`.
Cited (Davenport Ch. 22), NOT proved. -/
def SW (N : ℕ) : Prop :=
  ∀ K : ℝ, ∃ C x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ N →
    a.Coprime q → |thetaAP x q a - x / (q.totient : ℝ)| ≤ C * x / Real.log x ^ K

/-- The textbook theorem: `SW N` for every `N`. -/
def SWAll : Prop := ∀ N : ℕ, SW N

/-- The instance the paper invokes on page 9: moduli up to `(log x)^{B + 3A + 1}`. -/
def SWfor (A B : ℕ) : Prop := SW (B + 3 * A + 1)

/-- **The textbook form with saving `exp(-c √log x)`**, Davenport Ch. 22, for `θ`. -/
def SWExp (N : ℕ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∃ C x0 : ℝ, ∀ x : ℝ, x0 ≤ x → ∀ q a : ℕ, 1 ≤ q →
    (q : ℝ) ≤ Real.log x ^ N → a.Coprime q →
      |thetaAP x q a - x / (q.totient : ℝ)| ≤ C * x * Real.exp (-(c * Real.sqrt (Real.log x)))

/-- `exp(-c √L) ≤ C_K L^{-K}` for large `L`. -/
theorem exp_sqrt_le (c K : ℝ) (hc : 0 < c) :
    ∃ D L0 : ℝ, ∀ L : ℝ, L0 ≤ L → Real.exp (-(c * Real.sqrt L)) ≤ D / L ^ K := by
  obtain ⟨n, hn⟩ := exists_nat_ge K
  -- s^(2n) e^{-s} → 0, s = c √L
  have ht := Real.tendsto_pow_mul_exp_neg_atTop_nhds_zero (2 * n)
  have hev := (ht.eventually (gt_mem_nhds (zero_lt_one))).exists_forall_of_atTop
  obtain ⟨s0, hs0⟩ := hev
  refine ⟨(1 / c) ^ (2 * n), max 1 ((s0 / c) ^ 2 + 1), fun L hL => ?_⟩
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hL
  have hL0 : 0 < L := by linarith
  have hsq : 0 < Real.sqrt L := Real.sqrt_pos.mpr hL0
  set s := c * Real.sqrt L with hs
  have hspos : 0 < s := by positivity
  have hs0' : s0 ≤ s := by
    have h2 : (s0 / c) ^ 2 + 1 ≤ L := le_trans (le_max_right _ _) hL
    by_contra hlt
    push Not at hlt
    have h3 : Real.sqrt L < s0 / c := by rw [lt_div_iff₀ hc]; linarith
    have hs0c : 0 < s0 / c := lt_trans hsq h3
    have h4 : L < (s0 / c) ^ 2 := (Real.sqrt_lt' hs0c).mp h3
    linarith
  have hbound := hs0 s hs0'
  -- s^(2n) e^{-s} < 1
  have hpow : 0 < s ^ (2 * n) := by positivity
  have he : Real.exp (-s) < 1 / s ^ (2 * n) := by
    rw [lt_div_iff₀ hpow]; linarith [mul_comm (s ^ (2 * n)) (Real.exp (-s))]
  -- L^K ≤ L^n and s^(2n) = c^(2n) L^n
  have hLK : L ^ K ≤ L ^ (n : ℝ) := Real.rpow_le_rpow_of_exponent_le hL1 hn
  have hsn : s ^ (2 * n) = c ^ (2 * n) * L ^ (n : ℝ) := by
    rw [hs, mul_pow, pow_mul (Real.sqrt L), Real.sq_sqrt hL0.le, Real.rpow_natCast]
  have hLKpos : 0 < L ^ K := Real.rpow_pos_of_pos hL0 K
  rw [le_div_iff₀ hLKpos]
  calc Real.exp (-s) * L ^ K ≤ Real.exp (-s) * L ^ (n : ℝ) :=
        mul_le_mul_of_nonneg_left hLK (Real.exp_pos _).le
    _ ≤ 1 / s ^ (2 * n) * L ^ (n : ℝ) :=
        mul_le_mul_of_nonneg_right he.le (by positivity)
    _ = (1 / c) ^ (2 * n) := by
        rw [hsn, one_div_pow, div_mul_eq_mul_div, one_mul,
          div_eq_div_iff (by positivity) (by positivity)]
        ring

/-- **`SW N` is no stronger than the textbook theorem**: the `exp(-c √log x)` form implies it.
PROVED. -/
theorem sw_of_swExp (N : ℕ) (h : SWExp N) : SW N := by
  obtain ⟨c, hc, C, x0, hC⟩ := h
  intro K
  obtain ⟨D, L0, hD⟩ := exp_sqrt_le c K hc
  refine ⟨|C| * D, max x0 (max (Real.exp (max L0 1)) 1), fun x hx q a hq hqx hco => ?_⟩
  have hx0 : x0 ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp (max L0 1) ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hxpos : 0 < x := lt_of_lt_of_le (Real.exp_pos _) hxe
  have hlog : max L0 1 ≤ Real.log x := by
    rw [← Real.log_exp (max L0 1)]; exact Real.log_le_log (Real.exp_pos _) hxe
  have hL0 : L0 ≤ Real.log x := le_trans (le_max_left _ _) hlog
  have hl1 : 0 < Real.log x := by linarith [le_max_right L0 1]
  have h1 := hC x hx0 q a hq hqx hco
  have h2 := hD (Real.log x) hL0
  have hD0 : 0 ≤ D := by
    have : 0 ≤ D / Real.log x ^ K := le_trans (Real.exp_pos _).le h2
    have hp : 0 < Real.log x ^ K := Real.rpow_pos_of_pos hl1 K
    by_contra hneg; push Not at hneg
    have := div_neg_of_neg_of_pos hneg hp
    linarith
  calc |thetaAP x q a - x / (q.totient : ℝ)|
      ≤ C * x * Real.exp (-(c * Real.sqrt (Real.log x))) := h1
    _ ≤ |C| * x * Real.exp (-(c * Real.sqrt (Real.log x))) := by
        gcongr; exact le_abs_self C
    _ ≤ |C| * x * (D / Real.log x ^ K) := by gcongr
    _ = |C| * D * x / Real.log x ^ K := by ring

/-- Monotonicity in the modulus range: `SW N → SW N'` for `N' ≤ N`. PROVED. -/
theorem sw_mono {N N' : ℕ} (hN : N' ≤ N) (h : SW N) : SW N' := by
  intro K
  obtain ⟨C, x0, hC⟩ := h K
  refine ⟨C, max x0 (Real.exp 1), fun x hx q a hq hqx hco => ?_⟩
  have hx0 : x0 ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hl : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hxe
  exact hC x hx0 q a hq (le_trans hqx (pow_le_pow_right₀ hl hN)) hco

/-- **Content check**: `SW N` contains the prime number theorem for `θ` with a power-of-log
error, the case `q = 1`, `a = 0`. So the input is not vacuous. PROVED. -/
theorem sw_q_one (N : ℕ) (h : SW N) (K : ℝ) :
    ∃ C x0 : ℝ, ∀ x : ℝ, x0 ≤ x → |thetaAP x 1 0 - x| ≤ C * x / Real.log x ^ K := by
  obtain ⟨C, x0, hC⟩ := h K
  refine ⟨C, max x0 (Real.exp 1), fun x hx => ?_⟩
  have hx0 : x0 ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hl : 1 ≤ Real.log x := by
    rw [← Real.log_exp 1]; exact Real.log_le_log (Real.exp_pos _) hxe
  have := hC x hx0 1 0 le_rfl (by simpa using one_le_pow₀ hl) (Nat.coprime_zero_left 1 |>.mpr rfl)
  simpa using this

end LeanLab.SparseTernary.SWInput
