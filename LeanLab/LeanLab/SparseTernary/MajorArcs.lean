/-
P0086 Basak, Bhat, Dong, Zaharescu 2024, arXiv 2409.08968 v1, Sections 6, 7, 8.
The major arcs: `MajorLower A B (9A + 1)` CONDITIONAL ON four named inputs.

Named inputs, stated as `Prop`s, never axioms, NOT proved here:
* `Major618 A B`: display (6.18), the major arc integral equals `H(m,u) 𝔖_P(m)` up to
  `u² (log u)^{12A - B + ε}`, the error as the paper states it after (6.21). This is the
  Siegel-Walfisz consequence of Section 6: (6.1)-(6.13) use Siegel-Walfisz for the moduli
  `q q_0 ≤ (log u)^{B + 3A + 1}`, (6.14)-(6.17) evaluate the singular integral.
* `Tail72 A B`: the factorisation `f = g * h` of (7.3)-(7.15) together with the tail bound
  (7.2), `Σ_{q > P} |f(q)| ≪ (log u)^{-(B - 27A - 1)}`, in the combined form
  `|𝔖_P(m) - G(q_0) Σ_v h(v)| ≪ (log u)^{-(B - 27A - 1)}`.
* `Lemma82`: Lemma 8.2, `G(q_0) = ∏ G(p_j)`, together with OUR evaluation of the local factor
  `G(p) = p N_p(m) / (p - 1)³`, `N_p(m)` the number of triples of `L_p` summing to `m mod p`.
  Section 8.3 was unreachable; the closed form was checked in Python against the definition
  (8.1) for `q_0 = 2, 6, 30, 210` and eight odd `m` each, agreement to `1e-13`.
* `Euler716`: the Euler product (7.16), corrected, gives `Σ_v h(v)` real and at least
  `∏_{p | m, p ≥ Z} (1 - 1/(p-1)²)`. As printed, (7.16) carries the factor `1 - 1/(p-1)²` at
  `p | q_0`, which vanishes at `p = 2`; by (7.15) `h(p^j) = 0` for `p | q_0`, and the factor
  `1 - 1/(p-1)²` belongs to `p | m`, `p ∤ q_0`. Checked in Python, `v < 3000`.

PROVED here with zero sorry: the finite product estimates `euler_lower` (the `h` part is at
least `1/2` once `Z ≥ 4`), `G_lower` (`∏ p N_p/(p-1)³ ≥ 1/q_0²`, via `local_three`),
`q0_sq_le` (`q_0² ≤ (log u)^{9A}`, via Mathlib's `θ(x) ≤ x log 4` and `6 log 4 < 9`),
`qell_of_dvd` (the `q_ℓ` of (7.6) reduces to the one in (8.1) when `w ∣ q_0`), and
`majorLower_of_inputs`, the exponent bookkeeping: with `κ = 9A + 1` and `B ≥ 36A + 3` the
errors `12A - B + 1` and `-(B - 27A - 1)` are both at most `-(9A + 2)`.
`repProp_of_inputs`: `RepProp A` for `B ≥ 36A + 3`, `B ≥ 28A + 13`, CONDITIONAL ON
`Minor516W A B`, `Major618 A B`, `Tail72 A B`, `Lemma82`, `Euler716`.

AI-written Lean code, Claude, run 20261021T0103Z-19411, unit U-1319. Checked only by the Lean
kernel. Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.SparseTernary.RepAssembly
import LeanLab.SparseTernary.SizeProp

open Finset Filter Real
open scoped Classical Chebyshev

noncomputable section
namespace LeanLab.SparseTernary.MajorArcs

open LeanLab.SparseTernary LeanLab.SparseTernary.Section4

/-! ### Definitions: the singular series of (6.18), (6.22), (7.1), (7.14)-(7.15), (8.1) -/

/-- (7.6) `q_ℓ = q q_0 / (q q_0, a q_0 + ℓ q)`, the reduced denominator of `a/q + ℓ/q_0`. -/
def qell (Z q a ℓ : ℕ) : ℕ := q * q0 Z / Nat.gcd (q * q0 Z) (a * q0 Z + ℓ * q)

/-- `μ(n)/φ(n)`. -/
def muphi (n : ℕ) : ℝ := (ArithmeticFunction.moebius n : ℝ) / (n.totient : ℝ)

/-- The inner sum `Σ_{0 ≤ ℓ < q_0} μ(q_ℓ)/φ(q_ℓ) Σ_{r ∈ R_0} e(-ℓ r / q_0)`. -/
def inner (Z q a : ℕ) : ℂ :=
  ∑ ℓ ∈ range (q0 Z), (muphi (qell Z q a ℓ) : ℂ) * ∑ r ∈ R0 Z, ee (-((ℓ : ℝ) * r / q0 Z))

/-- (7.1) `f(q) = q_0^{-3} Σ_{(a,q)=1} e(-am/q) Σ_{rᵢ} Σ_{ℓᵢ} e(-Σℓᵢrᵢ/q_0) ∏ μ(q_{ℓᵢ})/φ(q_{ℓᵢ})`,
the triple sum over `(rᵢ, ℓᵢ)` written as the cube of `inner`, which it is by distributivity. -/
def fq (Z m q : ℕ) : ℂ :=
  1 / (q0 Z : ℂ) ^ 3 * ∑ a ∈ (Icc 1 q).filter (fun a => a.Coprime q),
    ee (-((a : ℝ) * m / q)) * inner Z q a ^ 3

/-- (6.22) `𝔖(m, q_0, R_0) = Σ_{q ≤ P} f(q)`. -/
def SingP (Z m : ℕ) (P : ℝ) : ℂ := ∑ q ∈ Icc 1 ⌊P⌋₊, fq Z m q

/-- (8.1) `G(q_0) = Σ_w g(w)`, with (7.14) `g(w) = f(w)` for `w ∣ q_0` and `0` otherwise. -/
def Gq0 (Z m : ℕ) : ℂ := ∑ w ∈ (q0 Z).divisors, fq Z m w

/-- (7.15) `h(v) = μ(v)/φ(v)³ Σ_{(a,v)=1} e(-am/v)` for `(v, q_0) = 1`, else `0`. -/
def hv (Z m v : ℕ) : ℂ :=
  if v.Coprime (q0 Z) then
    (ArithmeticFunction.moebius v : ℂ) / (v.totient : ℂ) ^ 3 *
      ∑ a ∈ (Icc 1 v).filter (fun a => a.Coprime v), ee (-((a : ℝ) * m / v))
  else 0

/-- `Σ_v h(v)`. -/
def hsum (Z m : ℕ) : ℂ := ∑' v : ℕ, hv Z m v

/-- `N_p(m)`: the triples of `L_p` whose sum is `m mod p`. -/
def Np (p m : ℕ) : ℕ :=
  #((Lset p ×ˢ Lset p ×ˢ Lset p).filter (fun t => t.1 + t.2.1 + t.2.2 ≡ m [MOD p]))

/-- The closed form `∏_{p < Z} p N_p(m) / (p - 1)³` of `G(q_0)`. -/
def Gprod (Z m : ℕ) : ℝ := ∏ p ∈ Nat.primesBelow Z, (p : ℝ) * Np p m / ((p : ℝ) - 1) ^ 3

/-! ### The named inputs -/

/-- **(6.18)**, with the error the paper states after (6.21): for `4u ≤ m ≤ 5u`,
`∫_𝔐 S³ e(-mα) = H(m,u) 𝔖_P(m) + O_ε(u² (log u)^{12A - B + ε})`, `P = (log u)^B`,
`Q = u (log u)^{-B}`, `Z = ⌈3A log log u⌉`. Siegel-Walfisz consequence; cited, NOT proved. -/
def Major618 (A B : ℕ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ C u0 : ℝ, ∀ u : ℝ, u0 ≤ u → ∀ m : ℕ, 4 * u ≤ m → (m : ℝ) ≤ 5 * u →
    ‖(∫ α in majorArcs (Real.log u ^ B) (u / Real.log u ^ B),
        Sexp (Zof A u) u α ^ 3 * ee (-(m * α))) -
      (Hmu m u : ℂ) * SingP (Zof A u) m (Real.log u ^ B)‖ ≤
      C * u ^ 2 * Real.log u ^ (12 * (A : ℝ) - B + ε)

/-- **(7.2) with (7.3)-(7.15)**: `|𝔖_P(m) - G(q_0) Σ_v h(v)| ≪ (log u)^{-(B - 27A - 1)}`
for odd `m`. Cited, NOT proved. -/
def Tail72 (A B : ℕ) : Prop :=
  ∃ C u0 : ℝ, ∀ u : ℝ, u0 ≤ u → ∀ m : ℕ, Odd m → 4 * u ≤ m → (m : ℝ) ≤ 5 * u →
    ‖SingP (Zof A u) m (Real.log u ^ B) - Gq0 (Zof A u) m * hsum (Zof A u) m‖ ≤
      C * Real.log u ^ (-((B : ℝ) - 27 * A - 1))

/-- **Lemma 8.2** `G(q_0) = ∏ G(p_j)`, with the local factor evaluated as
`G(p) = p N_p(m)/(p - 1)³`, for odd `m`. Cited, NOT proved; Python-checked. -/
def Lemma82 : Prop := ∀ Z m : ℕ, Odd m → Gq0 Z m = (Gprod Z m : ℂ)

/-- **(7.16), corrected**: for odd `m`, `Σ_v h(v)` is real and at least
`∏_{p | m, p ≥ Z} (1 - 1/(p-1)²)`; the other Euler factors `1 + 1/(p-1)³` are at least `1`.
Cited, NOT proved; Python-checked. -/
def Euler716 : Prop := ∀ Z m : ℕ, Odd m → ∃ x : ℝ, hsum Z m = (x : ℂ) ∧
  ∏ p ∈ m.primeFactors.filter (fun p => Z ≤ p), (1 - 1 / ((p : ℝ) - 1) ^ 2) ≤ x

/-! ### Faithfulness of (8.1) -/

/-- For `w ∣ q_0`, the `q_ℓ` of (7.6) is the `q_0 / (q_0, a q_0/w + ℓ)` printed in (8.1). -/
theorem qell_of_dvd {Z w : ℕ} (a ℓ : ℕ) (hw : w ∣ q0 Z) (hw0 : 0 < w) :
    qell Z w a ℓ = q0 Z / Nat.gcd (q0 Z) (a * (q0 Z / w) + ℓ) := by
  obtain ⟨k, hk⟩ := hw
  have hk' : q0 Z / w = k := by rw [hk, Nat.mul_div_cancel_left _ hw0]
  unfold qell
  rw [hk', hk]
  have e : a * (w * k) + ℓ * w = w * (a * k + ℓ) := by ring
  rw [e, Nat.gcd_mul_left, Nat.mul_div_mul_left _ _ hw0]

/-! ### The `h` part: a finite product estimate -/

/-- Weierstrass: `∏ (1 - xᵢ) ≥ 1 - Σ xᵢ` for `0 ≤ xᵢ ≤ 1`. -/
theorem one_sub_sum_le_prod (s : Finset ℕ) (x : ℕ → ℝ) (h0 : ∀ n ∈ s, 0 ≤ x n)
    (h1 : ∀ n ∈ s, x n ≤ 1) : 1 - ∑ n ∈ s, x n ≤ ∏ n ∈ s, (1 - x n) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [sum_insert ha, prod_insert ha]
    have hs := ih (fun n hn => h0 n (mem_insert_of_mem hn)) (fun n hn => h1 n (mem_insert_of_mem hn))
    have ha0 := h0 a (mem_insert_self a s)
    have ha1 := h1 a (mem_insert_self a s)
    have hS : 0 ≤ ∑ n ∈ s, x n := sum_nonneg fun n hn => h0 n (mem_insert_of_mem hn)
    nlinarith [mul_le_mul_of_nonneg_left hs (by linarith : (0 : ℝ) ≤ 1 - x a)]

/-- Telescoping: `Σ_{k < K} (1/(N+k-2) - 1/(N+k-1)) = 1/(N-2) - 1/(N+K-2)`. -/
theorem telescope (N : ℕ) (hN : 3 ≤ N) (K : ℕ) :
    ∑ k ∈ range K, (1 / ((N + k : ℕ) - 2 : ℝ) - 1 / ((N + k : ℕ) - 1 : ℝ)) =
      1 / ((N : ℝ) - 2) - 1 / ((N + K : ℕ) - 2 : ℝ) := by
  induction K with
  | zero => simp
  | succ K ih =>
    rw [sum_range_succ, ih]
    push_cast
    have : ((N : ℝ) + (K + 1) - 2) = (N : ℝ) + K - 1 := by ring
    rw [this]; ring

theorem sum_inv_sq_le (N : ℕ) (hN : 3 ≤ N) (s : Finset ℕ) (hs : ∀ n ∈ s, N ≤ n) :
    ∑ n ∈ s, 1 / ((n : ℝ) - 1) ^ 2 ≤ 1 / ((N : ℝ) - 2) := by
  set t : ℕ → ℝ := fun n => 1 / ((n : ℝ) - 2) - 1 / ((n : ℝ) - 1)
  have hN' : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have ht : ∀ n, N ≤ n → 1 / ((n : ℝ) - 1) ^ 2 ≤ t n ∧ 0 ≤ t n := by
    intro n hn
    have hn' : (3 : ℝ) ≤ n := le_trans hN' (by exact_mod_cast hn)
    have e : t n = 1 / (((n : ℝ) - 2) * ((n : ℝ) - 1)) := by
      have ha : (n : ℝ) - 2 ≠ 0 := by intro h; linarith
      have hb : (n : ℝ) - 1 ≠ 0 := by intro h; linarith
      simp only [t]; rw [div_sub_div _ _ ha hb]; congr 1; ring
    rw [e]
    constructor
    · apply one_div_le_one_div_of_le (by nlinarith); nlinarith
    · exact (one_div_pos.mpr (by nlinarith)).le
  set K := s.sup id + 1
  have hsub : s ⊆ Ico N (N + K) := by
    intro n hn
    have : n ≤ s.sup id := le_sup (f := id) hn
    rw [mem_Ico]; exact ⟨hs n hn, by omega⟩
  calc ∑ n ∈ s, 1 / ((n : ℝ) - 1) ^ 2 ≤ ∑ n ∈ s, t n :=
        sum_le_sum fun n hn => (ht n (hs n hn)).1
    _ ≤ ∑ n ∈ Ico N (N + K), t n :=
        sum_le_sum_of_subset_of_nonneg hsub fun n hn _ => (ht n (mem_Ico.mp hn).1).2
    _ = ∑ k ∈ range K, t (N + k) := by rw [sum_Ico_eq_sum_range]; simp
    _ = 1 / ((N : ℝ) - 2) - 1 / ((N + K : ℕ) - 2 : ℝ) := telescope N hN K
    _ ≤ 1 / ((N : ℝ) - 2) := by
        have : (0 : ℝ) < ((N + K : ℕ) : ℝ) - 2 := by push_cast; linarith [Nat.cast_nonneg (α := ℝ) K]
        linarith [one_div_pos.mpr this]

/-- **The `h` part is at least `1/2`**: for `Z ≥ 4` and any `m`,
`∏_{p | m, p ≥ Z} (1 - 1/(p-1)²) ≥ 1 - 1/(Z-2) ≥ 1/2`. PROVED. -/
theorem euler_lower (Z m : ℕ) (hZ : 4 ≤ Z) :
    1 / 2 ≤ ∏ p ∈ m.primeFactors.filter (fun p => Z ≤ p), (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  set s := m.primeFactors.filter (fun p => Z ≤ p)
  have hs : ∀ n ∈ s, Z ≤ n := fun n hn => (mem_filter.mp hn).2
  have hZ' : (4 : ℝ) ≤ Z := by exact_mod_cast hZ
  have h0 : ∀ n ∈ s, 0 ≤ 1 / ((n : ℝ) - 1) ^ 2 := fun n _ => by positivity
  have h1 : ∀ n ∈ s, 1 / ((n : ℝ) - 1) ^ 2 ≤ 1 := by
    intro n hn
    have : (4 : ℝ) ≤ n := le_trans hZ' (by exact_mod_cast hs n hn)
    rw [div_le_one (by nlinarith)]; nlinarith
  have hw := one_sub_sum_le_prod s _ h0 h1
  have hsum := sum_inv_sq_le Z (by omega) s hs
  have : 1 / ((Z : ℝ) - 2) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) (by linarith)
  linarith

/-! ### The `G` part: a finite product estimate -/

theorem Np_pos (p m : ℕ) (hp : p.Prime) (hm : Odd m) : 1 ≤ Np p m := by
  obtain ⟨t, h1, h2, h3, h4⟩ := local_three p hp m (fun _ => Nat.odd_iff.mp hm)
  unfold Np
  exact card_pos.mpr ⟨t, mem_filter.mpr ⟨mem_product.mpr ⟨h1, mem_product.mpr ⟨h2, h3⟩⟩, h4⟩⟩

theorem local_factor_ge (p N : ℕ) (hp : 2 ≤ p) (hN : 1 ≤ N) :
    1 / (p : ℝ) ^ 2 ≤ (p : ℝ) * N / ((p : ℝ) - 1) ^ 3 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hq : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h3 : ((p : ℝ) - 1) ^ 3 ≤ (p : ℝ) ^ 3 := pow_le_pow_left₀ hq.le (by linarith) 3
  have h4 : (p : ℝ) ^ 3 ≤ (p : ℝ) * N * (p : ℝ) ^ 2 := by
    have : (p : ℝ) ^ 3 = (p : ℝ) * 1 * (p : ℝ) ^ 2 := by ring
    rw [this]; gcongr
  linarith

/-- **`G(q_0) ≥ 1/q_0²`** in closed form, for odd `m`: each local factor `p N_p(m)/(p-1)³`
is at least `1/p²` because `N_p(m) ≥ 1` by `local_three`. PROVED. -/
theorem G_lower (Z m : ℕ) (hm : Odd m) : 1 / ((q0 Z : ℝ)) ^ 2 ≤ Gprod Z m := by
  unfold Gprod
  have e : 1 / ((q0 Z : ℝ)) ^ 2 = ∏ p ∈ Nat.primesBelow Z, 1 / (p : ℝ) ^ 2 := by
    unfold q0; push_cast; rw [prod_div_distrib, prod_const_one, prod_pow]
  rw [e]
  refine Finset.prod_le_prod₀ (fun p _ => by positivity) fun p hp => ?_
  have hpp := Nat.prime_of_mem_primesBelow hp
  exact local_factor_ge p (Np p m) hpp.two_le (Np_pos p m hpp hm)

/-- `G(q_0) ≥ 0`, closed form. -/
theorem Gprod_nonneg (Z m : ℕ) : 0 ≤ Gprod Z m := by
  unfold Gprod
  refine prod_nonneg fun p hp => ?_
  have : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt.le
  have : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
  positivity

/-- **`q_0² ≤ (log u)^{9A}`** once `log u ≥ 1`, from `θ(x) ≤ x log 4` and `6 log 4 < 9`. -/
theorem q0_sq_le (A : ℕ) (u : ℝ) (hL : 1 ≤ Real.log u) :
    ((q0 (Zof A u) : ℝ)) ^ 2 ≤ Real.log u ^ (9 * (A : ℝ)) := by
  set y := 3 * (A : ℝ) * Real.log (Real.log u)
  have hll : 0 ≤ Real.log (Real.log u) := Real.log_nonneg hL
  have hy : 0 ≤ y := by positivity
  have hZ : (((Zof A u - 1 : ℕ)) : ℝ) ≤ y := by
    have hc := Nat.ceil_lt_add_one hy
    unfold Zof
    rcases Nat.eq_zero_or_pos ⌈y⌉₊ with h | h
    · rw [h]; simpa using hy
    · rw [Nat.cast_sub h]; push_cast; linarith
  have hθ := Chebyshev.theta_le_log4_mul_x (Nat.cast_nonneg (α := ℝ) (Zof A u - 1))
  have hlog4 : Real.log 4 < 3 / 2 := by
    have : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := Real.log_two_lt_d9; linarith
  have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hq := SizeProof.log_q0 (Zof A u)
  have hq0 : (0 : ℝ) < q0 (Zof A u) := by exact_mod_cast q0_pos _
  have hbound : 2 * Real.log (q0 (Zof A u)) ≤ Real.log (Real.log u) * (9 * A) := by
    rw [hq]
    have : Real.log 4 * (((Zof A u - 1 : ℕ)) : ℝ) ≤ 3 / 2 * y :=
      mul_le_mul hlog4.le hZ (Nat.cast_nonneg _) (by norm_num)
    simp only [y] at this
    nlinarith
  rw [Real.rpow_def_of_pos (by linarith)]
  calc ((q0 (Zof A u) : ℝ)) ^ 2 = Real.exp (2 * Real.log (q0 (Zof A u))) := by
        rw [← Real.log_rpow hq0, Real.exp_log (by positivity)]; norm_cast
    _ ≤ _ := Real.exp_le_exp.mpr hbound

/-! ### The exponent bookkeeping and MajorLower -/

/-- The final algebra: main term `u²/(4 L^{9A})` beats `C u² L^{-(9A+2)}` by `u²/L^{9A+1}`
once `L² ≥ 4 (L + C)`. -/
theorem absorb_alg (A : ℕ) (L U C : ℝ) (hL : 1 ≤ L) (hU : 0 ≤ U) (hC : 0 ≤ C)
    (hbig : 4 * (L + C) ≤ L ^ 2) :
    U / L ^ (9 * (A : ℝ) + 1) ≤
      U / (4 * L ^ (9 * (A : ℝ))) - C * U * L ^ (-(9 * (A : ℝ) + 2)) := by
  have hL0 : 0 < L := by linarith
  set D := L ^ (-(9 * (A : ℝ) + 2)) with hD
  have hDp : 0 < D := Real.rpow_pos_of_pos hL0 _
  have e1 : L ^ (9 * (A : ℝ)) * D = L ^ (-2 : ℝ) := by
    rw [hD, ← Real.rpow_add hL0]; ring_nf
  have e2 : L ^ (9 * (A : ℝ) + 1) * D = L ^ (-1 : ℝ) := by
    rw [hD, ← Real.rpow_add hL0]; ring_nf
  have m1 : L ^ (-2 : ℝ) * L ^ 2 = 1 := by
    rw [show (L ^ 2 : ℝ) = L ^ (2 : ℝ) by norm_cast, ← Real.rpow_add hL0]; simp
  have m2 : L ^ (-1 : ℝ) * L = 1 := by
    rw [Real.rpow_neg_one]; field_simp
  have hA : 0 < L ^ (9 * (A : ℝ)) := Real.rpow_pos_of_pos hL0 _
  have hA1 : 0 < L ^ (9 * (A : ℝ) + 1) := Real.rpow_pos_of_pos hL0 _
  -- 1/L^{9A} = L² D and 1/L^{9A+1} = L D
  have f1 : 1 / L ^ (9 * (A : ℝ)) = L ^ 2 * D := by
    rw [div_eq_iff hA.ne']
    calc 1 = L ^ (-2 : ℝ) * L ^ 2 := m1.symm
      _ = L ^ 2 * D * L ^ (9 * (A : ℝ)) := by rw [← e1]; ring
  have f2 : 1 / L ^ (9 * (A : ℝ) + 1) = L * D := by
    rw [div_eq_iff hA1.ne']
    calc 1 = L ^ (-1 : ℝ) * L := m2.symm
      _ = L * D * L ^ (9 * (A : ℝ) + 1) := by rw [← e2]; ring
  have g1 : U / (4 * L ^ (9 * (A : ℝ))) = U / 4 * (L ^ 2 * D) := by
    rw [← f1]; field_simp
  have g2 : U / L ^ (9 * (A : ℝ) + 1) = U * (L * D) := by
    rw [← f2]; field_simp
  rw [g1, g2]
  have : 0 ≤ U * D := mul_nonneg hU hDp.le
  nlinarith [mul_le_mul_of_nonneg_left hbig this]

/-- **MajorLower, CONDITIONAL ON `Major618 A B`, `Tail72 A B`, `Lemma82`, `Euler716`**,
with `κ = 9A + 1` and `B ≥ 36A + 3`. The bookkeeping: the main term `H 𝔖` is at least
`(u²/2)(1/q_0²)(1/2) ≥ u²/(4 (log u)^{9A})`; the (6.18) error at `ε = 1` has exponent
`12A - B + 1 ≤ -(9A + 2)`, the (7.2) error `-(B - 27A - 1) ≤ -(9A + 2)`. -/
theorem majorLower_of_inputs (A B : ℕ) (hA : 1 ≤ A) (hB : 36 * A + 3 ≤ B)
    (h618 : Major618 A B) (h72 : Tail72 A B) (h82 : Lemma82) (h716 : Euler716) :
    MajorLower A B (9 * (A : ℝ) + 1) := by
  have hBr : (36 : ℝ) * A + 3 ≤ B := by exact_mod_cast hB
  have hAr : (1 : ℝ) ≤ A := by exact_mod_cast hA
  obtain ⟨C1, u0, hC1⟩ := h618 1 one_pos
  obtain ⟨C2, u1, hC2⟩ := h72
  set C := |C1| + |C2| with hCdef
  have hC0 : 0 ≤ C := by positivity
  have hlog := Real.tendsto_log_atTop
  have hev := ((hlog.eventually_ge_atTop (4 + 4 * C)).and
    ((SizeProof.tendsto_Zof A hA).eventually_ge_atTop 4)).and
    (eventually_ge_atTop (max u0 u1))
  obtain ⟨u2, hu2⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max u2 1, fun u hu m hodd h4 h5 => ?_⟩
  obtain ⟨⟨hLbig, hZ4⟩, hmax⟩ := hu2 u (le_trans (le_max_left _ _) hu)
  have hu0 : u0 ≤ u := le_trans (le_max_left _ _) hmax
  have hu1 : u1 ≤ u := le_trans (le_max_right _ _) hmax
  set L := Real.log u with hLdef
  have hL1 : 1 ≤ L := by linarith
  have hL0 : 0 < L := by linarith
  have hbig : 4 * (L + C) ≤ L ^ 2 := by nlinarith
  set Z := Zof A u
  set I := ∫ α in majorArcs (L ^ B) (u / L ^ B), Sexp Z u α ^ 3 * ee (-(m * α))
  set SP := SingP Z m (L ^ B)
  have e618 := hC1 u hu0 m h4 h5
  have e72 := hC2 u hu1 m hodd h4 h5
  obtain ⟨x, hx, hxl⟩ := h716 Z m hodd
  have hG := h82 Z m hodd
  rw [hG, hx] at e72
  have hxh : 1 / 2 ≤ x := le_trans (euler_lower Z m hZ4) hxl
  have hGl := G_lower Z m hodd
  have hG0 := Gprod_nonneg Z m
  have hq2 := q0_sq_le A u hL1
  have hq0 : (0 : ℝ) < q0 Z := by exact_mod_cast q0_pos _
  have hLA : 0 < L ^ (9 * (A : ℝ)) := Real.rpow_pos_of_pos hL0 _
  have hGL : 1 / L ^ (9 * (A : ℝ)) ≤ Gprod Z m :=
    le_trans (one_div_le_one_div_of_le (by positivity) hq2) hGl
  -- H bounds
  have hu4 : 0 ≤ u := by
    have : (1 : ℝ) ≤ u := le_trans (le_max_right _ _) hu
    linarith
  have hH1 := Hmu_ge m u h4 h5
  have hH2 : Hmu m u ≤ u ^ 2 := by
    unfold Hmu; nlinarith [sq_nonneg ((m : ℝ) - 4 * u), sq_nonneg (5 * u - m)]
  -- exponent comparisons
  have hx1 : L ^ (12 * (A : ℝ) - B + 1) ≤ L ^ (-(9 * (A : ℝ) + 2)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hx2 : L ^ (-((B : ℝ) - 27 * A - 1)) ≤ L ^ (-(9 * (A : ℝ) + 2)) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  set D := L ^ (-(9 * (A : ℝ) + 2))
  have hD0 : 0 ≤ D := (Real.rpow_pos_of_pos hL0 _).le
  have hE1 : 0 ≤ L ^ (12 * (A : ℝ) - B + 1) := (Real.rpow_pos_of_pos hL0 _).le
  have hE2 : 0 ≤ L ^ (-((B : ℝ) - 27 * A - 1)) := (Real.rpow_pos_of_pos hL0 _).le
  -- real parts
  have r1 : (Hmu m u : ℝ) * SP.re - ‖I - (Hmu m u : ℂ) * SP‖ ≤ I.re := by
    have := Complex.abs_re_le_norm (I - (Hmu m u : ℂ) * SP)
    have h' : (I - (Hmu m u : ℂ) * SP).re = I.re - Hmu m u * SP.re := by
      simp [Complex.sub_re, Complex.mul_re]
    rw [h'] at this; linarith [neg_abs_le (I.re - Hmu m u * SP.re), le_abs_self (I.re - Hmu m u * SP.re)]
  have r2 : Gprod Z m * x - ‖SP - (Gprod Z m : ℂ) * (x : ℂ)‖ ≤ SP.re := by
    have := Complex.abs_re_le_norm (SP - (Gprod Z m : ℂ) * (x : ℂ))
    have h' : (SP - (Gprod Z m : ℂ) * (x : ℂ)).re = SP.re - Gprod Z m * x := by
      simp [Complex.sub_re, Complex.mul_re]
    rw [h'] at this
    linarith [le_abs_self (SP.re - Gprod Z m * x), neg_abs_le (SP.re - Gprod Z m * x)]
  -- assemble
  have hmain : u ^ 2 / (4 * L ^ (9 * (A : ℝ))) ≤ Hmu m u * (Gprod Z m * x) := by
    have : u ^ 2 / (4 * L ^ (9 * (A : ℝ))) = (u ^ 2 / 2) * ((1 / L ^ (9 * (A : ℝ))) * (1 / 2)) := by
      field_simp; ring
    rw [this]
    apply mul_le_mul hH1 (mul_le_mul hGL hxh (by norm_num) hG0) (by positivity) (by linarith)
  have hT2 : Hmu m u * ‖SP - (Gprod Z m : ℂ) * (x : ℂ)‖ ≤ |C2| * u ^ 2 * D := by
    have hn := le_trans e72 (mul_le_mul_of_nonneg_right (le_abs_self C2) hE2)
    calc Hmu m u * ‖SP - (Gprod Z m : ℂ) * (x : ℂ)‖
        ≤ u ^ 2 * (|C2| * L ^ (-((B : ℝ) - 27 * A - 1))) :=
          mul_le_mul hH2 hn (norm_nonneg _) (by positivity)
      _ ≤ u ^ 2 * (|C2| * D) := by gcongr
      _ = |C2| * u ^ 2 * D := by ring
  have hT1 : ‖I - (Hmu m u : ℂ) * SP‖ ≤ |C1| * u ^ 2 * D := by
    calc ‖I - (Hmu m u : ℂ) * SP‖ ≤ C1 * u ^ 2 * L ^ (12 * (A : ℝ) - B + 1) := e618
      _ ≤ |C1| * u ^ 2 * L ^ (12 * (A : ℝ) - B + 1) := by
          gcongr; exact le_abs_self C1
      _ ≤ |C1| * u ^ 2 * D := by gcongr
  have hHSP : Hmu m u * (Gprod Z m * x) - Hmu m u * ‖SP - (Gprod Z m : ℂ) * (x : ℂ)‖ ≤
      Hmu m u * SP.re := by
    have hH0 : 0 ≤ Hmu m u := le_trans (by positivity) hH1
    nlinarith [mul_le_mul_of_nonneg_left r2 hH0]
  have hfin := absorb_alg A L (u ^ 2) C hL1 (by positivity) hC0 hbig
  have hCU : C * u ^ 2 * D = |C1| * u ^ 2 * D + |C2| * u ^ 2 * D := by rw [hCdef]; ring
  linarith

/-- **RepProp A, CONDITIONAL ON `Minor516W A B`, `Major618 A B`, `Tail72 A B`, `Lemma82`,
`Euler716`**, for `A ≥ 1`, `B ≥ 36A + 3` and `B ≥ 28A + 13`; the second condition is
`κ = 9A + 1 < B/2 - 5A - 5`. -/
theorem repProp_of_inputs (A B : ℕ) (hA : 1 ≤ A) (hB1 : 36 * A + 3 ≤ B) (hB2 : 28 * A + 13 ≤ B)
    (hmin : RepAssembly.Minor516W A B) (h618 : Major618 A B) (h72 : Tail72 A B)
    (h82 : Lemma82) (h716 : Euler716) : RepProp A := by
  have hB2r : (28 : ℝ) * A + 13 ≤ B := by exact_mod_cast hB2
  exact RepAssembly.repProp_of_parts A B (9 * (A : ℝ) + 1) (by linarith) hmin
    (majorLower_of_inputs A B hA hB1 h618 h72 h82 h716)

/-! ### Vacuity tests -/

/-- The side conditions of `repProp_of_inputs` hold at `A = 1`, `B = 41`. -/
example : 1 ≤ (1 : ℕ) ∧ 36 * 1 + 3 ≤ (41 : ℕ) ∧ 28 * 1 + 13 ≤ (41 : ℕ) := by norm_num

/-- `euler_lower` at `Z = 4`, `m = 35 = 5 · 7`: both prime factors are counted. -/
example : 1 / 2 ≤ ∏ p ∈ (35 : ℕ).primeFactors.filter (fun p => 4 ≤ p),
    (1 - 1 / ((p : ℝ) - 1) ^ 2) := euler_lower 4 35 le_rfl

/-- `G_lower` at `Z = 4`, `m = 1`: `q_0 = 6`, a genuine instance with two primes. -/
example : 1 / ((q0 4 : ℝ)) ^ 2 ≤ Gprod 4 1 := G_lower 4 1 odd_one

/-- `q0_sq_le` applies at `u = e^e`, where `log u = e ≥ 1`. -/
example : ((q0 (Zof 1 (Real.exp (Real.exp 1))) : ℝ)) ^ 2 ≤
    Real.log (Real.exp (Real.exp 1)) ^ (9 * ((1 : ℕ) : ℝ)) := by
  refine q0_sq_le 1 _ ?_
  rw [Real.log_exp]; have := Real.add_one_le_exp 1; linarith

end LeanLab.SparseTernary.MajorArcs

#print axioms LeanLab.SparseTernary.MajorArcs.qell_of_dvd
#print axioms LeanLab.SparseTernary.MajorArcs.euler_lower
#print axioms LeanLab.SparseTernary.MajorArcs.G_lower
#print axioms LeanLab.SparseTernary.MajorArcs.q0_sq_le
#print axioms LeanLab.SparseTernary.MajorArcs.majorLower_of_inputs
#print axioms LeanLab.SparseTernary.MajorArcs.repProp_of_inputs
