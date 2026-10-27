/-
Unit U-1543, run 20261026T0808Z-17522, track T1. Decomposition of Proposition 6.1 of
Liu-Wang 2002, Acta Arith. 105, pp. 133-175, the explicit Vinogradov estimate for the
exponential sum over primes, pp. 168-174, the step that bounds `S(α)` on the arcs `M4`.
This file holds the objects of Section 6, the Vaughan split (6.7)-(6.8) p. 168-169, and the
dyadic, Cauchy and counting leaves of Lemma 6.7, (6.10)-(6.12) p. 170-171, (6.20) p. 173 and
the first line of p. 174. Source: papers/P0023.pdf, pages rendered with pdftoppm.
Leaves carry `sorry` and are the open work. Three inputs from other papers, two lemmas of
Wang-Chen 1994 and a Rosser-Schoenfeld 1962 bound, also carry `sorry`; their doc comments
say so. Assemblies have real proofs and are CONDITIONAL ON the leaves; they are here and in
Decomp1543b and Decomp1543c.
AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.LiuWang2002.U1543

open Real Finset ArithmeticFunction

/-! ### Objects of Section 6 -/

/-- `e(x) = exp(2πix)`, p. 144 above (3.8). -/
noncomputable def e (x : ℝ) : ℂ := Complex.exp (2 * π * Complex.I * x)

/-- `‖x‖`, the distance from `x` to the nearest integer, Lemma 6.3 p. 169. -/
noncomputable def nint (x : ℝ) : ℝ := |x - round x|

/-- `min(X, 1/(2‖θ‖))`, read as `X` when `θ` is an integer. -/
noncomputable def minK (X θ : ℝ) : ℝ := if nint θ = 0 then X else min X (1 / (2 * nint θ))

/-- The range `cN < n ≤ N` of (6.8) p. 169. -/
noncomputable def rangeN (c : ℝ) (N : ℕ) : Finset ℕ := (Icc 1 N).filter (fun n => c * N < n)

/-- (6.8) p. 169: `∑_{cN<n≤N} f(n) e(αn)`. With `f = Λ` this is `S(α)` of Proposition 6.1;
the paper's (3.8) also counts the endpoint `n = cN`, which changes `S` by at most `log N`. -/
noncomputable def Ssum (f : ℕ → ℝ) (c : ℝ) (N : ℕ) (α : ℝ) : ℂ :=
  ∑ n ∈ rangeN c N, (f n : ℂ) * e (α * n)

/-- `Λ1` of (6.8): `Λ(n)` for `n ≤ U`, else `0`. -/
noncomputable def lam1 (U : ℝ) (n : ℕ) : ℝ := if (n : ℝ) ≤ U then vonMangoldt n else 0

/-- `Λ2` of (6.8): `∑_{mt=n, t≤V} μ(t) log m`. -/
noncomputable def lam2 (V : ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ n.divisors.filter (fun t : ℕ => (t : ℝ) ≤ V), (moebius t : ℝ) * Real.log ((n / t : ℕ) : ℝ)

/-- `Λ3` of (6.8): `-∑_{rt | n, r≤U, t≤V} Λ(r) μ(t)`. -/
noncomputable def lam3 (U V : ℝ) (n : ℕ) : ℝ :=
  -∑ r ∈ n.divisors, ∑ t ∈ n.divisors,
    if (r : ℝ) ≤ U ∧ (t : ℝ) ≤ V ∧ r * t ∣ n then vonMangoldt r * (moebius t : ℝ) else 0

/-- `a_m = ∑_{r | m, r > U} Λ(r)`, (6.10) p. 170. -/
noncomputable def am (U : ℝ) (m : ℕ) : ℝ :=
  ∑ r ∈ m.divisors.filter (fun r : ℕ => U < (r : ℝ)), vonMangoldt r

/-- `Λ4` of (6.8): `∑_{mt=n, t>V} μ(t) a_m`. -/
noncomputable def lam4 (U V : ℝ) (n : ℕ) : ℝ :=
  ∑ t ∈ n.divisors.filter (fun t : ℕ => V < (t : ℝ)), (moebius t : ℝ) * am U (n / t)

/-- `U = N^(2/5) log^(-4/5) N`, (6.6) p. 168. -/
noncomputable def Uf (N : ℕ) : ℝ := (N : ℝ) ^ ((2 : ℝ) / 5) * Real.log N ^ (-(4 : ℝ) / 5)

/-- `V = N^(2/5) log^(1/5) N`, (6.6) p. 168. -/
noncomputable def Vf (N : ℕ) : ℝ := (N : ℝ) ^ ((2 : ℝ) / 5) * Real.log N ^ ((1 : ℝ) / 5)

/-- (6.1) p. 168: `α = a/q + θ/q^2` with `q ≥ 1`, `(a, q) = 1`, `|θ| ≤ 1`. -/
def Dioph (α : ℝ) (a : ℤ) (q : ℕ) : Prop :=
  1 ≤ q ∧ Int.gcd a q = 1 ∧ |α - a / q| ≤ 1 / (q : ℝ) ^ 2

/-- The dyadic block `M < t ≤ 2M`, cut to `[1, N]`, of (6.11) p. 170. -/
noncomputable def tBlock (N : ℕ) (M : ℝ) : Finset ℕ := (Icc 1 N).filter (fun t => M < t ∧ (t : ℝ) ≤ 2 * M)

/-- The inner range `cN/t < m ≤ N/t, m > U` of (6.11). -/
noncomputable def mRange (c : ℝ) (N : ℕ) (U : ℝ) (t : ℕ) : Finset ℕ :=
  (Icc 1 N).filter (fun m => c * N < ((m * t : ℕ) : ℝ) ∧ m * t ≤ N ∧ U < m)

/-- The inner sum `∑_{cN/t<m≤N/t, m>U} a_m e(αmt)` of (6.11). -/
noncomputable def inner (c : ℝ) (N : ℕ) (U α : ℝ) (t : ℕ) : ℂ :=
  ∑ m ∈ mRange c N U t, (am U m : ℂ) * e (α * ((m * t : ℕ) : ℝ))

/-- One dyadic block of `S4`, `∑_{M<t≤2M} μ(t) ∑_m a_m e(αmt)`, (6.11). -/
noncomputable def block (c : ℝ) (N : ℕ) (U M α : ℝ) : ℂ :=
  ∑ t ∈ tBlock N M, (moebius t : ℂ) * inner c N U α t

/-- `J = [log(N/(UV))/log 2] + 1`, (6.10) p. 170. -/
noncomputable def Jn (N : ℕ) (U V : ℝ) : ℕ := ⌊Real.log (N / (U * V)) / Real.log 2⌋₊ + 1

/-- The range `U < m ≤ X` in `[1, N]`, used in (6.12) with `X = N/M_j`. -/
noncomputable def lRange (N : ℕ) (U X : ℝ) : Finset ℕ := (Icc 1 N).filter (fun m => U < m ∧ (m : ℝ) ≤ X)

/-! ### Inputs from other papers -/

/-- Lemma 6.3 p. 169, the statement of Wang-Chen 1994, Lemma 2. -/
def WCLemma2 : Prop :=
  ∀ (α : ℝ) (a : ℤ) (q : ℕ), Dioph α a q → ∀ X : ℝ, 0 < X → ∀ (Y : ℕ) (Z : ℤ), 1 ≤ Y →
    ∑ n ∈ Ioc Z (Z + Y), minK X (α * n) ≤ (((Y / q : ℕ) : ℝ) + 1) * (5 * X + q * Real.log q)

/-- CITED, not proved in the lab: Lemma 6.3 p. 169 is [WC, Lemma 2], Wang-Chen, Acta Math.
Sinica 37 (1994). The paper says `‖x‖` is the fractional part; we read the distance to the
nearest integer, which gives the weaker statement and is what the proof of Lemma 6.7 uses. -/
theorem wc_lemma2 : WCLemma2 := by sorry

/-! ### Leaves -/

/-- LEAF. Unit U-1543. The Vaughan identity (6.7), coefficientwise: for `V ≥ 1` and `n ≥ 1`,
`Λ(n) = Λ1(n) + Λ2(n) + Λ3(n) + Λ4(n)` with the four functions of (6.8), p. 168-169. It follows
from `Akeno2026.Vaughan86.vaughan_identity` with the roles of `U` and `V` exchanged. -/
theorem vaughan_coeff (U V : ℝ) (hV : 1 ≤ V) (n : ℕ) (hn : 1 ≤ n) :
    (vonMangoldt n : ℝ) = lam1 U n + lam2 V n + lam3 U V n + lam4 U V n := by sorry

/-- LEAF. Unit U-1543. Cauchy's inequality for one dyadic block, (6.11) p. 170:
`|∑_t μ(t) z_t| ≤ (∑_t |μ(t)|)^(1/2) (∑_t |z_t|^2)^(1/2)`, using `μ(t)^2 = |μ(t)|`. -/
theorem block_cauchy (T : Finset ℕ) (z : ℕ → ℂ) :
    ‖∑ t ∈ T, (moebius t : ℂ) * z t‖ ≤
      √(∑ t ∈ T, |(moebius t : ℝ)|) * √(∑ t ∈ T, ‖z t‖ ^ 2) := by sorry

/-- LEAF. Unit U-1543. The geometric sum over a run of integers inside `(M, 2M]`:
`|∑_{A<t≤B} e(θt)| ≤ min(M + 0.5, 1/(2‖θ‖))`, used for the first display of p. 171.
The run has at most `[2M] - [M] ≤ M + 0.5` terms. -/
theorem geom_dyadic (θ M : ℝ) (hM : 0 ≤ M) (A B : ℤ) (hA : ⌊M⌋ ≤ A) (hB : B ≤ ⌊2 * M⌋) :
    ‖∑ t ∈ Ioc A B, e (θ * t)‖ ≤ minK (M + 1 / 2) θ := by sorry

/-- LEAF. Unit U-1543. The first display of p. 171: expanding the square in (6.11) and
summing over `t` first,
`∑_{M<t≤2M} |∑_m a_m e(αmt)|^2 ≤ ∑_{U<m≤N/M} a_m^2 ∑_{U<l≤N/M} min(M + 0.5, 1/(2‖α(m-l)‖))`,
given the geometric sum bound `hgeom`, which is `geom_dyadic`. -/
theorem square_expand (c : ℝ) (N : ℕ) (U M α : ℝ) (hU : 0 ≤ U) (hM : 1 ≤ M)
    (hgeom : ∀ θ : ℝ, ∀ A B : ℤ, ⌊M⌋ ≤ A → B ≤ ⌊2 * M⌋ →
      ‖∑ t ∈ Ioc A B, e (θ * t)‖ ≤ minK (M + 1 / 2) θ) :
    ∑ t ∈ tBlock N M, ‖inner c N U α t‖ ^ 2 ≤
      ∑ m ∈ lRange N U (N / M), am U m ^ 2 *
        ∑ l ∈ lRange N U (N / M), minK (M + 1 / 2) (α * ((m : ℝ) - l)) := by sorry

/-- LEAF. Unit U-1543. (6.12) p. 171: Lemma 6.3 applied to the sum over `l`, with
`n = m - l` running over `[Y] - [U]` consecutive integers:
`∑_{U<l≤Y} min(X, 1/(2‖α(m-l)‖)) ≤ ([([Y] - [U])/q] + 1)(5X + q log q)`. -/
theorem inner_l_sum (hwc : WCLemma2) (α : ℝ) (a : ℤ) (q : ℕ) (hD : Dioph α a q) (N : ℕ)
    (U Y X : ℝ) (hU : 0 ≤ U) (hX : 0 < X) (m : ℕ) :
    ∑ l ∈ lRange N U Y, minK X (α * ((m : ℝ) - l)) ≤
      ((((⌊Y⌋₊ - ⌊U⌋₊) / q : ℕ) : ℝ) + 1) * (5 * X + q * Real.log q) := by sorry

/-- LEAF. Unit U-1543. (6.10)-(6.11) p. 170: substituting `n = mt` in `S4`, dropping the
`m ≤ U` terms, where `a_m = 0`, and cutting `V < t < N/U` into the `J` dyadic blocks
`(2^j V, 2^(j+1) V]`, `0 ≤ j < J`, gives `S4(α) = ∑_j block_j`. -/
theorem S4_dyadic (c : ℝ) (N : ℕ) (U V α : ℝ) (hU : 0 < U) (hV : 0 < V) :
    Ssum (lam4 U V) c N α = ∑ j ∈ range (Jn N U V), block c N U (2 ^ j * V) α := by sorry

/-- LEAF. Unit U-1543. (6.20) p. 173: for `M ≥ exp(13.066)`, the squarefree count
`∑_{M<t≤2M} |μ(t)| ≤ 0.6111 M`. -/
theorem squarefree_dyadic (N : ℕ) (M : ℝ) (hM : exp 13.066 ≤ M) :
    ∑ t ∈ tBlock N M, |(moebius t : ℝ)| ≤ 0.6111 * M := by sorry

/-- LEAF. Unit U-1543. P. 174, line 1: `∑_{j=1}^J M_j^(1/2) ≤ (2 + √2)(N/U)^(1/2)` with
`M_j = 2^(j-1) V`, given `M_J ≤ N/U`. -/
theorem dyadic_sqrt_sum (N : ℕ) (U V : ℝ) (hU : 0 < U) (hV : 0 < V) (J : ℕ) (hJ : 1 ≤ J)
    (hJV : 2 ^ (J - 1) * V ≤ N / U) :
    ∑ j ∈ range J, √(2 ^ j * V) ≤ (2 + √2) * √(N / U) := by sorry

/-- LEAF. Unit U-1543. P. 174, line 2: `∑_{j=1}^J M_j^(-1/2) ≤ (2 + √2) V^(-1/2)`. -/
theorem dyadic_invsqrt_sum (V : ℝ) (hV : 0 < V) (J : ℕ) :
    ∑ j ∈ range J, 1 / √(2 ^ j * V) ≤ (2 + √2) / √V := by sorry

/-- LEAF. Unit U-1543. (6.10) p. 170: with `J = [log(N/(UV))/log 2] + 1` and `UV ≤ N`,
`M_J = 2^(J-1) V ≤ N/U` and `J ≤ 1 + log(N/(UV))/log 2`. -/
theorem J_props (N : ℕ) (U V : ℝ) (hU : 0 < U) (hV : 0 < V) (hUV : U * V ≤ N) :
    2 ^ (Jn N U V - 1) * V ≤ N / U ∧
      (Jn N U V : ℝ) ≤ 1 + Real.log (N / (U * V)) / Real.log 2 := by sorry

/-! ### Assembly -/

/-- (6.7) p. 168: `S = S1 + S2 + S3 + S4`. PROVED, CONDITIONAL ON `vaughan_coeff`. -/
theorem S_split (c : ℝ) (N : ℕ) (U V α : ℝ) (hV : 1 ≤ V) :
    Ssum (fun n => (vonMangoldt n : ℝ)) c N α =
      Ssum (lam1 U) c N α + Ssum (lam2 V) c N α + Ssum (lam3 U V) c N α +
        Ssum (lam4 U V) c N α := by
  unfold Ssum
  rw [← sum_add_distrib, ← sum_add_distrib, ← sum_add_distrib]
  refine sum_congr rfl fun n hn => ?_
  have hn1 : 1 ≤ n := (mem_Icc.mp (mem_filter.mp hn).1).1
  dsimp only
  rw [vaughan_coeff U V hV n hn1]
  push_cast
  ring

/-! ### Vacuity instances -/

/-- Vacuity: `Dioph` holds for `α = 0`, `a = 0`, `q = 1`. PROVED. -/
theorem dioph_inhabited : Dioph 0 0 1 := by
  refine ⟨le_rfl, by decide, ?_⟩
  norm_num

/-- Vacuity: the hypotheses of `WCLemma2` can hold, and its conclusion holds in the case
`q = 1`, `X = 1`, `Y = 1`, `Z = 0`, `α = 0`: `min(1, ...) = 1 ≤ 2 · 5`. PROVED. -/
theorem wcLemma2_instance :
    Dioph 0 0 1 ∧ ∑ n ∈ Ioc (0 : ℤ) (0 + (1 : ℕ)), minK 1 (0 * n) ≤
      ((((1 : ℕ) / 1 : ℕ) : ℝ) + 1) * (5 * 1 + (1 : ℕ) * Real.log (1 : ℕ)) := by
  refine ⟨dioph_inhabited, ?_⟩
  have h : Ioc (0 : ℤ) (0 + (1 : ℕ)) = {1} := by decide
  rw [h, sum_singleton]
  simp [minK, nint]
  norm_num

end LeanLab.LiuWang2002.U1543
