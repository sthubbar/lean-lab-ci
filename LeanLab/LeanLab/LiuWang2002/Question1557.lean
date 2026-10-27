/-
Unit U-1557, run 20261026T1604Z-17563, track T1 QUESTION. Liu-Wang 2002, Acta Arith. 105,
pp. 168-174, Proposition 6.1 on the range `30.95 ≤ log N < 40.06`.
Background: F-0071 PRELIMINARY, units U-1543, U-1548, U-1553. The step `log U / log(N/V) ≥ 2/3`
of p. 173 is false, and the printed chain for Proposition 6.1 then fails for `log N < 40.06`.
Question: is Proposition 6.1 itself true there?
Answer stated here, numerics in Python, scratch file u1557/num.py and num2.py of the run:
* YES, by the paper's own method. Keep `x_j = log(N/M_j)` inside the bound for `W` of
  (6.13)-(6.17), instead of the p. 173 step `log(N/M_j) ≤ log(N/V)` followed by the false `5/9`.
  Then the `q^(-1/2)` coefficient of Lemma 6.7 is at most `0.1635` on the range, so the total is
  at most `0.2048 ≤ 0.28`. The other two totals are at most `2.22 ≤ 4` and `0.058 ≤ 0.09`.
* For `log N ≤ 32.636` the trivial bound `1.0012 N` alone already gives (6.2) for every `q`.
* The paper uses Proposition 6.1 only for `log N ≥ 3100`, proof of Theorem 1 p. 174.
Lean content: the question and its inputs as Props, three PROVED reduction steps with clean
axioms, the PROVED assembly `prop61At_of_inputs`, CONDITIONAL ON the named Props, and vacuity
instances. The numerical leaf `KeptNumAt` and the sharpened `Lemma67KeptAt` stay OPEN as Props.
AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.LiuWang2002.Decomp1543c

namespace LeanLab.LiuWang2002.U1557

open Real Finset ArithmeticFunction LeanLab.LiuWang2002.U1543

/-! ### The question -/

/-- The right side of (6.2) p. 168. -/
noncomputable def rhs62 (N q : ℕ) : ℝ :=
  0.28 * N / √q * Real.log N ^ 2 + 4 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) +
    0.09 * √N * √q * Real.log N ^ (2.5 : ℝ)

/-- Proposition 6.1 p. 168 at one `N`: for every `0 < c < 1` and every `α` as in (6.1),
`|S(α)| ≤ rhs62 N q`. `Ssum` sums `cN < n ≤ N`, the range of (6.8). -/
def Prop61At (N : ℕ) : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 → ∀ (α : ℝ) (a : ℤ) (q : ℕ), Dioph α a q →
    ‖Ssum (fun n => (vonMangoldt n : ℝ)) c N α‖ ≤ rhs62 N q

/-- QUESTION U-1557: Proposition 6.1 holds for every `N` with `30.95 ≤ log N < 40.06`. -/
def Q1557 : Prop :=
  ∀ N : ℕ, 30.95 ≤ Real.log N → Real.log N < 40.06 → Prop61At N

/-! ### Inputs, stated as Props -/

/-- P. 168: `|S(α)| ≤ ∑_{n≤N} Λ(n) ≤ 1.0012 N`, from [RS2] (3.6) and [RS1] (5.1), (5.3). -/
def TrivialPsiAt (N : ℕ) : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 → ∀ α : ℝ, ‖Ssum (fun n => (vonMangoldt n : ℝ)) c N α‖ ≤ 1.0012 * N

/-- Numerical leaf, Python: for every `q ≥ 1`, `1.0012 N ≤ rhs62 N q`. True exactly when
`log N ≤ 32.6367`, by the minimum over real `q`. -/
def MinRhsAbove (N : ℕ) : Prop := ∀ q : ℕ, 1 ≤ q → 1.0012 * N ≤ rhs62 N q

/-- (6.3) p. 168. -/
def InRange63 (N q : ℕ) : Prop :=
  (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q ∧ (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5

/-- (6.7) p. 168, `S = S1 + S2 + S3 + S4`; `U1543.S_split` gives it from `vaughan_coeff`. -/
def SplitAt (N : ℕ) : Prop :=
  ∀ c α : ℝ, Ssum (fun n => (vonMangoldt n : ℝ)) c N α =
    Ssum (lam1 (Uf N)) c N α + Ssum (lam2 (Vf N)) c N α + Ssum (lam3 (Uf N) (Vf N)) c N α +
      Ssum (lam4 (Uf N) (Vf N)) c N α

/-- Lemma 6.2 p. 169: `|S1(α)| ≤ 1.02 U`. -/
def Lemma62At (N : ℕ) : Prop := ∀ c α : ℝ, ‖Ssum (lam1 (Uf N)) c N α‖ ≤ 1.02 * Uf N

/-- Lemma 6.5 p. 169, printed constants, for `q` in (6.3). -/
def Lemma65At (N : ℕ) : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 → ∀ (α : ℝ) (a : ℤ) (q : ℕ), Dioph α a q → InRange63 N q →
    ‖Ssum (lam2 (Vf N)) c N α‖ ≤ 0.0282 * N / √q * Real.log N ^ 2 +
      0.0001 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) +
        0.0006 * √N * √q * Real.log N ^ (2.5 : ℝ)

/-- Lemma 6.6 p. 170, printed constants, for `q` in (6.3). -/
def Lemma66At (N : ℕ) : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 → ∀ (α : ℝ) (a : ℤ) (q : ℕ), Dioph α a q → InRange63 N q →
    ‖Ssum (lam3 (Uf N) (Vf N)) c N α‖ ≤ 0.0131 * N / √q * Real.log N ^ 2 +
      0.8 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) +
        0.0005 * √N * √q * Real.log N ^ (2.5 : ℝ)

/-- The budget form of Lemma 6.7 that Proposition 6.1 needs, with `0.2387 = 0.28 - 0.0282 -
0.0131`, `3.1 ≤ 4 - 0.0001 - 0.8 - 0.0999`, `0.0889 = 0.09 - 0.0006 - 0.0005`. The paper prints
`0.2264`, `2.787`, `0.0785`. -/
def Lemma67Mid (N : ℕ) : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 → ∀ (α : ℝ) (a : ℤ) (q : ℕ), Dioph α a q → InRange63 N q →
    ‖Ssum (lam4 (Uf N) (Vf N)) c N α‖ ≤ 0.2387 * N / √q * Real.log N ^ 2 +
      3.1 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) +
        0.0889 * √N * √q * Real.log N ^ (2.5 : ℝ)

/-! ### The sharpened chain of Lemma 6.7 -/

/-- The bound for `W / X` of (6.13)-(6.17), first display of p. 173, kept as a function of
`x = log X`: `(x^2 - a^2)/2 + 0.105 x + 2.5876 + 2 · 0.0681` with `a = log U`. -/
noncomputable def wK (a x : ℝ) : ℝ := (x ^ 2 - a ^ 2) / 2 + 0.105 * x + 2.5876 + 2 * 0.0681

/-- `x_j = log(N/M_j)` for `M_j = 2^j V`, `j = 0, ..., J-1`; the paper indexes from `1`. -/
noncomputable def xj (N j : ℕ) : ℝ := Real.log (N / Vf N) - j * Real.log 2

/-- `M_j = 2^j V`, (6.10) p. 170. -/
noncomputable def Mj (N j : ℕ) : ℝ := 2 ^ j * Vf N

/-- The kept form of (6.12)-(6.13), before the step of p. 173: for `U ≤ X ≤ N/V`,
`W ≤ X · wK(log U, log X)`. -/
def WKeptAt (N : ℕ) : Prop :=
  ∀ X : ℝ, Uf N ≤ X → X ≤ N / Vf N → Wsum N (Uf N) X ≤ X * wK (Real.log (Uf N)) (Real.log X)

/-- The right side of (6.21) with `W_j` bounded by `WKeptAt` block by block:
`0.6111^(1/2) N^(1/2) ∑_j wK(a, x_j)^(1/2) ((5N/q)^(1/2) + (5M_j)^(1/2) + (N log q/M_j)^(1/2)
+ (q log q)^(1/2))`. -/
noncomputable def keptRHS (N q : ℕ) : ℝ :=
  √0.6111 * √N * ∑ j ∈ range (Jn N (Uf N) (Vf N)),
    √(wK (Real.log (Uf N)) (xj N j)) *
      (√(5 * N / q) + √5 * √(Mj N j) + √(N * Real.log q) / √(Mj N j) + √(q * Real.log q))

/-- Lemma 6.7 by the sharpened chain: (6.11), (6.12), (6.19), (6.20), (6.21) with `WKeptAt`
in place of the p. 173 display. OPEN as stated; the U-1543 proof of `block_bound` and `lemma67`
carries over with `WKeptAt` in place of `W_bound`. -/
def Lemma67KeptAt (N : ℕ) : Prop :=
  ∀ c : ℝ, 0 < c → c < 1 → ∀ (α : ℝ) (a : ℤ) (q : ℕ), Dioph α a q → InRange63 N q →
    ‖Ssum (lam4 (Uf N) (Vf N)) c N α‖ ≤ keptRHS N q

/-- Numerical leaf, Python: the kept right side fits the budget of `Lemma67Mid`. Python finds
the three coefficients at most `0.1635`, `1.42`, `0.0568` on `30.95 ≤ log N < 40.06`. -/
def KeptNumAt (N : ℕ) : Prop :=
  ∀ q : ℕ, InRange63 N q → keptRHS N q ≤ 0.2387 * N / √q * Real.log N ^ 2 +
    3.1 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) +
      0.0889 * √N * √q * Real.log N ^ (2.5 : ℝ)

/-! ### Proofs -/

/-- PROVED. The sharpened chain implies the budget form of Lemma 6.7. -/
theorem lemma67Mid_of_kept (N : ℕ) (hK : Lemma67KeptAt N) (hn : KeptNumAt N) :
    Lemma67Mid N := fun c hc0 hc1 α a q hD hq => (hK c hc0 hc1 α a q hD hq).trans (hn q hq)

/-- PROVED. The kept bound is never worse than the paper's chain before the false step: each
block term is at most the `j = 0` term, `wK(a, x_j) ≤ wK(a, log(N/V))`, when all `x_j ≥ 0`. -/
theorem keptSum_le_paper (a b : ℝ) (J : ℕ) (hJ : 0 ≤ b - (J - 1 : ℝ) * Real.log 2) :
    ∑ j ∈ range J, √(wK a (b - j * Real.log 2)) ≤ J * √(wK a b) := by
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have key : ∀ j ∈ range J, √(wK a (b - j * Real.log 2)) ≤ √(wK a b) := by
    intro j hj
    have hjJ : (j : ℝ) ≤ J - 1 := by
      have : j + 1 ≤ J := mem_range.mp hj
      have : ((j + 1 : ℕ) : ℝ) ≤ J := by exact_mod_cast this
      push_cast at this; linarith
    have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
    have hx0 : 0 ≤ b - j * Real.log 2 := by nlinarith
    have hxb : b - j * Real.log 2 ≤ b := by nlinarith
    apply Real.sqrt_le_sqrt
    unfold wK
    nlinarith
  calc ∑ j ∈ range J, √(wK a (b - j * Real.log 2)) ≤ ∑ _j ∈ range J, √(wK a b) :=
        sum_le_sum key
    _ = J * √(wK a b) := by rw [sum_const, card_range, nsmul_eq_mul]

/-- PROVED. The case `q ≤ (0.28/1.0012)^2 log^4 N` of p. 168: the first term of (6.2) is at
least `1.0012 N`. -/
theorem rhs_small_q (N q : ℕ) (hq : 1 ≤ q)
    (hq1 : (q : ℝ) ≤ (0.28 / 1.0012) ^ 2 * Real.log N ^ 4) : 1.0012 * N ≤ rhs62 N q := by
  set L := Real.log N
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hs : 0 < √(q : ℝ) := Real.sqrt_pos.mpr hq0
  have hsq : √(q : ℝ) ≤ 0.28 / 1.0012 * L ^ 2 := by
    have e : (0.28 / 1.0012) ^ 2 * L ^ 4 = (0.28 / 1.0012 * L ^ 2) ^ 2 := by ring
    rw [e] at hq1
    calc √(q : ℝ) ≤ √((0.28 / 1.0012 * L ^ 2) ^ 2) := Real.sqrt_le_sqrt hq1
      _ = 0.28 / 1.0012 * L ^ 2 := Real.sqrt_sq (by positivity)
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have h1 : 1.0012 * N ≤ 0.28 * N / √q * L ^ 2 := by
    rw [div_mul_eq_mul_div, le_div_iff₀ hs]
    nlinarith
  have h2 : 0 ≤ 4 * (N : ℝ) ^ ((4 : ℝ) / 5) * L ^ (1.4 : ℝ) := by positivity
  have h3 : 0 ≤ 0.09 * √(N : ℝ) * √q * L ^ (2.5 : ℝ) := by positivity
  unfold rhs62
  linarith

/-- PROVED. The case `q ≥ (1.0012/0.09)^2 N log^(-5) N` of p. 168: the third term of (6.2) is
at least `1.0012 N`. -/
theorem rhs_large_q (N q : ℕ) (hL : 1 ≤ Real.log N)
    (hq2 : (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5 ≤ q) : 1.0012 * N ≤ rhs62 N q := by
  set L := Real.log N
  have hL0 : 0 < L := by linarith
  have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg q
  set P := L ^ (2.5 : ℝ) with hP
  have hP0 : 0 ≤ P := by positivity
  have hP2 : P ^ 2 = L ^ 5 := by
    rw [hP, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]
    norm_num
  have hqP : (1.0012 / 0.09) ^ 2 * N ≤ q * P ^ 2 := by
    rw [hP2]; rwa [div_le_iff₀ (by positivity)] at hq2
  set X := √(N : ℝ) * √q * P with hX
  have hX0 : 0 ≤ X := by positivity
  have hX2 : X ^ 2 = N * q * P ^ 2 := by
    rw [hX, mul_pow, mul_pow, Real.sq_sqrt hN, Real.sq_sqrt hq]
  have h3 : 1.0012 * N ≤ 0.09 * X := by
    have hsq : (1.0012 * N) ^ 2 ≤ (0.09 * X) ^ 2 := by
      rw [mul_pow (0.09 : ℝ), hX2]
      nlinarith [mul_le_mul_of_nonneg_left hqP hN]
    exact (pow_le_pow_iff_left₀ (by positivity) (by positivity) two_ne_zero).mp hsq
  have h1 : 0 ≤ 0.28 * N / √q * L ^ 2 := by positivity
  have h2 : 0 ≤ 4 * (N : ℝ) ^ ((4 : ℝ) / 5) * L ^ (1.4 : ℝ) := by positivity
  unfold rhs62
  have e : 0.09 * √(N : ℝ) * √q * L ^ (2.5 : ℝ) = 0.09 * X := by rw [hX, hP]; ring
  linarith

/-- PROVED. For `log N ≤ 32.636` the trivial bound decides: `TrivialPsiAt` and `MinRhsAbove`
give Proposition 6.1 at `N`. -/
theorem prop61_of_trivial (N : ℕ) (hT : TrivialPsiAt N) (hM : MinRhsAbove N) : Prop61At N :=
  fun c hc0 hc1 α _ q hD => (hT c hc0 hc1 α).trans (hM q hD.1)

/-- PROVED, CONDITIONAL ON `TrivialPsiAt`, `SplitAt`, `Lemma62At`, the absorption of `1.02 U`,
`Lemma65At`, `Lemma66At`, `Lemma67Mid`: Proposition 6.1 at one `N` with `log N ≥ 1`. The case
split on `q` is the reduction of p. 168. -/
theorem prop61At_of_inputs (N : ℕ) (hL : 1 ≤ Real.log N) (hT : TrivialPsiAt N)
    (hS : SplitAt N) (h62 : Lemma62At N)
    (hS1 : 1.02 * Uf N ≤ 0.0999 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ))
    (h65 : Lemma65At N) (h66 : Lemma66At N) (h67 : Lemma67Mid N) : Prop61At N := by
  intro c hc0 hc1 α a q hD
  have hq1 : 1 ≤ q := hD.1
  rcases le_or_gt (q : ℝ) ((0.28 / 1.0012) ^ 2 * Real.log N ^ 4) with hs | hs
  · exact (hT c hc0 hc1 α).trans (rhs_small_q N q hq1 hs)
  rcases le_or_gt ((1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) (q : ℝ) with hb | hb
  · exact (hT c hc0 hc1 α).trans (rhs_large_q N q hL hb)
  have hR : InRange63 N q := ⟨hs, hb⟩
  rw [hS c α]
  have t : ‖Ssum (lam1 (Uf N)) c N α + Ssum (lam2 (Vf N)) c N α +
      Ssum (lam3 (Uf N) (Vf N)) c N α + Ssum (lam4 (Uf N) (Vf N)) c N α‖ ≤
      ‖Ssum (lam1 (Uf N)) c N α‖ + ‖Ssum (lam2 (Vf N)) c N α‖ +
      ‖Ssum (lam3 (Uf N) (Vf N)) c N α‖ + ‖Ssum (lam4 (Uf N) (Vf N)) c N α‖ := norm_add₄_le
  have g1 := h62 c α
  have g2 := h65 c hc0 hc1 α a q hD hR
  have g3 := h66 c hc0 hc1 α a q hD hR
  have g4 := h67 c hc0 hc1 α a q hD hR
  set A := (N : ℝ) / √q * Real.log N ^ 2 with hA
  set B := (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) with hB
  set C := √(N : ℝ) * √q * Real.log N ^ (2.5 : ℝ) with hC
  have e1 : ∀ x : ℝ, x * N / √q * Real.log N ^ 2 = x * A := fun x => by rw [hA]; ring
  have e2 : ∀ x : ℝ, x * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) = x * B :=
    fun x => by rw [hB]; ring
  have e3 : ∀ x : ℝ, x * √(N : ℝ) * √q * Real.log N ^ (2.5 : ℝ) = x * C :=
    fun x => by rw [hC]; ring
  unfold rhs62
  rw [e1, e2, e3] at g2 g3 g4 ⊢
  rw [e2] at hS1
  linarith

/-- PROVED, CONDITIONAL ON the inputs of `prop61At_of_inputs` for every `N` of the range: the
answer to `Q1557`. The inputs `Lemma67Mid` come from `Lemma67KeptAt` and `KeptNumAt` by
`lemma67Mid_of_kept`. -/
theorem q1557_of_inputs
    (h : ∀ N : ℕ, 30.95 ≤ Real.log N → Real.log N < 40.06 →
      TrivialPsiAt N ∧ SplitAt N ∧ Lemma62At N ∧
      1.02 * Uf N ≤ 0.0999 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) ∧
      Lemma65At N ∧ Lemma66At N ∧ Lemma67KeptAt N ∧ KeptNumAt N) : Q1557 := by
  intro N hL1 hL2
  obtain ⟨hT, hS, h62, hS1, h65, h66, hK, hn⟩ := h N hL1 hL2
  exact prop61At_of_inputs N (by linarith) hT hS h62 hS1 h65 h66 (lemma67Mid_of_kept N hK hn)

/-! ### Vacuity instances -/

/-- Vacuity, PROVED: the range of `Q1557` and the range (6.3) are inhabited together, with
`N = 2^50`, `log N = 50 log 2 ≈ 34.657`, `q = 10^6`, `α = 1/q`, `a = 1`. -/
theorem mid_hyps_hold : ∃ N q : ℕ, 30.95 ≤ Real.log N ∧ Real.log N < 40.06 ∧
    InRange63 N q ∧ Dioph (1 / q) 1 q := by
  have hlog : Real.log ((2 ^ 50 : ℕ) : ℝ) = 50 * Real.log 2 := by
    rw [Nat.cast_pow, Real.log_pow]; norm_num
  have l1 := Real.log_two_gt_d9
  have l2 := Real.log_two_lt_d9
  have hLlo : (34.6573 : ℝ) ≤ 50 * Real.log 2 := by linarith
  have hLhi : 50 * Real.log 2 ≤ 34.6574 := by linarith
  refine ⟨2 ^ 50, 10 ^ 6, ?_, ?_, ⟨?_, ?_⟩, ?_⟩
  · rw [hlog]; linarith
  · rw [hlog]; linarith
  · rw [hlog]
    have : (50 * Real.log 2) ^ 4 ≤ (34.6574 : ℝ) ^ 4 :=
      pow_le_pow_left₀ (by linarith) hLhi 4
    push_cast
    nlinarith
  · rw [hlog]
    have h5 : (50 * Real.log 2) ^ 5 ≤ (34.6574 : ℝ) ^ 5 :=
      pow_le_pow_left₀ (by linarith) hLhi 5
    have h5p : 0 < (50 * Real.log 2) ^ 5 := by positivity
    rw [lt_div_iff₀ h5p]
    push_cast
    nlinarith
  · refine ⟨by norm_num, by simp, ?_⟩
    push_cast
    rw [sub_self, abs_zero]
    positivity

/-- Vacuity, PROVED: `MinRhsAbove` and `TrivialPsiAt` are not contradictory in form; at
`N = 0` both sides vanish. The meaningful instance is the Python check for
`30.95 ≤ log N ≤ 32.636`. -/
theorem minRhs_zero : MinRhsAbove 0 := by
  intro q _
  unfold rhs62
  simp

end LeanLab.LiuWang2002.U1557
