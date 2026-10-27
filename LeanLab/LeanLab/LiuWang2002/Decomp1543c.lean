/-
Unit U-1543, run 20261026T0808Z-17522, track T1. Decomposition of Lemmas 6.2, 6.5, 6.6 of
Liu-Wang 2002, Acta Arith. 105, pp. 169-170, the sums `S1`, `S2`, `S3` of the Vaughan split,
and the assembly `prop61_large`: Proposition 6.1 p. 168 for `log N ≥ 3100` and `q` in the
range (6.3), with the printed constants `0.28`, `4`, `0.09`, proved CONDITIONAL ON the leaves
of Decomp1543a, Decomp1543b and this file. The reduction to (6.3) on p. 168 and the case
`log N < 3100` are not formalized here.
Source: papers/P0023.pdf, pages 168-170 rendered with pdftoppm.
AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.LiuWang2002.Decomp1543b
import LeanLab.LiuWang2002.Constants

namespace LeanLab.LiuWang2002.U1543

open Real Finset ArithmeticFunction

/-! ### Input from another paper -/

/-- Lemma 6.4 p. 169, the statement of Wang-Chen 1994, Lemma 3: for `X ≥ 1`, `q ≥ 15`,
`∑_{n≤X} min(Y/n, 1/(2‖αn‖)) ≤ 5q + 1.5 q log q + X log q + 5Y q^(-1) log X`. -/
def WCLemma3 : Prop :=
  ∀ (α : ℝ) (a : ℤ) (q : ℕ), Dioph α a q → 15 ≤ q → ∀ X Y : ℝ, 1 ≤ X → 0 < Y →
    ∑ n ∈ Icc 1 ⌊X⌋₊, minK (Y / n) (α * n) ≤
      5 * q + 1.5 * q * Real.log q + X * Real.log q + 5 * Y / q * Real.log X

/-- CITED, not proved in the lab: Lemma 6.4 p. 169 is [WC, Lemma 3], Wang-Chen, Acta Math.
Sinica 37 (1994), read with `‖x‖` the distance to the nearest integer. -/
theorem wc_lemma3 : WCLemma3 := by sorry

/-! ### Leaves -/

/-- LEAF. Unit U-1543. Proof of Lemma 6.5 p. 170, first line, by partial summation:
`|S2(α)| ≤ log N ∑_{t≤V} min(N/t, 1/(2‖αt‖))`, for `c ≥ 0`. -/
theorem S2_le (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (V α : ℝ) :
    ‖Ssum (lam2 V) c N α‖ ≤
      Real.log N * ∑ t ∈ Icc 1 ⌊V⌋₊, minK ((N : ℝ) / t) (α * t) := by sorry

/-- LEAF. Unit U-1543. Proof of Lemma 6.6 p. 170, first line: with `k = rt ≤ UV` and
`|∑_{rt=k} Λ(r) μ(t)| ≤ ∑_{r|k} Λ(r) = log k ≤ log(UV)`,
`|S3(α)| ≤ log(UV) ∑_{k≤UV} min(N/k, 1/(2‖αk‖))`, for `c ≥ 0`, `U, V ≥ 1`. -/
theorem S3_le (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (U V α : ℝ) (hU : 1 ≤ U) (hV : 1 ≤ V) :
    ‖Ssum (lam3 U V) c N α‖ ≤
      Real.log (U * V) * ∑ k ∈ Icc 1 ⌊U * V⌋₊, minK ((N : ℝ) / k) (α * k) := by

  unfold Ssum
  sorry



/-- LEAF. Unit U-1543. Lemma 6.2 p. 169, for `log N ≥ 3100`:
`|S1(α)| ≤ ∑_{n≤U} Λ(n) ≤ 1.02 U`, using a Chebyshev bound at `U ≥ exp(9.634)`. -/
theorem lemma62_S1 (c : ℝ) (N : ℕ) (hL : 3100 ≤ Real.log N) (α : ℝ) :
    ‖Ssum (lam1 (Uf N)) c N α‖ ≤ 1.02 * Uf N := by
  unfold Ssum
  sorry


/-- LEAF. Unit U-1543. The `S1` term is absorbed in the middle term of (6.2) p. 168:
`1.02 U ≤ 0.38 N^(4/5) log^1.4 N` for `log N ≥ 3100`. -/
theorem S1_absorb (N : ℕ) (hL : 3100 ≤ Real.log N) :
    1.02 * Uf N ≤ 0.38 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by



  sorry





/-- LEAF. Unit U-1543. Proof of Lemma 6.5 p. 170: under (6.3),
`(5q + 1.5 q log q) log N ≤ 0.0006 N^(1/2) q^(1/2) log^2.5 N`, for `log N ≥ 3100`. -/
theorem n65a (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    (5 * q + 1.5 * q * Real.log q) * Real.log N ≤
      0.0006 * √N * √q * Real.log N ^ (2.5 : ℝ) := by sorry

/-- LEAF. Unit U-1543. Proof of Lemma 6.5 p. 170: `V log q · log N ≤ 0.0001 N^(4/5) log^1.4 N`;
the paper writes `N^(2/5) (log N)^(1/5) log q ≤ 0.0001 N^(4/5) log^0.4 N`. -/
theorem n65b (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    Vf N * Real.log q * Real.log N ≤ 0.0001 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by
  sorry

/-- LEAF. Unit U-1543. Proof of Lemma 6.5 p. 170: `5 N q^(-1) log V · log N ≤ 0.0282 N q^(-1/2)
log^2 N`. -/
theorem n65c (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    5 * N / q * Real.log (Vf N) * Real.log N ≤ 0.0282 * N / √q * Real.log N ^ 2 := by sorry

/-- LEAF. Unit U-1543. Proof of Lemma 6.6 p. 170: `(5q + 1.5 q log q) log(UV) ≤
0.0005 N^(1/2) q^(1/2) log^2.5 N`. -/
theorem n66a (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    (5 * q + 1.5 * q * Real.log q) * Real.log (Uf N * Vf N) ≤
      0.0005 * √N * √q * Real.log N ^ (2.5 : ℝ) := by sorry

/-- LEAF. Unit U-1543. Proof of Lemma 6.6 p. 170: `UV (log q) log(UV) ≤ 0.8 N^(4/5) log^1.4 N`. -/
theorem n66b (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    Uf N * Vf N * Real.log q * Real.log (Uf N * Vf N) ≤
      0.8 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by sorry

/-- LEAF. Unit U-1543. Proof of Lemma 6.6 p. 170: `5 N q^(-1) log^2(UV) ≤ 0.0131 N q^(-1/2)
log^2 N`. -/
theorem n66c (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    5 * N / q * Real.log (Uf N * Vf N) * Real.log (Uf N * Vf N) ≤
      0.0131 * N / √q * Real.log N ^ 2 := by sorry

/-! ### Assemblies -/

/-- The range (6.3) with `log N ≥ 3100` gives `15 ≤ q ≤ N`. PROVED. -/
theorem q_range (N : ℕ) (hL : 3100 ≤ Real.log N) (q : ℕ)
    (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) : 15 ≤ q ∧ q ≤ N := by
  have h4 : (3100 : ℝ) ^ 4 ≤ Real.log N ^ 4 := pow_le_pow_left₀ (by norm_num) hL 4
  have h5 : (3100 : ℝ) ^ 5 ≤ Real.log N ^ 5 := pow_le_pow_left₀ (by norm_num) hL 5
  have hL5 : (0 : ℝ) < Real.log N ^ 5 := by positivity
  constructor
  · have : (15 : ℝ) < q := by nlinarith
    exact_mod_cast this.le
  · have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    have : (1.0012 / 0.09) ^ 2 * (N : ℝ) / Real.log N ^ 5 ≤ N := by
      rw [div_le_iff₀ hL5]; nlinarith
    exact_mod_cast (hq2.trans_le this).le

/-- Lemma 6.5 p. 169 for `log N ≥ 3100` and `q` in (6.3): `|S2(α)| ≤ 0.0282 N q^(-1/2) log^2 N
+ 0.0001 N^(4/5) log^1.4 N + 0.0006 N^(1/2) q^(1/2) log^2.5 N`. PROVED, CONDITIONAL ON `S2_le`,
`wc_lemma3`, `n65a`, `n65b`, `n65c`, `params_facts`. -/
theorem lemma65 (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (hL : 3100 ≤ Real.log N) (α : ℝ) (a : ℤ) (q : ℕ)
    (hD : Dioph α a q) (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    ‖Ssum (lam2 (Vf N)) c N α‖ ≤ 0.0282 * N / √q * Real.log N ^ 2 +
      0.0001 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) +
        0.0006 * √N * √q * Real.log N ^ (2.5 : ℝ) := by
  obtain ⟨-, hV13, -, -, -, hN0⟩ := params_facts N hL
  have hV1 : (1 : ℝ) ≤ Vf N := le_trans (Real.one_le_exp (by norm_num)) hV13
  have hq15 := (q_range N hL q hq1 hq2).1
  have hw := wc_lemma3 α a q hD hq15 (Vf N) N hV1 hN0
  have hL0 : 0 ≤ Real.log N := by linarith
  have h1 := (S2_le c hc N (Vf N) α).trans (mul_le_mul_of_nonneg_left hw hL0)
  have e : Real.log N * (5 * q + 1.5 * q * Real.log q + Vf N * Real.log q +
      5 * N / q * Real.log (Vf N)) = (5 * q + 1.5 * q * Real.log q) * Real.log N +
      Vf N * Real.log q * Real.log N + 5 * N / q * Real.log (Vf N) * Real.log N := by ring
  rw [e] at h1
  linarith [n65a N hL q hq1 hq2, n65b N hL q hq1 hq2, n65c N hL q hq1 hq2]

/-- Lemma 6.6 p. 170 for `log N ≥ 3100` and `q` in (6.3): `|S3(α)| ≤ 0.0131 N q^(-1/2) log^2 N
+ 0.8 N^(4/5) log^1.4 N + 0.0005 N^(1/2) q^(1/2) log^2.5 N`. PROVED, CONDITIONAL ON `S3_le`,
`wc_lemma3`, `n66a`, `n66b`, `n66c`, `params_facts`. -/
theorem lemma66 (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (hL : 3100 ≤ Real.log N) (α : ℝ) (a : ℤ) (q : ℕ)
    (hD : Dioph α a q) (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    ‖Ssum (lam3 (Uf N) (Vf N)) c N α‖ ≤ 0.0131 * N / √q * Real.log N ^ 2 +
      0.8 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) +
        0.0005 * √N * √q * Real.log N ^ (2.5 : ℝ) := by
  obtain ⟨hU15, hV13, -, -, -, hN0⟩ := params_facts N hL
  have hV1 : (1 : ℝ) ≤ Vf N := le_trans (Real.one_le_exp (by norm_num)) hV13
  have hU1 : (1 : ℝ) ≤ Uf N := by linarith
  have hUV1 : (1 : ℝ) ≤ Uf N * Vf N := by nlinarith
  have hq15 := (q_range N hL q hq1 hq2).1
  have hw := wc_lemma3 α a q hD hq15 (Uf N * Vf N) N hUV1 hN0
  have hl0 : 0 ≤ Real.log (Uf N * Vf N) := Real.log_nonneg hUV1
  have h1 := (S3_le c hc N (Uf N) (Vf N) α hU1 hV1).trans (mul_le_mul_of_nonneg_left hw hl0)
  have e : Real.log (Uf N * Vf N) * (5 * q + 1.5 * q * Real.log q +
      Uf N * Vf N * Real.log q + 5 * N / q * Real.log (Uf N * Vf N)) =
      (5 * q + 1.5 * q * Real.log q) * Real.log (Uf N * Vf N) +
      Uf N * Vf N * Real.log q * Real.log (Uf N * Vf N) +
      5 * N / q * Real.log (Uf N * Vf N) * Real.log (Uf N * Vf N) := by ring
  rw [e] at h1
  linarith [n66a N hL q hq1 hq2, n66b N hL q hq1 hq2, n66c N hL q hq1 hq2]

/-- Proposition 6.1 p. 168, (6.2), for `log N ≥ 3100`, `c ≥ 0` and `q` in the range (6.3):
`|S(α)| ≤ 0.28 N q^(-1/2) log^2 N + 4 N^(4/5) log^1.4 N + 0.09 N^(1/2) q^(1/2) log^2.5 N`,
with `S` summed over `cN < n ≤ N`. The coefficients add up as `0.0282 + 0.0131 + 0.2264 ≤ 0.28`,
`0.38 + 0.0001 + 0.8 + 2.81 ≤ 4`, `0.0006 + 0.0005 + 0.0785 ≤ 0.09`. PROVED, CONDITIONAL ON
`S_split`, `lemma62_S1`, `S1_absorb`, `lemma65`, `lemma66`, `lemma67` and all their leaves. -/
theorem prop61_large (c : ℝ) (hc : 0 ≤ c) (N : ℕ) (hL : 3100 ≤ Real.log N) (α : ℝ) (a : ℤ)
    (q : ℕ) (hD : Dioph α a q) (hq1 : (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q)
    (hq2 : (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5) :
    ‖Ssum (fun n => (vonMangoldt n : ℝ)) c N α‖ ≤ 0.28 * N / √q * Real.log N ^ 2 +
      4 * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) +
        0.09 * √N * √q * Real.log N ^ (2.5 : ℝ) := by
  obtain ⟨-, hV13, -, -, -, -⟩ := params_facts N hL
  have hV1 : (1 : ℝ) ≤ Vf N := le_trans (Real.one_le_exp (by norm_num)) hV13
  obtain ⟨hq15, hqN⟩ := q_range N hL q hq1 hq2
  rw [S_split c N (Uf N) (Vf N) α hV1]
  have h1 := (lemma62_S1 c N hL α).trans (S1_absorb N hL)
  have h2 := lemma65 c hc N hL α a q hD hq1 hq2
  have h3 := lemma66 c hc N hL α a q hD hq1 hq2
  have h4 := lemma67 c N hL α a q hD (by omega) hqN
  have p1 : 0 ≤ (N : ℝ) / √q * Real.log N ^ 2 := by positivity
  have p2 : 0 ≤ (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) := by positivity
  have p3 : 0 ≤ √(N : ℝ) * √q * Real.log N ^ (2.5 : ℝ) := by positivity
  have t : ‖Ssum (lam1 (Uf N)) c N α + Ssum (lam2 (Vf N)) c N α +
      Ssum (lam3 (Uf N) (Vf N)) c N α + Ssum (lam4 (Uf N) (Vf N)) c N α‖ ≤
      ‖Ssum (lam1 (Uf N)) c N α‖ + ‖Ssum (lam2 (Vf N)) c N α‖ +
      ‖Ssum (lam3 (Uf N) (Vf N)) c N α‖ + ‖Ssum (lam4 (Uf N) (Vf N)) c N α‖ := norm_add₄_le
  set A := (N : ℝ) / √q * Real.log N ^ 2 with hA
  set B := (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) with hB
  set C := √(N : ℝ) * √q * Real.log N ^ (2.5 : ℝ) with hC
  have e1 : ∀ x : ℝ, x * N / √q * Real.log N ^ 2 = x * A := fun x => by rw [hA]; ring
  have e2 : ∀ x : ℝ, x * (N : ℝ) ^ ((4 : ℝ) / 5) * Real.log N ^ (1.4 : ℝ) = x * B :=
    fun x => by rw [hB]; ring
  have e3 : ∀ x : ℝ, x * √(N : ℝ) * √q * Real.log N ^ (2.5 : ℝ) = x * C :=
    fun x => by rw [hC]; ring
  rw [e1, e2, e3] at h2 h3 h4 ⊢
  rw [e2] at h1
  linarith

/-! ### Vacuity instances -/

/-- Vacuity: the hypotheses of `WCLemma3` can hold: `α = 1/15`, `a = 1`, `q = 15`. PROVED. -/
theorem wcLemma3_hyps_hold : Dioph (1 / 15) 1 15 ∧ 15 ≤ 15 := by
  refine ⟨⟨by norm_num, by decide, ?_⟩, le_rfl⟩
  norm_num

/-- Vacuity: the hypotheses of `prop61_large`, `lemma65`, `lemma66` and the numerical leaves of
this file hold together, with `N = ⌈e^3100⌉`, `q = ⌈log^6 N⌉`, `α = 1/q`, `a = 1`. PROVED,
using `Constants.aux_half`. -/
theorem prop61_hyps_hold : ∃ N q : ℕ, 3100 ≤ Real.log N ∧
    (0.28 / 1.0012) ^ 2 * Real.log N ^ 4 < q ∧
    (q : ℝ) < (1.0012 / 0.09) ^ 2 * N / Real.log N ^ 5 ∧ Dioph (1 / q) 1 q := by
  have hL := logN_hyp_holds
  set N : ℕ := ⌈exp 3100⌉₊ with hNdef
  set L := Real.log N with hLdef
  have hN : (0 : ℝ) < N := lt_of_lt_of_le (Real.exp_pos 3100) (Nat.le_ceil _)
  have hNe : (N : ℝ) = exp L := (Real.exp_log hN).symm
  have hL1 : (1 : ℝ) ≤ L := by linarith
  have hL6 : 0 < L ^ 6 := by positivity
  have hq0 : 0 < ⌈L ^ 6⌉₊ := Nat.ceil_pos.mpr hL6
  refine ⟨N, ⌈L ^ 6⌉₊, hL, ?_, ?_, ?_⟩
  · have h2 : (3100 : ℝ) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ (by norm_num) hL 2
    have h4 : 0 < L ^ 4 := by positivity
    have : (0.28 / 1.0012) ^ 2 * L ^ 4 < L ^ 6 := by
      have : L ^ 6 = L ^ 4 * L ^ 2 := by ring
      rw [this]; nlinarith
    exact this.trans_le (Nat.le_ceil _)
  · have hc : (⌈L ^ 6⌉₊ : ℝ) < L ^ 6 + 1 := Nat.ceil_lt_add_one hL6.le
    have hh := LeanLab.LiuWang2002.Constants.aux_half L hL
    have hE : 81 * L ^ 14 ≤ exp L := by
      have : exp L = exp (L / 2) * exp (L / 2) := by rw [← Real.exp_add]; ring_nf
      rw [this]
      have h7 : 0 ≤ 9 * L ^ 7 := by positivity
      nlinarith [mul_le_mul hh hh h7 (Real.exp_pos _).le]
    have hL5 : 0 < L ^ 5 := by positivity
    have h611 : L ^ 11 ≤ L ^ 14 := pow_le_pow_right₀ hL1 (by norm_num)
    have h06 : 1 ≤ L ^ 6 := one_le_pow₀ hL1
    rw [lt_div_iff₀ hL5, hNe]
    have : (L ^ 6 + 1) * L ^ 5 ≤ 2 * L ^ 11 := by
      have : L ^ 11 = L ^ 6 * L ^ 5 := by ring
      nlinarith
    nlinarith
  · refine ⟨hq0, by simp, ?_⟩
    push_cast
    rw [sub_self, abs_zero]
    positivity

end LeanLab.LiuWang2002.U1543
