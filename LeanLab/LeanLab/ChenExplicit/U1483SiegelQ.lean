/-
AI-written Lean code, Claude, Lean Lab run 20261022T1302Z-31860, unit U-1483, track T2 FRONTIER,
paper P0009 Bordignon, Johnston, Starichkova 2022, idea I-0105 of sweep U-1480.

A q-dependent exceptional zero bound for even primitive real characters, composed from
Bordignon, arXiv 1907.08327 v1, Section 1 Theorems 1.1 and 1.3, Section 2 eq (4), Section 2.1
eq (5), with the elementary unit bound in place of the computed 12.52 of eq (7).

Source check, read this unit through arxiv.org/abs and arxiv.org/pdf, the ar5iv html as well:
* Theorem 1.1 assumes chi even primitive real, sigma in (beta0, 1), beta0 >= 1 - 100/(sqrt q log^2 q),
  q > 4e5, and gives |L'(sigma, chi)| <= log^2 q / 8.  The beta0 hypothesis matters: it is how the
  factor q^{(1-beta0)/2} of eq (9) is controlled.  Below it is used only on the contrary assumption
  beta0 > 1 - c/(sqrt q log^2 q) with c >= 100, and that does NOT meet it: c > 100 makes the
  contrary assumption weaker than beta0 >= 1 - 100/(sqrt q log^2 q).  So the printed Theorem 1.1
  cannot give the new bound.  What is needed is the c-form, Section 2.2 with c in [100, 1000]
  "to be chosen later" and eq (9); the paper states the L' bound only at c = 100 and uses larger
  c, up to 660, only in the table for q <= 1e7.  That c-form is the cited Prop `Thm11C` below,
  an inference from the proof, NOT a printed statement; it is the open check of this unit.
* eq (5) is L(1, chi) = h log eta_d / sqrt d with eta_d = (v0 + u0 sqrt d)/2 and v0^2 - d u0^2 = 4
  as printed.  When the fundamental unit has norm -1 the correct regulator is that of the norm -1
  unit, which satisfies v^2 - d u^2 = -4; the cited Prop `ClassNumberH1` below therefore allows
  either sign, and the proof uses only eta >= sqrt d / 2, so it is right in both cases.
  Consequence: the constant is 4 log (q/4), not the sweep's 4 log q.
* eq (7) is h log eta_d >= log u0 sqrt d >= (1/2) log (7.5e10) >= 12.52, used for d u0^2 >= 7.5e10.

The cited inputs are named Props over Mathlib's `DirichletCharacter.LFunction`; nothing about
L-functions is proved here.  Everything else is proved.  Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Routes.U1480SiegelUnit

namespace LeanLab.ChenExplicit.U1483

open Real DirichletCharacter

/-- even, primitive, real, non-principal, the class of Bordignon's Theorems 1.1 and 1.2. -/
def EvenRealPrim {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) : Prop :=
  χ.Even ∧ χ.IsPrimitive ∧ χ ≠ 1 ∧ χ ^ 2 = 1

/-- a real zero `β ∈ (0,1)` of `L(s, χ)`. -/
def RealZero {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (β : ℝ) : Prop :=
  0 < β ∧ β < 1 ∧ LFunction χ (β : ℂ) = 0

/-- CITED, Bordignon Section 2.1 eq (5) with `h ≥ 1`, Dirichlet's class number formula for the real
quadratic field of discriminant `d = q`, the unit `(v + u √q)/2` of either norm. -/
def ClassNumberH1 : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), EvenRealPrim χ → (4e5 : ℝ) < q →
    ∃ (h : ℕ) (u v : ℝ), 1 ≤ h ∧ 1 ≤ u ∧ 0 < v ∧
      (v ^ 2 - q * u ^ 2 = 4 ∨ v ^ 2 - q * u ^ 2 = -4) ∧
      ‖LFunction χ 1‖ = h * Real.log ((v + u * Real.sqrt q) / 2) / Real.sqrt q

/-- CITED, Bordignon Section 2 eq (4), the mean value step after [2, Section 3]:
`1 - β₀ = L(1, χ)/|L'(σ, χ)|` for some `σ ∈ (β₀, 1)`, written without division. -/
def MeanValueStep : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), EvenRealPrim χ → ∀ β : ℝ, RealZero χ β →
    ∃ σ : ℝ, β < σ ∧ σ < 1 ∧
      ‖LFunction χ 1‖ = (1 - β) * ‖deriv (LFunction χ) (σ : ℂ)‖

/-- CITED, Bordignon Theorem 1.1, eq (1). -/
def BordignonThm11 : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), EvenRealPrim χ → (4e5 : ℝ) < q →
    ∀ β σ : ℝ, RealZero χ β →
      1 - 100 / (Real.sqrt q * Real.log q ^ 2) ≤ β → β < σ → σ < 1 →
      ‖deriv (LFunction χ) (σ : ℂ)‖ ≤ Real.log q ^ 2 / 8

/-- CITED BUT NOT PRINTED, the c-form of Theorem 1.1 read off Section 2.2: for every
`c ∈ [100, 1000]`, the same L' bound under `β ≥ 1 - c/(√q log² q)`.  Bordignon's Section 2.2
introduces `c ∈ [100, 1000]` but proves the bound only at `c = 100`, via eq (9). -/
def Thm11C : Prop :=
  ∀ (c : ℝ), 100 ≤ c → c ≤ 1000 →
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), EvenRealPrim χ → (4e5 : ℝ) < q →
    ∀ β σ : ℝ, RealZero χ β →
      1 - c / (Real.sqrt q * Real.log q ^ 2) ≤ β → β < σ → σ < 1 →
      ‖deriv (LFunction χ) (σ : ℂ)‖ ≤ Real.log q ^ 2 / 8

/-- the c-form contains the printed Theorem 1.1, at `c = 100`. -/
theorem thm11_of_thm11C (h : Thm11C) : BordignonThm11 :=
  fun q _ χ hχ hq β σ hβ h1 h2 h3 => h 100 le_rfl (by norm_num) q χ hχ hq β σ hβ h1 h2 h3

/-- CITED, Bordignon Theorem 1.3, eq (3), here only for primitive characters. -/
def BordignonThm13 : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q), EvenRealPrim χ → (4e5 : ℝ) < q →
    ∀ β : ℝ, RealZero χ β → β ≤ 1 - 100 / (Real.sqrt q * Real.log q ^ 2)

/-- the new constant `max(100, 4 log (q/4))`. -/
noncomputable def cQ (q : ℝ) : ℝ := max 100 (4 * Real.log (q / 4))

/-- the new Siegel gap `cQ q / (√q log² q)`. -/
noncomputable def gapQ (q : ℝ) : ℝ := cQ q / (Real.sqrt q * Real.log q ^ 2)

/-- the unit `(v + u √d)/2`, `u ≥ 1`, `v > 0`, of either norm, has `log ≥ log (d/4) / 2`. -/
theorem log_unit_ge_any {d u v : ℝ} (hd : 0 < d) (hu : 1 ≤ u) (hv : 0 < v) :
    Real.log (d / 4) / 2 ≤ Real.log ((v + u * Real.sqrt d) / 2) := by
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have h3 : Real.sqrt d / 2 ≤ (v + u * Real.sqrt d) / 2 := by nlinarith
  have e : Real.log (d / 4) / 2 = Real.log (Real.sqrt d / 2) := by
    rw [show d / 4 = (Real.sqrt d / 2) ^ 2 by rw [div_pow, Real.sq_sqrt hd.le]; norm_num,
      Real.log_pow]; push_cast; ring
  rw [e]; exact Real.log_le_log (by positivity) h3

/-- the gap core: `L₁ ≥ A/(2√q)`, `|L'| ≤ log² q/8`, `L₁ = δ |L'|`, `A > 0` give
`δ ≥ 4A/(√q log² q)`. -/
theorem gap_core {q L1 M δ A : ℝ} (hq : 1 < q) (hA : 0 < A) (hM0 : 0 ≤ M)
    (hMle : M ≤ Real.log q ^ 2 / 8) (hL1 : A / (2 * Real.sqrt q) ≤ L1) (hmv : L1 = δ * M) :
    4 * A / (Real.sqrt q * Real.log q ^ 2) ≤ δ := by
  have hl : 0 < Real.log q := Real.log_pos hq
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 (by linarith)
  have hL1pos : 0 < L1 := lt_of_lt_of_le (by positivity) hL1
  have hMpos : 0 < M := by
    rcases hM0.lt_or_eq with h | h
    · exact h
    · rw [← h, mul_zero] at hmv; linarith
  have hδ : 0 < δ := by
    by_contra hc; push_neg at hc; nlinarith
  have hA' : A / (2 * Real.sqrt q) ≤ δ * (Real.log q ^ 2 / 8) := by
    calc A / (2 * Real.sqrt q) ≤ L1 := hL1
      _ = δ * M := hmv
      _ ≤ δ * (Real.log q ^ 2 / 8) := by gcongr
  rw [div_le_iff₀ (by positivity)] at hA'
  rw [div_le_iff₀ (by positivity)]
  nlinarith

/-- **The composed bound.** For every even primitive real `χ` mod `q > 4·10⁵` and every real zero
`β ∈ (0,1)` of `L(s, χ)`, with `log(q/4) ≤ 250`: `β ≤ 1 - max(100, 4 log(q/4))/(√q log² q)`. -/
theorem siegel_even_q_dep (hC : ClassNumberH1) (hM : MeanValueStep) (h11 : Thm11C)
    (h13 : BordignonThm13) (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (hχ : EvenRealPrim χ)
    (hq : (4e5 : ℝ) < q) (hqU : Real.log ((q : ℝ) / 4) ≤ 250) (β : ℝ) (hβ : RealZero χ β) :
    β ≤ 1 - gapQ q := by
  have hq1 : (1 : ℝ) < q := by linarith
  have hl : 0 < Real.log q := Real.log_pos hq1
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 (by linarith)
  have hD : 0 < Real.sqrt q * Real.log q ^ 2 := by positivity
  unfold gapQ cQ
  rcases le_total (4 * Real.log ((q : ℝ) / 4)) 100 with hc | hc
  · rw [max_eq_left hc]; exact h13 q χ hχ hq β hβ
  · rw [max_eq_right hc]
    by_contra hcon
    push_neg at hcon
    obtain ⟨σ, hσ1, hσ2, hmv⟩ := hM q χ hχ β hβ
    have hMle := h11 (4 * Real.log ((q : ℝ) / 4)) hc (by linarith) q χ hχ hq β σ hβ hcon.le
      hσ1 hσ2
    obtain ⟨h, u, v, hh, hu, hv, _, hL⟩ := hC q χ hχ hq
    have hA : 0 < Real.log ((q : ℝ) / 4) := by linarith
    have hunit := log_unit_ge_any (d := (q : ℝ)) (by linarith) hu hv
    have hL1 : Real.log ((q : ℝ) / 4) / (2 * Real.sqrt q) ≤ ‖LFunction χ 1‖ := by
      rw [hL]
      have hh' : (1 : ℝ) ≤ h := by exact_mod_cast hh
      have hlu : 0 ≤ Real.log ((v + u * Real.sqrt q) / 2) := by linarith
      rw [div_le_div_iff₀ (by positivity) hs]
      have : Real.log ((q : ℝ) / 4) ≤ 2 * (h * Real.log ((v + u * Real.sqrt q) / 2)) := by
        nlinarith
      nlinarith
    have hg := gap_core hq1 hA (norm_nonneg _) hMle hL1 hmv
    linarith

/-- the norm `+1` refinement through U-1480: when the class number formula comes with
`v² - q u² = 4`, the U-1480 lemmas give the constant `4 log q`. -/
theorem gap_plus_of_unit {q L1 M δ u v : ℝ} (hq : 1 < q) (hu : 1 ≤ u) (hv : 0 < v)
    (hpell : v ^ 2 - q * u ^ 2 = 4) (hM : 0 < M) (hMle : M ≤ Real.log q ^ 2 / 8)
    (hL : L1 = Real.log ((v + u * Real.sqrt q) / 2) / Real.sqrt q) (hmv : L1 ≤ δ * M) :
    4 / (Real.sqrt q * Real.log q) ≤ δ := by
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 (by linarith)
  have hu' := LeanLab.Routes.U1480.log_unit_ge (by linarith) hu hv hpell
  refine LeanLab.Routes.U1480.siegel_gap hq hM hMle ?_ hmv
  rw [hL, div_le_div_iff₀ (by positivity) hs]
  nlinarith

/-- `log 4 ≤ 1.3863`. -/
lemma log4_le : Real.log 4 ≤ 1.3863 := by
  rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
  have := Real.log_two_lt_d9; push_cast; nlinarith

/-- monotonicity: `(a - c)/a² ≥ (b - c)/b²` for `2c ≤ a ≤ b`. -/
lemma ratio_anti {a b c : ℝ} (hc : 0 ≤ c) (ha : 2 * c ≤ a) (hab : a ≤ b) (ha0 : 0 < a) :
    (b - c) / b ^ 2 ≤ (a - c) / a ^ 2 := by
  have hb0 : 0 < b := by linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h1 : 0 ≤ b - a := by linarith
  have h2 : 0 ≤ a * b - c * (a + b) := by nlinarith
  nlinarith [mul_nonneg h1 h2]

/-- **The BJS form.** If `100 ≤ 4 log(K/4)` then for `4·10⁵ < q ≤ K`,
`gapQ q ≥ 4 log(K/4)/(√K log² K)`; so every real zero for a modulus up to `K` is at most
`1 - 4 log(K/4)/(√K log² K)`. -/
theorem gapQ_ge_K {q K : ℝ} (hq : 4e5 < q) (hqK : q ≤ K) (hK : 100 ≤ 4 * Real.log (K / 4)) :
    4 * Real.log (K / 4) / (Real.sqrt K * Real.log K ^ 2) ≤ gapQ q := by
  have hq0 : 0 < q := by linarith
  have hK0 : 0 < K := by linarith
  have c4 := log4_le
  have c4' : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
  have hlq : 12 ≤ Real.log q := by
    have : Real.log 400000 ≤ Real.log q :=
      Real.log_le_log (by norm_num) (by norm_num at hq ⊢; linarith)
    have h2 : (12 : ℝ) ≤ Real.log 400000 := by
      rw [Real.le_log_iff_exp_le (by norm_num)]
      have := Real.exp_one_lt_d9
      have e : Real.exp 12 = Real.exp 1 ^ 12 := by rw [← Real.exp_nat_mul]; norm_num
      rw [e]
      have : Real.exp 1 ^ 12 ≤ (2.7182818286 : ℝ) ^ 12 :=
        pow_le_pow_left₀ (Real.exp_pos 1).le this.le 12
      have : (2.7182818286 : ℝ) ^ 12 ≤ 400000 := by norm_num
      linarith
    linarith
  have hlqK : Real.log q ≤ Real.log K := Real.log_le_log hq0 hqK
  have lq4 : Real.log (q / 4) = Real.log q - Real.log 4 := Real.log_div hq0.ne' (by norm_num)
  have lK4 : Real.log (K / 4) = Real.log K - Real.log 4 := Real.log_div hK0.ne' (by norm_num)
  have hsq : 1 / Real.sqrt K ≤ 1 / Real.sqrt q :=
    one_div_le_one_div_of_le (Real.sqrt_pos.2 hq0) (Real.sqrt_le_sqrt hqK)
  have hsK : 0 < Real.sqrt K := Real.sqrt_pos.2 hK0
  have hsq0 : 0 < Real.sqrt q := Real.sqrt_pos.2 hq0
  -- the log factor: 4 (b - c)/b² ≤ cQ q / a²
  rw [lK4] at hK
  set a := Real.log q
  set b := Real.log K
  set c := Real.log 4
  have hfac : 4 * (b - c) / b ^ 2 ≤ cQ q / a ^ 2 := by
    unfold cQ
    rw [lq4]
    rcases le_total (4 * (a - c)) 100 with h | h
    · -- a below the crossover t* = 25 + c ≤ b
      rw [max_eq_left h]
      have ht : 2 * c ≤ 25 + c := by linarith
      have h1 := ratio_anti c4' ht (show 25 + c ≤ b by linarith) (by linarith)
      have h2 : 100 / (25 + c) ^ 2 ≤ 100 / a ^ 2 := by
        apply div_le_div_of_nonneg_left (by norm_num) (by positivity)
        exact pow_le_pow_left₀ (by linarith) (by linarith) 2
      have e : 4 * ((25 + c - c) / (25 + c) ^ 2) = 100 / (25 + c) ^ 2 := by ring
      have e2 : 4 * (b - c) / b ^ 2 = 4 * ((b - c) / b ^ 2) := by ring
      rw [e2]; linarith
    · rw [max_eq_right h]
      have h1 := ratio_anti c4' (show 2 * c ≤ a by linarith) hlqK (by linarith)
      have e2 : 4 * (b - c) / b ^ 2 = 4 * ((b - c) / b ^ 2) := by ring
      have e3 : 4 * (a - c) / a ^ 2 = 4 * ((a - c) / a ^ 2) := by ring
      rw [e2, e3]; linarith
  have hfac0 : 0 ≤ 4 * (b - c) / b ^ 2 := by
    apply div_nonneg (by linarith) (by positivity)
  unfold gapQ
  rw [lK4]
  have e1 : 4 * (b - c) / (Real.sqrt K * b ^ 2) = (1 / Real.sqrt K) * (4 * (b - c) / b ^ 2) := by
    field_simp
  have e2 : cQ q / (Real.sqrt q * a ^ 2) = (1 / Real.sqrt q) * (cQ q / a ^ 2) := by
    field_simp
  rw [e1, e2]
  exact mul_le_mul hsq hfac hfac0 (by positivity)

/-- **BJS consequence**, CONDITIONAL ON the four cited Props: for `100 ≤ 4 log(K/4)`, every real
zero of every even primitive real `L(s, χ)` mod `q`, `4·10⁵ < q ≤ K`, is at most
`1 - 4 log(K/4)/(√K log² K)`. -/
theorem siegel_even_upto_K (hC : ClassNumberH1) (hM : MeanValueStep) (h11 : Thm11C)
    (h13 : BordignonThm13) {K : ℝ} (hK : 100 ≤ 4 * Real.log (K / 4))
    (hKU : Real.log (K / 4) ≤ 250) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : EvenRealPrim χ) (hq : (4e5 : ℝ) < q) (hqK : (q : ℝ) ≤ K)
    (β : ℝ) (hβ : RealZero χ β) :
    β ≤ 1 - 4 * Real.log (K / 4) / (Real.sqrt K * Real.log K ^ 2) := by
  have hq0 : (0 : ℝ) < q := by norm_num at hq ⊢; linarith
  have hqU : Real.log ((q : ℝ) / 4) ≤ 250 :=
    le_trans (Real.log_le_log (by positivity) (by linarith)) hKU
  have := siegel_even_q_dep hC hM h11 h13 q χ hχ hq hqU β hβ
  have := gapQ_ge_K hq hqK hK
  linarith

/-- the new constant is never worse than Bordignon's, and is strictly better once
`4 log(q/4) > 100`. -/
theorem gapQ_ge_old {q : ℝ} (hq : 1 < q) : 100 / (Real.sqrt q * Real.log q ^ 2) ≤ gapQ q := by
  have hl : 0 < Real.log q := Real.log_pos hq
  have hs : 0 < Real.sqrt q := Real.sqrt_pos.2 (by linarith)
  unfold gapQ cQ
  exact div_le_div_of_nonneg_right (le_max_left _ _) (by positivity)

/-- Vacuity, part 1: the side condition `100 ≤ 4 log(K/4)` holds at `K = e^{27}`, and it fails
at `K = e^{26}`, so the condition is a real restriction, the crossover being `log K = 25 + log 4`. -/
theorem side_condition_e27 : 100 ≤ 4 * Real.log (Real.exp 27 / 4) := by
  rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
  have := log4_le; linarith

theorem side_condition_fails_e26 : ¬ (100 ≤ 4 * Real.log (Real.exp 26 / 4)) := by
  rw [Real.log_div (Real.exp_pos _).ne' (by norm_num), Real.log_exp]
  have : (1.38 : ℝ) ≤ Real.log 4 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    have := Real.log_two_gt_d9; push_cast; nlinarith
  linarith

/-- Vacuity, part 2: the hypotheses of `gap_core` are jointly satisfiable with a strict gain,
`q = e^{40}`, `A = 38`, `M = log² q/8 = 200`, `L₁ = A/(2√q)`, `δ = L₁/M`. -/
example : 4 * 38 / (Real.sqrt (Real.exp 40) * Real.log (Real.exp 40) ^ 2) ≤
    (38 / (2 * Real.sqrt (Real.exp 40))) / 200 := by
  refine gap_core (M := 200) (L1 := 38 / (2 * Real.sqrt (Real.exp 40)))
    (by have := Real.add_one_le_exp (40 : ℝ); linarith) (by norm_num) (by norm_num)
    (by rw [Real.log_exp]; norm_num) le_rfl ?_
  field_simp

/-- Vacuity, part 3: the class `EvenRealPrim` is not forced empty by its definition alone:
the trivial character mod 1 is even and primitive and squares to 1; it is excluded only by
`χ ≠ 1`, which is the intended exclusion of the principal character. -/
example : (1 : DirichletCharacter ℂ 1).Even ∧ (1 : DirichletCharacter ℂ 1).IsPrimitive ∧
    (1 : DirichletCharacter ℂ 1) ^ 2 = 1 := by
  refine ⟨?_, ?_, by simp⟩
  · show (1 : DirichletCharacter ℂ 1) (-1) = 1
    rw [show (-1 : ZMod 1) = 1 from Subsingleton.elim _ _]; exact map_one _
  · exact DirichletCharacter.isPrimitive_one_level_one

end LeanLab.ChenExplicit.U1483

#print axioms LeanLab.ChenExplicit.U1483.log_unit_ge_any
#print axioms LeanLab.ChenExplicit.U1483.gap_core
#print axioms LeanLab.ChenExplicit.U1483.thm11_of_thm11C
#print axioms LeanLab.ChenExplicit.U1483.siegel_even_q_dep
#print axioms LeanLab.ChenExplicit.U1483.gap_plus_of_unit
#print axioms LeanLab.ChenExplicit.U1483.ratio_anti
#print axioms LeanLab.ChenExplicit.U1483.gapQ_ge_K
#print axioms LeanLab.ChenExplicit.U1483.siegel_even_upto_K
#print axioms LeanLab.ChenExplicit.U1483.gapQ_ge_old
#print axioms LeanLab.ChenExplicit.U1483.side_condition_e27
#print axioms LeanLab.ChenExplicit.U1483.side_condition_fails_e26
