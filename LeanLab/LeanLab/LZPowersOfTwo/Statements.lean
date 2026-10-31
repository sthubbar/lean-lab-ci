/-
P0079 A. Languasco and A. Zaccagnini, "On a Diophantine problem with two primes and s powers
of two", arXiv 0811.3663, read as v2 of 2 Apr 2009 with pdftotext on 2026-10-17.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Binary Goldbach is OPEN. Nothing here says anything about Goldbach for every even number:
the paper's Theorem needs `λ1 / λ2` irrational, so the integer case `λ = μ = 1` is outside it.

Encoding choices, all stated honestly:
* The paper writes the shift as `γ`; so do we.
* `μ` is an infinite sequence `ℕ → ℝ` of nonzero reals and the form with `s` powers of two
  uses `μ 0, ..., μ (s-1)`. Only `μ 0 = μ1` and `μ 1 = μ2` enter the rationality hypothesis and
  `s0`, exactly as in the paper. With a sequence, "η sufficiently small" may depend on all of
  `λ, μ`, which is the weakest reading of the paper's quantifier order.
* "η sufficiently small" is encoded as an existential threshold `η0 > 0`.
* "reduced representation `a_i / q_i`" of `λ_i / μ_i` is a rational `r_i` with numerator `a_i`
  and denominator `q_i > 0`; Mathlib's `Rat.num`, `Rat.den` are reduced.
* The Theorem's hypothesis reads `η < λ1 / a1`, without absolute value, while the Corollary
  reads `|λ1 / a1|`. We copy both literally.
* The quantitative form `N(X) ≫_{s,λ,ε} η X (log X)^{s-2}` of Section 2 is encoded with explicit
  existential constants `c > 0` and `X0`, for every sufficiently small `ε`.
* The decimal constants `C`, `0.83372131685`, `0.91237810306` are copied as exact decimals.
-/
import Mathlib
import LeanLab.Common.Goldbach

open Real Finset

noncomputable section
namespace LeanLab.LZPowersOfTwo

/-! ### Definitions -/

/-- The paper's (1) plus shift: `λ1 p1 + λ2 p2 + μ1 2^{m1} + ... + μs 2^{ms} + γ`. -/
def form {s : ℕ} (l1 l2 : ℝ) (μ : Fin s → ℝ) (γ : ℝ) (p1 p2 : ℕ) (m : Fin s → ℕ) : ℝ :=
  l1 * p1 + l2 * p2 + ∑ i, μ i * 2 ^ m i + γ

/-- Solutions of the inequality (6): primes `p1, p2`, positive integers `m_i`, and
`|form| < η`. -/
def Sol {s : ℕ} (l1 l2 : ℝ) (μ : Fin s → ℝ) (γ η : ℝ) : Set (ℕ × ℕ × (Fin s → ℕ)) :=
  {x | x.1.Prime ∧ x.2.1.Prime ∧ (∀ i, 1 ≤ x.2.2 i) ∧ |form l1 l2 μ γ x.1 x.2.1 x.2.2| < η}

/-- (5): `S'(n) = ∏_{p | n, p > 2} (p - 1)/(p - 2)`. -/
def Sprime (n : ℕ) : ℝ :=
  ∏ p ∈ n.primeFactors.filter (fun p => 2 < p), ((p : ℝ) - 1) / ((p : ℝ) - 2)

/-- The constant `C = 10.0219168340` of (4). -/
def bigC : ℝ := 10.0219168340

/-- (4): `C(q1, q2) = (log 2 + C S'(q1))^{1/2} (log 2 + C S'(q2))^{1/2}`. -/
def Cq (q1 q2 : ℕ) : ℝ := √(log 2 + bigC * Sprime q1) * √(log 2 + bigC * Sprime q2)

/-- The constant of (2), for `λ1/λ2` transcendental. -/
def nuTr : ℝ := 0.91237810306

/-- The constant of (3), for `λ1/λ2` algebraic. -/
def nuAlg : ℝ := 0.83372131685

/-- (2) and (3): `s0 = 2 + ⌈(log(2 C(q1,q2) |λ1 λ2|) - log η) / (-log ν)⌉`. -/
def s0 (ν l1 l2 : ℝ) (q1 q2 : ℕ) (η : ℝ) : ℤ :=
  2 + ⌈(log (2 * Cq q1 q2 * |l1 * l2|) - log η) / (-log ν)⌉

/-- The paper's Theorem, for a given constant `ν` and a given kind of `λ1/λ2`:
`λ1 > 1`, `λ2 < -1`, `|λ1/λ2| ≥ 1`, `λ1/λ2` irrational and of the given kind, all `μ_i ≠ 0`,
`λ_i/μ_i = a_i/q_i` reduced for `i = 1, 2`, `η` sufficiently small with
`η < min(λ1/a1, |λ2/a2|)`; then for every real `γ` and every `s ≥ s0` the inequality (6)
has infinitely many solutions. We add `2 ≤ s`, which the paper uses implicitly. -/
def MainStatement (ν : ℝ) (kind : ℝ → Prop) : Prop :=
  ∀ (l1 l2 : ℝ) (μ : ℕ → ℝ), 1 < l1 → l2 < -1 → 1 ≤ |l1 / l2| → Irrational (l1 / l2) →
    kind (l1 / l2) → (∀ i, μ i ≠ 0) →
    ∀ r1 r2 : ℚ, (r1 : ℝ) = l1 / μ 0 → (r2 : ℝ) = l2 / μ 1 →
    ∃ η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 0 < η → η < η0 → η < l1 / r1.num → η < |l2 / r2.num| →
      ∀ γ : ℝ, ∀ s : ℕ, 2 ≤ s → s0 ν l1 l2 r1.den r2.den η ≤ s →
        (Sol l1 l2 (fun i : Fin s => μ i) γ η).Infinite

/-- Solutions counted by the paper's `N(X)`: `εX ≤ p1, p2 ≤ X` and
`1 ≤ m_i ≤ L = log_2(εX/(2M))`, `M = |μ1| + ... + |μs|`. -/
def NX {s : ℕ} (l1 l2 : ℝ) (μ : Fin s → ℝ) (γ η ε X : ℝ) : ℕ :=
  Set.ncard {x ∈ Sol l1 l2 μ γ η | ε * X ≤ x.1 ∧ (x.1 : ℝ) ≤ X ∧ ε * X ≤ x.2.1 ∧
    (x.2.1 : ℝ) ≤ X ∧ ∀ i, (x.2.2 i : ℝ) ≤ logb 2 (ε * X / (2 * ∑ j, |μ j|))}

/-- Section 2, the quantitative form actually proved: under the Theorem's hypotheses, for every
sufficiently small `ε`, `N(X) ≥ c X (log X)^{s-2}` for all large `X`, with explicit existential
constants `c > 0`, `X0` standing for `≫_{s,λ,ε}`; the factor `η` is absorbed into `c`. -/
def DensityStatement (ν : ℝ) (kind : ℝ → Prop) : Prop :=
  ∀ (l1 l2 : ℝ) (μ : ℕ → ℝ), 1 < l1 → l2 < -1 → 1 ≤ |l1 / l2| → Irrational (l1 / l2) →
    kind (l1 / l2) → (∀ i, μ i ≠ 0) →
    ∀ r1 r2 : ℚ, (r1 : ℝ) = l1 / μ 0 → (r2 : ℝ) = l2 / μ 1 →
    ∃ η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 0 < η → η < η0 → η < l1 / r1.num → η < |l2 / r2.num| →
      ∀ γ : ℝ, ∀ s : ℕ, 2 ≤ s → s0 ν l1 l2 r1.den r2.den η ≤ s →
        ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε, 0 < ε → ε < ε0 → ∃ c X0 : ℝ, 0 < c ∧ ∀ X, X0 ≤ X →
          c * X * (log X) ^ (s - 2) ≤ NX l1 l2 (fun i : Fin s => μ i) γ η ε X

/-- The paper's Corollary: `λ1/λ2` negative and irrational, no size condition,
`η < min(|λ1/a1|, |λ2/a2|)` sufficiently small, `τ ≥ η`; then (10) with `τ` has infinitely
many solutions for every `γ` and `s ≥ s0(λ, μ, η)`. The bound `s0(λ, μ, η)` comes from the
Theorem after rescaling `λ, μ, γ, η` by a suitable constant, so it is existential here; the
Theorem's formula `s0 ν l1 l2 ...` at the unscaled `λ` was used before audit U-1012, run
20261019T0202Z-9877, and claimed more than the paper proves, since that formula is not scale
invariant. The old form is `CorollaryStatementFormula`, a `def` only. -/
def CorollaryStatement (ν : ℝ) (kind : ℝ → Prop) : Prop :=
  ∀ (l1 l2 : ℝ) (μ : ℕ → ℝ), l1 / l2 < 0 → Irrational (l1 / l2) →
    kind (l1 / l2) → (∀ i, μ i ≠ 0) →
    ∀ r1 r2 : ℚ, (r1 : ℝ) = l1 / μ 0 → (r2 : ℝ) = l2 / μ 1 →
    ∃ η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 0 < η → η < η0 → η < |l1 / r1.num| → η < |l2 / r2.num| →
      ∃ S0 : ℕ, ∀ τ : ℝ, η ≤ τ → ∀ γ : ℝ, ∀ s : ℕ, 2 ≤ s → S0 ≤ s →
        (Sol l1 l2 (fun i : Fin s => μ i) γ τ).Infinite

/-- The Corollary with the Theorem's `s0` formula at the unscaled `λ`. A `def` only. -/
def CorollaryStatementFormula (ν : ℝ) (kind : ℝ → Prop) : Prop :=
  ∀ (l1 l2 : ℝ) (μ : ℕ → ℝ), l1 / l2 < 0 → Irrational (l1 / l2) →
    kind (l1 / l2) → (∀ i, μ i ≠ 0) →
    ∀ r1 r2 : ℚ, (r1 : ℝ) = l1 / μ 0 → (r2 : ℝ) = l2 / μ 1 →
    ∃ η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 0 < η → η < η0 → η < |l1 / r1.num| → η < |l2 / r2.num| →
      ∀ τ : ℝ, η ≤ τ → ∀ γ : ℝ, ∀ s : ℕ, 2 ≤ s → s0 ν l1 l2 r1.den r2.den η ≤ s →
        (Sol l1 l2 (fun i : Fin s => μ i) γ τ).Infinite

/-- Transcendental over `ℚ`. -/
def IsTr (x : ℝ) : Prop := Transcendental ℚ x
/-- Algebraic over `ℚ`. -/
def IsAlg (x : ℝ) : Prop := IsAlgebraic ℚ x

/-! ### The paper, cited, with `sorry` -/

/-- P0079 Theorem, `λ1/λ2` transcendental, `s0` from (2). Cited. -/
theorem lz_theorem_tr : MainStatement nuTr IsTr := by sorry

/-- P0079 Theorem, `λ1/λ2` algebraic, `s0` from (3). Cited. -/
theorem lz_theorem_alg : MainStatement nuAlg IsAlg := by sorry

/-- P0079 Section 2, `N(X) ≫ η X (log X)^{s-2}`, transcendental case. Cited. -/
theorem lz_density_tr : DensityStatement nuTr IsTr := by sorry

/-- P0079 Section 2, `N(X) ≫ η X (log X)^{s-2}`, algebraic case. Cited. -/
theorem lz_density_alg : DensityStatement nuAlg IsAlg := by sorry

/-- P0079 Corollary, transcendental case. Cited. -/
theorem lz_corollary_tr : CorollaryStatement nuTr IsTr := by sorry

/-- P0079 Corollary, algebraic case. Cited. -/
theorem lz_corollary_alg : CorollaryStatement nuAlg IsAlg := by sorry

/-! ### Links, zero sorry -/

/-- Monotonicity in `η`: a solution for `η` is a solution for any `τ ≥ η`. -/
theorem sol_mono {s : ℕ} {l1 l2 γ η τ : ℝ} {μ : Fin s → ℝ} (h : η ≤ τ) :
    Sol l1 l2 μ γ η ⊆ Sol l1 l2 μ γ τ := by
  rintro x ⟨h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, h4.trans_le h⟩

theorem sol_infinite_mono {s : ℕ} {l1 l2 γ η τ : ℝ} {μ : Fin s → ℝ} (h : η ≤ τ)
    (hi : (Sol l1 l2 μ γ η).Infinite) : (Sol l1 l2 μ γ τ).Infinite :=
  hi.mono (sol_mono h)

/-- Scaling, the honest content of "multiplying by a suitable constant": for `t ≠ 0`, scaling
`λ, μ, γ` by `t` and `η` by `|t|` gives the same solution set. -/
theorem sol_scale {s : ℕ} {l1 l2 γ η t : ℝ} {μ : Fin s → ℝ} (ht : t ≠ 0) :
    Sol (t * l1) (t * l2) (fun i => t * μ i) (t * γ) (|t| * η) = Sol l1 l2 μ γ η := by
  ext x
  have hf : form (t * l1) (t * l2) (fun i => t * μ i) (t * γ) x.1 x.2.1 x.2.2
      = t * form l1 l2 μ γ x.1 x.2.1 x.2.2 := by
    simp only [form, mul_add, Finset.mul_sum]; ring_nf
  simp only [Sol, Set.mem_ofPred_eq, hf, abs_mul]
  have : 0 < |t| := abs_pos.mpr ht
  rw [mul_lt_mul_iff_right₀ this]

/-- `s0` is antitone in `η`: a larger `η` needs no more powers of two. -/
theorem s0_antitone {ν l1 l2 η η' : ℝ} {q1 q2 : ℕ} (hν0 : 0 < ν) (hν1 : ν < 1)
    (hη : 0 < η) (hle : η ≤ η') : s0 ν l1 l2 q1 q2 η' ≤ s0 ν l1 l2 q1 q2 η := by
  unfold s0
  have hd : 0 < -log ν := neg_pos.mpr (log_neg hν0 hν1)
  have hl : log η ≤ log η' := log_le_log hη hle
  gcongr

theorem nuAlg_pos : 0 < nuAlg := by norm_num [nuAlg]
theorem nuAlg_lt_one : nuAlg < 1 := by norm_num [nuAlg]
theorem nuTr_pos : 0 < nuTr := by norm_num [nuTr]
theorem nuTr_lt_one : nuTr < 1 := by norm_num [nuTr]
theorem nuAlg_lt_nuTr : nuAlg < nuTr := by norm_num [nuAlg, nuTr]

/-- The algebraic `s0` of (3) is at most the transcendental `s0` of (2) whenever the numerator
`log(2 C |λ1 λ2|) - log η` is nonnegative. -/
theorem s0_alg_le_tr {l1 l2 η : ℝ} {q1 q2 : ℕ}
    (hnum : 0 ≤ log (2 * Cq q1 q2 * |l1 * l2|) - log η) :
    s0 nuAlg l1 l2 q1 q2 η ≤ s0 nuTr l1 l2 q1 q2 η := by
  unfold s0
  have hT : 0 < -log nuTr := neg_pos.mpr (log_neg nuTr_pos nuTr_lt_one)
  have hA : -log nuTr ≤ -log nuAlg := neg_le_neg (log_le_log nuAlg_pos nuAlg_lt_nuTr.le)
  gcongr

/-- The quantitative form gives infinitely many solutions: `DensityStatement` implies
`MainStatement`, for any `ν` and kind. -/
theorem main_of_density {ν : ℝ} {kind : ℝ → Prop} (h : DensityStatement ν kind) :
    MainStatement ν kind := by
  intro l1 l2 μ h1 h2 h3 h4 h5 h6 r1 r2 hr1 hr2
  obtain ⟨η0, hη0, H⟩ := h l1 l2 μ h1 h2 h3 h4 h5 h6 r1 r2 hr1 hr2
  refine ⟨η0, hη0, fun η a b c d γ s hs hs0 => ?_⟩
  obtain ⟨ε0, hε0, H⟩ := H η a b c d γ s hs hs0
  obtain ⟨c', X0, hc, H⟩ := H (ε0 / 2) (by positivity) (by linarith)
  intro hfin
  set S := Sol l1 l2 (fun i : Fin s => μ i) γ η
  set X := max (max X0 3) ((S.ncard + 1) / c')
  have hX3 : (3 : ℝ) ≤ X := (le_max_right _ _).trans (le_max_left _ _)
  have hlog : 1 ≤ log X := by
    rw [← log_exp 1]
    exact log_le_log (exp_pos 1) (by linarith [exp_one_lt_d9])
  have hpow : 1 ≤ (log X) ^ (s - 2) := one_le_pow₀ hlog
  have hcX : (S.ncard : ℝ) + 1 ≤ c' * X := by
    have : (S.ncard + 1) / c' ≤ X := le_max_right _ _
    rwa [div_le_iff₀ hc, mul_comm] at this
  have hbig : c' * X ≤ c' * X * (log X) ^ (s - 2) := by
    have : 0 ≤ c' * X := by positivity
    nlinarith
  have hN := H X ((le_max_left _ _).trans (le_max_left _ _))
  have hsub : NX l1 l2 (fun i : Fin s => μ i) γ η (ε0 / 2) X ≤ S.ncard :=
    Set.ncard_le_ncard (fun x hx => hx.1) hfin
  have : (NX l1 l2 (fun i : Fin s => μ i) γ η (ε0 / 2) X : ℝ) ≤ S.ncard := by exact_mod_cast hsub
  linarith

/-- The Corollary in the Theorem's own regime follows from the Theorem and monotonicity in `η`:
`λ1 > 1`, `λ2 < -1`, `|λ1/λ2| ≥ 1`, and `a1 > 0` so that `λ1/a1 = |λ1/a1|`. -/
theorem corollary_in_regime {ν : ℝ} {kind : ℝ → Prop} (hM : MainStatement ν kind)
    (l1 l2 : ℝ) (μ : ℕ → ℝ) (h1 : 1 < l1) (h2 : l2 < -1) (h3 : 1 ≤ |l1 / l2|)
    (h4 : Irrational (l1 / l2)) (h5 : kind (l1 / l2)) (h6 : ∀ i, μ i ≠ 0)
    (r1 r2 : ℚ) (hr1 : (r1 : ℝ) = l1 / μ 0) (hr2 : (r2 : ℝ) = l2 / μ 1) (ha : 0 < r1.num) :
    ∃ η0 : ℝ, 0 < η0 ∧ ∀ η : ℝ, 0 < η → η < η0 → η < |l1 / r1.num| → η < |l2 / r2.num| →
      ∀ τ : ℝ, η ≤ τ → ∀ γ : ℝ, ∀ s : ℕ, 2 ≤ s → s0 ν l1 l2 r1.den r2.den η ≤ s →
        (Sol l1 l2 (fun i : Fin s => μ i) γ τ).Infinite := by
  obtain ⟨η0, hη0, H⟩ := hM l1 l2 μ h1 h2 h3 h4 h5 h6 r1 r2 hr1 hr2
  refine ⟨η0, hη0, fun η a b c d τ hτ γ s hs hs0 => ?_⟩
  have hpos : (0 : ℝ) < l1 / r1.num := div_pos (by linarith) (by exact_mod_cast ha)
  rw [abs_of_pos hpos] at c
  exact sol_infinite_mono hτ (H η a b c d γ s hs hs0)

/-- `N = p + q + 2^{ν_1} + ... + 2^{ν_K}` with all `ν_i ≥ 1`. This is a verbatim copy of
`LeanLab.Linnik.LinnikExact` in `LeanLab/Linnik/Statements.lean`; that module is not built, so
it is copied rather than imported. -/
def LinnikExact (K N : ℕ) : Prop :=
  ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ ∃ ν : Fin K → ℕ, (∀ i, 1 ≤ ν i) ∧ N = p + q + ∑ i, 2 ^ ν i

/-- Link to Linnik's problem: with `λ1 = λ2 = μ_i = 1`, `γ = -N` and `0 < η ≤ 1`, the
inequality (6) has a solution iff `N` is two primes and exactly `s` powers of two. This case
has `λ1/λ2 = 1` rational, so it is outside the paper's Theorem. -/
theorem sol_nonempty_iff_linnik {s N : ℕ} {η : ℝ} (h0 : 0 < η) (h1 : η ≤ 1) :
    (Sol 1 1 (fun _ : Fin s => (1 : ℝ)) (-(N : ℝ)) η).Nonempty ↔ LinnikExact s N := by
  have key : ∀ (p q : ℕ) (m : Fin s → ℕ), form 1 1 (fun _ : Fin s => (1 : ℝ)) (-(N : ℝ)) p q m
      = (((p + q + ∑ i, 2 ^ m i : ℕ) : ℤ) - (N : ℤ) : ℤ) := by
    intro p q m; simp [form]; ring
  constructor
  · rintro ⟨⟨p, q, m⟩, hp, hq, hm, hlt⟩
    refine ⟨p, q, hp, hq, m, hm, ?_⟩
    rw [key] at hlt
    have hlt' : |(((p + q + ∑ i, 2 ^ m i : ℕ) : ℤ) - (N : ℤ))| < 1 := by
      have : ((|(((p + q + ∑ i, 2 ^ m i : ℕ) : ℤ) - (N : ℤ))| : ℤ) : ℝ) < 1 := by
        push_cast at hlt ⊢; linarith
      exact_mod_cast this
    rw [Int.abs_lt_one_iff, sub_eq_zero] at hlt'
    exact_mod_cast hlt'.symm
  · rintro ⟨p, q, hp, hq, m, hm, hN⟩
    refine ⟨⟨p, q, m⟩, hp, hq, hm, ?_⟩
    show |form 1 1 (fun _ : Fin s => (1 : ℝ)) (-(N : ℝ)) p q m| < η
    rw [key, ← hN]; simpa using h0

/-- Binary Goldbach is the case `s = 0` of `LinnikExact`. -/
theorem linnikExact_zero_iff (N : ℕ) : LinnikExact 0 N ↔ IsGoldbachSum N := by
  constructor
  · rintro ⟨p, q, hp, hq, ν, -, hN⟩
    exact ⟨p, q, hp, hq, by simpa using hN.symm⟩
  · rintro ⟨p, q, hp, hq, h⟩
    exact ⟨p, q, hp, hq, Fin.elim0, fun i => i.elim0, by simp [h]⟩

/-! ### Kernel checks of the constants -/

/-- Lemma 4 proof: `C = 2B(1 + A(1))` with `B = 3.9171`, `A(1) < 0.2792521041`; the stated `C`
is at least this product and exceeds it by less than `10^{-9}`. -/
theorem bigC_check : 2 * 3.9171 * (1 + 0.2792521041 : ℝ) ≤ bigC ∧
    bigC < 2 * 3.9171 * (1 + 0.2792521041 : ℝ) + 1 / 10 ^ 9 := by
  norm_num [bigC]

/-- Lemma 4 proof, under the twin prime hypothesis `B = 1`: `2(1 + A(1)) = 2.5585042082`. -/
theorem bigC_twin_check : 2 * (1 + 0.2792521041 : ℝ) = 2.5585042082 := by norm_num

theorem Sprime_one : Sprime 1 = 1 := by simp [Sprime]

theorem Sprime_two : Sprime 2 = 1 := by
  simp only [Sprime, Nat.Prime.primeFactors Nat.prime_two, Finset.filter_singleton]; norm_num

theorem Sprime_three : Sprime 3 = 2 := by
  simp only [Sprime, Nat.Prime.primeFactors Nat.prime_three, Finset.filter_singleton]; norm_num

/-- `S'(2^k n) = S'(n)` for `n` odd is used after (27); here the instance `S'(4) = S'(1)`. -/
theorem Sprime_four : Sprime 4 = 1 := by
  have : Nat.primeFactors 4 = {2} := by
    rw [show (4 : ℕ) = 2 ^ 2 by norm_num, Nat.primeFactors_prime_pow (by norm_num) Nat.prime_two]
  simp only [Sprime, this, Finset.filter_singleton]; norm_num

end LeanLab.LZPowersOfTwo
