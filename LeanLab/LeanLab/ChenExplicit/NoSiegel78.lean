/-
Lean Lab, ChenExplicit, unit U-1219, idea I-0090, track T2 FRONTIER, run 20261020T1403Z-32020.
P0009, Bordignon, Johnston, Starichkova, "An explicit version of Chen's theorem", arXiv 2207.09452,
read from the repo copy papers/P0009.txt: Theorem 26 and Lemmas 27, 30, 32, page 21 to 28, and
Theorems 44, 50, 51, pages 42, 47, 56.

What is here, AI wrote this Lean code:
* `kadiriEdge_gt`, `noSiegel_of_H78`: under `Hθ (7/8)` no zero of a primitive L-function mod
  q ≥ 4 lies in Kadiri's zone β ≥ 1 − 1/(R₀ log max(q, q|γ|)), R₀ = 6.3970, of BJS Theorem 26.
* `noExceptional_of_H78`: under `Hθ (7/8)` there is no BJS exceptional zero
  β ≥ 1 − 1/(2 R₁ log Q₁), R₁ = 2.0452, once log Q₁ ≥ 2; in BJS log Q₁ = 10 log log x ≥ 104.
  So k₁ = k₂ = 0 in (77), and only case (a) of Theorems 44 and 50 can occur.
* `beta_term_le`: the Siegel term x^{β−1}/β of Lemmas 27 to 29 is at most (8/7) x^{−1/8} for every
  1/2 ≤ β ≤ 7/8 once log x ≥ 2.
* `thm50_alpha_floor`, `thm44_alpha_floor`, `thm51_alpha_floor`: the u₀ = 10⁹ conditions of
  Theorems 44, 50, 51 with their ranges α₁ < 1/8, α₂ < 1/24, α₃ < 1/6 force log N > 8·10⁹,
  24·10⁹, 6·10⁹. With Theorem 50 that is log log N > 23.8 for every N the paper's argument
  covers, whatever is known about zeros. A barrier of the framework, not of Chen's theorem.

Every result here is PROVED, 0 sorry. `noSiegel_of_H78` and `noExceptional_of_H78` take
`Hθ (7/8)` as a hypothesis; the 7/8 theorem is OpenAI's unrefereed claim, checked by the lab only
as Lean in the openai/math workspace, see OAIQuasiRiemann/LabBridge.lean.txt. Binary Goldbach is
OPEN; nothing here is progress on it.
-/
import LeanLab.ExceptionalSet.PintzAlthofer2026

namespace LeanLab.ChenExplicit.NoSiegel78

open Real
open LeanLab.ExceptionalSet.PintzAlthofer2026 (Hθ)

/-- Kadiri's constant `R₀ = 6.3970`, BJS Theorem 26. -/
noncomputable def R0 : ℝ := 6.3970

/-- `R₁ = 2.0452`, BJS Theorem 26. -/
noncomputable def R1 : ℝ := 2.0452

/-- The left edge of Kadiri's Siegel zone at height `Q = max(q, q|γ|)`: `1 − 1/(R₀ log Q)`. -/
noncomputable def kadiriEdge (Q : ℝ) : ℝ := 1 - 1 / (R0 * log Q)

/-- The left edge of the BJS exceptional zone up to `Q₁`: `1 − 1/(2 R₁ log Q₁)`. -/
noncomputable def exceptionalEdge (Q1 : ℝ) : ℝ := 1 - 1 / (2 * R1 * log Q1)

lemma log_four_gt : (1.38 : ℝ) < log 4 := by
  have h2 := Real.log_two_gt_d9
  have : log (4 : ℝ) = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast; ring
  rw [this]; linarith

/-- For `Q ≥ 4` Kadiri's zone lies right of `7/8`. -/
theorem kadiriEdge_gt (Q : ℝ) (hQ : 4 ≤ Q) : 7 / 8 < kadiriEdge Q := by
  have hl : (1.38 : ℝ) < log Q :=
    lt_of_lt_of_le log_four_gt (Real.log_le_log (by norm_num) hQ)
  have hpos : (8 : ℝ) < R0 * log Q := by
    unfold R0; nlinarith
  unfold kadiriEdge
  have : 1 / (R0 * log Q) < 1 / 8 := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith

/-- Under `Hθ (7/8)`, no zero of a primitive L-function mod `q ≥ 4` lies in Kadiri's Siegel
zone of BJS Theorem 26: every zero `s` with `0 < Re s < 1` has `Re s < 1 − 1/(R₀ log Q)` for every
`Q ≥ q`, in particular for `Q = max(q, q|γ|)`. -/
theorem noSiegel_of_H78 (h : Hθ (7 / 8)) (q : ℕ) [NeZero q] (hq : 4 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : DirichletCharacter.LFunction χ s = 0) (Q : ℝ) (hQ : (q : ℝ) ≤ Q) :
    s.re < kadiriEdge Q := by
  have h1 := h q χ hχ s hs0 hs1 hz
  have h4 : (4 : ℝ) ≤ Q := le_trans (by exact_mod_cast hq) hQ
  linarith [kadiriEdge_gt Q h4]

/-- The same at Theorem 26's own height `Q = max(q, q|γ|)`. -/
theorem noSiegel_of_H78_height (h : Hθ (7 / 8)) (q : ℕ) [NeZero q] (hq : 4 ≤ q)
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : DirichletCharacter.LFunction χ s = 0) :
    s.re < kadiriEdge (max (q : ℝ) ((q : ℝ) * |s.im|)) :=
  noSiegel_of_H78 h q hq χ hχ s hs0 hs1 hz _ (le_max_left _ _)

/-- For `log Q₁ ≥ 2` the BJS exceptional zone lies right of `7/8`. -/
theorem exceptionalEdge_gt (Q1 : ℝ) (hQ : 2 ≤ log Q1) : 7 / 8 < exceptionalEdge Q1 := by
  have hpos : (8 : ℝ) < 2 * R1 * log Q1 := by unfold R1; nlinarith
  unfold exceptionalEdge
  have : 1 / (2 * R1 * log Q1) < 1 / 8 := by
    rw [div_lt_div_iff₀ (by linarith) (by norm_num)]; linarith
  linarith

/-- Under `Hθ (7/8)` there is no exceptional zero in the sense of BJS Theorem 26: no zero of a
primitive L-function, of any modulus, has real part in `[1 − 1/(2 R₁ log Q₁), 1)` once
`log Q₁ ≥ 2`. In BJS, `Q₁ = log¹⁰ xᵢ` with `log log xᵢ ≥ 10.4`, so `log Q₁ ≥ 104`; hence the
exceptional modulus `k₀(xᵢ)` does not exist and `kᵢ = 0` in (77). -/
theorem noExceptional_of_H78 (h : Hθ (7 / 8)) (Q1 : ℝ) (hQ : 2 ≤ log Q1) (q : ℕ) [NeZero q]
    (χ : DirichletCharacter ℂ q) (hχ : χ.IsPrimitive) (s : ℂ) (hs0 : 0 < s.re) (hs1 : s.re < 1)
    (hz : DirichletCharacter.LFunction χ s = 0) : s.re < exceptionalEdge Q1 := by
  have h1 := h q χ hχ s hs0 hs1 hz
  linarith [exceptionalEdge_gt Q1 hQ]

/-- In BJS, `log Q₁(x) = 10 log log x`, so `log log x ≥ 10.4` gives `log Q₁ ≥ 2`. -/
lemma logQ1_ge (x : ℝ) (hx : 10.4 ≤ log (log x)) (hx1 : 1 < log x) :
    2 ≤ log (log x ^ 10) := by
  rw [Real.log_pow]; push_cast; linarith

/-- The Siegel term of Lemmas 27 to 29: for `1/2 ≤ β ≤ 7/8` and `log x ≥ 2`,
`x^{β−1}/β ≤ (8/7) x^{−1/8}`. Under `Hθ (7/8)` any Siegel zero left in Lemma 27 is mod `k ≤ 3`
with `β ≥ 1 − 1/(R₀ log 3) > 1/2`, so this covers it. -/
theorem beta_term_le (x β : ℝ) (hx : 0 < x) (hlx : 2 ≤ log x) (hb1 : 1 / 2 ≤ β)
    (hb2 : β ≤ 7 / 8) : x ^ (β - 1) / β ≤ 8 / 7 * x ^ (-(1 / 8 : ℝ)) := by
  set t := 7 / 8 - β with ht
  have ht0 : 0 ≤ t := by linarith
  have hβ : 0 < β := by linarith
  -- x^t ≥ 1 + t log x ≥ 1 + 2t
  have hxt : 1 + 2 * t ≤ x ^ t := by
    rw [Real.rpow_def_of_pos hx]
    have := Real.add_one_le_exp (log x * t)
    nlinarith
  have hsplit : x ^ (β - 1) = x ^ (-(1 / 8 : ℝ)) / x ^ t := by
    rw [← Real.rpow_sub hx]; congr 1; rw [ht]; ring
  have hxpos : 0 < x ^ (-(1 / 8 : ℝ)) := Real.rpow_pos_of_pos hx _
  have hxtpos : 0 < x ^ t := Real.rpow_pos_of_pos hx _
  rw [hsplit, div_div, div_le_iff₀ (by positivity)]
  -- need x^{-1/8} ≤ 8/7 x^{-1/8} (x^t β), i.e. 1 ≤ (8/7) β x^t
  have key : 1 ≤ 8 / 7 * (x ^ t * β) := by
    have hb : β = 7 / 8 - t := by rw [ht]; ring
    rw [hb]
    have h38 : t ≤ 3 / 8 := by linarith
    nlinarith
  nlinarith

/-! ### The u₀ floor of Theorems 44, 50, 51

Each theorem asks `N^α / (log-powers) ≥ exp(u₀(1 + 9·10⁻⁷/log u₀))` with `u₀ = 10⁹`. In logs, with
`L = log N`, the left side is `α L` minus nonnegative log-log terms, so `α L ≥ 10⁹`. -/

/-- `u₀ (1 + 9·10⁻⁷/log u₀) ≥ 10⁹` for `u₀ = 10⁹`. -/
lemma U0_ge : (10 ^ 9 : ℝ) ≤ 10 ^ 9 * (1 + 9e-7 / log (10 ^ 9)) := by
  have : 0 < log ((10 : ℝ) ^ 9) := Real.log_pos (by norm_num)
  have : 0 ≤ 9e-7 / log ((10 : ℝ) ^ 9) := by positivity
  nlinarith

/-- `exp 23.8 < 2.4·10¹⁰`. -/
lemma exp_238_lt : exp (23.8 : ℝ) < 2.4e10 := by
  have h1 : exp (23.8 : ℝ) = exp 1 ^ 23 * exp 0.8 := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num
  have he := Real.exp_one_lt_d9
  have he0 : 0 < exp (1 : ℝ) := Real.exp_pos 1
  have h08 : exp (0.8 : ℝ) ≤ 2.2268 := by
    have hb := Real.exp_bound' (x := (0.8 : ℝ)) (by norm_num) (by norm_num) (n := 4) (by norm_num)
    norm_num [Finset.sum_range_succ, Nat.factorial] at hb
    linarith
  have hpow : exp (1 : ℝ) ^ 23 < 2.7182818286 ^ 23 := by
    apply pow_lt_pow_left₀ he he0.le (by norm_num)
  rw [h1]
  have : (2.7182818286 : ℝ) ^ 23 * 2.2268 < 2.4e10 := by norm_num
  have h08' : 0 < exp (0.8 : ℝ) := Real.exp_pos _
  calc exp 1 ^ 23 * exp 0.8 ≤ 2.7182818286 ^ 23 * exp 0.8 := by
        exact mul_le_mul_of_nonneg_right hpow.le h08'.le
    _ ≤ 2.7182818286 ^ 23 * 2.2268 := by
        exact mul_le_mul_of_nonneg_left h08 (by positivity)
    _ < 2.4e10 := this

/-- The log form of the Theorem 50 condition: `α L − 10 log lx₁ − 2.5 log L ≥ U₀` with
`L = log N ≥ 1`, `lx₁ = log x₁(N) ≥ 1` and `0 < α < 1/24` gives `L > 24·10⁹` and
`log L > 23.8`. -/
theorem thm50_alpha_floor_log (α L lx1 : ℝ) (hL : 1 ≤ L) (hx1 : 1 ≤ lx1) (hα : α < 1 / 24)
    (hcond : 10 ^ 9 * (1 + 9e-7 / log (10 ^ 9)) ≤ α * L - 10 * log lx1 - 2.5 * log L) :
    24e9 < L ∧ 23.8 < log L := by
  have h1 : 0 ≤ log lx1 := Real.log_nonneg hx1
  have h2 : 0 ≤ log L := Real.log_nonneg hL
  have hU := U0_ge
  have hαL : 10 ^ 9 ≤ α * L := by linarith
  have hL24 : 24e9 < L := by nlinarith
  refine ⟨hL24, ?_⟩
  have : exp (23.8 : ℝ) < L := lt_trans exp_238_lt (by linarith)
  rw [Real.lt_log_iff_exp_lt (by linarith)]; exact this

/-- Theorem 50's condition as printed, with `N` itself: `N^{α₂}/(log¹⁰ x₁(N) log^{2.5} N) ≥
exp(u₀(1 + 9·10⁻⁷/log u₀))`, `u₀ = 10⁹`, `x₁(N) = N/log⁵ N` and the range `0 < α₂ < 1/24`, force
`log N > 24·10⁹` and `log log N > 23.8`. -/
theorem thm50_alpha_floor (N α : ℝ) (hN : 0 < N) (hL : 1 ≤ log N)
    (hx1 : 1 ≤ log (N / log N ^ 5)) (hα : α < 1 / 24)
    (hcond : exp (10 ^ 9 * (1 + 9e-7 / log (10 ^ 9))) ≤
      N ^ α / (log (N / log N ^ 5) ^ (10 : ℝ) * log N ^ (2.5 : ℝ))) :
    24e9 < log N ∧ 23.8 < log (log N) := by
  set L := log N
  set lx1 := log (N / log N ^ 5)
  have hLpos : 0 < L := by linarith
  have hx1pos : 0 < lx1 := by linarith
  have hden : 0 < lx1 ^ (10 : ℝ) * L ^ (2.5 : ℝ) := by positivity
  have hnum : 0 < N ^ α := Real.rpow_pos_of_pos hN _
  have hlog := Real.log_le_log (Real.exp_pos _) hcond
  rw [Real.log_exp, Real.log_div hnum.ne' hden.ne', Real.log_mul (by positivity) (by positivity),
    Real.log_rpow hN, Real.log_rpow hx1pos, Real.log_rpow hLpos] at hlog
  exact thm50_alpha_floor_log α L lx1 hL hx1 hα (by linarith)

/-- Theorem 44's condition, same form, with `8α₁ < 1` from (140): `log N > 8·10⁹`. -/
theorem thm44_alpha_floor_log (α L lx1 : ℝ) (hL : 1 ≤ L) (hx1 : 1 ≤ lx1) (hα : 8 * α < 1)
    (hcond : 10 ^ 9 * (1 + 9e-7 / log (10 ^ 9)) ≤ α * L - 10 * log lx1 - 2.5 * log L) :
    8e9 < L := by
  have h1 : 0 ≤ log lx1 := Real.log_nonneg hx1
  have h2 : 0 ≤ log L := Real.log_nonneg hL
  have hU := U0_ge
  nlinarith

/-- Theorem 51's condition in logs, `log 310 + α₃ L − 10 log L ≥ U₀` with `α₃ < 1/6`:
`log N > 6·10⁹ − 36`. -/
theorem thm51_alpha_floor_log (α L : ℝ) (hL : 1 ≤ L) (hα : α < 1 / 6)
    (hcond : 10 ^ 9 * (1 + 9e-7 / log (10 ^ 9)) ≤ log 310 + α * L - 10 * log L) :
    6e9 - 36 < L := by
  have h2 : 0 ≤ log L := Real.log_nonneg hL
  have hU := U0_ge
  have h310 : log (310 : ℝ) < 6 := by
    rw [Real.log_lt_iff_lt_exp (by norm_num)]
    have := Real.add_one_le_exp (6 : ℝ)
    have h3 : (310 : ℝ) < exp 6 := by
      have he : (2.7 : ℝ) < exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
      have : exp (6 : ℝ) = exp 1 ^ 6 := by rw [← Real.exp_nat_mul]; norm_num
      rw [this]
      calc (310 : ℝ) < 2.7 ^ 6 := by norm_num
        _ < exp 1 ^ 6 := pow_lt_pow_left₀ he (by norm_num) (by norm_num)
    exact h3
  nlinarith

/-! ### Vacuity: the hypotheses can hold -/

/-- Theorem 50's log condition holds at `L = 10¹²`, `lx₁ = 1`, `α = 1/25`, inside the range. -/
example : 10 ^ 9 * (1 + 9e-7 / log (10 ^ 9)) ≤
    (1 / 25 : ℝ) * 10 ^ 12 - 10 * log 1 - 2.5 * log (10 ^ 12) := by
  have hlog : log ((10 : ℝ) ^ 12) ≤ 10 ^ 12 := by
    have := Real.log_le_sub_one_of_pos (x := (10 : ℝ) ^ 12) (by norm_num); linarith
  have h9 : (1 : ℝ) ≤ log (10 ^ 9) := by
    rw [Real.le_log_iff_exp_le (by norm_num)]
    have : exp (1 : ℝ) < 3 := lt_trans Real.exp_one_lt_d9 (by norm_num)
    linarith
  have hfrac : 9e-7 / log ((10 : ℝ) ^ 9) ≤ 9e-7 := div_le_self (by norm_num) h9
  have hl12 : log ((10 : ℝ) ^ 12) ≤ 28 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have : (2.7 : ℝ) < exp 1 := lt_trans (by norm_num) Real.exp_one_gt_d9
    have h28 : exp (28 : ℝ) = exp 1 ^ 28 := by rw [← Real.exp_nat_mul]; norm_num
    rw [h28]
    calc (10 : ℝ) ^ 12 ≤ 2.7 ^ 28 := by norm_num
      _ ≤ exp 1 ^ 28 := pow_le_pow_left₀ (by norm_num) this.le 28
  rw [Real.log_one]
  have hm : (10 : ℝ) ^ 9 * (1 + 9e-7 / log (10 ^ 9)) ≤ 10 ^ 9 * (1 + 9e-7) := by gcongr
  have h25 : (2.5 : ℝ) * log (10 ^ 12) ≤ 2.5 * 28 := by gcongr
  norm_num at hm h25 ⊢
  linarith

/-- `beta_term_le` is not vacuous: `x = e²`, `β = 7/8` meets its hypotheses. -/
example : (0 : ℝ) < exp 2 ∧ 2 ≤ log (exp 2) ∧ (1 / 2 : ℝ) ≤ 7 / 8 ∧ (7 / 8 : ℝ) ≤ 7 / 8 :=
  ⟨Real.exp_pos 2, by rw [Real.log_exp], by norm_num, le_rfl⟩

end LeanLab.ChenExplicit.NoSiegel78

#print axioms LeanLab.ChenExplicit.NoSiegel78.noSiegel_of_H78
#print axioms LeanLab.ChenExplicit.NoSiegel78.noSiegel_of_H78_height
#print axioms LeanLab.ChenExplicit.NoSiegel78.noExceptional_of_H78
#print axioms LeanLab.ChenExplicit.NoSiegel78.logQ1_ge
#print axioms LeanLab.ChenExplicit.NoSiegel78.beta_term_le
#print axioms LeanLab.ChenExplicit.NoSiegel78.thm50_alpha_floor
#print axioms LeanLab.ChenExplicit.NoSiegel78.thm50_alpha_floor_log
#print axioms LeanLab.ChenExplicit.NoSiegel78.thm44_alpha_floor_log
#print axioms LeanLab.ChenExplicit.NoSiegel78.thm51_alpha_floor_log
#print axioms LeanLab.ChenExplicit.NoSiegel78.exp_238_lt
