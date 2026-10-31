/-
# A kernel table for the cited Rosser and Schoenfeld θ bound

Unit U-1329, PC run 20261021T0103Z-19411, track T1, ladder rung 5b shared input.
AI-written Lean code, Claude, 2026-10-21. Checked only by the Lean kernel. Known mathematics.

`Lower1318.lean` reduced the cited `Dudek2014.Section22.Schoenfeld` to `RSThetaLower`:
`θ(t) ≥ 0.98 t` for `t ≥ 7481`, Rosser and Schoenfeld 1962 Theorem 10, p. 71. Here:
* `primStep`, `primorial_succ_eq_primStep`: `primorial (n+1)` from `primorial n` by one gcd,
  since `n+1` is prime iff it is coprime to `primorial n`;
* `thChk_table*`: `decide +kernel` tables, `5329^(n+1) ≤ 2000^(n+1) · primorial n` on
  `7481 ≤ n < T0`;
* `theta_ge_table`: hence `0.98 t ≤ θ t` on `7481 ≤ t < T0`, unconditional, via
  `exp 0.98 < 5329/2000`;
* `RSThetaLowerFrom`, `rsThetaLower_iff_from`: the cited input is equivalent to its tail `t ≥ T0`;
* `schoenfeld_of_rs_from`: `Schoenfeld` CONDITIONAL ON `RSThetaLowerFrom T0` only.
Goldbach is open.
-/
import LeanLab.Common.PsiTheta.Lower1318

namespace LeanLab.Common.PsiTheta

open Real Chebyshev
open LeanLab.Dudek2014.Section22

/-! ### Primorial by gcd -/

/-- One step: multiply by `n+1` iff it is coprime to the current product. -/
def primStep (n P : ℕ) : ℕ := cond (Nat.beq (Nat.gcd P (n + 1)) 1) (P * (n + 1)) P

lemma primorial_succ_if (n : ℕ) :
    primorial (n + 1) = if (n + 1).Prime then primorial n * (n + 1) else primorial n := by
  unfold primorial
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with h
  · rw [Finset.prod_insert (by simp), mul_comm]
  · rfl

lemma coprime_primorial_iff {n : ℕ} (hn : 1 ≤ n) :
    Nat.Coprime (primorial n) (n + 1) ↔ (n + 1).Prime := by
  constructor
  · intro hc
    by_contra hp
    have h1 : n + 1 ≠ 1 := by omega
    have hq := Nat.minFac_prime h1
    have hle : Nat.minFac (n + 1) ≤ n := by
      have h2 := Nat.minFac_le (show 0 < n + 1 by omega)
      have h3 : Nat.minFac (n + 1) ≠ n + 1 := by
        intro e; exact hp (Nat.prime_def_minFac.mpr ⟨by omega, e⟩)
      omega
    have hd : Nat.minFac (n + 1) ∣ primorial n := by
      unfold primorial
      apply Finset.dvd_prod_of_mem
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hq⟩
    have h4 : Nat.minFac (n + 1) ∣ Nat.gcd (primorial n) (n + 1) :=
      Nat.dvd_gcd hd (Nat.minFac_dvd _)
    rw [hc, Nat.dvd_one] at h4
    exact hq.one_lt.ne' h4
  · intro hp
    unfold primorial
    apply Nat.Coprime.prod_left
    intro q hq
    simp only [Finset.mem_filter, Finset.mem_range] at hq
    exact (Nat.coprime_primes hq.2 hp).mpr (by omega)

lemma primorial_succ_eq_primStep (n : ℕ) : primorial (n + 1) = primStep n (primorial n) := by
  unfold primStep
  rcases Nat.eq_zero_or_pos n with h | h
  · subst h; decide
  · rw [primorial_succ_if]
    have e := coprime_primorial_iff (n := n) h
    unfold Nat.Coprime at e
    by_cases hp : (n + 1).Prime
    · have : Nat.gcd (primorial n) (n + 1) = 1 := e.mpr hp
      rw [if_pos hp, this]; rfl
    · have : Nat.gcd (primorial n) (n + 1) ≠ 1 := fun h' => hp (e.mp h')
      rw [if_neg hp]
      have hb : Nat.beq (Nat.gcd (primorial n) (n + 1)) 1 = false := by
        exact Bool.eq_false_iff.mpr (fun h' => this (Nat.eq_of_beq_eq_true h'))
      rw [hb]; rfl

/-- `primIt k n (primorial n) = primorial (n + k)`. -/
def primIt : ℕ → ℕ → ℕ → ℕ
  | 0, _, P => P
  | k + 1, n, P => cond (Nat.ble 1 P) (primIt k (n + 1) (primStep n P)) 0

lemma primIt_eq : ∀ k n, primIt k n (primorial n) = primorial (n + k) := by
  intro k
  induction k with
  | zero => intro n; rfl
  | succ k ih =>
    intro n
    have hb : Nat.ble 1 (primorial n) = true := Nat.ble_eq.mpr (primorial_pos n)
    simp only [primIt, hb, Bool.cond_true]
    rw [← primorial_succ_eq_primStep, ih (n + 1)]
    congr 1; omega

/-! ### The kernel tables -/

/-- Row `n` state: `P = primorial n`, `A = 5329^(n+1)`, `B = 2000^(n+1)`; checks `k` rows. -/
def thChk : ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | 0, _, _, _, _ => true
  | k + 1, n, P, A, B =>
    Nat.ble A (B * P) && thChk k (n + 1) (primStep n P) (5329 * A) (2000 * B)

lemma thChk_sound : ∀ (k n : ℕ),
    thChk k n (primorial n) (5329 ^ (n + 1)) (2000 ^ (n + 1)) = true →
    ∀ m, n ≤ m → m < n + k → 5329 ^ (m + 1) ≤ 2000 ^ (m + 1) * primorial m := by
  intro k
  induction k with
  | zero => intro n _ m h1 h2; omega
  | succ k ih =>
    intro n h m h1 h2
    simp only [thChk, Bool.and_eq_true, Nat.ble_eq] at h
    rw [← primorial_succ_eq_primStep, show 5329 * 5329 ^ (n + 1) = 5329 ^ (n + 1 + 1) by ring,
      show 2000 * 2000 ^ (n + 1) = 2000 ^ (n + 1 + 1) by ring] at h
    rcases Nat.eq_or_lt_of_le h1 with e | e
    · subst e; exact h.1
    · exact ih (n + 1) h.2 m e (by omega)

lemma thChk_start (k n : ℕ)
    (h : thChk k n (primIt n 0 1) (5329 ^ (n + 1)) (2000 ^ (n + 1)) = true) :
    ∀ m, n ≤ m → m < n + k → 5329 ^ (m + 1) ≤ 2000 ^ (m + 1) * primorial m := by
  have e := primIt_eq n 0
  rw [zero_add, show primorial 0 = 1 by decide] at e
  rw [e] at h
  exact thChk_sound k n h

/-- Table 1: rows `7481 ≤ n < 17481`. -/
lemma thChk_table1 : thChk 10000 7481 (primIt 7481 0 1) (5329 ^ 7482) (2000 ^ 7482) = true := by
  decide +kernel

/-- Table 2: rows `17481 ≤ n < 27481`. -/
lemma thChk_table2 : thChk 10000 17481 (primIt 17481 0 1) (5329 ^ 17482) (2000 ^ 17482) = true := by
  decide +kernel

/-- Table 3: rows `27481 ≤ n < 37481`. -/
lemma thChk_table3 : thChk 10000 27481 (primIt 27481 0 1) (5329 ^ 27482) (2000 ^ 27482) = true := by
  decide +kernel

/-- **`5329^(n+1) ≤ 2000^(n+1) · primorial n` for `7481 ≤ n < T0`.** -/
theorem primorial_table {n : ℕ} (h1 : 7481 ≤ n) (h2 : n < 37481) :
    5329 ^ (n + 1) ≤ 2000 ^ (n + 1) * primorial n := by
  rcases lt_or_ge n 17481 with a | a
  · exact thChk_start 10000 7481 thChk_table1 n h1 (by omega)
  rcases lt_or_ge n 27481 with b | b
  · exact thChk_start 10000 17481 thChk_table2 n a (by omega)
  · exact thChk_start 10000 27481 thChk_table3 n b (by omega)

/-! ### Real analysis -/

/-- `exp 0.98 < 5329/2000 = 2.6645`, from `e < 2.7182818286` and `exp 0.02 ≥ 1.0202`. -/
lemma exp098_lt : exp (0.98 : ℝ) < 5329 / 2000 := by
  have h1 := Real.exp_one_lt_d9
  have h2 : (1.0202 : ℝ) ≤ exp 0.02 := by
    have := Real.quadratic_le_exp_of_nonneg (show (0 : ℝ) ≤ 0.02 by norm_num); nlinarith
  have : exp (1 : ℝ) = exp 0.98 * exp 0.02 := by rw [← Real.exp_add]; norm_num
  have hp := Real.exp_pos 0.98
  nlinarith

lemma log_ratio_gt : (0.98 : ℝ) < log 5329 - log 2000 := by
  rw [← Real.log_div (by norm_num) (by norm_num), Real.lt_log_iff_exp_lt (by norm_num)]
  have := exp098_lt; norm_num at this ⊢; linarith

/-- The real-variable form of a table row. -/
lemma theta_ge_of_row {t : ℝ} (ht : 0 ≤ t)
    (hrow : 5329 ^ (⌊t⌋₊ + 1) ≤ 2000 ^ (⌊t⌋₊ + 1) * primorial ⌊t⌋₊) : 0.98 * t ≤ θ t := by
  set n := ⌊t⌋₊ with hn
  have hnt' : t < n + 1 := Nat.lt_floor_add_one t
  have hR : ((5329 : ℝ)) ^ (n + 1) ≤ (2000 : ℝ) ^ (n + 1) * (primorial n : ℝ) := by
    exact_mod_cast hrow
  have hP0 : (0 : ℝ) < primorial n := by exact_mod_cast primorial_pos n
  have hlog := Real.log_le_log (by positivity) hR
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  rw [theta_eq_log_primorial]
  have h := log_ratio_gt
  have hn1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  push_cast at hlog
  nlinarith

/-- The upper end of the proved range. -/
def thetaT0 : ℝ := 37481

/-- **`0.98 t ≤ θ t` for `7481 ≤ t < T0`, unconditional.** -/
theorem theta_ge_table {t : ℝ} (h1 : 7481 ≤ t) (h2 : t < thetaT0) : 0.98 * t ≤ θ t := by
  have ht0 : 0 ≤ t := by linarith
  apply theta_ge_of_row ht0
  apply primorial_table
  · exact Nat.le_floor (by norm_num; linarith)
  · have := (Nat.floor_lt ht0).mpr (show t < ((37481 : ℕ) : ℝ) by
      unfold thetaT0 at h2; norm_num; linarith)
    exact this

/-! ### The shrunken cited input -/

/-- The tail of `RSThetaLower` from `T0` on: `0.98 t ≤ θ t` for every `t ≥ T0`. -/
def RSThetaLowerFrom (T0 : ℝ) : Prop :=
  ∀ t : ℝ, T0 ≤ t → 0.98 * t ≤ θ t

/-- **The cited `RSThetaLower` is equivalent to its tail from `T0`.** -/
theorem rsThetaLower_iff_from : RSThetaLower ↔ RSThetaLowerFrom thetaT0 := by
  constructor
  · intro h t ht
    exact h t (by unfold thetaT0 at ht; linarith)
  · intro h t ht
    rcases lt_or_ge t thetaT0 with h' | h'
    · exact theta_ge_table ht h'
    · exact h t h'

/-- **`Schoenfeld` from the tail of the Rosser and Schoenfeld bound.**
CONDITIONAL ON `RSThetaLowerFrom thetaT0` only. -/
theorem schoenfeld_of_rs_from (h : RSThetaLowerFrom thetaT0) : Schoenfeld :=
  schoenfeld_of_rs (rsThetaLower_iff_from.mpr h)

/-- Vacuity instance of the table range: `0.98 · 7481 ≤ θ 7481`. -/
theorem theta_ge_at_7481 : 0.98 * (7481 : ℝ) ≤ θ 7481 :=
  theta_ge_table le_rfl (by unfold thetaT0; norm_num)

end LeanLab.Common.PsiTheta
