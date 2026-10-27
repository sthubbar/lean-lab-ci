/-
P0009 Bordignon, Johnston, Starichkova 2022, Theorem 5 at the corrected threshold.
The paper, page 63: Theorem 5 follows from Theorem 3 and Dudek's theorem by computing the largest
k with p₁ ⋯ p_k ≤ exp(exp 32.7), and [46, Theorems 3 & 4] give e^29.2 < k < e^29.3.
FINDING F-0023 shows the printed Section 9 argument does not reach exp(exp 32.7); the lab's
corrected chain reaches exp(exp 32.73). This file shows the e^29.3 of Theorem 5 survives at
exp(exp 32.73): CONDITIONAL ON Theorem 3 in the Chen form at 32.73, Dudek's theorem, Dusart 2010
Theorem 5.2 k = 2, and Dusart 2010's bound π(x) ≤ x / (ln x - 1.1) for x ≥ 60184.
The step from primorials to a prime count is proved here unconditionally, `card_primeFactors_le`.
Audit U-1011 and unit U-1021, run 20261019T0403Z-4324. AI-written Lean code, Claude.
Checked only by the Lean kernel. Goldbach is open.
-/
import LeanLab.AlmostPrimes.Statements
import LeanLab.Common.ThetaWindowDusart

open Real Finset

namespace LeanLab.AlmostPrimes.Thm5

/-- Dusart 2010, arXiv 1002.0442, introduction display: `π(x) ≤ x/(ln x − 1.1)` for
`x ≥ 60184`. Read twice on ar5iv by WebFetch, non-strict. Cited. -/
def DusartPi11 : Prop :=
  ∀ x : ℝ, 60184 ≤ x → ((Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) ≤ x / (Real.log x - 1.1)

/-- Dudek, BJS Theorem 53: every integer greater than two is a prime plus a square-free
number. Cited. -/
def DudekSqfree : Prop :=
  ∀ N : ℕ, 2 < N → ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m

/-- Unconditional: if `log m < θ X` then `m` has at most `π ⌊X⌋` distinct prime factors.
A set of primes with more elements than the primes up to `X` has log-sum at least `θ X`. -/
theorem card_primeFactors_le {m : ℕ} (hm : 0 < m) {X : ℝ} (_hX : 0 ≤ X)
    (hlog : Real.log m < Chebyshev.theta X) :
    m.primeFactors.card ≤ Nat.primeCounting ⌊X⌋₊ := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  set S := m.primeFactors
  set A := Nat.primesLE ⌊X⌋₊
  by_contra hcon
  push Not at hcon
  set c := Real.log ((⌊X⌋₊ : ℝ) + 1)
  have hc : 0 ≤ c := Real.log_nonneg (by have := Nat.cast_nonneg (α := ℝ) ⌊X⌋₊; linarith)
  have hA : ∀ q ∈ A, q.Prime ∧ q ≤ ⌊X⌋₊ := fun q hq => by
    simpa [A, Nat.primesLE, Nat.mem_primesBelow, Nat.lt_succ_iff, and_comm] using hq
  have hSA : ∀ p ∈ S \ A, c ≤ Real.log p := by
    intro p hp
    rw [mem_sdiff] at hp
    have hpp : p.Prime := Nat.prime_of_mem_primeFactors hp.1
    have : ⌊X⌋₊ < p := by
      by_contra h; push Not at h
      exact hp.2 (by simp [A, Nat.primesLE, Nat.mem_primesBelow, h, hpp])
    apply Real.log_le_log (by positivity)
    exact_mod_cast this
  have hAS : ∀ q ∈ A \ S, Real.log q ≤ c := by
    intro q hq
    rw [mem_sdiff] at hq
    have := (hA q hq.1)
    apply Real.log_le_log (by exact_mod_cast this.1.pos)
    have : (q : ℝ) ≤ ⌊X⌋₊ := by exact_mod_cast this.2
    linarith
  have hcard : (A \ S).card ≤ (S \ A).card := by
    have h1 := card_sdiff_add_card_inter S A
    have h2 := card_sdiff_add_card_inter A S
    rw [inter_comm] at h2
    omega
  have e1 : ∑ p ∈ S, Real.log p = ∑ p ∈ S ∩ A, Real.log p + ∑ p ∈ S \ A, Real.log p :=
    (sum_inter_add_sum_sdiff _ _ _).symm
  have e2 : ∑ p ∈ A, Real.log p = ∑ p ∈ S ∩ A, Real.log p + ∑ p ∈ A \ S, Real.log p := by
    rw [inter_comm]; exact (sum_inter_add_sum_sdiff _ _ _).symm
  have b1 : ((S \ A).card : ℝ) * c ≤ ∑ p ∈ S \ A, Real.log p := by
    rw [← nsmul_eq_mul, ← sum_const]; exact sum_le_sum hSA
  have b2 : ∑ p ∈ A \ S, Real.log p ≤ ((A \ S).card : ℝ) * c := by
    rw [← nsmul_eq_mul, ← sum_const]; exact sum_le_sum hAS
  have b3 : ((A \ S).card : ℝ) * c ≤ ((S \ A).card : ℝ) * c :=
    mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) hc
  have hθ : Chebyshev.theta X = ∑ p ∈ A, Real.log p := Chebyshev.theta_eq_sum_primesLE X
  have hSm : ∑ p ∈ S, Real.log p ≤ Real.log m := by
    rw [← Real.log_prod (fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).ne_zero)]
    apply Real.log_le_log
    · exact prod_pos fun p hp => by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
    · have := Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
      rw [← Nat.cast_prod]; exact_mod_cast this
  linarith

/-- Unconditional: Ω equals the number of distinct prime factors for square-free `m`. -/
theorem bigOmega_eq_card_of_squarefree {m : ℕ} (hm : 0 < m) (hsq : Squarefree m) :
    bigOmega m = m.primeFactors.card := by
  rw [bigOmega_eq_cardFactors, ← (ArithmeticFunction.cardDistinctFactors_eq_cardFactors_iff_squarefree
    hm.ne').2 hsq, ArithmeticFunction.cardDistinctFactors_apply, Nat.primeFactors,
    List.card_toFinset]

/-! ### Numerics at the corrected threshold, unconditional -/

theorem exp_043_le : Real.exp 0.43 ≤ 1.5374 := by
  have h := Real.exp_bound (x := 0.43) (by norm_num [abs_of_pos]) (n := 6) (by norm_num)
  rw [abs_le] at h
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  norm_num [abs_of_pos] at h
  linarith [h.2]

theorem exp_343_le : Real.exp 3.43 ≤ 30.89 := by
  have h3 : Real.exp 3 ≤ 2.7182818286 ^ 3 := by
    rw [show (3 : ℝ) = (3 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
  have : Real.exp 3.43 = Real.exp 3 * Real.exp 0.43 := by rw [← Real.exp_add]; norm_num
  rw [this]
  have := exp_043_le
  have hp : 0 ≤ Real.exp 0.43 := (Real.exp_pos _).le
  calc Real.exp 3 * Real.exp 0.43 ≤ 2.7182818286 ^ 3 * 1.5374 :=
        mul_le_mul h3 this hp (by positivity)
    _ ≤ 30.89 := by norm_num

theorem exp_3273_ge : (6 : ℝ) * 10 ^ 13 ≤ Real.exp 32.73 := by
  have h : 2.7182818283 ^ 32 ≤ Real.exp 32 := by
    rw [show (32 : ℝ) = (32 : ℕ) * 1 by norm_num, Real.exp_nat_mul]
    exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 32
  have : Real.exp 32 ≤ Real.exp 32.73 := Real.exp_le_exp.2 (by norm_num)
  have h2 : (6 : ℝ) * 10 ^ 13 ≤ 2.7182818283 ^ 32 := by norm_num
  linarith

/-- The cut-off `X = 1.001 exp 32.73`. -/
noncomputable def X0 : ℝ := Real.exp 32.73 * 1.001

theorem log_X0 : Real.log X0 = 32.73 + Real.log 1.001 := by
  rw [X0, Real.log_mul (Real.exp_pos _).ne' (by norm_num), Real.log_exp]

theorem log_X0_bounds : 32.73 ≤ Real.log X0 ∧ Real.log X0 ≤ 32.731 := by
  rw [log_X0]
  have h0 : 0 ≤ Real.log 1.001 := Real.log_nonneg (by norm_num)
  have h1 : Real.log 1.001 ≤ 1.001 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  constructor <;> linarith

theorem X0_ge : (6 : ℝ) * 10 ^ 13 ≤ X0 := by
  have := exp_3273_ge; rw [X0]; nlinarith

/-- CONDITIONAL ON Dusart Theorem 5.2 k = 2: `exp 32.73 < θ X0`. -/
theorem theta_X0 (hD : LeanLab.Common.ThetaWindow.DusartThm52k2) :
    Real.exp 32.73 < Chebyshev.theta X0 := by
  have hX := X0_ge
  have h := hD X0 (by linarith)
  rw [abs_le] at h
  obtain ⟨hL, -⟩ := log_X0_bounds
  have hL2 : (32.73 : ℝ) ^ 2 ≤ Real.log X0 ^ 2 := pow_le_pow_left₀ (by norm_num) hL 2
  have hX0 : 0 < X0 := by linarith
  have hE : 0.01 * X0 / Real.log X0 ^ 2 ≤ 0.01 * X0 / 32.73 ^ 2 :=
    div_le_div_of_nonneg_left (by positivity) (by positivity) hL2
  have : Real.exp 32.73 = X0 / 1.001 := by rw [X0]; field_simp
  rw [this]
  have hq : X0 / 1.001 ≤ 0.9991 * X0 := by rw [div_le_iff₀ (by norm_num)]; nlinarith
  have : 0.01 * X0 / 32.73 ^ 2 < X0 - X0 / 1.001 := by
    rw [div_lt_iff₀ (by norm_num)]; nlinarith
  linarith [h.1]

/-- CONDITIONAL ON Dusart's `π(x) ≤ x/(ln x − 1.1)`: `π ⌊X0⌋ ≤ e^29.3`. -/
theorem pi_X0 (hP : DusartPi11) :
    ((Nat.primeCounting ⌊X0⌋₊ : ℕ) : ℝ) ≤ Real.exp 29.3 := by
  have hX := X0_ge
  have h := hP X0 (by linarith)
  obtain ⟨hL, -⟩ := log_X0_bounds
  have hX0 : 0 < X0 := by linarith
  have h1 : X0 / (Real.log X0 - 1.1) ≤ X0 / 31.63 :=
    div_le_div_of_nonneg_left hX0.le (by norm_num) (by linarith)
  have hsplit : X0 = Real.exp 29.3 * Real.exp 3.43 * 1.001 := by
    rw [X0, ← Real.exp_add]; norm_num
  have he := exp_343_le
  have hp : 0 < Real.exp 29.3 := Real.exp_pos _
  have h2 : X0 / 31.63 ≤ Real.exp 29.3 := by
    rw [div_le_iff₀ (by norm_num), hsplit]
    have : Real.exp 3.43 * 1.001 ≤ 31.63 := by nlinarith
    nlinarith
  linarith

/-- CONDITIONAL ON both Dusart bounds: a square-free `m ≤ exp(exp 32.73)` has
`Ω m ≤ e^29.3`. -/
theorem bigOmega_le_of_sqfree (hD : LeanLab.Common.ThetaWindow.DusartThm52k2) (hP : DusartPi11)
    {m : ℕ} (hm : 0 < m) (hsq : Squarefree m) (hmX : (m : ℝ) ≤ Real.exp (Real.exp 32.73)) :
    (bigOmega m : ℝ) ≤ Real.exp 29.3 := by
  have hlog : Real.log m < Chebyshev.theta X0 := by
    have : Real.log m ≤ Real.exp 32.73 := by
      calc Real.log m ≤ Real.log (Real.exp (Real.exp 32.73)) :=
            Real.log_le_log (by exact_mod_cast hm) hmX
        _ = Real.exp 32.73 := Real.log_exp _
    linarith [theta_X0 hD]
  have hX0 : 0 ≤ X0 := by have := X0_ge; linarith
  rw [bigOmega_eq_card_of_squarefree hm hsq]
  have := card_primeFactors_le hm hX0 hlog
  calc ((m.primeFactors.card : ℕ) : ℝ) ≤ ((Nat.primeCounting ⌊X0⌋₊ : ℕ) : ℝ) := by
        exact_mod_cast this
    _ ≤ Real.exp 29.3 := pi_X0 hP

/-- BJS Theorem 5 at the corrected threshold. CONDITIONAL ON: the Chen form at `exp(exp 32.73)`,
Dudek's theorem, Dusart Theorem 5.2 k = 2 and Dusart's `π(x) ≤ x/(ln x − 1.1)`. So the printed
`e^29.3` survives F-0023. -/
theorem bjs_thm5_of_3273
    (h3273 : ∀ N : ℕ, Even N → Real.exp (Real.exp 32.73) < N → PrimePlusAlmostPrime 2 N)
    (hDu : DudekSqfree) (hD : LeanLab.Common.ThetaWindow.DusartThm52k2) (hP : DusartPi11) :
    ∀ N : ℕ, Even N → 4 ≤ N → ∃ k : ℕ, (k : ℝ) ≤ Real.exp 29.3 ∧ PrimePlusAlmostPrime k N := by
  intro N hE hN
  by_cases hbig : Real.exp (Real.exp 32.73) < N
  · refine ⟨2, ?_, h3273 N hE hbig⟩
    have : (2 : ℝ) ≤ 1 + 29.3 := by norm_num
    have := Real.add_one_le_exp 29.3
    push_cast; linarith
  · push Not at hbig
    obtain ⟨p, m, hp, hm, hsq, hNpm⟩ := hDu N (by omega)
    refine ⟨bigOmega m, ?_, ⟨p, m, hp, hm, hNpm, le_rfl⟩⟩
    apply bigOmega_le_of_sqfree hD hP hm hsq
    have : (m : ℝ) ≤ N := by exact_mod_cast (by omega : m ≤ N)
    linarith

end LeanLab.AlmostPrimes.Thm5
