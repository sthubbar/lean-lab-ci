import LeanLab.AlmostPrimes.DudekFrom4e18

/-!
# BJS Theorem 5 without the Dusart inputs, at `e^29.4`

Unit U-5655, CLOUD 20261019T1515Z-cloud27. AI wrote the Lean code. KNOWN mathematics.

BJS Theorem 5 bounds `Ω(m)` for the square-free `m ≤ exp(exp 32.73)` left by Dudek's theorem, and
the lab's `Thm5.bigOmega_le_of_sqfree` takes two Dusart bounds for that step, to reach `e^29.3`.
The trivial bound does almost as well: `k` distinct primes have product at least `(k + 1)!`, so
`log m ≥ (k + 1) log(k + 1) - (k + 1)`, and `log m ≤ e^32.73` forces `k ≤ e^29.4`, because
`e^29.4 · 28.4 > e^32.73`, that is `e^3.33 < 28.4`.

* `omega_le_of_log`: square-free `m ≥ 1` with `log m ≤ e^32.73` has `Ω(m) ≤ e^29.4`, no cited input.
* `bjs_thm5_294`: every even `N ≥ 4` is `p + m` with `Ω(m) ≤ e^29.4`, CONDITIONAL ON the Chen form
  at `exp(exp 32.73)` and the even Goldbach check to `4·10¹⁸` only. Dudek 2017 and both Dusart
  bounds are no longer inputs; the price is `e^29.3 → e^29.4`.
-/

open Real Finset

noncomputable section

namespace LeanLab.AlmostPrimes.NoDusart

open LeanLab.AlmostPrimes LeanLab.AlmostPrimes.Thm5

/-- A finite set of naturals `≥ 2` with `k` elements has product at least `(k + 1)!`. -/
lemma factorial_le_prod (S : Finset ℕ) (hS : ∀ x ∈ S, 2 ≤ x) :
    (S.card + 1).factorial ≤ ∏ x ∈ S, x := by
  induction S using Finset.strongInduction with
  | H S ih =>
  rcases S.eq_empty_or_nonempty with h | hne
  · subst h; simp
  set a := S.max' hne with ha
  have haS : a ∈ S := S.max'_mem hne
  set T := S.erase a with hT
  have hTcard : T.card + 1 = S.card := Finset.card_erase_add_one haS
  have hTsub : T ⊂ S := Finset.erase_ssubset haS
  have ihT := ih T hTsub (fun x hx => hS x (Finset.mem_of_mem_erase hx))
  -- `S ⊆ [2, a]`, so `card S ≤ a - 1`
  have hsub : S ⊆ Icc 2 a := by
    intro x hx; rw [mem_Icc]; exact ⟨hS x hx, S.le_max' x hx⟩
  have hcard : S.card ≤ a - 1 := by
    have := card_le_card hsub; simp at this; omega
  have ha2 : 2 ≤ a := hS a haS
  rw [← Finset.mul_prod_erase S (fun x => x) haS, ← hTcard, Nat.factorial_succ]
  apply Nat.mul_le_mul (by omega) ihT

/-- `t log t - t ≥ K log K - K` for `t ≥ K ≥ 1`. -/
lemma xlogx_mono {t K : ℝ} (hK1 : 1 ≤ K) (htK : K ≤ t) :
    K * Real.log K - K ≤ t * Real.log t - t := by
  have hK : 0 < K := by linarith
  have ht : 0 < t := lt_of_lt_of_le hK htK
  have hlK0 : 0 ≤ Real.log K := Real.log_nonneg hK1
  have hprod : 0 ≤ (t - K) * Real.log K := mul_nonneg (by linarith) hlK0
  have h1 : 1 - K / t ≤ Real.log (t / K) := by
    have := Real.one_sub_inv_le_log_of_pos (x := t / K) (by positivity)
    rwa [inv_div] at this
  rw [Real.log_div ht.ne' hK.ne'] at h1
  have hlogK : Real.log K ≤ Real.log t := Real.log_le_log hK htK
  have h2 : t * (1 - K / t) = t - K := by field_simp
  have h3 : t * (1 - K / t) ≤ t * (Real.log t - Real.log K) := mul_le_mul_of_nonneg_left h1 ht.le
  nlinarith

/-- `e^3.33 < 28.4`, from `e^10 ≤ 2.7182818286^10 < 28.4³`. -/
lemma exp333_lt : exp 3.33 < 28.4 := by
  have h10 : exp 10 ≤ (2.7182818286 : ℝ) ^ 10 := by
    have := Real.exp_nat_mul 1 10
    rw [mul_one] at this
    rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, this]
    exact pow_le_pow_left₀ (exp_pos 1).le Real.exp_one_lt_d9.le 10
  have hc : exp (10 / 3) ^ 3 = exp 10 := by
    rw [← Real.exp_nat_mul]; norm_num
  have h3 : exp (10 / 3) < 28.4 := by
    by_contra h
    push Not at h
    have : (28.4 : ℝ) ^ 3 ≤ exp (10 / 3) ^ 3 := pow_le_pow_left₀ (by norm_num) h 3
    rw [hc] at this
    have : (28.4 : ℝ) ^ 3 ≤ (2.7182818286 : ℝ) ^ 10 := this.trans h10
    norm_num at this
  calc exp 3.33 ≤ exp (10 / 3) := Real.exp_le_exp.mpr (by norm_num)
    _ < 28.4 := h3

/-- **`Ω` of a square-free `m` with `log m ≤ e^32.73` is at most `e^29.4`, no cited input.** -/
theorem omega_le_of_log {m : ℕ} (hm : 0 < m) (hsq : Squarefree m)
    (hlog : Real.log m ≤ exp 32.73) : (bigOmega m : ℝ) ≤ exp 29.4 := by
  rw [bigOmega_eq_card_of_squarefree hm hsq]
  set k := m.primeFactors.card
  by_contra hk
  push Not at hk
  -- `(k + 1)! ≤ m`
  have hprod : (k + 1).factorial ≤ m := by
    have h1 := factorial_le_prod m.primeFactors (fun p hp => (Nat.prime_of_mem_primeFactors hp).two_le)
    have h2 : ∏ p ∈ m.primeFactors, p ≤ m :=
      Nat.le_of_dvd hm (Nat.prod_primeFactors_dvd m)
    exact h1.trans h2
  have hfac : ((k + 1 : ℕ) : ℝ) * Real.log ((k + 1 : ℕ) : ℝ) - ((k + 1 : ℕ) : ℝ) ≤ Real.log m := by
    have hs := Real.le_sum_log_nat (N := k + 1)
    rw [Real.sum_log_eq_log_factorial] at hs
    refine hs.trans (Real.log_le_log (by positivity) ?_)
    exact_mod_cast hprod
  set K := exp 29.4 with hKdef
  have hK0 : 0 < K := exp_pos _
  have hKt : K ≤ ((k + 1 : ℕ) : ℝ) := by push_cast; linarith
  have hK1 : 1 ≤ K := by rw [hKdef]; exact Real.one_le_exp (by norm_num)
  have hmono := xlogx_mono hK1 hKt
  have hlogK : Real.log K = 29.4 := Real.log_exp _
  rw [hlogK] at hmono
  -- `K · 28.4 > e^32.73`
  have hsplit : exp 32.73 = K * exp 3.33 := by rw [hKdef, ← Real.exp_add]; norm_num
  have h333 := exp333_lt
  have : exp 32.73 < K * 28.4 := by rw [hsplit]; exact mul_lt_mul_of_pos_left h333 hK0
  linarith

/-- **BJS Theorem 5 at `e^29.4`, CONDITIONAL ON the Chen form at `exp(exp 32.73)` and the even
Goldbach check to `4·10¹⁸` only.** Every even `N ≥ 4` is `p + m` with `Ω(m) ≤ e^29.4`. -/
theorem bjs_thm5_294
    (h3273 : ∀ N : ℕ, Even N → Real.exp (Real.exp 32.73) < N → PrimePlusAlmostPrime 2 N)
    (hG : LeanLab.EvenGoldbachUpTo (4 * 10 ^ 18)) :
    ∀ N : ℕ, Even N → 4 ≤ N → ∃ k : ℕ, (k : ℝ) ≤ Real.exp 29.4 ∧ PrimePlusAlmostPrime k N := by
  intro N hE hN
  by_cases hbig : Real.exp (Real.exp 32.73) < N
  · refine ⟨2, ?_, h3273 N hE hbig⟩
    have := Real.add_one_le_exp 29.4
    push_cast; linarith
  · push Not at hbig
    obtain ⟨p, m, hp, hm, hsq, hNpm⟩ := DudekFrom4e18.dudek_even_of_4e18 hG N hE hN
    refine ⟨bigOmega m, ?_, ⟨p, m, hp, hm, hNpm, le_rfl⟩⟩
    apply omega_le_of_log hm hsq
    have hmN : (m : ℝ) ≤ N := by exact_mod_cast (by omega : m ≤ N)
    calc Real.log m ≤ Real.log (Real.exp (Real.exp 32.73)) :=
          Real.log_le_log (by exact_mod_cast hm) (hmN.trans hbig)
      _ = Real.exp 32.73 := Real.log_exp _

end LeanLab.AlmostPrimes.NoDusart
