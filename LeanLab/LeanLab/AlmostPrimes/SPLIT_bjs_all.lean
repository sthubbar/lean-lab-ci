/-
Split of `bjs_all` into leaves.

The whole statement is cut at the corrected Chen threshold `Real.exp (Real.exp 32.73)`:

* below the threshold the small case uses the square-free remainder input (`N = p + m` with `m`
  square-free) and the counting estimate which turns `m ≤ exp (exp 32.73)` into
  `Ω m ≤ exp 29.3` for a square-free `m`: there the number of prime factors with multiplicity
  equals the number of distinct prime factors, and the distinct count is bounded by the count of
  primes below a short window above `exp 32.73`;
* above the threshold the large case is `bjs_chen_3273`, which gives `Ω ≤ 2` and hence the
  constant `k = 2`, with `2 ≤ exp 29.3`.

The leaves below are the two open steps of the small case, plus the multiplicity identity linking
them. Each is strictly weaker than `bjs_all`: the first is restricted to one range and asserts no
factor bound, the second is an estimate about one integer with no prime decomposition in it, the
third is a multiplicity identity for square-free integers.

AI-written Lean code. Checked only by the Lean kernel.
-/
import LeanLab.AlmostPrimes.Statements
import LeanLab.ChebyshevExplicit.PiUpperSharp


namespace LeanLab.AlmostPrimes

/-! ### Counting input for LEAF 2

The `16 j` threshold comes from Chebyshev's explicit `1.1062` prime-counting bound
(`LeanLab.ChebyshevExplicit.pi_le_11062_sharp`): `π (16 j) < j` for `j ≥ 10^9`, so the
`j`-th smallest prime factor of a square-free-free `m` with `j ≥ 10^9` distinct prime
factors exceeds `16 j`, and peeling the largest gives `∏_{i = 10^9}^{j} (16 i) ≤ m`.
`log` of that with `log j! ≥ j log j - j` beats `exp 32.73` once `j > exp 29.3`.
The `xlogx_mono` proof is the lab's (`LeanLab.AlmostPrimes.NoDusart.xlogx_mono`), inlined. -/

private theorem log_sixteen_ge : (2.7725 : ℝ) ≤ Real.log 16 := by
  rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
  push_cast
  nlinarith [Real.log_two_gt_d9]

private theorem log_sixteen_e9_ge : (23 : ℝ) ≤ Real.log (16 * 10 ^ 9) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h1 : Real.exp 23 ≤ (2.7182818286 : ℝ) ^ 23 := by
    rw [show Real.exp 23 = (Real.exp 1) ^ 23 by rw [← Real.exp_nat_mul]; norm_num]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 23
  have h2 : (2.7182818286 : ℝ) ^ 23 < 1.6e10 := by norm_num
  have h3 : (16 : ℝ) * 10 ^ 9 = 1.6e10 := by norm_num
  linarith

private theorem log_e293_ge : (1.9e11 : ℝ) ≤ Real.exp 29.3 := by
  have h1 : Real.exp 26 ≤ Real.exp 29.3 := Real.exp_le_exp.2 (by norm_num)
  have h2 : (2.7182818283 : ℝ) ^ 26 ≤ Real.exp 26 := by
    rw [show Real.exp 26 = (Real.exp 1) ^ 26 by rw [← Real.exp_nat_mul]; norm_num]
    exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 26
  have h3 : (1.9e11 : ℝ) ≤ (2.7182818283 : ℝ) ^ 26 := by norm_num
  linarith

private theorem exp_343_le : Real.exp 3.43 ≤ 30.89 := by
  have hexp043 : Real.exp 0.43 ≤ 1.5374 := by
    have h := Real.exp_bound (x := 0.43) (by norm_num [abs_of_pos]) (n := 6) (by norm_num)
    rw [abs_le] at h
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
    norm_num [abs_of_pos] at h
    linarith [h.2]
  have h3 : Real.exp 3 ≤ (2.7182818286 : ℝ) ^ 3 := by
    rw [show Real.exp 3 = (Real.exp 1) ^ 3 by rw [← Real.exp_nat_mul]; norm_num]
    exact pow_le_pow_left₀ (Real.exp_pos 1).le Real.exp_one_lt_d9.le 3
  have hsplit : Real.exp 3.43 = Real.exp 3 * Real.exp 0.43 := by
    rw [← Real.exp_add]; norm_num
  rw [hsplit]
  have hp : (0 : ℝ) ≤ Real.exp 0.43 := (Real.exp_pos _).le
  calc Real.exp 3 * Real.exp 0.43 ≤ (2.7182818286 : ℝ) ^ 3 * 1.5374 :=
        mul_le_mul h3 hexp043 hp (by positivity)
    _ ≤ 30.89 := by norm_num

private theorem exp_twenty_one_ge : (1e9 : ℝ) ≤ Real.exp 21 := by
  have h1 : (2.7182818283 : ℝ) ^ 21 ≤ Real.exp 21 := by
    rw [show Real.exp 21 = (Real.exp 1) ^ 21 by rw [← Real.exp_nat_mul]; norm_num]
    exact pow_le_pow_left₀ (by norm_num) Real.exp_one_gt_d9.le 21
  have h2 : (1e9 : ℝ) ≤ (2.7182818283 : ℝ) ^ 21 := by norm_num
  linarith

private theorem log_e9m1_le : Real.log (((10 ^ 9 : ℕ) - 1 : ℕ) : ℝ) ≤ 21 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : (((10 ^ 9 : ℕ) - 1 : ℕ) : ℝ) ≤ 1e9 := by push_cast; norm_num
  exact le_trans h1 exp_twenty_one_ge

/-! ### The prime count at `16 j` -/

private theorem pi_sixteen_mul_lt (j : ℕ) (hj : 10 ^ 9 ≤ j) :
    (Nat.primeCounting (16 * j) : ℝ) < (j : ℝ) := by
  have hj4 : 4 ≤ 16 * j := by omega
  have h := LeanLab.ChebyshevExplicit.pi_le_11062_sharp (16 * j) hj4
  have hjR : (10 ^ 9 : ℝ) ≤ (j : ℝ) := by exact_mod_cast hj
  have hcast : ((16 * j : ℕ) : ℝ) = 16 * (j : ℝ) := by push_cast; ring
  set L := Real.log ((16 * j : ℕ) : ℝ) with hL
  have hL23 : (23 : ℝ) ≤ L := by
    rw [hL, hcast]
    refine le_trans log_sixteen_e9_ge (Real.log_le_log (by norm_num) (by linarith))
  have hLpos : (0 : ℝ) < L := by linarith
  have hjpos : (0 : ℝ) < (j : ℝ) := by linarith
  have hLsq : (529 : ℝ) ≤ L ^ 2 := by nlinarith [hL23]
  have hsqrtj : Real.sqrt (j : ℝ) ≤ (j : ℝ) / 31622 := by
    have h31622 : (31622 : ℝ) ^ 2 ≤ (j : ℝ) := by nlinarith [hjR]
    have hin : (j : ℝ) ≤ ((j : ℝ) / 31622) ^ 2 := by
      rw [div_pow, le_div_iff₀ (by norm_num : (0 : ℝ) < (31622 : ℝ) ^ 2)]
      nlinarith [hjpos, h31622]
    exact (Real.sqrt_le_left (by positivity)).mpr hin
  have hsqrt16 : Real.sqrt ((16 * j : ℕ) : ℝ) = 4 * Real.sqrt (j : ℝ) := by
    rw [hcast, Real.sqrt_mul (by norm_num)]
    rw [show Real.sqrt (16 : ℝ) = 4 by
      rw [show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
  set S := Real.sqrt ((16 * j : ℕ) : ℝ) with hS
  have hS_nonneg : (0 : ℝ) ≤ S := Real.sqrt_nonneg _
  have hlog2sq : (0.48039 : ℝ) ≤ Real.log 2 ^ 2 := by nlinarith [Real.log_two_gt_d9]
  have h1 : 1.1062 * ((16 * j : ℕ) : ℝ) / L ≤ 0.775 * (j : ℝ) := by
    rw [hcast, div_le_iff₀ hLpos]
    nlinarith [hL23, hjpos]
  have h2 : 4.4248 * ((16 * j : ℕ) : ℝ) / L ^ 2 ≤ 0.135 * (j : ℝ) := by
    rw [hcast, div_le_iff₀ (by positivity : (0 : ℝ) < L ^ 2)]
    nlinarith [hLsq, hjpos]
  have h3 : 1.1062 * S / Real.log 2 ^ 2 ≤ 0.0003 * (j : ℝ) := by
    rw [hsqrt16, div_le_iff₀ (by positivity : (0 : ℝ) < Real.log 2 ^ 2)]
    nlinarith [hsqrtj, hlog2sq, hjpos, Real.sqrt_nonneg (j : ℝ)]
  have hlog_sqrt : L ≤ 8 * Real.sqrt (j : ℝ) := by
    have h2' := Real.log_le_rpow_div (x := ((16 * j : ℕ) : ℝ)) (by positivity) (ε := (1 : ℝ) / 2)
      (by norm_num)
    have e1 : ((16 * j : ℕ) : ℝ) ^ ((1 : ℝ) / 2) = Real.sqrt ((16 * j : ℕ) : ℝ) := by
      rw [Real.sqrt_eq_rpow]
    rw [e1] at h2'
    have e2 : Real.sqrt ((16 * j : ℕ) : ℝ) / (1 / 2) = 2 * Real.sqrt ((16 * j : ℕ) : ℝ) := by ring
    rw [e2] at h2'
    rw [← hL] at h2'
    rw [← hS] at h2'
    rw [hsqrt16] at h2'
    linarith
  have h45 : 4 * L + 160 / Real.log 2 - 2 * Real.log 2 ≤ 0.0012 * (j : ℝ) := by
    have hlog2p : (0 : ℝ) < Real.log 2 := by linarith [Real.log_two_gt_d9]
    have h160 : 160 / Real.log 2 ≤ 231 := by
      rw [div_le_iff₀ hlog2p]
      nlinarith [Real.log_two_gt_d9]
    have hlog2pos : 0 ≤ 2 * Real.log 2 := by linarith [Real.log_two_gt_d9]
    nlinarith [hlog_sqrt, hsqrtj, hjR, h160, hlog2pos]
  linarith [h, h1, h2, h3, h45]

/-! ### Peeling the largest prime factor -/

private theorem prod_Icc_le_prod_of_prime (S : Finset ℕ) (hP : ∀ p ∈ S, p.Prime)
    (hcard : 10 ^ 9 ≤ S.card) :
    (∏ j ∈ Finset.Icc (10 ^ 9) S.card, ((16 * j : ℕ) : ℝ)) ≤ ∏ p ∈ S, (p : ℝ) := by
  induction S using Finset.strongInduction with
  | H S ih =>
    rcases S.eq_empty_or_nonempty with h | hne
    · rw [h] at hcard; simp at hcard
    set k := S.card with hk
    set M := S.max' hne with hM
    have hMS : M ∈ S := S.max'_mem hne
    have hMprime : M.Prime := hP M hMS
    have h16k : 16 * k < M := by
      by_contra hcon
      push Not at hcon
      have hsub : S ⊆ Nat.primesLE (16 * k) := by
        intro p hp
        rw [Nat.mem_primesLE]
        exact ⟨le_trans (S.le_max' p hp) hcon, hP p hp⟩
      have h1 : S.card ≤ (Nat.primesLE (16 * k)).card := Finset.card_le_card hsub
      rw [Nat.primesLE_card_eq_primeCounting] at h1
      have h2 : (Nat.primeCounting (16 * k) : ℝ) < (k : ℝ) := pi_sixteen_mul_lt k hcard
      have h3 : (k : ℝ) ≤ (Nat.primeCounting (16 * k) : ℝ) := by exact_mod_cast h1
      linarith
    have hk1 : 1 ≤ k := by have := hcard; omega
    have h16kM : (16 : ℝ) * (k : ℝ) ≤ (M : ℝ) := by
      have : 16 * k + 1 ≤ M := h16k
      have : ((16 * k + 1 : ℕ) : ℝ) ≤ (M : ℝ) := by exact_mod_cast this
      push_cast at this
      linarith
    have herase : (S.erase M).card = k - 1 := by
      rw [Finset.card_erase_of_mem hMS, hk]
    have hprodS : (∏ p ∈ S, (p : ℝ)) = (∏ p ∈ S.erase M, (p : ℝ)) * (M : ℝ) :=
      (Finset.prod_erase_mul S (fun p => (p : ℝ)) hMS).symm
    have hprodErase_nonneg : (0 : ℝ) ≤ ∏ p ∈ S.erase M, (p : ℝ) :=
      Finset.prod_nonneg (fun p _ => by positivity)
    have hIcc_split : (∏ j ∈ Finset.Icc (10 ^ 9) k, ((16 * j : ℕ) : ℝ))
        = (∏ j ∈ Finset.Icc (10 ^ 9) (k - 1), ((16 * j : ℕ) : ℝ)) * (16 * (k : ℝ)) := by
      have hstep := Finset.prod_Icc_succ_top (a := 10 ^ 9) (b := k - 1) (by omega)
        (fun j : ℕ => ((16 * j : ℕ) : ℝ))
      have hk' : k - 1 + 1 = k := by omega
      rw [hk'] at hstep
      rw [hstep]
      push_cast
      ring
    rcases Nat.lt_or_ge (S.erase M).card (10 ^ 9) with hlt | hge
    · -- then k = 10^9
      have hk1e9 : k = 10 ^ 9 := by omega
      have hIk : Finset.Icc (10 ^ 9) k = {10 ^ 9} := by
        rw [hk1e9, Finset.Icc_self]
      rw [hIk, Finset.prod_singleton, hprodS]
      have h16k' : 16 * (10 ^ 9 : ℕ) < M := by omega
      have h16 : ((16 * (10 ^ 9) : ℕ) : ℝ) ≤ (M : ℝ) := by
        have h' : ((16 * (10 ^ 9 : ℕ) : ℕ) : ℝ) ≤ ((M : ℕ) : ℝ) := by
          exact_mod_cast Nat.le_of_lt h16k'
        push_cast at h' ⊢
        linarith
      refine le_trans h16 ?_
      have hN : 1 ≤ ∏ p ∈ S.erase M, p := by
        refine Nat.one_le_iff_ne_zero.mpr ?_
        refine Finset.prod_ne_zero_iff.mpr ?_
        intro p hp hzero
        exact (hP p (Finset.mem_of_mem_erase hp)).ne_zero hzero
      have h1 : (1 : ℝ) ≤ ∏ p ∈ S.erase M, (p : ℝ) := by
        have : ((1 : ℕ) : ℝ) ≤ ((∏ p ∈ S.erase M, p : ℕ) : ℝ) := by exact_mod_cast hN
        simpa using this
      have hMpos : (0 : ℝ) < (M : ℝ) := by
        have : (2 : ℝ) ≤ (M : ℝ) := by exact_mod_cast hMprime.two_le
        linarith
      calc (M : ℝ) = (M : ℝ) * 1 := by ring
        _ ≤ (M : ℝ) * (∏ p ∈ S.erase M, (p : ℝ)) :=
            mul_le_mul_of_nonneg_left h1 hMpos.le
        _ = (∏ p ∈ S.erase M, (p : ℝ)) * (M : ℝ) := by ring
    · -- induction step
      have hih := ih (S.erase M) (Finset.erase_ssubset hMS)
        (fun p hp => hP p (Finset.mem_of_mem_erase hp)) hge
      rw [herase] at hih
      rw [hprodS, hIcc_split]
      have h16k'' : ((16 * (k : ℕ) : ℕ) : ℝ) = 16 * (k : ℝ) := by push_cast; ring
      have hstep2 : (∏ j ∈ Finset.Icc (10 ^ 9) (k - 1), ((16 * j : ℕ) : ℝ)) * (16 * (k : ℝ))
          ≤ (∏ p ∈ S.erase M, (p : ℝ)) * (M : ℝ) := by
        have hnn : (0 : ℝ) ≤ ∏ j ∈ Finset.Icc (10 ^ 9) (k - 1), ((16 * j : ℕ) : ℝ) :=
          Finset.prod_nonneg (fun j _ => by positivity)
        have h16k3 : (16 : ℝ) * (k : ℝ) ≤ (M : ℝ) := h16kM
        nlinarith [hih, hprodErase_nonneg, hnn, h16k3]
      linarith [hstep2]

private theorem xlogx_mono {t K : ℝ} (hK1 : 1 ≤ K) (htK : K ≤ t) :
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

/-- LEAF 1 of 3, the square-free remainder step on the small range: an even `N ≥ 4` that does not
exceed `exp (exp 32.73)` splits as a prime plus a positive square-free integer. This is the
Dudek-type remainder input; it asserts no bound on the number of prime factors of the
remainder. -/
theorem leaf_squarefree_remainder (N : ℕ) (hEven : Even N) (hN : 4 ≤ N)
    (hsmall : (N : ℝ) ≤ Real.exp (Real.exp 32.73)) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m := by
  sorry

/-- LEAF 2 of 3, the counting estimate of the small range: a positive integer below
`exp (exp 32.73)` has at most `exp 29.3` distinct prime factors. The constant is the one obtained
by counting the primes in a window just above `exp 32.73`; it is the step that fixes `29.3`. -/
theorem leaf_card_primeFactors_le_exp (m : ℕ) (hm : 0 < m)
    (hmX : (m : ℝ) ≤ Real.exp (Real.exp 32.73)) :
    ((m.primeFactors.card : ℕ) : ℝ) ≤ Real.exp 29.3 := by
  by_contra hcon
  push Not at hcon
  set k := m.primeFactors.card with hk
  set x := Real.exp 29.3 with hx
  clear_value k x
  have hxk : x < (k : ℝ) := hcon
  have hxpos : (0 : ℝ) < x := by rw [hx]; exact Real.exp_pos _
  have hxbig : (1.9e11 : ℝ) ≤ x := hx ▸ log_e293_ge
  have hkpos : (0 : ℝ) < (k : ℝ) := lt_trans hxpos hxk
  have hkbig : 10 ^ 9 ≤ k := by
    have h1 : (10 ^ 9 : ℝ) < (k : ℝ) := lt_of_le_of_lt (le_trans (by norm_num) hxbig) hxk
    have h2 : 10 ^ 9 < k := by exact_mod_cast h1
    omega
  have hprod : (∏ j ∈ Finset.Icc (10 ^ 9) k, ((16 * j : ℕ) : ℝ))
      ≤ ∏ p ∈ m.primeFactors, (p : ℝ) := by
    have h := prod_Icc_le_prod_of_prime m.primeFactors
      (fun p hp => Nat.prime_of_mem_primeFactors hp) (by rw [← hk]; exact hkbig)
    simpa [hk] using h
  have hprodp : (0 : ℝ) < ∏ j ∈ Finset.Icc (10 ^ 9) k, ((16 * j : ℕ) : ℝ) := by
    refine Finset.prod_pos (fun j hj => ?_)
    have hj1 : (0 : ℕ) < j := by have := (Finset.mem_Icc.mp hj).1; omega
    have hj1' : (0 : ℝ) < (j : ℝ) := by exact_mod_cast hj1
    have hc : ((16 * j : ℕ) : ℝ) = 16 * (j : ℝ) := by push_cast; ring
    rw [hc]
    positivity
  have hSp : (0 : ℝ) < ∏ p ∈ m.primeFactors, (p : ℝ) :=
    Finset.prod_pos (fun p hp => by
      have hp' := Nat.prime_of_mem_primeFactors hp
      exact_mod_cast hp'.pos)
  have hSle : ∏ p ∈ m.primeFactors, (p : ℝ) ≤ (m : ℝ) := by
    have hd : (∏ p ∈ m.primeFactors, p) ∣ m := Nat.prod_primeFactors_dvd m
    have hle : (∏ p ∈ m.primeFactors, p) ≤ m := Nat.le_of_dvd hm hd
    have h' : ((∏ p ∈ m.primeFactors, p : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hle
    simpa using h'
  have hlog1 : Real.log (∏ j ∈ Finset.Icc (10 ^ 9) k, ((16 * j : ℕ) : ℝ)) ≤ Real.log (m : ℝ) :=
    Real.log_le_log hprodp (le_trans hprod hSle)
  have hlogprod : Real.log (∏ j ∈ Finset.Icc (10 ^ 9) k, ((16 * j : ℕ) : ℝ))
      = ∑ j ∈ Finset.Icc (10 ^ 9) k, Real.log (16 * (j : ℝ)) := by
    have hlog := Real.log_prod (s := Finset.Icc (10 ^ 9) k)
      (f := fun j : ℕ => ((16 * j : ℕ) : ℝ))
      (fun j hj => by
        have hj1 : (0 : ℕ) < j := by have := (Finset.mem_Icc.mp hj).1; omega
        have hc : ((16 * j : ℕ) : ℝ) = 16 * (j : ℝ) := by push_cast; ring
        rw [hc]
        positivity)
    rw [hlog]
    refine Finset.sum_congr rfl ?_
    intro j hj
    push_cast
    ring
  have hlogsplit : ∑ j ∈ Finset.Icc (10 ^ 9) k, Real.log (16 * (j : ℝ))
      = ((k : ℝ) - 10 ^ 9 + 1) * Real.log 16 + ∑ j ∈ Finset.Icc (10 ^ 9) k, Real.log (j : ℝ) := by
    have hpt : ∀ j ∈ Finset.Icc (10 ^ 9) k, Real.log (16 * (j : ℝ)) = Real.log 16 + Real.log (j : ℝ) := by
      intro j hj
      have hj1 : 10 ^ 9 ≤ j := (Finset.mem_Icc.mp hj).1
      have hj0 : (0 : ℝ) < (j : ℝ) := by
        have : (0 : ℕ) < j := by omega
        exact_mod_cast this
      rw [Real.log_mul (by norm_num) hj0.ne']
    rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const, Nat.card_Icc,
      nsmul_eq_mul]
    have hle : 10 ^ 9 ≤ k + 1 := by omega
    have hcast : ((k + 1 - 10 ^ 9 : ℕ) : ℝ) = (k : ℝ) - 10 ^ 9 + 1 := by
      rw [Nat.cast_sub hle]
      push_cast
      ring
    rw [hcast]
  have hfackey : Real.log (k.factorial : ℝ)
      = ∑ j ∈ Finset.Ioc (0 : ℕ) (10 ^ 9 - 1), Real.log (j : ℝ)
        + ∑ j ∈ Finset.Icc (10 ^ 9) k, Real.log (j : ℝ) := by
    rw [← Real.sum_log_eq_log_factorial (N := k)]
    have hunion : Finset.Ioc (0 : ℕ) k = Finset.Ioc (0 : ℕ) (10 ^ 9 - 1) ∪ Finset.Icc (10 ^ 9) k := by
      ext j
      simp only [Finset.mem_Ioc, Finset.mem_Icc, Finset.mem_union]
      omega
    rw [hunion, Finset.sum_union]
    exact Finset.disjoint_left.mpr (fun a ha hb => by
      simp only [Finset.mem_Ioc, Finset.mem_Icc] at ha hb
      omega)
  have hstir : (k : ℝ) * Real.log (k : ℝ) - (k : ℝ) ≤ Real.log (k.factorial : ℝ) := by
    have := Real.le_sum_log_nat (N := k)
    rwa [Real.sum_log_eq_log_factorial] at this
  have htail : ∑ j ∈ Finset.Ioc (0 : ℕ) (10 ^ 9 - 1), Real.log (j : ℝ) ≤ 10 ^ 9 * 21 := by
    have hpts : ∀ j ∈ Finset.Ioc (0 : ℕ) (10 ^ 9 - 1), Real.log (j : ℝ) ≤ 21 := by
      intro j hj
      have hj1 : 1 ≤ j := (Finset.mem_Ioc.mp hj).1
      have hj2 : j ≤ 10 ^ 9 - 1 := (Finset.mem_Ioc.mp hj).2
      refine le_trans ?_ log_e9m1_le
      exact Real.log_le_log (by exact_mod_cast hj1) (by exact_mod_cast hj2)
    calc ∑ j ∈ Finset.Ioc (0 : ℕ) (10 ^ 9 - 1), Real.log (j : ℝ)
        ≤ ∑ j ∈ Finset.Ioc (0 : ℕ) (10 ^ 9 - 1), (21 : ℝ) := Finset.sum_le_sum hpts
      _ = ((Finset.Ioc (0 : ℕ) (10 ^ 9 - 1)).card : ℝ) * 21 := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ 10 ^ 9 * 21 := by
          have hc : (Finset.Ioc (0 : ℕ) (10 ^ 9 - 1)).card ≤ 10 ^ 9 := by
            rw [Nat.card_Ioc]
            omega
          have hc' : ((Finset.Ioc (0 : ℕ) (10 ^ 9 - 1)).card : ℝ) ≤ 10 ^ 9 := by exact_mod_cast hc
          linarith
  have hB : (∑ j ∈ Finset.Icc (10 ^ 9) k, Real.log (j : ℝ))
      ≥ Real.log (k.factorial : ℝ) - 10 ^ 9 * 21 := by linarith
  have hmain : Real.log (m : ℝ)
      ≥ ((k : ℝ) - 10 ^ 9 + 1) * Real.log 16 + (Real.log (k.factorial : ℝ) - 10 ^ 9 * 21) := by
    rw [hlogprod, hlogsplit] at hlog1
    linarith
  have hmain2 : ((k : ℝ) - 10 ^ 9 + 1) * Real.log 16 + (Real.log (k.factorial : ℝ) - 10 ^ 9 * 21)
      ≥ ((k : ℝ) - 10 ^ 9 + 1) * Real.log 16 + ((k : ℝ) * Real.log (k : ℝ) - (k : ℝ)) - 10 ^ 9 * 21 := by
    linarith
  have hlogk : (29.3 : ℝ) ≤ Real.log (k : ℝ) := by
    have h1 : Real.log x ≤ Real.log (k : ℝ) := Real.log_le_log hxpos hxk.le
    rwa [hx, Real.log_exp] at h1
  have hxx : x * 29.3 - x ≤ (k : ℝ) * Real.log (k : ℝ) - (k : ℝ) := by
    have hf := xlogx_mono (K := x) (t := (k : ℝ)) (by linarith [hxbig]) hxk.le
    have hxlog : Real.log x = 29.3 := by rw [hx, Real.log_exp]
    rwa [hxlog] at hf
  have hA : (x - 10 ^ 9 + 1) * 2.7725 ≤ ((k : ℝ) - 10 ^ 9 + 1) * Real.log 16 := by
    have hp : (0 : ℝ) ≤ x - 10 ^ 9 + 1 := by nlinarith [hxbig]
    have hk' : x - 10 ^ 9 + 1 ≤ (k : ℝ) - 10 ^ 9 + 1 := by linarith
    calc (x - 10 ^ 9 + 1) * 2.7725 ≤ (x - 10 ^ 9 + 1) * Real.log 16 :=
          mul_le_mul_of_nonneg_left log_sixteen_ge hp
      _ ≤ ((k : ℝ) - 10 ^ 9 + 1) * Real.log 16 :=
          mul_le_mul_of_nonneg_right hk' (by linarith [log_sixteen_ge])
  have hexp32 : Real.exp 32.73 ≤ x * 30.89 := by
    rw [hx, show (32.73 : ℝ) = 29.3 + 3.43 by norm_num, Real.exp_add]
    exact mul_le_mul_of_nonneg_left exp_343_le (Real.exp_pos 29.3).le
  have hlow : Real.exp 32.73 < (x - 10 ^ 9 + 1) * 2.7725 + (x * 29.3 - x - 10 ^ 9 * 21) := by
    nlinarith [hxbig, hexp32]
  have hlogm : Real.log (m : ℝ) ≤ Real.exp 32.73 := by
    have h1 : Real.log (m : ℝ) ≤ Real.log (Real.exp (Real.exp 32.73)) :=
      Real.log_le_log (by exact_mod_cast hm) hmX
    rwa [Real.log_exp] at h1
  linarith

/-- LEAF 3 of 3, the multiplicity identity used to pass from the distinct prime factors to
`bigOmega`: for a positive square-free integer the number of prime factors counted with
multiplicity is the number of distinct prime factors. -/
theorem leaf_bigOmega_eq_card_of_squarefree (m : ℕ) (hm : 0 < m) (hsq : Squarefree m) :
    bigOmega m = m.primeFactors.card := by
  have hnd : m.primeFactorsList.Nodup :=
    (Nat.squarefree_iff_nodup_primeFactorsList hm.ne').1 hsq
  unfold bigOmega
  exact (List.toFinset_card_of_nodup hnd).symm

/-- `bjs_all` assembled from the three leaves: the small case below `exp (exp 32.73)` runs through
`LEAF 1` and `LEAF 2` with `k = bigOmega m = m.primeFactors.card`, and the large case takes
`k = 2` from `bjs_chen_3273`. -/
theorem bjs_all_split :
    ∀ N : ℕ, Even N → 4 ≤ N → ∃ k : ℕ, (k : ℝ) ≤ Real.exp 29.3 ∧ PrimePlusAlmostPrime k N := by
  intro N hEven hN
  by_cases hsmall : (N : ℝ) ≤ Real.exp (Real.exp 32.73)
  · obtain ⟨p, m, hp, hm, hsq, hNpm⟩ := leaf_squarefree_remainder N hEven hN hsmall
    refine ⟨bigOmega m, ?_, p, m, hp, hm, hNpm, le_rfl⟩
    rw [leaf_bigOmega_eq_card_of_squarefree m hm hsq]
    refine leaf_card_primeFactors_le_exp m hm (le_trans ?_ hsmall)
    exact_mod_cast (by omega : m ≤ N)
  · refine ⟨2, ?_, bjs_chen_3273 N hEven (not_le.mp hsmall)⟩
    have h := Real.add_one_le_exp 29.3
    push_cast
    linarith

end LeanLab.AlmostPrimes

#print axioms LeanLab.AlmostPrimes.bjs_all_split
