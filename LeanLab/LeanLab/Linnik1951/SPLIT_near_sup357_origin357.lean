/-
Split of the phase-zero pointwise supremum bound `near_sup357_origin357` into four
smaller steps. Nothing here changes the statement: `near_sup357_origin357_split`
repeats it character for character and proves it from the four OPEN leaves below,
which record, in order, (1) the size of the damped character prime sum restricted to
the short range where the damping weight is not yet negligible, (2) the smallness of
the complementary range, where the exponential damping alone already bounds the sum
by an absolute constant, (3) the exact splitting of the phase-zero sum into those two
ranges, and (4) the elementary lower bound of the weight N over q times log N to the
fifth. The assembly does not use `near_sup357_origin357`.
-/
import LeanLab.Linnik1951.SPLIT_near_positive_sup357

namespace LeanLab.Linnik1951

/-! ### Private helpers for the leaves

Elementary estimates on the damped prime weight `exp (-(p / N))` and on the geometric series
it is compared with. Nothing here uses more character information than `‖χ a‖ ≤ 1`. -/

/-- The damped weight at a prime is bounded by the geometric weight `exp (-(1/N)) ^ p`. -/
private lemma near_sup357_origin_norm_damped_le {N : ℕ} (hN : 1 ≤ N) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (p : Nat.Primes) :
    ‖χ (p : ℕ) * (Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ))) : ℂ)‖ ≤
      Real.exp (-(1 / (N : ℝ))) ^ (p : ℕ) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  have hpow : Real.exp (-(1 / (N : ℝ))) ^ (p : ℕ) =
      Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ))) := by
    rw [← Real.exp_nat_mul]
    congr 1
    field_simp
  rw [hpow, norm_mul, Complex.norm_of_nonneg (Real.exp_pos _).le]
  have hχ : ‖χ (p : ℕ)‖ ≤ 1 := DirichletCharacter.norm_le_one χ (((p : ℕ)) : ZMod q)
  calc ‖χ (p : ℕ)‖ * Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))
      ≤ 1 * Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ))) :=
        mul_le_mul_of_nonneg_right hχ (Real.exp_pos _).le
    _ = Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ))) := one_mul _

/-- The damped character prime sum is summable: it is dominated termwise by a geometric
series of ratio `exp (-(1/N)) < 1`. -/
private lemma near_sup357_origin_summable_damped {N : ℕ} (hN : 1 ≤ N) {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    Summable (fun p : Nat.Primes =>
      χ (p : ℕ) * (Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ))) : ℂ)) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hρlt : ‖Real.exp (-(1 / (N : ℝ)))‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff]
    have : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    linarith
  exact Summable.of_norm_bounded
    ((summable_geometric_of_norm_lt_one hρlt).subtype (fun n : ℕ => n.Prime))
    (fun p => near_sup357_origin_norm_damped_le hN χ p)

/-- Any one-sided cut of the damped character prime sum is summable, for the same reason. -/
private lemma near_sup357_origin_summable_cut {N : ℕ} (hN : 1 ≤ N) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (c : Nat.Primes → Prop) [DecidablePred c] :
    Summable (fun p : Nat.Primes =>
      if c p then χ (p : ℕ) * (Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ))) : ℂ) else 0) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hρlt : ‖Real.exp (-(1 / (N : ℝ)))‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff]
    have : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    linarith
  refine Summable.of_norm_bounded
    ((summable_geometric_of_norm_lt_one hρlt).subtype (fun n : ℕ => n.Prime)) (fun p => ?_)
  split_ifs with h
  · exact near_sup357_origin_norm_damped_le hN χ p
  · rw [norm_zero]
    exact pow_nonneg (Real.exp_pos _).le _

/-- The complementary cut, written with the zero in the first branch. -/
private lemma near_sup357_origin_summable_compl {N : ℕ} (hN : 1 ≤ N) {q : ℕ}
    (χ : DirichletCharacter ℂ q) (c : Nat.Primes → Prop) [DecidablePred c] :
    Summable (fun p : Nat.Primes =>
      if c p then 0 else χ (p : ℕ) * (Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ))) : ℂ)) := by
  have hρlt : ‖Real.exp (-(1 / (N : ℝ)))‖ < 1 := by
    rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_lt_one_iff]
    have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
    have : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    linarith
  refine Summable.of_norm_bounded
    ((summable_geometric_of_norm_lt_one hρlt).subtype (fun n : ℕ => n.Prime)) (fun p => ?_)
  split_ifs with h
  · rw [norm_zero]
    exact pow_nonneg (Real.exp_pos _).le _
  · exact near_sup357_origin_norm_damped_le hN χ p

/-- Writing `-(a / b)` as `(-a) / b` under the exponential, to match the shape used by
`characterPrime280`. -/
private lemma near_sup357_origin_exp_damped_eq (N p : ℕ) :
    Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ))) = Real.exp ((-(((p : ℕ) : ℝ))) / (N : ℝ)) := by
  rw [neg_div]

/-- `exp (-(1/N)) ^ p` is the damped weight at `p`. -/
private lemma near_sup357_origin_rho_pow {N : ℕ} (hN : 1 ≤ N) (n : ℕ) :
    Real.exp (-(1 / (N : ℝ))) ^ n = Real.exp (-(((n : ℕ) : ℝ) / (N : ℝ))) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNne : (N : ℝ) ≠ 0 := ne_of_gt hNpos
  rw [← Real.exp_nat_mul]
  congr 1
  field_simp


/-- LEAF. Step 1 of 4: the short range at phase zero. There is a fixed positive
constant C such that for every large N, every modulus q with 1 at most q at most N to
the one seventh, and every nonprincipal character mod q, the squared norm of the
damped character prime sum, cut down to the primes p at most N log N, is at most C
times N over q times log N to the fifth. All of the character information sits in
this step; the range is short enough that the bound can be read off from the partial
sums of the character over primes, and no prime beyond N log N is involved. -/
theorem near_sup357_origin_short357 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ) else 0)‖ ^ 2 ≤
            C * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := by
  sorry

/-- LEAF. Step 2 of 4: the complementary range carries no character information. For
N at least three, any modulus and any character mod it, the damped character prime sum
over the primes p beyond N log N has norm at most 2. Each summand has norm at most the
real weight exp of minus p over N, and the sum of those weights beyond N log N is at
most 1 because exp of minus log N is 1 over N; the factor 2 leaves room for the
comparison with the integral of the decreasing weight. No cancellation and no
arithmetic input is used. -/
theorem near_sup357_origin_tail357 (N : ℕ) (hN : 3 ≤ N) {q : ℕ}
    (χ : DirichletCharacter ℂ q) :
    ‖∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                (0 : ℂ) else χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ))‖ ≤ 2 := by
  have hN1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  set M : ℝ := (N : ℝ) * Real.log N with hMdef
  set ρ : ℝ := Real.exp (-(1 / (N : ℝ))) with hρdef
  have hρpos : 0 < ρ := by rw [hρdef]; exact Real.exp_pos _
  have hρlt1 : ρ < 1 := by
    rw [hρdef, Real.exp_lt_one_iff]
    have : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    linarith
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    have : (0 : ℝ) ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN1)
    positivity
  have hgeom : Summable (fun n : ℕ => ρ ^ n) := by
    refine summable_geometric_of_norm_lt_one ?_
    rwa [Real.norm_of_nonneg hρpos.le]
  have hgeomP : Summable (fun p : Nat.Primes => ρ ^ (p : ℕ)) :=
    hgeom.subtype (fun n : ℕ => n.Prime)
  -- the summand is dominated by the geometric weight
  have hb : ∀ p : Nat.Primes,
      ‖(if ((p : ℕ) : ℝ) ≤ M then (0 : ℂ) else
        χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ))‖ ≤ ρ ^ (p : ℕ) := by
    intro p
    split_ifs with h
    · rw [norm_zero]
      exact pow_nonneg hρpos.le _
    · rw [hρdef]
      exact near_sup357_origin_norm_damped_le hN1 χ p
  have hF : Summable (fun p : Nat.Primes =>
      (if ((p : ℕ) : ℝ) ≤ M then (0 : ℂ) else
        χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ))) :=
    Summable.of_norm_bounded hgeomP hb
  -- summability of the geometric tail with the integer cut
  have hg : Summable (fun n : ℕ => if Nat.floor M + 1 ≤ n then ρ ^ n else 0) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hgeom
    · split_ifs with h
      · exact pow_nonneg hρpos.le n
      · exact le_rfl
    · split_ifs with h
      · exact le_rfl
      · exact pow_nonneg hρpos.le n
  -- termwise comparison after turning the prime sum into an integer sum
  have hstep1 : ∑' p : Nat.Primes,
      ‖(if ((p : ℕ) : ℝ) ≤ M then (0 : ℂ) else
        χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ))‖ ≤
      ∑' p : Nat.Primes, (if ((p : ℕ) : ℝ) ≤ M then (0 : ℝ) else ρ ^ (p : ℕ)) := by
    refine Summable.tsum_le_tsum (fun p => ?_) hF.norm ?_
    · split_ifs with h
      · simp
      · simpa only [if_neg h] using hb p
    · refine Summable.of_nonneg_of_le (fun p => ?_) (fun p => ?_) hgeomP
      · split_ifs with h
        · exact le_rfl
        · exact pow_nonneg hρpos.le _
      · split_ifs with h
        · exact pow_nonneg hρpos.le _
        · exact le_rfl
  have hsub : (∑' p : Nat.Primes, (if ((p : ℕ) : ℝ) ≤ M then (0 : ℝ) else ρ ^ (p : ℕ))) =
      ∑' n : ℕ, (if n.Prime then (if (n : ℝ) ≤ M then (0 : ℝ) else ρ ^ n) else 0) :=
    Nat.Primes.tsum_eq_tsum_ite (f := fun n : ℕ => if (n : ℝ) ≤ M then (0 : ℝ) else ρ ^ n)
  have hite : Summable (fun n : ℕ =>
      if n.Prime then (if (n : ℝ) ≤ M then (0 : ℝ) else ρ ^ n) else 0) := by
    refine Summable.of_nonneg_of_le (fun n => ?_) (fun n => ?_) hgeom
    · by_cases hnp : n.Prime
      · rw [if_pos hnp]
        by_cases hn : (n : ℝ) ≤ M
        · rw [if_pos hn]
        · rw [if_neg hn]
          exact pow_nonneg hρpos.le n
      · rw [if_neg hnp]
    · by_cases hnp : n.Prime
      · rw [if_pos hnp]
        by_cases hn : (n : ℝ) ≤ M
        · rw [if_pos hn]
          exact pow_nonneg hρpos.le n
        · rw [if_neg hn]
      · rw [if_neg hnp]
        exact pow_nonneg hρpos.le n
  have hstep2 : ∑' p : Nat.Primes, (if ((p : ℕ) : ℝ) ≤ M then (0 : ℝ) else ρ ^ (p : ℕ)) ≤
      ∑' n : ℕ, (if Nat.floor M + 1 ≤ n then ρ ^ n else 0) := by
    rw [hsub]
    refine Summable.tsum_le_tsum (fun n => ?_) hite hg
    by_cases hnp : n.Prime
    · rw [if_pos hnp]
      by_cases hn : (n : ℝ) ≤ M
      · rw [if_pos hn]
        split_ifs with hk
        · exact pow_nonneg hρpos.le n
        · exact le_rfl
      · rw [if_neg hn]
        have hk : Nat.floor M + 1 ≤ n := by
          have hlt : Nat.floor M < n := (Nat.floor_lt hM0).mpr (lt_of_not_ge hn)
          omega
        rw [if_pos hk]
    · rw [if_neg hnp]
      split_ifs with hk
      · exact pow_nonneg hρpos.le n
      · exact le_rfl
  -- value of the geometric tail
  have hgeomsum : ∑' n : ℕ, ρ ^ n = (1 - ρ)⁻¹ :=
    tsum_geometric_of_norm_lt_one (by rwa [Real.norm_of_nonneg hρpos.le])
  have hsplit := hg.sum_add_tsum_nat_add (Nat.floor M + 1)
  have hzero : ∑ i ∈ Finset.range (Nat.floor M + 1),
      (if Nat.floor M + 1 ≤ i then ρ ^ i else 0) = 0 := by
    refine Finset.sum_eq_zero (fun i hi => ?_)
    rw [Finset.mem_range] at hi
    rw [if_neg (by omega)]
  have hval : ∑' n : ℕ, (if Nat.floor M + 1 ≤ n then ρ ^ n else 0) = ρ ^ (Nat.floor M + 1) * (1 - ρ)⁻¹ := by
    rw [← hsplit, hzero, zero_add]
    have hstep : (∑' i : ℕ, (if Nat.floor M + 1 ≤ i + (Nat.floor M + 1) then
        ρ ^ (i + (Nat.floor M + 1)) else 0)) = ∑' i : ℕ, ρ ^ (i + (Nat.floor M + 1)) :=
      tsum_congr (fun i => if_pos (by omega))
    rw [hstep]
    have hstep2 : (∑' i : ℕ, ρ ^ (i + (Nat.floor M + 1))) =
        ∑' i : ℕ, ρ ^ i * ρ ^ (Nat.floor M + 1) :=
      tsum_congr (fun i => pow_add ρ i (Nat.floor M + 1))
    rw [hstep2, tsum_mul_right, hgeomsum, mul_comm]
  -- numerical bound for the tail
  have hMk : M < ((Nat.floor M + 1 : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one M
    push_cast
    linarith
  have hρpow : ρ ^ (Nat.floor M + 1) = Real.exp (-(((Nat.floor M + 1 : ℕ) : ℝ) / (N : ℝ))) := by
    rw [hρdef]
    exact near_sup357_origin_rho_pow hN1 (Nat.floor M + 1)
  have hlog3 : (1 : ℝ) ≤ Real.log N := by
    have h3 : Real.log 3 ≤ Real.log N := Real.log_le_log (by norm_num) (by exact_mod_cast hN)
    have he1 : (1 : ℝ) ≤ Real.log 3 := by
      have h := Real.log_le_log (Real.exp_pos 1) (le_of_lt Real.exp_one_lt_three)
      rwa [Real.log_exp] at h
    linarith
  have hρk : ρ ^ (Nat.floor M + 1) ≤ 1 / (N : ℝ) := by
    rw [hρpow]
    have hquot : Real.log N < ((Nat.floor M + 1 : ℕ) : ℝ) / (N : ℝ) := by
      rw [lt_div_iff₀ hNpos, mul_comm]
      exact hMk
    have hmono : -(((Nat.floor M + 1 : ℕ) : ℝ) / (N : ℝ)) ≤ -(Real.log N) := by linarith
    calc Real.exp (-(((Nat.floor M + 1 : ℕ) : ℝ) / (N : ℝ))) ≤ Real.exp (-(Real.log N)) :=
          (Real.exp_le_exp).mpr hmono
      _ = 1 / (N : ℝ) := by
          rw [Real.exp_neg, Real.exp_log hNpos]
          ring
  have hρle : ρ ≤ (N : ℝ) / ((N : ℝ) + 1) := by
    have ht : (0 : ℝ) < 1 / (N : ℝ) := by positivity
    have hexp1 : 1 + 1 / (N : ℝ) ≤ Real.exp (1 / (N : ℝ)) := by
      have := Real.add_one_le_exp (1 / (N : ℝ))
      linarith
    have hρinv : ρ = (Real.exp (1 / (N : ℝ)))⁻¹ := by
      rw [hρdef, ← Real.exp_neg]
    have hp : (0 : ℝ) < 1 + 1 / (N : ℝ) := by positivity
    rw [hρinv]
    calc (Real.exp (1 / (N : ℝ)))⁻¹ ≤ (1 + 1 / (N : ℝ))⁻¹ :=
          (inv_le_inv₀ (Real.exp_pos _) hp).mpr hexp1
      _ = (N : ℝ) / ((N : ℝ) + 1) := by
          field_simp
          try ring
  have hone : 1 / ((N : ℝ) + 1) ≤ 1 - ρ := by
    have hN1p : (0 : ℝ) < (N : ℝ) + 1 := by positivity
    have hfrac : (N : ℝ) / ((N : ℝ) + 1) = 1 - 1 / ((N : ℝ) + 1) := by
      field_simp
      try ring
    linarith [hρle]
  have hden : 0 < 1 - ρ := by linarith
  have hinv : (1 - ρ)⁻¹ ≤ (N : ℝ) + 1 := by
    calc (1 - ρ)⁻¹ ≤ (1 / ((N : ℝ) + 1))⁻¹ :=
          (inv_le_inv₀ hden (by positivity)).mpr hone
      _ = (N : ℝ) + 1 := by
          field_simp
  have hfinal : (1 - ρ)⁻¹ * ρ ^ (Nat.floor M + 1) ≤ 2 := by
    have h1 : (1 - ρ)⁻¹ * ρ ^ (Nat.floor M + 1) ≤ ((N : ℝ) + 1) * (1 / (N : ℝ)) :=
      mul_le_mul hinv hρk (pow_nonneg hρpos.le _) (by positivity)
    have h2 : ((N : ℝ) + 1) * (1 / (N : ℝ)) = 1 + 1 / (N : ℝ) := by
      field_simp
    have h3 : 1 / (N : ℝ) ≤ 1 := by
      rw [div_le_one hNpos]
      exact_mod_cast hN1
    linarith
  calc ‖∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ M then
                (0 : ℂ) else χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ))‖
      ≤ ∑' p : Nat.Primes,
              ‖(if ((p : ℕ) : ℝ) ≤ M then
                (0 : ℂ) else χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ))‖ :=
        norm_tsum_le_tsum_norm hF.norm
    _ ≤ ∑' p : Nat.Primes, (if ((p : ℕ) : ℝ) ≤ M then (0 : ℝ) else ρ ^ (p : ℕ)) := hstep1
    _ ≤ ∑' n : ℕ, (if Nat.floor M + 1 ≤ n then ρ ^ n else 0) := hstep2
    _ = ρ ^ (Nat.floor M + 1) * (1 - ρ)⁻¹ := hval
    _ = (1 - ρ)⁻¹ * ρ ^ (Nat.floor M + 1) := by ring
    _ ≤ 2 := hfinal

/-- LEAF. Step 3 of 4: the splitting identity at phase zero. For N at least one, any
modulus and any character mod it, the value of the damped character prime sum at phase
zero is the sum of its two ranges, the primes p at most N log N and the primes p
beyond N log N. At phase zero the oscillating factor is 1, and the two ranges are the
two complementary branches of the same indicator, so the single sum over all primes is
the sum of the two pieces. -/
theorem near_sup357_origin_split357 {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ)
    (hN : 1 ≤ N) :
    characterPrime280 χ N 0 = ∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ) else 0) + ∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                (0 : ℂ) else χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ)) := by
  have hA : Summable (fun p : Nat.Primes =>
      if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
        χ (p : ℕ) * (Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ))) : ℂ) else 0) :=
    near_sup357_origin_summable_cut (N := N) hN χ
      (fun p : Nat.Primes => ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N)
  have hB : Summable (fun p : Nat.Primes =>
      if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then 0 else
        χ (p : ℕ) * (Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ))) : ℂ)) :=
    near_sup357_origin_summable_compl (N := N) hN χ
      (fun p : Nat.Primes => ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N)
  calc characterPrime280 χ N 0
      = ∑' p : Nat.Primes,
          (χ (p : ℕ) * (Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ))) : ℂ)) := by
        unfold characterPrime280
        apply tsum_congr
        intro p
        simp only [near_sup357_origin_exp_damped_eq]
        simp
    _ = ∑' p : Nat.Primes,
          ((if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
              χ (p : ℕ) * (Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ))) : ℂ) else 0) +
            (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then 0 else
              χ (p : ℕ) * (Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ))) : ℂ))) :=
        tsum_congr (fun p => by split_ifs <;> simp)
    _ = (∑' p : Nat.Primes,
            (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
              χ (p : ℕ) * (Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ))) : ℂ) else 0)) +
          (∑' p : Nat.Primes,
            (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then 0 else
              χ (p : ℕ) * (Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ))) : ℂ))) :=
        Summable.tsum_add hA hB

/-- LEAF. Step 4 of 4: the weight is at least one. For N at least three, every modulus
q with 1 at most q at most N to the one seventh satisfies 1 at most N over q times log
N to the fifth. The hypotheses give log N at least 1 and N over q at least N to the six
sevenths, which is at least 1, so the product is at least 1. This is what lets the
assembly trade the absolute constant 8 of step 2 for the same weight that the other
terms carry. -/
theorem near_sup357_origin_weight_one357 {N : ℕ} (hN : 3 ≤ N) {q : ℕ} (hq : 1 ≤ q)
    (hqt : (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ)) :
    (1 : ℝ) ≤ (N : ℝ) / (q : ℝ) * Real.log N ^ 5 := by
  have hNr : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast (by omega : 1 ≤ N)
  have hqr : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hlog1 : (1 : ℝ) ≤ Real.log N := by
    have h3 : Real.log 3 ≤ Real.log N :=
      Real.log_le_log (by norm_num) (by exact_mod_cast hN)
    have he1 : (1 : ℝ) ≤ Real.log 3 := by
      have h := Real.log_le_log (Real.exp_pos 1) (le_of_lt Real.exp_one_lt_three)
      rwa [Real.log_exp] at h
    linarith
  have hpow : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) := by
    calc (1 : ℝ) = (1 : ℝ) ^ (1 / 7 : ℝ) := by simp
      _ ≤ (N : ℝ) ^ (1 / 7 : ℝ) :=
        Real.rpow_le_rpow zero_le_one hNr (by norm_num)
  have hqN : (q : ℝ) ≤ (N : ℝ) := by
    refine le_trans hqt ?_
    exact Real.rpow_le_self_of_one_le hNr (by norm_num)
  have hdiv : (1 : ℝ) ≤ (N : ℝ) / (q : ℝ) := (one_le_div hqr).mpr hqN
  have hlog5 : (1 : ℝ) ≤ Real.log N ^ 5 := one_le_pow₀ hlog1
  have h := mul_le_mul hdiv hlog5 (by norm_num : (0 : ℝ) ≤ 1) (le_trans (by norm_num : (0 : ℝ) ≤ 1) hdiv)
  simpa using h


/-- Private helper for the assembly: the squared norm of a sum of two vectors is at
most twice the sum of the squared norms. -/
private lemma near_sup357_origin_norm_add_sq357 (a b : ℂ) :
    ‖a + b‖ ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
  have h1 : ‖a + b‖ ≤ ‖a‖ + ‖b‖ := norm_add_le a b
  have h2 : ‖a + b‖ ^ 2 ≤ (‖a‖ + ‖b‖) ^ 2 :=
    pow_le_pow_left₀ (norm_nonneg _) h1 2
  have h3 : (‖a‖ + ‖b‖) ^ 2 ≤ 2 * ‖a‖ ^ 2 + 2 * ‖b‖ ^ 2 := by
    nlinarith [sq_nonneg (‖a‖ - ‖b‖)]
  linarith

/-- Private helper for the assembly: with a nonnegative constant and a weight at least
one, twice C times the weight plus twice the constant 4 of the tail step is at most the
constant 2 C plus 8 applied to the weight. -/
private lemma near_sup357_origin_absorb357 (C W : ℝ) (hC : 0 ≤ C) (hW : 1 ≤ W) :
    2 * (C * W) + 2 * 4 ≤ (2 * C + 8) * W := by
  nlinarith [hC, hW]

/-- Assembly of `near_sup357_origin357` from the four leaves above: split the value at
phase zero into the short range and its complement, bound the short range by step 1 and
the complement by the absolute constant of step 2, use step 4 to replace that constant
by the weight, and collect 2 C plus 8 as the new constant. No step uses
`near_sup357_origin357` itself. -/
theorem near_sup357_origin357_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          ‖characterPrime280 χ N 0‖ ^ 2 ≤ C * (N : ℝ) / (q : ℝ) * Real.log N ^ 5 := by
  obtain ⟨C, hC, N0, hshort⟩ := near_sup357_origin_short357 hG
  refine ⟨2 * C + 8, by linarith, max N0 2, ?_⟩
  intro N hN q hq hqt χ hχ
  have hN2 : 2 < N := lt_of_le_of_lt (le_max_right _ _) hN
  have hN0N : N0 < N := lt_of_le_of_lt (le_max_left _ _) hN
  have hN3 : 3 ≤ N := hN2
  have hN1 : 1 ≤ N := by omega
  have hsplit := near_sup357_origin_split357 (χ := χ) (N := N) hN1
  have htail := near_sup357_origin_tail357 N hN3 χ
  have hshortN := hshort N hN0N q hq hqt χ hχ
  have htail2 : ‖∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                (0 : ℂ) else χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ))‖ ^ 2 ≤ 4 := by
    have h := pow_le_pow_left₀ (norm_nonneg _) htail 2
    have hpow : (2 : ℝ) ^ 2 = 4 := by norm_num
    rw [hpow] at h
    exact h
  have hW := near_sup357_origin_weight_one357 hN3 hq hqt
  have hC0 : (0 : ℝ) ≤ C := le_of_lt hC
  have htri := near_sup357_origin_norm_add_sq357 (∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ) else 0)) (∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                (0 : ℂ) else χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ)))
  have hWnn : (0 : ℝ) ≤ C * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) :=
    mul_nonneg hC0 (le_trans zero_le_one hW)
  have hmain : ‖∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ) else 0) + ∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                (0 : ℂ) else χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ))‖ ^ 2 ≤
      (2 * C + 8) * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := by
    have hbound : ‖∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ) else 0) + ∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                (0 : ℂ) else χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ))‖ ^ 2 ≤
        2 * (C * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5)) + 2 * 4 := by
      nlinarith [htri, hshortN, htail2]
    exact le_trans hbound (near_sup357_origin_absorb357 C
      ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) hC0 hW)
  calc ‖characterPrime280 χ N 0‖ ^ 2 = ‖∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ) else 0) + ∑' p : Nat.Primes,
              (if ((p : ℕ) : ℝ) ≤ (N : ℝ) * Real.log N then
                (0 : ℂ) else χ (p : ℕ) * ((Real.exp (-(((p : ℕ) : ℝ) / (N : ℝ)))) : ℂ))‖ ^ 2 := by rw [hsplit]
    _ ≤ (2 * C + 8) * ((N : ℝ) / (q : ℝ) * Real.log N ^ 5) := hmain
    _ = (2 * C + 8) * (N : ℝ) / (q : ℝ) * Real.log N ^ 5 := by ring

end LeanLab.Linnik1951
