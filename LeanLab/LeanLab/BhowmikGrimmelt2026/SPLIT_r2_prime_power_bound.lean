/-
Split of `r2_prime_power_bound` (`BhowmikGrimmelt2026/DecompJ1034.lean`).

The statement splits `r2 N = Σ_{a+b=N} Λ(a)Λ(b)` at an even `N` that is *not* a Goldbach sum.
Two facts carry the split:

* the pairs `(a, b)` in which both entries are prime contribute nothing, because there is no such
  pair at an `N` that is not a Goldbach sum — this is the only place the hypothesis
  `¬ IsGoldbachSum N` is used;
* what is left is carried by pairs whose first entry is not prime, and by pairs whose first entry
  is prime while the second is not. Each of those two masses is bounded by three quarters of the
  right-hand side; twice three quarters is the factor `3/2` of the statement.

Note on the exponent: REPAIRED 20261108 STATEFIX arch20261108T1030Z. The exponent was the literal
`1/2`, natural division with value 0, so the factor was 1. It is now the real one half, as in
`r2_prime_power_bound` of DecompJ1034, and leaves 2 and 3 carry the same real exponent. The assembly
does not depend on the exponent beyond the shape of the right hand side.
-/
import LeanLab.BhowmikGrimmelt2026.DecompJ1034

namespace LeanLab.BhowmikGrimmelt2026

/-! ## The three-way split of the antidiagonal sum -/

/-- `r2 N` is the sum of three parts over the same antidiagonal: the part where both entries are
prime, the part where the first entry is not prime, and the part where the first entry is prime and
the second is not. This is a pointwise case distinction on the two primality conditions, so it
holds for every `N` and needs no hypothesis. -/
private lemma r2_three_parts (N : ℕ) :
    r2 N =
      (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
        (if x.1.Prime ∧ x.2.Prime then
          ArithmeticFunction.vonMangoldt x.1 * ArithmeticFunction.vonMangoldt x.2 else 0))
      + (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
        (if ¬ x.1.Prime then
          ArithmeticFunction.vonMangoldt x.1 * ArithmeticFunction.vonMangoldt x.2 else 0))
      + (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
        (if x.1.Prime then
          (if ¬ x.2.Prime then
            ArithmeticFunction.vonMangoldt x.1 * ArithmeticFunction.vonMangoldt x.2 else 0)
          else 0)) := by
  unfold r2
  conv_rhs => rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro x _
  by_cases h1 : x.1.Prime <;> by_cases h2 : x.2.Prime <;> simp [h1, h2]

/-! ### A nonzero von Mangoldt value at a non-prime is a prime power of exponent at least two -/

private lemma vm_structure {a : ℕ} (h : ArithmeticFunction.vonMangoldt a ≠ 0) (ha : ¬ a.Prime) :
    ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ p ^ k = a := by
  obtain ⟨p, k, hp, hk, hpk⟩ :=
    isPrimePow_nat_iff a |>.mp (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h)
  have hk2 : 2 ≤ k := by
    rcases Nat.lt_or_ge k 2 with h2 | h2
    · have hk1 : k = 1 := by omega
      rw [hk1, pow_one] at hpk
      exact absurd (hpk ▸ hp) ha
    · exact h2
  exact ⟨p, k, hp, hk2, hpk⟩

/-- `Λ m ≤ log N` for `m ≤ N` and `1 ≤ N`. -/
private lemma vm_le_log {m N : ℕ} (hN : 1 ≤ N) (hm : m ≤ N) :
    ArithmeticFunction.vonMangoldt m ≤ Real.log (N : ℝ) := by
  rcases eq_or_ne m 0 with rfl | hm0
  · have h0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
      rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
      exact not_isPrimePow_zero
    rw [h0]
    exact Real.log_nonneg (by exact_mod_cast hN : (1:ℝ) ≤ (N:ℝ))
  · refine (ArithmeticFunction.vonMangoldt_le_log (n := m)).trans ?_
    have hmpos : (0:ℝ) < (m:ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hm0
    exact Real.log_le_log hmpos (by exact_mod_cast hm)

/-- At a non-prime `a ≤ N` with `Λ a ≠ 0` one has `Λ a ≤ log N / 2`, because `a = p^k`, `k ≥ 2`. -/
private lemma vm_half_le_log {a N : ℕ} (hN : 2 ≤ N) (haN : a ≤ N)
    (h : ArithmeticFunction.vonMangoldt a ≠ 0) (ha : ¬ a.Prime) :
    ArithmeticFunction.vonMangoldt a ≤ Real.log (N : ℝ) / 2 := by
  obtain ⟨p, k, hp, hk2, hpk⟩ := vm_structure h ha
  have hapos : (0:ℝ) < (a:ℝ) := by
    have h' : (0:ℕ) < a := (ArithmeticFunction.vonMangoldt_ne_zero_iff.mp h).pos
    exact_mod_cast h'
  have hk0 : k ≠ 0 := by omega
  have hΛ : ArithmeticFunction.vonMangoldt a = Real.log (p:ℝ) := by
    rw [← hpk, ArithmeticFunction.vonMangoldt_apply_pow hk0,
      ArithmeticFunction.vonMangoldt_apply_prime hp]
  have h2 : 2 * Real.log (p:ℝ) ≤ Real.log (N:ℝ) := by
    have hkR : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk2
    have hlp : 0 ≤ Real.log (p:ℝ) := Real.log_nonneg (by exact_mod_cast hp.one_le)
    have h1 : 2 * Real.log (p:ℝ) ≤ (k:ℝ) * Real.log (p:ℝ) := by nlinarith
    have h2' : (k:ℝ) * Real.log (p:ℝ) = Real.log ((p:ℝ)^k) := by
      rw [Real.log_pow]
    have h3 : Real.log ((p:ℝ)^k) = Real.log (a:ℝ) := by rw [← Nat.cast_pow, hpk]
    have h4 : Real.log (a:ℝ) ≤ Real.log (N:ℝ) :=
      Real.log_le_log hapos (by exact_mod_cast haN)
    linarith
  rw [hΛ]; linarith

/-! ### Counting the prime powers -/

/-- A finite set of primes `p` with `p ^ k ≤ N` has at most `N ^ (1/k)` elements (`k ≥ 1`). -/
private lemma card_primes_pow_le (N k : ℕ) (hk : 1 ≤ k) (s : Finset ℕ)
    (hprime : ∀ p ∈ s, p.Prime) (hpow : ∀ p ∈ s, p ^ k ≤ N) :
    ((s.card : ℝ)) ≤ (N : ℝ) ^ ((1 : ℝ) / k) := by
  have hx0 : (0:ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / k) := Real.rpow_nonneg (by positivity) _
  have hsub : s ⊆ Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1 : ℝ) / k))) := by
    intro p hp
    have hpp : p.Prime := hprime p hp
    refine Finset.mem_Icc.mpr ⟨hpp.one_le, ?_⟩
    refine Nat.le_floor ?_
    have hpk : (p:ℝ) ^ k ≤ (N:ℝ) := by exact_mod_cast hpow p hp
    have hp0 : (0:ℝ) ≤ (p:ℝ) := by positivity
    have hkey : (p:ℝ) = ((p:ℝ) ^ k) ^ ((1:ℝ) / k) := by
      rw [← Real.rpow_natCast (p:ℝ) k, ← Real.rpow_mul hp0]
      have hone : ((k:ℝ) * ((1:ℝ)/k)) = 1 := by field_simp
      rw [hone, Real.rpow_one]
    rw [hkey]
    exact Real.rpow_le_rpow (by positivity) hpk (by positivity)
  calc ((s.card : ℝ)) ≤ ((Finset.Icc 1 (Nat.floor ((N : ℝ) ^ ((1 : ℝ) / k)))).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ = ((Nat.floor ((N : ℝ) ^ ((1 : ℝ) / k))) : ℝ) := by
        rw [Nat.card_Icc]
        norm_num
    _ ≤ ((N : ℝ) ^ ((1 : ℝ) / k)) := Nat.floor_le hx0

/-- `N ^ (1/k) ≤ √N * (4/5)^(k-2)` for `k ≥ 2` as long as `2^k ≤ N`. -/
private lemma rpow_le_sqrt_mul (N k : ℕ) (hk : 2 ≤ k) (hNk : 2 ^ k ≤ N) :
    (N : ℝ) ^ ((1 : ℝ) / k) ≤ Real.sqrt (N : ℝ) * (4/5) ^ (k - 2) := by
  have hkR : (2:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hkpos : (0:ℝ) < (k:ℝ) := by linarith
  have hNpos : (0:ℝ) < (N:ℝ) := by
    have h2 : (0:ℕ) < N := lt_of_lt_of_le (by norm_num) hNk
    exact_mod_cast h2
  have hsplit : (N:ℝ) ^ ((1:ℝ)/k) = Real.sqrt (N:ℝ) * (N:ℝ) ^ ((1:ℝ)/k - (1:ℝ)/2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add hNpos]
    congr 1
    ring
  rw [hsplit]
  refine mul_le_mul_of_nonneg_left ?_ (Real.sqrt_nonneg _)
  have hc : ((1:ℝ)/k - (1:ℝ)/2) ≤ 0 := by
    have h1 : (1:ℝ)/(k:ℝ) ≤ (1:ℝ)/2 := by
      rw [div_le_div_iff₀ hkpos (by norm_num : (0:ℝ) < 2)]
      nlinarith
    linarith
  have hstep : (N:ℝ) ^ ((1:ℝ)/k - (1:ℝ)/2) ≤ ((2:ℝ)^k) ^ ((1:ℝ)/k - (1:ℝ)/2) := by
    refine Real.rpow_le_rpow_of_nonpos ?_ ?_ hc
    · positivity
    · exact_mod_cast hNk
  refine hstep.trans ?_
  have hbase : (2:ℝ) ^ (-((1:ℝ)/2)) ≤ 4/5 := by
    have hsqrt : ((2:ℝ) ^ (-((1:ℝ)/2))) = 1/Real.sqrt 2 := by
      rw [show (2:ℝ) ^ (-((1:ℝ)/2)) = ((2:ℝ) ^ ((1:ℝ)/2))⁻¹ from
        Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2) ((1:ℝ)/2), Real.sqrt_eq_rpow, inv_eq_one_div]
    rw [hsqrt, div_le_iff₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2))]
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  have hval : ((2:ℝ)^k) ^ ((1:ℝ)/k - (1:ℝ)/2) = ((2:ℝ)^(-((1:ℝ)/2))) ^ (k - 2) := by
    have l1 : ((2:ℝ)^k) ^ ((1:ℝ)/k - (1:ℝ)/2) = (2:ℝ) ^ ((1:ℝ) - (k:ℝ)/2) := by
      have s1 : ((2:ℝ)^k) ^ ((1:ℝ)/k - (1:ℝ)/2)
          = ((2:ℝ)^(k:ℝ)) ^ ((1:ℝ)/k - (1:ℝ)/2) := by
        rw [← Real.rpow_natCast (2:ℝ) k]
      rw [s1]
      have s2 : ((2:ℝ)^(k:ℝ)) ^ ((1:ℝ)/k - (1:ℝ)/2)
          = (2:ℝ) ^ ((k:ℝ) * ((1:ℝ)/k - (1:ℝ)/2)) :=
        (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) ((k:ℝ)) _).symm
      rw [s2]
      congr 1
      field_simp
    have l2 : ((2:ℝ)^(-((1:ℝ)/2))) ^ (k - 2) = (2:ℝ) ^ ((1:ℝ) - (k:ℝ)/2) := by
      have hcast : ((k - 2 : ℕ) : ℝ) = ((k:ℝ) - 2) := by simp [Nat.cast_sub hk]
      have s1 : ((2:ℝ)^(-((1:ℝ)/2))) ^ (k - 2)
          = ((2:ℝ)^(-((1:ℝ)/2))) ^ ((k:ℝ) - 2) := by
        rw [← Real.rpow_natCast ((2:ℝ)^(-((1:ℝ)/2))) (k - 2), hcast]
      rw [s1]
      have s2 : ((2:ℝ)^(-((1:ℝ)/2))) ^ ((k:ℝ) - 2)
          = (2:ℝ) ^ ((-((1:ℝ)/2)) * ((k:ℝ) - 2)) :=
        (Real.rpow_mul (by norm_num : (0:ℝ) ≤ 2) _ _).symm
      rw [s2]
      congr 1
      ring
    rw [l1, l2]
  rw [hval]
  have hfin : ((2:ℝ)^(-((1:ℝ)/2))) ^ (k - 2) ≤ (4/5:ℝ)^(k - 2) := by
    induction (k - 2) with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, pow_succ]
        exact mul_le_mul ih hbase (Real.rpow_nonneg (by norm_num : (0:ℝ) ≤ 2) _) (by positivity)
  exact hfin

/-! ### The mass bound -/

/-- The mass over pairs whose first entry is not prime is at most `(log N)^2/2` times the number of
non-prime prime powers below `N`. -/
private lemma mass_le_card (N : ℕ) (hN : 2 ≤ N) :
    (∑ a ∈ Finset.range (N+1),
        (if ¬ a.Prime then ArithmeticFunction.vonMangoldt a * ArithmeticFunction.vonMangoldt (N-a) else 0))
      ≤ Real.log (N : ℝ) * (Real.log (N : ℝ) / 2) *
          ((((Finset.range (N+1)).filter
            (fun a => ¬ a.Prime ∧ ArithmeticFunction.vonMangoldt a ≠ 0))).card : ℝ) := by
  classical
  set S := (Finset.range (N+1)).filter
    (fun a => ¬ a.Prime ∧ ArithmeticFunction.vonMangoldt a ≠ 0) with hS
  have hstep : (∑ a ∈ Finset.range (N+1),
        (if ¬ a.Prime then ArithmeticFunction.vonMangoldt a * ArithmeticFunction.vonMangoldt (N-a) else 0))
      = ∑ a ∈ S, ArithmeticFunction.vonMangoldt a * ArithmeticFunction.vonMangoldt (N-a) := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl ?_
    intro a _
    by_cases h1 : a.Prime
    · simp [h1]
    · by_cases h2 : ArithmeticFunction.vonMangoldt a = 0
      · simp [h1, h2]
      · simp [h1, h2]
  rw [hstep]
  have hbound : ∀ a ∈ S, ArithmeticFunction.vonMangoldt a * ArithmeticFunction.vonMangoldt (N-a)
      ≤ Real.log (N:ℝ) * (Real.log (N:ℝ) / 2) := by
    intro a ha
    simp only [hS, Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨haN, haNP, haΛ⟩ := ha
    have h1 : ArithmeticFunction.vonMangoldt a ≤ Real.log (N:ℝ) / 2 :=
      vm_half_le_log hN (by omega) haΛ haNP
    have h2 : ArithmeticFunction.vonMangoldt (N-a) ≤ Real.log (N:ℝ) :=
      vm_le_log (by omega) (by omega)
    have h4 : 0 ≤ ArithmeticFunction.vonMangoldt (N-a) := ArithmeticFunction.vonMangoldt_nonneg
    have h6 : 0 ≤ Real.log (N:ℝ) / 2 := by
      have h7 := Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N) : (1:ℝ) ≤ (N:ℝ))
      linarith
    calc ArithmeticFunction.vonMangoldt a * ArithmeticFunction.vonMangoldt (N-a)
        ≤ (Real.log (N:ℝ) / 2) * Real.log (N:ℝ) := mul_le_mul h1 h2 h4 h6
      _ = Real.log (N:ℝ) * (Real.log (N:ℝ) / 2) := by ring
  calc ∑ a ∈ S, ArithmeticFunction.vonMangoldt a * ArithmeticFunction.vonMangoldt (N-a)
      ≤ ∑ a ∈ S, (Real.log (N:ℝ) * (Real.log (N:ℝ) / 2)) := Finset.sum_le_sum hbound
    _ = Real.log (N:ℝ) * (Real.log (N:ℝ) / 2) * (S.card : ℝ) := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring

/-! ### A geometric bound -/

private lemma geom_range_le (m : ℕ) : ∑ i ∈ Finset.range m, (4/5:ℝ)^i ≤ 5 := by
  rcases Nat.eq_zero_or_pos m with hm | hm
  · subst hm
    simp
  · have hr : ((4/5:ℝ)) ≠ 1 := by norm_num
    rw [geom_sum_eq hr m]
    have h2 : ((4/5:ℝ)^m - 1) / ((4/5:ℝ) - 1) = (1 - (4/5:ℝ)^m) / (1 - 4/5) := by
      field_simp
      ring
    rw [h2, div_le_iff₀ (by norm_num : (0:ℝ) < 1 - 4/5)]
    have h3 := pow_nonneg (by norm_num : (0:ℝ) ≤ 4/5) m
    nlinarith

/-- The number of non-prime prime powers below `N` is at most `5 √N`. -/
private lemma card_S_le (N : ℕ) (hN : 4 ≤ N) :
    ((((Finset.range (N+1)).filter
        (fun a => ¬ a.Prime ∧ ArithmeticFunction.vonMangoldt a ≠ 0))).card : ℝ)
      ≤ 5 * (N:ℝ)^((1:ℝ)/2) := by
  classical
  set K := Nat.log 2 N with hK
  set Q : ℕ → Finset ℕ := fun k => (Finset.range (Nat.sqrt N + 1)).filter
    (fun p => p.Prime ∧ p ^ k ≤ N) with hQ
  have hK2 : 2 ≤ K := by
    rw [hK]
    exact Nat.le_log_of_pow_le (by norm_num) (by omega)
  have hsub : ((Finset.range (N+1)).filter
      (fun a => ¬ a.Prime ∧ ArithmeticFunction.vonMangoldt a ≠ 0))
      ⊆ (Finset.Icc 2 K).biUnion (fun k => (Q k).image (fun p => p ^ k)) := by
    intro a ha
    simp only [Finset.mem_filter, Finset.mem_range] at ha
    obtain ⟨haN, haNP, haΛ⟩ := ha
    obtain ⟨p, k, hp, hk2, hpk⟩ := vm_structure haΛ haNP
    have hpN : p ≤ Nat.sqrt N := by
      rw [Nat.le_sqrt]
      calc p * p = p ^ 2 := by ring
        _ ≤ p ^ k := Nat.pow_le_pow_right hp.pos hk2
        _ = a := hpk
        _ ≤ N := by omega
    have hkK : k ≤ K := by
      rw [hK]
      apply Nat.le_log_of_pow_le (by norm_num)
      calc 2 ^ k ≤ p ^ k := Nat.pow_le_pow_left hp.two_le k
        _ = a := hpk
        _ ≤ N := by omega
    refine Finset.mem_biUnion.mpr ⟨k, Finset.mem_Icc.mpr ⟨hk2, hkK⟩, ?_⟩
    exact Finset.mem_image.mpr
      ⟨p, Finset.mem_filter.mpr ⟨by simp [hpN], hp, by rw [hpk]; omega⟩, hpk⟩
  have hcard1 : (((Finset.range (N+1)).filter
      (fun a => ¬ a.Prime ∧ ArithmeticFunction.vonMangoldt a ≠ 0)).card)
      ≤ ∑ k ∈ Finset.Icc 2 K, (Q k).card := by
    refine le_trans (Finset.card_le_card hsub) ?_
    refine le_trans (Finset.card_biUnion_le) ?_
    exact Finset.sum_le_sum (fun k _ => Finset.card_image_le)
  have hcard2 : ((∑ k ∈ Finset.Icc 2 K, (Q k).card : ℕ) : ℝ)
      ≤ ∑ k ∈ Finset.Icc 2 K, (N:ℝ)^((1:ℝ)/k) := by
    rw [Nat.cast_sum]
    refine Finset.sum_le_sum ?_
    intro k hk
    obtain ⟨hk2, -⟩ := Finset.mem_Icc.mp hk
    exact card_primes_pow_le N k (by omega) (Q k)
      (fun p hp => (Finset.mem_filter.mp hp).2.1)
      (fun p hp => (Finset.mem_filter.mp hp).2.2)
  have hcard3 : ∑ k ∈ Finset.Icc 2 K, (N:ℝ)^((1:ℝ)/k)
      ≤ ∑ k ∈ Finset.Icc 2 K, (Real.sqrt (N:ℝ) * (4/5)^(k-2)) := by
    refine Finset.sum_le_sum ?_
    intro k hk
    obtain ⟨hk2, hkK⟩ := Finset.mem_Icc.mp hk
    have h2k : 2 ^ k ≤ N := by
      calc 2 ^ k ≤ 2 ^ K := Nat.pow_le_pow_right (by norm_num) hkK
        _ ≤ N := Nat.pow_log_le_self 2 (by omega)
    exact rpow_le_sqrt_mul N k hk2 h2k
  have hgeom : ∑ k ∈ Finset.Icc 2 K, (4/5:ℝ)^(k-2) ≤ 5 := by
    have hinj : Set.InjOn (fun k : ℕ => k - 2) ↑(Finset.Icc 2 K) := by
      intro x hx y hy hxy
      obtain ⟨hx2, hxK⟩ := Finset.mem_Icc.mp hx
      obtain ⟨hy2, hyK⟩ := Finset.mem_Icc.mp hy
      have hxy' : x - 2 = y - 2 := hxy
      omega
    have h1 : ∑ j ∈ (Finset.Icc 2 K).image (fun k => k - 2), (4/5:ℝ)^j
        = ∑ k ∈ Finset.Icc 2 K, (4/5:ℝ)^(k-2) := Finset.sum_image hinj
    rw [← h1]
    refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_) (geom_range_le (K-1))
    · intro j hj
      simp only [Finset.mem_image, Finset.mem_Icc, Finset.mem_range] at hj ⊢
      obtain ⟨k, ⟨hk2, hkK⟩, rfl⟩ := hj
      omega
    · intro j _ _; positivity
  have hcollapse : ∑ k ∈ Finset.Icc 2 K, (Real.sqrt (N:ℝ) * (4/5)^(k-2))
      = Real.sqrt (N:ℝ) * ∑ k ∈ Finset.Icc 2 K, (4/5:ℝ)^(k-2) := (Finset.mul_sum ..).symm
  have hcast : ((((Finset.range (N+1)).filter
      (fun a => ¬ a.Prime ∧ ArithmeticFunction.vonMangoldt a ≠ 0))).card : ℝ)
      ≤ ((∑ k ∈ Finset.Icc 2 K, (Q k).card : ℕ) : ℝ) := by
    exact_mod_cast hcard1
  refine le_trans hcast (le_trans hcard2 (le_trans hcard3 ?_))
  rw [hcollapse]
  calc Real.sqrt (N:ℝ) * ∑ k ∈ Finset.Icc 2 K, (4/5:ℝ)^(k-2)
      ≤ Real.sqrt (N:ℝ) * 5 := mul_le_mul_of_nonneg_left hgeom (Real.sqrt_nonneg _)
    _ = 5 * (N:ℝ)^((1:ℝ)/2) := by rw [Real.sqrt_eq_rpow]; ring

/-! ### Small `N` -/

private lemma goldbach_small (N : ℕ) (h63 : N ≤ 63) (hEven : Even N)
    (hG : ¬ IsGoldbachSum N) : N ≤ 2 := by
  obtain ⟨j, rfl⟩ := hEven
  have hj : j ≤ 31 := by omega
  interval_cases j <;> try omega
  all_goals (exfalso; first
    | exact hG ⟨2, 2, by decide, by decide, by omega⟩
    | exact hG ⟨3, 3, by decide, by decide, by omega⟩
    | exact hG ⟨3, 5, by decide, by decide, by omega⟩
    | exact hG ⟨3, 7, by decide, by decide, by omega⟩
    | exact hG ⟨5, 7, by decide, by decide, by omega⟩
    | exact hG ⟨3, 11, by decide, by decide, by omega⟩
    | exact hG ⟨3, 13, by decide, by decide, by omega⟩
    | exact hG ⟨5, 13, by decide, by decide, by omega⟩
    | exact hG ⟨3, 17, by decide, by decide, by omega⟩
    | exact hG ⟨3, 19, by decide, by decide, by omega⟩
    | exact hG ⟨5, 19, by decide, by decide, by omega⟩
    | exact hG ⟨3, 23, by decide, by decide, by omega⟩
    | exact hG ⟨5, 23, by decide, by decide, by omega⟩
    | exact hG ⟨7, 23, by decide, by decide, by omega⟩
    | exact hG ⟨3, 29, by decide, by decide, by omega⟩
    | exact hG ⟨3, 31, by decide, by decide, by omega⟩
    | exact hG ⟨5, 31, by decide, by decide, by omega⟩
    | exact hG ⟨7, 31, by decide, by decide, by omega⟩
    | exact hG ⟨3, 37, by decide, by decide, by omega⟩
    | exact hG ⟨5, 37, by decide, by decide, by omega⟩
    | exact hG ⟨3, 41, by decide, by decide, by omega⟩
    | exact hG ⟨3, 43, by decide, by decide, by omega⟩
    | exact hG ⟨5, 43, by decide, by decide, by omega⟩
    | exact hG ⟨3, 47, by decide, by decide, by omega⟩
    | exact hG ⟨5, 47, by decide, by decide, by omega⟩
    | exact hG ⟨7, 47, by decide, by decide, by omega⟩
    | exact hG ⟨3, 53, by decide, by decide, by omega⟩
    | exact hG ⟨5, 53, by decide, by decide, by omega⟩
    | exact hG ⟨7, 53, by decide, by decide, by omega⟩
    | exact hG ⟨3, 59, by decide, by decide, by omega⟩)

/-! ### Reindexing the antidiagonal -/

private lemma antidiagonal_eq_range (N : ℕ) :
    (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
      (if ¬ x.1.Prime then ArithmeticFunction.vonMangoldt x.1 * ArithmeticFunction.vonMangoldt x.2 else 0))
    = ∑ a ∈ Finset.range (N+1),
        (if ¬ a.Prime then ArithmeticFunction.vonMangoldt a * ArithmeticFunction.vonMangoldt (N-a) else 0) := by
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ (fun a b =>
    (if ¬ a.Prime then ArithmeticFunction.vonMangoldt a * ArithmeticFunction.vonMangoldt b else 0)) N]

/-- The range sum vanishes when `M ≤ 2`: then a non-prime first entry is `0` or `1`, where `Λ` is
zero. -/
private lemma small_terms_vanish (M : ℕ) (hM : M ≤ 2) :
    (∑ a ∈ Finset.range (M+1),
        (if ¬ a.Prime then
          ArithmeticFunction.vonMangoldt a * ArithmeticFunction.vonMangoldt (M-a) else 0)) = 0 := by
  classical
  refine Finset.sum_eq_zero ?_
  intro a ha
  have haM : a ≤ M := by simpa using ha
  have ha2 : a ≤ 2 := by omega
  have ha0 : ArithmeticFunction.vonMangoldt 0 = 0 := by
    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
    exact not_isPrimePow_zero
  interval_cases a <;>
    simp [ha0, ArithmeticFunction.vonMangoldt_apply_one, Nat.not_prime_zero, Nat.not_prime_one,
      Nat.prime_two]

/-! ## The leaves -/

/-- LEAF. Step 1 of the proof: the part of the von Mangoldt sum over pairs whose two entries are
both prime is zero at an `N` that is not a Goldbach sum. Such a pair would be a pair of primes with
`p + q = N`, which is exactly what the hypothesis excludes; every remaining term is replaced by
`0`. -/
theorem leaf_both_prime_part_vanishes (N : ℕ) (h_not_G : ¬ IsGoldbachSum N) :
    (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
      (if x.1.Prime ∧ x.2.Prime then
        ArithmeticFunction.vonMangoldt x.1 * ArithmeticFunction.vonMangoldt x.2 else 0)) = 0 := by
  apply Finset.sum_eq_zero
  intro x hx
  rw [if_neg]
  rintro ⟨h1, h2⟩
  exact h_not_G ⟨x.1, x.2, h1, h2, Finset.HasAntidiagonal.mem_antidiagonal.mp hx⟩

/-- LEAF. Step 2 of the proof: the mass carried by the pairs whose first entry is not prime — that
is, since `Λ` vanishes off the prime powers, whose first entry is a proper prime power — is at most
three quarters of the right-hand side. This is the first half of the count of proper prime power
representations of `N`, and it is the only estimate in the split that is not a formal identity. -/
theorem leaf_first_entry_not_prime_mass (N : ℕ) (hN : Even N) (h_not_G : ¬ IsGoldbachSum N) :
    (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
      (if ¬ x.1.Prime then
        ArithmeticFunction.vonMangoldt x.1 * ArithmeticFunction.vonMangoldt x.2 else 0))
      ≤ 3/4 * ((N : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (N : ℝ))^3) := by
  classical
  rw [antidiagonal_eq_range]
  rcases lt_or_ge N 64 with hsmall | hbig
  · have hN2 : N ≤ 2 := goldbach_small N (by omega) hN h_not_G
    have hzero := small_terms_vanish N hN2
    rw [hzero]
    interval_cases N
    · simp [Real.log_zero, Real.zero_rpow]
    · simp [Real.log_one, Real.one_rpow]
    · have hlog2 : (0:ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      have hsq : (0:ℝ) ≤ (Real.log 2)^3 := by positivity
      have hrt : (0:ℝ) ≤ (2:ℝ)^((1:ℝ)/2) := Real.rpow_nonneg (by norm_num) _
      nlinarith [hsq, hrt]
  · have hN4 : (4:ℕ) ≤ N := by omega
    have hmass := mass_le_card N (by omega)
    have hcard := card_S_le N hN4
    have hlog64 : (10/3 : ℝ) ≤ Real.log (N:ℝ) := by
      have hmono : Real.log (64:ℝ) ≤ Real.log (N:ℝ) :=
        Real.log_le_log (by norm_num) (by exact_mod_cast (by omega : 64 ≤ N))
      have h64 : Real.log (64:ℝ) = 6 * Real.log 2 := by
        rw [show (64:ℝ) = 2^6 by norm_num, Real.log_pow]; push_cast; ring
      have hgt := Real.log_two_gt_d9
      rw [h64] at hmono
      linarith
    refine le_trans hmass ?_
    refine le_trans (mul_le_mul_of_nonneg_left hcard (by positivity)) ?_
    have hxL : (0:ℝ) ≤ (N:ℝ)^((1:ℝ)/2) * (Real.log (N:ℝ))^2 := by positivity
    have hkey : (5/2 : ℝ) ≤ 3/4 * Real.log (N:ℝ) := by linarith
    calc Real.log (N:ℝ) * (Real.log (N:ℝ) / 2) * (5 * (N:ℝ)^((1:ℝ)/2))
        = ((N:ℝ)^((1:ℝ)/2) * (Real.log (N:ℝ))^2) * (5/2) := by ring
      _ ≤ ((N:ℝ)^((1:ℝ)/2) * (Real.log (N:ℝ))^2) * (3/4 * Real.log (N:ℝ)) :=
          mul_le_mul_of_nonneg_left hkey hxL
      _ = (3/4) * ((N:ℝ)^((1:ℝ)/2) * (Real.log (N:ℝ))^3) := by ring


/-- LEAF. Step 3 of the proof: the mass carried by the pairs whose first entry is prime while the
second is not is at most three quarters of the right-hand side. Together with step 2 this is the
full proper prime power count: at an `N` that is not a Goldbach sum, a term with both entries prime
never occurs, so every surviving pair has a non-prime entry, and the two steps cover the two ways
that can happen. -/
theorem leaf_second_entry_not_prime_mass (N : ℕ) (hN : Even N) (h_not_G : ¬ IsGoldbachSum N) :
    (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
      (if x.1.Prime then
        (if ¬ x.2.Prime then
          ArithmeticFunction.vonMangoldt x.1 * ArithmeticFunction.vonMangoldt x.2 else 0)
        else 0))
      ≤ 3/4 * ((N : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (N : ℝ))^3) := by
  classical
  have hmono : (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
      (if x.1.Prime then
        (if ¬ x.2.Prime then
          ArithmeticFunction.vonMangoldt x.1 * ArithmeticFunction.vonMangoldt x.2 else 0)
        else 0))
      ≤ ∑ x ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
        (if ¬ x.2.Prime then
          ArithmeticFunction.vonMangoldt x.1 * ArithmeticFunction.vonMangoldt x.2 else 0) := by
    refine Finset.sum_le_sum ?_
    intro x _
    have hnn : 0 ≤ ArithmeticFunction.vonMangoldt x.1 * ArithmeticFunction.vonMangoldt x.2 :=
      mul_nonneg ArithmeticFunction.vonMangoldt_nonneg ArithmeticFunction.vonMangoldt_nonneg
    by_cases hp : x.1.Prime
    · by_cases hq : x.2.Prime
      · simp [hp, hq]
      · simp [hp, hq]
    · by_cases hq : x.2.Prime
      · simp [hp, hq]
      · simp [hp, hq, hnn]
  have hswap : (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
        (if ¬ x.2.Prime then
          ArithmeticFunction.vonMangoldt x.1 * ArithmeticFunction.vonMangoldt x.2 else 0))
      = (∑ x ∈ (Finset.HasAntidiagonal.antidiagonal N : Finset (ℕ × ℕ)),
        (if ¬ x.1.Prime then
          ArithmeticFunction.vonMangoldt x.1 * ArithmeticFunction.vonMangoldt x.2 else 0)) := by
    rw [← Finset.Nat.sum_antidiagonal_swap (f := fun p : ℕ × ℕ =>
      (if ¬ p.2.Prime then ArithmeticFunction.vonMangoldt p.1 * ArithmeticFunction.vonMangoldt p.2 else 0))]
    refine Finset.sum_congr rfl ?_
    intro p _
    simp only [Prod.fst_swap, Prod.snd_swap]
    split_ifs <;> ring
  refine le_trans hmono ?_
  rw [hswap]
  exact leaf_first_entry_not_prime_mass N hN h_not_G


/-! ## The assembly -/

/-- The statement of `r2_prime_power_bound`, derived from the three steps above. The whole content
sits in leaves 2 and 3; the assembly is the case distinction of `r2_three_parts` and the vanishing
of leaf 1. -/
theorem r2_prime_power_bound_split (N : ℕ) (hN : Even N) (h_not_G : ¬ IsGoldbachSum N) :
   r2 N ≤ 3/2 * (N : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (N : ℝ))^3 := by
  have hu : 3/2 * (N : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (N : ℝ))^3
      = 3/2 * ((N : ℝ) ^ ((1 : ℝ) / 2) * (Real.log (N : ℝ))^3) := by ring
  have h1 := leaf_both_prime_part_vanishes N h_not_G
  have h2 := leaf_first_entry_not_prime_mass N hN h_not_G
  have h3 := leaf_second_entry_not_prime_mass N hN h_not_G
  have hsp := r2_three_parts N
  rw [hu]
  linarith [hsp, h1, h2, h3]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.r2_prime_power_bound_split
