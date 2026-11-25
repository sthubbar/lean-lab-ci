import LeanLab.ExceptionalSet.UpJ200.Lemma2MV.Lemma55Split

/-!
# Proof of the leaf `lem55_ksum`, P0015 Lemma 5.5, the Euler product bound on page 360

Source P0015, Montgomery and Vaughan, The exceptional set in Goldbach's problem,
Acta Arith. 27, 1975, page 360: the sum over squarefree `k` coprime to `r₄` of
`φ(k)⁻¹ φ(k/(k,m))⁻¹` is `∏_{p ∤ r₄m} (1 + (p-1)⁻²) ∏_{p | m, p ∤ r₄} (1 + (p-1)⁻¹)`.
* (a) `ksum_le_euler`: the truncated sum is at most the finite Euler product over primes
  `p ≤ N`, `p ∤ r₄`, of `1 + f(p)`, via `k ↦ primeFactors k` and `prod_one_add`.
* (b) `ksum_euler_const`: `∏ (1 + (p-1)⁻²) ≤ e²`, from `∑ 1/i² ≤ 2`.
* (c) `ksum_one_add_inv`: `1 + (p-1)⁻¹ = (1 - 1/p)⁻¹`.
* `lem55_ksum_proved`, PROVED sorry free with `C = e²`, twin `lem55_ksum_twin` typed
  `type_of% @lem55_ksum`.

AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Lemma2MVKSum

open Real Finset

/-- P0015 page 360: for squarefree `k`, `φ(k) = ∏_{p | k} (p - 1)`. -/
theorem ksum_totient_sqfree {k : ℕ} (hk : Squarefree k) :
    ((k.totient : ℕ) : ℝ) = ∏ p ∈ k.primeFactors, ((p : ℝ) - 1) := by
  have h := Nat.totient_mul_prod_primeFactors k
  rw [Nat.prod_primeFactors_of_squarefree hk] at h
  have hk0 : k ≠ 0 := hk.ne_zero
  have h2 : k.totient = ∏ p ∈ k.primeFactors, (p - 1) := by
    rw [mul_comm] at h
    exact Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hk0) h
  rw [h2, Nat.cast_prod]
  refine prod_congr rfl fun p hp => ?_
  rw [Nat.cast_sub (Nat.prime_of_mem_primeFactors hp).one_le, Nat.cast_one]

/-- P0015 page 360: for squarefree `k`, the primes of `k/(k,n)` are the primes of `k` not
dividing `n`. -/
theorem ksum_primeFactors_div_gcd {k : ℕ} (hk : Squarefree k) (n : ℕ) :
    (k / Nat.gcd k n).primeFactors = k.primeFactors.filter (fun p => ¬ p ∣ n) := by
  have hk0 : k ≠ 0 := hk.ne_zero
  have hg : Nat.gcd k n ∣ k := Nat.gcd_dvd_left k n
  have hkeq : Nat.gcd k n * (k / Nat.gcd k n) = k := Nat.mul_div_cancel' hg
  have hk'0 : k / Nat.gcd k n ≠ 0 := by
    intro h; rw [h, mul_zero] at hkeq; exact hk0 hkeq.symm
  ext p
  simp only [mem_filter, Nat.mem_primeFactors]
  constructor
  · rintro ⟨hp, hpd, -⟩
    have hpk : p ∣ k := hpd.trans (Nat.div_dvd_of_dvd hg)
    refine ⟨⟨hp, hpk, hk0⟩, fun hpn => ?_⟩
    have hpg : p ∣ Nat.gcd k n := Nat.dvd_gcd hpk hpn
    have : p * p ∣ k := by
      rw [← hkeq]; exact Nat.mul_dvd_mul hpg hpd
    exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hk p this))
  · rintro ⟨⟨hp, hpk, -⟩, hpn⟩
    refine ⟨hp, ?_, hk'0⟩
    rw [← hkeq] at hpk
    rcases (Nat.Prime.dvd_mul hp).mp hpk with h | h
    · exact absurd (h.trans (Nat.gcd_dvd_right k n)) hpn
    · exact h

/-- P0015 page 360: for squarefree `k`, `φ(k/(k,n)) = ∏_{p | k} (if p | n then 1 else p - 1)`. -/
theorem ksum_totient_div_gcd {k : ℕ} (hk : Squarefree k) (n : ℕ) :
    (((k / Nat.gcd k n).totient : ℕ) : ℝ) =
      ∏ p ∈ k.primeFactors, (if p ∣ n then (1 : ℝ) else (p : ℝ) - 1) := by
  have hsq : Squarefree (k / Nat.gcd k n) := hk.squarefree_of_dvd (Nat.div_dvd_of_dvd (Nat.gcd_dvd_left k n))
  rw [ksum_totient_sqfree hsq, ksum_primeFactors_div_gcd hk, prod_filter]
  refine prod_congr rfl fun p _ => ?_
  split_ifs <;> rfl

/-- The local factor `f(p)` of the multiplicative function `μ(k)² φ(k)⁻¹ φ(k/(k,m))⁻¹`,
P0015 page 360: `(p-1)⁻²` if `p ∤ m` and `(p-1)⁻¹` if `p | m`. -/
noncomputable def ksumW (n p : ℕ) : ℝ :=
  1 / (((p : ℝ) - 1) * (if p ∣ n then (1 : ℝ) else (p : ℝ) - 1))

/-- P0015 page 360: for squarefree `k`, `φ(k)⁻¹ φ(k/(k,n))⁻¹ = ∏_{p | k} f(p)`. -/
theorem ksum_term_eq {k : ℕ} (hk : Squarefree k) (n : ℕ) :
    1 / (((k.totient : ℕ) : ℝ) * (((k / Nat.gcd k n).totient : ℕ) : ℝ)) =
      ∏ p ∈ k.primeFactors, ksumW n p := by
  rw [ksum_totient_sqfree hk, ksum_totient_div_gcd hk, ← prod_mul_distrib]
  simp only [ksumW, one_div, prod_inv_distrib]

/-- Step (a), P0015 page 360: the truncated sum over squarefree `k ≤ N` coprime to `r₄`
is at most the finite Euler product `∏_{p ≤ N, p ∤ r₄} (1 + f(p))`. -/
theorem ksum_le_euler (r₄ n N : ℕ) :
    ∑ q ∈ Icc 1 N, (if r₄ ∣ q then
        (if Nat.Coprime (q / r₄) r₄ ∧ Squarefree (q / r₄) then
          1 / (((q / r₄).totient : ℝ) * (((q / r₄) / Nat.gcd (q / r₄) n).totient : ℝ))
        else 0) else 0) ≤
      ∏ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ r₄), (1 + ksumW n p) := by
  classical
  set S := (range (N + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ r₄) with hS
  set A := (Icc 1 N).filter
    (fun q => r₄ ∣ q ∧ Nat.Coprime (q / r₄) r₄ ∧ Squarefree (q / r₄)) with hA
  have hW0 : ∀ p ∈ S, 0 ≤ ksumW n p := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ p := by
      exact_mod_cast (mem_filter.mp hp).2.1.two_le
    unfold ksumW
    apply div_nonneg zero_le_one
    apply mul_nonneg (by linarith)
    split_ifs <;> linarith
  have h1 : ∑ q ∈ Icc 1 N, (if r₄ ∣ q then
        (if Nat.Coprime (q / r₄) r₄ ∧ Squarefree (q / r₄) then
          1 / (((q / r₄).totient : ℝ) * (((q / r₄) / Nat.gcd (q / r₄) n).totient : ℝ))
        else 0) else 0) =
      ∑ q ∈ A, ∏ p ∈ (q / r₄).primeFactors, ksumW n p := by
    rw [hA, sum_filter]
    refine sum_congr rfl fun q _ => ?_
    by_cases h1 : r₄ ∣ q
    · by_cases h2 : Nat.Coprime (q / r₄) r₄ ∧ Squarefree (q / r₄)
      · have h3 : r₄ ∣ q ∧ Nat.Coprime (q / r₄) r₄ ∧ Squarefree (q / r₄) := ⟨h1, h2⟩
        rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_left_of_eq_true _ _ (eq_true h2),
          ite_eq_left_of_eq_true _ _ (eq_true h3), ksum_term_eq h2.2]
      · have h3 : ¬ (r₄ ∣ q ∧ Nat.Coprime (q / r₄) r₄ ∧ Squarefree (q / r₄)) := fun h => h2 h.2
        rw [ite_eq_left_of_eq_true _ _ (eq_true h1), ite_eq_right_of_eq_false _ _ (eq_false h2),
          ite_eq_right_of_eq_false _ _ (eq_false h3)]
    · have h3 : ¬ (r₄ ∣ q ∧ Nat.Coprime (q / r₄) r₄ ∧ Squarefree (q / r₄)) := fun h => h1 h.1
      rw [ite_eq_right_of_eq_false _ _ (eq_false h1), ite_eq_right_of_eq_false _ _ (eq_false h3)]
  have hinj : Set.InjOn (fun q => (q / r₄).primeFactors) (A : Set ℕ) := by
    intro a ha b hb hab
    simp only [hA, coe_filter] at ha hb
    have hab' : a / r₄ = b / r₄ := by
      rw [← Nat.prod_primeFactors_of_squarefree ha.2.2.2,
        ← Nat.prod_primeFactors_of_squarefree hb.2.2.2]
      exact congrArg (fun s => ∏ p ∈ s, p) hab
    rw [← Nat.div_mul_cancel ha.2.1, ← Nat.div_mul_cancel hb.2.1, hab']
  have hsub : A.image (fun q => (q / r₄).primeFactors) ⊆ S.powerset := by
    intro T hT
    rw [mem_image] at hT
    obtain ⟨q, hq, rfl⟩ := hT
    rw [hA, mem_filter, mem_Icc] at hq
    rw [mem_powerset]
    intro p hp
    have hp' := Nat.mem_primeFactors.mp hp
    rw [hS, mem_filter, mem_range]
    refine ⟨?_, hp'.1, fun hpr => ?_⟩
    · have : p ≤ q / r₄ := Nat.le_of_dvd (Nat.pos_of_ne_zero hp'.2.2) hp'.2.1
      have : q / r₄ ≤ q := Nat.div_le_self q r₄
      omega
    · have hd := Nat.dvd_gcd hp'.2.1 hpr
      rw [hq.2.2.1.gcd_eq_one] at hd
      exact hp'.1.one_lt.ne' (Nat.dvd_one.mp hd)
  rw [h1, prod_one_add, ← sum_image (f := fun T => ∏ p ∈ T, ksumW n p) hinj]
  refine sum_le_sum_of_subset_of_nonneg hsub fun T hT _ => ?_
  exact prod_nonneg fun p hp => hW0 p (mem_powerset.mp hT hp)

/-- Step (c), P0015 page 360: `1 + (p-1)⁻¹ = (1 - 1/p)⁻¹` for a prime `p`. -/
theorem ksum_one_add_inv {p : ℕ} (hp : p.Prime) :
    1 + 1 / ((p : ℝ) - 1) = (1 - 1 / (p : ℝ))⁻¹ := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have h1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have h0 : (p : ℝ) ≠ 0 := by linarith
  field_simp
  ring

/-- P0015 page 360, local factor: `1 + f(p) ≤ (1 + (p-1)⁻²) · [p | n](1 - 1/p)⁻¹`. -/
theorem ksum_local (n : ℕ) {p : ℕ} (hp : p.Prime) :
    1 + ksumW n p ≤ (1 + 1 / ((p : ℝ) - 1) ^ 2) *
      (if p ∣ n then (1 - 1 / (p : ℝ))⁻¹ else 1) := by
  have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hpos : 0 < (p : ℝ) - 1 := by linarith
  unfold ksumW
  split_ifs with h
  · rw [← ksum_one_add_inv hp, mul_one]
    have hx : 0 ≤ 1 / ((p : ℝ) - 1) := by positivity
    have hy : 0 ≤ 1 / ((p : ℝ) - 1) ^ 2 := by positivity
    nlinarith [mul_nonneg hy hx]
  · rw [mul_one, sq]

/-- Step (b), P0015 page 360: `∏_p (1 + (p-1)⁻²) ≤ e²` over any finite set of primes. -/
theorem ksum_euler_const (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    ∏ p ∈ S, (1 + 1 / ((p : ℝ) - 1) ^ 2) ≤ Real.exp 2 := by
  have hstep : ∏ p ∈ S, (1 + 1 / ((p : ℝ) - 1) ^ 2) ≤
      ∏ p ∈ S, Real.exp (1 / ((p : ℝ) - 1) ^ 2) := by
    refine prod_le_prod₀ (fun p _ => by positivity) fun p _ => ?_
    have := Real.add_one_le_exp (1 / ((p : ℝ) - 1) ^ 2)
    linarith
  refine hstep.trans ?_
  rw [← Real.exp_sum, Real.exp_le_exp]
  set M := S.sup id + 1
  have hinj : Set.InjOn (fun p : ℕ => p - 1) (S : Set ℕ) := by
    intro a ha b hb hab
    have := (hS a ha).one_le
    have := (hS b hb).one_le
    simp only at hab
    omega
  have heq : ∑ p ∈ S, 1 / ((p : ℝ) - 1) ^ 2 =
      ∑ i ∈ S.image (fun p : ℕ => p - 1), ((i : ℝ) ^ 2)⁻¹ := by
    rw [sum_image hinj]
    refine sum_congr rfl fun p hp => ?_
    rw [Nat.cast_sub (hS p hp).one_le, Nat.cast_one, one_div]
  have hsub : S.image (fun p : ℕ => p - 1) ⊆ Ioo 0 M := by
    intro i hi
    rw [mem_image] at hi
    obtain ⟨p, hp, rfl⟩ := hi
    have h2 := (hS p hp).two_le
    have hle : p ≤ S.sup id := le_sup (f := id) hp
    rw [mem_Ioo]
    omega
  rw [heq]
  refine (sum_le_sum_of_subset_of_nonneg hsub fun i _ _ => by positivity).trans ?_
  have := sum_Ioo_inv_sq_le (α := ℝ) 0 M
  norm_num at this ⊢
  exact this

/-- Step (c) applied, P0015 page 360: `∏_{p ≤ N, p ∤ r₄} [p | n](1 - 1/p)⁻¹` is at most
`∏_{p | n, p ∤ r₄} (1 - 1/p)⁻¹`, each factor being at least one. -/
theorem ksum_mfactor (r₄ n N : ℕ) (hn : n ≠ 0) :
    ∏ p ∈ (range (N + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ r₄),
        (if p ∣ n then (1 - 1 / (p : ℝ))⁻¹ else 1) ≤
      ∏ p ∈ n.primeFactors.filter (fun p => ¬ p ∣ r₄), (1 - 1 / (p : ℝ))⁻¹ := by
  classical
  set U := ((range (N + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ r₄)).filter (fun p => p ∣ n)
  set T := n.primeFactors.filter (fun p => ¬ p ∣ r₄)
  have hU : U ⊆ T := by
    intro p hp
    simp only [U, T, mem_filter, Nat.mem_primeFactors] at hp ⊢
    exact ⟨⟨hp.1.2.1, hp.2, hn⟩, hp.1.2.2⟩
  have hge : ∀ p ∈ T, 1 ≤ (1 - 1 / (p : ℝ))⁻¹ := by
    intro p hp
    have h2 : (2 : ℝ) ≤ p := by
      exact_mod_cast (Nat.prime_of_mem_primeFactors (mem_filter.mp hp).1).two_le
    have hpos : 0 < 1 - 1 / (p : ℝ) := by
      have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
      linarith
    rw [one_le_inv₀ hpos]
    have : 0 < 1 / (p : ℝ) := by positivity
    linarith
  rw [← prod_filter, ← prod_sdiff hU]
  have h1 : 1 ≤ ∏ p ∈ T \ U, (1 - 1 / (p : ℝ))⁻¹ := by
    have := prod_le_prod₀ (s := T \ U) (f := fun _ : ℕ => (1 : ℝ))
      (g := fun p : ℕ => (1 - 1 / (p : ℝ))⁻¹) (fun _ _ => zero_le_one)
      (fun p hp => hge p (mem_sdiff.mp hp).1)
    rwa [prod_const_one] at this
  have h0 : 0 ≤ ∏ p ∈ U, (1 - 1 / (p : ℝ))⁻¹ :=
    prod_nonneg fun p hp => le_trans zero_le_one (hge p (hU hp))
  nlinarith

/-- P0015 Lemma 5.5 proof, page 360, PROVED: the `k` sum is at most
`e² ∏_{p | m, p ∤ r₄} (1 - 1/p)⁻¹`. Exact statement of `lem55_ksum`. -/
theorem lem55_ksum_proved : ∃ C : ℝ, 0 < C ∧ ∀ (r₄ : ℕ), 1 ≤ r₄ → ∀ m : ℤ, m ≠ 0 → ∀ N : ℕ,
    ∑ q ∈ Icc 1 N, (if r₄ ∣ q then
        (if Nat.Coprime (q / r₄) r₄ ∧ Squarefree (q / r₄) then
          1 / (((q / r₄).totient : ℝ) * (((q / r₄) / Nat.gcd (q / r₄) m.natAbs).totient : ℝ))
        else 0) else 0) ≤
      C * ∏ p ∈ m.natAbs.primeFactors.filter (fun p => ¬ p ∣ r₄), (1 - 1 / (p : ℝ))⁻¹ := by
  refine ⟨Real.exp 2, Real.exp_pos 2, fun r₄ _ m hm N => ?_⟩
  set S := (range (N + 1)).filter (fun p => p.Prime ∧ ¬ p ∣ r₄)
  have hSp : ∀ p ∈ S, p.Prime := fun p hp => (mem_filter.mp hp).2.1
  refine (ksum_le_euler r₄ m.natAbs N).trans ?_
  have hloc : ∏ p ∈ S, (1 + ksumW m.natAbs p) ≤
      ∏ p ∈ S, ((1 + 1 / ((p : ℝ) - 1) ^ 2) *
        (if p ∣ m.natAbs then (1 - 1 / (p : ℝ))⁻¹ else 1)) := by
    refine prod_le_prod₀ (fun p hp => ?_) fun p hp => ksum_local m.natAbs (hSp p hp)
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hSp p hp).two_le
    have : 0 ≤ ksumW m.natAbs p := by
      unfold ksumW
      apply div_nonneg zero_le_one
      apply mul_nonneg (by linarith)
      split_ifs <;> linarith
    linarith
  refine hloc.trans ?_
  rw [prod_mul_distrib]
  have hA := ksum_euler_const S hSp
  have hB := ksum_mfactor r₄ m.natAbs N (Int.natAbs_ne_zero.mpr hm)
  have hB0 : 0 ≤ ∏ p ∈ S, (if p ∣ m.natAbs then (1 - 1 / (p : ℝ))⁻¹ else 1) := by
    refine prod_nonneg fun p hp => ?_
    have h2 : (2 : ℝ) ≤ p := by exact_mod_cast (hSp p hp).two_le
    have : 1 / (p : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) h2
    split_ifs
    · exact inv_nonneg.mpr (by linarith)
    · exact zero_le_one
  exact mul_le_mul hA hB hB0 (Real.exp_pos 2).le

/-- Exact-type twin: `lem55_ksum_proved` has exactly the type of the leaf `lem55_ksum`. -/
theorem lem55_ksum_twin : type_of% @LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.lem55_ksum :=
  lem55_ksum_proved

end LeanLab.ExceptionalSet.UpJ200.Lemma2MVKSum

#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVKSum.lem55_ksum_proved
#print axioms LeanLab.ExceptionalSet.UpJ200.Lemma2MVKSum.lem55_ksum_twin
