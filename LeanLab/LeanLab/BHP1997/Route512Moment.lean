/-
P0069, Baker Harman Pintz 1997, page 9, first display:
the short interval divisor moment bound
  sum over k in I of tau(k)^(2B) << Y L^B,  I = (x - 2Y, x],  Y = x^(11/20 + eps),
which the paper asserts without proof. Here it is proved in full, in the form
  sum over k in I of tau(k)^(2B) <= C * Y * (log x)^c  for x >= C,
with c and C depending only on B and eps. The exponent c produced here is 2^M with
M the ceiling of 8 max(B,0); it is not the exponent B of the paper's display, and the
statement below only asserts the existence of some c.

Method: every n >= 1 has a divisor d with d * d <= n and tau(n) <= 2 tau(d)^4;
harmonic sums of tau(d)^M / d over d <= z are at most (1 + log z)^(2^M); and the
number of multiples of d in I is at most 4 Y / d for d <= sqrt x.

AI wrote the Lean code. Goldbach is open.
-/
import Mathlib

namespace LeanLab.BHP1997.Route512

/-- The divisor count is submultiplicative. -/
private theorem card_divisors_mul_le512m (a b : ℕ) :
    (a * b).divisors.card ≤ a.divisors.card * b.divisors.card := by
  rw [Nat.divisors_mul]
  exact Finset.card_mul_le

private theorem card_divisors_pos512m {n : ℕ} (hn : n ≠ 0) : 1 ≤ n.divisors.card :=
  Finset.card_pos.mpr ⟨1, Nat.one_mem_divisors.mpr hn⟩

private theorem card_divisors_le_of_dvd512m {a b : ℕ} (h : a ∣ b) (hb : b ≠ 0) :
    a.divisors.card ≤ b.divisors.card :=
  Finset.card_le_card (Nat.divisors_subset_of_dvd hb h)

private theorem card_divisors_prime512m {p : ℕ} (hp : p.Prime) : p.divisors.card = 2 := by
  rw [hp.divisors, Finset.card_pair hp.one_lt.ne]

/-- Squarefree case: a squarefree `s` has a divisor `d` with `d * d ≤ s` and
`τ(s) ≤ 2 τ(d)^2`. -/
private theorem squarefree_half512m : ∀ s : ℕ, Squarefree s →
    ∃ d : ℕ, d ∣ s ∧ d * d ≤ s ∧ s.divisors.card ≤ 2 * d.divisors.card ^ 2 := by
  intro s
  induction s using Nat.strong_induction_on with
  | _ s ih =>
    intro hs
    by_cases h1 : s = 1
    · subst h1
      exact ⟨1, one_dvd _, by norm_num, by simp⟩
    have hp : (Nat.minFac s).Prime := Nat.minFac_prime h1
    have hmin : ∀ q : ℕ, q.Prime → q ∣ s → Nat.minFac s ≤ q :=
      fun q hq hqs => Nat.minFac_le_of_dvd hq.two_le hqs
    obtain ⟨t, ht⟩ := Nat.minFac_dvd s
    generalize Nat.minFac s = p at hp hmin ht
    subst ht
    by_cases ht1 : t = 1
    · subst ht1
      refine ⟨1, one_dvd _, ?_, ?_⟩
      · have := hp.two_le
        omega
      · rw [mul_one, card_divisors_prime512m hp]
        simp
    have ht0 : t ≠ 0 := by
      rintro rfl
      simp at hs
    have hq : (Nat.minFac t).Prime := Nat.minFac_prime ht1
    have hpq : p ≤ Nat.minFac t := hmin _ hq (dvd_mul_of_dvd_right (Nat.minFac_dvd t) p)
    obtain ⟨u, hu⟩ := Nat.minFac_dvd t
    generalize Nat.minFac t = q at hq hu hpq
    subst hu
    have hu0 : u ≠ 0 := by
      rintro rfl
      simp at ht0
    have hsu : Squarefree u := (Squarefree.of_mul_right hs).of_mul_right
    have hlt : u < p * (q * u) := by
      have h4 : 2 * (2 * u) ≤ p * (q * u) :=
        Nat.mul_le_mul hp.two_le (Nat.mul_le_mul hq.two_le le_rfl)
      have := Nat.pos_of_ne_zero hu0
      omega
    obtain ⟨d, hdu, hdd, hτ⟩ := ih u hlt hsu
    have hpd : ¬ p ∣ d := by
      intro h
      have h2 : p * p ∣ p * (q * u) :=
        mul_dvd_mul_left p (dvd_mul_of_dvd_right (h.trans hdu) q)
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hs p h2))
    have hcop : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
    refine ⟨p * d, mul_dvd_mul_left p (dvd_mul_of_dvd_right hdu q), ?_, ?_⟩
    · calc p * d * (p * d) = p * p * (d * d) := by ring
        _ ≤ p * q * u := Nat.mul_le_mul (Nat.mul_le_mul_left p hpq) hdd
        _ = p * (q * u) := by ring
    · rw [hcop.card_divisors_mul, card_divisors_prime512m hp]
      calc (p * (q * u)).divisors.card
          ≤ p.divisors.card * (q * u).divisors.card := card_divisors_mul_le512m _ _
        _ ≤ p.divisors.card * (q.divisors.card * u.divisors.card) :=
            Nat.mul_le_mul_left _ (card_divisors_mul_le512m _ _)
        _ = 4 * u.divisors.card := by
            rw [card_divisors_prime512m hp, card_divisors_prime512m hq]; ring
        _ ≤ 4 * (2 * d.divisors.card ^ 2) := Nat.mul_le_mul_left _ hτ
        _ = 2 * (2 * d.divisors.card) ^ 2 := by ring

/-- Key lemma: every `n ≥ 1` has a divisor `d` with `d * d ≤ n` and `τ(n) ≤ 2 τ(d)^4`. -/
theorem exists_small_divisor512m (n : ℕ) (hn : n ≠ 0) :
    ∃ d : ℕ, d ∣ n ∧ d * d ≤ n ∧ n.divisors.card ≤ 2 * d.divisors.card ^ 4 := by
  obtain ⟨m, s, hsm, hs⟩ := exists_sq_mul_squarefree n
  subst hsm
  have hm0 : m ≠ 0 := by
    rintro rfl
    simp at hn
  have hs0 : s ≠ 0 := hs.ne_zero
  obtain ⟨d1, hd1, hdd, hτ⟩ := squarefree_half512m s hs
  have hd10 : d1 ≠ 0 := by
    rintro rfl
    exact hs0 (zero_dvd_iff.mp hd1)
  have hd0 : d1 * m ≠ 0 := mul_ne_zero hd10 hm0
  have h3 : m.divisors.card ≤ (d1 * m).divisors.card :=
    card_divisors_le_of_dvd512m (dvd_mul_left m d1) hd0
  have h4 : d1.divisors.card ≤ (d1 * m).divisors.card :=
    card_divisors_le_of_dvd512m (dvd_mul_right d1 m) hd0
  refine ⟨d1 * m, ?_, ?_, ?_⟩
  · obtain ⟨e, rfl⟩ := hd1
    exact ⟨m * e, by ring⟩
  · calc d1 * m * (d1 * m) = m ^ 2 * (d1 * d1) := by ring
      _ ≤ m ^ 2 * s := Nat.mul_le_mul_left _ hdd
  · calc (m ^ 2 * s).divisors.card
        ≤ (m ^ 2).divisors.card * s.divisors.card := card_divisors_mul_le512m _ _
      _ ≤ (m.divisors.card * m.divisors.card) * (2 * d1.divisors.card ^ 2) :=
          Nat.mul_le_mul (by rw [pow_two]; exact card_divisors_mul_le512m m m) hτ
      _ ≤ ((d1 * m).divisors.card * (d1 * m).divisors.card)
            * (2 * (d1 * m).divisors.card ^ 2) :=
          Nat.mul_le_mul (Nat.mul_le_mul h3 h3)
            (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left h4 2))
      _ = 2 * (d1 * m).divisors.card ^ 4 := by ring

private theorem term_le512m (M e f : ℕ) (he : e ≠ 0) (hf : f ≠ 0) :
    (((e * f).divisors.card : ℕ) : ℝ) ^ M / ((e * f : ℕ) : ℝ)
      ≤ ((e.divisors.card : ℕ) : ℝ) ^ M / (e : ℝ)
        * (((f.divisors.card : ℕ) : ℝ) ^ M / (f : ℝ)) := by
  rw [div_mul_div_comm, ← mul_pow, Nat.cast_mul]
  have h : (((e * f).divisors.card : ℕ) : ℝ)
      ≤ ((e.divisors.card : ℕ) : ℝ) * ((f.divisors.card : ℕ) : ℝ) := by
    exact_mod_cast card_divisors_mul_le512m e f
  have he' : (0:ℝ) < e := Nat.cast_pos.mpr (Nat.pos_of_ne_zero he)
  have hf' : (0:ℝ) < f := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hf)
  have hef : (0:ℝ) ≤ (e:ℝ) * f := (mul_pos he' hf').le
  have h0 : (0:ℝ) ≤ (((e * f).divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
  exact div_le_div_of_nonneg_right (pow_le_pow_left₀ h0 h M) hef

private theorem sum_antidiag_le512m (g : ℕ → ℝ) (hg : ∀ n, 0 ≤ g n) (z : ℕ) :
    ∑ d ∈ Finset.Icc 1 z, ∑ x ∈ d.divisorsAntidiagonal, g x.1 * g x.2
      ≤ (∑ d ∈ Finset.Icc 1 z, g d) ^ 2 := by
  have hdisj : Set.PairwiseDisjoint (↑(Finset.Icc 1 z) : Set ℕ)
      (fun d : ℕ => d.divisorsAntidiagonal) := by
    intro d _ d' _ hne
    show Disjoint d.divisorsAntidiagonal d'.divisorsAntidiagonal
    refine Finset.disjoint_left.mpr (fun x hx hx' => hne ?_)
    rw [Nat.mem_divisorsAntidiagonal] at hx hx'
    exact hx.1.symm.trans hx'.1
  have hprod : (∑ d ∈ Finset.Icc 1 z, g d) ^ 2
      = ∑ x ∈ Finset.Icc 1 z ×ˢ Finset.Icc 1 z, g x.1 * g x.2 := by
    rw [pow_two, Finset.sum_mul_sum, Finset.sum_product]
  rw [← Finset.sum_biUnion hdisj, hprod]
  refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun x _ _ => mul_nonneg (hg _) (hg _))
  intro x hx
  rw [Finset.mem_biUnion] at hx
  obtain ⟨d, hd, hx⟩ := hx
  rw [Nat.mem_divisorsAntidiagonal] at hx
  rw [Finset.mem_Icc] at hd
  obtain ⟨hxd, hd0⟩ := hx
  have h1 : x.1 ≠ 0 := by
    intro h
    rw [h, zero_mul] at hxd
    exact hd0 hxd.symm
  have h2 : x.2 ≠ 0 := by
    intro h
    rw [h, mul_zero] at hxd
    exact hd0 hxd.symm
  have h3 : x.1 ≤ x.1 * x.2 := Nat.le_mul_of_pos_right _ (Nat.pos_of_ne_zero h2)
  have h4 : x.2 ≤ x.1 * x.2 := Nat.le_mul_of_pos_left _ (Nat.pos_of_ne_zero h1)
  rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
  exact ⟨⟨Nat.pos_of_ne_zero h1, by omega⟩, ⟨Nat.pos_of_ne_zero h2, by omega⟩⟩

/-- Harmonic divisor power sums: `∑_{d ≤ z} τ(d)^M / d ≤ (1 + log z)^(2^M)`. -/
theorem harmonic_divisor_pow_sum512m (M z : ℕ) :
    ∑ d ∈ Finset.Icc 1 z, ((d.divisors.card : ℕ) : ℝ) ^ M / (d : ℝ)
      ≤ (1 + Real.log z) ^ (2 ^ M) := by
  induction M with
  | zero =>
    have h := harmonic_le_one_add_log z
    rw [harmonic_eq_sum_Icc] at h
    push_cast at h
    simpa using h
  | succ M ih =>
    have h1 : ∀ d ∈ Finset.Icc 1 z, ((d.divisors.card : ℕ) : ℝ) ^ (M + 1) / (d : ℝ)
        ≤ ∑ x ∈ d.divisorsAntidiagonal,
            (((x.1.divisors.card : ℕ) : ℝ) ^ M / (x.1 : ℝ))
              * (((x.2.divisors.card : ℕ) : ℝ) ^ M / (x.2 : ℝ)) := by
      intro d hd
      have hd0 : d ≠ 0 := by
        rw [Finset.mem_Icc] at hd
        omega
      have hanti := Nat.sum_divisorsAntidiagonal (n := d)
        (f := fun a b : ℕ => (((a.divisors.card : ℕ) : ℝ) ^ M / (a : ℝ))
              * (((b.divisors.card : ℕ) : ℝ) ^ M / (b : ℝ)))
      rw [hanti]
      calc ((d.divisors.card : ℕ) : ℝ) ^ (M + 1) / (d : ℝ)
          = ∑ _e ∈ d.divisors, ((d.divisors.card : ℕ) : ℝ) ^ M / (d : ℝ) := by
            rw [Finset.sum_const, nsmul_eq_mul, pow_succ]; ring
        _ ≤ _ := by
            refine Finset.sum_le_sum (fun e he => ?_)
            have hed : e ∣ d := Nat.dvd_of_mem_divisors he
            obtain ⟨f, rfl⟩ := hed
            have he0 : e ≠ 0 := left_ne_zero_of_mul hd0
            have hf0 : f ≠ 0 := right_ne_zero_of_mul hd0
            rw [Nat.mul_div_cancel_left f (Nat.pos_of_ne_zero he0)]
            exact term_le512m M e f he0 hf0
    have key := sum_antidiag_le512m
      (fun n : ℕ => ((n.divisors.card : ℕ) : ℝ) ^ M / (n : ℝ)) (fun n => by positivity) z
    beta_reduce at key
    have hnn : 0 ≤ ∑ d ∈ Finset.Icc 1 z, ((d.divisors.card : ℕ) : ℝ) ^ M / (d : ℝ) :=
      Finset.sum_nonneg (fun d _ => by positivity)
    calc ∑ d ∈ Finset.Icc 1 z, ((d.divisors.card : ℕ) : ℝ) ^ (M + 1) / (d : ℝ)
        ≤ _ := Finset.sum_le_sum h1
      _ ≤ _ := key
      _ ≤ ((1 + Real.log z) ^ (2 ^ M)) ^ 2 := pow_le_pow_left₀ hnn ih 2
      _ = (1 + Real.log z) ^ (2 ^ (M + 1)) := by rw [← pow_mul, pow_succ]

/-- The number of multiples of `d` in `(a, b]` is at most `(b - a) / d + 1`. -/
theorem count_dvd512m (a b d : ℕ) (hd : 0 < d) (hab : a ≤ b) :
    (((Finset.Ioc a b).filter (fun k => d ∣ k)).card : ℝ) ≤ ((b : ℝ) - a) / d + 1 := by
  have hcard : ((Finset.Ioc a b).filter (fun k => d ∣ k)).card
      ≤ (Finset.Ioc (a / d) (b / d)).card := by
    apply Finset.card_le_card_of_injOn (fun k => k / d)
    · intro k hk
      simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_ofPred_eq, Finset.coe_Ioc,
        Set.mem_Ioc] at hk ⊢
      obtain ⟨⟨h1, h2⟩, j, rfl⟩ := hk
      rw [Nat.mul_div_cancel_left j hd]
      refine ⟨Nat.div_lt_of_lt_mul h1, (Nat.le_div_iff_mul_le hd).mpr ?_⟩
      rw [mul_comm]
      exact h2
    · intro k hk k' hk' h
      simp only [Finset.coe_filter, Finset.mem_Ioc, Set.mem_ofPred_eq] at hk hk'
      obtain ⟨_, j, rfl⟩ := hk
      obtain ⟨_, j', rfl⟩ := hk'
      simp only [Nat.mul_div_cancel_left _ hd] at h
      rw [h]
  rw [Nat.card_Ioc] at hcard
  have hle : a / d ≤ b / d := Nat.div_le_div_right hab
  have h1 : ((b / d : ℕ) : ℝ) ≤ (b:ℝ) / d := Nat.cast_div_le
  have hdR : (0:ℝ) < d := Nat.cast_pos.mpr hd
  have h2 : (a:ℝ) / d ≤ ((a / d : ℕ) : ℝ) + 1 := by
    rw [div_le_iff₀ hdR]
    have h3 : a < d * (a / d) + d := by
      have := Nat.div_add_mod a d
      have := Nat.mod_lt a hd
      omega
    have h4 : (a:ℝ) < d * ((a / d : ℕ) : ℝ) + d := by exact_mod_cast h3
    nlinarith
  have h5 : ((((Finset.Ioc a b).filter (fun k => d ∣ k)).card : ℕ) : ℝ)
      + ((a / d : ℕ) : ℝ) ≤ ((b / d : ℕ) : ℝ) := by
    have : ((Finset.Ioc a b).filter (fun k => d ∣ k)).card + a / d ≤ b / d := by omega
    exact_mod_cast this
  have h6 : ((b:ℝ) - a) / d = (b:ℝ) / d - (a:ℝ) / d := sub_div _ _ _
  linarith

/-- The moment bound for nonnegative `B`. -/
private theorem moment_nonneg512m (B ε : ℝ) (hB : 0 ≤ B) (hε : 0 < ε) :
    ∃ c C : ℝ, ∀ x : ℝ, C ≤ x →
      ∑ k ∈ Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊,
        ((k.divisors.card : ℕ) : ℝ) ^ (2 * B) ≤ C * x ^ (11 / 20 + ε) * Real.log x ^ c := by
  obtain ⟨M, hMB⟩ : ∃ M : ℕ, 8 * B ≤ (M : ℝ) := ⟨⌈8 * B⌉₊, Nat.le_ceil _⟩
  refine ⟨((2 ^ M : ℕ) : ℝ), (2:ℝ) ^ (2 * B) * 4 * 2 ^ (2 ^ M) + 3, ?_⟩
  intro x hx
  have hK : (0:ℝ) ≤ (2:ℝ) ^ (2 * B) * 4 * 2 ^ (2 ^ M) := by positivity
  have h2Bpos : (0:ℝ) ≤ (2:ℝ) ^ (2 * B) := by positivity
  have hx3 : (3:ℝ) ≤ x := by linarith
  have hx1 : (1:ℝ) ≤ x := by linarith
  have hx0 : (0:ℝ) ≤ x := by linarith
  have hxpos : (0:ℝ) < x := by linarith
  have hY1' : 1 ≤ x ^ (11 / 20 + ε) := Real.one_le_rpow hx1 (by linarith)
  have hYY' : x ≤ x ^ (11 / 20 + ε) * x ^ (11 / 20 + ε) := by
    rw [← Real.rpow_add hxpos]
    calc x = x ^ (1:ℝ) := (Real.rpow_one x).symm
      _ ≤ _ := Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
  generalize x ^ (11 / 20 + ε) = Y at hY1' hYY' ⊢
  have hY0 : 0 ≤ Y := by linarith
  have hab' : ⌊x - 2 * Y⌋₊ ≤ ⌊x⌋₊ := Nat.floor_le_floor (by linarith)
  have hbx' : ((⌊x⌋₊ : ℕ) : ℝ) ≤ x := Nat.floor_le hx0
  have hax' : x - 2 * Y < ((⌊x - 2 * Y⌋₊ : ℕ) : ℝ) + 1 := Nat.lt_floor_add_one _
  have hb1' : 1 ≤ ⌊x⌋₊ := Nat.le_floor (by simpa using hx1)
  generalize ⌊x - 2 * Y⌋₊ = a at hab' hax' ⊢
  generalize ⌊x⌋₊ = b at hab' hbx' hb1' ⊢
  have hz1 : 1 ≤ Nat.sqrt b := Nat.le_sqrt.mpr (by simpa using hb1')
  have hzb : Nat.sqrt b ≤ b := Nat.sqrt_le_self b
  have hL1 : 1 ≤ Real.log x := by
    rw [Real.le_log_iff_exp_le hxpos]
    have := Real.exp_one_lt_d9
    linarith
  have hz1R : (1:ℝ) ≤ (Nat.sqrt b : ℝ) := by exact_mod_cast hz1
  have hLz0 : 0 ≤ Real.log (Nat.sqrt b : ℝ) := Real.log_nonneg hz1R
  have hLz : Real.log (Nat.sqrt b : ℝ) ≤ Real.log x :=
    Real.log_le_log (by linarith) (le_trans (by exact_mod_cast hzb) hbx')
  -- pointwise bound
  have hpt : ∀ k ∈ Finset.Ioc a b, ((k.divisors.card : ℕ) : ℝ) ^ (2 * B) ≤
      (2:ℝ) ^ (2 * B) * ∑ d ∈ (Finset.Icc 1 (Nat.sqrt b)).filter (fun d => d ∣ k),
        ((d.divisors.card : ℕ) : ℝ) ^ M := by
    intro k hk
    rw [Finset.mem_Ioc] at hk
    have hk0 : k ≠ 0 := by omega
    obtain ⟨d, hdk, hdd, hτ⟩ := exists_small_divisor512m k hk0
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact hk0 (zero_dvd_iff.mp hdk)
    have hdz : d ≤ Nat.sqrt b := Nat.le_sqrt.mpr (le_trans hdd hk.2)
    have hdmem : d ∈ (Finset.Icc 1 (Nat.sqrt b)).filter (fun d => d ∣ k) := by
      simp only [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨Nat.one_le_iff_ne_zero.mpr hd0, hdz⟩, hdk⟩
    have hτd1 : (1:ℝ) ≤ ((d.divisors.card : ℕ) : ℝ) := by
      exact_mod_cast card_divisors_pos512m hd0
    have hτd0 : (0:ℝ) ≤ ((d.divisors.card : ℕ) : ℝ) := Nat.cast_nonneg _
    have hτR : ((k.divisors.card : ℕ) : ℝ) ≤ 2 * ((d.divisors.card : ℕ) : ℝ) ^ 4 := by
      exact_mod_cast hτ
    have h2B : 0 ≤ 2 * B := by linarith
    calc ((k.divisors.card : ℕ) : ℝ) ^ (2 * B)
        ≤ (2 * ((d.divisors.card : ℕ) : ℝ) ^ 4) ^ (2 * B) :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hτR h2B
      _ = (2:ℝ) ^ (2 * B) * ((d.divisors.card : ℕ) : ℝ) ^ (4 * (2 * B)) := by
          rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) (pow_nonneg hτd0 4),
            ← Real.rpow_natCast, ← Real.rpow_mul hτd0]
          norm_num
      _ ≤ (2:ℝ) ^ (2 * B) * ((d.divisors.card : ℕ) : ℝ) ^ (M : ℝ) :=
          mul_le_mul_of_nonneg_left
            (Real.rpow_le_rpow_of_exponent_le hτd1 (by linarith)) h2Bpos
      _ = (2:ℝ) ^ (2 * B) * ((d.divisors.card : ℕ) : ℝ) ^ M := by rw [Real.rpow_natCast]
      _ ≤ _ := by
          refine mul_le_mul_of_nonneg_left ?_ h2Bpos
          exact Finset.single_le_sum (f := fun d : ℕ => ((d.divisors.card : ℕ) : ℝ) ^ M)
            (fun i _ => by positivity) hdmem
  -- swap the order of summation
  have hswap : ∑ k ∈ Finset.Ioc a b, ∑ d ∈ (Finset.Icc 1 (Nat.sqrt b)).filter (fun d => d ∣ k),
        ((d.divisors.card : ℕ) : ℝ) ^ M
      = ∑ d ∈ Finset.Icc 1 (Nat.sqrt b),
          (((Finset.Ioc a b).filter (fun k => d ∣ k)).card : ℝ)
            * ((d.divisors.card : ℕ) : ℝ) ^ M := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  -- the count of multiples
  have hcount : ∀ d ∈ Finset.Icc 1 (Nat.sqrt b),
      (((Finset.Ioc a b).filter (fun k => d ∣ k)).card : ℝ) ≤ 4 * Y / d := by
    intro d hd
    rw [Finset.mem_Icc] at hd
    have hdpos : (0:ℝ) < d := Nat.cast_pos.mpr hd.1
    have hd1 : (1:ℝ) ≤ d := by exact_mod_cast hd.1
    have hdY : (d:ℝ) ≤ Y := by
      have h1 : d * d ≤ b := Nat.le_sqrt.mp hd.2
      have h2 : (d:ℝ) * d ≤ x := le_trans (by exact_mod_cast h1) hbx'
      by_contra hcon
      have := mul_self_lt_mul_self hY0 (not_le.mp hcon)
      linarith
    have h := count_dvd512m a b d hd.1 hab'
    have hba : ((b:ℝ) - a) / d ≤ (2 * Y + 1) / d :=
      div_le_div_of_nonneg_right (by linarith) hdpos.le
    calc (((Finset.Ioc a b).filter (fun k => d ∣ k)).card : ℝ) ≤ ((b:ℝ) - a) / d + 1 := h
      _ ≤ (2 * Y + 1) / d + d / d := by
          rw [div_self hdpos.ne']
          linarith
      _ = (2 * Y + 1 + d) / d := by ring
      _ ≤ 4 * Y / d := div_le_div_of_nonneg_right (by linarith) hdpos.le
  have hS := harmonic_divisor_pow_sum512m M (Nat.sqrt b)
  have hpow : (1 + Real.log (Nat.sqrt b : ℝ)) ^ (2 ^ M) ≤ (2 * Real.log x) ^ (2 ^ M) :=
    pow_le_pow_left₀ (by linarith) (by linarith) _
  have h4Y : 0 ≤ 4 * Y := by linarith
  have hLpow : 0 ≤ Real.log x ^ (2 ^ M) := pow_nonneg (by linarith) _
  calc ∑ k ∈ Finset.Ioc a b, ((k.divisors.card : ℕ) : ℝ) ^ (2 * B)
      ≤ ∑ k ∈ Finset.Ioc a b, (2:ℝ) ^ (2 * B)
          * ∑ d ∈ (Finset.Icc 1 (Nat.sqrt b)).filter (fun d => d ∣ k),
            ((d.divisors.card : ℕ) : ℝ) ^ M := Finset.sum_le_sum hpt
    _ = (2:ℝ) ^ (2 * B) * ∑ d ∈ Finset.Icc 1 (Nat.sqrt b),
          (((Finset.Ioc a b).filter (fun k => d ∣ k)).card : ℝ)
            * ((d.divisors.card : ℕ) : ℝ) ^ M := by
        rw [← Finset.mul_sum, hswap]
    _ ≤ (2:ℝ) ^ (2 * B) * ∑ d ∈ Finset.Icc 1 (Nat.sqrt b),
          (4 * Y / d) * ((d.divisors.card : ℕ) : ℝ) ^ M := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun d hd => ?_)) h2Bpos
        exact mul_le_mul_of_nonneg_right (hcount d hd) (by positivity)
    _ = (2:ℝ) ^ (2 * B) * (4 * Y * ∑ d ∈ Finset.Icc 1 (Nat.sqrt b),
          ((d.divisors.card : ℕ) : ℝ) ^ M / d) := by
        congr 1
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl (fun d _ => by ring)
    _ ≤ (2:ℝ) ^ (2 * B) * (4 * Y * (2 * Real.log x) ^ (2 ^ M)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (hS.trans hpow) h4Y) h2Bpos
    _ = (2:ℝ) ^ (2 * B) * 4 * 2 ^ (2 ^ M) * Y * Real.log x ^ (2 ^ M) := by
        rw [mul_pow]; ring
    _ ≤ ((2:ℝ) ^ (2 * B) * 4 * 2 ^ (2 ^ M) + 3) * Y * Real.log x ^ (((2 ^ M : ℕ) : ℝ)) := by
        rw [Real.rpow_natCast]
        have hP : 0 ≤ Y * Real.log x ^ (2 ^ M) := mul_nonneg hY0 hLpow
        nlinarith

/-- P0069 page 9, first display: the short interval divisor moment bound
`∑_{k ∈ (x - 2Y, x]} τ(k)^(2B) ≤ C Y (log x)^c` with `Y = x^(11/20 + ε)`, for `x ≥ C`. -/
theorem short_divisor_moment512 (B ε : ℝ) (hε : 0 < ε) :
    ∃ c C : ℝ, ∀ x : ℝ, C ≤ x →
      ∑ k ∈ Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊,
        ((k.divisors.card : ℕ) : ℝ) ^ (2 * B) ≤ C * x ^ (11 / 20 + ε) * Real.log x ^ c := by
  obtain ⟨c, C, h⟩ := moment_nonneg512m (max B 0) ε (le_max_right _ _) hε
  refine ⟨c, C, fun x hx => le_trans (Finset.sum_le_sum ?_) (h x hx)⟩
  intro k hk
  have hk0 : k ≠ 0 := by
    rw [Finset.mem_Ioc] at hk
    omega
  have h1 : (1:ℝ) ≤ ((k.divisors.card : ℕ) : ℝ) := by
    exact_mod_cast card_divisors_pos512m hk0
  exact Real.rpow_le_rpow_of_exponent_le h1 (by linarith [le_max_left B 0])

end LeanLab.BHP1997.Route512
