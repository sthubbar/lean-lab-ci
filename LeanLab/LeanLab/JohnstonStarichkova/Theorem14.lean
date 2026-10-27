/-
Johnston and Starichkova, P0019, arXiv 2208.01229v3: Proposition 5.6 arithmetic and
Theorem 1.4 under GRH, printed with K = 33. Unit U-0343, run 20261017T1803Z-21479.
With the printed ranges and X₂ = exp exp 5.087, each range gives at most 32 prime factors:
first 22 primes removed, exp 158 < N < X₂: 32; first 15 removed, exp 109 ≤ N ≤ exp 158: 32;
Lemma 3.4 below exp 109: 26; the sieve range: 17. Theorem 1.4 is assembled here from cited
inputs and holds with 32; it is CONDITIONAL ON those inputs, which carry GRH, not PROVED.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
-/
import Mathlib
import LeanLab.JohnstonStarichkova.Lemma34

namespace LeanLab.JohnstonStarichkova

open Finset Nat

/-- Primes at least `b`. -/
def Pge (b p : ℕ) : Prop := p.Prime ∧ b ≤ p

instance (b : ℕ) : DecidablePred (Pge b) := fun p => by unfold Pge; infer_instance

theorem Pge_infinite (b : ℕ) : (Set.ofPred (Pge b)).Infinite := by
  refine (Nat.infinite_setOf_prime.diff (Set.finite_lt_nat b)).mono ?_
  intro p hp
  simp only [Set.mem_diff, Set.mem_setOf_eq, not_lt] at hp
  exact ⟨hp.1, hp.2⟩

theorem prod_nth_le_ge (b : ℕ) (S : Finset ℕ) (hS : ∀ s ∈ S, Pge b s) :
    ∏ i ∈ range S.card, nth (Pge b) i ≤ ∏ s ∈ S, s := by
  induction S using Finset.induction_on_max with
  | empty => simp
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    rw [card_insert_of_notMem ha, prod_range_succ, prod_insert ha]
    have ih' := ih (fun x hx => hS x (mem_insert_of_mem hx))
    have hPa : Pge b a := hS a (mem_insert_self a s)
    have hcard : s.card ≤ count (Pge b) a := by
      rw [count_eq_card_filter_range]
      apply card_le_card
      intro x hx
      simp only [mem_filter, mem_range]
      exact ⟨hlt x hx, hS x (mem_insert_of_mem hx)⟩
    have hnth : nth (Pge b) s.card ≤ a :=
      calc nth (Pge b) s.card ≤ nth (Pge b) (count (Pge b) a) :=
            nth_monotone (Pge_infinite b) hcard
        _ = a := nth_count hPa
    rw [mul_comm]
    exact Nat.mul_le_mul hnth ih'

/-- The primes from p_{L+1} on, re-indexed. -/
theorem nth_Pge (L i : ℕ) : nth (Pge (nth Nat.Prime L)) i = nth Nat.Prime (i + L) := by
  have hinf : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOf_prime
  set b := nth Nat.Prime L with hb
  set q := nth Nat.Prime (i + L) with hqdef
  have hq : q.Prime := nth_mem_of_infinite hinf _
  have hbq : b ≤ q := nth_monotone hinf (by omega)
  have hcb : count Nat.Prime b = L := count_nth_of_infinite hinf L
  have hcq : count Nat.Prime q = i + L := count_nth_of_infinite hinf _
  have h0 : count (Pge b) b = 0 := by
    rw [count_eq_card_filter_range, Finset.card_eq_zero, filter_eq_empty_iff]
    intro x hx hp
    simp only [mem_range] at hx
    exact absurd hp.2 (by omega)
  have hs1 := count_add (p := Nat.Prime) b (q - b)
  have hs2 := count_add (p := Pge b) b (q - b)
  have heq : count (fun k => Pge b (b + k)) (q - b) = count (fun k => Nat.Prime (b + k)) (q - b) :=
    count_congr' (fun k => ⟨fun h => h.1, fun h => ⟨h, by omega⟩⟩) _
  have hbq' : b + (q - b) = q := by omega
  rw [hbq'] at hs1 hs2
  have hc : count (Pge b) q = i := by omega
  calc nth (Pge b) i = nth (Pge b) (count (Pge b) q) := by rw [hc]
    _ = q := nth_count ⟨hq, hbq⟩

/-- Generic core: square-free η < X coprime to c, every prime below b dividing c. -/
theorem length_le_of_prod_ge {η X k b c : ℕ} (hbc : ∀ s, s.Prime → s < b → s ∣ c)
    (hsq : Squarefree η) (hcop : Nat.Coprime η c) (hηX : η < X)
    (hk : X ≤ ∏ i ∈ range (k + 1), nth (Pge b) i) : η.primeFactorsList.length ≤ k := by
  by_contra hcon
  push_neg at hcon
  have h0 : η ≠ 0 := by rintro rfl; exact not_squarefree_zero hsq
  have hnd := (squarefree_iff_nodup_primeFactorsList h0).mp hsq
  have hcard : η.primeFactorsList.toFinset.card = η.primeFactorsList.length :=
    List.toFinset_card_of_nodup hnd
  have hprod : ∏ s ∈ η.primeFactorsList.toFinset, s = η := by
    rw [List.prod_toFinset _ hnd]; simp [Nat.prod_primeFactorsList h0]
  have hS : ∀ s ∈ η.primeFactorsList.toFinset, Pge b s := by
    intro s hs
    have hs' := List.mem_toFinset.mp hs
    have hp := Nat.prime_of_mem_primeFactorsList hs'
    have hd := Nat.dvd_of_mem_primeFactorsList hs'
    refine ⟨hp, ?_⟩
    by_contra hlt
    push_neg at hlt
    have h1 := Nat.dvd_gcd hd (hbc s hp hlt)
    rw [Nat.Coprime.gcd_eq_one hcop] at h1
    exact hp.ne_one (Nat.dvd_one.mp h1)
  have h1 : ∏ i ∈ range (k + 1), nth (Pge b) i ≤
      ∏ i ∈ range η.primeFactorsList.toFinset.card, nth (Pge b) i := by
    apply prod_le_prod_of_subset_of_one_le'
    · exact range_subset_range.mpr (by omega)
    · intro i _ _
      exact (nth_mem_of_infinite (Pge_infinite b) i).1.one_lt.le
  have h2 := prod_nth_le_ge b _ hS
  rw [hprod] at h2
  omega

/-! ### Numbers -/

theorem exp_lt_of_nat {P n : ℕ} (hn : 0 < n) (h : 27182818286 ^ n < P * 10 ^ (10 * n)) :
    Real.exp n < P := by
  have he : Real.exp n = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul, mul_one]
  have h1 : Real.exp 1 ^ n < ((27182818286 : ℝ) / 10 ^ 10) ^ n := by
    apply pow_lt_pow_left₀ _ (Real.exp_pos 1).le hn.ne'
    have := Real.exp_one_lt_d9
    norm_num at this ⊢
    linarith
  rw [he]
  refine h1.trans ?_
  rw [div_pow, div_lt_iff₀ (by positivity), ← pow_mul]
  exact_mod_cast h

theorem lt_exp_of_nat {P n : ℕ} (hn : 0 < n) (h : P * 10 ^ (10 * n) < 27182818283 ^ n) :
    (P : ℝ) < Real.exp n := by
  have he : Real.exp n = Real.exp 1 ^ n := by rw [← Real.exp_nat_mul, mul_one]
  have h1 : ((27182818283 : ℝ) / 10 ^ 10) ^ n < Real.exp 1 ^ n := by
    apply pow_lt_pow_left₀ _ (by positivity) hn.ne'
    have := Real.exp_one_gt_d9
    norm_num at this ⊢
    linarith
  rw [he]
  refine lt_trans ?_ h1
  rw [div_pow, lt_div_iff₀ (by positivity), ← pow_mul]
  exact_mod_cast h

/-- The GRH section's X₂ = exp(exp 5.087). -/
noncomputable def X2G : ℝ := Real.exp (Real.exp 5.087)

theorem exp_087_le : Real.exp 0.087 ≤ 1.0909 := by
  have h := Real.exp_bound' (x := 0.087) (by norm_num) (by norm_num) (n := 8) (by norm_num)
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem exp_087_ge : 1.09089 ≤ Real.exp 0.087 := by
  have h := Real.sum_le_exp_of_nonneg (x := 0.087) (by norm_num) 8
  norm_num [Finset.sum_range_succ, Nat.factorial] at h
  linarith

theorem exp5087_eq : Real.exp 5.087 = Real.exp 1 ^ 5 * Real.exp 0.087 := by
  rw [← Real.exp_nat_mul, ← Real.exp_add]; norm_num

theorem exp5087_lt : Real.exp 5.087 < 167 := by
  rw [exp5087_eq]
  have h3 : Real.exp 1 ^ 5 < 2.7182818286 ^ 5 := by gcongr; exact Real.exp_one_lt_d9
  calc Real.exp 1 ^ 5 * Real.exp 0.087 ≤ 2.7182818286 ^ 5 * 1.0909 :=
        mul_le_mul h3.le exp_087_le (Real.exp_pos _).le (by positivity)
    _ < 167 := by norm_num

theorem exp5087_gt : 161.89 < Real.exp 5.087 := by
  rw [exp5087_eq]
  have h3 : 2.7182818283 ^ 5 < Real.exp 1 ^ 5 := by gcongr; exact Real.exp_one_gt_d9
  calc (161.89 : ℝ) < 2.7182818283 ^ 5 * 1.09089 := by norm_num
    _ ≤ Real.exp 1 ^ 5 * Real.exp 0.087 :=
        mul_le_mul h3.le exp_087_ge (by norm_num) (by positivity)

theorem big22hi : 27182818286 ^ 167 < (∏ i ∈ range 33, Q.getD (i + 16) 0) * 10 ^ (10 * 167) := by
  decide +kernel

theorem big22lo : (∏ i ∈ range 32, Q.getD (i + 16) 0) ^ 100 * 10 ^ (10 * 16189) <
    27182818283 ^ 16189 := by
  decide +kernel

theorem big15hi : 27182818286 ^ 158 < (∏ i ∈ range 33, Q.getD (i + 9) 0) * 10 ^ (10 * 158) := by
  decide +kernel

theorem big15lo : (∏ i ∈ range 32, Q.getD (i + 9) 0) * 10 ^ (10 * 158) < 27182818283 ^ 158 := by
  decide +kernel

theorem big6hi : 27182818286 ^ 109 < (∏ i ∈ range 27, Q.getD i 0) * 10 ^ (10 * 109) := by
  decide +kernel

theorem big6lo : (∏ i ∈ range 26, Q.getD i 0) * 10 ^ (10 * 109) < 27182818283 ^ 109 := by
  decide +kernel

theorem prodShift_eq {k s : ℕ} (hk : k + s ≤ 370) :
    ∏ i ∈ range k, nth Nat.Prime (i + (s + 6)) = ∏ i ∈ range k, Q.getD (i + s) 0 :=
  prod_congr rfl (fun i hi => by
    rw [show i + (s + 6) = (i + s) + 6 by ring]
    exact nth_prime_Q (by simp at hi; omega))

theorem nth_prime_22 : nth Nat.Prime 22 = 83 := by
  have := nth_prime_Q (i := 16) (by norm_num)
  rw [show (16 : ℕ) + 6 = 22 from rfl] at this
  rw [this]; decide +kernel

theorem nth_prime_15 : nth Nat.Prime 15 = 53 := by
  have := nth_prime_Q (i := 9) (by norm_num)
  rw [show (9 : ℕ) + 6 = 15 from rfl] at this
  rw [this]; decide +kernel

/-- Proposition 5.6's K, first 22 primes removed, X₂ = exp exp 5.087: K = 32, not 33. -/
theorem K22_eq_32 :
    ((∏ i ∈ range 32, nth Nat.Prime (i + 22) : ℕ) : ℝ) < X2G ∧
      X2G < ((∏ i ∈ range 33, nth Nat.Prime (i + 22) : ℕ) : ℝ) := by
  rw [prodShift_eq (s := 16) (by norm_num), prodShift_eq (s := 16) (by norm_num)]
  constructor
  · set P := ∏ i ∈ range 32, Q.getD (i + 16) 0
    have h1 : ((P ^ 100 : ℕ) : ℝ) < Real.exp (16189 : ℕ) := lt_exp_of_nat (by norm_num) big22lo
    have h2 : Real.exp (16189 : ℕ) = Real.exp 161.89 ^ 100 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h2] at h1
    push_cast at h1
    have h3 : (P : ℝ) < Real.exp 161.89 :=
      (pow_lt_pow_iff_left₀ (by positivity) (Real.exp_pos _).le (by norm_num)).mp h1
    exact h3.trans (Real.exp_lt_exp.mpr exp5087_gt)
  · have h1 := exp_lt_of_nat (by norm_num) big22hi
    exact (Real.exp_lt_exp.mpr exp5087_lt).trans h1

/-- Proposition 5.6's K, first 15 primes removed, X = exp 158: K = 32, not 33. -/
theorem K15_eq_32 :
    ((∏ i ∈ range 32, nth Nat.Prime (i + 15) : ℕ) : ℝ) < Real.exp 158 ∧
      Real.exp 158 < ((∏ i ∈ range 33, nth Nat.Prime (i + 15) : ℕ) : ℝ) := by
  rw [prodShift_eq (s := 9) (by norm_num), prodShift_eq (s := 9) (by norm_num)]
  have h1 := lt_exp_of_nat (by norm_num) big15lo
  have h2 := exp_lt_of_nat (by norm_num) big15hi
  exact ⟨h1, h2⟩

/-- Lemma 3.4 below exp 109: K = 26. -/
theorem K6_eq_26 :
    ((∏ i ∈ range 26, nth Nat.Prime (i + 6) : ℕ) : ℝ) < Real.exp 109 ∧
      Real.exp 109 < ((∏ i ∈ range 27, nth Nat.Prime (i + 6) : ℕ) : ℝ) := by
  rw [prodShift_eq (s := 0) (by norm_num), prodShift_eq (s := 0) (by norm_num)]
  simp only [add_zero]
  have h1 := lt_exp_of_nat (by norm_num) big6lo
  have h2 := exp_lt_of_nat (by norm_num) big6hi
  exact ⟨h1, h2⟩

/-- Product of the first 15 primes. -/
def c15 : ℕ := 614889782588491410
/-- Product of the first 22 primes. -/
def c22 : ℕ := 3217644767340672907899084554130

theorem dvd_c15 : ∀ s, s.Prime → s < 53 → s ∣ c15 := by
  intro s hs hlt
  interval_cases s <;> first | (exfalso; revert hs; norm_num; done) | (norm_num [c15])

theorem dvd_c22 : ∀ s, s.Prime → s < 83 → s ∣ c22 := by
  intro s hs hlt
  interval_cases s <;> first | (exfalso; revert hs; norm_num; done) | (norm_num [c22])

theorem omega22 {η : ℕ} (hsq : Squarefree η) (hcop : Nat.Coprime η c22) (hη : (η : ℝ) < X2G) :
    η.primeFactorsList.length ≤ 32 := by
  apply length_le_of_prod_ge (b := 83) dvd_c22 hsq hcop
    (X := ∏ i ∈ range 33, nth (Pge 83) i) _ le_rfl
  have he : ∏ i ∈ range 33, nth (Pge 83) i = ∏ i ∈ range 33, Q.getD (i + 16) 0 := by
    rw [← nth_prime_22]
    simp only [nth_Pge]
    exact prodShift_eq (s := 16) (by norm_num)
  rw [he]
  have h1 := exp_lt_of_nat (by norm_num) big22hi
  push_cast at h1
  have : (η : ℝ) < ((∏ i ∈ range 33, Q.getD (i + 16) 0 : ℕ) : ℝ) := by
    push_cast
    exact hη.trans ((Real.exp_lt_exp.mpr exp5087_lt).trans h1)
  exact_mod_cast this

theorem omega15 {η : ℕ} (hsq : Squarefree η) (hcop : Nat.Coprime η c15)
    (hη : (η : ℝ) ≤ Real.exp 158) : η.primeFactorsList.length ≤ 32 := by
  apply length_le_of_prod_ge (b := 53) dvd_c15 hsq hcop
    (X := ∏ i ∈ range 33, nth (Pge 53) i) _ le_rfl
  have he : ∏ i ∈ range 33, nth (Pge 53) i = ∏ i ∈ range 33, Q.getD (i + 9) 0 := by
    rw [← nth_prime_15]
    simp only [nth_Pge]
    exact prodShift_eq (s := 9) (by norm_num)
  rw [he]
  have h1 := exp_lt_of_nat (by norm_num) big15hi
  push_cast at h1
  have : (η : ℝ) < ((∏ i ∈ range 33, Q.getD (i + 9) 0 : ℕ) : ℝ) := by
    push_cast
    exact lt_of_le_of_lt hη h1
  exact_mod_cast this

theorem omega6 {η : ℕ} (hsq : Squarefree η) (hcop : Nat.Coprime η 30030)
    (hη : (η : ℝ) < Real.exp 109) : η.primeFactorsList.length ≤ 26 := by
  apply length_le_of_prod hsq hcop (X := ∏ i ∈ range 27, nth P17 i) _ le_rfl
  rw [prodP17_eq (by norm_num)]
  have h1 := exp_lt_of_nat (by norm_num) big6hi
  push_cast at h1
  have : (η : ℝ) < ((∏ i ∈ range 27, Q.getD i 0 : ℕ) : ℝ) := by
    push_cast
    exact hη.trans h1
  exact_mod_cast this

/-! ### Theorem 1.4 from cited inputs -/

open LeanLab.AlmostPrimes in
/-- Cited, under GRH: the sieve range, every even N ≥ X₂ is a prime plus a number with at
most M - 1 = 17 prime factors. -/
def SieveRangeGRH : Prop := ∀ N : ℕ, Even N → X2G ≤ N → PrimePlusAlmostPrime 17 N

/-- Cited, under GRH: Corollary 5.5, first part, N ≥ exp 109. -/
def Cor55a : Prop := ∀ N : ℕ, Even N → Real.exp 109 ≤ N →
  ∃ p η : ℕ, p.Prime ∧ Squarefree η ∧ Nat.Coprime η c15 ∧ N = p + η

/-- Cited, under GRH: Corollary 5.5, second part, N ≥ exp 158. -/
def Cor55b : Prop := ∀ N : ℕ, Even N → Real.exp 158 ≤ N →
  ∃ p η : ℕ, p.Prime ∧ Squarefree η ∧ Nat.Coprime η c22 ∧ N = p + η

theorem exp109_lt_X2 : Real.exp 109 < X2 := by
  unfold X2
  apply Real.exp_lt_exp.mpr
  linarith [exp7816_gt]

theorem four_e18_lt_exp109 : ((4 * 10 ^ 18 : ℕ) : ℝ) < Real.exp 109 := by
  have h := lt_exp_of_nat (P := 4 * 10 ^ 18) (n := 43) (by norm_num) (by decide +kernel)
  have h2 : Real.exp (43 : ℕ) < Real.exp 109 := Real.exp_lt_exp.mpr (by norm_num)
  exact h.trans h2

open LeanLab.AlmostPrimes in
/-- Theorem 1.4 with 32 in place of the printed 33, CONDITIONAL ON the cited inputs, which
carry GRH, and on HJ21 and even Goldbach to 4e18. -/
theorem theorem1_4_32 (hS : SieveRangeGRH) (ha : Cor55a) (hb : Cor55b) (hH : HJ21)
    (hG : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    ∀ N : ℕ, Even N → 4 ≤ N → PrimePlusAlmostPrime 32 N := by
  intro N hN h4
  have pos_of_sq : ∀ η : ℕ, Squarefree η → 0 < η := fun η h =>
    Nat.pos_of_ne_zero (by rintro rfl; exact not_squarefree_zero h)
  by_cases hsmall : N ≤ 4 * 10 ^ 18
  · obtain ⟨p, q, hp, hq, hpq⟩ := hG N hN h4 hsmall
    refine ⟨p, q, hp, hq.pos, hpq.symm, ?_⟩
    simp [bigOmega, Nat.primeFactorsList_prime hq]
  push_neg at hsmall
  by_cases h109 : (N : ℝ) < Real.exp 109
  · obtain ⟨p, η, hp, hsq, _, hcop, hpη⟩ := hH N hN hsmall (h109.trans exp109_lt_X2)
    refine ⟨p, η, hp, pos_of_sq η hsq, hpη, ?_⟩
    have : (η : ℝ) < Real.exp 109 := lt_of_le_of_lt (by exact_mod_cast (by omega : η ≤ N)) h109
    exact (omega6 hsq hcop this).trans (by norm_num)
  push_neg at h109
  by_cases h158 : (N : ℝ) ≤ Real.exp 158
  · obtain ⟨p, η, hp, hsq, hcop, hpη⟩ := ha N hN h109
    refine ⟨p, η, hp, pos_of_sq η hsq, hpη, ?_⟩
    exact omega15 hsq hcop (le_trans (by exact_mod_cast (by omega : η ≤ N)) h158)
  push_neg at h158
  by_cases hX : (N : ℝ) < X2G
  · obtain ⟨p, η, hp, hsq, hcop, hpη⟩ := hb N hN h158.le
    refine ⟨p, η, hp, pos_of_sq η hsq, hpη, ?_⟩
    exact omega22 hsq hcop (lt_of_le_of_lt (by exact_mod_cast (by omega : η ≤ N)) hX)
  push_neg at hX
  exact primePlus_mono (hS N hN hX) (by norm_num)

open LeanLab.AlmostPrimes in
/-- The printed Theorem 1.4, 33, CONDITIONAL ON the same inputs. -/
theorem theorem1_4 (hS : SieveRangeGRH) (ha : Cor55a) (hb : Cor55b) (hH : HJ21)
    (hG : EvenGoldbachUpTo (4 * 10 ^ 18)) :
    ∀ N : ℕ, Even N → 4 ≤ N → PrimePlusAlmostPrime 33 N :=
  fun N hN h4 => primePlus_mono (theorem1_4_32 hS ha hb hH hG N hN h4) (by norm_num)

end LeanLab.JohnstonStarichkova
