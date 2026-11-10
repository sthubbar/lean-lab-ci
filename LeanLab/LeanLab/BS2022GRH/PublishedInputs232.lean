/- AI wrote this Lean code for CODEX task232.
Published analytic inputs for DecompC169b. Goldbach is open. -/
import LeanLab.BS2022GRH.PaperInputs148
import LeanLab.BS2022GRH.ModelC233
import LeanLab.BS2022GRH.Theta332

namespace LeanLab.BS2022GRH.PublishedInputs232
open Real Finset ChenThresholdGRH

/-- LEAF. Journal Lemma 5 p. 1216, Buthe 2014 display 4.6.
The squarefree count is the Mobius square sum. -/
theorem lemma5_mu : PaperInputs148.Lemma5MuJ := by
  sorry

/-- LEAF. Journal Lemma 5 p. 1216, Ramare 2019 Theorem 3.1.
Keep the reciprocal totient weight rather than replacing it by one. -/
theorem lemma5_phi : PaperInputs148.Lemma5PhiJ := by
  sorry

/-- LEAF. Schoenfeld Corollary 1, journal Lemma 1 p. 1215. -/
theorem lemma1_schoenfeld : PaperInputs148.Lemma1J := by
  sorry

/-! ### Private development for `lemma4_robin` (Robin Theorem 11)

`k log k ≤ log P_k` for `k ≥ 52` from the elementary count `π x ≤ x/3 + 5`, and the
finite range `13 ≤ k ≤ 51` by `k^k ≤ P_k`.  No statement, definition or import is
changed; every declaration below is private and used only by `lemma4_robin`. -/

set_option maxRecDepth 200000
set_option maxHeartbeats 8000000

/-! ### A modulus-6 count of the primes -/

/-- At most `N/6 + 1` integers below `N` lie in one fixed residue mod 6. -/
private lemma card_mod_six_le (N r : ℕ) :
    ((Finset.range N).filter (fun n => n % 6 = r)).card ≤ N / 6 + 1 := by
  set S := (Finset.range N).filter (fun n => n % 6 = r) with hS
  have hmap : ∀ a ∈ S, a / 6 ∈ Finset.range (N / 6 + 1) := by
    intro a ha
    simp only [hS, Finset.mem_filter, Finset.mem_range] at ha
    simp only [Finset.mem_range]
    have h : a / 6 ≤ N / 6 := Nat.div_le_div_right (le_of_lt ha.1)
    omega
  have hinj : ∀ a ∈ S, ∀ b ∈ S, a / 6 = b / 6 → a = b := by
    intro a ha b hb hab
    simp only [hS, Finset.mem_filter] at ha hb
    have h1 : a = 6 * (a / 6) + a % 6 := (Nat.div_add_mod a 6).symm
    have h2 : b = 6 * (b / 6) + b % 6 := (Nat.div_add_mod b 6).symm
    rw [h1, h2, ha.2, hb.2, hab]
  have h := Finset.card_le_card_of_injOn (fun n : ℕ => n / 6)
    (fun a ha => hmap a ha) (fun a ha b hb hab => hinj a ha b hb hab)
  simpa using h

/-- A prime bigger than `3` is `1` or `5` modulo `6`. -/
private lemma prime_mod_six {p : ℕ} (hp : p.Prime) (h3 : 3 < p) :
    p % 6 = 1 ∨ p % 6 = 5 := by
  have hp2 : p ≠ 2 := by omega
  have hodd : p % 2 = 1 := by
    rcases hp.eq_two_or_odd with h | h
    · omega
    · simpa [Nat.odd_iff] using h
  have hp3 : p ≠ 3 := by omega
  have h3dvd : ¬ (3 ∣ p) := by
    intro h
    rcases (Nat.dvd_prime hp).mp h with h1 | h1
    · omega
    · omega
  have hmod : (p % 6) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd p (by norm_num : 2 ∣ 6)]
    exact hodd
  have hmod3 : (p % 6) % 3 ≠ 0 := by
    rw [Nat.mod_mod_of_dvd p (by norm_num : 3 ∣ 6)]
    intro h
    exact h3dvd (Nat.dvd_of_mod_eq_zero h)
  have hlt : p % 6 < 6 := Nat.mod_lt _ (by norm_num)
  omega

/-- `π x ≤ x/3 + 5` for `x ≥ 6`. -/
private lemma pi_le_third {x : ℝ} (hx : 6 ≤ x) :
    ((Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) ≤ x / 3 + 5 := by
  set N := ⌊x⌋₊ with hN
  have hN6 : 6 ≤ N := by
    have h : ⌊(6:ℝ)⌋₊ ≤ ⌊x⌋₊ := Nat.floor_mono hx
    simpa using h
  have hNx : (N : ℝ) ≤ x := Nat.floor_le (by linarith)
  set S := Nat.primesLE N with hSdef
  have hScard : (Nat.primeCounting N : ℕ) = S.card := (Nat.primesLE_card_eq_primeCounting N).symm
  have hsplit : S.card = (S.filter (fun p => p ≤ 3)).card
      + (S.filter (fun p => ¬ p ≤ 3)).card := by
    have h := Finset.card_filter_add_card_filter_not (s := S) (p := fun p => p ≤ 3)
    omega
  have hsmall : (S.filter (fun p => p ≤ 3)).card ≤ 2 := by
    have hsub : S.filter (fun p => p ≤ 3) ⊆ ({2, 3} : Finset ℕ) := by
      intro p hp
      rw [Finset.mem_filter, Nat.mem_primesLE] at hp
      obtain ⟨⟨-, hpp⟩, hp3⟩ := hp
      rw [Finset.mem_insert, Finset.mem_singleton]
      have h2 : 2 ≤ p := hpp.two_le
      interval_cases p
      · exact Or.inl rfl
      · exact Or.inr rfl
    have h := Finset.card_le_card hsub
    simpa using h
  have hbig : (S.filter (fun p => ¬ p ≤ 3)).card
      ≤ ((N+1)/6 + 1) + ((N+1)/6 + 1) := by
    have hsub : S.filter (fun p => ¬ p ≤ 3) ⊆
        ((Finset.range (N+1)).filter (fun n => n % 6 = 1)) ∪
        ((Finset.range (N+1)).filter (fun n => n % 6 = 5)) := by
      intro p hp
      rw [Finset.mem_filter, Nat.mem_primesLE] at hp
      obtain ⟨⟨hpN, hpp⟩, hp3⟩ := hp
      simp only [not_le] at hp3
      have hmod := prime_mod_six hpp hp3
      have hpN' : p < N + 1 := by omega
      rcases hmod with h | h
      · refine Finset.mem_union.mpr (Or.inl ?_)
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨hpN', h⟩
      · refine Finset.mem_union.mpr (Or.inr ?_)
        simp only [Finset.mem_filter, Finset.mem_range]
        exact ⟨hpN', h⟩
    have h1 := Finset.card_le_card hsub
    have h2 := Finset.card_union_le ((Finset.range (N+1)).filter (fun n => n % 6 = 1))
      ((Finset.range (N+1)).filter (fun n => n % 6 = 5))
    have h3 := card_mod_six_le (N+1) 1
    have h4 := card_mod_six_le (N+1) 5
    omega
  have hfin : (Nat.primeCounting N : ℕ) ≤ 2 + (((N+1)/6 + 1) + ((N+1)/6 + 1)) := by omega
  have hcast : ((Nat.primeCounting N : ℕ) : ℝ)
      ≤ 2 + (((((N+1)/6 : ℕ)) : ℝ) + 1 + ((((N+1)/6 : ℕ)) : ℝ) + 1) := by
    exact_mod_cast hfin
  have hdiv : (((N+1)/6 : ℕ) : ℝ) ≤ ((N:ℝ)+1)/6 := by
    have h : ((N+1)/6 : ℕ) * 6 ≤ N + 1 := Nat.div_mul_le_self (N+1) 6
    have h' : (((N+1)/6 : ℕ) : ℝ) * 6 ≤ (N:ℝ) + 1 := by exact_mod_cast h
    linarith
  have hgoal : ((Nat.primeCounting N : ℕ) : ℝ) ≤ x/3 + 5 := by nlinarith
  calc ((Nat.primeCounting ⌊x⌋₊ : ℕ) : ℝ) = ((Nat.primeCounting N : ℕ) : ℝ) := by rw [hN]
    _ ≤ x/3 + 5 := hgoal

/-! ### The `n`-th prime -/

private lemma nth_prime_prime (i : ℕ) : (Nat.nth Nat.Prime i).Prime :=
  Nat.nth_mem i (fun hf => absurd hf Nat.infinite_setOfPred_prime)

private lemma count_primes_nth (i : ℕ) : Nat.count Nat.Prime (Nat.nth Nat.Prime i) = i :=
  Nat.count_nth_of_infinite Nat.infinite_setOfPred_prime i

private lemma nth_prime_count (n i : ℕ) (h : Nat.Prime n) (hc : Nat.count Nat.Prime n = i) :
    Nat.nth Nat.Prime i = n := by
  have := Nat.nth_count (p := Nat.Prime) h
  rwa [hc] at this

private lemma nth_prime_0 : Nat.nth Nat.Prime 0 = 2 := nth_prime_count 2 0 (by norm_num) (by decide)
private lemma nth_prime_1 : Nat.nth Nat.Prime 1 = 3 := nth_prime_count 3 1 (by norm_num) (by decide)
private lemma nth_prime_2 : Nat.nth Nat.Prime 2 = 5 := nth_prime_count 5 2 (by norm_num) (by decide)
private lemma nth_prime_3 : Nat.nth Nat.Prime 3 = 7 := nth_prime_count 7 3 (by norm_num) (by decide)
private lemma nth_prime_4 : Nat.nth Nat.Prime 4 = 11 := nth_prime_count 11 4 (by norm_num) (by decide)
private lemma nth_prime_5 : Nat.nth Nat.Prime 5 = 13 := nth_prime_count 13 5 (by norm_num) (by decide)
private lemma nth_prime_6 : Nat.nth Nat.Prime 6 = 17 := nth_prime_count 17 6 (by norm_num) (by decide)
private lemma nth_prime_7 : Nat.nth Nat.Prime 7 = 19 := nth_prime_count 19 7 (by norm_num) (by decide)
private lemma nth_prime_8 : Nat.nth Nat.Prime 8 = 23 := nth_prime_count 23 8 (by norm_num) (by decide)
private lemma nth_prime_9 : Nat.nth Nat.Prime 9 = 29 := nth_prime_count 29 9 (by norm_num) (by decide)
private lemma nth_prime_10 : Nat.nth Nat.Prime 10 = 31 := nth_prime_count 31 10 (by norm_num) (by decide)
private lemma nth_prime_11 : Nat.nth Nat.Prime 11 = 37 := nth_prime_count 37 11 (by norm_num) (by decide)
private lemma nth_prime_12 : Nat.nth Nat.Prime 12 = 41 := nth_prime_count 41 12 (by norm_num) (by decide)
private lemma nth_prime_13 : Nat.nth Nat.Prime 13 = 43 := nth_prime_count 43 13 (by norm_num) (by decide)
private lemma nth_prime_14 : Nat.nth Nat.Prime 14 = 47 := nth_prime_count 47 14 (by norm_num) (by decide)
private lemma nth_prime_15 : Nat.nth Nat.Prime 15 = 53 := nth_prime_count 53 15 (by norm_num) (by decide)
private lemma nth_prime_16 : Nat.nth Nat.Prime 16 = 59 := nth_prime_count 59 16 (by norm_num) (by decide)
private lemma nth_prime_17 : Nat.nth Nat.Prime 17 = 61 := nth_prime_count 61 17 (by norm_num) (by decide)
private lemma nth_prime_18 : Nat.nth Nat.Prime 18 = 67 := nth_prime_count 67 18 (by norm_num) (by decide)
private lemma nth_prime_19 : Nat.nth Nat.Prime 19 = 71 := nth_prime_count 71 19 (by norm_num) (by decide)
private lemma nth_prime_20 : Nat.nth Nat.Prime 20 = 73 := nth_prime_count 73 20 (by norm_num) (by decide)
private lemma nth_prime_21 : Nat.nth Nat.Prime 21 = 79 := nth_prime_count 79 21 (by norm_num) (by decide)
private lemma nth_prime_22 : Nat.nth Nat.Prime 22 = 83 := nth_prime_count 83 22 (by norm_num) (by decide)
private lemma nth_prime_23 : Nat.nth Nat.Prime 23 = 89 := nth_prime_count 89 23 (by norm_num) (by decide)
private lemma nth_prime_24 : Nat.nth Nat.Prime 24 = 97 := nth_prime_count 97 24 (by norm_num) (by decide)
private lemma nth_prime_25 : Nat.nth Nat.Prime 25 = 101 := nth_prime_count 101 25 (by norm_num) (by decide)
private lemma nth_prime_26 : Nat.nth Nat.Prime 26 = 103 := nth_prime_count 103 26 (by norm_num) (by decide)
private lemma nth_prime_27 : Nat.nth Nat.Prime 27 = 107 := nth_prime_count 107 27 (by norm_num) (by decide)
private lemma nth_prime_28 : Nat.nth Nat.Prime 28 = 109 := nth_prime_count 109 28 (by norm_num) (by decide)
private lemma nth_prime_29 : Nat.nth Nat.Prime 29 = 113 := nth_prime_count 113 29 (by norm_num) (by decide)
private lemma nth_prime_30 : Nat.nth Nat.Prime 30 = 127 := nth_prime_count 127 30 (by norm_num) (by decide)
private lemma nth_prime_31 : Nat.nth Nat.Prime 31 = 131 := nth_prime_count 131 31 (by norm_num) (by decide)
private lemma nth_prime_32 : Nat.nth Nat.Prime 32 = 137 := nth_prime_count 137 32 (by norm_num) (by decide)
private lemma nth_prime_33 : Nat.nth Nat.Prime 33 = 139 := nth_prime_count 139 33 (by norm_num) (by decide)
private lemma nth_prime_34 : Nat.nth Nat.Prime 34 = 149 := nth_prime_count 149 34 (by norm_num) (by decide)
private lemma nth_prime_35 : Nat.nth Nat.Prime 35 = 151 := nth_prime_count 151 35 (by norm_num) (by decide)
private lemma nth_prime_36 : Nat.nth Nat.Prime 36 = 157 := nth_prime_count 157 36 (by norm_num) (by decide)
private lemma nth_prime_37 : Nat.nth Nat.Prime 37 = 163 := nth_prime_count 163 37 (by norm_num) (by decide)
private lemma nth_prime_38 : Nat.nth Nat.Prime 38 = 167 := nth_prime_count 167 38 (by norm_num) (by decide)
private lemma nth_prime_39 : Nat.nth Nat.Prime 39 = 173 := nth_prime_count 173 39 (by norm_num) (by decide)
private lemma nth_prime_40 : Nat.nth Nat.Prime 40 = 179 := nth_prime_count 179 40 (by norm_num) (by decide)
private lemma nth_prime_41 : Nat.nth Nat.Prime 41 = 181 := nth_prime_count 181 41 (by norm_num) (by decide)
private lemma nth_prime_42 : Nat.nth Nat.Prime 42 = 191 := nth_prime_count 191 42 (by norm_num) (by decide)
private lemma nth_prime_43 : Nat.nth Nat.Prime 43 = 193 := nth_prime_count 193 43 (by norm_num) (by decide)
private lemma nth_prime_44 : Nat.nth Nat.Prime 44 = 197 := nth_prime_count 197 44 (by norm_num) (by decide)
private lemma nth_prime_45 : Nat.nth Nat.Prime 45 = 199 := nth_prime_count 199 45 (by norm_num) (by decide)
private lemma nth_prime_46 : Nat.nth Nat.Prime 46 = 211 := nth_prime_count 211 46 (by norm_num) (by decide)
private lemma nth_prime_47 : Nat.nth Nat.Prime 47 = 223 := nth_prime_count 223 47 (by norm_num) (by decide)
private lemma nth_prime_48 : Nat.nth Nat.Prime 48 = 227 := nth_prime_count 227 48 (by norm_num) (by decide)
private lemma nth_prime_49 : Nat.nth Nat.Prime 49 = 229 := nth_prime_count 229 49 (by norm_num) (by decide)
private lemma nth_prime_50 : Nat.nth Nat.Prime 50 = 233 := nth_prime_count 233 50 (by norm_num) (by decide)
private lemma nth_prime_51 : Nat.nth Nat.Prime 51 = 239 := nth_prime_count 239 51 (by norm_num) (by decide)



private lemma primorial_succ (k : ℕ) :
    (∏ i ∈ Finset.range (k+1), Nat.nth Nat.Prime i) = (∏ i ∈ Finset.range k, Nat.nth Nat.Prime i) * Nat.nth Nat.Prime k := by
  simp only [Finset.prod_range_succ]

private lemma two_le_primorial (k : ℕ) : 2 ^ k ≤ (∏ i ∈ Finset.range k, Nat.nth Nat.Prime i) := by
  have h2 : ∀ i ∈ Finset.range k, 2 ≤ Nat.nth Nat.Prime i :=
    fun i _ => (nth_prime_prime i).two_le
  calc 2 ^ k = ∏ _i ∈ Finset.range k, 2 := by simp
    _ ≤ ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i := Finset.prod_le_prod h2


/-- Every `k`-element set of primes has product at least `(∏ i ∈ Finset.range k, Nat.nth Nat.Prime i)`. -/
private lemma primorial_le_prod_aux (n : ℕ) :
    ∀ (S : Finset ℕ), S.card = n → (∀ p ∈ S, p.Prime) → (∏ i ∈ Finset.range S.card, Nat.nth Nat.Prime i) ≤ ∏ p ∈ S, p := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro S hcard hS
    subst hcard
    rcases Finset.eq_empty_or_nonempty S with rfl | hne
    · simp
    · set M := S.max' hne with hM
      have hMS : M ∈ S := Finset.max'_mem S hne
      have hcard' : (S.erase M).card = S.card - 1 := Finset.card_erase_of_mem hMS
      have hSe : ∀ p ∈ S.erase M, p.Prime := fun p hp => hS p (Finset.mem_of_mem_erase hp)
      have hpos : 0 < S.card := Finset.card_pos.mpr hne
      have ih' : (∏ i ∈ Finset.range (S.erase M).card, Nat.nth Nat.Prime i) ≤ ∏ p ∈ S.erase M, p :=
        ih (S.erase M).card (by omega) (S.erase M) rfl hSe
      rw [hcard'] at ih'
      have hMge : Nat.nth Nat.Prime (S.card - 1) ≤ M := by
        by_contra hlt
        push_neg at hlt
        have hsub : S ⊆ (Finset.range (Nat.nth Nat.Prime (S.card - 1))).filter Nat.Prime := by
          intro p hp
          simp only [Finset.mem_filter, Finset.mem_range]
          refine ⟨lt_of_le_of_lt ?_ hlt, hS p hp⟩
          rw [hM]
          exact Finset.le_max' S p hp
        have hc1 : S.card ≤ ((Finset.range (Nat.nth Nat.Prime (S.card - 1))).filter
            Nat.Prime).card := Finset.card_le_card hsub
        have hc2 : ((Finset.range (Nat.nth Nat.Prime (S.card - 1))).filter Nat.Prime).card
            = S.card - 1 := by
          rw [← Nat.count_eq_card_filter_range, count_primes_nth]
        omega
      have hnot : M ∉ S.erase M := by simp
      have hprod : ∏ p ∈ S, p = (∏ p ∈ S.erase M, p) * M := by
        conv_lhs => rw [← Finset.insert_erase hMS]
        rw [Finset.prod_insert hnot]
        exact mul_comm M (∏ p ∈ S.erase M, p)
      have hsplit : (∏ i ∈ Finset.range S.card, Nat.nth Nat.Prime i)
          = (∏ i ∈ Finset.range (S.card - 1), Nat.nth Nat.Prime i) * Nat.nth Nat.Prime (S.card - 1) := by
        conv_lhs => rw [show S.card = (S.card - 1) + 1 by omega]
        exact primorial_succ (S.card - 1)
      rw [hprod, hsplit]
      exact mul_le_mul ih' (by rw [hM]; exact hMge) (by positivity) (by positivity)

private lemma primorial_le_prod (S : Finset ℕ) (hS : ∀ p ∈ S, p.Prime) :
    (∏ i ∈ Finset.range S.card, Nat.nth Nat.Prime i) ≤ ∏ p ∈ S, p :=
  primorial_le_prod_aux S.card S rfl hS

/-- `(∏ i ∈ Finset.range (ω n), Nat.nth Nat.Prime i) ≤ n` for `n ≠ 0`. -/
private lemma primorial_card_primeFactors_le {n : ℕ} (hn : n ≠ 0) :
    (∏ i ∈ Finset.range n.primeFactors.card, Nat.nth Nat.Prime i) ≤ n := by
  have h1 : (∏ i ∈ Finset.range n.primeFactors.card, Nat.nth Nat.Prime i) ≤ ∏ p ∈ n.primeFactors, p :=
    primorial_le_prod _ (fun p hp => (Nat.mem_primeFactors.mp hp).1)
  have h2 : ∏ p ∈ n.primeFactors, p ∣ n := Nat.prod_primeFactors_dvd n
  have h3 : ∏ p ∈ n.primeFactors, p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn) h2
  linarith


/-- `log log x / log x ≤ 1/e` for `x > 1`. -/
private lemma loglog_div_log_le_inv_e {x : ℝ} (hx : 1 < x) :
    Real.log (Real.log x) / Real.log x ≤ 1 / Real.exp 1 := by
  have hlog : 0 < Real.log x := Real.log_pos hx
  have h2 : Real.log (Real.log x) ≤ Real.log x / Real.exp 1 := by
    have h3 : Real.log (Real.log x) ≤ Real.exp (Real.log (Real.log x) - 1) := by
      have h4 := Real.add_one_le_exp (Real.log (Real.log x) - 1)
      linarith
    have h5 : Real.exp (Real.log (Real.log x) - 1) = Real.log x / Real.exp 1 := by
      rw [Real.exp_sub, Real.exp_log hlog]
    linarith
  rw [div_le_iff₀ hlog]
  have h6 : Real.log x / Real.exp 1 = (1 / Real.exp 1) * Real.log x := by ring
  linarith [h6 ▸ h2]

/-- `x ↦ log log x / log x` is antitone on `[e^e, ∞)`. -/
private lemma loglog_div_log_antitone :
    AntitoneOn (fun x : ℝ => Real.log (Real.log x) / Real.log x)
      (Set.Ici (Real.exp (Real.exp 1))) := by
  have hE1 : (1:ℝ) < Real.exp 1 := by
    have := Real.add_one_le_exp (1:ℝ); linarith
  have hEE : (1:ℝ) < Real.exp (Real.exp 1) := by
    calc (1:ℝ) < Real.exp 1 := hE1
      _ ≤ Real.exp (Real.exp 1) := Real.exp_le_exp.mpr hE1.le
  have hlogx : ContinuousOn (fun x : ℝ => Real.log x) (Set.Ici (Real.exp (Real.exp 1))) := by
    apply Real.continuousOn_log.mono
    intro x hx
    have hx1 : (1:ℝ) < x := lt_of_lt_of_le hEE hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  have hloglog : ContinuousOn (fun x : ℝ => Real.log (Real.log x))
      (Set.Ici (Real.exp (Real.exp 1))) := by
    apply ContinuousOn.log hlogx
    intro x hx
    have hx1 : (1:ℝ) < x := lt_of_lt_of_le hEE hx
    exact ne_of_gt (Real.log_pos hx1)
  have hcont : ContinuousOn (fun x : ℝ => Real.log (Real.log x) / Real.log x)
      (Set.Ici (Real.exp (Real.exp 1))) := by
    apply ContinuousOn.div hloglog hlogx
    intro x hx
    have hx1 : (1:ℝ) < x := lt_of_lt_of_le hEE hx
    exact ne_of_gt (Real.log_pos hx1)
  have hdiff : DifferentiableOn ℝ (fun x : ℝ => Real.log (Real.log x) / Real.log x)
      (interior (Set.Ici (Real.exp (Real.exp 1)))) := by
    intro x hx
    rw [interior_Ici] at hx
    have hx1 : (1:ℝ) < x := lt_of_lt_of_le hEE hx.le
    have hlx : 0 < Real.log x := Real.log_pos hx1
    have h1 : HasDerivAt (fun y : ℝ => Real.log y) x⁻¹ x := hasDerivAt_log (by linarith)
    have h2 : HasDerivAt (fun y : ℝ => Real.log (Real.log y))
        (x⁻¹ / Real.log x) x := h1.log (ne_of_gt hlx)
    exact (h2.div h1 (ne_of_gt hlx)).differentiableAt.differentiableWithinAt
  refine antitoneOn_of_deriv_nonpos (convex_Ici _) hcont hdiff (fun x hx => ?_)
  rw [interior_Ici] at hx
  have hx1 : (1:ℝ) < x := lt_of_lt_of_le hEE hx.le
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hloglog1 : (1:ℝ) ≤ Real.log (Real.log x) := by
    have h2 : Real.exp 1 ≤ Real.log x := by
      have h := Real.log_le_log (Real.exp_pos (Real.exp 1)) hx.le
      rwa [Real.log_exp] at h
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log (Real.log x) := Real.log_le_log (Real.exp_pos 1) h2
  have h1 : HasDerivAt (fun y : ℝ => Real.log y) x⁻¹ x := hasDerivAt_log (by linarith)
  have h2 : HasDerivAt (fun y : ℝ => Real.log (Real.log y)) (x⁻¹ / Real.log x) x :=
    h1.log (ne_of_gt hlx)
  have h3 : HasDerivAt (fun y : ℝ => Real.log (Real.log y) / Real.log y)
      ((x⁻¹ / Real.log x * Real.log x - Real.log (Real.log x) * x⁻¹) / (Real.log x)^2) x :=
    h2.div h1 (ne_of_gt hlx)
  rw [h3.deriv]
  have heq : (x⁻¹ / Real.log x * Real.log x - Real.log (Real.log x) * x⁻¹) / (Real.log x)^2
      = (1 - Real.log (Real.log x)) / (x * (Real.log x)^2) := by
    field_simp
    try ring
  rw [heq]
  have hden : (0:ℝ) < x * (Real.log x)^2 := by positivity
  apply div_nonpos_of_nonpos_of_nonneg _ hden.le
  linarith

/-- `e^e ≤ 16`. -/
private lemma exp_exp_one_le_sixteen : Real.exp (Real.exp 1) ≤ 16 := by
  have h1 : Real.exp 1 ≤ 2.72 := by
    have := Real.exp_one_lt_d9; linarith
  have h2 : Real.exp (Real.exp 1) ≤ Real.exp 2.72 := Real.exp_le_exp.mpr h1
  have h3 : Real.exp 2.72 ≤ Real.exp (Real.log 16) := by
    apply Real.exp_le_exp.mpr
    have h4 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16:ℝ) = 2^4 by norm_num, Real.log_pow]; push_cast; ring
    rw [h4]
    have h5 := Real.log_two_gt_d9
    linarith
  have h6 : Real.exp (Real.log 16) = 16 := Real.exp_log (by norm_num)
  linarith [h2, h3]

/-- The (∏ i ∈ Finset.range bound, Nat.nth Nat.Prime i) at `k ≥ 4` gives `e^e ≤ (∏ i ∈ Finset.range k, Nat.nth Nat.Prime i)`. -/
private lemma exp_exp_one_le_primorial {k : ℕ} (hk : 4 ≤ k) :
    Real.exp (Real.exp 1) ≤ ((∏ i ∈ Finset.range k, Nat.nth Nat.Prime i) : ℝ) := by
  have h1 : Real.exp (Real.exp 1) ≤ 16 := exp_exp_one_le_sixteen
  have h2 : (16:ℕ) ≤ (∏ i ∈ Finset.range k, Nat.nth Nat.Prime i) := by
    have h3 : (16:ℕ) = 2^4 := by norm_num
    rw [h3]
    exact le_trans (Nat.pow_le_pow_right (by norm_num) hk) (two_le_primorial k)
  have h4 : (16:ℝ) ≤ ((∏ i ∈ Finset.range k, Nat.nth Nat.Prime i) : ℝ) := by exact_mod_cast h2
  linarith

/-! ### The first primes and the first primorials -/

private lemma primorial_four : (∏ i ∈ Finset.range 4, Nat.nth Nat.Prime i) = 210 := by
  simp only [Finset.prod_range_succ, Finset.prod_range_zero,
    nth_prime_0, nth_prime_1, nth_prime_2, nth_prime_3]
  norm_num
private lemma primorial_five : (∏ i ∈ Finset.range 5, Nat.nth Nat.Prime i) = 2310 := by
  rw [show (5:ℕ) = 4+1 by norm_num, primorial_succ, primorial_four, nth_prime_4]
private lemma primorial_six : (∏ i ∈ Finset.range 6, Nat.nth Nat.Prime i) = 30030 := by
  rw [show (6:ℕ) = 5+1 by norm_num, primorial_succ, primorial_five, nth_prime_5]
private lemma primorial_seven : (∏ i ∈ Finset.range 7, Nat.nth Nat.Prime i) = 510510 := by
  rw [show (7:ℕ) = 6+1 by norm_num, primorial_succ, primorial_six, nth_prime_6]
private lemma primorial_eight : (∏ i ∈ Finset.range 8, Nat.nth Nat.Prime i) = 9699690 := by
  rw [show (8:ℕ) = 7+1 by norm_num, primorial_succ, primorial_seven, nth_prime_7]
private lemma primorial_nine : (∏ i ∈ Finset.range 9, Nat.nth Nat.Prime i) = 223092870 := by
  rw [show (9:ℕ) = 8+1 by norm_num, primorial_succ, primorial_eight, nth_prime_8]


/-! ### Rigorous bounds for `exp` and `log` -/

/-- `exp m ≤ 2.7182818286^m` for natural `m`. -/
private lemma exp_nat_le (m : ℕ) : Real.exp (m:ℝ) ≤ 2.7182818286^m := by
  have h1 : Real.exp ((m:ℕ):ℝ) = Real.exp 1 ^ m := by
    rw [show ((m:ℕ):ℝ) = (m:ℝ) * 1 by ring, Real.exp_nat_mul]
  rw [h1]
  exact pow_le_pow_left₀ (le_of_lt (Real.exp_pos 1)) (le_of_lt Real.exp_one_lt_d9) m

/-- `2.7182818283^m ≤ exp m` for natural `m`. -/
private lemma exp_nat_ge (m : ℕ) : 2.7182818283^m ≤ Real.exp (m:ℝ) := by
  have h1 : Real.exp ((m:ℕ):ℝ) = Real.exp 1 ^ m := by
    rw [show ((m:ℕ):ℝ) = (m:ℝ) * 1 by ring, Real.exp_nat_mul]
  rw [h1]
  exact pow_le_pow_left₀ (by norm_num) (le_of_lt Real.exp_one_gt_d9) m

/-- Taylor upper bound for `exp` on `[0,1]`, 12 terms, error `10⁻⁸`. -/
private lemma exp_frac_le {f : ℝ} (h0 : 0 ≤ f) (h1 : f ≤ 1) :
    Real.exp f ≤ (∑ m ∈ Finset.range 12, f^m/(m.factorial : ℝ)) + 1/10^8 := by
  have habs : |f| ≤ 1 := by rw [abs_of_nonneg h0]; exact h1
  have hb := Real.exp_bound (x := f) habs (n := 12) (by norm_num)
  have herr : |f|^12 * ((13:ℝ) / ((Nat.factorial 12 : ℝ) * 12)) ≤ 1/10^8 := by
    have h2 : |f|^12 ≤ 1 := by
      have := pow_le_pow_left₀ (abs_nonneg f) habs 12
      simpa using this
    have h3 : (0:ℝ) ≤ (13:ℝ) / ((Nat.factorial 12 : ℝ) * 12) := by positivity
    calc |f|^12 * ((13:ℝ) / ((Nat.factorial 12 : ℝ) * 12))
        ≤ 1 * ((13:ℝ) / ((Nat.factorial 12 : ℝ) * 12)) := by
          exact mul_le_mul_of_nonneg_right h2 h3
      _ ≤ 1/10^8 := by norm_num
  have h4 := abs_le.mp hb
  linarith [h4.2, herr]

/-! ### `L ↦ log L / L` is antitone on `[e, ∞)` -/


private lemma log_div_self_antitone :
    AntitoneOn (fun L : ℝ => Real.log L / L) (Set.Ici (Real.exp 1)) := by
  have he : (1:ℝ) < Real.exp 1 := by
    have h := Real.add_one_le_exp (1:ℝ); linarith
  have hcont : ContinuousOn (fun L : ℝ => Real.log L / L) (Set.Ici (Real.exp 1)) := by
    refine ContinuousOn.div ?_ continuousOn_id ?_
    · apply Real.continuousOn_log.mono
      intro x hx
      have hx1 : (1:ℝ) < x := lt_of_lt_of_le he hx
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      linarith
    · intro x hx
      exact ne_of_gt (lt_of_lt_of_le (Real.exp_pos 1) hx)
  have hdiff : DifferentiableOn ℝ (fun L : ℝ => Real.log L / L)
      (interior (Set.Ici (Real.exp 1))) := by
    intro L hL
    rw [interior_Ici] at hL
    have hLpos : (0:ℝ) < L := lt_trans (Real.exp_pos 1) hL
    have h1 : HasDerivAt (fun y : ℝ => Real.log y) L⁻¹ L := hasDerivAt_log (ne_of_gt hLpos)
    have h2 : HasDerivAt (fun y : ℝ => y) 1 L := hasDerivAt_id L
    exact (h1.div h2 (ne_of_gt hLpos)).differentiableAt.differentiableWithinAt
  refine antitoneOn_of_deriv_nonpos (convex_Ici _) hcont hdiff (fun L hL => ?_)
  rw [interior_Ici] at hL
  have hLpos : (0:ℝ) < L := lt_trans (Real.exp_pos 1) hL
  have h1 : HasDerivAt (fun y : ℝ => Real.log y) L⁻¹ L := hasDerivAt_log (ne_of_gt hLpos)
  have h2 : HasDerivAt (fun y : ℝ => y) 1 L := hasDerivAt_id L
  have h3 : HasDerivAt (fun y : ℝ => Real.log y / y) ((L⁻¹ * L - Real.log L * 1)/L^2) L :=
    h1.div h2 (ne_of_gt hLpos)
  rw [h3.deriv]
  have heq : (L⁻¹ * L - Real.log L * 1)/L^2 = (1 - Real.log L)/L^2 := by
    field_simp
    try ring
  rw [heq]
  have hlog : 1 ≤ Real.log L := by
    have h4 : Real.exp 1 ≤ L := le_of_lt hL
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ ≤ Real.log L := Real.log_le_log (Real.exp_pos 1) h4
  apply div_nonpos_of_nonpos_of_nonneg _ (by positivity)
  linarith

/-- If `exp c ≤ P` and `log c ≤ d` then the Robin ratio at `P` is at most `k·d/c`. -/
private lemma robin_ratio_le {k : ℕ} {P c d : ℝ} (hexp : Real.exp c ≤ P) (hce : Real.exp 1 ≤ c)
    (hlogc : Real.log c ≤ d) :
    (k:ℝ) * (Real.log (Real.log P) / Real.log P) ≤ (k:ℝ) * (d / c) := by
  have hcpos : (0:ℝ) < c := lt_of_lt_of_le (Real.exp_pos 1) hce
  have hlogP : c ≤ Real.log P := by
    have h1 : Real.log (Real.exp c) ≤ Real.log P := Real.log_le_log (Real.exp_pos c) hexp
    rwa [Real.log_exp] at h1
  have hPge : Real.exp 1 ≤ Real.log P := le_trans hce hlogP
  have hanti := log_div_self_antitone hce hPge hlogP
  have h1 : Real.log (Real.log P) / Real.log P ≤ d / c := by
    refine le_trans hanti ?_
    exact div_le_div_of_nonneg_right hlogc hcpos.le
  exact mul_le_mul_of_nonneg_left h1 (by positivity)


/-- `exp (m + f) ≤ P` for `0 ≤ f ≤ 1` from a rational check. -/

private lemma exp_add_frac_le {m : ℕ} {f : ℝ} (h0 : 0 ≤ f) (h1 : f ≤ 1) {P : ℕ}
    (h : 2.7182818286^m * ((∑ i ∈ Finset.range 12, f^i/(i.factorial : ℝ)) + 1/10^8)
      ≤ (P:ℝ)) :
    Real.exp ((m:ℝ) + f) ≤ (P:ℝ) := by
  rw [Real.exp_add]
  have h1' : Real.exp (m:ℝ) ≤ 2.7182818286^m := exp_nat_le m
  have h2' : Real.exp f ≤ (∑ i ∈ Finset.range 12, f^i/(i.factorial : ℝ)) + 1/10^8 :=
    exp_frac_le h0 h1
  calc Real.exp (m:ℝ) * Real.exp f
      ≤ 2.7182818286^m * ((∑ i ∈ Finset.range 12, f^i/(i.factorial : ℝ)) + 1/10^8) :=
        mul_le_mul h1' h2' (by linarith [Real.exp_pos f]) (by positivity)
    _ ≤ (P:ℝ) := h

/-- `c ≤ exp (m + f)` for `0 ≤ f` from a rational check. -/
private lemma le_exp_add_frac {m : ℕ} {f : ℝ} (h0 : 0 ≤ f) {c : ℝ}
    (h : c ≤ 2.7182818283^m * (∑ i ∈ Finset.range 12, f^i/(i.factorial : ℝ))) :
    c ≤ Real.exp ((m:ℝ) + f) := by
  rw [Real.exp_add]
  have h1' : (2.7182818283:ℝ)^m ≤ Real.exp (m:ℝ) := exp_nat_ge m
  have h2' : (∑ i ∈ Finset.range 12, f^i/(i.factorial : ℝ)) ≤ Real.exp f :=
    Real.sum_le_exp_of_nonneg h0 12
  have h3 : (0:ℝ) ≤ (∑ i ∈ Finset.range 12, f^i/(i.factorial : ℝ)) := by positivity
  calc c ≤ 2.7182818283^m * (∑ i ∈ Finset.range 12, f^i/(i.factorial : ℝ)) := h
    _ ≤ Real.exp (m:ℝ) * Real.exp f :=
        mul_le_mul h1' h2' h3 (by linarith [Real.exp_pos (m:ℝ)])

/-! ### The six (∏ i ∈ Finset.range instances, Nat.nth Nat.Prime i) -/


private theorem robin_four :
    (4:ℝ) * (Real.log (Real.log (∏ i ∈ Finset.range 4, (Nat.nth Nat.Prime i : ℝ))) / Real.log (∏ i ∈ Finset.range 4, (Nat.nth Nat.Prime i : ℝ))) < 1.3841 := by
  have hP : (∏ i ∈ Finset.range 4, (Nat.nth Nat.Prime i : ℝ)) = 210 := by
    have h := primorial_four
    have h' : (((∏ i ∈ Finset.range 4, Nat.nth Nat.Prime i) : ℕ) : ℝ) = ((210:ℕ):ℝ) :=
      by rw [h]
    simpa using h'
  rw [hP]
  have hexp : Real.exp 5 ≤ (210:ℝ) := by
    refine le_trans (exp_nat_le 5) ?_
    norm_num
  have hc : Real.exp 1 ≤ (5:ℝ) := by
    have h := Real.exp_one_lt_d9; linarith
  have hlogc : Real.log (5:ℝ) ≤ 1.61 := by
    have h := Real.log_five_lt_d9; linarith
  have h := robin_ratio_le (k := 4) hexp hc hlogc
  have h2 : (4:ℝ) * ((1.61:ℝ)/5) < 1.3841 := by norm_num
  linarith

private theorem robin_five :
    (5:ℝ) * (Real.log (Real.log (∏ i ∈ Finset.range 5, (Nat.nth Nat.Prime i : ℝ))) / Real.log (∏ i ∈ Finset.range 5, (Nat.nth Nat.Prime i : ℝ))) < 1.3841 := by
  have hP : (∏ i ∈ Finset.range 5, (Nat.nth Nat.Prime i : ℝ)) = 2310 := by
    have h := primorial_five
    have h' : (((∏ i ∈ Finset.range 5, Nat.nth Nat.Prime i) : ℕ) : ℝ) = ((2310:ℕ):ℝ) :=
      by rw [h]
    simpa using h'
  rw [hP]
  have hexp : Real.exp (72/10 : ℝ) ≤ (2310:ℝ) := by
    have hsplit : Real.exp (72/10 : ℝ) = Real.exp 7 * Real.exp (2/10 : ℝ) := by
      rw [← Real.exp_add]; norm_num
    rw [hsplit]
    have h1 : Real.exp 7 ≤ 2.7182818286^7 := exp_nat_le 7
    have h2 : Real.exp (2/10 : ℝ) ≤ 1.2215 := by
      refine le_trans (exp_frac_le (f := 2/10) (by norm_num) (by norm_num)) ?_
      norm_num
    calc Real.exp 7 * Real.exp (2/10 : ℝ) ≤ 2.7182818286^7 * 1.2215 := by
          exact mul_le_mul h1 h2 (by linarith [Real.exp_pos (2/10:ℝ)])
            (by positivity)
      _ ≤ 2310 := by norm_num
  have hc : Real.exp 1 ≤ (72/10:ℝ) := by
    have h := Real.exp_one_lt_d9; linarith
  have hlogc : Real.log (72/10:ℝ) ≤ 1.9740810269 := by
    have h2 := Real.log_two_lt_d9
    have h3 := Real.log_three_lt_d9
    have h5 := Real.log_five_gt_d9
    have hrw : Real.log (72/10:ℝ) = 2 * Real.log 2 + 2 * Real.log 3 - Real.log 5 := by
      have e1 : (72/10:ℝ) = 36/5 := by norm_num
      rw [e1, Real.log_div (by norm_num) (by norm_num)]
      have e2 : Real.log (36:ℝ) = 2 * Real.log 6 := by
        rw [show (36:ℝ) = 6^2 by norm_num, Real.log_pow]; push_cast; ring
      have e3 : Real.log (6:ℝ) = Real.log 2 + Real.log 3 := by
        rw [show (6:ℝ) = 2*3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
      linarith
    rw [hrw]
    linarith
  have h := robin_ratio_le (k := 5) hexp hc hlogc
  have h2 : (5:ℝ) * ((1.9740810269:ℝ)/(72/10)) < 1.3841 := by norm_num
  linarith

private theorem robin_six :
    (6:ℝ) * (Real.log (Real.log (∏ i ∈ Finset.range 6, (Nat.nth Nat.Prime i : ℝ))) / Real.log (∏ i ∈ Finset.range 6, (Nat.nth Nat.Prime i : ℝ))) < 1.3841 := by
  have hP : (∏ i ∈ Finset.range 6, (Nat.nth Nat.Prime i : ℝ)) = 30030 := by
    have h := primorial_six
    have h' : (((∏ i ∈ Finset.range 6, Nat.nth Nat.Prime i) : ℕ) : ℝ) = ((30030:ℕ):ℝ) :=
      by rw [h]
    simpa using h'
  rw [hP]
  have hexp : Real.exp 10 ≤ (30030:ℝ) := by
    refine le_trans (exp_nat_le 10) ?_
    norm_num
  have hc : Real.exp 1 ≤ (10:ℝ) := by
    have h := Real.exp_one_lt_d9; linarith
  have hlogc : Real.log (10:ℝ) ≤ 2.3025850934 := by
    have h2 := Real.log_two_lt_d9
    have h5 := Real.log_five_lt_d9
    have hrw : Real.log (10:ℝ) = Real.log 2 + Real.log 5 := by
      rw [show (10:ℝ) = 2*5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    rw [hrw]; linarith
  have h := robin_ratio_le (k := 6) hexp hc hlogc
  have h2 : (6:ℝ) * ((2.3025850934:ℝ)/10) < 1.3841 := by norm_num
  linarith

private theorem robin_seven :
    (7:ℝ) * (Real.log (Real.log (∏ i ∈ Finset.range 7, (Nat.nth Nat.Prime i : ℝ))) / Real.log (∏ i ∈ Finset.range 7, (Nat.nth Nat.Prime i : ℝ))) < 1.3841 := by
  have hP : (∏ i ∈ Finset.range 7, (Nat.nth Nat.Prime i : ℝ)) = 510510 := by
    have h := primorial_seven
    have h' : (((∏ i ∈ Finset.range 7, Nat.nth Nat.Prime i) : ℕ) : ℝ) = ((510510:ℕ):ℝ) :=
      by rw [h]
    simpa using h'
  rw [hP]
  have hexp : Real.exp (1296/100 : ℝ) ≤ (510510:ℝ) := by
    have hsplit : Real.exp (1296/100 : ℝ) = Real.exp 12 * Real.exp (96/100 : ℝ) := by
      rw [← Real.exp_add]; norm_num
    rw [hsplit]
    have h1 : Real.exp 12 ≤ 2.7182818286^12 := exp_nat_le 12
    have h2 : Real.exp (96/100 : ℝ) ≤ 2.6117 := by
      refine le_trans (exp_frac_le (f := 96/100) (by norm_num) (by norm_num)) ?_
      norm_num
    calc Real.exp 12 * Real.exp (96/100 : ℝ) ≤ 2.7182818286^12 * 2.6117 := by
          exact mul_le_mul h1 h2 (by linarith [Real.exp_pos (96/100:ℝ)]) (by positivity)
      _ ≤ 510510 := by norm_num
  have hc : Real.exp 1 ≤ (1296/100:ℝ) := by
    have h := Real.exp_one_lt_d9; linarith
  have hlogc : Real.log (1296/100:ℝ) ≤ 2.5618676922 := by
    have h2 := Real.log_two_lt_d9
    have h3 := Real.log_three_lt_d9
    have h5 := Real.log_five_gt_d9
    have hrw : Real.log (1296/100:ℝ) = 4 * Real.log 6 - 2 * Real.log 10 := by
      have e1 : (1296/100:ℝ) = 6^4 / 10^2 := by norm_num
      rw [e1, Real.log_div (by norm_num) (by norm_num), Real.log_pow, Real.log_pow]
      push_cast
      ring
    have e6 : Real.log (6:ℝ) = Real.log 2 + Real.log 3 := by
      rw [show (6:ℝ) = 2*3 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    have e10 : Real.log (10:ℝ) = Real.log 2 + Real.log 5 := by
      rw [show (10:ℝ) = 2*5 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    rw [hrw, e6, e10]
    linarith
  have h := robin_ratio_le (k := 7) hexp hc hlogc
  have h2 : (7:ℝ) * ((2.5618676922:ℝ)/(1296/100)) < 1.3841 := by norm_num
  linarith

private theorem robin_eight :
    (8:ℝ) * (Real.log (Real.log (∏ i ∈ Finset.range 8, (Nat.nth Nat.Prime i : ℝ))) / Real.log (∏ i ∈ Finset.range 8, (Nat.nth Nat.Prime i : ℝ))) < 1.3841 := by
  have hP : (∏ i ∈ Finset.range 8, (Nat.nth Nat.Prime i : ℝ)) = 9699690 := by
    have h := primorial_eight
    have h' : (((∏ i ∈ Finset.range 8, Nat.nth Nat.Prime i) : ℕ) : ℝ) = ((9699690:ℕ):ℝ) :=
      by rw [h]
    simpa using h'
  rw [hP]
  have hexp : Real.exp (1605/100 : ℝ) ≤ (9699690:ℝ) := by
    have hsplit : Real.exp (1605/100 : ℝ) = Real.exp 16 * Real.exp (5/100 : ℝ) := by
      rw [← Real.exp_add]; norm_num
    rw [hsplit]
    have h1 : Real.exp 16 ≤ 2.7182818286^16 := exp_nat_le 16
    have h2 : Real.exp (5/100 : ℝ) ≤ 1.0513 := by
      refine le_trans (exp_frac_le (f := 5/100) (by norm_num) (by norm_num)) ?_
      norm_num
    calc Real.exp 16 * Real.exp (5/100 : ℝ) ≤ 2.7182818286^16 * 1.0513 := by
          exact mul_le_mul h1 h2 (by linarith [Real.exp_pos (5/100:ℝ)]) (by positivity)
      _ ≤ 9699690 := by norm_num
  have hc : Real.exp 1 ≤ (1605/100:ℝ) := by
    have h := Real.exp_one_lt_d9; linarith
  have hlogc : Real.log (1605/100:ℝ) ≤ 2.776 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have hsplit : Real.exp (2.776 : ℝ) = Real.exp 2 * Real.exp (0.776 : ℝ) := by
      rw [← Real.exp_add]; norm_num
    rw [hsplit]
    have h1 : (2.7182818283:ℝ)^2 ≤ Real.exp 2 := exp_nat_ge 2
    have h2 : (∑ m ∈ Finset.range 12, ((0.776:ℝ)^m/(m.factorial : ℝ)))
        ≤ Real.exp (0.776 : ℝ) := Real.sum_le_exp_of_nonneg (by norm_num) 12
    have h3 : (2.7182818283:ℝ)^2 * (∑ m ∈ Finset.range 12, ((0.776:ℝ)^m/(m.factorial : ℝ)))
        ≥ 1605/100 := by norm_num
    calc (1605/100 : ℝ) ≤ (2.7182818283:ℝ)^2 *
          (∑ m ∈ Finset.range 12, ((0.776:ℝ)^m/(m.factorial : ℝ))) := by linarith
      _ ≤ Real.exp 2 * Real.exp (0.776 : ℝ) := by
          exact mul_le_mul h1 h2 (by positivity) (by linarith [Real.exp_pos (2:ℝ)])
  have h := robin_ratio_le (k := 8) hexp hc hlogc
  have h2 : (8:ℝ) * ((2.776:ℝ)/(1605/100)) < 1.3841 := by norm_num
  linarith

private theorem robin_nine :
    (9:ℝ) * (Real.log (Real.log (∏ i ∈ Finset.range 9, (Nat.nth Nat.Prime i : ℝ))) / Real.log (∏ i ∈ Finset.range 9, (Nat.nth Nat.Prime i : ℝ))) < 1.3841 := by
  have hP : (∏ i ∈ Finset.range 9, (Nat.nth Nat.Prime i : ℝ)) = 223092870 := by
    have h := primorial_nine
    have h' : (((∏ i ∈ Finset.range 9, Nat.nth Nat.Prime i) : ℕ) : ℝ) = ((223092870:ℕ):ℝ) :=
      by rw [h]
    simpa using h'
  rw [hP]
  have hexp : Real.exp (19222/1000 : ℝ) ≤ (223092870:ℝ) := by
    have hsplit : Real.exp (19222/1000 : ℝ) = Real.exp 19 * Real.exp (222/1000 : ℝ) := by
      rw [← Real.exp_add]; norm_num
    rw [hsplit]
    have h1 : Real.exp 19 ≤ 2.7182818286^19 := exp_nat_le 19
    have h2 : Real.exp (222/1000 : ℝ) ≤ 1.2486 := by
      refine le_trans (exp_frac_le (f := 222/1000) (by norm_num) (by norm_num)) ?_
      norm_num
    calc Real.exp 19 * Real.exp (222/1000 : ℝ) ≤ 2.7182818286^19 * 1.2486 := by
          exact mul_le_mul h1 h2 (by linarith [Real.exp_pos (222/1000:ℝ)]) (by positivity)
      _ ≤ 223092870 := by norm_num
  have hc : Real.exp 1 ≤ (19222/1000:ℝ) := by
    have h := Real.exp_one_lt_d9; linarith
  have hlogc : Real.log (19222/1000:ℝ) ≤ 2.9561 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have hsplit : Real.exp (2.9561 : ℝ) = Real.exp 2 * Real.exp (0.9561 : ℝ) := by
      rw [← Real.exp_add]; norm_num
    rw [hsplit]
    have h1 : (2.7182818283:ℝ)^2 ≤ Real.exp 2 := exp_nat_ge 2
    have h2 : (∑ m ∈ Finset.range 12, ((0.9561:ℝ)^m/(m.factorial : ℝ)))
        ≤ Real.exp (0.9561 : ℝ) := Real.sum_le_exp_of_nonneg (by norm_num) 12
    have h3 : (2.7182818283:ℝ)^2 *
        (∑ m ∈ Finset.range 12, ((0.9561:ℝ)^m/(m.factorial : ℝ))) ≥ 19222/1000 := by
      norm_num
    calc (19222/1000 : ℝ) ≤ (2.7182818283:ℝ)^2 *
          (∑ m ∈ Finset.range 12, ((0.9561:ℝ)^m/(m.factorial : ℝ))) := by linarith
      _ ≤ Real.exp 2 * Real.exp (0.9561 : ℝ) := by
          exact mul_le_mul h1 h2 (by positivity) (by linarith [Real.exp_pos (2:ℝ)])
  have h := robin_ratio_le (k := 9) hexp hc hlogc
  have h2 : (9:ℝ) * ((2.9561:ℝ)/(19222/1000)) < 1.3841 := by norm_num
  linarith


/-- **Reduction of `lemma4_robin` (Robin Theorem 11), bounded form.**
If `k·log log P_k/log P_k < 1.3841` for `4 ≤ k ≤ K`, then every `n ≥ 3` with `ω n ≤ K`
satisfies `ω(n) < 1.3841·log n/log log n`.  Only two inputs about `n` are used:
`n ≥ P_{ω(n)}` and the monotonicity of `log log x/log x` beyond `eᵉ`. -/
private theorem robin_of_primorial_le (K : ℕ)
    (hP : ∀ k : ℕ, 4 ≤ k → k ≤ K →
      (k : ℝ) * (Real.log (Real.log ((∏ i ∈ Finset.range k, Nat.nth Nat.Prime i) : ℝ)) / Real.log ((∏ i ∈ Finset.range k, Nat.nth Nat.Prime i) : ℝ))
        < 1.3841) :
    ∀ n : ℕ, 3 ≤ n → n.primeFactors.card ≤ K →
      (n.primeFactors.card : ℝ) < 1.3841 * Real.log n / Real.log (Real.log n) := by
  intro n hn hK
  have hn0 : n ≠ 0 := by omega
  have hn1 : (1:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 1 < n)
  have hlog : 0 < Real.log (n:ℝ) := Real.log_pos hn1
  have hexp1 : (1:ℝ) < Real.log (n:ℝ) := by
    have h2 : Real.exp 1 < (n:ℝ) := by
      have h3 : (2.72 : ℝ) < (n:ℝ) := by
        have h4 : (3:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
        linarith
      linarith [Real.exp_one_lt_d9]
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log (n:ℝ) := Real.log_lt_log (Real.exp_pos 1) h2
  have hloglog : 0 < Real.log (Real.log (n:ℝ)) := Real.log_pos hexp1
  have hratio_nonneg : (0:ℝ) ≤ Real.log (Real.log (n:ℝ)) / Real.log (n:ℝ) := by positivity
  have key : (n.primeFactors.card : ℝ) *
      (Real.log (Real.log (n:ℝ)) / Real.log (n:ℝ)) < 1.3841 := by
    by_cases hk3 : n.primeFactors.card ≤ 3
    · have h2 : Real.log (Real.log (n:ℝ)) / Real.log (n:ℝ) ≤ 1 / Real.exp 1 :=
        loglog_div_log_le_inv_e hn1
      have h3 : (n.primeFactors.card : ℝ) ≤ 3 := by exact_mod_cast hk3
      have h4 : (3:ℝ) * (1 / Real.exp 1) < 1.3841 := by
        have h5 : Real.exp 1 > 2.7 := by linarith [Real.exp_one_gt_d9]
        have h6 : (1:ℝ) / Real.exp 1 < 1 / 2.7 := by
          apply one_div_lt_one_div_of_lt (by norm_num : (0:ℝ) < 2.7) h5
        nlinarith
      nlinarith [h2, h3, h4, hratio_nonneg]
    · push_neg at hk3
      have hk4 : 4 ≤ n.primeFactors.card := hk3
      have hprim : (∏ i ∈ Finset.range n.primeFactors.card, Nat.nth Nat.Prime i) ≤ n := primorial_card_primeFactors_le hn0
      have hbig : Real.exp (Real.exp 1) ≤ ((∏ i ∈ Finset.range n.primeFactors.card, Nat.nth Nat.Prime i) : ℝ) :=
        exp_exp_one_le_primorial hk4
      have hnmem : (n:ℝ) ∈ Set.Ici (Real.exp (Real.exp 1)) := by
        refine le_trans hbig ?_
        exact_mod_cast hprim
      have hanti := loglog_div_log_antitone hbig hnmem (by exact_mod_cast hprim)
      have hPk := hP n.primeFactors.card hk4 hK
      have hkpos : (0:ℝ) ≤ (n.primeFactors.card : ℝ) := by positivity
      nlinarith [hanti, hPk, hkpos, hratio_nonneg]
  rw [lt_div_iff₀ hloglog]
  have he : (n.primeFactors.card : ℝ) *
        (Real.log (Real.log (n:ℝ)) / Real.log (n:ℝ)) * Real.log (n:ℝ)
      = (n.primeFactors.card : ℝ) * Real.log (Real.log (n:ℝ)) := by
    field_simp
  nlinarith [key, hlog, he]



/-! ### `π` of the `n`-th prime and a lower bound for it -/

private lemma pi_nth (n : ℕ) : Nat.primeCounting (Nat.nth Nat.Prime n) = n + 1 := by
  rw [Nat.primeCounting_eq_primeCounting'_succ]
  show Nat.count Nat.Prime (Nat.nth Nat.Prime n + 1) = n + 1
  rw [Nat.count_succ, count_primes_nth]
  simp [nth_prime_prime n]

/-- `3 (n - 4) ≤ nth Prime n`. -/
private lemma nth_lower (n : ℕ) (hn : 5 ≤ n) :
    (3:ℝ) * ((n:ℝ) - 4) ≤ (Nat.nth Nat.Prime n : ℝ) := by
  have h2 : (6:ℕ) ≤ Nat.nth Nat.Prime n := by
    have h1 : n + 2 ≤ Nat.nth Nat.Prime n := Nat.add_two_le_nth_prime n
    omega
  have h6 : (6:ℝ) ≤ (Nat.nth Nat.Prime n : ℝ) := by exact_mod_cast h2
  have h3 := pi_le_third (x := (Nat.nth Nat.Prime n : ℝ)) h6
  rw [Nat.floor_natCast] at h3
  have h4 : ((Nat.primeCounting (Nat.nth Nat.Prime n) : ℕ) : ℝ) = (n:ℝ) + 1 := by
    rw [pi_nth]; push_cast; ring
  rw [h4] at h3
  linarith

/-- `log 10 > 2.3024`. -/
private lemma log_ten_gt : (2.3024 : ℝ) < Real.log 10 := by
  have h1 : Real.log (1024:ℝ) = 10 * Real.log 2 := by
    rw [show (1024:ℝ) = 2^10 by norm_num, Real.log_pow]; norm_num
  have h2 : Real.log (1000:ℝ) = 3 * Real.log 10 := by
    rw [show (1000:ℝ) = 10^3 by norm_num, Real.log_pow]; norm_num
  have h3 : Real.log (1024:ℝ) = Real.log 1000 + Real.log (1024/1000) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h4 : Real.log (1024/1000:ℝ) ≤ 1024/1000 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h5 := Real.log_two_gt_d9
  linarith

/-- `log` of the product of the first `k` primes. -/
private lemma log_prod_primes (k : ℕ) :
    Real.log ((∏ i ∈ Finset.range k, Nat.nth Nat.Prime i : ℕ) : ℝ)
      = ∑ i ∈ Finset.range k, Real.log (Nat.nth Nat.Prime i : ℝ) := by
  have hne : ∀ i ∈ Finset.range k, ((Nat.nth Nat.Prime i : ℕ) : ℝ) ≠ 0 := by
    intro i _
    have := (nth_prime_prime i).pos
    positivity
  have h1 : ((∏ i ∈ Finset.range k, Nat.nth Nat.Prime i : ℕ) : ℝ)
      = ∏ i ∈ Finset.range k, ((Nat.nth Nat.Prime i : ℕ) : ℝ) := by push_cast; ring
  rw [h1, Real.log_prod hne]

/-- `log P_52 ≥ 221`. -/
private lemma base52 : (221:ℝ) ≤ ∑ i ∈ Finset.range 52, Real.log (Nat.nth Nat.Prime i : ℝ) := by
  have hP : (10:ℕ)^96 ≤ ∏ i ∈ Finset.range 52, Nat.nth Nat.Prime i := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, nth_prime_0, nth_prime_1,
      nth_prime_2, nth_prime_3, nth_prime_4, nth_prime_5, nth_prime_6, nth_prime_7,
      nth_prime_8, nth_prime_9, nth_prime_10, nth_prime_11, nth_prime_12, nth_prime_13,
      nth_prime_14, nth_prime_15, nth_prime_16, nth_prime_17, nth_prime_18, nth_prime_19,
      nth_prime_20, nth_prime_21, nth_prime_22, nth_prime_23, nth_prime_24, nth_prime_25,
      nth_prime_26, nth_prime_27, nth_prime_28, nth_prime_29, nth_prime_30, nth_prime_31,
      nth_prime_32, nth_prime_33, nth_prime_34, nth_prime_35, nth_prime_36, nth_prime_37,
      nth_prime_38, nth_prime_39, nth_prime_40, nth_prime_41, nth_prime_42, nth_prime_43,
      nth_prime_44, nth_prime_45, nth_prime_46, nth_prime_47, nth_prime_48, nth_prime_49,
      nth_prime_50, nth_prime_51]
    norm_num
  have hcast : (((10:ℕ)^96 : ℕ) : ℝ)
      ≤ ((∏ i ∈ Finset.range 52, Nat.nth Nat.Prime i : ℕ) : ℝ) := by exact_mod_cast hP
  have hlog := Real.log_le_log (by positivity) hcast
  have h96 : Real.log ((((10:ℕ)^96 : ℕ) : ℝ)) = 96 * Real.log 10 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]; push_cast; ring
  rw [h96] at hlog
  rw [← log_prod_primes 52]
  have h10 := log_ten_gt
  linarith

/-- The `k`-fold logarithmic bound: `k log k` against `(k-5) log (k-5)`. -/
private lemma key_log1 {k : ℝ} (hk : 52 ≤ k) :
    k * Real.log k ≤ (k - 5) * Real.log (k - 5) + 5 * Real.log k + 5.6 := by
  have h5 : (0:ℝ) < k - 5 := by linarith
  have hk0 : (0:ℝ) < k := by linarith
  have h1 : Real.log k = Real.log (k - 5) + Real.log (k/(k-5)) := by
    rw [← Real.log_mul (ne_of_gt h5) (by positivity)]
    congr 1
    field_simp
  have h2 : Real.log (k/(k-5)) ≤ k/(k-5) - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h3 : k/(k-5) - 1 = 5/(k-5) := by field_simp; ring
  have h4 : 5/(k-5) ≤ 5/47 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
  have hmul : k * Real.log k ≤ k * Real.log (k - 5) + k * (5/(k-5)) := by
    have hb : Real.log k ≤ Real.log (k-5) + 5/(k-5) := by linarith
    calc k * Real.log k ≤ k * (Real.log (k-5) + 5/(k-5)) :=
          mul_le_mul_of_nonneg_left hb hk0.le
      _ = k * Real.log (k - 5) + k * (5/(k-5)) := by ring
  have hkq : k * (5/(k-5)) ≤ 5 + 25/47 := by
    have h : k * (5/(k-5)) = 5 + 25/(k-5) := by field_simp; ring
    rw [h]
    have h6 : 25/(k-5) ≤ 25/47 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith
  have hsplit : k * Real.log (k - 5) = (k - 5) * Real.log (k - 5) + 5 * Real.log (k - 5) := by
    ring
  have hmono : Real.log (k - 5) ≤ Real.log k := Real.log_le_log h5 (by linarith)
  nlinarith [hmul, hkq, hsplit, hmono, hk0]

/-- Concavity bound for `log k` at `k = 52`. -/
private lemma key_log2 {k : ℝ} (hk : 52 ≤ k) :
    5 * Real.log k ≤ 5 * Real.log 52 + 5 * ((k - 52)/52) := by
  have h1 : Real.log k = Real.log 52 + Real.log (k/52) := by
    rw [← Real.log_mul (by norm_num) (by positivity)]
    congr 1
    field_simp
  have h2 : Real.log (k/52) ≤ k/52 - 1 := Real.log_le_sub_one_of_pos (by positivity)
  have h3 : k/52 - 1 = (k - 52)/52 := by rw [div_sub_one (by norm_num)]
  linarith


private lemma log47_le : Real.log 47 ≤ 3.851 := by
  have h1 : Real.log 48 = 4 * Real.log 2 + Real.log 3 := by
    rw [show (48:ℝ) = 2^4 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast; ring
  have h2 : Real.log 47 = Real.log 48 + Real.log (47/48) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h3 : Real.log (47/48) ≤ 47/48 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h4 := Real.log_two_lt_d9
  have h5 := Real.log_three_lt_d9
  linarith

private lemma log52_le : Real.log 52 ≤ 3.96 := by
  have h1 : Real.log 52 = 2 * Real.log 2 + Real.log 13 := by
    rw [show (52:ℝ) = 2^2 * 13 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast; ring
  have h2 : Real.log 13 = Real.log 12 + Real.log (13/12) := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]; norm_num
  have h3 : Real.log 12 = 2 * Real.log 2 + Real.log 3 := by
    rw [show (12:ℝ) = 2^2 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_pow]
    push_cast; ring
  have h4 : Real.log (13/12) ≤ 13/12 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
  have h5 := Real.log_two_lt_d9
  have h6 := Real.log_three_lt_d9
  linarith

/-- The integral comparison `∫_{47}^{k-5} log ≤ Σ_{j<k-52} log (j+48)`. -/
private lemma integral_le_sum (k : ℕ) (hk : 52 ≤ k) :
    ∫ t in (47:ℝ)..((k:ℝ) - 5), Real.log t
      ≤ ∑ j ∈ Finset.range (k - 52), Real.log ((j:ℝ) + 48) := by
  have h := MonotoneOn.integral_le_sum_Ico (f := Real.log) (a := 47) (b := k - 5)
      (by omega) (Real.strictMonoOn_log.monotoneOn.mono (by
    intro x hx
    exact Set.mem_Ioi.mpr (lt_of_lt_of_le (by norm_num) hx.1)))
  have hcast : ((k - 5 : ℕ) : ℝ) = (k:ℝ) - 5 := by
    have h5 : (5:ℕ) ≤ k := by omega
    push_cast [h5]; ring
  rw [hcast] at h
  have h2 : ∑ x ∈ Finset.Ico 47 (k - 5), Real.log ((x:ℝ) + 1)
      = ∑ j ∈ Finset.range (k - 52), Real.log ((j:ℝ) + 48) := by
    rw [show k - 5 = 47 + (k - 52) by omega, Finset.sum_Ico_eq_sum_range]
    rw [show 47 + (k - 52) - 47 = k - 52 by omega]
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    push_cast
    ring
  simp only [Nat.cast_add, Nat.cast_one] at h
  rw [h2] at h
  exact h

/-- The tail: `k log k ≤ log P_k` for `k ≥ 52`. -/
private lemma tail_ge (k : ℕ) (hk : 52 ≤ k) :
    (k:ℝ) * Real.log (k:ℝ)
      ≤ Real.log ((∏ i ∈ Finset.range k, Nat.nth Nat.Prime i : ℕ) : ℝ) := by
  have hlog := log_prod_primes k
  have hsplit : (∑ i ∈ Finset.range k, Real.log (Nat.nth Nat.Prime i : ℝ))
      = (∑ i ∈ Finset.range 52, Real.log (Nat.nth Nat.Prime i : ℝ))
        + ∑ j ∈ Finset.range (k - 52), Real.log (Nat.nth Nat.Prime (52 + j) : ℝ) := by
    conv_lhs => rw [show k = 52 + (k - 52) by omega]
    rw [Finset.sum_range_add]
  set B := ∑ i ∈ Finset.range 52, Real.log (Nat.nth Nat.Prime i : ℝ) with hB
  have hBge : (221:ℝ) ≤ B := base52
  have hterm : ∀ j ∈ Finset.range (k - 52),
      Real.log 3 + Real.log ((j:ℝ) + 48) ≤ Real.log (Nat.nth Nat.Prime (52 + j) : ℝ) := by
    intro j hj
    have h1 : (3:ℝ) * ((j:ℝ) + 48) ≤ (Nat.nth Nat.Prime (52 + j) : ℝ) := by
      have h2 := nth_lower (52 + j) (by omega)
      have h3 : ((52 + j : ℕ) : ℝ) - 4 = (j:ℝ) + 48 := by push_cast; ring
      linarith
    have h4 : (0:ℝ) < 3 * ((j:ℝ) + 48) := by positivity
    have h5 : Real.log (3 * ((j:ℝ) + 48)) ≤ Real.log (Nat.nth Nat.Prime (52 + j) : ℝ) :=
      Real.log_le_log h4 h1
    rw [Real.log_mul (by norm_num) (by positivity)] at h5
    linarith
  have hsumge : ((k - 52 : ℕ) : ℝ) * Real.log 3
      + ∑ j ∈ Finset.range (k - 52), Real.log ((j:ℝ) + 48)
      ≤ ∑ j ∈ Finset.range (k - 52), Real.log (Nat.nth Nat.Prime (52 + j) : ℝ) := by
    have h1 := Finset.sum_le_sum hterm
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range] at h1
    simpa using h1
  have hInt := integral_le_sum k hk
  have hIval : ∫ t in (47:ℝ)..((k:ℝ) - 5), Real.log t
      = ((k:ℝ) - 5) * Real.log ((k:ℝ) - 5) - 47 * Real.log 47 - ((k:ℝ) - 5) + 47 :=
    integral_log
  have hk52 : ((k - 52 : ℕ) : ℝ) = (k:ℝ) - 52 := by
    have h : (52:ℕ) ≤ k := by omega
    push_cast [h]; ring
  have hK1 := key_log1 (k := (k:ℝ)) (by exact_mod_cast hk)
  have hK2 := key_log2 (k := (k:ℝ)) (by exact_mod_cast hk)
  have h47 := log47_le
  have h52 := log52_le
  have h3 := Real.log_three_gt_d9
  have hmul : ((k:ℝ) - 52) * 1.0986 ≤ ((k:ℝ) - 52) * Real.log 3 :=
    mul_le_mul_of_nonneg_left (le_of_lt (lt_trans (by norm_num) h3)) (by linarith)
  have key : (k:ℝ) * Real.log (k:ℝ) ≤ B + ((k:ℝ) - 52) * Real.log 3
      + (((k:ℝ) - 5) * Real.log ((k:ℝ) - 5) - 47 * Real.log 47 - ((k:ℝ) - 5) + 47) := by
    linarith only [hK1, hK2, hBge, h47, h52, hmul]
  calc (k:ℝ) * Real.log (k:ℝ)
      ≤ B + ((k:ℝ) - 52) * Real.log 3
        + (((k:ℝ) - 5) * Real.log ((k:ℝ) - 5) - 47 * Real.log 47 - ((k:ℝ) - 5) + 47) := key
    _ = B + ((k:ℝ) - 52) * Real.log 3 + ∫ t in (47:ℝ)..((k:ℝ) - 5), Real.log t := by
        rw [hIval]
    _ ≤ B + ((k:ℝ) - 52) * Real.log 3
        + ∑ j ∈ Finset.range (k - 52), Real.log ((j:ℝ) + 48) := by linarith only [hInt]
    _ ≤ B + ∑ j ∈ Finset.range (k - 52), Real.log (Nat.nth Nat.Prime (52 + j) : ℝ) := by
        have hcast2 : ((k - 52 : ℕ) : ℝ) * Real.log 3 = ((k:ℝ) - 52) * Real.log 3 := by
          rw [hk52]
        linarith only [hsumge, hcast2]
    _ = Real.log ((∏ i ∈ Finset.range k, Nat.nth Nat.Prime i : ℕ) : ℝ) := by
        rw [hlog, hsplit]



/-! ### The finite range `13 ≤ k ≤ 51` -/

private lemma head_pow (k : ℕ) (h13 : 13 ≤ k) (h51 : k ≤ 51) :
    k ^ k ≤ ∏ i ∈ Finset.range k, Nat.nth Nat.Prime i := by
  interval_cases k <;>
    (simp only [Finset.prod_range_succ, Finset.prod_range_zero, nth_prime_0, nth_prime_1, nth_prime_2, nth_prime_3, nth_prime_4, nth_prime_5, nth_prime_6, nth_prime_7, nth_prime_8, nth_prime_9, nth_prime_10, nth_prime_11, nth_prime_12, nth_prime_13, nth_prime_14, nth_prime_15, nth_prime_16, nth_prime_17, nth_prime_18, nth_prime_19, nth_prime_20, nth_prime_21, nth_prime_22, nth_prime_23, nth_prime_24, nth_prime_25, nth_prime_26, nth_prime_27, nth_prime_28, nth_prime_29, nth_prime_30, nth_prime_31, nth_prime_32, nth_prime_33, nth_prime_34, nth_prime_35, nth_prime_36, nth_prime_37, nth_prime_38, nth_prime_39, nth_prime_40, nth_prime_41, nth_prime_42, nth_prime_43, nth_prime_44, nth_prime_45, nth_prime_46, nth_prime_47, nth_prime_48, nth_prime_49, nth_prime_50]; norm_num)

/-- `k log k ≤ log P_k` for `k ≥ 13`. -/
private lemma htail (k : ℕ) (hk : 13 ≤ k) :
    (k:ℝ) * Real.log (k:ℝ)
      ≤ Real.log ((∏ i ∈ Finset.range k, Nat.nth Nat.Prime i : ℕ) : ℝ) := by
  by_cases h : k ≤ 51
  · have hp := head_pow k hk h
    have hcast : (((k:ℕ)^k : ℕ) : ℝ)
        ≤ ((∏ i ∈ Finset.range k, Nat.nth Nat.Prime i : ℕ) : ℝ) := by exact_mod_cast hp
    have hpos : (0:ℝ) < (((k:ℕ)^k : ℕ) : ℝ) := by
      have h0 : (0:ℕ) < k ^ k := pow_pos (by omega) k
      exact_mod_cast h0
    have hlog := Real.log_le_log hpos hcast
    have hpow : Real.log ((((k:ℕ)^k : ℕ) : ℝ)) = (k:ℝ) * Real.log (k:ℝ) := by
      rw [Nat.cast_pow, Real.log_pow]
    rw [hpow] at hlog
    exact hlog
  · push_neg at h
    exact tail_ge k (by omega)

/-! ### The Robin ratio for `k ≥ 13` -/

private lemma log_thirteen_ge : (2.5:ℝ) ≤ Real.log 13 := by
  have hexp : Real.exp (2.5:ℝ) ≤ 13 := by
    have hsplit : Real.exp (2.5:ℝ) = Real.exp 2 * Real.exp (0.5:ℝ) := by
      rw [← Real.exp_add]; norm_num
    rw [hsplit]
    have h1 : Real.exp 2 ≤ 2.7182818286^2 := exp_nat_le 2
    have h2 : Real.exp (0.5:ℝ) ≤ 1.6488 := by
      refine le_trans (exp_frac_le (f := 0.5) (by norm_num) (by norm_num)) ?_
      norm_num
    calc Real.exp 2 * Real.exp (0.5:ℝ) ≤ 2.7182818286^2 * 1.6488 :=
          mul_le_mul h1 h2 (by linarith [Real.exp_pos (0.5:ℝ)]) (by positivity)
      _ ≤ 13 := by norm_num
  have h := Real.log_le_log (Real.exp_pos (2.5:ℝ)) hexp
  rwa [Real.log_exp] at h

private lemma ratio_high (k : ℕ) (hk : 13 ≤ k) :
    (k:ℝ) * (Real.log (Real.log (∏ i ∈ Finset.range k, (Nat.nth Nat.Prime i : ℝ)))
      / Real.log (∏ i ∈ Finset.range k, (Nat.nth Nat.Prime i : ℝ))) < 1.3841 := by
  set P := (∏ i ∈ Finset.range k, (Nat.nth Nat.Prime i : ℝ)) with hP
  have hA : (k:ℝ) * Real.log (k:ℝ) ≤ Real.log P := by
    rw [hP]; simpa using htail k hk
  have hk13 : (13:ℝ) ≤ (k:ℝ) := by exact_mod_cast hk
  have hkpos : (0:ℝ) < (k:ℝ) := by linarith
  have hk1 : (1:ℝ) < (k:ℝ) := by linarith
  have hlogk : (1:ℝ) < Real.log (k:ℝ) := by
    have h2 : Real.exp 1 < (k:ℝ) := by
      have h3 : (2.72:ℝ) < (k:ℝ) := by linarith
      linarith [Real.exp_one_lt_d9]
    calc (1:ℝ) = Real.log (Real.exp 1) := (Real.log_exp 1).symm
      _ < Real.log (k:ℝ) := Real.log_lt_log (Real.exp_pos 1) h2
  have hlog13 : (2.5:ℝ) ≤ Real.log (k:ℝ) :=
    le_trans log_thirteen_ge (Real.log_le_log (by norm_num) hk13)
  have hAe : Real.exp 1 ≤ (k:ℝ) * Real.log (k:ℝ) := by
    have h : (13:ℝ) * 2.5 ≤ (k:ℝ) * Real.log (k:ℝ) :=
      mul_le_mul hk13 hlog13 (by norm_num) hkpos.le
    linarith [Real.exp_one_lt_d9]
  have hPge : Real.exp 1 ≤ Real.log P := le_trans hAe hA
  have hanti := log_div_self_antitone hAe hPge hA
  have hstep : (k:ℝ) * (Real.log (Real.log P) / Real.log P)
      ≤ (k:ℝ) * (Real.log ((k:ℝ) * Real.log (k:ℝ)) / ((k:ℝ) * Real.log (k:ℝ))) :=
    mul_le_mul_of_nonneg_left hanti hkpos.le
  have hval : (k:ℝ) * (Real.log ((k:ℝ) * Real.log (k:ℝ)) / ((k:ℝ) * Real.log (k:ℝ)))
      = 1 + Real.log (Real.log (k:ℝ)) / Real.log (k:ℝ) := by
    have h1 : Real.log ((k:ℝ) * Real.log (k:ℝ))
        = Real.log (k:ℝ) + Real.log (Real.log (k:ℝ)) := by
      rw [Real.log_mul (ne_of_gt hkpos) (ne_of_gt (Real.log_pos hk1))]
    rw [h1]
    field_simp
  have hle := loglog_div_log_le_inv_e hk1
  have he : (1:ℝ) + 1/Real.exp 1 < 1.3841 := by
    have h2 : (2.7:ℝ) < Real.exp 1 := by linarith [Real.exp_one_gt_d9]
    have h3 : (1:ℝ)/Real.exp 1 ≤ 1/2.7 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num) h2.le
    have h4 : (1:ℝ) + 1/2.7 < 1.3841 := by norm_num
    linarith
  calc (k:ℝ) * (Real.log (Real.log P) / Real.log P)
      ≤ (k:ℝ) * (Real.log ((k:ℝ) * Real.log (k:ℝ)) / ((k:ℝ) * Real.log (k:ℝ))) := hstep
    _ = 1 + Real.log (Real.log (k:ℝ)) / Real.log (k:ℝ) := hval
    _ ≤ 1 + 1/Real.exp 1 := by linarith
    _ < 1.3841 := he



/-- The Robin ratio at `k = 10` (where `k^k > P_k`). -/
private lemma ratio_10 :
    (10:ℝ) * (Real.log (Real.log ((∏ i ∈ Finset.range 10, Nat.nth Nat.Prime i : ℝ)))
      / Real.log (∏ i ∈ Finset.range 10, (Nat.nth Nat.Prime i : ℝ))) < 1.3841 := by
  have hP : (∏ i ∈ Finset.range 10, (Nat.nth Nat.Prime i : ℝ)) = 6469693230 := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, nth_prime_0, nth_prime_1, nth_prime_2, nth_prime_3, nth_prime_4, nth_prime_5, nth_prime_6, nth_prime_7, nth_prime_8, nth_prime_9, nth_prime_10, nth_prime_11]
    norm_num
  rw [hP]
  have hexp : Real.exp (22.58:ℝ) ≤ (6469693230:ℝ) := by
    have hsplit : Real.exp (22.58:ℝ) = Real.exp 22 * Real.exp (0.58:ℝ) := by
      rw [← Real.exp_add]; norm_num
    rw [hsplit]
    have h1 : Real.exp (22:ℝ) ≤ 2.7182818286^22 := exp_nat_le 22
    have h2 : Real.exp (0.58:ℝ) ≤ 1.7861 := by
      refine le_trans (exp_frac_le (f := 0.58) (by norm_num) (by norm_num)) ?_
      norm_num
    calc Real.exp 22 * Real.exp (0.58:ℝ) ≤ 2.7182818286^22 * 1.7861 :=
          mul_le_mul h1 h2 (by linarith [Real.exp_pos (0.58:ℝ)]) (by positivity)
      _ ≤ 6469693230 := by norm_num
  have hc : Real.exp 1 ≤ (22.58:ℝ) := by have h := Real.exp_one_lt_d9; linarith
  have hlogc : Real.log (22.58:ℝ) ≤ 3.1202 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have hsplit : Real.exp (3.1202:ℝ) = Real.exp 3 * Real.exp (0.1202:ℝ) := by
      rw [← Real.exp_add]; norm_num
    rw [hsplit]
    have h1 : (2.7182818283:ℝ)^3 ≤ Real.exp 3 := exp_nat_ge 3
    have h2 : (∑ m ∈ Finset.range 12, ((0.1202:ℝ)^m/(m.factorial : ℝ)))
        ≤ Real.exp (0.1202:ℝ) := Real.sum_le_exp_of_nonneg (by norm_num) 12
    have h3 : (2.7182818283:ℝ)^3 *
        (∑ m ∈ Finset.range 12, ((0.1202:ℝ)^m/(m.factorial : ℝ))) ≥ (22.58:ℝ) := by norm_num
    calc (22.58:ℝ) ≤ _ := by linarith
      _ ≤ Real.exp 3 * Real.exp (0.1202:ℝ) :=
          mul_le_mul h1 h2 (by positivity) (by linarith [Real.exp_pos (3:ℝ)])
  have h := robin_ratio_le (k := 10) hexp hc hlogc
  have h2 : (10:ℝ) * ((3.1202:ℝ)/(22.58:ℝ)) < 1.3841 := by norm_num
  linarith

/-- The Robin ratio at `k = 11` (where `k^k > P_k`). -/
private lemma ratio_11 :
    (11:ℝ) * (Real.log (Real.log ((∏ i ∈ Finset.range 11, Nat.nth Nat.Prime i : ℝ)))
      / Real.log (∏ i ∈ Finset.range 11, (Nat.nth Nat.Prime i : ℝ))) < 1.3841 := by
  have hP : (∏ i ∈ Finset.range 11, (Nat.nth Nat.Prime i : ℝ)) = 200560490130 := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, nth_prime_0, nth_prime_1, nth_prime_2, nth_prime_3, nth_prime_4, nth_prime_5, nth_prime_6, nth_prime_7, nth_prime_8, nth_prime_9, nth_prime_10, nth_prime_11]
    norm_num
  rw [hP]
  have hexp : Real.exp (25.9:ℝ) ≤ (200560490130:ℝ) := by
    have hsplit : Real.exp (25.9:ℝ) = Real.exp 25 * Real.exp (0.9:ℝ) := by
      rw [← Real.exp_add]; norm_num
    rw [hsplit]
    have h1 : Real.exp (25:ℝ) ≤ 2.7182818286^25 := exp_nat_le 25
    have h2 : Real.exp (0.9:ℝ) ≤ 2.4597 := by
      refine le_trans (exp_frac_le (f := 0.9) (by norm_num) (by norm_num)) ?_
      norm_num
    calc Real.exp 25 * Real.exp (0.9:ℝ) ≤ 2.7182818286^25 * 2.4597 :=
          mul_le_mul h1 h2 (by linarith [Real.exp_pos (0.9:ℝ)]) (by positivity)
      _ ≤ 200560490130 := by norm_num
  have hc : Real.exp 1 ≤ (25.9:ℝ) := by have h := Real.exp_one_lt_d9; linarith
  have hlogc : Real.log (25.9:ℝ) ≤ 3.2565 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have hsplit : Real.exp (3.2565:ℝ) = Real.exp 3 * Real.exp (0.2565:ℝ) := by
      rw [← Real.exp_add]; norm_num
    rw [hsplit]
    have h1 : (2.7182818283:ℝ)^3 ≤ Real.exp 3 := exp_nat_ge 3
    have h2 : (∑ m ∈ Finset.range 12, ((0.2565:ℝ)^m/(m.factorial : ℝ)))
        ≤ Real.exp (0.2565:ℝ) := Real.sum_le_exp_of_nonneg (by norm_num) 12
    have h3 : (2.7182818283:ℝ)^3 *
        (∑ m ∈ Finset.range 12, ((0.2565:ℝ)^m/(m.factorial : ℝ))) ≥ (25.9:ℝ) := by norm_num
    calc (25.9:ℝ) ≤ _ := by linarith
      _ ≤ Real.exp 3 * Real.exp (0.2565:ℝ) :=
          mul_le_mul h1 h2 (by positivity) (by linarith [Real.exp_pos (3:ℝ)])
  have h := robin_ratio_le (k := 11) hexp hc hlogc
  have h2 : (11:ℝ) * ((3.2565:ℝ)/(25.9:ℝ)) < 1.3841 := by norm_num
  linarith

/-- The Robin ratio at `k = 12` (where `k^k > P_k`). -/
private lemma ratio_12 :
    (12:ℝ) * (Real.log (Real.log ((∏ i ∈ Finset.range 12, Nat.nth Nat.Prime i : ℝ)))
      / Real.log (∏ i ∈ Finset.range 12, (Nat.nth Nat.Prime i : ℝ))) < 1.3841 := by
  have hP : (∏ i ∈ Finset.range 12, (Nat.nth Nat.Prime i : ℝ)) = 7420738134810 := by
    simp only [Finset.prod_range_succ, Finset.prod_range_zero, nth_prime_0, nth_prime_1, nth_prime_2, nth_prime_3, nth_prime_4, nth_prime_5, nth_prime_6, nth_prime_7, nth_prime_8, nth_prime_9, nth_prime_10, nth_prime_11]
    norm_num
  rw [hP]
  have hexp : Real.exp (29.5:ℝ) ≤ (7420738134810:ℝ) := by
    have hsplit : Real.exp (29.5:ℝ) = Real.exp 29 * Real.exp (0.5:ℝ) := by
      rw [← Real.exp_add]; norm_num
    rw [hsplit]
    have h1 : Real.exp (29:ℝ) ≤ 2.7182818286^29 := exp_nat_le 29
    have h2 : Real.exp (0.5:ℝ) ≤ 1.6488 := by
      refine le_trans (exp_frac_le (f := 0.5) (by norm_num) (by norm_num)) ?_
      norm_num
    calc Real.exp 29 * Real.exp (0.5:ℝ) ≤ 2.7182818286^29 * 1.6488 :=
          mul_le_mul h1 h2 (by linarith [Real.exp_pos (0.5:ℝ)]) (by positivity)
      _ ≤ 7420738134810 := by norm_num
  have hc : Real.exp 1 ≤ (29.5:ℝ) := by have h := Real.exp_one_lt_d9; linarith
  have hlogc : Real.log (29.5:ℝ) ≤ 3.39 := by
    rw [Real.log_le_iff_le_exp (by norm_num)]
    have hsplit : Real.exp (3.39:ℝ) = Real.exp 3 * Real.exp (0.39:ℝ) := by
      rw [← Real.exp_add]; norm_num
    rw [hsplit]
    have h1 : (2.7182818283:ℝ)^3 ≤ Real.exp 3 := exp_nat_ge 3
    have h2 : (∑ m ∈ Finset.range 12, ((0.39:ℝ)^m/(m.factorial : ℝ)))
        ≤ Real.exp (0.39:ℝ) := Real.sum_le_exp_of_nonneg (by norm_num) 12
    have h3 : (2.7182818283:ℝ)^3 *
        (∑ m ∈ Finset.range 12, ((0.39:ℝ)^m/(m.factorial : ℝ))) ≥ (29.5:ℝ) := by norm_num
    calc (29.5:ℝ) ≤ _ := by linarith
      _ ≤ Real.exp 3 * Real.exp (0.39:ℝ) :=
          mul_le_mul h1 h2 (by positivity) (by linarith [Real.exp_pos (3:ℝ)])
  have h := robin_ratio_le (k := 12) hexp hc hlogc
  have h2 : (12:ℝ) * ((3.39:ℝ)/(29.5:ℝ)) < 1.3841 := by norm_num
  linarith

private lemma ratio_all (k : ℕ) (hk : 4 ≤ k) :
    (k:ℝ) * (Real.log (Real.log (∏ i ∈ Finset.range k, (Nat.nth Nat.Prime i : ℝ)))
      / Real.log (∏ i ∈ Finset.range k, (Nat.nth Nat.Prime i : ℝ))) < 1.3841 := by
  by_cases h9 : k ≤ 9
  · interval_cases k
    · exact robin_four
    · exact robin_five
    · exact robin_six
    · exact robin_seven
    · exact robin_eight
    · exact robin_nine
  · push_neg at h9
    by_cases h12 : k ≤ 12
    · interval_cases k
      · exact ratio_10
      · exact ratio_11
      · exact ratio_12
    · push_neg at h12
      exact ratio_high k (by omega)

/-- Robin Theorem 11, journal Lemma 4. -/
private theorem robin_all (n : ℕ) (hn : 3 ≤ n) :
    (n.primeFactors.card : ℝ) < 1.3841 * Real.log n / Real.log (Real.log n) :=
  robin_of_primorial_le n.primeFactors.card (fun k hk _ => ratio_all k hk) n hn le_rfl

/-- LEAF. Robin Theorem 11, journal Lemma 4 p. 1216. -/
theorem lemma4_robin : PaperInputs148.Lemma4J :=
  robin_all

/-- LEAF. Rosser and Schoenfeld 1962 Theorem 18, journal Lemma 2 p. 1215. -/
theorem lemma2_theta : PaperInputs148.Lemma2J := by
  exact Theta332.theta_of_buthe ThetaInputs224.theta_buthe_1e19

/-- LEAF. Weighted reciprocal prime sum, journal p. 1234 first display.
Bordignon and Starichkova apply reference 7 Lemma 1 part ii and evaluate the integral. -/
theorem weighted_reciprocal_primes (n : ℕ) (α : ℝ)
    (hn : exp (exp 10) ≤ (n : ℝ)) (hα : 0 < α) (hα1 : α < 1 / 24) :
    (∑ q ∈ U7153.Qset n,
      (1 : ℝ) / ((q : ℝ) * log ((n : ℝ) ^ (1 / 2 - α) / q))) ≤
      (log 6 + log ((3 - 8 * α) / (3 - 18 * α))) / ((1 / 2 - α) * log n) +
        512 / (kA α * log n ^ 3) := by
  sorry

/-- LEAF. Unweighted reciprocal prime interval, journal p. 1234.
Rosser and Schoenfeld reference 16 Theorem 5. The lower endpoint is inclusive. -/
theorem reciprocal_prime_interval (n : ℕ) (hn : exp (exp 10) ≤ (n : ℝ)) (hev : Even n) :
    (∑ q ∈ U7153.Qset n, (1 : ℝ) / q) ≤ log (8 / 3) + 64 / log n ^ 2 := by
  sorry

/-- A concrete nonempty domain check for the squarefree counting input, p. 1216. -/
theorem lemma5_mu_one_instance :
    ((((Icc 1 ⌊(1 : ℝ)⌋₊).filter (fun n => Squarefree n)).card : ℝ)) ≤
      Lemma5Coeffs138.mMu 1 * 1 := by
  have hcard : ((((Icc 1 ⌊(1 : ℝ)⌋₊).filter (fun n => Squarefree n)).card : ℝ)) ≤ 1 := by
    have h := card_filter_le (Icc 1 ⌊(1 : ℝ)⌋₊) (fun n => Squarefree n)
    norm_num at h ⊢
    exact_mod_cast h
  have hπ : π ^ 2 ≤ (16 : ℝ) := by nlinarith [pi_pos, pi_lt_four]
  have hdiv : (6 : ℝ) / 16 ≤ 6 / π ^ 2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hπ
  apply hcard.trans
  norm_num [Lemma5Coeffs138.mMu]
  linarith

/-- A concrete nonempty weighted domain check for Lemma 5, p. 1216. -/
theorem lemma5_phi_two_instance :
    (∑ n ∈ (Icc 1 ⌊(2 : ℝ)⌋₊).filter (fun n => Squarefree n), (1 : ℝ) / n.totient) ≤
      Mphi 2 * log 2 := by
  have hset : (Icc 1 ⌊(2 : ℝ)⌋₊).filter (fun n => Squarefree n) = {1, 2} := by
    ext n
    simp only [mem_filter, mem_Icc, mem_insert, mem_singleton]
    norm_num only [Nat.floor_ofNat] 
    constructor
    · intro h
      omega
    · intro h
      rcases h with rfl | rfl
      · norm_num
      · exact ⟨⟨by norm_num, le_rfl⟩, Nat.prime_two.squarefree⟩
  rw [hset]
  norm_num only [sum_insert, mem_singleton, reduceCtorEq, not_false_eq_true, sum_singleton,
    Nat.totient_one, Nat.totient_two, Nat.cast_one, div_one]
  have hlog : 0 < log (2 : ℝ) := log_pos (by norm_num)
  have hmin : 0 ≤ min (2.44 / (√(2 : ℝ) * log 2)) (11 / (√(2 : ℝ) * log 2 ^ 2)) := by positivity
  have hmul := mul_nonneg hmin hlog.le
  calc
    (2 : ℝ) ≤ log 2 + 1.333 := by linarith [log_two_gt_d9]
    _ ≤ log 2 + 1.333 + min (2.44 / (√(2 : ℝ) * log 2))
        (11 / (√(2 : ℝ) * log 2 ^ 2)) * log 2 := le_add_of_nonneg_right hmul
    _ = _ := by unfold Mphi; field_simp


/-! ### Proof of `li_bounds_large`

Everything below is a private development for the leaf `li_bounds_large`: the
principal-value logarithmic integral `liPV` is expanded by three integrations by
parts into `y/L + y/L² + 2y/L³ - A + liPV 2 + 6∫₂^y dt/(log t)^4`, the integral is
bounded above by a convexity (trapezoid) sum on the partition `exp (11 - k/10)` and
below by the monotonicity of the integrand, and the comparison functions are
extended to all `y ≥ exp 11` by monotonicity.  Nothing here changes an existing
statement. -/
namespace LiProof232
open Real MeasureTheory Filter Topology Set
noncomputable section

lemma exp_eleven_le : exp 11 ≤ 59874.142 := by
  have h1 : exp (11 : ℝ) = exp 1 ^ 11 := by
    simpa using Real.exp_nat_mul (x := (1 : ℝ)) 11
  rw [h1]
  have h2 : exp 1 ≤ 2.7182818286 := le_of_lt Real.exp_one_lt_d9
  have h3 : exp 1 ^ 11 ≤ (2.7182818286 : ℝ) ^ 11 := by gcongr
  have h4 : (2.7182818286 : ℝ) ^ 11 ≤ 59874.142 := by norm_num
  linarith

/-- `exp (-1/8) ≤ 481/512`, from `exp (1/8) ≥ 1 + 1/8 + (1/8)²/2 = 145/128`. -/
lemma exp_neg_eighth_le : exp (-(1/8)) ≤ 481/512 := by
  have h2 : ∑ i ∈ Finset.range 3, ((1/8 : ℝ)) ^ i / (i.factorial : ℝ) ≤ exp (1/8) :=
    Real.sum_le_exp_of_nonneg (by norm_num) 3
  have h3 : (145/128 : ℝ) ≤ exp (1/8) := by
    norm_num [Finset.sum_range_succ, Nat.factorial] at h2 ⊢
    linarith
  have h5 : (exp (1/8))⁻¹ ≤ (145/128 : ℝ)⁻¹ := by
    have h6 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 145/128) h3
    simpa [one_div] using h6
  have h6 : (145/128 : ℝ)⁻¹ ≤ 481/512 := by norm_num
  have h7 : exp (-(1/8)) = (exp (1/8))⁻¹ := by
    rw [show (-(1/8) : ℝ) = -(1/8) by norm_num, Real.exp_neg]
  rw [h7]
  linarith

lemma exp_shift_le (k : ℕ) : exp (11 - (k : ℝ)/8) ≤ 59874.142 * (481/512)^k := by
  have hs : (11 : ℝ) - (k : ℝ)/8 = 11 + (k : ℝ) * (-(1/8)) := by ring
  rw [hs, Real.exp_add, Real.exp_nat_mul]
  have hp : (0 : ℝ) < exp (-(1/8)) := exp_pos _
  have h8 : exp (-(1/8)) ≤ 481/512 := exp_neg_eighth_le
  have h3 : exp (-(1/8)) ^ k ≤ (481/512)^k := by gcongr
  exact mul_le_mul exp_eleven_le h3 (by positivity) (by norm_num)

/-! ## The integrand `f4 x = (log x)⁻⁴` -/

/-- `f4 x = 1 / (log x)^4`, the integrand in the integration by parts. -/
def f4 (x : ℝ) : ℝ := ((log x)^4)⁻¹

lemma f4_exp (s : ℝ) : f4 (exp s) = (s^4)⁻¹ := by simp [f4]

lemma f4_pos {x : ℝ} (hx : 1 < x) : 0 < f4 x := by
  have h : 0 < log x := log_pos hx
  simp only [f4]
  positivity

lemma continuousOn_f4 : ContinuousOn f4 (Ici (2:ℝ)) := by
  have h0 : ContinuousOn (fun x : ℝ => log x) (Ici (2:ℝ)) := by
    apply Real.continuousOn_log.mono
    intro x hx
    have hx2 : (2:ℝ) ≤ x := hx
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith
  have h1 : ContinuousOn (fun x : ℝ => (log x)^4) (Ici (2:ℝ)) := h0.pow 4
  refine h1.inv₀ (fun x hx => ?_)
  have hx2 : (2:ℝ) ≤ x := hx
  have hpos : 0 < log x := log_pos (by linarith)
  positivity

lemma intervalIntegrable_f4 {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable f4 volume a b := by
  apply ContinuousOn.intervalIntegrable
  rcases le_total a b with h | h
  · rw [uIcc_of_le h]
    exact continuousOn_f4.mono (by intro x hx; exact le_trans ha hx.1)
  · rw [uIcc_of_ge h]
    exact continuousOn_f4.mono (by intro x hx; exact le_trans hb hx.1)

/-! ## Derivatives and convexity of `f4` -/

/-- The derivative of `f4`. -/
def f4d (x : ℝ) : ℝ := -4 * (x * (log x)^5)⁻¹

/-- The second derivative of `f4`. -/
def f4dd (x : ℝ) : ℝ := (4 * log x + 20) * (x^2 * (log x)^6)⁻¹

lemma hasDerivAt_f4 {x : ℝ} (hx : 1 < x) : HasDerivAt f4 (f4d x) x := by
  have hx0 : x ≠ 0 := by linarith
  have hlog : log x ≠ 0 := (log_pos hx).ne'
  have h1 : HasDerivAt (fun y : ℝ => log y) x⁻¹ x := hasDerivAt_log hx0
  have h2 : HasDerivAt (fun y : ℝ => (log y)^4) ((4:ℝ) * (log x)^3 * x⁻¹) x := h1.pow 4
  have h3 : HasDerivAt (fun y : ℝ => ((log y)^4)⁻¹)
      (-((4:ℝ) * (log x)^3 * x⁻¹) / ((log x)^4)^2) x :=
    h2.inv (by positivity)
  have hval : (-((4:ℝ) * (log x)^3 * x⁻¹) / ((log x)^4)^2) = f4d x := by
    simp only [f4d]
    field_simp
    try ring
  rw [hval] at h3
  exact h3

lemma hasDerivAt_f4d {x : ℝ} (hx : 1 < x) : HasDerivAt f4d (f4dd x) x := by
  have hx0 : x ≠ 0 := by linarith
  have hlog : log x ≠ 0 := (log_pos hx).ne'
  have h1 : HasDerivAt (fun y : ℝ => log y) x⁻¹ x := hasDerivAt_log hx0
  have h2' := (hasDerivAt_id (x : ℝ)).mul (h1.pow 5)
  have h2 : HasDerivAt (fun y : ℝ => y * (log y)^5)
      ((log x)^5 + x * (5 * (log x)^4 * x⁻¹)) x := by
    have hfun : (fun y : ℝ => y * (log y)^5) = id * (fun y : ℝ => log y)^5 := by
      funext y; simp
    rw [hfun]
    convert h2' using 1
    try simp
    try ring
  have h3 : HasDerivAt (fun y : ℝ => (y * (log y)^5)⁻¹)
      (-((log x)^5 + x * (5 * (log x)^4 * x⁻¹)) / (x * (log x)^5)^2) x :=
    h2.inv (by positivity)
  have h4 : HasDerivAt (fun y : ℝ => -4 * (y * (log y)^5)⁻¹)
      (-4 * (-((log x)^5 + x * (5 * (log x)^4 * x⁻¹)) / (x * (log x)^5)^2)) x :=
    h3.const_mul (-4)
  have hval : (-4 * (-((log x)^5 + x * (5 * (log x)^4 * x⁻¹)) / (x * (log x)^5)^2)) = f4dd x := by
    simp only [f4dd]
    field_simp
    try ring
  rw [hval] at h4
  exact h4

lemma deriv_f4_eq {x : ℝ} (hx : 1 < x) : deriv f4 x = f4d x := (hasDerivAt_f4 hx).deriv

lemma convexOn_f4 : ConvexOn ℝ (Ioi (1:ℝ)) f4 := by
  have hconv : Convex ℝ (Ioi (1:ℝ)) := convex_Ioi 1
  have hdiff1 : DifferentiableOn ℝ f4 (Ioi (1:ℝ)) := fun x hx =>
    (hasDerivAt_f4 hx).differentiableAt.differentiableWithinAt
  have hdiff2 : DifferentiableOn ℝ (deriv f4) (Ioi (1:ℝ)) := by
    intro x hx
    have h2 : deriv f4 =ᶠ[𝓝 x] f4d := by
      filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy using deriv_f4_eq hy
    exact ((hasDerivAt_f4d hx).congr_of_eventuallyEq h2).differentiableAt.differentiableWithinAt
  refine convexOn_of_deriv2_nonneg' hconv hdiff1 hdiff2 (fun x hx => ?_)
  have h2 : deriv f4 =ᶠ[𝓝 x] f4d := by
    filter_upwards [isOpen_Ioi.mem_nhds hx] with y hy using deriv_f4_eq hy
  have h3 : deriv^[2] f4 x = deriv f4d x := by
    rw [show deriv^[2] f4 = deriv (deriv f4) from rfl, h2.deriv_eq]
  rw [h3, (hasDerivAt_f4d hx).deriv]
  have hx1 : (1:ℝ) < x := hx
  have hlog : 0 < log x := log_pos hx1
  have hx0 : 0 < x := by linarith
  simp only [f4dd]
  have h5 : (0:ℝ) < 4 * log x + 20 := by linarith
  have h6 : (0:ℝ) < x^2 * (log x)^6 := by positivity
  exact mul_nonneg h5.le (inv_nonneg.mpr h6.le)

/-! ## The trapezoid bound -/

/-- For the convex `f4`, the integral is at most the trapezoid area. -/
lemma integral_f4_le_trapz {a b : ℝ} (ha : 2 ≤ a) (hab : a ≤ b) :
    ∫ t in a..b, f4 t ≤ (b - a) * (f4 a + f4 b) / 2 := by
  rcases eq_or_lt_of_le hab with h | h
  · subst h; simp
  have ha1 : (1:ℝ) < a := by linarith
  have hb1 : (1:ℝ) < b := by linarith
  have hbda : (0:ℝ) < b - a := by linarith
  have hchord : ∀ t ∈ Icc a b, f4 t ≤ ((b - t) * f4 a + (t - a) * f4 b) / (b - a) := by
    intro t ht
    obtain ⟨hta, htb⟩ := ht
    set p : ℝ := (b - t) / (b - a) with hp
    set q : ℝ := (t - a) / (b - a) with hq
    have hp0 : 0 ≤ p := div_nonneg (by linarith) hbda.le
    have hq0 : 0 ≤ q := div_nonneg (by linarith) hbda.le
    have hpq : p + q = 1 := by
      simp only [hp, hq]
      field_simp
      ring
    obtain ⟨-, hcv⟩ := convexOn_f4
    have hconv : f4 (p * a + q * b) ≤ p * f4 a + q * f4 b :=
      hcv ha1 hb1 hp0 hq0 hpq
    have hpt : p * a + q * b = t := by
      simp only [hp, hq]
      field_simp
      ring
    rw [← hpt]
    refine hconv.trans_eq ?_
    simp only [hp, hq]
    field_simp
    ring
  have hint1 : IntervalIntegrable f4 volume a b := intervalIntegrable_f4 ha (le_trans ha hab)
  have hint2 : IntervalIntegrable (fun t : ℝ => ((b - t) * f4 a + (t - a) * f4 b) / (b - a))
      volume a b := by
    apply Continuous.intervalIntegrable
    fun_prop
  have hmono := intervalIntegral.integral_mono_on hab hint1 hint2 hchord
  have hsq : ∀ x : ℝ, HasDerivAt (fun s : ℝ => s^2/2) x x := by
    intro x
    have h4 : HasDerivAt (fun s : ℝ => s^2) (2 * x) x := by
      simpa using hasDerivAt_pow 2 x
    have h5 : HasDerivAt (fun s : ℝ => s^2/2) ((2 : ℝ) * x / 2) x := h4.div_const 2
    convert h5 using 1
    try ring
  have hprim : ∀ x ∈ uIcc a b, HasDerivAt
      (fun s : ℝ => (f4 a * (b * s - s^2/2) + f4 b * (s^2/2 - a * s)) / (b - a))
      (((b - x) * f4 a + (x - a) * f4 b) / (b - a)) x := by
    intro x _
    have h1 : HasDerivAt (fun s : ℝ => b * s - s^2/2) (b - x) x := by
      have hb1' : HasDerivAt (fun s : ℝ => b * s) b x := by
        simpa using (hasDerivAt_id x).const_mul (b:ℝ)
      have h6 := hb1'.sub (hsq x)
      convert h6 using 1
      try ring
    have h7 : HasDerivAt (fun s : ℝ => s^2/2 - a * s) (x - a) x := by
      have h8 : HasDerivAt (fun s : ℝ => a * s) a x := by
        simpa using (hasDerivAt_id x).const_mul (a:ℝ)
      have h6 := (hsq x).sub h8
      convert h6 using 1
      try ring
    have h9 := h1.const_mul (f4 a)
    have h10 := h7.const_mul (f4 b)
    have h11 := h9.add h10
    have h12 : HasDerivAt (fun s : ℝ =>
        (f4 a * (b * s - s^2/2) + f4 b * (s^2/2 - a * s)) / (b - a))
        ((f4 a * (b - x) + f4 b * (x - a)) / (b - a)) x := h11.div_const (b - a)
    convert h12 using 1
    try ring
  have hval : (∫ t in a..b, ((b - t) * f4 a + (t - a) * f4 b) / (b - a))
      = (b - a) * (f4 a + f4 b) / 2 := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := a) (b := b) hprim hint2
    rw [this]
    field_simp
    try ring
  rw [hval] at hmono
  exact hmono



/-! ## Exponential bounds at `1/10` (the partition of `[2, exp 11]`) -/

lemma exp_tenth_ge : (1.10517 : ℝ) ≤ exp (1/10) := by
  have h2 : ∑ i ∈ Finset.range 5, ((1/10 : ℝ)) ^ i / (i.factorial : ℝ) ≤ exp (1/10) :=
    Real.sum_le_exp_of_nonneg (by norm_num) 5
  norm_num [Finset.sum_range_succ, Nat.factorial] at h2 ⊢
  linarith

lemma exp_tenth_le : exp (1/10) ≤ 1.10518 := by
  by_contra h
  push_neg at h
  have e1 : exp (1:ℝ) = exp (1/10)^10 := by
    simpa using Real.exp_nat_mul (x := (1/10 : ℝ)) 10
  have h2 : exp (1:ℝ) ≤ 2.7182818286 := le_of_lt Real.exp_one_lt_d9
  have h2' : exp (1/10)^10 ≤ 2.7182818286 := by rw [← e1]; exact h2
  have h3 : (1.10518:ℝ)^10 < exp (1/10)^10 :=
    pow_lt_pow_left₀ h (by norm_num) (by norm_num : (10:ℕ) ≠ 0)
  have h4 : (2.7182818286:ℝ) < (1.10518:ℝ)^10 := by norm_num
  linarith

lemma exp_neg_tenth_le : exp (-(1/10)) ≤ 904839/1000000 := by
  have h3 : (1.10517 : ℝ) ≤ exp (1/10) := exp_tenth_ge
  have h5 : (exp (1/10))⁻¹ ≤ (1.10517 : ℝ)⁻¹ := by
    have h6 := one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 1.10517) h3
    simpa [one_div] using h6
  have h6 : (1.10517 : ℝ)⁻¹ ≤ 904839/1000000 := by norm_num
  have h7 : exp (-(1/10)) = (exp (1/10))⁻¹ := by
    rw [show (-(1/10) : ℝ) = -(1/10) by norm_num, Real.exp_neg]
  rw [h7]
  linarith

lemma one_sub_exp_neg_tenth_le : 1 - exp (-(1/10)) ≤ 0.09518 := by
  have h3 : exp (1/10) ≤ 1.10518 := exp_tenth_le
  have hpos : (0:ℝ) < exp (1/10) := exp_pos _
  have h4 : (1.10518 : ℝ)⁻¹ ≤ exp (-(1/10)) := by
    have h6 := one_div_le_one_div_of_le hpos h3
    have h7 : exp (-(1/10)) = (exp (1/10))⁻¹ := by
      rw [show (-(1/10) : ℝ) = -(1/10) by norm_num, Real.exp_neg]
    rw [h7]
    simpa [one_div] using h6
  have h5 : (1 - (1.10518:ℝ)⁻¹) ≤ 0.09518 := by norm_num
  linarith

lemma exp_shift_le10 (k : ℕ) : exp (11 - (k : ℝ)/10) ≤ 59874.142 * (904839/1000000)^k := by
  have hs : (11 : ℝ) - (k : ℝ)/10 = 11 + (k : ℝ) * (-(1/10)) := by ring
  rw [hs, Real.exp_add, Real.exp_nat_mul]
  have hp : (0 : ℝ) < exp (-(1/10)) := exp_pos _
  have h8 : exp (-(1/10)) ≤ 904839/1000000 := exp_neg_tenth_le
  have h3 : exp (-(1/10)) ^ k ≤ (904839/1000000)^k := by gcongr
  exact mul_le_mul exp_eleven_le h3 (by positivity) (by norm_num)

/-! ## The partition `tpt k = exp (11 - k/10)` -/

/-- `tpt k = exp (11 - k/10)`, a decreasing family from `exp 11` down past `2`. -/
def tpt (k : ℕ) : ℝ := exp (11 - (k:ℝ)/10)

lemma tpt_zero : tpt 0 = exp 11 := by norm_num [tpt]

lemma tpt_anti : Antitone tpt := by
  intro k l hkl
  simp only [tpt]
  apply exp_le_exp.mpr
  have h : (k:ℝ) ≤ (l:ℝ) := by exact_mod_cast hkl
  linarith

lemma two_le_tpt_103 : (2:ℝ) ≤ tpt 103 := by
  have h1 : (2.01 : ℝ) ≤ exp (7/10) := by
    have h2 : ∑ i ∈ Finset.range 5, ((7/10:ℝ))^i / (i.factorial : ℝ) ≤ exp (7/10) :=
      Real.sum_le_exp_of_nonneg (by norm_num) 5
    norm_num [Finset.sum_range_succ, Nat.factorial] at h2 ⊢
    linarith
  have h3 : exp (7/10) ≤ exp (11 - (103:ℝ)/10) := by
    apply exp_le_exp.mpr
    norm_num
  have h4 : tpt 103 = exp (11 - (103:ℝ)/10) := rfl
  rw [h4]
  linarith

lemma two_le_tpt {k : ℕ} (hk : k ≤ 103) : (2:ℝ) ≤ tpt k :=
  le_trans two_le_tpt_103 (tpt_anti hk)

lemma f4_tpt (k : ℕ) : f4 (tpt k) = ((11 - (k:ℝ)/10)^4)⁻¹ := by
  simp only [tpt, f4, Real.log_exp]

lemma tpt_sub_le (k : ℕ) :
    tpt k - tpt (k+1) ≤ 59874.142 * (904839/1000000)^k * 0.09518 := by
  have hsplit : tpt k - tpt (k+1) = exp (11 - (k:ℝ)/10) * (1 - exp (-(1/10))) := by
    have step : exp ((11 - (k:ℝ)/10) + (-(1/10))) =
        exp (11 - (k:ℝ)/10) * exp (-(1/10)) := Real.exp_add _ _
    simp only [tpt, Nat.cast_add, Nat.cast_one]
    rw [show (11:ℝ) - ((k:ℝ)+1)/10 = (11 - (k:ℝ)/10) + (-(1/10)) by ring, step]
    ring
  rw [hsplit]
  have h2 : exp (11 - (k:ℝ)/10) ≤ 59874.142 * (904839/1000000)^k := exp_shift_le10 k
  have h3 : 1 - exp (-(1/10)) ≤ 0.09518 := one_sub_exp_neg_tenth_le
  have h4 : (0:ℝ) ≤ 1 - exp (-(1/10)) := by
    have h5 : exp (-(1/10)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; norm_num
    linarith
  calc exp (11 - (k:ℝ)/10) * (1 - exp (-(1/10)))
      ≤ (59874.142 * (904839/1000000)^k) * 0.09518 := mul_le_mul h2 h3 h4 (by norm_num)
    _ = _ := by ring

/-- The closed-form upper bound for the `k`-th trapezoid term. -/
def Db (k : ℕ) : ℝ :=
  (59874.142 * (904839/1000000)^k * 0.09518) *
    (((11 - (k:ℝ)/10)^4)⁻¹ + ((11 - ((k:ℝ)+1)/10)^4)⁻¹) / 2

lemma term_le_Db (k : ℕ) :
    (tpt k - tpt (k+1)) * (f4 (tpt k) + f4 (tpt (k+1)))/2 ≤ Db k := by
  have h1 : tpt k - tpt (k+1) ≤ 59874.142 * (904839/1000000)^k * 0.09518 := tpt_sub_le k
  have h2 : (0:ℝ) ≤ ((11 - (k:ℝ)/10)^4)⁻¹ + ((11 - ((k:ℝ)+1)/10)^4)⁻¹ := by positivity
  simp only [f4_tpt, Nat.cast_add, Nat.cast_one, Db]
  exact div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right h1 h2) (by norm_num)

/-! ## The numerical table -/

/-- `Q k` bounds `(904839/1000000)^k` from above, and `Ct k` bounds the `k`-th trapezoid term. -/
def Q : ℕ → ℝ
  | 0 => 1.000000000000
  | 1 => 0.904839000000
  | 2 => 0.818733615921
  | 3 => 0.740822106297
  | 4 => 0.670324733840
  | 5 => 0.606535961844
  | 6 => 0.548817393179
  | 7 => 0.496591381227
  | 8 => 0.449335248799
  | 9 => 0.406576057189
  | 10 => 0.367885873011
  | 11 => 0.332877485450
  | 12 => 0.301200531058
  | 13 => 0.272537987322
  | 14 => 0.246602999911
  | 15 => 0.223136011837
  | 16 => 0.201902165815
  | 17 => 0.182688953814
  | 18 => 0.165304090281
  | 19 => 0.149573587746
  | 20 => 0.135340015563
  | 21 => 0.122460924343
  | 22 => 0.110807420322
  | 23 => 0.100262875397
  | 24 => 0.090721759912
  | 25 => 0.082088586518
  | 26 => 0.074276954537
  | 27 => 0.067208685267
  | 28 => 0.060813039569
  | 29 => 0.055026009911
  | 30 => 0.049789679782
  | 31 => 0.045051644065
  | 32 => 0.040764484565
  | 33 => 0.036885295450
  | 34 => 0.033375253850
  | 35 => 0.030199231319
  | 36 => 0.027325442268
  | 37 => 0.024725125857
  | 38 => 0.022372258156
  | 39 => 0.020243291698
  | 40 => 0.018316919817
  | 41 => 0.016573863411
  | 42 => 0.014996677995
  | 43 => 0.013569579121
  | 44 => 0.012278284403
  | 45 => 0.011109870581
  | 46 => 0.010052644187
  | 47 => 0.009096024514
  | 48 => 0.008230437726
  | 49 => 0.007447221042
  | 50 => 0.006738536041
  | 51 => 0.006097290213
  | 52 => 0.005517065980
  | 53 => 0.004992056465
  | 54 => 0.004517007380
  | 55 => 0.004087164441
  | 56 => 0.003698225786
  | 57 => 0.003346298922
  | 58 => 0.003027861771
  | 59 => 0.002739727418
  | 60 => 0.002479012218
  | 61 => 0.002243106937
  | 62 => 0.002029650638
  | 63 => 0.001836507054
  | 64 => 0.001661743207
  | 65 => 0.001503610062
  | 66 => 0.001360525025
  | 67 => 0.001231056104
  | 68 => 0.001113907575
  | 69 => 0.001007907017
  | 70 => 0.000911993578
  | 71 => 0.000825207358
  | 72 => 0.000746679801
  | 73 => 0.000675625005
  | 74 => 0.000611331854
  | 75 => 0.000553156904
  | 76 => 0.000500517940
  | 77 => 0.000452888153
  | 78 => 0.000409790864
  | 79 => 0.000370794756
  | 80 => 0.000335509557
  | 81 => 0.000303582133
  | 82 => 0.000274692954
  | 83 => 0.000248552898
  | 84 => 0.000224900356
  | 85 => 0.000203498614
  | 86 => 0.000184133483
  | 87 => 0.000166611157
  | 88 => 0.000150756273
  | 89 => 0.000136410156
  | 90 => 0.000123429230
  | 91 => 0.000111683582
  | 92 => 0.000101055661
  | 93 => 0.000091439104
  | 94 => 0.000082737668
  | 95 => 0.000074864269
  | 96 => 0.000067740111
  | 97 => 0.000061293895
  | 98 => 0.000055461107
  | 99 => 0.000050183373
  | 100 => 0.000045407874
  | 101 => 0.000041086816
  | 102 => 0.000037176954
  | 103 => 0.000033639158
  | _ => 0

def Ct : ℕ → ℝ
  | 0 => 0.396478
  | 1 => 0.372160
  | 2 => 0.349453
  | 3 => 0.328244
  | 4 => 0.308431
  | 5 => 0.289919
  | 6 => 0.272617
  | 7 => 0.256444
  | 8 => 0.241322
  | 9 => 0.227180
  | 10 => 0.213952
  | 11 => 0.201575
  | 12 => 0.189993
  | 13 => 0.179152
  | 14 => 0.169001
  | 15 => 0.159496
  | 16 => 0.150593
  | 17 => 0.142252
  | 18 => 0.134436
  | 19 => 0.127110
  | 20 => 0.120242
  | 21 => 0.113802
  | 22 => 0.107762
  | 23 => 0.102096
  | 24 => 0.096779
  | 25 => 0.091790
  | 26 => 0.087107
  | 27 => 0.082710
  | 28 => 0.078581
  | 29 => 0.074703
  | 30 => 0.071061
  | 31 => 0.067639
  | 32 => 0.064423
  | 33 => 0.061402
  | 34 => 0.058562
  | 35 => 0.055893
  | 36 => 0.053384
  | 37 => 0.051025
  | 38 => 0.048808
  | 39 => 0.046723
  | 40 => 0.044764
  | 41 => 0.042922
  | 42 => 0.041192
  | 43 => 0.039565
  | 44 => 0.038038
  | 45 => 0.036603
  | 46 => 0.035257
  | 47 => 0.033994
  | 48 => 0.032810
  | 49 => 0.031700
  | 50 => 0.030662
  | 51 => 0.029691
  | 52 => 0.028784
  | 53 => 0.027939
  | 54 => 0.027153
  | 55 => 0.026424
  | 56 => 0.025748
  | 57 => 0.025126
  | 58 => 0.024553
  | 59 => 0.024030
  | 60 => 0.023556
  | 61 => 0.023128
  | 62 => 0.022747
  | 63 => 0.022412
  | 64 => 0.022123
  | 65 => 0.021880
  | 66 => 0.021683
  | 67 => 0.021534
  | 68 => 0.021433
  | 69 => 0.021382
  | 70 => 0.021384
  | 71 => 0.021441
  | 72 => 0.021556
  | 73 => 0.021734
  | 74 => 0.021980
  | 75 => 0.022299
  | 76 => 0.022699
  | 77 => 0.023189
  | 78 => 0.023780
  | 79 => 0.024485
  | 80 => 0.025320
  | 81 => 0.026304
  | 82 => 0.027463
  | 83 => 0.028825
  | 84 => 0.030429
  | 85 => 0.032322
  | 86 => 0.034563
  | 87 => 0.037231
  | 88 => 0.040426
  | 89 => 0.044279
  | 90 => 0.048969
  | 91 => 0.054734
  | 92 => 0.061907
  | 93 => 0.070952
  | 94 => 0.082542
  | 95 => 0.097666
  | 96 => 0.117826
  | 97 => 0.145377
  | 98 => 0.184149
  | 99 => 0.240660
  | 100 => 0.326590
  | 101 => 0.464262
  | 102 => 0.699826
  | 103 => 0.059970
  | _ => 0

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma Q_step : ∀ k < 103, Q k * 0.904839 ≤ Q (k+1) := by
  intro k hk
  interval_cases k <;> simp only [Q] <;> norm_num

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma geom_le : ∀ k, k ≤ 103 → ((904839/1000000 : ℝ))^k ≤ Q k
  | 0, _ => by simp only [Q]; norm_num
  | (n+1), hn => by
    have hn' : n ≤ 103 := by omega
    have hQpos : (0:ℝ) ≤ Q n := by
      have h99 := geom_le n hn'
      have : (0:ℝ) ≤ ((904839/1000000 : ℝ))^n := by positivity
      linarith
    have hstep : Q n * 0.904839 ≤ Q (n+1) := by
      have hn'' : n < 103 := by omega
      interval_cases n <;> simp only [Q] <;> norm_num
    rw [pow_succ]
    calc ((904839/1000000 : ℝ))^n * (904839/1000000) ≤ Q n * 0.904839 := by
          apply mul_le_mul (geom_le n hn') (by norm_num) (by norm_num) hQpos
      _ ≤ Q (n+1) := hstep

/-- The trapezoid term with `Q` in place of the power. -/
def DbQ (k : ℕ) : ℝ :=
  (59874.142 * Q k * 0.09518) *
    (((11 - (k:ℝ)/10)^4)⁻¹ + ((11 - ((k:ℝ)+1)/10)^4)⁻¹) / 2

lemma Db_le_DbQ {k : ℕ} (hk : k ≤ 103) : Db k ≤ DbQ k := by
  have h1 : ((904839/1000000 : ℝ))^k ≤ Q k := geom_le k hk
  have h2 : (0:ℝ) ≤ ((11 - (k:ℝ)/10)^4)⁻¹ + ((11 - ((k:ℝ)+1)/10)^4)⁻¹ := by positivity
  simp only [Db, DbQ]
  apply div_le_div_of_nonneg_right _ (by norm_num)
  apply mul_le_mul_of_nonneg_right _ h2
  apply mul_le_mul_of_nonneg_right _ (by norm_num)
  exact mul_le_mul_of_nonneg_left h1 (by norm_num)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma DbQ_le_Ct : ∀ k < 103, DbQ k ≤ Ct k := by
  intro k hk
  interval_cases k <;> (simp only [DbQ, Q, Ct] <;> norm_num)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma Db_le_Ct : ∀ k < 103, Db k ≤ Ct k := by
  intro k hk
  have hk' : k ≤ 103 := by omega
  exact (Db_le_DbQ hk').trans (DbQ_le_Ct k hk)

set_option maxRecDepth 100000 in
set_option maxHeartbeats 4000000 in
lemma Ct_sum_le : (∑ k ∈ Finset.range 104, Ct k) ≤ 10.33 := by
  simp only [Finset.sum_range_succ, Ct]
  norm_num

/-- The partition bound: `∫_2^{tpt 0} ≤ Σ (trapezoids) + ∫_2^{tpt N}`. -/
lemma I4_partial (N : ℕ) (hN : N ≤ 103) :
    ∫ x in (2:ℝ)..tpt 0, f4 x ≤
      (∑ k ∈ Finset.range N, (tpt k - tpt (k+1)) * (f4 (tpt k) + f4 (tpt (k+1)))/2)
        + ∫ x in (2:ℝ)..tpt N, f4 x := by
  induction N with
  | zero => simp
  | succ n ih =>
    have hn : n ≤ 103 := le_trans (Nat.le_succ n) hN
    have hn1 : n + 1 ≤ 103 := hN
    have h2n : (2:ℝ) ≤ tpt n := two_le_tpt hn
    have h2n1 : (2:ℝ) ≤ tpt (n+1) := two_le_tpt hn1
    have hanti : tpt (n+1) ≤ tpt n := tpt_anti (Nat.le_succ n)
    have hsplit : (∫ x in (2:ℝ)..tpt (n+1), f4 x) + (∫ x in (tpt (n+1))..tpt n, f4 x)
        = ∫ x in (2:ℝ)..tpt n, f4 x :=
      intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_f4 le_rfl h2n1)
        (intervalIntegrable_f4 h2n1 h2n)
    have hstep0 := integral_f4_le_trapz (a := tpt (n+1)) (b := tpt n) h2n1 hanti
    have hstep : ∫ x in (tpt (n+1))..tpt n, f4 x ≤
        (tpt n - tpt (n+1)) * (f4 (tpt n) + f4 (tpt (n+1)))/2 := by
      rw [add_comm (f4 (tpt (n+1))) (f4 (tpt n))] at hstep0
      exact hstep0
    have ih' := ih hn
    have key : (∑ k ∈ Finset.range n,
          (tpt k - tpt (k+1)) * (f4 (tpt k) + f4 (tpt (k+1)))/2)
          + ∫ x in (2:ℝ)..tpt n, f4 x ≤
        (∑ k ∈ Finset.range (n+1),
          (tpt k - tpt (k+1)) * (f4 (tpt k) + f4 (tpt (k+1)))/2)
          + ∫ x in (2:ℝ)..tpt (n+1), f4 x := by
      rw [Finset.sum_range_succ, ← hsplit]
      linarith
    exact ih'.trans key

/-- `∫_2^{exp 11} dt/(log t)^4 ≤ 10.33`, the numerical core. -/
lemma I4_exp11_le : ∫ x in (2:ℝ)..exp 11, f4 x ≤ 10.33 := by
  have hpart := I4_partial 103 le_rfl
  rw [tpt_zero] at hpart
  have hCt103 : Ct 103 = 0.059970 := by simp only [Ct]
  have hlast : ∫ x in (2:ℝ)..tpt 103, f4 x ≤ Ct 103 := by
    refine (integral_f4_le_trapz (a := 2) (b := tpt 103) le_rfl two_le_tpt_103).trans ?_
    have hle : tpt 103 ≤ 59874.142 * (904839/1000000)^103 := exp_shift_le10 103
    have hbase : (2:ℝ) ≤ 59874.142 * (904839/1000000)^103 := by norm_num
    have hd : tpt 103 - 2 ≤ 59874.142 * (904839/1000000)^103 - 2 := by linarith
    have hf2 : f4 2 ≤ ((0.6931471803:ℝ)^4)⁻¹ := by
      have hlog : (0.6931471803:ℝ) ≤ log 2 := le_of_lt Real.log_two_gt_d9
      have h0 : (0:ℝ) < 0.6931471803 := by norm_num
      have hp : (0.6931471803:ℝ)^4 ≤ (log 2)^4 := pow_le_pow_left₀ h0.le hlog 4
      have h6 := one_div_le_one_div_of_le (by positivity : (0:ℝ) < (0.6931471803:ℝ)^4) hp
      simpa [f4, one_div] using h6
    have hfl : f4 (tpt 103) = ((0.7:ℝ)^4)⁻¹ := by
      simp only [tpt, f4, Real.log_exp]
      norm_num
    have hS : f4 2 + f4 (tpt 103) ≤ ((0.6931471803:ℝ)^4)⁻¹ + ((0.7:ℝ)^4)⁻¹ := by
      rw [hfl]; linarith
    have hSn : (0:ℝ) ≤ f4 2 + f4 (tpt 103) := by
      have h1 : (0:ℝ) ≤ f4 2 := by simp only [f4]; positivity
      have h2 : (0:ℝ) ≤ f4 (tpt 103) := by simp only [f4]; positivity
      linarith
    have hb : (tpt 103 - 2) * (f4 2 + f4 (tpt 103))/2 ≤
        (59874.142 * (904839/1000000)^103 - 2) *
          (((0.6931471803:ℝ)^4)⁻¹ + ((0.7:ℝ)^4)⁻¹)/2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact mul_le_mul hd hS hSn (by linarith)
    rw [hCt103]
    refine hb.trans ?_
    norm_num
  have hsum : (∑ k ∈ Finset.range 103,
        (tpt k - tpt (k+1)) * (f4 (tpt k) + f4 (tpt (k+1)))/2)
      ≤ (∑ k ∈ Finset.range 103, Ct k) := by
    apply Finset.sum_le_sum
    intro k hk
    exact (term_le_Db k).trans (Db_le_Ct k (Finset.mem_range.mp hk))
  have hcsum : (∑ k ∈ Finset.range 103, Ct k) + Ct 103 ≤ 10.33 := by
    have h := Ct_sum_le
    rw [Finset.sum_range_succ] at h
    exact h
  linarith

/-! ## Integrability of the integrands `(log t)^{-k}` -/

lemma continuousOn_logpow_inv {k : ℕ} :
    ContinuousOn (fun t : ℝ => ((log t)^k)⁻¹) (Ici (2:ℝ)) := by
  have h0 : ContinuousOn (fun t : ℝ => log t) (Ici (2:ℝ)) := by
    apply Real.continuousOn_log.mono
    intro x hx
    have hx2 : (2:ℝ) ≤ x := hx
    simp only [mem_compl_iff, mem_singleton_iff]
    linarith
  have h1 : ContinuousOn (fun t : ℝ => (log t)^k) (Ici (2:ℝ)) := h0.pow k
  refine h1.inv₀ (fun x hx => ?_)
  have hx2 : (2:ℝ) ≤ x := hx
  have hpos : 0 < log x := log_pos (by linarith)
  positivity

lemma ii_logpow_inv {k : ℕ} {a b : ℝ} (ha : 2 ≤ a) (hb : 2 ≤ b) :
    IntervalIntegrable (fun t : ℝ => ((log t)^k)⁻¹) volume a b := by
  apply ContinuousOn.intervalIntegrable
  rcases le_total a b with h | h
  · rw [uIcc_of_le h]
    exact continuousOn_logpow_inv.mono (by intro x hx; exact le_trans ha hx.1)
  · rw [uIcc_of_ge h]
    exact continuousOn_logpow_inv.mono (by intro x hx; exact le_trans hb hx.1)

lemma continuousOn_f4_Ioi : ContinuousOn f4 (Ioi (1:ℝ)) := by
  have h0 : ContinuousOn (fun t : ℝ => log t) (Ioi (1:ℝ)) := by
    apply Real.continuousOn_log.mono
    intro x hx
    have hx1 : (1:ℝ) < x := hx
    simp only [mem_compl_iff, mem_singleton_iff]
    linarith
  have h1 : ContinuousOn (fun t : ℝ => (log t)^4) (Ioi (1:ℝ)) := h0.pow 4
  refine h1.inv₀ (fun x hx => ?_)
  have hx1 : (1:ℝ) < x := hx
  have hpos : 0 < log x := log_pos hx1
  positivity

lemma intervalIntegrable_f4_Ioi {a b : ℝ} (ha : 1 < a) (hb : 1 < b) :
    IntervalIntegrable f4 volume a b := by
  apply ContinuousOn.intervalIntegrable
  rcases le_total a b with h | h
  · rw [uIcc_of_le h]
    exact continuousOn_f4_Ioi.mono (by intro x hx; exact lt_of_lt_of_le ha hx.1)
  · rw [uIcc_of_ge h]
    exact continuousOn_f4_Ioi.mono (by intro x hx; exact lt_of_lt_of_le hb hx.1)

/-! ## The partial integrals `IL k y = ∫_2^y dt/(log t)^k` -/

/-- `IL k y = ∫_2^y dt / (log t)^k`. -/
noncomputable def IL (k : ℕ) (y : ℝ) : ℝ := ∫ t in (2:ℝ)..y, ((log t)^k)⁻¹

/-- The partial integral `∫_2^y dt/(log t)^4`, the same as `IL 4`. -/
noncomputable def I4f (y : ℝ) : ℝ := ∫ t in (2:ℝ)..y, f4 t

/-- One integration by parts: `∫_2^y dt/log t = y/log y - 2/log 2 + ∫_2^y dt/(log t)²`. -/
lemma IL_rec1 {y : ℝ} (hy : 2 ≤ y) : IL 1 y = y/log y - 2/log 2 + IL 2 y := by
  have hderiv : ∀ t ∈ uIcc (2:ℝ) y, HasDerivAt (fun s : ℝ => s/log s) (1/log t - 1/(log t)^2) t := by
    intro t ht
    rw [uIcc_of_le hy] at ht
    have ht2 : (2:ℝ) ≤ t := ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlog : log t ≠ 0 := (log_pos (by linarith)).ne'
    have h1 : HasDerivAt (fun s : ℝ => log s) t⁻¹ t := hasDerivAt_log ht0
    have h2 : HasDerivAt (fun s : ℝ => (log s)⁻¹) (-(t⁻¹) / (log t)^2) t := h1.inv hlog
    have h3 := (hasDerivAt_id t).mul h2
    have hval : 1 * (log t)⁻¹ + t * (-(t⁻¹) / (log t)^2) = 1/log t - 1/(log t)^2 := by
      field_simp
      ring
    rw [← hval]
    have hfun : (fun s : ℝ => s/log s) = id * (fun s : ℝ => (log s)⁻¹) := by
      funext s; simp [div_eq_mul_inv]
    rw [hfun]
    exact h3
  have ha : IntervalIntegrable (fun t : ℝ => 1/log t) volume 2 y := by
    simpa using ii_logpow_inv (k := 1) le_rfl hy
  have hb : IntervalIntegrable (fun t : ℝ => 1/(log t)^2) volume 2 y := by
    simpa using ii_logpow_inv (k := 2) le_rfl hy
  have hint : IntervalIntegrable (fun t : ℝ => 1/log t - 1/(log t)^2) volume 2 y := ha.sub hb
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_sub ha hb] at hInt
  have e1 : (∫ t in (2:ℝ)..y, 1/log t) = IL 1 y := by simp [IL, div_eq_mul_inv]
  have e2 : (∫ t in (2:ℝ)..y, 1/(log t)^2) = IL 2 y := by simp [IL, div_eq_mul_inv]
  rw [e1, e2] at hInt
  simp only [div_eq_mul_inv] at hInt ⊢
  linarith

/-- `∫_2^y dt/(log t)² = y/(log y)² - 2/(log 2)² + 2∫_2^y dt/(log t)³`. -/
lemma IL_rec2 {y : ℝ} (hy : 2 ≤ y) :
    IL 2 y = y/(log y)^2 - 2/(log 2)^2 + 2 * IL 3 y := by
  have hderiv : ∀ t ∈ uIcc (2:ℝ) y,
      HasDerivAt (fun s : ℝ => s/(log s)^2) (1/(log t)^2 - 2 * (1/(log t)^3)) t := by
    intro t ht
    rw [uIcc_of_le hy] at ht
    have ht2 : (2:ℝ) ≤ t := ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlog : log t ≠ 0 := (log_pos (by linarith)).ne'
    have h1 : HasDerivAt (fun s : ℝ => log s) t⁻¹ t := hasDerivAt_log ht0
    have h2 : HasDerivAt (fun s : ℝ => (log s)^2) (2 * log t * t⁻¹) t := by
      have hfun : (fun s : ℝ => (log s)^2) = (fun s : ℝ => log s)^2 := by
        funext s; rfl
      rw [hfun]
      simpa using h1.pow 2
    have h3 : HasDerivAt (fun s : ℝ => ((log s)^2)⁻¹)
        (-(2 * log t * t⁻¹) / ((log t)^2)^2) t := h2.inv (by positivity)
    have h4 := (hasDerivAt_id t).mul h3
    have hval : 1 * ((log t)^2)⁻¹ + t * (-(2 * log t * t⁻¹) / ((log t)^2)^2)
        = 1/(log t)^2 - 2 * (1/(log t)^3) := by
      field_simp
      ring
    rw [← hval]
    have hfun : (fun s : ℝ => s/(log s)^2) = id * (fun s : ℝ => ((log s)^2)⁻¹) := by
      funext s; simp [div_eq_mul_inv]
    rw [hfun]
    exact h4
  have ha : IntervalIntegrable (fun t : ℝ => 1/(log t)^2) volume 2 y := by
    simpa using ii_logpow_inv (k := 2) le_rfl hy
  have hb : IntervalIntegrable (fun t : ℝ => 2 * (1/(log t)^3)) volume 2 y := by
    have h := ii_logpow_inv (k := 3) (a := 2) (b := y) le_rfl hy
    simpa [mul_comm] using h.const_mul 2
  have hint : IntervalIntegrable (fun t : ℝ => 1/(log t)^2 - 2 * (1/(log t)^3)) volume 2 y :=
    ha.sub hb
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_sub ha hb, intervalIntegral.integral_const_mul] at hInt
  have e1 : (∫ t in (2:ℝ)..y, 1/(log t)^2) = IL 2 y := by simp [IL, div_eq_mul_inv]
  have e2 : (∫ t in (2:ℝ)..y, 1/(log t)^3) = IL 3 y := by simp [IL, div_eq_mul_inv]
  rw [e1, e2] at hInt
  simp only [div_eq_mul_inv] at hInt ⊢
  linarith

/-- `∫_2^y dt/(log t)³ = y/(log y)³ - 2/(log 2)³ + 3∫_2^y dt/(log t)⁴`. -/
lemma IL_rec3 {y : ℝ} (hy : 2 ≤ y) :
    IL 3 y = y/(log y)^3 - 2/(log 2)^3 + 3 * I4f y := by
  have hderiv : ∀ t ∈ uIcc (2:ℝ) y,
      HasDerivAt (fun s : ℝ => s/(log s)^3) (1/(log t)^3 - 3 * ((log t)^4)⁻¹) t := by
    intro t ht
    rw [uIcc_of_le hy] at ht
    have ht2 : (2:ℝ) ≤ t := ht.1
    have ht0 : t ≠ 0 := by linarith
    have hlog : log t ≠ 0 := (log_pos (by linarith)).ne'
    have h1 : HasDerivAt (fun s : ℝ => log s) t⁻¹ t := hasDerivAt_log ht0
    have h2 : HasDerivAt (fun s : ℝ => (log s)^3) (3 * (log t)^2 * t⁻¹) t := h1.pow 3
    have h3 : HasDerivAt (fun s : ℝ => ((log s)^3)⁻¹)
        (-(3 * (log t)^2 * t⁻¹) / ((log t)^3)^2) t := h2.inv (by positivity)
    have h4 := (hasDerivAt_id t).mul h3
    have hval : 1 * ((log t)^3)⁻¹ + t * (-(3 * (log t)^2 * t⁻¹) / ((log t)^3)^2)
        = 1/(log t)^3 - 3 * ((log t)^4)⁻¹ := by
      field_simp
      ring
    rw [← hval]
    have hfun : (fun s : ℝ => s/(log s)^3) = id * (fun s : ℝ => ((log s)^3)⁻¹) := by
      funext s; simp [div_eq_mul_inv]
    rw [hfun]
    exact h4
  have ha : IntervalIntegrable (fun t : ℝ => 1/(log t)^3) volume 2 y := by
    simpa using ii_logpow_inv (k := 3) le_rfl hy
  have hb : IntervalIntegrable (fun t : ℝ => 3 * ((log t)^4)⁻¹) volume 2 y := by
    have h := ii_logpow_inv (k := 4) (a := 2) (b := y) le_rfl hy
    simpa [mul_comm] using h.const_mul 3
  have hint : IntervalIntegrable (fun t : ℝ => 1/(log t)^3 - 3 * ((log t)^4)⁻¹) volume 2 y :=
    ha.sub hb
  have hInt := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [intervalIntegral.integral_sub ha hb, intervalIntegral.integral_const_mul] at hInt
  have e1 : (∫ t in (2:ℝ)..y, 1/(log t)^3) = IL 3 y := by simp [IL, div_eq_mul_inv]
  have e2 : (∫ t in (2:ℝ)..y, ((log t)^4)⁻¹) = I4f y := by simp [I4f, f4]
  rw [e1, e2] at hInt
  simp only [div_eq_mul_inv] at hInt ⊢
  linarith

/-- `A = 2/log 2 + 2/(log 2)² + 4/(log 2)³`, the constant of the expansion. -/
def Aexpr : ℝ := 2/log 2 + 2/(log 2)^2 + 4/(log 2)^3

lemma Aexpr_ge : (19.0592 : ℝ) ≤ Aexpr := by
  have h2 : (0.6931471803 : ℝ) ≤ log 2 := le_of_lt Real.log_two_gt_d9
  have h3 : log 2 ≤ 0.6931471808 := le_of_lt Real.log_two_lt_d9
  have h4 : (0:ℝ) < log 2 := by linarith
  have hsq : (log 2)^2 ≤ (0.6931471808:ℝ)^2 := pow_le_pow_left₀ h4.le h3 2
  have hcb : (log 2)^3 ≤ (0.6931471808:ℝ)^3 := pow_le_pow_left₀ h4.le h3 3
  have e1 : (2:ℝ)/0.6931471808 ≤ 2/log 2 := div_le_div_of_nonneg_left (by norm_num) h4 h3
  have e2 : (2:ℝ)/(0.6931471808)^2 ≤ 2/(log 2)^2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
  have e3 : (4:ℝ)/(0.6931471808)^3 ≤ 4/(log 2)^3 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hcb
  have e4 : (19.0592:ℝ) ≤ 2/(0.6931471808:ℝ) + 2/(0.6931471808:ℝ)^2 + 4/(0.6931471808:ℝ)^3 := by
    norm_num
  simp only [Aexpr]
  linarith

/-- The three integration-by-parts steps combined. -/
lemma IL_one_expansion {y : ℝ} (hy : 2 ≤ y) :
    IL 1 y = y/log y + y/(log y)^2 + 2 * (y/(log y)^3) - Aexpr + 6 * I4f y := by
  rw [IL_rec1 hy, IL_rec2 hy, IL_rec3 hy]
  simp only [Aexpr, div_eq_mul_inv]
  ring

/-! ## The monotonicity of `ψ y = y/(log y)³ - 6∫_2^y dt/(log t)^4` -/

lemma IL_one_eq (y : ℝ) : IL 1 y = ∫ t in (2:ℝ)..y, 1/log t := by
  simp [IL, div_eq_mul_inv]

lemma I4f_hasDerivAt {y : ℝ} (hy : 1 < y) : HasDerivAt I4f (f4 y) y := by
  have hcont : ContinuousAt f4 y := by
    have hfun : f4 = fun s : ℝ => ((log s)^4)⁻¹ := rfl
    rw [hfun]
    have h1 : ContinuousAt (fun s : ℝ => log s) y := Real.continuousAt_log (by linarith)
    refine (h1.pow 4).inv₀ ?_
    have hpos : 0 < log y := log_pos hy
    exact (pow_pos hpos 4).ne'
  have hsm : StronglyMeasurableAtFilter f4 (𝓝 y) volume := by
    have hcont' : ∀ x ∈ Ioi (1:ℝ), ContinuousAt f4 x := by
      intro x hx
      have hx1 : (1:ℝ) < x := hx
      have hfun : f4 = fun s : ℝ => ((log s)^4)⁻¹ := rfl
      rw [hfun]
      have h1 : ContinuousAt (fun s : ℝ => log s) x := Real.continuousAt_log (by linarith)
      refine (h1.pow 4).inv₀ ?_
      have hpos : 0 < log x := log_pos hx1
      exact (pow_pos hpos 4).ne'
    exact ContinuousAt.stronglyMeasurableAtFilter (s := Ioi (1:ℝ)) isOpen_Ioi hcont' y hy
  have hint : IntervalIntegrable f4 volume 2 y := intervalIntegrable_f4_Ioi (by norm_num) hy
  exact intervalIntegral.integral_hasDerivAt_right hint hsm hcont


lemma exp_eleven_ge : (59874.1414 : ℝ) ≤ exp 11 := by
  have h1 : exp (11 : ℝ) = exp 1 ^ 11 := by
    simpa using Real.exp_nat_mul (x := (1 : ℝ)) 11
  rw [h1]
  have h2 : (2.7182818283 : ℝ) ≤ exp 1 := le_of_lt Real.exp_one_gt_d9
  have h3 : (2.7182818283:ℝ)^11 ≤ exp 1^11 := pow_le_pow_left₀ (by norm_num) h2 11
  have h4 : (59874.1414:ℝ) ≤ (2.7182818283:ℝ)^11 := by norm_num
  linarith

lemma f4_antitone : AntitoneOn f4 (Ici (2:ℝ)) := by
  intro a ha b hb hab
  have ha2 : (2:ℝ) ≤ a := ha
  have hb2 : (2:ℝ) ≤ b := hb
  have ha1 : (1:ℝ) < a := by linarith
  have hb1 : (1:ℝ) < b := by linarith
  have hla : 0 < log a := log_pos ha1
  have h1 : log a ≤ log b := log_le_log (by linarith) hab
  have h2 : (log a)^4 ≤ (log b)^4 := pow_le_pow_left₀ hla.le h1 4
  simp only [f4]
  simpa [one_div] using one_div_le_one_div_of_le (pow_pos hla 4) h2

/-- A crude lower bound for the whole integral, enough to dominate the expansion constant. -/
lemma I4f_exp11_ge : (3.4:ℝ) ≤ I4f (exp 11) := by
  have hy2 : (2:ℝ) ≤ exp 11 := by
    have h := Real.add_one_le_exp (11:ℝ)
    linarith
  have hexp11 : (59874.1414 : ℝ) ≤ exp 11 := exp_eleven_ge
  have hmono : ∫ x in (2:ℝ)..(exp 11), f4 x ≥ (exp 11 - 2) * f4 (exp 11) := by
    have hc : IntervalIntegrable (fun _ : ℝ => f4 (exp 11)) volume 2 (exp 11) := intervalIntegrable_const
    have hexp2 : (2:ℝ) ≤ exp 11 := hy2
    have hle : ∀ x ∈ Icc (2:ℝ) (exp 11), f4 (exp 11) ≤ f4 x := by
      intro x hx
      have hx2 : (2:ℝ) ≤ x := hx.1
      exact f4_antitone (by simpa using hx2) hexp2 hx.2
    have := intervalIntegral.integral_mono_on hy2 hc (intervalIntegrable_f4 le_rfl hy2) hle
    rwa [intervalIntegral.integral_const, smul_eq_mul] at this
  have hf4 : f4 (exp 11) = ((11:ℝ)^4)⁻¹ := by simp only [f4, Real.log_exp]
  have hval : (3.4:ℝ) ≤ (exp 11 - 2) * f4 (exp 11) := by
    rw [hf4]
    have h5 : (59874.1414 - 2) * ((11:ℝ)^4)⁻¹ ≤ (exp 11 - 2) * ((11:ℝ)^4)⁻¹ := by
      apply mul_le_mul_of_nonneg_right _ (by positivity)
      linarith
    have h6 : (3.4:ℝ) ≤ (59874.1414 - 2) * ((11:ℝ)^4)⁻¹ := by norm_num
    linarith
  simp only [I4f]
  linarith

lemma Aexpr_le : Aexpr ≤ 19.0594 := by
  have h2 : (0.6931471803 : ℝ) ≤ log 2 := le_of_lt Real.log_two_gt_d9
  have h3 : (0:ℝ) < 0.6931471803 := by norm_num
  have hsq : (0.6931471803:ℝ)^2 ≤ (log 2)^2 := pow_le_pow_left₀ h3.le h2 2
  have hcb : (0.6931471803:ℝ)^3 ≤ (log 2)^3 := pow_le_pow_left₀ h3.le h2 3
  have e1 : (2:ℝ)/log 2 ≤ 2/0.6931471803 := div_le_div_of_nonneg_left (by norm_num) h3 h2
  have e2 : (2:ℝ)/(log 2)^2 ≤ 2/(0.6931471803)^2 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hsq
  have e3 : (4:ℝ)/(log 2)^3 ≤ 4/(0.6931471803)^3 :=
    div_le_div_of_nonneg_left (by norm_num) (by positivity) hcb
  have e4 : (2:ℝ)/0.6931471803 + 2/(0.6931471803)^2 + 4/(0.6931471803)^3 ≤ 19.0594 := by
    norm_num
  simp only [Aexpr]
  linarith

/-- `ψ y = y/(log y)³ - 6∫_2^y dt/(log t)^4`. -/
noncomputable abbrev psi (y : ℝ) : ℝ := y/(log y)^3 - 6 * I4f y

lemma psi_hasDerivAt {y : ℝ} (hy : 1 < y) : HasDerivAt psi ((log y - 9)/(log y)^4) y := by
  have hlog : (0:ℝ) < log y := log_pos hy
  have hy0 : y ≠ 0 := by linarith
  have h2 : HasDerivAt (fun s : ℝ => (log s)^3) (3 * (log y)^2 * y⁻¹) y := by
    have hfun : (fun s : ℝ => (log s)^3) = (fun s : ℝ => log s)^3 := by
      funext s; rfl
    rw [hfun]
    simpa using (hasDerivAt_log hy0).pow 3
  have h3 : HasDerivAt (fun s : ℝ => ((log s)^3)⁻¹)
      (-(3 * (log y)^2 * y⁻¹) / ((log y)^3)^2) y := h2.inv (by positivity)
  have h4 := (hasDerivAt_id y).mul h3
  have hval1 : 1 * ((log y)^3)⁻¹ + y * (-(3 * (log y)^2 * y⁻¹) / ((log y)^3)^2)
      = ((log y)^3)⁻¹ - 3 * ((log y)^4)⁻¹ := by
    field_simp
    ring
  have hfirst : HasDerivAt (fun s : ℝ => s/(log s)^3) (((log y)^3)⁻¹ - 3 * ((log y)^4)⁻¹) y := by
    rw [← hval1]
    have hfun : (fun s : ℝ => s/(log s)^3) = id * (fun s : ℝ => ((log s)^3)⁻¹) := by
      funext s; simp [div_eq_mul_inv]
    rw [hfun]
    exact h4
  have hsecond : HasDerivAt (fun s : ℝ => 6 * I4f s) (6 * f4 y) y :=
    (I4f_hasDerivAt hy).const_mul 6
  have hsum := hfirst.sub hsecond
  have hval2 : ((log y)^3)⁻¹ - 3 * ((log y)^4)⁻¹ - 6 * f4 y = (log y - 9)/(log y)^4 := by
    simp only [f4]
    field_simp
    ring
  have hsum' : HasDerivAt (fun s : ℝ => s / (log s)^3 - 6 * I4f s)
      (((log y)^3)⁻¹ - 3 * ((log y)^4)⁻¹ - 6 * f4 y) y := hsum
  rw [hval2] at hsum'
  simpa only [psi] using hsum'

lemma psi_mono : MonotoneOn psi (Ici (exp 11)) := by
  have hexp1 : (1:ℝ) < exp 11 := by
    have h := Real.add_one_le_exp (11:ℝ)
    linarith
  refine monotoneOn_of_deriv_nonneg (convex_Ici _) ?_ ?_ ?_
  · intro y hy
    have hy1 : (1:ℝ) < y := lt_of_lt_of_le hexp1 hy
    exact (psi_hasDerivAt hy1).continuousAt.continuousWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    have hy1 : (1:ℝ) < y := lt_of_lt_of_le hexp1 (le_of_lt hy)
    exact (psi_hasDerivAt hy1).differentiableAt.differentiableWithinAt
  · intro y hy
    rw [interior_Ici] at hy
    have hy1 : (1:ℝ) < y := lt_of_lt_of_le hexp1 (le_of_lt hy)
    rw [(psi_hasDerivAt hy1).deriv]
    have hL : (11:ℝ) ≤ log y := by
      have h := Real.log_le_log (Real.exp_pos 11) (le_of_lt hy)
      rwa [Real.log_exp] at h
    have hpos : (0:ℝ) < log y := by linarith
    apply div_nonneg _ (by positivity)
    linarith


/-- **The journal's two logarithmic integral bounds**, journal Lemma 11 proof p. 1228. -/
theorem li_bounds_large_proof (n : ℕ) (hn : exp 11 ≤ (n : ℝ)) :
    (1 + 1 / log (n : ℝ)) * n / log n ≤ LeanLab.BS2022GRH.liPV n ∧
      LeanLab.BS2022GRH.liPV n ≤ (1 + 1 / log (n : ℝ) + 3 / log n ^ 2) * n / log n := by
  have hy : (2:ℝ) ≤ (n:ℝ) := by
    have h : (2:ℝ) ≤ exp 11 := by
      have h2 := Real.add_one_le_exp (11:ℝ)
      linarith
    linarith
  have hy1 : (1:ℝ) < (n:ℝ) := by linarith
  have hL : (0:ℝ) < log (n:ℝ) := log_pos hy1
  have hL11 : (11:ℝ) ≤ log (n:ℝ) := by
    have h := Real.log_le_log (Real.exp_pos 11) hn
    rwa [Real.log_exp] at h
  constructor
  · rw [LeanLab.BS2022GRH.liPV_eq_add hy, ← IL_one_eq, IL_one_expansion hy]
    have hli2 : (0:ℝ) ≤ LeanLab.BS2022GRH.liPV 2 := (LeanLab.BS2022GRH.liPV_two_le).1
    have hAup : Aexpr ≤ 19.0594 := Aexpr_le
    have hI4up : (3.4:ℝ) ≤ I4f (n:ℝ) := by
      have h1 : (3.4:ℝ) ≤ I4f (exp 11) := I4f_exp11_ge
      have hsplit : I4f (n:ℝ) = I4f (exp 11) + ∫ x in (exp 11)..(n:ℝ), f4 x := by
        rw [I4f, I4f]
        rw [intervalIntegral.integral_add_adjacent_intervals (intervalIntegrable_f4 le_rfl (by
          have h := Real.add_one_le_exp (11:ℝ); linarith)) (intervalIntegrable_f4 (by
          have h := Real.add_one_le_exp (11:ℝ); linarith) hy)]
      have h2 : (0:ℝ) ≤ ∫ x in (exp 11)..(n:ℝ), f4 x := by
        apply intervalIntegral.integral_nonneg hn
        intro t ht
        simp only [f4]
        positivity
      linarith
    have expand : (1 + 1 / log (n:ℝ)) * (n:ℝ)/log (n:ℝ)
        = (n:ℝ)/log (n:ℝ) + (n:ℝ)/(log (n:ℝ))^2 := by
      field_simp
      try ring
    rw [expand]
    simp only [div_eq_mul_inv] at hI4up ⊢
    have hpos : (0:ℝ) ≤ 2 * ((n:ℝ) * ((log (n:ℝ))^3)⁻¹) := by positivity
    linarith [hli2, hI4up, hAup, hpos]
  · rw [LeanLab.BS2022GRH.liPV_eq_add hy, ← IL_one_eq, IL_one_expansion hy]
    have hli2 : LeanLab.BS2022GRH.liPV 2 ≤ 2 := (LeanLab.BS2022GRH.liPV_two_le).2
    have hA := Aexpr_ge
    have hpsi : psi (exp 11) ≤ psi (n:ℝ) :=
      psi_mono (mem_Ici.mpr le_rfl) (hn : (n:ℝ) ∈ Ici (exp 11)) hn
    have hexp11 : (59874.1414 : ℝ) ≤ exp 11 := exp_eleven_ge
    have hI4e : I4f (exp 11) ≤ 10.33 := I4_exp11_le
    have hI4 : 6 * I4f (n:ℝ) ≤ (n:ℝ)/(log (n:ℝ))^3 + (Aexpr - 2) := by
      have hbase : -(Aexpr - 2) ≤ psi (exp 11) := by
        have h11 : ((11:ℝ))^3 = 1331 := by norm_num
        have h11' : ((11:ℝ)) * 11 * 11 = 1331 := by norm_num
        simp only [psi, Real.log_exp, div_eq_mul_inv, h11]
        have h1 : (44.984 : ℝ) ≤ exp 11 / 1331 := by
          rw [le_div_iff₀ (by norm_num : (0:ℝ) < 1331)]
          linarith
        linarith
      have hle : psi (exp 11) ≤ psi (n:ℝ) := hpsi
      simp only [psi, div_eq_mul_inv] at hle hbase ⊢
      linarith
    have expand : (1 + 1 / log (n:ℝ) + 3 / log (n:ℝ) ^ 2) * (n:ℝ)/log (n:ℝ)
        = (n:ℝ)/log (n:ℝ) + (n:ℝ)/(log (n:ℝ))^2 + 3 * ((n:ℝ)/(log (n:ℝ))^3) := by
      field_simp
      try ring
    rw [expand]
    simp only [div_eq_mul_inv] at hI4 hli2 ⊢
    linarith

end
end LiProof232

/-- LEAF. The two logarithmic integral bounds printed in the proof of Lemma 11, p. 1228.
The principal value convention is the existing lab liPV. -/
theorem li_bounds_large (n : ℕ) (hn : exp 11 ≤ (n : ℝ)) :
    (1 + 1 / log (n : ℝ)) * n / log n ≤ liPV n ∧
      liPV n ≤ (1 + 1 / log (n : ℝ) + 3 / log n ^ 2) * n / log n := by
  exact LiProof232.li_bounds_large_proof n hn

/-- LEAF. The upper half of journal Lemma 10 at z, pp. 1227 and 1232 display 23.
The lab UNfull convention is retained. This is a non-strict upper estimate. -/
theorem density_upper (n : ℕ) (hn : exp (exp 10) ≤ (n : ℝ)) (hev : Even n) :
    DecompC169a.density n ≤ 8 * UNfull n / log n *
      (1 + 0.62 * log n / (n : ℝ) ^ (1 / 16 : ℝ)) := by
  sorry

end LeanLab.BS2022GRH.PublishedInputs232
#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma5_mu
#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma5_phi
#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma1_schoenfeld
#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma4_robin
#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma2_theta

#print axioms LeanLab.BS2022GRH.PublishedInputs232.weighted_reciprocal_primes

#print axioms LeanLab.BS2022GRH.PublishedInputs232.reciprocal_prime_interval

#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma5_mu_one_instance
#print axioms LeanLab.BS2022GRH.PublishedInputs232.lemma5_phi_two_instance

#print axioms LeanLab.BS2022GRH.PublishedInputs232.li_bounds_large
#print axioms LeanLab.BS2022GRH.PublishedInputs232.density_upper
