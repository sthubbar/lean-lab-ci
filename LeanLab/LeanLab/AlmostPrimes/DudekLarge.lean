import LeanLab.PNTSieve.BrunTitchmarshAP
import LeanLab.AlmostPrimes.BJSThm5At3273
import LeanLab.Common.Goldbach

/-!
# Dudek's prime plus square-free theorem for large even N

Unit U-5500, CLOUD 20261019T1218Z-cloud24. AI wrote the Lean code. Known mathematics: the
argument is the classical one behind Dudek 2017, BJS Theorem 53, with the lab's own
Brun-Titchmarsh `PNTSieve.BrunTitchmarshAP.brunTitchmarsh_ap` and Mathlib's `Chebyshev.pi_ge`
in place of Montgomery-Vaughan and Rosser-Schoenfeld, so the threshold is far larger.

`dudek_even_large`: every even `N ≥ exp 12000` is `p + m` with `p` prime and `m ≥ 1` square-free.
No cited input.

Proof. Let `A` be the primes in `[3, N]`; `#A ≥ π N - 1`. If `N - p` is not square-free for every
`p ∈ A`, some odd prime `r` has `r² ∣ N - p`. For `r ≤ Q` the prime `p` lies in the class
`N mod r²`, at most `2N/(r(r - 1) log z) + 4z(1 + log z)³` primes by Brun-Titchmarsh; for
`r > Q` the number `N - p ≤ N` is a multiple of `r²`, at most `N/r²` choices. With
`Σ_{r ≥ 3 prime} 1/(r(r - 1)) ≤ 3/10`, `z = N^{19/20}` and `Q = 100⌈log N⌉`, the bad primes number
at most `0.6316 N/log N + o(N/log N)`, below `π N - 1 ≥ 0.6931 N/log N - o(N/log N)`.

`bjs_thm5_of_3273_small` is BJS Theorem 5 with Dudek's input cut to even `N < exp 12000`.
-/

open Finset Real

noncomputable section

namespace LeanLab.AlmostPrimes.DudekLarge

/-- Telescoping: `Σ_{a < n ≤ M} 1/(n(n - 1)) = 1/a - 1/M` for `1 ≤ a ≤ M`. -/
theorem sum_Ioc_inv_mul_pred {a : ℕ} (ha : 1 ≤ a) :
    ∀ M : ℕ, a ≤ M →
      ∑ n ∈ Ioc a M, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) = 1 / a - 1 / M := by
  intro M hM
  induction M, hM using Nat.le_induction with
  | base => simp
  | succ M hM ih =>
    rw [Finset.sum_Ioc_succ_top (by omega), ih]
    have hM0 : (M : ℝ) ≠ 0 := by exact_mod_cast (show M ≠ 0 by omega)
    have hM1 : (M : ℝ) + 1 ≠ 0 := by positivity
    push_cast
    rw [show (M : ℝ) + 1 - 1 = M by ring]
    field_simp
    ring

theorem sum_Ioc_inv_mul_pred_le {a : ℕ} (ha : 1 ≤ a) (M : ℕ) :
    ∑ n ∈ Ioc a M, (1 : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) ≤ 1 / a := by
  rcases le_or_gt a M with h | h
  · rw [sum_Ioc_inv_mul_pred ha M h]
    have : (0 : ℝ) ≤ 1 / M := by positivity
    linarith
  · rw [Finset.Ioc_eq_empty (by omega)]
    simp

/-- `Σ_{3 ≤ r ≤ Q, r prime} 1/(r(r - 1)) ≤ 3/10`; the true value of the full sum is `0.2731`. -/
theorem sum_prime_inv_le (Q : ℕ) :
    ∑ r ∈ (Icc 3 Q).filter Nat.Prime, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) ≤ 3 / 10 := by
  have hsub : (Icc 3 Q).filter Nat.Prime ⊆ ((Icc 3 31).filter Nat.Prime) ∪ Ioc 31 Q := by
    intro r hr
    simp only [mem_filter, mem_Icc] at hr
    simp only [mem_union, mem_filter, mem_Icc, mem_Ioc]
    by_cases h : r ≤ 31
    · exact Or.inl ⟨⟨hr.1.1, h⟩, hr.2⟩
    · exact Or.inr ⟨by omega, hr.1.2⟩
  have hnn : ∀ r ∈ ((Icc 3 31).filter Nat.Prime) ∪ Ioc 31 Q,
      (0 : ℝ) ≤ 1 / ((r : ℝ) * ((r : ℝ) - 1)) := by
    intro r hr
    have : 1 ≤ r := by
      simp only [mem_union, mem_filter, mem_Icc, mem_Ioc] at hr; omega
    have : (1 : ℝ) ≤ r := by exact_mod_cast this
    have : (0 : ℝ) ≤ (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
    positivity
  calc _ ≤ ∑ r ∈ ((Icc 3 31).filter Nat.Prime) ∪ Ioc 31 Q,
          (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) := sum_le_sum_of_subset_of_nonneg hsub
            (fun r hr _ => hnn r hr)
    _ ≤ ∑ r ∈ (Icc 3 31).filter Nat.Prime, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) +
          ∑ r ∈ Ioc 31 Q, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) := by
          rw [sum_union]
          rw [Finset.disjoint_left]
          intro r h1 h2
          simp only [mem_filter, mem_Icc, mem_Ioc] at h1 h2
          omega
    _ ≤ ∑ r ∈ (Icc 3 31).filter Nat.Prime, (1 : ℝ) / ((r : ℝ) * ((r : ℝ) - 1)) + 1 / 31 := by
          have := sum_Ioc_inv_mul_pred_le (a := 31) (by norm_num) Q
          push_cast at this
          linarith
    _ ≤ 3 / 10 := by
          have hS : (Icc 3 31).filter Nat.Prime = {3, 5, 7, 11, 13, 17, 19, 23, 29, 31} := by
            decide
          rw [hS]
          simp
          norm_num

/-- The primes `p ≤ N + 1` in the class `N mod r²`, the set Brun-Titchmarsh bounds. -/
def cls (N r : ℕ) : Finset ℕ :=
  (Icc 1 (N + 1)).filter (fun p => p.Prime ∧ p % (r ^ 2) = N % (r ^ 2))

/-- At most `N / n²` numbers `p < N` have `n² ∣ N - p`. -/
theorem card_dvd_sub_le (N n : ℕ) :
    ((range N).filter (fun p => n ^ 2 ∣ N - p)).card ≤ N / n ^ 2 := by
  rw [← Nat.Ioc_filter_dvd_card_eq_div]
  apply card_le_card_of_injOn (fun p => N - p)
  · intro p hp
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hp
    simp only [coe_filter, mem_Ioc, Set.mem_ofPred_eq]
    exact ⟨⟨by omega, by omega⟩, hp.2⟩
  · intro p hp p' hp' h
    simp only [coe_filter, mem_range, Set.mem_ofPred_eq] at hp hp'
    simp only at h
    omega

/-- **Counting step.** If no even `N ≥ 4` decomposition `p + m` with `m` square-free exists, then
`π N - 1` is at most the Brun-Titchmarsh classes for odd primes `r ≤ Q` plus `Σ_{Q < n ≤ N} N/n²`. -/
theorem card_le_of_no_rep {N : ℕ} (Q : ℕ) (hE : Even N) (h4 : 4 ≤ N)
    (hno : ¬ ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m) :
    (Nat.primeCounting N : ℝ) - 1 ≤
      ∑ r ∈ (Icc 3 Q).filter Nat.Prime, ((cls N r).card : ℝ) +
        ∑ n ∈ Ioc Q N, ((N / n ^ 2 : ℕ) : ℝ) := by
  classical
  set A := (Icc 3 N).filter Nat.Prime with hA
  have h1 : Nat.primeCounting N ≤ A.card + 1 := by
    rw [Nat.primeCounting, ← Nat.primesBelow_card_eq_primeCounting']
    calc (N + 1).primesBelow.card ≤ (insert 2 A).card := by
          apply card_le_card
          intro p hp
          rw [Nat.mem_primesBelow] at hp
          rw [mem_insert, hA, mem_filter, mem_Icc]
          by_cases h2 : p = 2
          · exact Or.inl h2
          · have := hp.2.two_le
            exact Or.inr ⟨⟨by omega, by omega⟩, hp.2⟩
      _ ≤ A.card + 1 := card_insert_le _ _
  set B1 := ((Icc 3 Q).filter Nat.Prime).biUnion (fun r => cls N r) with hB1
  set B2 := (Ioc Q N).biUnion (fun n => (range N).filter (fun p => n ^ 2 ∣ N - p)) with hB2
  have hsub : A ⊆ B1 ∪ B2 := by
    intro p hp
    rw [hA, mem_filter, mem_Icc] at hp
    obtain ⟨⟨hp3, hpN⟩, hp⟩ := hp
    have hpodd : Odd p := hp.odd_of_ne_two (by omega)
    have hpne : p ≠ N := by
      rintro rfl
      exact (Nat.not_even_iff_odd.mpr hpodd) hE
    have hm : ¬ Squarefree (N - p) := by
      intro hsq
      exact hno ⟨p, N - p, hp, by omega, hsq, by omega⟩
    rw [Nat.squarefree_iff_prime_squarefree] at hm
    push Not at hm
    obtain ⟨r, hr, hrr⟩ := hm
    have hmodd : Odd (N - p) := by
      rcases hE with ⟨k, hk⟩
      rcases hpodd with ⟨j, hj⟩
      exact ⟨k - j - 1, by omega⟩
    have hr2 : r ≠ 2 := by
      rintro rfl
      have : 2 ∣ N - p := (Dvd.intro 2 rfl).trans hrr
      exact (Nat.not_even_iff_odd.mpr hmodd) (even_iff_two_dvd.mpr this)
    have hr3 : 3 ≤ r := by have := hr.two_le; omega
    have hrr' : r ^ 2 ∣ N - p := by rw [sq]; exact hrr
    rw [mem_union]
    by_cases hQ : r ≤ Q
    · left
      rw [hB1, mem_biUnion]
      refine ⟨r, by rw [mem_filter, mem_Icc]; exact ⟨⟨hr3, hQ⟩, hr⟩, ?_⟩
      rw [cls, mem_filter, mem_Icc]
      refine ⟨⟨by omega, by omega⟩, hp, ?_⟩
      exact ((Nat.modEq_iff_dvd' hpN).mpr hrr')
    · right
      rw [hB2, mem_biUnion]
      have hpos : 0 < N - p := by omega
      have hrle : r ≤ N - p := by
        have := Nat.le_of_dvd hpos hrr
        nlinarith
      refine ⟨r, by rw [mem_Ioc]; omega, ?_⟩
      rw [mem_filter, mem_range]
      exact ⟨by omega, hrr'⟩
  have hcard : A.card ≤ ∑ r ∈ (Icc 3 Q).filter Nat.Prime, (cls N r).card +
      ∑ n ∈ Ioc Q N, N / n ^ 2 := by
    calc A.card ≤ (B1 ∪ B2).card := card_le_card hsub
      _ ≤ B1.card + B2.card := card_union_le _ _
      _ ≤ _ := by
        apply add_le_add
        · exact card_biUnion_le
        · exact card_biUnion_le.trans (sum_le_sum fun n _ => card_dvd_sub_le N n)
  have : (Nat.primeCounting N : ℝ) ≤ (A.card : ℝ) + 1 := by exact_mod_cast h1
  have h2 : (A.card : ℝ) ≤ ∑ r ∈ (Icc 3 Q).filter Nat.Prime, ((cls N r).card : ℝ) +
      ∑ n ∈ Ioc Q N, ((N / n ^ 2 : ℕ) : ℝ) := by exact_mod_cast hcard
  linarith

/-- **Brun-Titchmarsh for the class `N mod r²`**, from the lab's `brunTitchmarsh_ap`. -/
theorem cls_card_le {N r : ℕ} (hr : r.Prime) (hN : 0 < N) {z : ℝ} (hz : 1 < z) :
    ((cls N r).card : ℝ) ≤
      2 * N / ((r : ℝ) * ((r : ℝ) - 1) * Real.log z) + 4 * z * (1 + Real.log z) ^ 3 := by
  have hbt := LeanLab.PNTSieve.BrunTitchmarshAP.brunTitchmarsh_ap 1 (N : ℝ) z (r ^ 2) N
    one_pos (by exact_mod_cast hN) hz (pow_pos hr.pos 2)
  have hc : ⌈(1 : ℝ)⌉₊ = 1 := Nat.ceil_one
  have hf : ⌊(1 : ℝ) + N⌋₊ = N + 1 := by
    rw [show (1 : ℝ) + N = ((N + 1 : ℕ) : ℝ) by push_cast; ring, Nat.floor_natCast]
  rw [hc, hf, Nat.totient_prime_pow hr two_pos] at hbt
  have hr1 : 1 ≤ r := hr.one_lt.le
  have hcast : (((r ^ (2 - 1) * (r - 1) : ℕ)) : ℝ) = (r : ℝ) * ((r : ℝ) - 1) := by
    rw [Nat.cast_mul, Nat.cast_sub hr1]; simp
  rw [hcast] at hbt
  exact hbt

/-- `10⁴ (L + 1)⁵ ≤ e^{L/20}` for `L ≥ 12000`, from `e^t ≥ t¹²/12!` at `t = L/20 ≥ 600`. -/
theorem poly_le_exp {L : ℝ} (hL : 12000 ≤ L) : 10000 * (L + 1) ^ 5 ≤ exp (L / 20) := by
  set t := L / 20 with ht
  have ht600 : 600 ≤ t := by rw [ht]; linarith
  have h1 : L + 1 ≤ 21 * t := by rw [ht]; linarith
  have h5 : (L + 1) ^ 5 ≤ (21 * t) ^ 5 := pow_le_pow_left₀ (by linarith) h1 5
  have hexp := Real.pow_div_factorial_le_exp t (by linarith : 0 ≤ t) 12
  have hf : ((Nat.factorial 12 : ℕ) : ℝ) = 479001600 := by norm_num [Nat.factorial]
  rw [hf] at hexp
  have h7 : (600 : ℝ) ^ 7 ≤ t ^ 7 := pow_le_pow_left₀ (by norm_num) ht600 7
  have ht5 : 0 ≤ t ^ 5 := by positivity
  have hprod : (600 : ℝ) ^ 7 * t ^ 5 ≤ t ^ 7 * t ^ 5 := mul_le_mul_of_nonneg_right h7 ht5
  have h12 : t ^ 12 = t ^ 7 * t ^ 5 := by ring
  have h21 : (21 * t) ^ 5 = 4084101 * t ^ 5 := by ring
  have hdiv : t ^ 12 / 479001600 = t ^ 12 * (1 / 479001600) := by ring
  rw [hdiv] at hexp
  nlinarith

/-- `Σ_{Q < n ≤ N} ⌊N/n²⌋ ≤ N/Q`. -/
theorem tail_le {N Q : ℕ} (hQ : 1 ≤ Q) :
    ∑ n ∈ Ioc Q N, ((N / n ^ 2 : ℕ) : ℝ) ≤ N / Q := by
  calc ∑ n ∈ Ioc Q N, ((N / n ^ 2 : ℕ) : ℝ)
      ≤ ∑ n ∈ Ioc Q N, (N : ℝ) * (1 / ((n : ℝ) * ((n : ℝ) - 1))) := by
        apply sum_le_sum
        intro n hn
        rw [mem_Ioc] at hn
        have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
        have hpos : (0 : ℝ) < (n : ℝ) * ((n : ℝ) - 1) := by nlinarith
        calc ((N / n ^ 2 : ℕ) : ℝ) ≤ (N : ℝ) / ((n ^ 2 : ℕ) : ℝ) := Nat.cast_div_le
          _ = (N : ℝ) / ((n : ℝ) ^ 2) := by push_cast; ring
          _ ≤ (N : ℝ) / ((n : ℝ) * ((n : ℝ) - 1)) := by
              apply div_le_div_of_nonneg_left (by positivity) hpos
              nlinarith
          _ = _ := by ring
    _ = (N : ℝ) * ∑ n ∈ Ioc Q N, (1 / ((n : ℝ) * ((n : ℝ) - 1))) := by rw [mul_sum]
    _ ≤ (N : ℝ) * (1 / Q) := by
        apply mul_le_mul_of_nonneg_left (sum_Ioc_inv_mul_pred_le hQ N) (by positivity)
    _ = N / Q := by ring

/-- The Brun-Titchmarsh part: `Σ_{3 ≤ r ≤ Q prime} #cls ≤ (2N/log z)(3/10) + Q · 4z(1 + log z)³`. -/
theorem head_le {N Q : ℕ} (hN : 0 < N) {z : ℝ} (hz : 1 < z) :
    ∑ r ∈ (Icc 3 Q).filter Nat.Prime, ((cls N r).card : ℝ) ≤
      2 * N / Real.log z * (3 / 10) + Q * (4 * z * (1 + Real.log z) ^ 3) := by
  have hlz : 0 < Real.log z := Real.log_pos hz
  calc ∑ r ∈ (Icc 3 Q).filter Nat.Prime, ((cls N r).card : ℝ)
      ≤ ∑ r ∈ (Icc 3 Q).filter Nat.Prime, (2 * N / Real.log z *
          (1 / ((r : ℝ) * ((r : ℝ) - 1))) + 4 * z * (1 + Real.log z) ^ 3) := by
        apply sum_le_sum
        intro r hr
        rw [mem_filter] at hr
        have := cls_card_le hr.2 hN hz
        have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr.2.two_le
        have hpos : (0 : ℝ) < (r : ℝ) * ((r : ℝ) - 1) := by nlinarith
        calc ((cls N r).card : ℝ) ≤ _ := this
          _ = _ := by field_simp
    _ = 2 * N / Real.log z * ∑ r ∈ (Icc 3 Q).filter Nat.Prime, (1 / ((r : ℝ) * ((r : ℝ) - 1)))
          + ((Icc 3 Q).filter Nat.Prime).card * (4 * z * (1 + Real.log z) ^ 3) := by
        rw [sum_add_distrib, mul_sum, sum_const, nsmul_eq_mul]
    _ ≤ 2 * N / Real.log z * (3 / 10) + Q * (4 * z * (1 + Real.log z) ^ 3) := by
        apply add_le_add
        · exact mul_le_mul_of_nonneg_left (sum_prime_inv_le Q) (by positivity)
        · apply mul_le_mul_of_nonneg_right _ (by positivity)
          have : ((Icc 3 Q).filter Nat.Prime).card ≤ Q :=
            (card_filter_le _ _).trans (by simp)
          exact_mod_cast this

/-- **Dudek's theorem for large even `N`, PROVED, no cited input.** Every even `N ≥ e^12000` is
`p + m` with `p` prime and `m ≥ 1` square-free. -/
theorem dudek_even_large (N : ℕ) (hE : Even N) (hN : exp 12000 ≤ N) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m := by
  by_contra hno
  have he : (12001 : ℝ) ≤ exp 12000 := by
    have := Real.add_one_le_exp (12000 : ℝ); linarith
  have hNr : (12001 : ℝ) ≤ N := he.trans hN
  have h4 : 4 ≤ N := by
    have : (4 : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hN0 : 0 < N := by omega
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN0
  set L := Real.log N with hLdef
  have hL : 12000 ≤ L := by
    have := Real.log_le_log (exp_pos 12000) hN
    rwa [Real.log_exp] at this
  have hLpos : 0 < L := by linarith
  have hexpL : exp L = N := Real.exp_log hNpos
  -- the parameters
  set Q : ℕ := 100 * ⌈L⌉₊ with hQdef
  have hQr : (Q : ℝ) = 100 * (⌈L⌉₊ : ℝ) := by rw [hQdef]; push_cast; ring
  have hceil1 : L ≤ (⌈L⌉₊ : ℝ) := Nat.le_ceil L
  have hceil2 : (⌈L⌉₊ : ℝ) < L + 1 := Nat.ceil_lt_add_one hLpos.le
  have hQlo : 100 * L ≤ (Q : ℝ) := by rw [hQr]; linarith
  have hQhi : (Q : ℝ) ≤ 100 * (L + 1) := by rw [hQr]; linarith
  have hQ1 : 1 ≤ Q := by
    have : (1 : ℝ) ≤ Q := by linarith
    exact_mod_cast this
  set z := exp (19 / 20 * L) with hz
  have hlogz : Real.log z = 19 / 20 * L := Real.log_exp _
  have hz1 : 1 < z := by rw [hz]; exact Real.one_lt_exp_iff.mpr (by linarith)
  have hzpos : 0 < z := by linarith
  have hzN : z * exp (L / 20) = N := by
    rw [hz, ← Real.exp_add, ← hexpL]; congr 1; ring
  -- the three estimates
  have hc := card_le_of_no_rep Q hE h4 hno
  have hhead := head_le (Q := Q) hN0 hz1
  have htail := tail_le (N := N) hQ1
  have hpi := Chebyshev.pi_ge N
  rw [hlogz] at hhead
  rw [← hLdef, div_le_iff₀ hLpos] at hpi
  -- multiply the head and tail by L
  have hhead1 : 2 * N / (19 / 20 * L) * (3 / 10) * L = 12 / 19 * N := by
    field_simp; ring
  have hE1 : 1 + 19 / 20 * L ≤ L + 1 := by linarith
  have hE3 : (1 + 19 / 20 * L) ^ 3 ≤ (L + 1) ^ 3 :=
    pow_le_pow_left₀ (by linarith) hE1 3
  have hpoly := poly_le_exp hL
  have hE2 : (Q : ℝ) * (4 * z * (1 + 19 / 20 * L) ^ 3) * L ≤ 4 / 100 * N := by
    have hA : (Q : ℝ) * L ≤ 100 * (L + 1) * (L + 1) :=
      mul_le_mul hQhi (by linarith) hLpos.le (by positivity)
    have hB : (Q : ℝ) * (4 * z * (1 + 19 / 20 * L) ^ 3) * L
        = 4 * z * ((Q : ℝ) * L) * (1 + 19 / 20 * L) ^ 3 := by ring
    rw [hB]
    calc 4 * z * ((Q : ℝ) * L) * (1 + 19 / 20 * L) ^ 3
        ≤ 4 * z * (100 * (L + 1) * (L + 1)) * (L + 1) ^ 3 := by
          apply mul_le_mul _ hE3 (by positivity) (by positivity)
          exact mul_le_mul_of_nonneg_left hA (by positivity)
      _ = 4 / 100 * (z * (10000 * (L + 1) ^ 5)) := by ring
      _ ≤ 4 / 100 * (z * exp (L / 20)) := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact mul_le_mul_of_nonneg_left hpoly hzpos.le
      _ = 4 / 100 * N := by rw [hzN]
  have htail1 : (N : ℝ) / Q * L ≤ 1 / 100 * N := by
    have hQpos : (0 : ℝ) < Q := by linarith
    rw [div_mul_eq_mul_div, div_le_iff₀ hQpos]
    nlinarith
  -- log (N + 1) + L is tiny next to N
  have hlog1 : Real.log (N + 1) ≤ L + 1 := by
    have h2N : (N : ℝ) + 1 ≤ N * exp 1 := by
      have := Real.add_one_le_exp (1 : ℝ)
      nlinarith
    calc Real.log (N + 1) ≤ Real.log (N * exp 1) := Real.log_le_log (by linarith) h2N
      _ = L + 1 := by rw [Real.log_mul hNpos.ne' (exp_pos 1).ne', Real.log_exp]
  have hsmall : 2 * L + 1 ≤ 1 / 100 * N := by
    have := Real.quadratic_le_exp_of_nonneg hLpos.le
    rw [hexpL] at this
    nlinarith
  have hlog2 := Real.log_two_gt_d9
  -- combine: π N L ≤ (head + tail + 1) L
  have hcL : (Nat.primeCounting N : ℝ) * L ≤
      (2 * N / (19 / 20 * L) * (3 / 10) + Q * (4 * z * (1 + 19 / 20 * L) ^ 3) + N / Q + 1) * L := by
    apply mul_le_mul_of_nonneg_right _ hLpos.le
    linarith
  have hexp : (2 * N / (19 / 20 * L) * (3 / 10) + Q * (4 * z * (1 + 19 / 20 * L) ^ 3) + N / Q + 1) * L
      = 2 * N / (19 / 20 * L) * (3 / 10) * L + Q * (4 * z * (1 + 19 / 20 * L) ^ 3) * L
        + N / Q * L + L := by ring
  rw [hexp, hhead1] at hcL
  nlinarith

/-- What is left of Dudek's theorem for BJS Theorem 5: even `N` with `4 ≤ N < e^12000`. Cited,
Dudek 2017; a finite statement. -/
def DudekEvenBelow : Prop :=
  ∀ N : ℕ, Even N → 4 ≤ N → (N : ℝ) < exp 12000 →
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m

/-- An even Goldbach verification to `M` gives the even Dudek statement up to `M`, since a prime
is square-free. So the lab's kernel checks and the cited `4·10¹⁸` cover the bottom of the range. -/
theorem dudek_even_of_goldbach {M : ℕ} (h : LeanLab.EvenGoldbachUpTo M) (N : ℕ)
    (hE : Even N) (h4 : 4 ≤ N) (hM : N ≤ M) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m := by
  obtain ⟨p, q, hp, hq, hpq⟩ := h N hE h4 hM
  exact ⟨p, q, hp, hq.pos, hq.squarefree, hpq.symm⟩

/-- Dudek's theorem for every even `N ≥ 4`, CONDITIONAL ON the finite range `DudekEvenBelow` only. -/
theorem dudek_even_of_below (h : DudekEvenBelow) (N : ℕ) (hE : Even N) (h4 : 4 ≤ N) :
    ∃ p m : ℕ, p.Prime ∧ 0 < m ∧ Squarefree m ∧ N = p + m := by
  by_cases hN : (N : ℝ) < exp 12000
  · exact h N hE h4 hN
  · exact dudek_even_large N hE (not_lt.mp hN)

/-- The full `Thm5.DudekSqfree` implies the finite range, so `DudekEvenBelow` is the weaker input. -/
theorem dudekEvenBelow_of_dudekSqfree (h : LeanLab.AlmostPrimes.Thm5.DudekSqfree) :
    DudekEvenBelow := fun N _ h4 _ => h N (by omega)

open LeanLab.AlmostPrimes LeanLab.AlmostPrimes.Thm5 in
/-- **BJS Theorem 5 at the corrected threshold, with Dudek's input cut to a finite range.**
CONDITIONAL ON the Chen form at `exp(exp 32.73)`, `DudekEvenBelow`, Dusart Theorem 5.2 k = 2 and
Dusart's `π(x) ≤ x/(ln x − 1.1)`. Same proof as `Thm5.bjs_thm5_of_3273`. -/
theorem bjs_thm5_of_3273_small
    (h3273 : ∀ N : ℕ, Even N → Real.exp (Real.exp 32.73) < N → PrimePlusAlmostPrime 2 N)
    (hDu : DudekEvenBelow) (hD : LeanLab.Common.ThetaWindow.DusartThm52k2) (hP : DusartPi11) :
    ∀ N : ℕ, Even N → 4 ≤ N → ∃ k : ℕ, (k : ℝ) ≤ Real.exp 29.3 ∧ PrimePlusAlmostPrime k N := by
  intro N hE hN
  by_cases hbig : Real.exp (Real.exp 32.73) < N
  · refine ⟨2, ?_, h3273 N hE hbig⟩
    have : (2 : ℝ) ≤ 1 + 29.3 := by norm_num
    have := Real.add_one_le_exp 29.3
    push_cast; linarith
  · push Not at hbig
    obtain ⟨p, m, hp, hm, hsq, hNpm⟩ := dudek_even_of_below hDu N hE hN
    refine ⟨bigOmega m, ?_, ⟨p, m, hp, hm, hNpm, le_rfl⟩⟩
    apply bigOmega_le_of_sqfree hD hP hm hsq
    have : (m : ℝ) ≤ N := by exact_mod_cast (by omega : m ≤ N)
    linarith

end LeanLab.AlmostPrimes.DudekLarge
