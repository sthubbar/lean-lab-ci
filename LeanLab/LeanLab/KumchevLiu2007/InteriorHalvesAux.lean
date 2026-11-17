/-
Kumchev and Liu 2007, P0088, page 10 display 41 and page 15, the paragraph after
display 52. Proved helper lemmas for the two open leaves
`leaf_interior_left_half` and `leaf_interior_right_half` of
`SPLIT_lemma34_second_sum_dyadic`. Both leaves stay open: they rest on Lemmas
3.1 and 3.2 of page 10, which the paper cites on page 9 to Liu and Zhan 1997.

* `display41_of_minor`: the hypothesis on alpha written in the leaves,
  q at most H / P and |q alpha - a| below P / H, gives the third condition of
  display 41, |alpha - a / q| below q^(-2).
* `card_large_prime_divisors_le_two`: a positive integer below z^3 has at most
  two prime divisors at least z. Lab lemma, not in the paper; it uses the same
  size fact as the remark of page 15 that m / p is small.
* `second_sum_coeff_norm_le_two`: the coefficient of the second sum of display
  52, restricted to any set of primes at least z, has norm at most 2. This
  bounds the coefficient of e(alpha m^2) in the lab form of the second sum. It
  is not the hypothesis on a_m of Lemma 3.4, whose a_m is the prime indicator.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Eq33RouteD

namespace LeanLab.KumchevLiu2007.Eq33RouteD

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- P0088 page 10 display 41, third condition. If 0 < q ≤ Q and
|q alpha - a| < 1 / Q then |alpha - a / q| < 1 / q^2. In the leaves
Q = H / (log X)^B. -/
theorem display41_of_minor {α Q : ℝ} {q : ℕ} {a : ℤ} (hq : 0 < q)
    (hqQ : (q : ℝ) ≤ Q) (hclose : |(q : ℝ) * α - a| < Q⁻¹) :
    |α - (a : ℝ) / (q : ℝ)| < 1 / (q : ℝ) ^ 2 := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hQ : 0 < Q := lt_of_lt_of_le hq' hqQ
  have h1 : α - (a : ℝ) / (q : ℝ) = ((q : ℝ) * α - a) / q := by
    field_simp
  rw [h1, abs_div, abs_of_pos hq', div_lt_iff₀ hq']
  have h2 : Q⁻¹ ≤ (q : ℝ)⁻¹ := inv_anti₀ hq' hqQ
  have h3 : 1 / (q : ℝ) ^ 2 * q = (q : ℝ)⁻¹ := by
    field_simp
  rw [h3]
  exact lt_of_lt_of_le hclose h2

/-- Lab lemma, not in the paper, using the same size fact as the remark of
P0088 page 15 between the display before 52 and display 52: a positive integer
below z^3 has at most two distinct prime divisors that are at least z. -/
theorem card_large_prime_divisors_le_two (z : ℝ) (m : ℕ) (hz : 1 ≤ z)
    (hm : 0 < m) (hb : (m : ℝ) < z ^ 3) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ z ≤ (p : ℝ) ∧ p ∣ m) : S.card ≤ 2 := by
  by_contra hcon
  have h3 : 3 ≤ S.card := by omega
  have hdvd : (∏ p ∈ S, p) ∣ m :=
    Finset.prod_primes_dvd m (fun p hp => (hS p hp).1.prime) (fun p hp => (hS p hp).2.2)
  have hle : (∏ p ∈ S, p) ≤ m := Nat.le_of_dvd hm hdvd
  have hprod : z ^ S.card ≤ ∏ p ∈ S, (p : ℝ) := by
    rw [← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun p _ => le_trans zero_le_one hz)
      (fun p hp => (hS p hp).2.1)
  have hcast : (∏ p ∈ S, (p : ℝ)) ≤ (m : ℝ) := by
    have : ((∏ p ∈ S, p : ℕ) : ℝ) ≤ (m : ℝ) := by exact_mod_cast hle
    simpa [Nat.cast_prod] using this
  have hpow : z ^ 3 ≤ z ^ S.card := pow_le_pow_right₀ hz h3
  linarith

/-- P0088 page 15, the coefficient of the second sum of display 52 is bounded:
for a positive integer m below z^3 and any set S of primes at least z dividing
m, the sum over S of the rough weight of m / p has norm at most 2. -/
theorem second_sum_coeff_norm_le_two (z w : ℝ) (m : ℕ) (hz : 1 ≤ z)
    (hm : 0 < m) (hb : (m : ℝ) < z ^ 3) (S : Finset ℕ)
    (hS : ∀ p ∈ S, p.Prime ∧ z ≤ (p : ℝ) ∧ p ∣ m) :
    ‖∑ p ∈ S, roughWeight w (m / p)‖ ≤ 2 := by
  calc ‖∑ p ∈ S, roughWeight w (m / p)‖
      ≤ ∑ p ∈ S, ‖roughWeight w (m / p)‖ := norm_sum_le _ _
    _ ≤ ∑ _p ∈ S, (1 : ℝ) := Finset.sum_le_sum (fun p _ => roughWeight_norm_le_one w (m / p))
    _ = (S.card : ℝ) := by simp
    _ ≤ 2 := by exact_mod_cast card_large_prime_divisors_le_two z m hz hm hb S hS

/-- The cancellation free bound for the mean square of a short sum: if every
coefficient has norm at most K then the mean square over a to b is at most
(b - a) (K card S)^2. This is the trivial bound that the estimate of P0088
page 11 Lemma 3.4 improves by a power of log x. -/
theorem short_sum_mean_sq_trivial (S : Finset ℕ) (c : ℕ → ℂ) (K : ℝ)
    (hc : ∀ m ∈ S, ‖c m‖ ≤ K) (H a b : ℝ) (hab : a ≤ b) :
    (∫ t in a..b,
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ^ 2) ≤
      (b - a) * ((S.card : ℝ) * K) ^ 2 := by
  have hpt : ∀ t : ℝ,
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ^ 2 ≤
        ((S.card : ℝ) * K) ^ 2 := by
    intro t
    have h1 : ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ≤
        ∑ m ∈ S, ‖c m‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _))
    have h2 : ∑ m ∈ S, ‖c m‖ ≤ (S.card : ℝ) * K := by
      calc ∑ m ∈ S, ‖c m‖ ≤ ∑ _m ∈ S, K := Finset.sum_le_sum hc
        _ = (S.card : ℝ) * K := by simp
    exact pow_le_pow_left₀ (norm_nonneg _) (h1.trans h2) 2
  calc (∫ t in a..b,
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ^ 2)
      ≤ ∫ _t in a..b, ((S.card : ℝ) * K) ^ 2 :=
        intervalIntegral.integral_mono_on hab (short_sum_sq_intervalIntegrable S c H a b)
          intervalIntegrable_const (fun t _ => hpt t)
    _ = (b - a) * ((S.card : ℝ) * K) ^ 2 := by simp

/-- P0088 page 15, the coefficient of the second sum of display 52 on the
window: for Y at least one, eps nonnegative and m in the square root window of
Y, the sum over the primes p of one dyadic block between z1 = Y^(1/6 + eps/2)
and z0 that divide m of the rough weight of m / p has norm at most 2. -/
theorem interior_coeff_norm_le_two (Y ε z0 M w : ℝ) (hY : 1 ≤ Y) (hε : 0 ≤ ε)
    (m : ℕ) (hm : m ∈ squareWindow Y) :
    ‖∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
          Y ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧ (p : ℝ) < z0 ∧ p ∣ m)).filter
          (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
        roughWeight w (m / p)‖ ≤ 2 := by
  have hY0 : (0 : ℝ) < Y := by linarith
  simp only [squareWindow, Finset.mem_filter] at hm
  obtain ⟨-, hl, hu⟩ := hm
  have hs : 0 < Real.sqrt Y := Real.sqrt_pos.mpr hY0
  have hmpos : 0 < m := by
    have : (0 : ℝ) < (m : ℝ) := by linarith
    exact_mod_cast this
  have hz : 1 ≤ Y ^ (1 / 6 + ε / 2) := Real.one_le_rpow hY (by linarith)
  have hcube : Real.sqrt Y ≤ (Y ^ (1 / 6 + ε / 2)) ^ 3 := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le, Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hY (by push_cast; linarith)
  refine second_sum_coeff_norm_le_two (Y ^ (1 / 6 + ε / 2)) w m hz hmpos
    (lt_of_lt_of_le hu hcube) _ ?_
  intro p hp
  obtain ⟨hp1, -⟩ := Finset.mem_filter.mp hp
  obtain ⟨-, hpp, hpz1, -, hpm⟩ := Finset.mem_filter.mp hp1
  exact ⟨hpp, hpz1, hpm⟩

/-- The cancellation free bound for the integral of the two interior half
leaves: over any t range from a to b the mean square of the short second sum
of display 52 for one dyadic block is at most (b - a) (2 card)^2, where card
is the number of integers in the square root window. With card at most
Y^(1/2) + 1 and b - a at most Y this is of size Y^2, so the bound
C H^2 / (log X)^A of the leaves is immediate once H is at least
Y (log X)^(A/2). That range lies outside P0088 page 11 Lemma 3.4; so does the
band of H between Y and Y (log X)^(A/2), which this bound does not reach. -/
theorem interior_mean_sq_trivial (Y ε z0 M w H α a b : ℝ) (hY : 1 ≤ Y) (hε : 0 ≤ ε)
    (hab : a ≤ b) :
    (∫ t in a..b,
      ‖∑ m ∈ (squareWindow Y).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
            Y ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧ (p : ℝ) < z0 ∧ p ∣ m)).filter
            (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
          roughWeight w (m / p)) *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
      (b - a) * (((squareWindow Y).card : ℝ) * 2) ^ 2 := by
  refine short_sum_mean_sq_trivial (squareWindow Y) _ 2 ?_ H a b hab
  intro m hm
  rw [norm_mul]
  have h1 : ‖fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ = 1 := by
    simp only [fourier_apply, Circle.norm_coe]
  rw [h1, mul_one]
  exact interior_coeff_norm_le_two Y ε z0 M w hY hε m hm

/-- The part of the written H range of the interior half leaves that P0088
page 11 Lemma 3.4 does not cover and that needs no cancellation. For X above
one, eps nonnegative and H at least Y (log X)^(A/2), with Y = windowY X eps,
the mean square of the short second sum of display 52 for one dyadic block,
over any t range from a to b of length at most Y, is at most
16 H^2 / (log X)^A. -/
theorem interior_large_H_core (A ε B X H α M a b : ℝ) (hX : 1 < X) (hε : 0 ≤ ε)
    (hab : a ≤ b) (hba : b - a ≤ windowY X ε)
    (hH : windowY X ε * Real.log X ^ (A / 2) ≤ H) :
    (∫ t in a..b,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            16 * H ^ 2 / Real.log X ^ A := by
  have hY : 1 ≤ windowY X ε := by
    unfold windowY
    exact Real.one_le_rpow hX.le (by linarith)
  have hL : 0 < Real.log X := Real.log_pos hX
  have hcard : ((squareWindow (windowY X ε)).card : ℝ) ≤ Real.sqrt (windowY X ε) + 1 := by
    have h : (squareWindow (windowY X ε)).card ≤ ⌊Real.sqrt (windowY X ε)⌋₊ + 1 := by
      unfold squareWindow
      exact (Finset.card_filter_le _ _).trans (by simp)
    have h2 : ((⌊Real.sqrt (windowY X ε)⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (windowY X ε) :=
      Nat.floor_le (Real.sqrt_nonneg _)
    have h3 : ((squareWindow (windowY X ε)).card : ℝ) ≤
        ((⌊Real.sqrt (windowY X ε)⌋₊ : ℕ) : ℝ) + 1 := by exact_mod_cast h
    linarith
  have hs1 : 1 ≤ Real.sqrt (windowY X ε) := Real.one_le_sqrt.mpr hY
  have hss : Real.sqrt (windowY X ε) ^ 2 = windowY X ε := Real.sq_sqrt (by linarith)
  have h1 := interior_mean_sq_trivial (windowY X ε) ε
    (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) M
    (windowY X ε ^ (1 / 6 + ε / 2)) H α a b hY hε hab
  have hc0 : (0 : ℝ) ≤ ((squareWindow (windowY X ε)).card : ℝ) := Nat.cast_nonneg _
  have hsq : (((squareWindow (windowY X ε)).card : ℝ) * 2) ^ 2 ≤ 16 * windowY X ε := by
    have hle : ((squareWindow (windowY X ε)).card : ℝ) * 2 ≤ 4 * Real.sqrt (windowY X ε) := by
      linarith
    have := pow_le_pow_left₀ (by positivity) hle 2
    calc (((squareWindow (windowY X ε)).card : ℝ) * 2) ^ 2
        ≤ (4 * Real.sqrt (windowY X ε)) ^ 2 := this
      _ = 16 * windowY X ε := by rw [mul_pow, hss]; norm_num
  have h2 : (b - a) * (((squareWindow (windowY X ε)).card : ℝ) * 2) ^ 2 ≤
      16 * windowY X ε ^ 2 := by
    calc (b - a) * (((squareWindow (windowY X ε)).card : ℝ) * 2) ^ 2
        ≤ windowY X ε * (16 * windowY X ε) :=
          mul_le_mul hba hsq (sq_nonneg _) (by linarith)
      _ = 16 * windowY X ε ^ 2 := by ring
  have hpow : (Real.log X ^ (A / 2)) ^ 2 = Real.log X ^ A := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1
    push_cast
    ring
  have h3 : windowY X ε ^ 2 ≤ H ^ 2 / Real.log X ^ A := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hL A)]
    calc windowY X ε ^ 2 * Real.log X ^ A
        = (windowY X ε * Real.log X ^ (A / 2)) ^ 2 := by rw [mul_pow, hpow]
      _ ≤ H ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (by linarith) (Real.rpow_pos_of_pos hL _).le) hH 2
  have h4 : 16 * H ^ 2 / Real.log X ^ A = 16 * (H ^ 2 / Real.log X ^ A) := by ring
  rw [h4]
  linarith

/-- The bound of `leaf_interior_left_half` on the part H at least
Y (log X)^(A/2) of its written H range, with the constant 16. -/
theorem interior_left_half_large_H (A ε B X H α M : ℝ) (hX : 1 < X) (hε : 0 ≤ ε)
    (hH : windowY X ε * Real.log X ^ (A / 2) ≤ H) :
    (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            16 * H ^ 2 / Real.log X ^ A := by
  have hY : 1 ≤ windowY X ε := by
    unfold windowY
    exact Real.one_le_rpow hX.le (by linarith)
  exact interior_large_H_core A ε B X H α M _ _ hX hε (by linarith) (by linarith) hH

/-- The bound of `leaf_interior_right_half` on the part H at least
Y (log X)^(A/2) of its written H range, with the constant 16. -/
theorem interior_right_half_large_H (A ε B X H α M : ℝ) (hX : 1 < X) (hε : 0 ≤ ε)
    (hH : windowY X ε * Real.log X ^ (A / 2) ≤ H) :
    (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            16 * H ^ 2 / Real.log X ^ A := by
  have hY : 1 ≤ windowY X ε := by
    unfold windowY
    exact Real.one_le_rpow hX.le (by linarith)
  exact interior_large_H_core A ε B X H α M _ _ hX hε (by linarith) (by linarith) hH

/-- P0088 page 8 display 34 and page 15: the two cutoffs cross for eps at
least 1/6. For X at least e, B nonnegative and eps at least 1/6, the sieve
cutoff z0 = Y^(1/4) (log X)^(-2B) is at most the rough cutoff
z1 = Y^(1/6 + eps/2). -/
theorem cutoffs_cross_of_large_eps (X ε B : ℝ) (hX : Real.exp 1 ≤ X) (hB : 0 ≤ B)
    (hε : 1 / 6 ≤ ε) :
    windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤
      windowY X ε ^ (1 / 6 + ε / 2) := by
  have hX1 : 1 ≤ X := le_trans (by linarith [Real.add_one_le_exp (1 : ℝ)]) hX
  have hX0 : 0 < X := by linarith
  have hY : 1 ≤ windowY X ε := by
    unfold windowY
    exact Real.one_le_rpow hX1 (by linarith)
  have hL : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le hX0]
    exact hX
  have hLB : 1 ≤ Real.log X ^ B := Real.one_le_rpow hL hB
  have hinv : (Real.log X ^ B) ^ (-2 : ℤ) ≤ 1 := by
    rw [zpow_neg]
    exact inv_le_one_of_one_le₀ (one_le_zpow₀ hLB (by norm_num))
  have hq : 0 ≤ windowY X ε ^ (1 / 4 : ℝ) := Real.rpow_nonneg (by linarith) _
  calc windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)
      ≤ windowY X ε ^ (1 / 4 : ℝ) * 1 := mul_le_mul_of_nonneg_left hinv hq
    _ = windowY X ε ^ (1 / 4 : ℝ) := mul_one _
    _ ≤ windowY X ε ^ (1 / 6 + ε / 2) :=
        Real.rpow_le_rpow_of_exponent_le hY (by linarith)

/-- When the sieve cutoff z0 is at most the rough cutoff z1 no prime lies
between them, so the coefficient of the second sum of display 52 is zero and
so is the integral of the interior half leaves, over any t range. -/
theorem interior_integral_zero_of_cutoffs_cross (X ε B M H α a b : ℝ)
    (hcross : windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤
      windowY X ε ^ (1 / 6 + ε / 2)) :
    (∫ t in a..b,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) = 0 := by
  have hcoef : ∀ m : ℕ, (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) = 0 := by
    intro m
    apply Finset.sum_eq_zero
    intro p hp
    obtain ⟨hp1, -⟩ := Finset.mem_filter.mp hp
    obtain ⟨-, -, hpz1, hpz0, -⟩ := Finset.mem_filter.mp hp1
    linarith
  simp only [hcoef, zero_mul, Finset.sum_const_zero, norm_zero]
  simp

/-- The bound of both interior half leaves for eps at least 1/6, X at least e
and B nonnegative: the block is empty and the integral over any t range is at
most any nonnegative bound, in particular C H^2 / (log X)^A with C positive. -/
theorem interior_integral_le_of_large_eps (A ε B X H α M a b C : ℝ)
    (hX : Real.exp 1 ≤ X) (hB : 0 ≤ B) (hε : 1 / 6 ≤ ε) (hC : 0 ≤ C) :
    (∫ t in a..b,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  rw [interior_integral_zero_of_cutoffs_cross X ε B M H α a b
    (cutoffs_cross_of_large_eps X ε B hX hB hε)]
  have hX0 : 0 < X := lt_of_lt_of_le (Real.exp_pos 1) hX
  have hL : 0 < Real.log X := by
    have : 1 ≤ Real.log X := by
      rw [Real.le_log_iff_exp_le hX0]
      exact hX
    linarith
  exact div_nonneg (mul_nonneg hC (sq_nonneg _)) (Real.rpow_pos_of_pos hL A).le

/-- Every m in the square root window of a nonnegative Y has square below Y.
P0088 page 2 display 5. -/
theorem squareWindow_sq_lt {Y : ℝ} (hY : 0 ≤ Y) {m : ℕ} (hm : m ∈ squareWindow Y) :
    (m : ℝ) ^ 2 < Y := by
  simp only [squareWindow, Finset.mem_filter] at hm
  obtain ⟨-, -, hu⟩ := hm
  have hs := Real.sq_sqrt hY
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  nlinarith

/-- Once the short window reaches past every square in play its length no
longer matters: if every m in S has square below Y and Y is at most a + H and
at most a + H', then the mean squares over t from a to b of the short sums of
lengths H and H' agree. In the leaves, where m^2 is below Y, every H with Y at
most a + H gives the same integral. In P0088 page 11 Lemma 3.4 itself the sum
over k is not capped, so this does not apply there. -/
theorem short_sum_integral_congr_H (S : Finset ℕ) (c : ℕ → ℂ) (Y H H' a b : ℝ)
    (hab : a ≤ b) (hS : ∀ m ∈ S, (m : ℝ) ^ 2 < Y) (hH : Y ≤ a + H) (hH' : Y ≤ a + H') :
    (∫ t in a..b,
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ^ 2) =
    (∫ t in a..b,
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H'), c m‖ ^ 2) := by
  apply intervalIntegral.integral_congr
  intro t ht
  rw [Set.uIcc_of_le hab] at ht
  have hfil : S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H) =
      S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H') := by
    apply Finset.filter_congr
    intro m hm
    have h1 := hS m hm
    have h2 := ht.1
    constructor
    · rintro ⟨h3, -⟩
      exact ⟨h3, by linarith⟩
    · rintro ⟨h3, -⟩
      exact ⟨h3, by linarith⟩
  simp only [hfil]

/-- The first sum of display 52 of P0088 page 15, cancellation free: for X
above one, eps nonnegative, any sieve cutoff z, a at most b with b - a at most
Y = windowY X eps, and H at least Y (log X)^(A/2), the mean square of the
short sum of the rough weight is at most 4 H^2 / (log X)^A. This is the part
of the written H range of `lemma34_first_sum` and of its leaves that Lemma 3.4
of page 11 does not cover. -/
theorem first_sum_large_H (A ε X H α z a b : ℝ) (hX : 1 < X) (hε : 0 ≤ ε)
    (hab : a ≤ b) (hba : b - a ≤ windowY X ε)
    (hH : windowY X ε * Real.log X ^ (A / 2) ≤ H) :
    (∫ t in a..b,
      ‖∑ m ∈ (squareWindow (windowY X ε)).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        roughWeight z m *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
      4 * H ^ 2 / Real.log X ^ A := by
  have hY : 1 ≤ windowY X ε := by
    unfold windowY
    exact Real.one_le_rpow hX.le (by linarith)
  have hL : 0 < Real.log X := Real.log_pos hX
  have hcard : ((squareWindow (windowY X ε)).card : ℝ) ≤ Real.sqrt (windowY X ε) + 1 := by
    have h : (squareWindow (windowY X ε)).card ≤ ⌊Real.sqrt (windowY X ε)⌋₊ + 1 := by
      unfold squareWindow
      exact (Finset.card_filter_le _ _).trans (by simp)
    have h2 : ((⌊Real.sqrt (windowY X ε)⌋₊ : ℕ) : ℝ) ≤ Real.sqrt (windowY X ε) :=
      Nat.floor_le (Real.sqrt_nonneg _)
    have h3 : ((squareWindow (windowY X ε)).card : ℝ) ≤
        ((⌊Real.sqrt (windowY X ε)⌋₊ : ℕ) : ℝ) + 1 := by exact_mod_cast h
    linarith
  have hs1 : 1 ≤ Real.sqrt (windowY X ε) := Real.one_le_sqrt.mpr hY
  have hss : Real.sqrt (windowY X ε) ^ 2 = windowY X ε := Real.sq_sqrt (by linarith)
  have h1 := short_sum_mean_sq_trivial (squareWindow (windowY X ε))
    (fun m : ℕ => roughWeight z m * fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))) 1
    (fun m _ => by
      rw [norm_mul]
      have hf : ‖fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ = 1 := by
        simp only [fourier_apply, Circle.norm_coe]
      rw [hf, mul_one]
      exact roughWeight_norm_le_one z m) H a b hab
  have hc0 : (0 : ℝ) ≤ ((squareWindow (windowY X ε)).card : ℝ) := Nat.cast_nonneg _
  have hsq : (((squareWindow (windowY X ε)).card : ℝ) * 1) ^ 2 ≤ 4 * windowY X ε := by
    have hle : ((squareWindow (windowY X ε)).card : ℝ) * 1 ≤ 2 * Real.sqrt (windowY X ε) := by
      linarith
    have := pow_le_pow_left₀ (by positivity) hle 2
    calc (((squareWindow (windowY X ε)).card : ℝ) * 1) ^ 2
        ≤ (2 * Real.sqrt (windowY X ε)) ^ 2 := this
      _ = 4 * windowY X ε := by rw [mul_pow, hss]; norm_num
  have h2 : (b - a) * (((squareWindow (windowY X ε)).card : ℝ) * 1) ^ 2 ≤
      4 * windowY X ε ^ 2 := by
    calc (b - a) * (((squareWindow (windowY X ε)).card : ℝ) * 1) ^ 2
        ≤ windowY X ε * (4 * windowY X ε) :=
          mul_le_mul hba hsq (sq_nonneg _) (by linarith)
      _ = 4 * windowY X ε ^ 2 := by ring
  have hpow : (Real.log X ^ (A / 2)) ^ 2 = Real.log X ^ A := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1
    push_cast
    ring
  have h3 : windowY X ε ^ 2 ≤ H ^ 2 / Real.log X ^ A := by
    rw [le_div_iff₀ (Real.rpow_pos_of_pos hL A)]
    calc windowY X ε ^ 2 * Real.log X ^ A
        = (windowY X ε * Real.log X ^ (A / 2)) ^ 2 := by rw [mul_pow, hpow]
      _ ≤ H ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (by linarith) (Real.rpow_pos_of_pos hL _).le) hH 2
  have h4 : 4 * H ^ 2 / Real.log X ^ A = 4 * (H ^ 2 / Real.log X ^ A) := by ring
  rw [h4]
  linarith

/-- `leaf_interior_left_half` restricted to eps at least 1/6, in the shape of
the leaf: B0 = 1, C = 1, X0 = 3, and no hypothesis on H, alpha, q, a or M is
used, since the block of primes is empty. -/
theorem interior_left_half_of_large_eps (A : ℝ) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 1 / 6 ≤ ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → ∀ α : ℝ, ∀ M : ℝ,
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  refine ⟨1, one_pos, fun B hB ε hε => ⟨1, 3, one_pos, by norm_num, ?_⟩⟩
  intro X H hX α M
  have he : Real.exp 1 ≤ X := by
    have := Real.exp_one_lt_d9
    linarith
  exact interior_integral_le_of_large_eps A ε B X H α M _ _ 1 he (by linarith) hε zero_le_one

/-- `leaf_interior_right_half` restricted to eps at least 1/6, in the shape of
the leaf: B0 = 1, C = 1, X0 = 3, and no hypothesis on H, alpha, q, a or M is
used, since the block of primes is empty. -/
theorem interior_right_half_of_large_eps (A : ℝ) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 1 / 6 ≤ ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → ∀ α : ℝ, ∀ M : ℝ,
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  refine ⟨1, one_pos, fun B hB ε hε => ⟨1, 3, one_pos, by norm_num, ?_⟩⟩
  intro X H hX α M
  have he : Real.exp 1 ≤ X := by
    have := Real.exp_one_lt_d9
    linarith
  exact interior_integral_le_of_large_eps A ε B X H α M _ _ 1 he (by linarith) hε zero_le_one

/-- The statement of `leaf_interior_left_half` follows from its
restriction to eps below 1/6 and H below Y (log X)^(A/2), with
Y = windowY X eps. The other two ranges are proved without cancellation:
`interior_integral_le_of_large_eps` and `interior_left_half_large_H`.
CONDITIONAL ON the hypothesis hcore, which is that restriction. The restricted
range contains the range H at most Y of P0088 page 11 Lemma 3.4, and also the
band of H between Y and Y (log X)^(A/2), which is outside the hypothesis
y at most x of that lemma and needs a separate reduction. -/
theorem leaf_interior_left_half_of_core (A : ℝ)
    (hcore : ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        H < windowY X ε * Real.log X ^ (A / 2) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → 
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        (∫ t in (windowY X ε / 4)..(windowY X ε / 2),
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := hcore
  refine ⟨max B1 1, lt_of_lt_of_le hB1 (le_max_left _ _), fun B hB ε hε => ?_⟩
  have hB0 : 0 ≤ B := le_trans zero_le_one ((le_max_right _ _).trans hB)
  by_cases hbig : 1 / 6 ≤ ε
  · refine ⟨1, 3, one_pos, by norm_num, ?_⟩
    intro X H hX _ _ α q a _ _ _ _ M _ _ _
    have he : Real.exp 1 ≤ X := by
      have := Real.exp_one_lt_d9
      linarith
    exact interior_integral_le_of_large_eps A ε B X H α M _ _ 1 he hB0 hbig zero_le_one
  · push Not at hbig
    obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε hbig
    refine ⟨max C1 16, X1, lt_of_lt_of_le hC1 (le_max_left _ _), hX1, ?_⟩
    intro X H hX hHl hHu α q a hcop hqP hqQ hclose M hM htop hlow
    have hX1' : 1 < X := by linarith
    have hL : 0 < Real.log X := Real.log_pos hX1'
    have hq : (0 : ℝ) ≤ H ^ 2 / Real.log X ^ A :=
      div_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos hL A).le
    have hkey : ∀ c : ℝ, c * H ^ 2 / Real.log X ^ A = c * (H ^ 2 / Real.log X ^ A) :=
      fun c => by ring
    by_cases hH : windowY X ε * Real.log X ^ (A / 2) ≤ H
    · have e := interior_left_half_large_H A ε B X H α M hX1' hε.le hH
      rw [hkey] at e ⊢
      exact e.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hq)
    · push Not at hH
      have e := k1 X H hX hHl hHu hH α q a hcop hqP hqQ hclose M hM htop hlow
      rw [hkey] at e ⊢
      exact e.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq)

/-- The statement of `leaf_interior_right_half` follows from its
restriction to eps below 1/6 and H below Y (log X)^(A/2), with
Y = windowY X eps. The other two ranges are proved without cancellation:
`interior_integral_le_of_large_eps` and `interior_right_half_large_H`.
CONDITIONAL ON the hypothesis hcore, which is that restriction. The restricted
range contains the range H at most Y of P0088 page 11 Lemma 3.4, and also the
band of H between Y and Y (log X)^(A/2), which is outside the hypothesis
y at most x of that lemma and needs a separate reduction. -/
theorem leaf_interior_right_half_of_core (A : ℝ)
    (hcore : ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → ε < 1 / 6 →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        H < windowY X ε * Real.log X ^ (A / 2) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε → 
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        M < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
        windowY X ε ^ (1 / 6 + ε / 2) < 2 * M →
        (∫ t in (windowY X ε / 2)..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := hcore
  refine ⟨max B1 1, lt_of_lt_of_le hB1 (le_max_left _ _), fun B hB ε hε => ?_⟩
  have hB0 : 0 ≤ B := le_trans zero_le_one ((le_max_right _ _).trans hB)
  by_cases hbig : 1 / 6 ≤ ε
  · refine ⟨1, 3, one_pos, by norm_num, ?_⟩
    intro X H hX _ _ α q a _ _ _ _ M _ _ _
    have he : Real.exp 1 ≤ X := by
      have := Real.exp_one_lt_d9
      linarith
    exact interior_integral_le_of_large_eps A ε B X H α M _ _ 1 he hB0 hbig zero_le_one
  · push Not at hbig
    obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε hbig
    refine ⟨max C1 16, X1, lt_of_lt_of_le hC1 (le_max_left _ _), hX1, ?_⟩
    intro X H hX hHl hHu α q a hcop hqP hqQ hclose M hM htop hlow
    have hX1' : 1 < X := by linarith
    have hL : 0 < Real.log X := Real.log_pos hX1'
    have hq : (0 : ℝ) ≤ H ^ 2 / Real.log X ^ A :=
      div_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos hL A).le
    have hkey : ∀ c : ℝ, c * H ^ 2 / Real.log X ^ A = c * (H ^ 2 / Real.log X ^ A) :=
      fun c => by ring
    by_cases hH : windowY X ε * Real.log X ^ (A / 2) ≤ H
    · have e := interior_right_half_large_H A ε B X H α M hX1' hε.le hH
      rw [hkey] at e ⊢
      exact e.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hq)
    · push Not at hH
      have e := k1 X H hX hHl hHu hH α q a hcop hqP hqQ hclose M hM htop hlow
      rw [hkey] at e ⊢
      exact e.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq)

/-- P0088 page 4 display 10 and page 11 Lemma 3.4, the lower end z = 2 of the
sieve cutoff: for z at most 2 the rough indicator is identically one, since
every prime is at least 2. -/
theorem roughWeight_eq_one_of_le_two (z : ℝ) (hz : z ≤ 2) (m : ℕ) : roughWeight z m = 1 := by
  unfold roughWeight
  have h : ∀ p : ℕ, p.Prime → p ∣ m → z ≤ (p : ℝ) := by
    intro p hp _
    have : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
    linarith
  rw [ite_eq_left_of_eq_true _ _ (eq_true h)]

/-- P0088 page 4 display 10: the rough indicator is monotone in the cutoff in
the sense that a number rough at z is rough at every smaller cutoff. -/
theorem roughWeight_eq_one_of_le {z w : ℝ} (hwz : w ≤ z) {m : ℕ}
    (h : roughWeight z m = 1) : roughWeight w m = 1 := by
  unfold roughWeight at h ⊢
  by_cases hc : ∀ p : ℕ, p.Prime → p ∣ m → z ≤ (p : ℝ)
  · have h' : ∀ p : ℕ, p.Prime → p ∣ m → w ≤ (p : ℝ) := fun p hp hd => hwz.trans (hc p hp hd)
    rw [ite_eq_left_of_eq_true _ _ (eq_true h')]
  · rw [ite_eq_right_of_eq_false _ _ (eq_false hc)] at h
    exact absurd h (by norm_num)

/-- The statement of `lemma34_first_sum` follows from its restriction to H
below Y (log X)^(A/2), with Y = windowY X eps. The range of H at or above that
is `first_sum_large_H`, proved without cancellation. CONDITIONAL ON the
hypothesis hcore, which is that restriction. For A positive and X above e the
restricted range contains the range H at most Y of P0088 page 11 Lemma 3.4 and
also the band of H between Y and Y (log X)^(A/2), which is outside the
hypothesis y at most x of that lemma. The theorem needs no sign condition on
A. -/
theorem lemma34_first_sum_of_core (A : ℝ)
    (hcore : ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        H < windowY X ε * Real.log X ^ (A / 2) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := hcore
  refine ⟨B1, hB1, fun B hB ε hε => ?_⟩
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B hB ε hε
  refine ⟨max C1 4, X1, lt_of_lt_of_le hC1 (le_max_left _ _), hX1, ?_⟩
  intro X H hX hHl hHu α q a hcop hqP hqQ hclose z hz
  have hX1' : 1 < X := by linarith
  have hL : 0 < Real.log X := Real.log_pos hX1'
  have hq : (0 : ℝ) ≤ H ^ 2 / Real.log X ^ A :=
    div_nonneg (sq_nonneg _) (Real.rpow_pos_of_pos hL A).le
  have hkey : ∀ c : ℝ, c * H ^ 2 / Real.log X ^ A = c * (H ^ 2 / Real.log X ^ A) :=
    fun c => by ring
  have hY : 1 ≤ windowY X ε := by
    unfold windowY
    exact Real.one_le_rpow hX1'.le (by linarith)
  by_cases hH : windowY X ε * Real.log X ^ (A / 2) ≤ H
  · have e := first_sum_large_H A ε X H α z (windowY X ε / 4) (windowY X ε) hX1' hε.le
      (by linarith) (by linarith) hH
    rw [hkey] at e ⊢
    exact e.trans (mul_le_mul_of_nonneg_right (le_max_right _ _) hq)
  · push Not at hH
    have e := k1 X H hX hHl hHu hH α q a hcop hqP hqQ hclose z hz
    rw [hkey] at e ⊢
    exact e.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hq)

/-- In the interior half leaves the integral does not depend on H once the
short window reaches past Y: for Y nonnegative, a at most b and two lengths H
and H' with Y at most a + H and Y at most a + H', the mean squares of the
short second sum of display 52 for one dyadic block agree. On the left half,
a = Y / 4, this is every H at least 3 Y / 4; on the right half, a = Y / 2,
every H at least Y / 2. The alpha hypothesis and the right side of the leaves
still depend on H. -/
theorem interior_integral_congr_H (Y ε z0 M w H H' α a b : ℝ) (hY : 0 ≤ Y)
    (hab : a ≤ b) (hH : Y ≤ a + H) (hH' : Y ≤ a + H') :
    (∫ t in a..b,
      ‖∑ m ∈ (squareWindow Y).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
            Y ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧ (p : ℝ) < z0 ∧ p ∣ m)).filter
            (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
          roughWeight w (m / p)) *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) =
    (∫ t in a..b,
      ‖∑ m ∈ (squareWindow Y).filter
          (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H'),
        (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
            Y ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧ (p : ℝ) < z0 ∧ p ∣ m)).filter
            (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
          roughWeight w (m / p)) *
          fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) :=
  short_sum_integral_congr_H (squareWindow Y) _ Y H H' a b hab
    (fun _ hm => squareWindow_sq_lt hY hm) hH hH'

/-- P0088 page 15, the size remark before display 52: for Y positive, m below
the square root of Y and p at least z1 = Y^(1/6 + eps/2), the quotient m / p
is below Y^(1/3 - eps/2). -/
theorem quotient_lt_of_window (Y ε : ℝ) (hY : 0 < Y) (m p : ℕ)
    (hm : (m : ℝ) < Real.sqrt Y) (hp : Y ^ (1 / 6 + ε / 2) ≤ (p : ℝ)) :
    (m : ℝ) / (p : ℝ) < Y ^ (1 / 3 - ε / 2) := by
  have hz : 0 < Y ^ (1 / 6 + ε / 2) := Real.rpow_pos_of_pos hY _
  have hp0 : (0 : ℝ) < (p : ℝ) := lt_of_lt_of_le hz hp
  have hm0 : (0 : ℝ) ≤ (m : ℝ) := Nat.cast_nonneg m
  have hsplit : Y ^ (1 / 3 - ε / 2) = Real.sqrt Y / Y ^ (1 / 6 + ε / 2) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_sub hY]
    congr 1
    ring
  rw [hsplit]
  calc (m : ℝ) / (p : ℝ) ≤ (m : ℝ) / Y ^ (1 / 6 + ε / 2) :=
        div_le_div_of_nonneg_left hm0 hz hp
    _ < Real.sqrt Y / Y ^ (1 / 6 + ε / 2) := div_lt_div_of_pos_right hm hz

end LeanLab.KumchevLiu2007.Eq33RouteD
