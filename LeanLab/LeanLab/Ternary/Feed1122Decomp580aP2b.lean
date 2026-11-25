/-
Split of `prop56`, burst-20261122 session S144.
Helfgott, The ternary Goldbach conjecture is true, arXiv 1312.7748v2, Proposition 5.6,
page 39 display (5.23). The proof writes `G_q(R) = φ(q)/q (log R + c_E + Σ_{p|q} log p/p) + err_{q,R}`,
display (5.24), and reduces (5.23) to display (5.26) on page 39, using
`ρ ≤ (log Q₀ + c₊)/(log Q + c_E) ≤ ω(ρ)` and `c₊ ≥ ρ c_E`. The rest of the proof,
pages 39 to 44, establishes (5.26).
The glue `prop56_of_leaves` is sorry free.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Feed1122Decomp580aP2

namespace LeanLab.Ternary.Task580

/-- The terms of the prime sum in `c_E`, Helfgott 1312.7748v2 display (5.14), are nonnegative.
Helper for `sieveConstant_le`, burst S144 wave 2. -/
private lemma term_nonneg (p : ℕ) :
    0 ≤ (if p.Prime then Real.log p / ((p : ℝ) * (p - 1 : ℝ)) else 0) := by
  split_ifs with hp
  · have h2 : (2:ℝ) ≤ p := by exact_mod_cast hp.two_le
    apply div_nonneg (Real.log_nonneg (by linarith)); nlinarith
  · exact le_rfl

private lemma term_le (n : ℕ) (hn : 2 ≤ n) :
    (if n.Prime then Real.log n / ((n : ℝ) * (n - 1 : ℝ)) else 0) ≤
      (Real.log n + 1) / ((n:ℝ) - 1) - (Real.log (n + 1 : ℕ) + 1) / (n : ℝ) := by
  have h2 : (2:ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0:ℝ) < n := by linarith
  have hn1 : (0:ℝ) < (n:ℝ) - 1 := by linarith
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by linarith)
  have hstep : Real.log ((n + 1 : ℕ) : ℝ) - Real.log n ≤ 1 / n := by
    rw [← Real.log_div (by push_cast; linarith) hn0.ne']
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < ((n + 1 : ℕ) : ℝ) / n by positivity)
    have he : ((n + 1 : ℕ) : ℝ) / n - 1 = 1 / n := by push_cast; field_simp; ring
    linarith
  have key : Real.log n / ((n : ℝ) * (n - 1 : ℝ)) ≤
      (Real.log n + 1) / ((n:ℝ) - 1) - (Real.log (n + 1 : ℕ) + 1) / (n : ℝ) := by
    rw [div_sub_div _ _ hn1.ne' hn0.ne', div_le_div_iff₀ (by positivity) (by positivity)]
    have h1 : ((n:ℝ) - 1) * (Real.log ((n + 1 : ℕ) : ℝ) - Real.log n) ≤ ((n:ℝ) - 1) * (1 / n) :=
      mul_le_mul_of_nonneg_left hstep hn1.le
    have h3 : ((n:ℝ) - 1) * (1 / n) ≤ 1 := by
      rw [mul_one_div, div_le_one hn0]; linarith
    have hpos : 0 ≤ (n:ℝ) * ((n:ℝ) - 1) := by positivity
    nlinarith [mul_nonneg hpos hpos]
  split_ifs
  · exact key
  · exact (div_nonneg hlogn (by positivity)).trans key

private lemma log_le_small : Real.log 2 ≤ 0.6932 ∧ Real.log 3 ≤ 1.11 ∧ Real.log 5 ≤ 1.64 ∧
    Real.log 7 ≤ 1.96 ∧ Real.log 8 ≤ 2.08 := by
  have l2 := Real.log_two_lt_d9
  have hb : ∀ a b : ℝ, 0 < a → 0 < b → Real.log b - Real.log a ≤ b / a - 1 := by
    intro a b ha hb
    rw [← Real.log_div hb.ne' ha.ne']; exact Real.log_le_sub_one_of_pos (by positivity)
  have l4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  have l8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8:ℝ) = 2 ^ 3 by norm_num, Real.log_pow]; norm_num
  have l3 := hb 2 3 (by norm_num) (by norm_num)
  have l5 := hb 4 5 (by norm_num) (by norm_num)
  have l7 := hb 4 7 (by norm_num) (by norm_num)
  have l3' : Real.log 3 ≤ 1.11 := by
    -- log 3 = log 9 / 2 and log 9 - log 8 ≤ 1/8
    have l9 : Real.log 9 = 2 * Real.log 3 := by
      rw [show (9:ℝ) = 3 ^ 2 by norm_num, Real.log_pow]; norm_num
    have := hb 8 9 (by norm_num) (by norm_num)
    norm_num at this l2 ⊢; linarith
  have l7' : Real.log 7 ≤ 1.96 := by
    have l49 : Real.log 49 = 2 * Real.log 7 := by
      rw [show (49:ℝ) = 7 ^ 2 by norm_num, Real.log_pow]; norm_num
    have l48 : Real.log 48 = 4 * Real.log 2 + Real.log 3 := by
      rw [show (48:ℝ) = 2 ^ 4 * 3 by norm_num, Real.log_mul (by norm_num) (by norm_num),
        Real.log_pow]; norm_num
    have := hb 48 49 (by norm_num) (by norm_num)
    norm_num at this l2 l3' ⊢; linarith
  refine ⟨by norm_num at l2 ⊢; linarith, l3', ?_, l7', by norm_num at l2 ⊢; linarith⟩
  norm_num at l5 l2 ⊢; linarith

/-- PROVED in S144 wave 2, formerly a MEDIUM LEAF: the numerical value of `c_E`, Helfgott 1312.7748v2 page 37 display (5.14),
`c_E = γ + Σ_p log p/(p(p-1)) = 1.3325822...`, used here only in the weak form `c_E ≤ 2`,
which is what `c₊ ≥ ρ c_E` on page 39 needs for `ρ ≤ 0.6`. Class MEDIUM. -/
theorem sieveConstant_le : sieveConstant ≤ 2 := by
  set f : ℕ → ℝ := fun p => if p.Prime then Real.log p / ((p : ℝ) * (p - 1 : ℝ)) else 0 with hf
  have hf0 : ∀ n, 0 ≤ f n := fun n => term_nonneg n
  obtain ⟨l2, l3, l5, l7, l8⟩ := log_le_small
  -- partial sums up to 8
  have hS8 : ∑ n ∈ Finset.range 8, f n ≤ 0.68 := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, hf]
    norm_num [Nat.prime_two, Nat.prime_three, Nat.prime_five, Nat.prime_seven]
    have h2 : Real.log 2 ≥ 0 := Real.log_nonneg (by norm_num)
    linarith
  have hind : ∀ k : ℕ, ∑ n ∈ Finset.range (k + 8), f n ≤
      1.12 - (Real.log ((k + 8 : ℕ) : ℝ) + 1) / (((k + 8 : ℕ) : ℝ) - 1) := by
    intro k
    induction k with
    | zero =>
      simp only [zero_add]
      have : (Real.log ((8 : ℕ) : ℝ) + 1) / (((8 : ℕ) : ℝ) - 1) ≤ 0.44 := by
        rw [div_le_iff₀ (by norm_num)]; push_cast; linarith
      linarith
    | succ k ih =>
      rw [show k + 1 + 8 = (k + 8) + 1 by ring, Finset.sum_range_succ]
      have := term_le (k + 8) (by omega)
      have e : ((k + 8 + 1 : ℕ) : ℝ) - 1 = ((k + 8 : ℕ) : ℝ) := by push_cast; ring
      rw [e]
      change _ + f (k + 8) ≤ _
      linarith
  have hall : ∀ N, ∑ n ∈ Finset.range N, f n ≤ 1.12 := by
    intro N
    have hmono : ∑ n ∈ Finset.range N, f n ≤ ∑ n ∈ Finset.range (N + 8), f n :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
        (fun i _ _ => hf0 i)
    have h := hind N
    have hpos : 0 ≤ (Real.log ((N + 8 : ℕ) : ℝ) + 1) / (((N + 8 : ℕ) : ℝ) - 1) := by
      apply div_nonneg
      · have := Real.log_nonneg (show (1:ℝ) ≤ ((N + 8 : ℕ) : ℝ) by push_cast; linarith); linarith
      · push_cast; linarith
    linarith
  have htsum := Real.tsum_le_of_sum_range_le hf0 hall
  have hγ := Real.eulerMascheroniConstant_lt_two_thirds
  unfold sieveConstant
  change Real.eulerMascheroniConstant + ∑' p : ℕ, f p ≤ 2
  linarith

/-- LEAF: display (5.26), Helfgott 1312.7748v2 page 39, proved on pages 39 to 44 by
(5.27) to (5.31), Lemma 5.5 and an interval arithmetic computation over `q < 3.3·10⁹`.
Class HARD. Here `Q₀,min = 10⁵`, `ρ = log Q₀/log Q`,
`ω(ρ) = (log Q₀,min + c₊)/(ρ⁻¹ log Q₀,min + c_E)`, `c₊ = 1.36`, `c_Δ = c₊ - c_E`, and
`err_{q,R} = G_q(R) - φ(q)/q (log R + c_E + Σ_{p|q} log p/p)` as in (5.24). -/
theorem prop56_display526 (Q Q₀ : ℝ) (hQ₀ : 1e5 ≤ Q₀) (hQ : 20000 * Q₀ ≤ Q)
    (hρ : Real.log Q₀ ≤ 0.6 * Real.log Q) (q : ℕ) (hq : 1 ≤ q) (hqQ : (q : ℝ) ≤ Q₀)
    (s : ℝ) (hs1 : 1 ≤ s) (hs : s ≤ Q₀ / q) :
    (q : ℝ) / (Nat.totient q : ℝ) *
        (sieveG q (Q₀ / (s * q)) - (Nat.totient q : ℝ) / q *
          (Real.log (Q₀ / (s * q)) + sieveConstant +
            ∑ p ∈ q.primeFactors, Real.log p / p)) +
      (Real.log 1e5 + 1.36) /
          (Real.log 1e5 / (Real.log Q₀ / Real.log Q) + sieveConstant) *
        max 0 (-((q : ℝ) / (Nat.totient q : ℝ) *
          (sieveG q (Q / (s * q)) - (Nat.totient q : ℝ) / q *
            (Real.log (Q / (s * q)) + sieveConstant +
              ∑ p ∈ q.primeFactors, Real.log p / p)))) ≤
      (1 - (Real.log 1e5 + 1.36) /
          (Real.log 1e5 / (Real.log Q₀ / Real.log Q) + sieveConstant)) *
        (Real.log (s * q) - ∑ p ∈ q.primeFactors, Real.log p / p) +
      (1.36 - sieveConstant) := by
  sorry

/-- `c_E ≥ 0`, from (5.14): `γ > 1/2` and every summand is nonnegative. -/
theorem sieveConstant_nonneg : 0 ≤ sieveConstant := by
  unfold sieveConstant
  have hγ := Real.one_half_lt_eulerMascheroniConstant
  have : 0 ≤ ∑' p : ℕ, (if p.Prime then Real.log p / ((p : ℝ) * (p - 1 : ℝ)) else 0) := by
    apply tsum_nonneg
    intro p
    split_ifs with hp
    · have h2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      apply div_nonneg (Real.log_nonneg (by linarith))
      apply mul_nonneg (by linarith) (by linarith)
    · exact le_rfl
  linarith

/-- `G_q(R) ≥ 1` for `R ≥ 1`, from the term `r = 1` of (5.5). -/
theorem one_le_sieveG (q : ℕ) (R : ℝ) (hR : 1 ≤ R) : 1 ≤ sieveG q R := by
  unfold sieveG
  have hmem : 1 ∈ (Finset.Icc 1 ⌊R⌋₊).filter (fun r => Nat.Coprime r q) := by
    simp only [Finset.mem_filter, Finset.mem_Icc, le_refl, true_and, Nat.coprime_one_left_eq_true,
      and_true]
    exact Nat.one_le_floor_iff _ |>.mpr hR
  have h := Finset.single_le_sum (f := fun r : ℕ =>
      ((ArithmeticFunction.moebius r : ℝ)) ^ 2 / (Nat.totient r : ℝ))
    (fun r _ => div_nonneg (sq_nonneg _) (Nat.cast_nonneg _)) hmem
  simpa using h

/-- `Σ_{p|q} log p/p ≤ log q`, used on page 39 for `log sq - Σ_{p|q} log p/p ≥ 0`. -/
theorem sum_log_primeFactors_le (q : ℕ) (hq : 1 ≤ q) :
    ∑ p ∈ q.primeFactors, Real.log p / p ≤ Real.log q := by
  have h1 : ∑ p ∈ q.primeFactors, Real.log p / p ≤ ∑ p ∈ q.primeFactors, Real.log p := by
    apply Finset.sum_le_sum
    intro p hp
    have hp2 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primeFactors hp).one_le
    exact div_le_self (Real.log_nonneg hp2) hp2
  have h2 : ∑ p ∈ q.primeFactors, Real.log p = Real.log (∏ p ∈ q.primeFactors, (p : ℝ)) := by
    rw [Real.log_prod]
    intro p hp
    have := (Nat.prime_of_mem_primeFactors hp).pos
    positivity
  have h3 : (∏ p ∈ q.primeFactors, (p : ℝ)) ≤ q := by
    have hd := Nat.prod_primeFactors_dvd q
    have := Nat.le_of_dvd (by omega) hd
    rw [← Nat.cast_prod]
    exact_mod_cast this
  have h4 : 0 < (∏ p ∈ q.primeFactors, (p : ℝ)) := by
    apply Finset.prod_pos
    intro p hp
    exact_mod_cast (Nat.prime_of_mem_primeFactors hp).pos
  rw [h2] at h1
  exact h1.trans (Real.log_le_log h4 h3)

/-- `(log Q₀ + c₊)/(log Q + c_E) ≤ ω(ρ)` when `Q₀ ≥ Q₀,min` and `c₊ ≥ ρ c_E`,
Helfgott 1312.7748v2 page 39 below (5.25). -/
theorem omega_ge_aux (a b L cE : ℝ) (hL : 0 < L) (haL : L ≤ a) (hb : 0 < b)
    (hcE0 : 0 ≤ cE) (hcb : cE * a ≤ 1.36 * b) :
    (a + 1.36) / (b + cE) ≤ (L + 1.36) / (L / (a / b) + cE) := by
  have ha0 : 0 < a := by linarith
  have hω' : (L + 1.36) / (L / (a / b) + cE) = (L + 1.36) * a / (L * b + cE * a) := by
    rw [div_div_eq_mul_div, div_add' _ _ _ ha0.ne', div_div_eq_mul_div]
  rw [hω', div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [mul_nonneg (sub_nonneg.2 haL) (sub_nonneg.2 hcb)]

/-- Proposition 5.6, Helfgott 1312.7748v2 page 39 display (5.23).
This is the statement of `prop56`, copied verbatim.
CONDITIONAL ON `sieveConstant_le` and `prop56_display526`. -/
theorem prop56_of_leaves (Q Q₀ : ℝ) (hQ₀ : 1e5 ≤ Q₀) (hQ : 20000 * Q₀ ≤ Q)
    (hρ : Real.log Q₀ ≤ 0.6 * Real.log Q) (q : ℕ) (hq : 1 ≤ q) (hqQ : (q : ℝ) ≤ Q₀)
    (s : ℝ) (hs1 : 1 ≤ s) (hs : s ≤ Q₀ / q) :
    sieveG q (Q₀ / (s * q)) / sieveG q (Q / (s * q)) ≤
      (Real.log Q₀ + 1.36) / (Real.log Q + sieveConstant) := by
  have h526 := prop56_display526 Q Q₀ hQ₀ hQ hρ q hq hqQ s hs1 hs
  have hcE0 := sieveConstant_nonneg
  have hcE1 := sieveConstant_le
  have hQ₀pos : 0 < Q₀ := by norm_num at hQ₀; linarith
  have hQpos : 0 < Q := by linarith
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq
  have hspos : 0 < s := by linarith
  have hsqpos : 0 < s * q := mul_pos hspos hqpos
  have hsqle : s * q ≤ Q₀ := by rwa [le_div_iff₀ hqpos] at hs
  have hR1 : 1 ≤ Q / (s * q) := by
    rw [le_div_iff₀ hsqpos]; linarith
  have hB := one_le_sieveG q (Q / (s * q)) hR1
  have hL : 0 < Real.log 1e5 := Real.log_pos (by norm_num)
  have haL : Real.log 1e5 ≤ Real.log Q₀ := Real.log_le_log (by norm_num) hQ₀
  have hb : 0 < Real.log Q := by
    apply Real.log_pos; norm_num at hQ₀; linarith
  have hlR : Real.log (Q₀ / (s * q)) = Real.log Q₀ - Real.log (s * q) :=
    Real.log_div hQ₀pos.ne' hsqpos.ne'
  have hlR' : Real.log (Q / (s * q)) = Real.log Q - Real.log (s * q) :=
    Real.log_div hQpos.ne' hsqpos.ne'
  have hX : 0 ≤ Real.log (s * q) - ∑ p ∈ q.primeFactors, Real.log p / p := by
    rw [Real.log_mul hspos.ne' hqpos.ne']
    have := sum_log_primeFactors_le q hq
    have := Real.log_nonneg hs1
    linarith
  have hφ : (0 : ℝ) < (Nat.totient q : ℝ) := by exact_mod_cast Nat.totient_pos.2 (by omega)
  set cE := sieveConstant with hcE
  set a := Real.log Q₀ with ha
  set b := Real.log Q with hb'
  set L := Real.log 1e5 with hL'
  set l := Real.log (s * q) with hl
  set P := ∑ p ∈ q.primeFactors, Real.log p / p with hP
  set A := sieveG q (Q₀ / (s * q)) with hA
  set B := sieveG q (Q / (s * q)) with hB'
  set ω := (L + 1.36) / (L / (a / b) + cE) with hω
  set T := (a + 1.36) / (b + cE) with hT
  set k := (q : ℝ) / (Nat.totient q : ℝ) with hk
  have hk0 : 0 < k := div_pos hqpos hφ
  have hkφ : k * ((Nat.totient q : ℝ) / q) = 1 := by
    rw [hk]; field_simp
  set E1 := k * (A - (Nat.totient q : ℝ) / q * (Real.log (Q₀ / (s * q)) + cE + P)) with hE1
  set E2 := k * (B - (Nat.totient q : ℝ) / q * (Real.log (Q / (s * q)) + cE + P)) with hE2
  have hkA : k * A = a - l + cE + P + E1 := by
    rw [hE1, hlR, mul_sub, ← mul_assoc, hkφ]; ring
  have hkB : k * B = b - l + cE + P + E2 := by
    rw [hE2, hlR', mul_sub, ← mul_assoc, hkφ]; ring
  have hbc : 0 < b + cE := by linarith
  have hTeq : T * (b + cE) = a + 1.36 := by rw [hT]; field_simp
  have hT0 : 0 ≤ T := div_nonneg (by linarith) hbc.le
  have hcb : cE * a ≤ 1.36 * b := by
    have h1 := mul_le_mul_of_nonneg_right hcE1 (show 0 ≤ a by linarith)
    linarith
  have hTω : T ≤ ω := omega_ge_aux a b L cE hL haL hb hcE0 hcb
  clear_value E1 E2 ω T k A B P l L a b cE
  have key : E1 ≤ (1 - T) * (l - P) + (1.36 - cE) + T * E2 := by
    have h1 : (1 - ω) * (l - P) ≤ (1 - T) * (l - P) := by
      have := mul_nonneg (sub_nonneg.2 hTω) hX
      linarith
    have h2 : -(ω * max 0 (-E2)) ≤ T * E2 := by
      rcases le_total 0 E2 with h | h
      · rw [max_eq_left (by linarith)]
        have := mul_nonneg hT0 h
        linarith
      · rw [max_eq_right (by linarith)]
        have := mul_nonneg (sub_nonneg.2 hTω) (neg_nonneg.2 h)
        linarith
    linarith
  have hB0 : 0 < B := by linarith
  rw [div_le_iff₀ hB0]
  have : k * A ≤ k * (T * B) := by
    have e : k * (T * B) = T * (k * B) := by ring
    rw [e, hkA, hkB]
    linarith [key, hTeq]
  exact le_of_mul_le_mul_left this hk0

end LeanLab.Ternary.Task580
