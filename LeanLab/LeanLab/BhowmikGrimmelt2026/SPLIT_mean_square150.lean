/-
A split of `mean_square150` into four leaves, with an assembly that uses nothing but the leaves.

The sum in `MeanSquare38` runs over every `N ≤ X`, so the first thing to fix is the parity of
`N`.  At an odd `N` the singular series vanishes: a pair of odd summands cannot sum to an odd
number, and the factor at the prime two in the Euler product records exactly that, so the main
term `N 𝔖(N)` drops out and `E2 N` is just the weighted representation count `r2 N`.  Moreover,
at an odd `N` one of the two summands is even, hence a power of two, so `r2 N` is a short sum of
`vonMangoldt` values and its second moment over the odd `N ≤ X` costs only `X ^ 2` up to a
constant.  The even `N` are where the main term lives and where the whole analytic content sits,
and they are left as one leaf carrying the exponent `3 / 2 + 2 * Θ + ε`.  Finally, the exponent
comparison `2 ≤ 3 / 2 + 2 * Θ + ε` needs `Θ ≥ 1 / 2`, which the functional equation supplies: a
zero-free bound cannot hold below `Θ = 1 / 2`.

So the leaves are: (1) `Θ ≥ 1 / 2` under `ZeroBound Θ`; (2) the singular series vanishes at an
odd `N`; (3) the second moment of `r2` over the odd `N ≤ X` is bounded by a constant times `X ^ 2`;
(4) the second moment of `E2` over the even `N ≤ X` is bounded by a constant times
`X ^ (3 / 2 + 2 * Θ + ε)`.  The assembly adds (3) and (4) and absorbs (3) into (4) by (1).

AI wrote the Lean code.
-/
import LeanLab.BhowmikGrimmelt2026.Decomp150a

namespace LeanLab.BhowmikGrimmelt2026

open LeanLab.ExceptionalSet (PowerBound)

open ArithmeticFunction

/-- LEAF. Step 1, the exponent comparison.  A zero-free bound at level `Θ` cannot hold with `Θ`
below one half: the functional equation puts a zero of the Riemann zeta function at real part
`1 / 2`, which is a zero of an `LFunction` of modulus `1` inside the open strip `0 < re s < 1`.
This is the step that later makes `2 ≤ 3 / 2 + 2 * Θ + ε` for every `ε > 0`, and hence lets the
`X ^ 2` bound on the odd `N` be absorbed into the target exponent. -/
theorem mean_square150_theta_ge_half {Θ : ℝ} (hZ : ZeroBound Θ) : 1 / 2 ≤ Θ := by
  sorry

/-! ## The singular series: divisor formula, multiplicativity, Euler product

Copied (with the leaf's own names) from the private development of the same unit in
`LeanLab/BhowmikGrimmelt2026/Decomp150a.lean`, which is private there and so not visible here.
It is what makes `singular` an Euler product; the leaf `mean_square150_odd_singular` only needs the
factor at the prime two.
-/

private lemma ee_add' (x y : ℝ) : ee (x + y) = ee x * ee y := by
  unfold ee; rw [← Complex.exp_add]; congr 1; push_cast; ring

private lemma ee_nat_mul (k : ℕ) (x : ℝ) : ee ((k : ℝ) * x) = (ee x) ^ k := by
  induction k with
  | zero => simp [ee]
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, ee_add', ih, pow_succ]

private lemma two_pi_I_ne_zero : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have h1 : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  exact mul_ne_zero h1 Complex.I_ne_zero

private lemma ee_one : ee (1 : ℝ) = 1 := by unfold ee; norm_num

private lemma ee_int_mul (k : ℤ) (x : ℝ) : ee ((k : ℝ) * x) = (ee x) ^ k := by
  unfold ee
  have harg : (2 * (Real.pi : ℂ) * Complex.I * (((k : ℝ) * x : ℝ) : ℂ))
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) := by push_cast; ring
  rw [harg, Complex.exp_int_mul]

private lemma ee_int_cast (k : ℤ) : ee ((k : ℝ)) = 1 := by
  have h := ee_int_mul k 1
  rw [mul_one] at h
  rw [h, ee_one, one_zpow]

private lemma ee_eq_one_iff {x : ℝ} : ee x = 1 ↔ ∃ k : ℤ, x = (k : ℝ) := by
  constructor
  · intro h
    have h' : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) = 1 := h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h'
    refine ⟨n, ?_⟩
    have hx : (2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ)
        = (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℝ) : ℂ) := by rw [hn]; push_cast; ring
    exact Complex.ofReal_injective (mul_left_cancel₀ two_pi_I_ne_zero hx)
  · rintro ⟨k, rfl⟩
    exact ee_int_cast k

/-- The orthogonality relation `Σ_{b<m} e(bN/m) = m` if `m ∣ N`, else `0`. -/
private lemma sum_ee_orth {m : ℕ} (hm : 0 < m) (N : ℤ) :
    ∑ b ∈ Finset.range m, ee (((b : ℝ) * (N : ℝ)) / m) =
      if (m : ℤ) ∣ N then (m : ℝ) else 0 := by
  have hmR : ((m : ℝ)) ≠ 0 := by positivity
  set c : ℂ := ee ((N : ℝ) / m) with hc
  have hterm : ∀ b ∈ Finset.range m, ee (((b : ℝ) * (N : ℝ)) / m) = c ^ b := by
    intro b _
    have harg : ((b : ℝ) * (N : ℝ)) / m = (b : ℝ) * ((N : ℝ) / m) := by field_simp
    rw [harg, ee_nat_mul]
  rw [Finset.sum_congr rfl hterm]
  have hcm : c ^ m = 1 := by
    have h1 : c ^ m = ee ((m : ℝ) * ((N : ℝ) / m)) := by
      rw [hc]; exact (ee_nat_mul m ((N : ℝ) / m)).symm
    rw [h1, mul_div_cancel₀ (N : ℝ) hmR, ee_int_cast]
  have hiff : c = 1 ↔ (m : ℤ) ∣ N := by
    rw [hc, ee_eq_one_iff]
    constructor
    · rintro ⟨k, hk⟩
      have h2 : (N : ℝ) = (k : ℝ) * (m : ℝ) := by
        rw [div_eq_iff hmR] at hk
        linarith [hk]
      have h3 : N = k * (m : ℤ) := by exact_mod_cast h2
      exact ⟨k, by rw [h3]; ring⟩
    · rintro ⟨k, rfl⟩
      refine ⟨k, ?_⟩
      push_cast
      field_simp
  by_cases h1 : c = 1
  · rw [if_pos (hiff.mp h1)]
    simp [h1]
  · rw [if_neg (fun h => h1 (hiff.mpr h))]
    rw [geom_sum_eq h1 m, hcm]
    simp

private lemma sum_moebius_divisors (n : ℕ) :
    ∑ d ∈ n.divisors, (moebius d : ℤ) = if n = 1 then 1 else 0 := by
  have h := ArithmeticFunction.coe_mul_zeta_apply (f := moebius) (x := n)
  rw [moebius_mul_coe_zeta] at h
  rw [← h]
  exact ArithmeticFunction.one_apply

private lemma divisors_filter_dvd_eq_gcd {q a : ℕ} (hq : q ≠ 0) :
    q.divisors.filter (fun d => d ∣ a) = (a.gcd q).divisors := by
  have hg : a.gcd q ∣ q := Nat.gcd_dvd_right a q
  have hg0 : a.gcd q ≠ 0 := by
    rcases Nat.eq_zero_or_pos (a.gcd q) with h | h
    · rw [h] at hg; exact absurd (Nat.eq_zero_of_zero_dvd hg) hq
    · exact h.ne'
  rw [← Nat.divisors_filter_dvd_of_dvd hq hg]
  refine Finset.filter_congr (fun d hd => ?_)
  simp only [Nat.mem_divisors] at hd
  exact ⟨fun h => Nat.dvd_gcd h hd.1, fun h => Nat.dvd_trans h (Nat.gcd_dvd_left a q)⟩

private lemma indicator_coprime {q : ℕ} (hq : q ≠ 0) (a : ℕ) :
    (if a.gcd q = 1 then (1:ℂ) else 0)
      = ∑ d ∈ q.divisors, (if d ∣ a then (moebius d : ℂ) else 0) := by
  rw [← Finset.sum_filter, divisors_filter_dvd_eq_gcd hq]
  have h := congrArg (fun z : ℤ => (z : ℂ)) (sum_moebius_divisors (a.gcd q))
  push_cast at h
  exact h.symm

private lemma sum_range_filter_dvd {q d : ℕ} (hd : 0 < d) (hdq : d ∣ q) (g : ℕ → ℂ) :
    ∑ a ∈ (Finset.range q).filter (fun a => d ∣ a), g a
      = ∑ b ∈ Finset.range (q / d), g (d * b) := by
  have hdq' : d * (q / d) = q := Nat.mul_div_cancel' hdq
  have hset : (Finset.range q).filter (fun a => d ∣ a)
      = (Finset.range (q / d)).image (fun b => d * b) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
    constructor
    · rintro ⟨haq, b, rfl⟩
      refine ⟨b, ?_, rfl⟩
      rw [← hdq'] at haq
      exact Nat.lt_of_mul_lt_mul_left haq
    · rintro ⟨b, hb, rfl⟩
      refine ⟨?_, ⟨b, rfl⟩⟩
      rw [← hdq']
      exact Nat.mul_lt_mul_of_pos_left hb hd
  rw [hset, Finset.sum_image]
  intro x _ y _ hxy
  exact Nat.eq_of_mul_eq_mul_left hd hxy

/-- The Ramanujan sum as a divisor sum: `c_q(N) = Σ_{d ∣ q, (q/d) ∣ N} μ(d)·(q/d)`. -/
private lemma ramanujan_eq_complex (q : ℕ) (N : ℤ) :
    ramanujan q N = ∑ d ∈ q.divisors,
      (moebius d : ℂ) * (if ((q / d : ℕ) : ℤ) ∣ N then ((q / d : ℕ) : ℂ) else 0) := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    simp [ramanujan]
  have hq0 : q ≠ 0 := hq.ne'
  have hfilter : (Finset.range q).filter (fun a => Nat.Coprime a q)
      = (Finset.range q).filter (fun a => a.gcd q = 1) :=
    Finset.filter_congr (fun a _ => Nat.coprime_iff_gcd_eq_one)
  rw [ramanujan, hfilter, Finset.sum_filter]
  have hstep1 : ∑ a ∈ Finset.range q, (if a.gcd q = 1 then ee (((a : ℝ) * (N : ℝ)) / q) else 0)
      = ∑ a ∈ Finset.range q,
          (∑ d ∈ q.divisors, (if d ∣ a then (moebius d : ℂ) else 0))
            * ee (((a : ℝ) * (N : ℝ)) / q) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have h1 : (if a.gcd q = 1 then (1:ℂ) else 0) * ee (((a : ℝ) * (N : ℝ)) / q)
        = (if a.gcd q = 1 then ee (((a : ℝ) * (N : ℝ)) / q) else 0) := by
      by_cases h : a.gcd q = 1 <;> simp [h]
    rw [← h1, indicator_coprime hq0 a]
  rw [hstep1]
  have hstep2 : ∀ a ∈ Finset.range q,
      (∑ d ∈ q.divisors, (if d ∣ a then (moebius d : ℂ) else 0))
        * ee (((a : ℝ) * (N : ℝ)) / q)
      = ∑ d ∈ q.divisors,
          (if d ∣ a then (moebius d : ℂ) else 0) * ee (((a : ℝ) * (N : ℝ)) / q) := by
    intro a _
    rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl hstep2, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdvd : d ∣ q := (Nat.mem_divisors.mp hd).1
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd hq
  have hm0 : 0 < q / d := Nat.div_pos (Nat.le_of_dvd hq hdvd) hd0
  have hfac : ∑ a ∈ Finset.range q,
        (if d ∣ a then (moebius d : ℂ) else 0) * ee (((a : ℝ) * (N : ℝ)) / q)
      = ∑ a ∈ Finset.range q,
          (if d ∣ a then (moebius d : ℂ) * ee (((a : ℝ) * (N : ℝ)) / q) else 0) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases h : d ∣ a <;> simp [h]
  rw [hfac, ← Finset.sum_filter, sum_range_filter_dvd hd0 hdvd, ← Finset.mul_sum]
  congr 1
  have hqd : d * (q / d) = q := Nat.mul_div_cancel' hdvd
  have hqd0 : ((q / d : ℕ) : ℝ) ≠ 0 := by positivity
  have harg : ∀ b : ℕ, ee (((d * b : ℕ) : ℝ) * (N : ℝ) / q)
      = ee (((b : ℝ) * (N : ℝ)) / (((q / d : ℕ)) : ℝ)) := by
    intro b
    congr 1
    rw [Nat.cast_div hdvd (by positivity : ((d : ℕ) : ℝ) ≠ 0), ← hqd]
    push_cast
    have hdR : ((d : ℕ) : ℝ) ≠ 0 := by positivity
    have hmR : ((q / d : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp
  rw [Finset.sum_congr rfl (fun b _ => harg b), sum_ee_orth hm0 N]
  have hcd : ((q : ℤ) / (d : ℤ)) = (((q / d : ℕ)) : ℤ) := (Int.natCast_div q d).symm
  by_cases h : (((q / d : ℕ)) : ℤ) ∣ N
  · rw [if_pos h, if_pos h]
    norm_num
  · rw [if_neg h, if_neg h]
    norm_num

/-- The Ramanujan sum, with the real divisor sum written out. -/
private lemma ramanujan_eq_real (N q : ℕ) :
    ramanujan q (N : ℤ) = ∑ d ∈ q.divisors,
      ((((moebius d : ℤ)) : ℝ) : ℂ) *
        ((if (q / d : ℕ) ∣ N then ((((q / d : ℕ)) : ℝ) : ℂ) else 0)) := by
  rw [ramanujan_eq_complex]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hiff : ((((q / d : ℕ)) : ℤ) ∣ ((N : ℕ) : ℤ)) ↔ (q / d : ℕ) ∣ N := Int.natCast_dvd_natCast
  have hmc : (moebius d : ℂ) = ((((moebius d : ℤ)) : ℝ) : ℂ) := by push_cast; ring
  have hif : (if ((((q / d : ℕ)) : ℤ) ∣ ((N : ℕ) : ℤ)) then (((q / d : ℕ)) : ℂ) else 0)
      = ((if (q / d : ℕ) ∣ N then ((((q / d : ℕ)) : ℝ) : ℂ) else 0)) := by
    by_cases hd : (q / d : ℕ) ∣ N
    · rw [if_pos (hiff.mpr hd), if_pos hd]
      norm_num
    · rw [if_neg (fun hh => hd (hiff.mp hh)), if_neg hd]
  rw [hmc, hif]

private lemma cN_eq (N q : ℕ) :
    (ramanujan q (N : ℤ)).re = ∑ d ∈ q.divisors,
      ((moebius d : ℤ) : ℝ) * (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) := by
  rw [ramanujan_eq_real, Complex.re_sum]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  by_cases hd : (q / d : ℕ) ∣ N
  · rw [if_pos hd, if_pos hd, ← Complex.ofReal_mul, Complex.ofReal_re]
  · rw [if_neg hd, if_neg hd]
    simp

private lemma cN_one (N : ℕ) : (ramanujan 1 (N : ℤ)).re = 1 := by
  have h := cN_eq N 1
  rw [h]
  simp [Nat.divisors_one]

private lemma cN_zero (N : ℕ) : (ramanujan 0 (N : ℤ)).re = 0 := by
  simp [ramanujan]

private lemma mul_div_mul_div {a b m n : ℕ} (ha : a ∣ m) (hb : b ∣ n) (ha0 : a ≠ 0) (hb0 : b ≠ 0) :
    (m * n) / (a * b) = (m / a) * (n / b) := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  have ha' : 0 < a := Nat.pos_of_ne_zero ha0
  have hb' : 0 < b := Nat.pos_of_ne_zero hb0
  have hab : 0 < a * b := Nat.mul_pos ha' hb'
  have h1 : a * x * (b * y) = (a * b) * (x * y) := by ring
  rw [h1, Nat.mul_div_right (x * y) hab, Nat.mul_div_right x ha', Nat.mul_div_right y hb']

private lemma cN_summand_mul {N m n a b : ℕ} (hmn : m.Coprime n) (ha : a ∈ m.divisors)
    (hb : b ∈ n.divisors) :
    ((moebius (a * b) : ℤ) : ℝ) *
        (if ((m * n) / (a * b) : ℕ) ∣ N then (((m * n) / (a * b) : ℕ) : ℝ) else 0)
      = (((moebius a : ℤ) : ℝ) * (if (m / a : ℕ) ∣ N then ((m / a : ℕ) : ℝ) else 0))
        * (((moebius b : ℤ) : ℝ) * (if (n / b : ℕ) ∣ N then ((n / b : ℕ) : ℝ) else 0)) := by
  have ha_m : a ∣ m := (Nat.mem_divisors.mp ha).1
  have hb_n : b ∣ n := (Nat.mem_divisors.mp hb).1
  have ha0 : a ≠ 0 := by rintro rfl; simp at ha
  have hb0 : b ≠ 0 := by rintro rfl; simp at hb
  have hcop : a.Coprime b := (hmn.coprime_dvd_left ha_m).coprime_dvd_right hb_n
  have hmu : ((moebius (a * b) : ℤ) : ℝ) = ((moebius a : ℤ) : ℝ) * ((moebius b : ℤ) : ℝ) := by
    rw [IsMultiplicative.map_mul_of_coprime isMultiplicative_moebius hcop]
    push_cast; ring
  have hdiv : ((m * n) / (a * b) : ℕ) = (m / a) * (n / b) := mul_div_mul_div ha_m hb_n ha0 hb0
  have hcop' : (m / a).Coprime (n / b) :=
    (hmn.coprime_dvd_left (Nat.div_dvd_of_dvd ha_m)).coprime_dvd_right
      (Nat.div_dvd_of_dvd hb_n)
  rw [hmu, hdiv]
  have hml : (n / b) ∣ (m / a) * (n / b) := dvd_mul_left _ _
  have hmr : (m / a) ∣ (m / a) * (n / b) := dvd_mul_right _ _
  by_cases hP : (m / a) ∣ N
  · by_cases hQ : (n / b) ∣ N
    · rw [if_pos (hcop'.mul_dvd_of_dvd_of_dvd hP hQ), if_pos hP, if_pos hQ]
      push_cast; ring
    · rw [if_neg (fun hh => hQ (dvd_trans hml hh)), if_pos hP, if_neg hQ]; ring
  · by_cases hQ : (n / b) ∣ N
    · rw [if_neg (fun hh => hP (dvd_trans hmr hh)), if_neg hP, if_pos hQ]; ring
    · rw [if_neg (fun hh => hP (dvd_trans hmr hh)), if_neg hP, if_neg hQ]; ring

/-- `Nat.divisors` of a product of coprime naturals, as the image of the product of the two
divisor sets under multiplication. -/
private lemma divisors_mul_image150 {m n : ℕ} (h : m.Coprime n) :
    (m * n).divisors = (m.divisors ×ˢ n.divisors).image (fun p : ℕ × ℕ => p.1 * p.2) := by
  rw [h.divisors_mul, Finset.map_eq_image]
  show (m.divisors ×ˢ n.divisors).attach.image
      (Function.comp (fun q : ℕ × ℕ => q.1 * q.2)
        (Subtype.val : {x // x ∈ m.divisors ×ˢ n.divisors} → ℕ × ℕ))
    = (m.divisors ×ˢ n.divisors).image (fun q : ℕ × ℕ => q.1 * q.2)
  rw [← Finset.image_image, Finset.attach_image_val]

private lemma cN_mul (N : ℕ) {m n : ℕ} (h : m.Coprime n) : (ramanujan (m * n) (N : ℤ)).re = (ramanujan m (N : ℤ)).re * (ramanujan n (N : ℤ)).re := by
  rcases Nat.eq_zero_or_pos m with hm0 | hm0
  · subst hm0
    rw [Nat.coprime_zero_left] at h
    subst h
    rw [mul_one, cN_zero, cN_one]
    ring
  rcases Nat.eq_zero_or_pos n with hn0 | hn0
  · subst hn0
    rw [Nat.coprime_zero_right] at h
    subst h
    rw [one_mul, cN_zero, cN_one]
    ring
  rw [cN_eq, cN_eq, cN_eq, divisors_mul_image150 h]
  rw [Finset.sum_image]
  · rw [Finset.sum_product]
    simp only [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    refine Finset.sum_congr rfl (fun b hb => ?_)
    exact cN_summand_mul h ha hb
  · intro p hp q hq hEq
    exact h.mul_injOn_divisors hp hq hEq


private lemma divisors_prime (p : ℕ) (hp : p.Prime) : p.divisors = {1, p} := by
  ext d
  rw [Nat.mem_divisors, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hd, -⟩
    rcases Nat.Prime.eq_one_or_self_of_dvd hp d hd with h | h
    · exact Or.inl h
    · exact Or.inr h
  · rintro (rfl | rfl)
    · exact ⟨one_dvd p, hp.ne_zero⟩
    · exact ⟨dvd_rfl, hp.ne_zero⟩

/-- The Ramanujan sum at a prime: `c_p(N) = p - 1` if `p ∣ N` and `-1` otherwise. -/
private lemma cN_prime (N p : ℕ) (hp : p.Prime) :
    (ramanujan p (N : ℤ)).re = if p ∣ N then ((p : ℝ) - 1) else (-1) := by
  rw [cN_eq, divisors_prime p hp]
  have hp1 : p ≠ 1 := hp.ne_one
  have hmu1 : ((moebius 1 : ℤ) : ℝ) = 1 := by simp
  have hmup : ((moebius p : ℤ) : ℝ) = -1 := by
    rw [moebius_apply_prime hp]; norm_num
  rw [Finset.sum_insert (by simp [Ne.symm hp1] : (1 : ℕ) ∉ ({p} : Finset ℕ)),
    Finset.sum_singleton, Nat.div_one, Nat.div_self hp.pos, hmu1, hmup]
  by_cases h : p ∣ N <;> simp [h] <;> ring


private lemma totient_eq_prod_of_squarefree {q : ℕ} (hq : Squarefree q) :
    q.totient = ∏ p ∈ q.primeFactors, (p - 1) := by
  have h := Nat.totient_eq_div_primeFactors_mul q
  have hq0 : q ≠ 0 := hq.ne_zero
  rw [Nat.prod_primeFactors_of_squarefree hq, Nat.div_self (Nat.pos_of_ne_zero hq0),
    one_mul] at h
  exact h

private lemma prime_pow_five_le {p : ℕ} (hp : p.Prime) (h3 : p ≠ 2) :
    (p : ℝ) ^ 5 ≤ ((p : ℝ) - 1) ^ 8 := by
  have hp2 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hpR : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp2
  have h1 : (2 / 3 : ℝ) * (p : ℝ) ≤ (p : ℝ) - 1 := by linarith
  have h2 : ((2 / 3 : ℝ) * (p : ℝ)) ^ 8 ≤ ((p : ℝ) - 1) ^ 8 := by
    exact pow_le_pow_left₀ (by linarith) h1 8
  have h3 : (1 : ℝ) ≤ (2 / 3 : ℝ) ^ 8 * (p : ℝ) ^ 3 := by
    have hbase : (1 : ℝ) ≤ (2 / 3 : ℝ) ^ 8 * (3 : ℝ) ^ 3 := by norm_num
    have hmono : (3 : ℝ) ^ 3 ≤ (p : ℝ) ^ 3 := by
      exact pow_le_pow_left₀ (by norm_num) hpR 3
    have := mul_le_mul_of_nonneg_left hmono (by norm_num : (0:ℝ) ≤ (2/3:ℝ)^8)
    linarith
  have h4 : (p : ℝ) ^ 5 ≤ ((2 / 3 : ℝ) * (p : ℝ)) ^ 8 := by
    have h8 : ((2 / 3 : ℝ) * (p : ℝ)) ^ 8 = (2 / 3 : ℝ) ^ 8 * (p : ℝ) ^ 8 := by ring
    rw [h8]
    have hp5 : (0 : ℝ) < (p : ℝ) ^ 5 := by positivity
    nlinarith [h3, hp5]
  linarith [h2, h4]

private lemma prod_le_one_of_le_one {s : Finset ℕ} {f : ℕ → ℝ}
    (h0 : ∀ p ∈ s, 0 ≤ f p) (h1 : ∀ p ∈ s, f p ≤ 1) : ∏ p ∈ s, f p ≤ 1 := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hA : f a ≤ 1 := h1 a (Finset.mem_insert_self a s)
    have hA0 : 0 ≤ f a := h0 a (Finset.mem_insert_self a s)
    have hB : ∏ x ∈ s, f x ≤ 1 :=
      ih (fun p hp => h0 p (Finset.mem_insert_of_mem hp))
        (fun p hp => h1 p (Finset.mem_insert_of_mem hp))
    have hB0 : 0 ≤ ∏ x ∈ s, f x :=
      Finset.prod_nonneg (fun p hp => h0 p (Finset.mem_insert_of_mem hp))
    nlinarith

private lemma prod_ratio_le {s : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p) :
    ∏ p ∈ s, ((p : ℝ) ^ 5 / ((p : ℝ) - 1) ^ 8) ≤ 32 := by
  have hpos : ∀ p ∈ s, (0 : ℝ) < ((p : ℝ) - 1) ^ 8 := by
    intro p hp
    have hp2 : 2 ≤ p := (hs p hp).two_le
    have : (1 : ℝ) ≤ (p : ℝ) - 1 := by
      have : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
      linarith
    positivity
  have hnum : ∀ p ∈ s, (0 : ℝ) < (p : ℝ) ^ 5 := by
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      have := (hs p hp).two_le
      exact_mod_cast this
    exact pow_pos (by linarith) 5
  have hle1 : ∀ p ∈ s, p ≠ 2 → ((p : ℝ) ^ 5 / ((p : ℝ) - 1) ^ 8) ≤ 1 := by
    intro p hp hpne
    have hp' := hs p hp
    have := prime_pow_five_le hp' hpne
    rw [div_le_one (hpos p hp)]
    exact this
  by_cases h2 : 2 ∈ s
  · rw [← Finset.mul_prod_erase s (fun p => ((p : ℝ) ^ 5 / ((p : ℝ) - 1) ^ 8)) h2]
    have h2val : ((2 : ℝ) ^ 5 / ((2 : ℝ) - 1) ^ 8) = 32 := by norm_num
    have hrest : ∏ x ∈ s.erase 2, ((x : ℝ) ^ 5 / ((x : ℝ) - 1) ^ 8) ≤ 1 := by
      refine prod_le_one_of_le_one (fun p hp => ?_) (fun p hp => ?_)
      · have hp' : p ∈ s := Finset.mem_of_mem_erase hp
        exact le_of_lt (div_pos (hnum p hp') (hpos p hp'))
      · have hp' : p ∈ s := Finset.mem_of_mem_erase hp
        exact hle1 p hp' (Finset.ne_of_mem_erase hp)
    have hrest0 : (0:ℝ) ≤ ∏ x ∈ s.erase 2, ((x : ℝ) ^ 5 / ((x : ℝ) - 1) ^ 8) :=
      Finset.prod_nonneg (fun p hp => le_of_lt (div_pos
        (hnum p (Finset.mem_of_mem_erase hp)) (hpos p (Finset.mem_of_mem_erase hp))))
    have h2val : ((↑(2:ℕ) : ℝ) ^ 5 / ((↑(2:ℕ) : ℝ) - 1) ^ 8) ≤ 32 := by norm_num
    nlinarith [h2val, hrest, hrest0]
  · have : ∏ p ∈ s, ((p : ℝ) ^ 5 / ((p : ℝ) - 1) ^ 8) ≤ 1 := by
      refine prod_le_one_of_le_one (fun p hp => ?_) (fun p hp => ?_)
      · exact le_of_lt (div_pos (hnum p hp) (hpos p hp))
      · exact hle1 p hp (by rintro rfl; exact h2 hp)
    linarith

private lemma totient_pow_le {q : ℕ} (hq : Squarefree q) :
    (q : ℝ) ^ 5 ≤ 32 * (q.totient : ℝ) ^ 8 := by
  have hprod := Nat.prod_primeFactors_of_squarefree hq
  have htot := totient_eq_prod_of_squarefree hq
  have hqeq : (q : ℝ) = ∏ p ∈ q.primeFactors, (p : ℝ) := by
    conv_lhs => rw [← hprod]
    push_cast
    simp
  have hteq : (q.totient : ℝ) = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) := by
    rw [htot]
    push_cast
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hp1 : 1 ≤ p := (Nat.prime_of_mem_primeFactors hp).one_lt.le
    rw [Nat.cast_sub hp1, Nat.cast_one]
  rw [hqeq, hteq]
  have h5 : (∏ p ∈ q.primeFactors, (p : ℝ)) ^ 5 = ∏ p ∈ q.primeFactors, (p : ℝ) ^ 5 :=
    (Finset.prod_pow q.primeFactors 5 (fun p => (p : ℝ))).symm
  have h8 : (∏ p ∈ q.primeFactors, ((p : ℝ) - 1)) ^ 8
      = ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) ^ 8 :=
    (Finset.prod_pow q.primeFactors 8 (fun p => ((p : ℝ) - 1))).symm
  rw [h5, h8]
  have hratio := prod_ratio_le (s := q.primeFactors)
    (fun p hp => Nat.prime_of_mem_primeFactors hp)
  rw [Finset.prod_div_distrib] at hratio
  have hbpos : (0 : ℝ) < ∏ p ∈ q.primeFactors, ((p : ℝ) - 1) ^ 8 := by
    apply Finset.prod_pos
    intro p hp
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      exact_mod_cast this
    have : (0:ℝ) < (p:ℝ) - 1 := by linarith
    positivity
  rw [div_le_iff₀ hbpos] at hratio
  linarith [hratio]

private lemma rpow_totient_le {q : ℕ} (hq : Squarefree q) :
    (q : ℝ) ^ (5 / 4 : ℝ) ≤ 32 ^ (1 / 4 : ℝ) * (q.totient : ℝ) ^ 2 := by
  have h := totient_pow_le hq
  have h1 := Real.rpow_le_rpow (by positivity : (0:ℝ) ≤ (q:ℝ)^5) h (by norm_num : (0:ℝ) ≤ 1/4)
  have e1 : ((q:ℝ)^5) ^ (1/4:ℝ) = (q:ℝ) ^ (5/4:ℝ) := by
    rw [← Real.rpow_natCast (q:ℝ) 5, ← Real.rpow_mul (by positivity)]
    norm_num
  have e2 : ((32:ℝ) * (q.totient:ℝ)^8) ^ (1/4:ℝ)
      = (32:ℝ)^(1/4:ℝ) * ((q.totient:ℝ)^8)^(1/4:ℝ) := by
    rw [Real.mul_rpow (by norm_num) (by positivity)]
  have e3 : ((q.totient:ℝ)^8)^(1/4:ℝ) = (q.totient:ℝ)^2 := by
    rw [← Real.rpow_natCast (q.totient:ℝ) 8, ← Real.rpow_mul (by positivity)]
    norm_num
  rw [e1, e2, e3] at h1
  exact h1


private lemma phiSq_nonneg (q : ℕ) : 0 ≤ ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 := by
  positivity

private lemma phiSq_le (q : ℕ) :
    ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 ≤ 32 ^ (1/4 : ℝ) * (1 / (q : ℝ) ^ (5/4 : ℝ)) := by
  rcases Nat.eq_zero_or_pos q with hq | hq
  · subst hq
    have h1 : ((moebius 0 : ℤ) : ℝ) = 0 := by simp
    rw [h1]
    simp [Real.zero_rpow]
  by_cases hsq : Squarefree q
  · have hmu : ((moebius q : ℤ) : ℝ) ^ 2 = 1 := by
      have h := moebius_sq_eq_one_of_squarefree hsq
      have hc := congrArg (fun z : ℤ => (z : ℝ)) h
      push_cast at hc
      simpa using hc
    rw [hmu]
    have hφpos : (0 : ℝ) < (q.totient : ℝ) ^ 2 := by
      have := Nat.totient_pos.mpr hq
      have : (0:ℝ) < (q.totient : ℝ) := by exact_mod_cast this
      positivity
    have hqpos : (0 : ℝ) < (q : ℝ) ^ (5/4 : ℝ) :=
      Real.rpow_pos_of_pos (by positivity : (0:ℝ) < (q:ℝ)) _
    have hkey := rpow_totient_le hsq
    have e : (32:ℝ) ^ (1/4:ℝ) * (1 / (q : ℝ) ^ (5/4 : ℝ))
        = (32:ℝ) ^ (1/4:ℝ) / (q : ℝ) ^ (5/4 : ℝ) := by ring
    rw [e, le_div_iff₀ hqpos]
    have heq : (1 / (q.totient : ℝ) ^ 2) * (q : ℝ) ^ (5/4 : ℝ)
        = (q : ℝ) ^ (5/4 : ℝ) / (q.totient : ℝ) ^ 2 := by ring
    rw [heq, div_le_iff₀ hφpos]
    linarith [hkey]
  · have hmu : ((moebius q : ℤ) : ℝ) = 0 := by
      have h := moebius_eq_zero_of_not_squarefree hsq
      rw [h]; simp
    rw [hmu]
    have hzero : ((0:ℝ)^2 / (q.totient : ℝ) ^ 2) = 0 := by simp
    rw [hzero]
    have : (0:ℝ) ≤ 32 ^ (1/4:ℝ) * (1 / (q : ℝ) ^ (5/4 : ℝ)) := by positivity
    exact this


private lemma summable_phiSq : Summable (fun q : ℕ => ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) := by
  have hmain : Summable (fun q : ℕ => (32:ℝ) ^ (1/4:ℝ) * (1 / (q : ℝ) ^ (5/4 : ℝ))) := by
    have h := Real.summable_one_div_nat_rpow.mpr (by norm_num : (1:ℝ) < 5/4)
    exact Summable.mul_left _ h
  exact Summable.of_nonneg_of_le phiSq_nonneg phiSq_le hmain

private lemma cN_abs_le (N : ℕ) (hN : 1 ≤ N) (q : ℕ) :
    |(ramanujan q (N : ℤ)).re| ≤ ∑ e ∈ N.divisors, (e : ℝ) := by
  rw [cN_eq]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  have hmu1 : ∀ d : ℕ, |((moebius d : ℤ) : ℝ)| ≤ 1 := by
    intro d
    have h := abs_moebius_le_one (n := d)
    rw [abs_le] at h ⊢
    constructor
    · exact_mod_cast h.1
    · exact_mod_cast h.2
  have hstep1 : ∑ d ∈ q.divisors,
      |((moebius d : ℤ) : ℝ) * (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0)|
      ≤ ∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) := by
    apply Finset.sum_le_sum
    intro d _
    rw [abs_mul]
    have hmu := hmu1 d
    have hnn : (0 : ℝ) ≤ (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) := by
      split_ifs <;> positivity
    calc |((moebius d : ℤ) : ℝ)| * |(if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0)|
        ≤ 1 * |(if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0)| :=
          mul_le_mul_of_nonneg_right hmu (abs_nonneg _)
      _ = |(if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0)| := one_mul _
      _ = (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) := abs_of_nonneg hnn
  refine le_trans hstep1 ?_
  have himg : (q.divisors.filter (fun d => (q / d : ℕ) ∣ N)).image (fun d => q / d) ⊆ N.divisors := by
    intro e he
    obtain ⟨d, hd, rfl⟩ := Finset.mem_image.mp he
    have hdN : (q / d : ℕ) ∣ N := (Finset.mem_filter.mp hd).2
    exact Nat.mem_divisors.mpr ⟨hdN, by omega⟩
  have hinj : Set.InjOn (fun d => q / d) ↑(q.divisors.filter (fun d => (q / d : ℕ) ∣ N)) := by
    intro d hd d' hd' heq
    have hd1 : d ∈ q.divisors := Finset.mem_of_mem_filter d hd
    have hd1' : d' ∈ q.divisors := Finset.mem_of_mem_filter d' hd'
    obtain ⟨hdq, hq0⟩ := Nat.mem_divisors.mp hd1
    obtain ⟨hdq', -⟩ := Nat.mem_divisors.mp hd1'
    have h1 : q / (q / d) = d := Nat.div_div_self hdq hq0
    have h2 : q / (q / d') = d' := Nat.div_div_self hdq' hq0
    have heq' : q / d = q / d' := heq
    rw [heq'] at h1
    rw [h1] at h2
    exact h2
  calc ∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0)
      = ∑ d ∈ q.divisors.filter (fun d => (q / d : ℕ) ∣ N), ((q / d : ℕ) : ℝ) :=
        (Finset.sum_filter _ _).symm
    _ = ∑ e ∈ (q.divisors.filter (fun d => (q / d : ℕ) ∣ N)).image (fun d => q / d), (e : ℝ) :=
        (Finset.sum_image hinj).symm
    _ ≤ ∑ e ∈ N.divisors, (e : ℝ) :=
        Finset.sum_le_sum_of_subset_of_nonneg himg (fun e _ _ => by positivity)

private lemma summable_singTerm (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun q : ℕ => ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * (ramanujan q (N : ℤ)).re) := by
  set C : ℝ := ∑ e ∈ N.divisors, (e : ℝ) with hCval
  have hC : 0 ≤ C := Finset.sum_nonneg (fun e _ => by positivity)
  refine Summable.of_norm_bounded (summable_phiSq.mul_left C) ?_
  intro q
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2| = ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 := by
    rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((moebius q : ℤ) : ℝ)^2),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (q.totient:ℝ)^2)]
  rw [h1]
  calc ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * |(ramanujan q (N : ℤ)).re| ≤ ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * C :=
        mul_le_mul_of_nonneg_left (cN_abs_le N hN q) (phiSq_nonneg q)
    _ = C * (((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) := by ring

private lemma singTerm_one (N : ℕ) :
    ((moebius 1 : ℤ) : ℝ) ^ 2 / ((1).totient : ℝ) ^ 2 * (ramanujan 1 (N : ℤ)).re = 1 := by
  simp [cN_one]

private lemma div_sq_mul_div_sq (a b c d e k : ℝ) :
    (a * d) ^ 2 / ((b * e) ^ 2) * (c * k) = (a ^ 2 / b ^ 2 * c) * (d ^ 2 / e ^ 2 * k) := by
  by_cases hb : b = 0
  · simp [hb]
  by_cases he : e = 0
  · simp [he]
  field_simp

private lemma singTerm_mul (N : ℕ) {m n : ℕ} (hmn : m.Coprime n) :
    ((moebius (m * n) : ℤ) : ℝ) ^ 2 / ((m * n).totient : ℝ) ^ 2 * (ramanujan (m * n) (N : ℤ)).re = (((moebius (m) : ℤ) : ℝ) ^ 2 / (((m).totient : ℝ) ^ 2) * (ramanujan (m) (N : ℤ)).re) * (((moebius (n) : ℤ) : ℝ) ^ 2 / (((n).totient : ℝ) ^ 2) * (ramanujan (n) (N : ℤ)).re) := by
  rw [Nat.totient_mul hmn, cN_mul N hmn,
    IsMultiplicative.map_mul_of_coprime isMultiplicative_moebius hmn]
  push_cast
  exact div_sq_mul_div_sq _ _ _ _ _ _

private lemma singTerm_isMultiplicative (N : ℕ) :
    IsMultiplicative (⟨fun q => ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * (ramanujan q (N : ℤ)).re, by simp⟩ : ArithmeticFunction ℝ) :=
  ⟨singTerm_one N, fun {_ _} hmn => singTerm_mul N hmn⟩

private lemma tsum_singTerm_prime (N p : ℕ) (hp : p.Prime) :
    ∑' e : ℕ, (((moebius (p ^ e) : ℤ) : ℝ) ^ 2 / (((p ^ e).totient : ℝ) ^ 2) * (ramanujan (p ^ e) (N : ℤ)).re) = 1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2 := by
  have hsupp : ∀ e ∉ Finset.range 2, (((moebius (p ^ e) : ℤ) : ℝ) ^ 2 / (((p ^ e).totient : ℝ) ^ 2) * (ramanujan (p ^ e) (N : ℤ)).re) = 0 := by
    intro e he
    simp only [Finset.mem_range, not_lt] at he
    have hμ : moebius (p ^ e) = 0 := by
      rw [moebius_apply_prime_pow hp (by omega : e ≠ 0)]
      rw [if_neg (by omega : ¬ e = 1)]
    rw [hμ]
    simp
  rw [tsum_eq_sum hsupp, Finset.sum_range_succ, Finset.sum_range_one]
  have h0 : p ^ 0 = 1 := by simp
  have h1 : p ^ 1 = p := by simp
  rw [h0, h1, singTerm_one, Nat.totient_prime hp]
  have hcast : (((p - 1 : ℕ)) : ℝ) = (p : ℝ) - 1 := by
    rw [Nat.cast_sub hp.one_lt.le]; norm_num
  have hmu : ((moebius p : ℤ) : ℝ) ^ 2 = 1 := by
    rw [moebius_apply_prime hp]
    norm_num
  rw [hcast, hmu, one_div, div_eq_mul_inv]
  ring

private lemma summable_norm_singTerm (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun q : ℕ => ‖(((moebius (q) : ℤ) : ℝ) ^ 2 / (((q).totient : ℝ) ^ 2) * (ramanujan (q) (N : ℤ)).re)‖) := by
  set C : ℝ := ∑ e ∈ N.divisors, (e : ℝ) with hCval
  have hC : 0 ≤ C := Finset.sum_nonneg (fun e _ => by positivity)
  refine Summable.of_nonneg_of_le (fun q => norm_nonneg _) (fun q => ?_)
    (summable_phiSq.mul_left C)
  rw [Real.norm_eq_abs, abs_mul]
  have h1 : |((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2| = ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 := by
    rw [abs_div, abs_of_nonneg (by positivity : (0:ℝ) ≤ ((moebius q : ℤ) : ℝ)^2),
      abs_of_nonneg (by positivity : (0:ℝ) ≤ (q.totient:ℝ)^2)]
  rw [h1]
  calc ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * |(ramanujan q (N : ℤ)).re| ≤ ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * C :=
        mul_le_mul_of_nonneg_left (cN_abs_le N hN q) (phiSq_nonneg q)
    _ = C * (((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2) := by ring

set_option maxHeartbeats 1000000 in
private lemma eulerProduct_singTerm (N : ℕ) (hN : 1 ≤ N) :
    Filter.Tendsto (fun n : ℕ => ∏ p ∈ n.primesBelow, (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2))
      Filter.atTop (nhds (∑' q : ℕ, (((moebius (q) : ℤ) : ℝ) ^ 2 / (((q).totient : ℝ) ^ 2) * (ramanujan (q) (N : ℤ)).re))) := by
  let F : ArithmeticFunction ℝ :=
    ⟨fun q => ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * (ramanujan q (N : ℤ)).re, by simp⟩
  have hFone : F 1 = 1 := by
    show ((moebius 1 : ℤ) : ℝ) ^ 2 / ((1).totient : ℝ) ^ 2 * (ramanujan 1 (N : ℤ)).re = 1
    exact singTerm_one N
  have hFmul : ∀ {m n : ℕ}, m.Coprime n → F (m * n) = F m * F n := by
    intro m n hmn
    exact singTerm_mul N hmn
  have hFm : F.IsMultiplicative := ⟨hFone, fun {_ _} hmn => hFmul hmn⟩
  have hFs : Summable (fun q : ℕ => ‖F q‖) := by
    show Summable (fun q : ℕ => ‖((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * (ramanujan q (N : ℤ)).re‖)
    exact summable_norm_singTerm N hN
  have h := IsMultiplicative.eulerProduct hFm hFs
  have h2 : (fun n : ℕ => ∏ p ∈ n.primesBelow, ∑' e : ℕ, F (p ^ e))
      = (fun n : ℕ => ∏ p ∈ n.primesBelow, (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2)) := by
    funext n
    exact Finset.prod_congr rfl (fun p hp => tsum_singTerm_prime N p (Nat.mem_primesBelow.mp hp).2)
  rw [h2] at h
  exact h

/-! ## The Ramanujan sum at the prime two, and the singular series at an odd `N` -/

private lemma cN_two_odd (N : ℕ) (hN : Odd N) : (ramanujan 2 (N : ℤ)).re = -1 := by
  rw [cN_prime N 2 Nat.prime_two]
  have h2 : ¬ (2 ∣ N) := fun h => (Nat.not_even_iff_odd).mpr hN (even_iff_two_dvd.mpr h)
  rw [if_neg h2]

private lemma singular_odd_zero (N : ℕ) (hN : Odd N) : singular N = 0 := by
  have hN1 : 1 ≤ N := by
    obtain ⟨m, hm⟩ := hN
    omega
  have hep := eulerProduct_singTerm N hN1
  have hz : ∀ n : ℕ, 3 ≤ n →
      ∏ p ∈ n.primesBelow,
        (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2) = 0 := by
    intro n hn
    have h2mem : 2 ∈ n.primesBelow := Nat.mem_primesBelow.mpr ⟨by omega, Nat.prime_two⟩
    refine Finset.prod_eq_zero h2mem ?_
    rw [cN_two_odd N hN]
    norm_num
  have heq : (fun n : ℕ => ∏ p ∈ n.primesBelow,
        (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2))
      =ᶠ[Filter.atTop] (fun _ => 0) := by
    filter_upwards [Filter.eventually_ge_atTop 3] with n hn
    exact hz n hn
  have h0 : Filter.Tendsto
      (fun n : ℕ => ∏ p ∈ n.primesBelow,
        (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2))
      Filter.atTop (nhds 0) :=
    Filter.Tendsto.congr' heq.symm tendsto_const_nhds
  exact tendsto_nhds_unique hep h0

/-- LEAF. Step 2, the odd `N`: the singular series vanishes there.  The local factor at the prime
two counts the representations of `N` as a sum of two units modulo two; at an odd `N` the two
summands would have to be odd, whose sum is even, so that local count is zero and the whole
series `Σ_q μ(q)² c_q(N) / φ(q)²` vanishes.  This is the step that removes the main term
`N * singular N` from `E2 N` at an odd `N`. -/
theorem mean_square150_odd_singular (N : ℕ) (hN : Odd N) : singular N = 0 :=
  singular_odd_zero N hN

/-! ## `r2` on an odd `N`: every contributing pair has exactly one power of two in it -/

private lemma r2_eq_sum_range150 (N : ℕ) :
    r2 N = ∑ k ∈ Finset.range (N + 1), vonMangoldt k * vonMangoldt (N - k) := by
  unfold r2
  exact Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => vonMangoldt a * vonMangoldt b) N

private lemma vM_le_log150 {N k : ℕ} (hk : k ≤ N) (hN : 1 ≤ N) :
    vonMangoldt k ≤ Real.log N := by
  refine le_trans vonMangoldt_le_log ?_
  rcases Nat.eq_zero_or_pos k with h | h
  · subst h
    simpa using Real.log_nonneg (by exact_mod_cast hN : (1:ℝ) ≤ (N:ℝ))
  · have hkR : (0:ℝ) < (k:ℝ) := by exact_mod_cast h
    have hle : (k:ℝ) ≤ (N:ℝ) := by exact_mod_cast hk
    exact Real.log_le_log hkR hle

/-- An even prime power is a power of two. -/
private lemma even_primePow_eq_two_pow {k : ℕ} (hk : IsPrimePow k) (he : Even k) :
    ∃ i, 0 < i ∧ k = 2 ^ i := by
  obtain ⟨p, j, hp, hj, hpj⟩ := hk
  have hp' : p.Prime := Nat.prime_iff.mpr hp
  have h2k : 2 ∣ k := even_iff_two_dvd.mp he
  have h2pj : 2 ∣ p ^ j := by rw [hpj]; exact h2k
  have h2p : 2 ∣ p := by
    have := Nat.Prime.dvd_of_dvd_pow (p := 2) (by norm_num : (2:ℕ).Prime) h2pj
    simpa using this
  rcases (Nat.dvd_prime hp').mp h2p with h | h
  · exact absurd h (by norm_num)
  · refine ⟨j, hj, ?_⟩
    rw [← hpj, ← h]

private lemma vM_two_pow150 {i : ℕ} (hi : 0 < i) : vonMangoldt (2 ^ i) = Real.log 2 := by
  rw [vonMangoldt_apply_pow (by omega : i ≠ 0), vonMangoldt_apply_prime Nat.prime_two]
  norm_num

/-- At an odd `N` a single term of `r2` is either zero or at most `log 2 * log N`. -/
private lemma r2_term_le150 {N k : ℕ} (hN : 1 ≤ N) (hNo : Odd N) (hk : k ≤ N) :
    vonMangoldt k * vonMangoldt (N - k) ≤
      Real.log 2 * Real.log N *
        (if vonMangoldt k * vonMangoldt (N - k) ≠ 0 then 1 else 0) := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  by_cases h : vonMangoldt k * vonMangoldt (N - k) = 0
  · rw [if_neg (by rw [h]; exact not_not_intro rfl)]
    simp [h]
  · have hk0 : vonMangoldt k ≠ 0 := fun hk' => h (by rw [hk']; simp)
    have hn0 : vonMangoldt (N - k) ≠ 0 := fun hn' => h (by rw [hn']; simp)
    have hppk : IsPrimePow k := vonMangoldt_ne_zero_iff.mp hk0
    have hppn : IsPrimePow (N - k) := vonMangoldt_ne_zero_iff.mp hn0
    have hk1 : vonMangoldt k ≤ Real.log N := vM_le_log150 hk hN
    have hn1 : vonMangoldt (N - k) ≤ Real.log N := vM_le_log150 (Nat.sub_le N k) hN
    rw [if_pos h, mul_one]
    rcases Nat.even_or_odd k with he | ho
    · obtain ⟨i, hi, hik⟩ := even_primePow_eq_two_pow hppk he
      have hvm : vonMangoldt k = Real.log 2 := by rw [hik, vM_two_pow150 hi]
      rw [hvm]
      exact mul_le_mul_of_nonneg_left hn1 hlog2
    · have hne : Even (N - k) := by
        have hNe : ¬ Even N := (Nat.not_even_iff_odd).mpr hNo
        have hke : ¬ Even k := (Nat.not_even_iff_odd).mpr ho
        rw [Nat.even_sub hk]
        exact ⟨fun hh => absurd hh hNe, fun hh => absurd hh hke⟩
      obtain ⟨i, hi, hik⟩ := even_primePow_eq_two_pow hppn hne
      have hvm : vonMangoldt (N - k) = Real.log 2 := by rw [hik, vM_two_pow150 hi]
      rw [hvm]
      calc vonMangoldt k * Real.log 2 ≤ Real.log N * Real.log 2 :=
            mul_le_mul_of_nonneg_right hk1 hlog2
        _ = Real.log 2 * Real.log N := by ring

/-! ## Counting the terms that survive -/

private lemma card_even_pp150 (N : ℕ) (hN : 1 ≤ N) :
    ((Finset.range (N + 1)).filter (fun k => Even k ∧ vonMangoldt k ≠ 0)).card
      ≤ Nat.log 2 N + 1 := by
  have hsub : (Finset.range (N + 1)).filter (fun k => Even k ∧ vonMangoldt k ≠ 0)
      ⊆ (Finset.range (Nat.log 2 N + 1)).image (fun i => 2 ^ i) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkN, he, hvm⟩ := hk
    obtain ⟨i, hi, hik⟩ := even_primePow_eq_two_pow (vonMangoldt_ne_zero_iff.mp hvm) he
    refine Finset.mem_image.mpr ⟨i, ?_, hik.symm⟩
    rw [Finset.mem_range]
    have h2i : 2 ^ i ≤ N := by rw [← hik]; omega
    have := Nat.le_log_of_pow_le (b := 2) (by norm_num : 1 < 2) h2i
    omega
  calc ((Finset.range (N + 1)).filter (fun k => Even k ∧ vonMangoldt k ≠ 0)).card
      ≤ ((Finset.range (Nat.log 2 N + 1)).image (fun i => 2 ^ i)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.range (Nat.log 2 N + 1)).card := Finset.card_image_le
    _ = Nat.log 2 N + 1 := Finset.card_range _

private lemma card_odd_pp150 (N : ℕ) (hN : 1 ≤ N) (hNo : Odd N) :
    ((Finset.range (N + 1)).filter (fun k => Odd k ∧ vonMangoldt (N - k) ≠ 0)).card
      ≤ Nat.log 2 N + 1 := by
  have hsub : (Finset.range (N + 1)).filter (fun k => Odd k ∧ vonMangoldt (N - k) ≠ 0)
      ⊆ (Finset.range (Nat.log 2 N + 1)).image (fun i => N - 2 ^ i) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkN, ho, hvm⟩ := hk
    have hne : Even (N - k) := by
      have hNe : ¬ Even N := (Nat.not_even_iff_odd).mpr hNo
      have hke : ¬ Even k := (Nat.not_even_iff_odd).mpr ho
      rw [Nat.even_sub (by omega : k ≤ N)]
      exact ⟨fun hh => absurd hh hNe, fun hh => absurd hh hke⟩
    obtain ⟨i, hi, hik⟩ := even_primePow_eq_two_pow (vonMangoldt_ne_zero_iff.mp hvm) hne
    refine Finset.mem_image.mpr ⟨i, ?_, ?_⟩
    · rw [Finset.mem_range]
      have h2i : 2 ^ i ≤ N := by rw [← hik]; omega
      have := Nat.le_log_of_pow_le (b := 2) (by norm_num : 1 < 2) h2i
      omega
    · omega
  calc ((Finset.range (N + 1)).filter (fun k => Odd k ∧ vonMangoldt (N - k) ≠ 0)).card
      ≤ ((Finset.range (Nat.log 2 N + 1)).image (fun i => N - 2 ^ i)).card :=
        Finset.card_le_card hsub
    _ ≤ (Finset.range (Nat.log 2 N + 1)).card := Finset.card_image_le
    _ = Nat.log 2 N + 1 := Finset.card_range _

private lemma card_support150 (N : ℕ) (hN : 1 ≤ N) (hNo : Odd N) :
    ((Finset.range (N + 1)).filter (fun k => vonMangoldt k * vonMangoldt (N - k) ≠ 0)).card
      ≤ 2 * (Nat.log 2 N + 1) := by
  set A := (Finset.range (N + 1)).filter (fun k => Even k ∧ vonMangoldt k ≠ 0) with hA
  set B := (Finset.range (N + 1)).filter (fun k => Odd k ∧ vonMangoldt (N - k) ≠ 0) with hB
  have hsub : (Finset.range (N + 1)).filter (fun k => vonMangoldt k * vonMangoldt (N - k) ≠ 0)
      ⊆ A ∪ B := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_range] at hk
    obtain ⟨hkN, hprod⟩ := hk
    have h1 : vonMangoldt k ≠ 0 := fun h => hprod (by rw [h]; simp)
    have h2 : vonMangoldt (N - k) ≠ 0 := fun h => hprod (by rw [h]; simp)
    have hkN' : k ∈ Finset.range (N + 1) := Finset.mem_range.mpr hkN
    rcases Nat.even_or_odd k with he | ho
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hkN', he, h1⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hkN', ho, h2⟩)
  calc ((Finset.range (N + 1)).filter (fun k => vonMangoldt k * vonMangoldt (N - k) ≠ 0)).card
      ≤ (A ∪ B).card := Finset.card_le_card hsub
    _ ≤ A.card + B.card := Finset.card_union_le A B
    _ ≤ (Nat.log 2 N + 1) + (Nat.log 2 N + 1) := by
        rw [hA, hB]
        exact add_le_add (card_even_pp150 N hN) (card_odd_pp150 N hN hNo)
    _ = 2 * (Nat.log 2 N + 1) := by ring

/-! ## The pointwise bound -/

private lemma r2_le150 (N : ℕ) (hN : 1 ≤ N) (hNo : Odd N) :
    r2 N ≤ Real.log 2 * Real.log N * (2 * ((Nat.log 2 N : ℝ) + 1)) := by
  rw [r2_eq_sum_range150]
  have hstep : ∑ k ∈ Finset.range (N + 1), vonMangoldt k * vonMangoldt (N - k) ≤
      ∑ k ∈ Finset.range (N + 1),
        Real.log 2 * Real.log N *
          (if vonMangoldt k * vonMangoldt (N - k) ≠ 0 then (1 : ℝ) else 0) :=
    Finset.sum_le_sum (fun k hk => r2_term_le150 hN hNo (by simpa using hk))
  refine le_trans hstep ?_
  rw [← Finset.mul_sum, Finset.sum_boole]
  have hcard := card_support150 N hN hNo
  have hnn : 0 ≤ Real.log 2 * Real.log N :=
    mul_nonneg (Real.log_nonneg (by norm_num)) (Real.log_nonneg (by exact_mod_cast hN))
  have hcast : ((((Finset.range (N + 1)).filter
      (fun k => vonMangoldt k * vonMangoldt (N - k) ≠ 0)).card : ℕ) : ℝ)
      ≤ 2 * ((Nat.log 2 N : ℝ) + 1) := by
    push_cast
    exact_mod_cast hcard
  exact mul_le_mul_of_nonneg_left hcast hnn

private lemma nat_log_le_two_log150 (N : ℕ) (hN : 1 ≤ N) :
    ((Nat.log 2 N : ℝ)) ≤ 2 * Real.log N := by
  have hN0 : N ≠ 0 := by omega
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hpowN : 2 ^ Nat.log 2 N ≤ N := Nat.pow_log_le_self 2 hN0
  have hpos : (0:ℝ) < ((2:ℝ) ^ Nat.log 2 N) := by positivity
  have hle : ((2:ℝ) ^ Nat.log 2 N) ≤ (N:ℝ) := by exact_mod_cast hpowN
  have hlog : Real.log ((2:ℝ) ^ Nat.log 2 N) ≤ Real.log (N:ℝ) := Real.log_le_log hpos hle
  rw [Real.log_pow] at hlog
  have hlog2 : (1/2:ℝ) ≤ Real.log 2 := by nlinarith [Real.log_two_gt_d9]
  have hk : (0:ℝ) ≤ (Nat.log 2 N : ℝ) := Nat.cast_nonneg _
  nlinarith [hlog, hlog2, hk]

/-- `(log N)^4 ≤ 20736 N`, from `log N ≤ 12 N^{1/12}`. -/
private lemma log_four_le150 (N : ℕ) (hN : 1 ≤ N) : (Real.log N) ^ 4 ≤ 20736 * (N : ℝ) := by
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast hN
  have hle1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
  have hlog0 : 0 ≤ Real.log N := Real.log_nonneg hle1
  have h1 : Real.log N ≤ 12 * (N:ℝ) ^ (1/12:ℝ) := by
    have h := Real.log_natCast_le_rpow_div N (by norm_num : (0:ℝ) < 1/12)
    have e : (N:ℝ) ^ (1/12:ℝ) / (1/12) = 12 * (N:ℝ) ^ (1/12:ℝ) := by ring
    rw [e] at h
    exact h
  have h2 : (Real.log N) ^ 4 ≤ (12 * (N:ℝ) ^ (1/12:ℝ)) ^ 4 := pow_le_pow_left₀ hlog0 h1 4
  have h3 : (12 * (N:ℝ) ^ (1/12:ℝ)) ^ 4 = 20736 * (N:ℝ) ^ (1/3:ℝ) := by
    have hpow : ((N:ℝ) ^ (1/12:ℝ)) ^ 4 = (N:ℝ) ^ (1/3:ℝ) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]
      norm_num
    rw [mul_pow, hpow]
    norm_num
  have h4 : (N:ℝ) ^ (1/3:ℝ) ≤ (N:ℝ) := by
    have hle1 : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN
    have h := Real.rpow_le_rpow_of_exponent_le hle1 (by norm_num : (1/3:ℝ) ≤ 1)
    simpa using h
  rw [h3] at h2
  nlinarith [h2, h4, hNpos]

private lemma r2_sq_le150 (N : ℕ) (hN : 1 ≤ N) (hNo : Odd N) :
    (r2 N) ^ 2 ≤ 72 * (Real.log 2) ^ 2 * (Real.log N) ^ 4 + 36 * (Real.log 2) ^ 2 := by
  have hlogN : 0 ≤ Real.log N := Real.log_nonneg (by exact_mod_cast hN)
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hkl : (Nat.log 2 N : ℝ) ≤ 2 * Real.log N := nat_log_le_two_log150 N hN
  have hbase : r2 N ≤ Real.log 2 * Real.log N * (2 * (2 * Real.log N + 1)) := by
    refine le_trans (r2_le150 N hN hNo) ?_
    have hmono : 2 * ((Nat.log 2 N : ℝ) + 1) ≤ 2 * (2 * Real.log N + 1) := by linarith
    exact mul_le_mul_of_nonneg_left hmono (mul_nonneg hlog2 hlogN)
  have hb0 : (0:ℝ) ≤ Real.log 2 * Real.log N * (2 * (2 * Real.log N + 1)) :=
    mul_nonneg (mul_nonneg hlog2 hlogN) (by nlinarith [hlogN])
  have hr2nn : (0:ℝ) ≤ r2 N := by
    unfold r2
    exact Finset.sum_nonneg (fun x _ => mul_nonneg vonMangoldt_nonneg vonMangoldt_nonneg)
  have hsq : (r2 N) ^ 2 ≤ (Real.log 2 * Real.log N * (2 * (2 * Real.log N + 1))) ^ 2 :=
    pow_le_pow_left₀ hr2nn hbase 2
  have hquad : (2 * (2 * Real.log N + 1)) ^ 2 ≤ 36 * ((Real.log N) ^ 2 + 1) := by
    nlinarith [hlogN]
  have hS : (0:ℝ) ≤ (Real.log 2 * Real.log N) ^ 2 := sq_nonneg _
  have step : (Real.log 2 * Real.log N * (2 * (2 * Real.log N + 1))) ^ 2
      ≤ 36 * (Real.log 2) ^ 2 * ((Real.log N) ^ 4 + (Real.log N) ^ 2) := by
    have h1 : (Real.log 2 * Real.log N * (2 * (2 * Real.log N + 1))) ^ 2
        = (Real.log 2 * Real.log N) ^ 2 * (2 * (2 * Real.log N + 1)) ^ 2 := by ring
    rw [h1]
    have h2 := mul_le_mul_of_nonneg_left hquad hS
    nlinarith [h2]
  have hlast : (Real.log N) ^ 2 ≤ (Real.log N) ^ 4 + 1 := by
    rcases le_total (Real.log N) 1 with h | h
    · nlinarith [hlogN, sq_nonneg (Real.log N)]
    · have h1 : (Real.log N) ^ 2 ≤ (Real.log N) ^ 4 :=
        pow_le_pow_right₀ h (by norm_num : 2 ≤ 4)
      linarith
  have hkey : ((Real.log N) ^ 4 + (Real.log N) ^ 2) ≤ 2 * (Real.log N) ^ 4 + 1 := by linarith
  have h36 : (0:ℝ) ≤ 36 * (Real.log 2) ^ 2 := by positivity
  calc (r2 N) ^ 2
      ≤ (Real.log 2 * Real.log N * (2 * (2 * Real.log N + 1))) ^ 2 := hsq
    _ ≤ 36 * (Real.log 2) ^ 2 * ((Real.log N) ^ 4 + (Real.log N) ^ 2) := step
    _ ≤ 36 * (Real.log 2) ^ 2 * (2 * (Real.log N) ^ 4 + 1) :=
        mul_le_mul_of_nonneg_left hkey h36
    _ = 72 * (Real.log 2) ^ 2 * (Real.log N) ^ 4 + 36 * (Real.log 2) ^ 2 := by ring

/-- LEAF. Step 3, the second moment over the odd `N`.  At an odd `N` a summand of `N` which is a
prime power is either odd or a power of two, and exactly one of the two summands is even, so
`r2 N` is at most `log 2` times a sum of `vonMangoldt` over the few shifted points `N - 2 ^ k`,
which is bounded by a fixed power of `log N`.  Squaring and summing over the odd `N ≤ X`
therefore costs a constant times `X ^ 2`.  The constant is chosen positive, and the bound is
genuinely a bound: at `X = 1` the sum is `(r2 1) ^ 2 = 0`. -/
theorem mean_square150_odd_second_moment :
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℕ, 1 ≤ X →
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N => Odd N), (r2 N) ^ 2 ≤ C * (X : ℝ) ^ 2 := by
  refine ⟨72 * (Real.log 2) ^ 2 * 20736 + 36 * (Real.log 2) ^ 2 + 1, by positivity, ?_⟩
  intro X hX
  set S := (Finset.Icc 1 X).filter (fun N => Odd N) with hS
  have hXR : (1:ℝ) ≤ (X:ℝ) := by exact_mod_cast hX
  have hmem : ∀ N ∈ S, 1 ≤ N ∧ N ≤ X ∧ Odd N := by
    intro N hN
    rw [hS, Finset.mem_filter, Finset.mem_Icc] at hN
    exact ⟨hN.1.1, hN.1.2, hN.2⟩
  have hterm : ∀ N ∈ S, (r2 N) ^ 2
      ≤ 72 * (Real.log 2) ^ 2 * 20736 * (X : ℝ) + 36 * (Real.log 2) ^ 2 := by
    intro N hN
    obtain ⟨hN1, hNX, hNo⟩ := hmem N hN
    have h1 := r2_sq_le150 N hN1 hNo
    have h2 := log_four_le150 N hN1
    have h3 : (N:ℝ) ≤ (X:ℝ) := by exact_mod_cast hNX
    have h4 : (0:ℝ) ≤ (Real.log 2) ^ 2 := sq_nonneg _
    nlinarith [h1, h2, h3, h4]
  have hcard : S.card ≤ X := by
    have hsub : S ⊆ Finset.Icc 1 X := by rw [hS]; exact Finset.filter_subset _ _
    have h2 := Finset.card_le_card hsub
    rw [Nat.card_Icc] at h2
    omega
  have hcardR : ((S.card : ℕ) : ℝ) ≤ (X:ℝ) := by exact_mod_cast hcard
  have hconst : (0:ℝ) ≤ 72 * (Real.log 2) ^ 2 * 20736 * (X : ℝ) + 36 * (Real.log 2) ^ 2 := by
    have h5 : (0:ℝ) ≤ (Real.log 2) ^ 2 := sq_nonneg _
    nlinarith [h5, hXR]
  calc ∑ N ∈ S, (r2 N) ^ 2
      ≤ ∑ _N ∈ S, (72 * (Real.log 2) ^ 2 * 20736 * (X : ℝ) + 36 * (Real.log 2) ^ 2) :=
        Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (72 * (Real.log 2) ^ 2 * 20736 * (X : ℝ) + 36 * (Real.log 2) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (X:ℝ) * (72 * (Real.log 2) ^ 2 * 20736 * (X : ℝ) + 36 * (Real.log 2) ^ 2) :=
        mul_le_mul_of_nonneg_right hcardR hconst
    _ ≤ (72 * (Real.log 2) ^ 2 * 20736 + 36 * (Real.log 2) ^ 2 + 1) * (X : ℝ) ^ 2 := by
        have hB : (0:ℝ) ≤ 36 * (Real.log 2) ^ 2 := by positivity
        have hXX : (X:ℝ) ≤ (X:ℝ) ^ 2 := by nlinarith [hXR, sq_nonneg ((X:ℝ) - 1)]
        have hs : 36 * (Real.log 2) ^ 2 * (X:ℝ) ≤ 36 * (Real.log 2) ^ 2 * (X:ℝ)^2 :=
          mul_le_mul_of_nonneg_left hXX hB
        have hsq2 : (0:ℝ) ≤ (X:ℝ) ^ 2 := sq_nonneg _
        nlinarith [hs, hsq2, hXR]

/-- LEAF. Step 4, the second moment over the even `N`: this is the analytic core, for the `N`
that carry a main term.  The circle method writes `r2` on the major arcs, where the zero-free
hypothesis governs the zeros and produces the exponent `2 * Θ` after Parseval, and bounds the
minor arcs by a second moment of the prime exponential sum; the two contributions combine to a
mean square of `E2` over the even `N ≤ X` of at most a constant times
`X ^ (3 / 2 + 2 * Θ + ε)`.  The constant depends on `Θ` and `ε` and is only asserted to exist.
This leaf is strictly weaker than the target, which asks the same bound for all `N ≤ X`. -/
theorem mean_square150_even_second_moment (Θ : ℝ) (hΘ : Θ < 3 / 4) (hZ : ZeroBound Θ) :
    ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, ∀ X : ℕ, 1 ≤ X →
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N), (E2 N) ^ 2 ≤
        C * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
  sorry

/-- The mean square estimate, assembled from the four leaves.  Split the sum over `N ≤ X` into
the even and the odd `N`; on the odd `N` the main term drops out by Step 2, so that half becomes
the second moment of `r2` and is bounded by a constant times `X ^ 2` by Step 3; the even half is
bounded by Step 4.  Step 1 gives `2 ≤ 3 / 2 + 2 * Θ + ε`, so the `X ^ 2` term is dominated by
`X ^ (3 / 2 + 2 * Θ + ε)` and the two constants add. -/
theorem mean_square150_split : MeanSquare38 := by
  intro Θ hΘ hZ ε hε
  obtain ⟨Ce, heEven⟩ := mean_square150_even_second_moment Θ hΘ hZ ε hε
  obtain ⟨Co, hoPos, hoOdd⟩ := mean_square150_odd_second_moment
  refine ⟨Ce + Co, ?_⟩
  intro X hX
  have hhalf : (1 : ℝ) / 2 ≤ Θ := mean_square150_theta_ge_half hZ
  have hX1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hexp : (2 : ℝ) ≤ 3 / 2 + 2 * Θ + ε := by linarith
  have hmono : (X : ℝ) ^ (2 : ℝ) ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) :=
    Real.rpow_le_rpow_of_exponent_le hX1 hexp
  have hmono' : (X : ℝ) ^ 2 ≤ (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
    simpa using hmono
  have hsplit :
      (∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N), (E2 N) ^ 2) +
        ∑ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ Even N), (E2 N) ^ 2 =
      ∑ N ∈ Finset.Icc 1 X, (E2 N) ^ 2 :=
    Finset.sum_filter_add_sum_filter_not (s := Finset.Icc 1 X)
      (p := fun N => Even N) (f := fun N => (E2 N) ^ 2)
  have hodd :
      ∑ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ Even N), (E2 N) ^ 2 ≤
        Co * (X : ℝ) ^ 2 := by
    have hEq :
        ∑ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ Even N), (E2 N) ^ 2 =
        ∑ N ∈ (Finset.Icc 1 X).filter (fun N => Odd N), (r2 N) ^ 2 := by
      refine Finset.sum_congr ?_ ?_
      · ext N
        simp only [Finset.mem_filter]
        exact ⟨fun h => ⟨h.1, Nat.not_even_iff_odd.mp h.2⟩,
          fun h => ⟨h.1, Nat.not_even_iff_odd.mpr h.2⟩⟩
      · intro N hN
        rw [Finset.mem_filter] at hN
        have h0 : singular N = 0 := mean_square150_odd_singular N hN.2
        simp only [E2, h0, mul_zero, sub_zero]
    rw [hEq]
    exact hoOdd X hX
  have heven := heEven X hX
  calc ∑ N ∈ Finset.Icc 1 X, (E2 N) ^ 2
      = (∑ N ∈ (Finset.Icc 1 X).filter (fun N => Even N), (E2 N) ^ 2) +
          ∑ N ∈ (Finset.Icc 1 X).filter (fun N => ¬ Even N), (E2 N) ^ 2 := hsplit.symm
    _ ≤ Ce * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) + Co * (X : ℝ) ^ 2 := by linarith
    _ ≤ Ce * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) + Co * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by
      have hCo := mul_le_mul_of_nonneg_left hmono' hoPos.le
      linarith
    _ = (Ce + Co) * (X : ℝ) ^ (3 / 2 + 2 * Θ + ε) := by ring

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.mean_square150_split
