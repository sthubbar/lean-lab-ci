/-
A split of `facts81`, the two formulas of display 8.1, into four leaves plus an assembly.

The four leaves are (1) the sign of the ordinary singular series at an even `N ≥ 2`, which
lets its complex image keep the same size, (2) the base case of the generalised series, at
both characters trivial of conductor one, where it is the ordinary singular series, (3) the
conductor saving: twisting the trivial character by a primitive real character of conductor
`r` costs the factor `r / φ(r)²`, and (4) the diagonal factorisation: for a primitive real
`χ` whose conductor divides `N`, the series of the pair `(χ, χ)` is `χ(-1)` times the
series of the pair of trivial characters of conductor one. The assembly rewrites the first
formula into the second through leaf 2 and reads off the second formula from leaf 4.

AI wrote the Lean code. Binary Goldbach is OPEN. The four leaves are open.
-/
import LeanLab.BhowmikGrimmelt2026.Statements

namespace LeanLab.BhowmikGrimmelt2026

open Real Filter Topology MeasureTheory ArithmeticFunction
open LeanLab.ExceptionalSet (E PowerBound PowerSaving LogPowerSaving EventuallyBelow DensityZero)

attribute [local instance] Classical.propDecidable

open ArithmeticFunction

/-! ### Development for `exceptional_gap150`: the singular series on even `N`

`singular N = Σ_q μ(q)² c_q(N)/φ(q)²`.  Below: (i) the divisor-sum formula for the
Ramanujan sum `c_q(N)`, (ii) multiplicativity of `q ↦ c_q(N)`, (iii) its value at a prime,
(iv) summability of `μ(q)²/φ(q)²` and of the series term.  All `private` to this file. -/

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
  have hm0' : m ≠ 0 := hm0.ne'
  have hn0' : n ≠ 0 := hn0.ne'
  rw [cN_eq, cN_eq, cN_eq, Nat.divisors_mul, Finset.mul_def]
  rw [Finset.sum_image]
  · rw [Finset.sum_product]
    simp only [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun a ha => ?_)
    refine Finset.sum_congr rfl (fun b hb => ?_)
    exact cN_summand_mul h ha hb
  · rintro ⟨a, b⟩ hp ⟨a', b'⟩ hp' hEq
    simp only [Finset.mem_coe, Finset.mem_product] at hp hp'
    obtain ⟨ham, hbn⟩ := hp
    obtain ⟨ha'm, hb'n⟩ := hp'
    change a * b = a' * b' at hEq
    have ha_m : a ∣ m := (Nat.mem_divisors.mp ham).1
    have hb_n : b ∣ n := (Nat.mem_divisors.mp hbn).1
    have ha'_m : a' ∣ m := (Nat.mem_divisors.mp ha'm).1
    have hb'_n : b' ∣ n := (Nat.mem_divisors.mp hb'n).1
    have ha0 : a ≠ 0 := by rintro rfl; simp at ham
    have hcop_ab' : a.Coprime b' := (h.coprime_dvd_left ha_m).coprime_dvd_right hb'_n
    have hcop_a'b : a'.Coprime b := (h.coprime_dvd_left ha'_m).coprime_dvd_right hb_n
    have h1 : a ∣ a' := by
      have : a ∣ a' * b' := by rw [← hEq]; exact dvd_mul_right a b
      exact hcop_ab'.dvd_of_dvd_mul_right this
    have h2 : a' ∣ a := by
      have : a' ∣ a * b := by rw [hEq]; exact dvd_mul_right a' b'
      exact hcop_a'b.dvd_of_dvd_mul_right this
    have haa : a = a' := Nat.dvd_antisymm h1 h2
    subst haa
    have : b = b' := Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero ha0) hEq
    exact Prod.ext rfl this

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
  set C : ℝ := ∑ e ∈ N.divisors, (e : ℝ) with hCdef
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
  set C : ℝ := ∑ e ∈ N.divisors, (e : ℝ) with hCdef
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

private lemma prod_one_sub_inv_sq {M : ℕ} (hM : 1 ≤ M) :
    ∏ m ∈ Finset.Icc 2 M, (1 - 1 / (m : ℝ) ^ 2) = ((M : ℝ) + 1) / (2 * (M : ℝ)) := by
  induction M with
  | zero => omega
  | succ k ih =>
    rcases Nat.eq_zero_or_pos k with hk | hk
    · subst hk
      simp
    · have h1 : 1 ≤ k := hk
      rw [Finset.prod_Icc_succ_top (by omega : 2 ≤ k + 1), ih h1]
      have hk0 : (k : ℝ) ≠ 0 := by positivity
      have hk1 : ((k : ℝ) + 1) ≠ 0 := by positivity
      have hk2 : (2 * (k : ℝ)) ≠ 0 := by positivity
      push_cast
      field_simp
      ring

/-- The odd-prime factor in the singular series: `∏_{2 ≤ m ≤ M}(1 - 1/m²) ≥ 1/2`. -/
private lemma half_le_prod_one_sub_inv_sq {M : ℕ} (hM : 1 ≤ M) :
    (1 / 2 : ℝ) ≤ ∏ m ∈ Finset.Icc 2 M, (1 - 1 / (m : ℝ) ^ 2) := by
  rw [prod_one_sub_inv_sq hM]
  have hM0 : (0 : ℝ) < (M : ℝ) := by exact_mod_cast hM
  rw [le_div_iff₀ (by positivity)]
  linarith


private lemma one_le_prod_of_one_le {s : Finset ℕ} {f : ℕ → ℝ} (h : ∀ p ∈ s, 1 ≤ f p) :
    (1 : ℝ) ≤ ∏ p ∈ s, f p := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have hA : 1 ≤ f a := h a (Finset.mem_insert_self a s)
    have hB : 1 ≤ ∏ x ∈ s, f x :=
      ih (fun p hp => h p (Finset.mem_insert_of_mem hp))
    have hB0 : (0 : ℝ) ≤ ∏ x ∈ s, f x := le_trans zero_le_one hB
    nlinarith

private lemma prod_le_prod' {s : Finset ℕ} {f g : ℕ → ℝ} (h0 : ∀ p ∈ s, 0 ≤ g p)
    (h : ∀ p ∈ s, g p ≤ f p) : ∏ p ∈ s, g p ≤ ∏ p ∈ s, f p := by
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    have hA0 : 0 ≤ g a := h0 a (Finset.mem_insert_self a s)
    have hA : g a ≤ f a := h a (Finset.mem_insert_self a s)
    have hB0 : 0 ≤ ∏ x ∈ s, g x :=
      Finset.prod_nonneg (fun p hp => h0 p (Finset.mem_insert_of_mem hp))
    have hB : ∏ x ∈ s, g x ≤ ∏ x ∈ s, f x :=
      ih (fun p hp => h0 p (Finset.mem_insert_of_mem hp))
        (fun p hp => h p (Finset.mem_insert_of_mem hp))
    have hfB0 : 0 ≤ ∏ x ∈ s, f x := le_trans hB0 hB
    nlinarith

private lemma cN_two (N : ℕ) (hEven : Even N) : (ramanujan 2 (N : ℤ)).re = 1 := by
  rw [cN_prime N 2 Nat.prime_two, if_pos (even_iff_two_dvd.mp hEven)]
  norm_num

private lemma local_factor_ge (N p : ℕ) (hp : p.Prime) (hne : p ≠ 2) :
    (1 : ℝ) - 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2 := by
  have hp3 : (3 : ℝ) ≤ (p : ℝ) := by
    have h2 : 2 ≤ p := hp.two_le
    have h3 : 3 ≤ p := by omega
    exact_mod_cast h3
  have hden : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by nlinarith
  have hge : -1 ≤ (ramanujan p (N : ℤ)).re := by
    rw [cN_prime N p hp]
    split_ifs with h
    · linarith
    · norm_num
  have key := div_le_div_of_nonneg_right hge hden.le
  have e : (-1 : ℝ) / ((p : ℝ) - 1) ^ 2 = -(1 / ((p : ℝ) - 1) ^ 2) := by ring
  rw [e] at key
  linarith

private lemma half_le_prod_odd {n : ℕ} :
    (1 / 2 : ℝ) ≤ ∏ p ∈ (n.primesBelow).erase 2, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  rcases Nat.lt_or_ge n 3 with hn | hn
  · have hempty : (n.primesBelow).erase 2 = ∅ := by
      ext p
      constructor
      · intro hp
        exfalso
        obtain ⟨hne, hp'⟩ := Finset.mem_erase.mp hp
        have hlt : p < n := (Nat.mem_primesBelow.mp hp').1
        have h2 : 2 ≤ p := (Nat.mem_primesBelow.mp hp').2.two_le
        omega
      · intro hp
        exact absurd hp (by simp)
    rw [hempty, Finset.prod_empty]
    norm_num
  · have hprime : ∀ p ∈ (n.primesBelow).erase 2, Nat.Prime p := fun p hp =>
      (Nat.mem_primesBelow.mp (Finset.mem_of_mem_erase hp)).2
    have h3le : ∀ p ∈ (n.primesBelow).erase 2, 3 ≤ p := by
      intro p hp
      have h2 : 2 ≤ p := (hprime p hp).two_le
      have hne : p ≠ 2 := Finset.ne_of_mem_erase hp
      omega
    have hinj : Set.InjOn (fun (p : ℕ) => p - 1) ↑((n.primesBelow).erase 2) := by
      intro a ha b hb h
      have ha3 : 3 ≤ a := h3le a ha
      have hb3 : 3 ≤ b := h3le b hb
      simp only at h
      omega
    have hprod : ∏ p ∈ (n.primesBelow).erase 2, (1 - 1 / ((p : ℝ) - 1) ^ 2)
        = ∏ a ∈ ((n.primesBelow).erase 2).image (fun (p : ℕ) => p - 1),
            (1 - 1 / ((a : ℝ)) ^ 2) := by
      rw [Finset.prod_image (g := fun (p : ℕ) => p - 1)
        (f := fun a : ℕ => 1 - 1 / ((a : ℝ)) ^ 2) hinj]
      refine Finset.prod_congr rfl (fun p hp => ?_)
      have hp1 : 1 ≤ p := by have := h3le p hp; omega
      rw [Nat.cast_sub hp1]
      norm_num
    rw [hprod]
    have hsub : ((n.primesBelow).erase 2).image (fun (p : ℕ) => p - 1) ⊆ Finset.Icc 2 n := by
      intro a ha
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
      have hlt : p < n := (Nat.mem_primesBelow.mp (Finset.mem_of_mem_erase hp)).1
      have h3 := h3le p hp
      simp only [Finset.mem_Icc]
      omega
    set U : Finset ℕ := ((n.primesBelow).erase 2).image (fun (p : ℕ) => p - 1) with hU
    have h0I : ∀ a ∈ Finset.Icc 2 n, (0 : ℝ) ≤ 1 - 1 / ((a : ℝ)) ^ 2 := by
      intro a ha
      have ha2 : (2 : ℝ) ≤ (a : ℝ) := by
        have : 2 ≤ a := (Finset.mem_Icc.mp ha).1
        exact_mod_cast this
      have h4 : (1 : ℝ) ≤ (a : ℝ) ^ 2 := by nlinarith [ha2]
      have h5 : 1 / ((a : ℝ)) ^ 2 ≤ 1 := by
        rw [div_le_one (by positivity)]
        exact h4
      rw [sub_nonneg]
      exact h5
    have h1I : ∀ a ∈ Finset.Icc 2 n, (1 - 1 / ((a : ℝ)) ^ 2) ≤ 1 := by
      intro a ha
      have h : (0 : ℝ) ≤ 1 / ((a : ℝ)) ^ 2 := by positivity
      linarith
    have hfill : ∏ a ∈ Finset.Icc 2 n \ U, (1 - 1 / ((a : ℝ)) ^ 2) ≤ 1 := by
      refine prod_le_one_of_le_one (fun a ha => ?_) (fun a ha => ?_)
      · exact h0I a (Finset.mem_sdiff.mp ha).1
      · exact h1I a (Finset.mem_sdiff.mp ha).1
    have hUprod0 : (0 : ℝ) ≤ ∏ a ∈ U, (1 - 1 / ((a : ℝ)) ^ 2) :=
      Finset.prod_nonneg (fun a ha => h0I a (hsub ha))
    have hle : ∏ a ∈ Finset.Icc 2 n, (1 - 1 / ((a : ℝ)) ^ 2)
        ≤ ∏ a ∈ U, (1 - 1 / ((a : ℝ)) ^ 2) := by
      rw [← Finset.prod_sdiff hsub]
      have h := mul_le_mul_of_nonneg_right hfill hUprod0
      linarith [h]
    calc (1 / 2 : ℝ) ≤ ∏ a ∈ Finset.Icc 2 n, (1 - 1 / ((a : ℝ)) ^ 2) :=
          half_le_prod_one_sub_inv_sq (M := n) (by omega)
      _ ≤ ∏ a ∈ U, (1 - 1 / ((a : ℝ)) ^ 2) := hle

private lemma one_le_prod_local (N n : ℕ) (hEven : Even N) :
    (1 : ℝ) ≤ ∏ p ∈ n.primesBelow, (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2) := by
  rcases Nat.lt_or_ge n 3 with hn | hn
  · apply one_le_prod_of_one_le
    intro p hp
    have hp' := Nat.mem_primesBelow.mp hp
    have h2 : 2 ≤ p := hp'.2.two_le
    have h3 : p < n := hp'.1
    have hp2 : p = 2 := by omega
    rw [hp2, cN_two N hEven]
    norm_num
  · have h2mem : (2 : ℕ) ∈ n.primesBelow := by
      rw [Nat.mem_primesBelow]
      exact ⟨by omega, Nat.prime_two⟩
    rw [← Finset.mul_prod_erase n.primesBelow (fun p => 1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2) h2mem]
    have h2val : (1 + (ramanujan 2 (N : ℤ)).re / ((↑(2 : ℕ) : ℝ) - 1) ^ 2) = 2 := by
      rw [cN_two N hEven]; norm_num
    rw [h2val]
    have hodd : (1 / 2 : ℝ) ≤ ∏ p ∈ (n.primesBelow).erase 2,
        (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2) := by
      refine le_trans (half_le_prod_odd (n := n)) ?_
      refine prod_le_prod' (fun p hp => ?_) (fun p hp => ?_)
      · have h3 : 3 ≤ p := by
          have h2 : 2 ≤ p := (Nat.mem_primesBelow.mp (Finset.mem_of_mem_erase hp)).2.two_le
          have hne : p ≠ 2 := Finset.ne_of_mem_erase hp
          omega
        have : (3 : ℝ) ≤ (p : ℝ) := by exact_mod_cast h3
        have : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by nlinarith
        have : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
          rw [div_le_one (by positivity)]
          nlinarith
        linarith
      · exact local_factor_ge N p (Nat.mem_primesBelow.mp (Finset.mem_of_mem_erase hp)).2
          (Finset.ne_of_mem_erase hp)
    linarith

private lemma one_le_singular (N : ℕ) (hN : 1 ≤ N) (hEven : Even N) : 1 ≤ singular N := by
  have hlim := eulerProduct_singTerm N hN
  have hfac : ∀ n : ℕ, (1 : ℝ) ≤ ∏ p ∈ n.primesBelow, (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2) :=
    fun n => one_le_prod_local N n hEven
  have h1 : (1 : ℝ) ≤ ∑' q : ℕ, ((moebius q : ℤ) : ℝ) ^ 2 / (q.totient : ℝ) ^ 2 * (ramanujan q (N : ℤ)).re :=
    le_of_tendsto_of_tendsto tendsto_const_nhds hlim (Filter.Eventually.of_forall hfac)
  exact h1

/-! ## SINGULAR SERIES DEVELOPMENT END -/

/-! ## LEAF 2: the base case, `genSing chi1 chi1 N = singular N`

Both `tauConj` and `cChi` at the trivial character are computed by summing over the units of
`ZMod Q`; the classical `ramanujan q N` sums over the coprime residues below `q`.  The bridge
`zmod_sum_ite_isUnit` identifies the two, and `ramanujan_eq_complex` (from the carried block)
supplies `c_Q(1) = μ(Q)`. -/

/-- Summing `if IsUnit` over `ZMod Q` is summing over the coprime residues below `Q`. -/
private lemma zmod_sum_ite_isUnit (Q : ℕ) [NeZero Q] (f : ℕ → ℂ) :
    (∑ a : ZMod Q, if IsUnit a then f a.val else 0)
      = ∑ a ∈ (Finset.range Q).filter (fun a => Nat.Coprime a Q), f a := by
  have hA : Finset.univ.image (fun u : (ZMod Q)ˣ => (u : ZMod Q))
      = Finset.univ.filter (fun a : ZMod Q => IsUnit a) := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ u.isUnit, fun ha => ⟨ha.unit, ha.unit_spec⟩⟩
  have hB : Finset.univ.image (fun u : (ZMod Q)ˣ => ((u : ZMod Q)).val)
      = (Finset.range Q).filter (fun a => Nat.Coprime a Q) := by
    ext b
    simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_filter, Finset.mem_range]
    exact ⟨fun ⟨u, hu⟩ => hu ▸ ⟨ZMod.val_lt _, ZMod.val_coe_unit_coprime u⟩,
      fun ⟨hbQ, hbc⟩ => ⟨ZMod.unitOfCoprime b hbc,
        by rw [ZMod.coe_unitOfCoprime, ZMod.val_cast_of_lt hbQ]⟩⟩
  rw [← Finset.sum_filter, ← hA, ← hB]
  rw [Finset.sum_image (g := fun u : (ZMod Q)ˣ => ((u : ZMod Q)).val) (f := fun b : ℕ => f b)
      (fun x _ y _ h => Units.ext (ZMod.val_injective Q h))]
  rw [Finset.sum_image (g := fun u : (ZMod Q)ˣ => (u : ZMod Q)) (f := fun a : ZMod Q => f a.val)
      (fun x _ y _ h => Units.ext h)]

/-- `c_Q(1) = μ(Q)`: the twisted Ramanujan sum at `N = 1` is the Möbius function. -/
private lemma ramanujan_one_eq_moebius (Q : ℕ) (hQ : 0 < Q) :
    (∑ a ∈ (Finset.range Q).filter (fun a => Nat.Coprime a Q), ee ((a : ℝ) / Q))
      = (moebius Q : ℂ) := by
  have h := ramanujan_eq_complex Q (1 : ℤ)
  have hL : ramanujan Q (1 : ℤ)
      = ∑ a ∈ (Finset.range Q).filter (fun a => Nat.Coprime a Q), ee ((a : ℝ) / Q) := by
    rw [ramanujan]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    norm_num
  rw [hL] at h
  have hdiv : (∑ d ∈ Q.divisors, (moebius d : ℂ) *
      (if (((Q / d : ℕ) : ℤ) ∣ (1 : ℤ)) then (((Q / d : ℕ)) : ℂ) else 0))
      = (moebius Q : ℂ) := by
    refine (Finset.sum_eq_single Q ?_ ?_).trans ?_
    · intro d hd hdne
      have hdvd : d ∣ Q := (Nat.mem_divisors.mp hd).1
      have h1 : (Q / d : ℕ) ≠ 1 := by
        intro h1
        exact hdne (by rw [← Nat.mul_div_cancel' hdvd, h1, mul_one])
      have hnd : ¬ ((Q / d : ℕ) : ℤ) ∣ (1 : ℤ) := by
        intro hh
        exact h1 (Nat.dvd_one.mp (by exact_mod_cast hh))
      rw [if_neg hnd, mul_zero]
    · intro hmem
      exact absurd (Nat.mem_divisors.mpr ⟨dvd_refl Q, hQ.ne'⟩) hmem
    · rw [Nat.div_self hQ]
      simp
  rw [hdiv] at h
  exact h

/-- The Gauss sum of the trivial character is `μ(Q)`. -/
private lemma tauConj_one (Q : ℕ) [NeZero Q] :
    tauConj (1 : DirichletCharacter ℂ Q) = (moebius Q : ℂ) := by
  have hQ : 0 < Q := NeZero.pos Q
  have hpt : ∀ a : ZMod Q,
      starRingEnd ℂ ((1 : DirichletCharacter ℂ Q) a) * ee ((a.val : ℝ) / Q)
        = (if IsUnit a then ee ((a.val : ℝ) / Q) else 0) := by
    intro a
    by_cases ha : IsUnit a
    · rw [if_pos ha, MulChar.one_apply ha, map_one, one_mul]
    · rw [if_neg ha]
      have hz : ((1 : DirichletCharacter ℂ Q) a) = 0 := MulChar.map_nonunit _ ha
      rw [hz]
      simp
  rw [tauConj, Finset.sum_congr rfl (fun a _ => hpt a),
    zmod_sum_ite_isUnit (Q := Q) (f := fun n => ee ((n : ℝ) / Q))]
  exact ramanujan_one_eq_moebius Q hQ

/-- The twisted Ramanujan sum of the trivial character is `c_Q(N)`. -/
private lemma cChi_one (Q : ℕ) [NeZero Q] (N : ℤ) :
    cChi (1 : DirichletCharacter ℂ Q) N = ramanujan Q N := by
  have hpt : ∀ a : ZMod Q,
      (1 : DirichletCharacter ℂ Q) a * ee ((a.val : ℝ) * N / Q)
        = (if IsUnit a then ee ((a.val : ℝ) * N / Q) else 0) := by
    intro a
    by_cases ha : IsUnit a
    · rw [if_pos ha, MulChar.one_apply ha, one_mul]
    · rw [if_neg ha, MulChar.map_nonunit _ ha, zero_mul]
  rw [cChi, ramanujan, Finset.sum_congr rfl (fun a _ => hpt a),
    zmod_sum_ite_isUnit (Q := Q) (f := fun n => ee ((n : ℝ) * N / Q))]

/-- The modulus-`Q` term at the pair of trivial characters is `μ(Q)^2 c_Q(N) / φ(Q)^2`. -/
private lemma Aq_chi1_chi1 (N : ℤ) (Q : ℕ) [NeZero Q] :
    Aq chi1 chi1 N Q = (moebius Q : ℂ) ^ 2 * ramanujan Q N / (Nat.totient Q : ℂ) ^ 2 := by
  rw [Aq]
  split_ifs with h
  · simp only [chi1, DirichletCharacter.changeLevel_one, one_mul]
    rw [tauConj_one, cChi_one]
    ring
  · exact absurd ⟨one_dvd Q, one_dvd Q⟩ h

/-- The Ramanujan sum is real. -/
private lemma ramanujan_im_zero (N q : ℕ) : (ramanujan q (N : ℤ)).im = 0 := by
  rw [ramanujan_eq_real, Complex.im_sum]
  refine Finset.sum_eq_zero (fun d _ => ?_)
  by_cases h : (q / d : ℕ) ∣ N
  · rw [if_pos h, ← Complex.ofReal_mul, Complex.ofReal_im]
  · rw [if_neg h]
    simp

/-- Hence it is the image of its real part. -/
private lemma ramanujan_eq_re (N q : ℕ) :
    ramanujan q (N : ℤ) = ((ramanujan q (N : ℤ)).re : ℂ) := by
  refine Complex.ext ?_ ?_
  · simp
  · simp [ramanujan_im_zero]

/-- The complex term of the generalised series is the image of the real term of `𝔖`. -/
private lemma complex_term_eq (N Q : ℕ) :
    (moebius Q : ℂ) ^ 2 * ramanujan Q (N : ℤ) / (Nat.totient Q : ℂ) ^ 2
      = ((((moebius Q : ℤ) : ℝ) ^ 2 / (Nat.totient Q : ℝ) ^ 2
          * (ramanujan Q (N : ℤ)).re : ℝ) : ℂ) := by
  rw [ramanujan_eq_re N Q]
  push_cast
  simp only [Complex.ofReal_re]
  ring

/-- Summability of the complex terms, from the carried real summability bound. -/
private lemma summable_complex_term (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun Q : ℕ =>
      (moebius Q : ℂ) ^ 2 * ramanujan Q (N : ℤ) / (Nat.totient Q : ℂ) ^ 2) := by
  refine Summable.of_norm ?_
  have hfun : (fun Q : ℕ => ‖(moebius Q : ℂ) ^ 2 * ramanujan Q (N : ℤ)
        / (Nat.totient Q : ℂ) ^ 2‖)
      = (fun Q : ℕ => ‖((moebius Q : ℤ) : ℝ) ^ 2 / (Nat.totient Q : ℝ) ^ 2
          * (ramanujan Q (N : ℤ)).re‖) := by
    funext Q
    rw [complex_term_eq N Q, Complex.norm_real]
  rw [hfun]
  exact (summable_singTerm N hN).norm


/-- LEAF. Step 1, the size of the ordinary series: for an even `N` at least two the singular
series `𝔖(N)` is nonnegative, so its image in `ℂ` has modulus `𝔖(N)` itself. This is what
turns the two sides of the first formula of 8.1 into the same shape, one written with the
series and one with its modulus. -/
theorem facts81_pos (N : ℕ) (hEven : Even N) (hN : 2 ≤ N) : 0 ≤ singular N := by
  have h1 : (1 : ℝ) ≤ singular N := one_le_singular N (by omega) hEven
  linarith

/-- LEAF. Step 2, the base case of the generalised series: with both characters trivial of
conductor one, the sum of `Aq` over the moduli is the ordinary singular series. Every modulus
`q + 1` is a multiple of both conductors, the two Gauss factors contribute `μ(q)²`, and the
character sum of the principal character is the Ramanujan sum at `q`, so the two series
coincide as real numbers, and the generalised one is its image in `ℂ`. -/
theorem facts81_base (N : ℕ) (hEven : Even N) (hN : 2 ≤ N) :
    genSing chi1 chi1 N = ((singular N : ℝ) : ℂ) := by
  have hN1 : 1 ≤ N := by omega
  have hs : Summable (fun Q : ℕ =>
      (moebius Q : ℂ) ^ 2 * ramanujan Q (N : ℤ) / (Nat.totient Q : ℂ) ^ 2) :=
    summable_complex_term N hN1
  rw [genSing, singular, tsum_congr (fun q : ℕ => Aq_chi1_chi1 (N : ℤ) (q + 1))]
  have hshift : (∑' q : ℕ, (moebius (q + 1) : ℂ) ^ 2 * ramanujan (q + 1) (N : ℤ)
        / (Nat.totient (q + 1) : ℂ) ^ 2)
      = ∑' Q : ℕ, (moebius Q : ℂ) ^ 2 * ramanujan Q (N : ℤ) / (Nat.totient Q : ℂ) ^ 2 := by
    have h := hs.sum_add_tsum_nat_add 1
    have h0 : (∑ i ∈ Finset.range 1,
        (moebius i : ℂ) ^ 2 * ramanujan i (N : ℤ) / (Nat.totient i : ℂ) ^ 2) = 0 := by
      rw [Finset.sum_range_one]
      simp
    rw [h0, zero_add] at h
    exact h
  rw [hshift]
  have hfun : (fun Q : ℕ => (moebius Q : ℂ) ^ 2 * ramanujan Q (N : ℤ) / (Nat.totient Q : ℂ) ^ 2)
      = (fun Q : ℕ => ((((moebius Q : ℤ) : ℝ) ^ 2 / (Nat.totient Q : ℝ) ^ 2
          * (ramanujan Q (N : ℤ)).re : ℝ) : ℂ)) := funext (complex_term_eq N)
  rw [hfun, Complex.ofReal_tsum]

/-! ## Development for `facts81_saving` and `facts81_diag`

Both open leaves are statements about the generalised series at a primitive real character.
The development below isolates what they need from the character side: a real character is
quadratic, `ZMod N` summation is invariant under negation, and the Gauss sum of a primitive
character has square `χ(-1)·N` also over a composite modulus, where `Mathlib`'s
`gaussSum_sq` (which needs a field) does not apply. -/

/-- Invariance of a sum over `ZMod N` under negation. -/
private lemma f81_sum_neg {N : ℕ} [NeZero N] (f : ZMod N → ℂ) : ∑ k : ZMod N, f (-k) = ∑ k : ZMod N, f k :=
  Fintype.sum_equiv (Equiv.neg _) _ _ fun _ => rfl

/-- The double discrete Fourier transform of a function on `ZMod N`. -/
private lemma f81_dft_dft {N : ℕ} [NeZero N] (Φ : ZMod N → ℂ) (j : ZMod N) :
    ZMod.dft (ZMod.dft Φ) j = (N : ℂ) * Φ (-j) := by
  have h := congrFun (ZMod.dft_dft Φ) j
  simpa [smul_eq_mul] using h

/-- A real Dirichlet character takes the values `±1` on units. -/
private lemma f81_unit_sq {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r} (hreal : IsRealChar χ)
    (u : (ZMod r)ˣ) : χ (u : ZMod r) = 1 ∨ χ (u : ZMod r) = -1 := by
  have h1 : ‖χ ((u : ZMod r))‖ = 1 := DirichletCharacter.unit_norm_eq_one (χ := χ) u
  have h2 : (χ ((u : ZMod r))).im = 0 := hreal _
  have hns : Complex.normSq (χ ((u : ZMod r))) = 1 := by
    rw [Complex.normSq_eq_norm_sq, h1]
    norm_num
  have hexp : Complex.normSq (χ ((u : ZMod r))) = (χ ((u : ZMod r))).re ^ 2 := by
    rw [Complex.normSq_apply, h2]
    ring
  have hre : (χ ((u : ZMod r))).re ^ 2 = 1 := by rw [← hexp, hns]
  have hz : χ ((u : ZMod r)) = (((χ ((u : ZMod r))).re : ℝ) : ℂ) := by
    refine Complex.ext ?_ ?_
    · simp
    · simpa [h2] using (Complex.ofReal_im ((χ ((u : ZMod r))).re)).symm
  rcases sq_eq_one_iff.mp hre with h | h
  · exact Or.inl (by rw [hz, h]; norm_num)
  · exact Or.inr (by rw [hz, h]; norm_num)

/-- A real Dirichlet character is quadratic. -/
private lemma f81_chi_mul_self {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r}
    (hreal : IsRealChar χ) : χ * χ = 1 := by
  apply MulChar.ext
  intro u
  rw [MulChar.mul_apply, MulChar.one_apply_coe]
  rcases f81_unit_sq hreal u with h | h <;> rw [h] <;> norm_num

/-- A real Dirichlet character is its own inverse. -/
private lemma f81_inv_eq_self {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r}
    (hreal : IsRealChar χ) : χ⁻¹ = χ :=
  inv_eq_of_mul_eq_one_right (f81_chi_mul_self hreal)

/-- The integer-frequency twisted sum is a shifted standard Gauss sum. -/
private lemma f81_cChi_int_gauss {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (N : ℤ) :
    cChi χ N = gaussSum χ ((ZMod.stdAddChar (N := q)).mulShift (N : ZMod q)) := by
  unfold cChi gaussSum
  apply Finset.sum_congr rfl
  intro a ha
  congr 1
  rw [AddChar.mulShift_apply]
  have he : (N : ZMod q) * a = ((N * (a.val : ℤ) : ℤ) : ZMod q) := by simp
  rw [he, ZMod.stdAddChar_coe]
  unfold ee
  congr 1
  push_cast
  ring

/-- A conjugate Gauss sum is the inverse character's twisted sum at frequency one. -/
private lemma f81_tauConj_eq {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    tauConj χ = cChi χ⁻¹ 1 := by
  unfold tauConj cChi
  apply Finset.sum_congr rfl
  intro a ha
  rw [show (starRingEnd ℂ) (χ a) = star (χ a) from rfl, MulChar.star_apply']
  simp

/-- The conjugate Gauss sum is the standard Gauss sum of the inverse character. -/
private lemma f81_tauConj_gaussSum {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) :
    tauConj χ = gaussSum χ⁻¹ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) := by
  rw [f81_tauConj_eq, f81_cChi_int_gauss, Int.cast_one, AddChar.mulShift_one]

/-- The double transform of a primitive character and the two Gauss sums. -/
private lemma f81_mul_gaussSum_mulShift {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) (j : ZMod N) :
    (N : ℂ) * χ (-j) = gaussSum χ (ZMod.stdAddChar : AddChar (ZMod N) ℂ) *
      gaussSum χ⁻¹ ((ZMod.stdAddChar : AddChar (ZMod N) ℂ).mulShift j) := by
  classical
  rw [← f81_dft_dft, ZMod.dft_apply]
  have hterm : ∀ k : ZMod N,
      ZMod.stdAddChar (-(k * j)) * ZMod.dft (χ : ZMod N → ℂ) k =
        gaussSum χ (ZMod.stdAddChar : AddChar (ZMod N) ℂ) *
          (χ⁻¹ (-k) * ZMod.stdAddChar (-(k * j))) := by
    intro k
    rw [hχ.fourierTransform_eq_inv_mul_gaussSum]
    ring
  have hstep : ∑ k : ZMod N, (χ⁻¹ (-k) * ZMod.stdAddChar (-(k * j)))
      = ∑ k : ZMod N, (χ⁻¹ k * ZMod.stdAddChar (k * j)) := by
    have e1 : ∑ k : ZMod N, (χ⁻¹ (-k) * ZMod.stdAddChar (-(k * j)))
        = ∑ k : ZMod N, (χ⁻¹ (-k) * ZMod.stdAddChar ((-k) * j)) :=
      Finset.sum_congr rfl fun k _ => by rw [neg_mul]
    rw [e1, f81_sum_neg (fun k : ZMod N => χ⁻¹ k * ZMod.stdAddChar (k * j))]
  calc ∑ k : ZMod N, ZMod.stdAddChar (-(k * j)) * ZMod.dft (χ : ZMod N → ℂ) k
      = ∑ k : ZMod N, gaussSum χ (ZMod.stdAddChar : AddChar (ZMod N) ℂ) *
          (χ⁻¹ (-k) * ZMod.stdAddChar (-(k * j))) := Finset.sum_congr rfl fun k _ => hterm k
    _ = gaussSum χ (ZMod.stdAddChar : AddChar (ZMod N) ℂ) *
          ∑ k : ZMod N, (χ⁻¹ (-k) * ZMod.stdAddChar (-(k * j))) := by
        rw [Finset.mul_sum]
    _ = gaussSum χ (ZMod.stdAddChar : AddChar (ZMod N) ℂ) *
          ∑ k : ZMod N, (χ⁻¹ k * ZMod.stdAddChar (k * j)) := by rw [hstep]
    _ = gaussSum χ (ZMod.stdAddChar : AddChar (ZMod N) ℂ) *
          gaussSum χ⁻¹ ((ZMod.stdAddChar : AddChar (ZMod N) ℂ).mulShift j) := by
        rw [gaussSum]
        congr 1
        exact Finset.sum_congr rfl fun k _ => by rw [AddChar.mulShift_apply, mul_comm j k]

/-- A primitive Gauss sum over the composite modulus `ZMod N` has modulus `√N`. -/
private lemma f81_gaussSum_norm_sq {N : ℕ} [NeZero N] {χ : DirichletCharacter ℂ N}
    (hχ : χ.IsPrimitive) :
    ‖gaussSum χ (ZMod.stdAddChar : AddChar (ZMod N) ℂ)‖ ^ 2 = (N : ℝ) := by
  set τ := gaussSum χ (ZMod.stdAddChar : AddChar (ZMod N) ℂ) with hτ
  have h := f81_mul_gaussSum_mulShift (N := N) hχ (-1 : ZMod N)
  rw [neg_neg, map_one, mul_one] at h
  have hconj : (starRingEnd ℂ) τ = gaussSum χ⁻¹
      ((ZMod.stdAddChar : AddChar (ZMod N) ℂ).mulShift (-1)) := by
    rw [hτ]
    exact (star_gaussSum_eq χ (ZMod.stdAddChar : AddChar (ZMod N) ℂ)).trans (by
      rw [AddChar.inv_mulShift])
  have hN : τ * (starRingEnd ℂ) τ = (N : ℂ) := by
    rw [hconj]
    exact h.symm
  have h1 : (‖τ‖ : ℂ) ^ 2 = (N : ℂ) := (Complex.mul_conj' τ).symm.trans hN
  have h2 : ‖τ‖ ^ 2 = (N : ℝ) := by
    have hpoly : ((‖τ‖ : ℂ) ^ 2).re = ‖τ‖ ^ 2 := by
      simp only [pow_two, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    have hthis := congrArg Complex.re h1
    rw [hpoly] at hthis
    simpa using hthis
  exact h2

/-- The Gauss sum of a real character at frequency `-1` is `χ(-1)` times the Gauss sum. -/
private lemma f81_gaussSum_neg {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}
    (hreal : IsRealChar χ) :
    gaussSum χ ((ZMod.stdAddChar : AddChar (ZMod q) ℂ).mulShift (-1)) =
      χ (-1) * gaussSum χ (ZMod.stdAddChar : AddChar (ZMod q) ℂ) := by
  have hstep : gaussSum χ ((ZMod.stdAddChar : AddChar (ZMod q) ℂ).mulShift (-1))
      = ∑ a : ZMod q, χ (-a) * ZMod.stdAddChar a := by
    rw [gaussSum]
    simp only [AddChar.mulShift_apply]
    rw [← f81_sum_neg (fun a : ZMod q => χ a * ZMod.stdAddChar ((-1) * a))]
    exact Finset.sum_congr rfl (fun a _ => by simp)
  rw [hstep, gaussSum, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [show (-a : ZMod q) = (-1) * a by ring, map_mul χ]
  ring

/-- A real character squares to the trivial character at `-1`. -/
private lemma f81_neg_one_sq {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q} :
    χ (-1) * χ (-1) = 1 := by
  rw [← map_mul χ, neg_one_mul, neg_neg, map_one χ]

/-- The Gauss sum of a primitive real character over its own modulus squares to `χ(-1)·r`. -/
private lemma f81_tauConj_sq {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r}
    (hreal : IsRealChar χ) (hprim : χ.IsPrimitive) :
    tauConj χ * tauConj χ = χ (-1) * (r : ℂ) := by
  set τ := gaussSum χ (ZMod.stdAddChar : AddChar (ZMod r) ℂ) with hτ
  have hT : tauConj χ = τ := by
    rw [f81_tauConj_gaussSum, f81_inv_eq_self hreal]
  have hnorm := f81_gaussSum_norm_sq (N := r) hprim
  have hconj : (starRingEnd ℂ) τ = χ (-1) * τ := by
    rw [hτ]
    exact (star_gaussSum_eq χ (ZMod.stdAddChar : AddChar (ZMod r) ℂ)).trans (by
      rw [AddChar.inv_mulShift, f81_inv_eq_self hreal, f81_gaussSum_neg hreal])
  have hprod : τ * (starRingEnd ℂ) τ = (r : ℂ) := by
    have h1 : τ * (starRingEnd ℂ) τ = ((‖τ‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
    rw [h1, hnorm]
    push_cast
    ring
  have h2 : τ * τ = χ (-1) * (r : ℂ) := by
    have h3 : χ (-1) * (τ * τ) = (r : ℂ) := by
      rw [← hprod, hconj]
      ring
    have h4 := congrArg (fun z => χ (-1) * z) h3
    rw [← mul_assoc, f81_neg_one_sq, one_mul] at h4
    exact h4
  rw [hT, h2]

/-- The exponential at zero is one. -/
private lemma f81_ee_zero : ee (0 : ℝ) = 1 := by
  unfold ee
  simp

/-- The Ramanujan sum at a modulus dividing `N` is the totient. -/
private lemma f81_ram_totient {r N : ℕ} (hd : r ∣ N) :
    ramanujan r (N : ℤ) = (Nat.totient r : ℂ) := by
  obtain ⟨k, rfl⟩ := hd
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    simp [ramanujan]
  have hcard : (((Finset.range r).filter (fun a => Nat.Coprime a r)).card : ℂ)
      = (Nat.totient r : ℂ) := by
    rw [Nat.totient_eq_card_coprime]
    congr 1
    exact congrArg Finset.card (Finset.filter_congr (fun a _ => Nat.coprime_comm))
  have hterm : ∀ a ∈ (Finset.range r).filter (fun a => Nat.Coprime a r),
      ee (((a : ℝ) * (((r * k : ℕ) : ℤ))) / (r)) = 1 := by
    intro a ha
    have harg : ((a : ℝ) * ((((r * k : ℕ)) : ℤ))) / (r) = (((a * k : ℕ)) : ℝ) := by
      push_cast
      field_simp
    rw [harg]
    simpa using ee_int_cast ((a * k : ℕ) : ℤ)
  unfold ramanujan
  rw [Finset.sum_congr rfl hterm]
  simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
  exact hcard

/-- The generalised series term of the pair `(χ, χ)` at the source modulus `r`. -/
private lemma f81_Aq_self {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (hreal : IsRealChar χ) (N : ℤ) :
    Aq χ χ N r = tauConj χ * tauConj χ * ramanujan r N / (Nat.totient r : ℂ) ^ 2 := by
  rw [Aq, dif_pos (show r ∣ r ∧ r ∣ r from ⟨dvd_refl r, dvd_refl r⟩),
    DirichletCharacter.changeLevel_self, f81_chi_mul_self hreal, cChi_one]

/-- Lifting a real character keeps it real. -/
private lemma f81_real_lift {r q : ℕ} [NeZero r] [NeZero q] {χ : DirichletCharacter ℂ r}
    (hreal : IsRealChar χ) (hd : r ∣ q) : IsRealChar (DirichletCharacter.changeLevel hd χ) := by
  intro a
  by_cases ha : IsUnit a
  · rw [← ha.unit_spec, DirichletCharacter.changeLevel_eq_cast_of_dvd]
    exact hreal _
  · rw [MulChar.map_nonunit _ ha]
    simp

/-- The standard additive character of `ZMod q` is not one at the complement of a prime factor. -/
private lemma f81_stdAddChar_ne_one {q p : ℕ} [NeZero q] (hp : p.Prime) (hpq : p ∣ q) :
    (ZMod.stdAddChar (N := q)) (((q / p : ℕ)) : ZMod q) ≠ 1 := by
  intro h
  have h0 : (ZMod.stdAddChar (N := q)) ((0 : ℕ) : ZMod q) = 1 := by
    simp
  have heq : (((q / p : ℕ)) : ZMod q) = ((0 : ℕ) : ZMod q) := by
    apply ZMod.injective_stdAddChar (N := q)
    rw [h, h0]
  have heq' : (((q / p : ℕ)) : ZMod q) = 0 := by simpa using heq
  rw [ZMod.natCast_eq_zero_iff] at heq'
  have hqpos : 0 < q := Nat.pos_of_ne_zero (NeZero.ne q)
  have hpos : 0 < q / p := Nat.div_pos (Nat.le_of_dvd hqpos hpq) hp.pos
  have hlt : q / p < q := Nat.div_lt_self hqpos hp.one_lt
  exact absurd (Nat.le_of_dvd hpos heq') (by omega)

/-- A square-zero shift carries units to units. -/
private lemma f81_isUnit_add_of_sq_zero {q : ℕ} [NeZero q] {d : ZMod q} (hd : d * d = 0)
    {a : ZMod q} (ha : IsUnit a) : IsUnit (a + d) := by
  obtain ⟨u, rfl⟩ := ha
  have hfac : ((u : ZMod q) + d) = (u : ZMod q) * (1 + (↑u⁻¹ : ZMod q) * d) := by
    calc (u : ZMod q) + d = (u : ZMod q) * 1 + (u : ZMod q) * ((↑u⁻¹ : ZMod q) * d) := by
          rw [mul_one, ← mul_assoc, Units.mul_inv, one_mul]
      _ = (u : ZMod q) * (1 + (↑u⁻¹ : ZMod q) * d) := by rw [mul_add]
  rw [hfac]
  have hy : ((↑u⁻¹ : ZMod q) * d) * ((↑u⁻¹ : ZMod q) * d) = 0 := by
    rw [mul_mul_mul_comm, hd, mul_zero]
  refine IsUnit.mul (Units.isUnit u) ⟨⟨1 + (↑u⁻¹ : ZMod q) * d,
    1 - (↑u⁻¹ : ZMod q) * d, ?_, ?_⟩, rfl⟩
  · have h : (1 + (↑u⁻¹ : ZMod q) * d) * (1 - (↑u⁻¹ : ZMod q) * d)
        = 1 - ((↑u⁻¹ : ZMod q) * d) * ((↑u⁻¹ : ZMod q) * d) := by ring
    rw [h, hy, sub_zero]
  · have h : (1 - (↑u⁻¹ : ZMod q) * d) * (1 + (↑u⁻¹ : ZMod q) * d)
        = 1 - ((↑u⁻¹ : ZMod q) * d) * ((↑u⁻¹ : ZMod q) * d) := by ring
    rw [h, hy, sub_zero]

/-- A lifted character is invariant under translation by a square-zero multiple of its level. -/
private lemma f81_lift_translate {r q : ℕ} [NeZero r] [NeZero q] (χ : DirichletCharacter ℂ r)
    (hd : r ∣ q) {d : ℕ} (hrd : r ∣ d)
    (hd2 : (((d : ℕ)) : ZMod q) * (((d : ℕ)) : ZMod q) = 0) (a : ZMod q) :
    DirichletCharacter.changeLevel hd χ (a + ((d : ℕ) : ZMod q))
      = DirichletCharacter.changeLevel hd χ a := by
  have hcast : (ZMod.cast (((d : ℕ)) : ZMod q) : ZMod r) = 0 := by
    rw [ZMod.cast_natCast hd d, ZMod.natCast_eq_zero_iff]
    exact hrd
  by_cases ha : IsUnit a
  · have ha' : IsUnit (a + ((d : ℕ) : ZMod q)) := f81_isUnit_add_of_sq_zero hd2 ha
    calc DirichletCharacter.changeLevel hd χ (a + ((d : ℕ) : ZMod q))
        = DirichletCharacter.changeLevel hd χ (↑ha'.unit : ZMod q) :=
          congrArg (DirichletCharacter.changeLevel hd χ) ha'.unit_spec.symm
      _ = χ (ZMod.cast (↑ha'.unit : ZMod q)) :=
          DirichletCharacter.changeLevel_eq_cast_of_dvd χ hd ha'.unit
      _ = χ (ZMod.cast (a + ((d : ℕ) : ZMod q))) :=
          congrArg (fun z => χ (ZMod.cast z)) ha'.unit_spec
      _ = χ (ZMod.cast a) := by rw [ZMod.cast_add hd, hcast, add_zero]
      _ = DirichletCharacter.changeLevel hd χ a :=
          ((congrArg (DirichletCharacter.changeLevel hd χ) ha.unit_spec.symm).trans
            ((DirichletCharacter.changeLevel_eq_cast_of_dvd χ hd ha.unit).trans
              (congrArg (fun z => χ (ZMod.cast z)) ha.unit_spec))).symm
  · have ha' : ¬ IsUnit (a + ((d : ℕ) : ZMod q)) := by
      intro hh
      have h1 : IsUnit ((a + ((d : ℕ) : ZMod q)) + (-(((d : ℕ)) : ZMod q))) :=
        f81_isUnit_add_of_sq_zero (d := -(((d : ℕ)) : ZMod q)) (by
          rw [neg_mul_neg, hd2]) hh
      exact ha (by simpa using h1)
    rw [MulChar.map_nonunit _ ha', MulChar.map_nonunit _ ha]

/-- The Gauss sum of a lifted real character vanishes when the level exceeds its conductor by a
prime factor: the standard additive character is then not one on the shift `q/p`. -/
private lemma f81_tau_lift_vanish {r q : ℕ} [NeZero r] [NeZero q] (χ : DirichletCharacter ℂ r)
    (hreal : IsRealChar χ) (hd : r ∣ q) {p : ℕ} (hp : p.Prime) (hpr : p ∣ r)
    (hpk : p ∣ q / r) :
    tauConj (DirichletCharacter.changeLevel hd χ) = 0 := by
  classical
  have hpq : p ∣ q := dvd_trans hpr hd
  obtain ⟨r', hr'⟩ := hpr
  obtain ⟨s, hs⟩ := hpk
  have hqr : q = r * (q / r) := (Nat.mul_div_cancel' hd).symm
  have hq : q = p * (p * (r' * s)) := by rw [hqr, hs, hr']; ring
  have hdq : q / p = p * (r' * s) := by rw [hq]; exact Nat.mul_div_cancel_left _ hp.pos
  have hdvd : q ∣ (q / p) * (q / p) := by
    refine ⟨r' * s, ?_⟩
    rw [hdq, hq]; ring
  have hrd : r ∣ q / p := by
    refine ⟨s, ?_⟩
    rw [hdq, hr']; ring
  have hd2 : (((q / p : ℕ)) : ZMod q) * (((q / p : ℕ)) : ZMod q) = 0 := by
    rw [← Nat.cast_mul, ZMod.natCast_eq_zero_iff]
    exact hdvd
  set c : ℂ := (ZMod.stdAddChar (N := q)) (((q / p : ℕ)) : ZMod q) with hc
  set S : ℂ := ∑ a : ZMod q, DirichletCharacter.changeLevel hd χ a
    * (ZMod.stdAddChar : AddChar (ZMod q) ℂ) a with hS
  have hshift : (∑ a : ZMod q, DirichletCharacter.changeLevel hd χ (a + (((q / p : ℕ)) : ZMod q))
      * (ZMod.stdAddChar : AddChar (ZMod q) ℂ) (a + (((q / p : ℕ)) : ZMod q))) = S :=
    Fintype.sum_equiv (Equiv.addLeft (((q / p : ℕ)) : ZMod q))
      (fun x => DirichletCharacter.changeLevel hd χ (x + (((q / p : ℕ)) : ZMod q))
        * (ZMod.stdAddChar : AddChar (ZMod q) ℂ) (x + (((q / p : ℕ)) : ZMod q)))
      (fun y => DirichletCharacter.changeLevel hd χ y
        * (ZMod.stdAddChar : AddChar (ZMod q) ℂ) y)
      (fun x => by rw [show (Equiv.addLeft (((q / p : ℕ)) : ZMod q)) x = (((q / p : ℕ)) : ZMod q) + x from rfl, add_comm])
  have hstep : (∑ a : ZMod q, DirichletCharacter.changeLevel hd χ (a + (((q / p : ℕ)) : ZMod q))
      * (ZMod.stdAddChar : AddChar (ZMod q) ℂ) (a + (((q / p : ℕ)) : ZMod q))) = S * c := by
    rw [hS, Finset.sum_mul]
    refine Finset.sum_congr rfl (fun a _ => ?_)
    rw [f81_lift_translate χ hd hrd hd2 a, AddChar.map_add_eq_mul, hc]
    ring
  have hSe : S = S * c := by rw [← hstep, hshift]
  have hne : c ≠ 1 := by rw [hc]; exact f81_stdAddChar_ne_one hp hpq
  have hz : S = 0 := by
    have h1 : S * (1 - c) = 0 := by
      have h2 : S * (1 - c) = S - S * c := by ring
      rw [h2, ← hSe]
      ring
    rcases mul_eq_zero.mp h1 with h | h
    · exact h
    · exact absurd (by linear_combination -h : c = 1) hne
  rw [f81_tauConj_gaussSum, f81_inv_eq_self (f81_real_lift hreal hd), gaussSum, ← hS]
  exact hz

/-- The standard additive phase splits using integer Bezout coefficients.
This is a derived finite identity and not an extra analytic assumption. -/
private lemma f81_crt_phase {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (A B : ℤ) (hAB : A * m + B * n = 1) (a : ZMod (m * n)) :
    ZMod.stdAddChar a =
      ZMod.stdAddChar ((B : ZMod m) * (ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) a)) *
      ZMod.stdAddChar ((A : ZMod n) * (ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) a)) := by
  have hm : (m : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne m
  have hn : (n : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne n
  have hab : (A : ℂ) / n + (B : ℂ) / m = 1 / ((m : ℂ) * n) := by
    have h : (A : ℂ) * m + (B : ℂ) * n = 1 := by exact_mod_cast hAB
    field_simp
    linear_combination h
  have hc₁ : ZMod.castHom (Nat.dvd_mul_right m n) (ZMod m) a = (a.val : ZMod m) := by
    rw [← ZMod.natCast_zmod_val a]
    simp
  have hc₂ : ZMod.castHom (Nat.dvd_mul_left n m) (ZMod n) a = (a.val : ZMod n) := by
    rw [← ZMod.natCast_zmod_val a]
    simp
  rw [hc₁, hc₂,
    show (B : ZMod m) * (a.val : ZMod m) = ((B * (a.val : ℤ) : ℤ) : ZMod m) by push_cast; rfl,
    show (A : ZMod n) * (a.val : ZMod n) = ((A * (a.val : ℤ) : ℤ) : ZMod n) by push_cast; rfl]
  conv_lhs => rw [← ZMod.natCast_zmod_val a]
  rw [show ((a.val : ℕ) : ZMod (m * n)) = ((a.val : ℤ) : ZMod (m * n)) by simp,
    ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe, ← Complex.exp_add]
  congr 1
  push_cast
  calc
    _ = (2 * (Real.pi : ℂ) * Complex.I * (a.val : ℂ)) *
        ((A : ℂ) / n + (B : ℂ) / m) := by rw [hab]; ring
    _ = _ := by ring

/-- Unit residues split independently under the Chinese remainder equivalence.
 -/
private lemma f81_unit_crt_sum {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcop : m.Coprime n) (F : (ZMod m)ˣ → ℂ) (G : (ZMod n)ˣ → ℂ) :
    (∑ a : (ZMod (m * n))ˣ,
      F (ZMod.unitsMap (Nat.dvd_mul_right m n) a) *
      G (ZMod.unitsMap (Nat.dvd_mul_left n m) a)) =
        (∑ u : (ZMod m)ˣ, F u) * ∑ v : (ZMod n)ˣ, G v := by
  let e := (Units.mapEquiv (ZMod.chineseRemainder hcop).toMulEquiv).trans MulEquiv.prodUnits
  have he (a : (ZMod (m * n))ˣ) : e a =
      (ZMod.unitsMap (Nat.dvd_mul_right m n) a,
        ZMod.unitsMap (Nat.dvd_mul_left n m) a) := by
    apply Prod.ext <;> apply Units.ext
    · change (ZMod.cast (a : ZMod (m * n)) : ZMod m × ZMod n).1 =
        (ZMod.cast (a : ZMod (m * n)) : ZMod m)
      exact Prod.fst_zmod_cast _
    · change (ZMod.cast (a : ZMod (m * n)) : ZMod m × ZMod n).2 =
        (ZMod.cast (a : ZMod (m * n)) : ZMod n)
      exact Prod.snd_zmod_cast _
  calc
    _ = ∑ a : (ZMod (m * n))ˣ, F (e a).1 * G (e a).2 := by simp only [he]
    _ = ∑ uv : (ZMod m)ˣ × (ZMod n)ˣ, F uv.1 * G uv.2 :=
      Equiv.sum_comp e.toEquiv (fun uv : (ZMod m)ˣ × (ZMod n)ˣ => F uv.1 * G uv.2)
    _ = _ := by rw [Fintype.sum_prod_type, Finset.sum_mul]; simp_rw [← Finset.mul_sum]

/-- A Gauss sum can be restricted to unit residues for any additive character.
 -/
private lemma f81_gaussSum_units {q : ℕ} [NeZero q]
    (χ : DirichletCharacter ℂ q) (ψ : AddChar (ZMod q) ℂ) :
    gaussSum χ ψ = ∑ a : (ZMod q)ˣ, χ a * ψ a := by
  classical
  unfold gaussSum
  symm
  apply Fintype.sum_of_injective (fun a : (ZMod q)ˣ => (a : ZMod q))
    Units.val_injective (fun a => χ a * ψ a) (fun a => χ a * ψ a) ?_ (fun _ => rfl)
  intro a ha
  rw [MulChar.map_nonunit χ (fun hu => ha ⟨hu.unit, hu.unit_spec⟩), zero_mul]

/-- The twisted sum of a CRT product factors with the exact Bezout frequency shifts.
Both frequency factors remain explicit. -/
private lemma f81_cChi_crt_shift {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcop : m.Coprime n) (χ : DirichletCharacter ℂ m) (ψ : DirichletCharacter ℂ n)
    (A B : ℤ) (hAB : A * m + B * n = 1) (N : ℤ) :
    cChi (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ *
      DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) ψ) N =
        cChi χ (B * N) * cChi ψ (A * N) := by
  rw [f81_cChi_int_gauss, f81_cChi_int_gauss, f81_cChi_int_gauss,
    f81_gaussSum_units, f81_gaussSum_units, f81_gaussSum_units]
  simp only [AddChar.mulShift_apply, Int.cast_mul]
  have ht (a : (ZMod (m * n))ˣ) :
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ *
          DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) ψ) a *
          ZMod.stdAddChar ((N : ZMod (m * n)) * (a : ZMod (m * n))) =
        (χ (ZMod.unitsMap (Nat.dvd_mul_right m n) a) *
          ZMod.stdAddChar (((B : ZMod m) * (N : ZMod m)) *
            (ZMod.unitsMap (Nat.dvd_mul_right m n) a : ZMod m))) *
        (ψ (ZMod.unitsMap (Nat.dvd_mul_left n m) a) *
          ZMod.stdAddChar (((A : ZMod n) * (N : ZMod n)) *
            (ZMod.unitsMap (Nat.dvd_mul_left n m) a : ZMod n))) := by
    rw [MulChar.mul_apply, DirichletCharacter.changeLevel_eq_cast_of_dvd,
      DirichletCharacter.changeLevel_eq_cast_of_dvd,
      f81_crt_phase A B hAB ((N : ZMod (m * n)) * (a : ZMod (m * n)))]
    simp only [map_mul, map_intCast, ZMod.castHom_apply, ZMod.unitsMap_val, mul_assoc]
    ring
  simp_rw [ht]
  exact f81_unit_crt_sum hcop
    (fun a => χ a * ZMod.stdAddChar (((B : ZMod m) * (N : ZMod m)) * (a : ZMod m)))
    (fun a => ψ a * ZMod.stdAddChar (((A : ZMod n) * (N : ZMod n)) * (a : ZMod n)))

/-- A unit frequency multiplier contributes the inverse character value.
 -/
private lemma f81_cChi_mul_unit {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q)
    (M N : ℤ) (hM : IsUnit (M : ZMod q)) :
    cChi χ (M * N) = χ⁻¹ (M : ZMod q) * cChi χ N := by
  rw [f81_cChi_int_gauss, f81_cChi_int_gauss]
  have he : (ZMod.stdAddChar (N := q)).mulShift ((M * N : ℤ) : ZMod q) =
      ((ZMod.stdAddChar (N := q)).mulShift (N : ZMod q)).mulShift hM.unit := by
    ext a
    simp only [AddChar.mulShift_apply, IsUnit.unit_spec, Int.cast_mul]
    congr 1
    ring
  rw [he, gaussSum_mulShift_eq, IsUnit.unit_spec]

/-- The common unit frequency factors cancel across the three coefficient sums.
 -/
private lemma f81_coefficient_phase_cancel {q : ℕ} [NeZero q]
    (χ₁ χ₂ : DirichletCharacter ℂ q) (M N : ℤ) (hM : IsUnit (M : ZMod q)) :
    cChi χ₁⁻¹ M * cChi χ₂⁻¹ M * cChi (χ₁ * χ₂) (M * N) =
      tauConj χ₁ * tauConj χ₂ * cChi (χ₁ * χ₂) N := by
  have h₁ : χ₁ (M : ZMod q) * χ₁⁻¹ (M : ZMod q) = 1 := by
    rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply hM]
  have h₂ : χ₂ (M : ZMod q) * χ₂⁻¹ (M : ZMod q) = 1 := by
    rw [← MulChar.mul_apply, mul_inv_cancel, MulChar.one_apply hM]
  have he₁ := f81_cChi_mul_unit χ₁⁻¹ M 1 hM
  have he₂ := f81_cChi_mul_unit χ₂⁻¹ M 1 hM
  simp only [mul_one, inv_inv] at he₁ he₂
  rw [he₁, he₂, f81_cChi_mul_unit (χ₁ * χ₂) M N hM,
    f81_tauConj_eq, f81_tauConj_eq]
  simp only [mul_inv_rev, MulChar.mul_apply]
  calc
    _ = (χ₁ (M : ZMod q) * χ₁⁻¹ (M : ZMod q)) *
        (χ₂ (M : ZMod q) * χ₂⁻¹ (M : ZMod q)) *
        (cChi χ₁⁻¹ 1 * cChi χ₂⁻¹ 1 * cChi (χ₁ * χ₂) N) := by ring
    _ = _ := by rw [h₁, h₂, one_mul, one_mul]


/-- The three shifted Gauss sums factor with exact cancellation of their common phases.
 -/
private lemma f81_Aq_crt {m n : ℕ} [NeZero m] [NeZero n] [NeZero (m * n)]
    (hcop : m.Coprime n) (χ₁ χ₂ : DirichletCharacter ℂ m)
    (ψ₁ ψ₂ : DirichletCharacter ℂ n) (N : ℤ) :
    Aq (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ₁ *
        DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) ψ₁)
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ₂ *
        DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) ψ₂) N (m * n) =
      Aq χ₁ χ₂ N m * Aq ψ₁ ψ₂ N n := by
  let A := (m : ℤ).gcdA n
  let B := (m : ℤ).gcdB n
  have hAB : A * m + B * n = 1 := by
    have h := Int.gcd_eq_gcd_ab (m : ℤ) (n : ℤ)
    rw [Int.gcd_natCast_natCast, hcop.gcd_eq_one] at h
    dsimp [A, B]
    linear_combination -h
  have hAeq : (A : ZMod n) * (m : ZMod n) = 1 := by
    have h := congrArg (Int.castRingHom (ZMod n)) hAB
    simpa using h
  have hBeq : (B : ZMod m) * (n : ZMod m) = 1 := by
    have h := congrArg (Int.castRingHom (ZMod m)) hAB
    simpa using h
  have hA : IsUnit (A : ZMod n) :=
    ⟨⟨A, m, hAeq, by simpa only [mul_comm] using hAeq⟩, rfl⟩
  have hB : IsUnit (B : ZMod m) :=
    ⟨⟨B, n, hBeq, by simpa only [mul_comm] using hBeq⟩, rfl⟩
  have ht (χ : DirichletCharacter ℂ m) (ψ : DirichletCharacter ℂ n) :
      tauConj (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ *
        DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) ψ) =
        cChi χ⁻¹ B * cChi ψ⁻¹ A := by
    rw [f81_tauConj_eq]
    simpa only [map_inv, mul_inv_rev, mul_one, mul_comm] using
      f81_cChi_crt_shift hcop χ⁻¹ ψ⁻¹ A B hAB 1
  have hprod :
      (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ₁ *
          DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) ψ₁) *
        (DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) χ₂ *
          DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) ψ₂) =
      DirichletCharacter.changeLevel (Nat.dvd_mul_right m n) (χ₁ * χ₂) *
        DirichletCharacter.changeLevel (Nat.dvd_mul_left n m) (ψ₁ * ψ₂) := by
    simp only [map_mul]
    ac_rfl
  have hc := f81_cChi_crt_shift hcop (χ₁ * χ₂) (ψ₁ * ψ₂) A B hAB N
  have hnum :
      (cChi χ₁⁻¹ B * cChi ψ₁⁻¹ A) * (cChi χ₂⁻¹ B * cChi ψ₂⁻¹ A) *
        (cChi (χ₁ * χ₂) (B * N) * cChi (ψ₁ * ψ₂) (A * N)) =
        (tauConj χ₁ * tauConj χ₂ * cChi (χ₁ * χ₂) N) *
          (tauConj ψ₁ * tauConj ψ₂ * cChi (ψ₁ * ψ₂) N) := by
    calc
      _ = (cChi χ₁⁻¹ B * cChi χ₂⁻¹ B * cChi (χ₁ * χ₂) (B * N)) *
          (cChi ψ₁⁻¹ A * cChi ψ₂⁻¹ A * cChi (ψ₁ * ψ₂) (A * N)) := by ring
      _ = _ := by rw [f81_coefficient_phase_cancel χ₁ χ₂ B N hB,
        f81_coefficient_phase_cancel ψ₁ ψ₂ A N hA]
  simp only [Aq, dif_pos (show m * n ∣ m * n ∧ m * n ∣ m * n from ⟨dvd_refl _, dvd_refl _⟩),
    dif_pos (show m ∣ m ∧ m ∣ m from ⟨dvd_refl _, dvd_refl _⟩),
    dif_pos (show n ∣ n ∧ n ∣ n from ⟨dvd_refl _, dvd_refl _⟩),
    DirichletCharacter.changeLevel_self]
  rw [ht, ht, hprod, hc, hnum, Nat.totient_mul hcop, Nat.cast_mul, mul_pow]
  exact mul_div_mul_comm _ _ _ _

/-- The Ramanujan sum is multiplicative in the modulus. -/
private lemma f81_ram_mul (N : ℕ) {m n : ℕ} (h : m.Coprime n) :
    ramanujan (m * n) (N : ℤ) = ramanujan m (N : ℤ) * ramanujan n (N : ℤ) := by
  rw [ramanujan_eq_re (N := N) (q := m * n), cN_mul N h]
  push_cast
  rw [← ramanujan_eq_re (N := N) (q := m), ← ramanujan_eq_re (N := N) (q := n)]

/-- Passing characters to the level `q` does not change their term at level `q`. -/
private lemma f81_Aq_lift_self {r₁ r₂ q : ℕ} [NeZero r₁] [NeZero r₂] [NeZero q]
    (h₁ : r₁ ∣ q) (h₂ : r₂ ∣ q) (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂)
    (N : ℤ) :
    Aq (DirichletCharacter.changeLevel h₁ χ₁) (DirichletCharacter.changeLevel h₂ χ₂) N q
      = Aq χ₁ χ₂ N q := by
  simp only [Aq, dif_pos (show q ∣ q ∧ q ∣ q from ⟨dvd_refl q, dvd_refl q⟩),
    dif_pos (show r₁ ∣ q ∧ r₂ ∣ q from ⟨h₁, h₂⟩), DirichletCharacter.changeLevel_self]

/-- The term of the generalised series factors over a coprime splitting of the modulus. -/
private lemma f81_Aq_mul_coprime {r k : ℕ} [NeZero r] [NeZero k] (hcop : r.Coprime k)
    (χ : DirichletCharacter ℂ r) (N : ℤ) :
    Aq χ χ N (r * k) =
      Aq χ χ N r * Aq (1 : DirichletCharacter ℂ k) (1 : DirichletCharacter ℂ k) N k := by
  haveI : NeZero (r * k) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne k)⟩
  rw [← f81_Aq_lift_self (Nat.dvd_mul_right r k) (Nat.dvd_mul_right r k) χ χ N]
  have h := f81_Aq_crt (m := r) (n := k) hcop χ χ
    (1 : DirichletCharacter ℂ k) (1 : DirichletCharacter ℂ k) N
  have e : DirichletCharacter.changeLevel (Nat.dvd_mul_left k r) (1 : DirichletCharacter ℂ k)
      = 1 := map_one _
  rw [e, mul_one] at h
  exact h

/-- The pair `(chi1, χ)` and the pair of the trivial character of `r` with `χ` agree. -/
private lemma f81_Aq_chi1_eq {r q : ℕ} [NeZero r] [NeZero q] (hd : r ∣ q)
    (χ : DirichletCharacter ℂ r) (N : ℤ) :
    Aq chi1 χ N q = Aq (1 : DirichletCharacter ℂ r) χ N q := by
  rw [Aq, Aq, dif_pos (show 1 ∣ q ∧ r ∣ q from ⟨one_dvd q, hd⟩),
    dif_pos (show r ∣ q ∧ r ∣ q from ⟨hd, hd⟩)]
  simp only [chi1, map_one]

/-- The term of the pair `(chi1, χ)` factors over a coprime splitting of the modulus. -/
private lemma f81_Aq_chi1_mul {r k : ℕ} [NeZero r] [NeZero k] (hcop : r.Coprime k)
    (χ : DirichletCharacter ℂ r) (N : ℤ) :
    Aq chi1 χ N (r * k) =
      Aq chi1 χ N r * Aq (1 : DirichletCharacter ℂ k) (1 : DirichletCharacter ℂ k) N k := by
  haveI : NeZero (r * k) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne k)⟩
  rw [f81_Aq_chi1_eq (Nat.dvd_mul_right r k) χ N,
    ← f81_Aq_lift_self (Nat.dvd_mul_right r k) (Nat.dvd_mul_right r k)
      (1 : DirichletCharacter ℂ r) χ N]
  have h := f81_Aq_crt (m := r) (n := k) hcop (1 : DirichletCharacter ℂ r) χ
    (1 : DirichletCharacter ℂ k) (1 : DirichletCharacter ℂ k) N
  have e1 : DirichletCharacter.changeLevel (Nat.dvd_mul_right r k) (1 : DirichletCharacter ℂ r)
      = 1 := map_one _
  have e2 : DirichletCharacter.changeLevel (Nat.dvd_mul_left k r) (1 : DirichletCharacter ℂ k)
      = 1 := map_one _
  rw [e1, e2] at h
  simp only [one_mul, mul_one] at h
  rw [f81_Aq_chi1_eq (dvd_refl r) χ N, e1]
  exact h

/-- The term of the generalised series at the pair `(chi1, χ)` at the source modulus `r`. -/
private lemma f81_Aq_chi1_chi_self {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (N : ℤ) :
    Aq chi1 χ N r = (ArithmeticFunction.moebius r : ℂ) * tauConj χ * cChi χ N
      / (Nat.totient r : ℂ) ^ 2 := by
  rw [Aq, dif_pos (show 1 ∣ r ∧ r ∣ r from ⟨one_dvd r, dvd_refl r⟩)]
  simp only [chi1, map_one, one_mul, mul_one, DirichletCharacter.changeLevel_self, tauConj_one]

/-- The term vanishes when the modulus exceeds the source level by a non-coprime factor. -/
private lemma f81_Aq_vanish {r Q : ℕ} [NeZero r] [NeZero Q] (χ : DirichletCharacter ℂ r)
    (hreal : IsRealChar χ) (hdvd : r ∣ Q) (hbad : ¬ Nat.Coprime (Q / r) r) (N : ℤ) :
    Aq χ χ N Q = 0 := by
  obtain ⟨p, hp, hpk, hpr⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbad
  have hv := f81_tau_lift_vanish χ hreal hdvd hp hpr hpk
  rw [Aq, dif_pos (show r ∣ Q ∧ r ∣ Q from ⟨hdvd, hdvd⟩), hv]
  simp

/-- The term factors through the source level and a coprime quotient. -/
private lemma f81_Aq_split {r k : ℕ} [NeZero r] [NeZero k] (χ : DirichletCharacter ℂ r)
    (hreal : IsRealChar χ) (N : ℤ) :
    Aq χ χ N (r * k) = if Nat.Coprime k r then
        Aq χ χ N r * Aq (1 : DirichletCharacter ℂ k) (1 : DirichletCharacter ℂ k) N k
      else 0 := by
  by_cases hcop : Nat.Coprime k r
  · rw [if_pos hcop]
    exact f81_Aq_mul_coprime hcop.symm χ N
  · rw [if_neg hcop]
    have hrpos : 0 < r := NeZero.pos r
    have hk : r * k / r = k := by
      refine Nat.mul_left_cancel hrpos ?_
      rw [Nat.mul_div_cancel' (Nat.dvd_mul_right r k)]
    exact f81_Aq_vanish χ hreal (Nat.dvd_mul_right r k) (by rw [hk]; exact hcop) N

/-- The term at the pair of trivial characters of level `k`. -/
private lemma f81_Aq_one_one_self {k : ℕ} [NeZero k] (N : ℤ) :
    Aq (1 : DirichletCharacter ℂ k) (1 : DirichletCharacter ℂ k) N k
      = (ArithmeticFunction.moebius k : ℂ) ^ 2 * ramanujan k N / (Nat.totient k : ℂ) ^ 2 := by
  rw [Aq, dif_pos (show k ∣ k ∧ k ∣ k from ⟨dvd_refl k, dvd_refl k⟩),
    DirichletCharacter.changeLevel_self, mul_one, tauConj_one, cChi_one]
  ring

/-- Reindexing a sum by the multiples of a positive `r`, for a summand vanishing off them. -/
private lemma f81_tsum_multiples {r : ℕ} (hr : 0 < r) {G H : ℕ → ℂ}
    (hmul : ∀ k, G (r * k) = H k) (hG : ∀ Q, ¬ r ∣ Q → G Q = 0)
    (hGs : Summable G) (hHs : Summable H) :
    ∑' Q : ℕ, G Q = ∑' k : ℕ, H k := by
  have hr1 : 1 ≤ r := hr
  have hpart : ∀ m : ℕ, ∑ Q ∈ Finset.range (r * m), G Q = ∑ k ∈ Finset.range m, H k := by
    intro m
    have himg : (Finset.range (r * m)).filter (fun Q => r ∣ Q)
        = (Finset.range m).image (fun k => r * k) := by
      ext Q
      simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_image]
      constructor
      · rintro ⟨hQ, k, rfl⟩
        refine ⟨k, ?_, rfl⟩
        by_contra hcon
        exact absurd hQ (not_lt.mpr (Nat.mul_le_mul_left r (not_lt.mp hcon)))
      · rintro ⟨k, hk, rfl⟩
        exact ⟨Nat.mul_lt_mul_of_pos_left hk hr, dvd_mul_right r k⟩
    have hzero : ∑ Q ∈ Finset.range (r * m), G Q
        = ∑ Q ∈ (Finset.range (r * m)).filter (fun Q => r ∣ Q), G Q := by
      refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
      intro x hx hxnot
      exact hG x (fun hd => hxnot (Finset.mem_filter.mpr ⟨hx, hd⟩))
    rw [hzero, himg, Finset.sum_image (fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_left hr hxy)]
    exact Finset.sum_congr rfl (fun k _ => hmul k)
  have h1 : Tendsto (fun m => ∑ k ∈ Finset.range m, H k) atTop (nhds (∑' Q : ℕ, G Q)) := by
    have h0 : Tendsto (fun n => ∑ Q ∈ Finset.range n, G Q) atTop (nhds (∑' Q : ℕ, G Q)) :=
      hGs.hasSum.tendsto_sum_nat
    have hmono : Tendsto (fun m : ℕ => r * m) atTop atTop :=
      tendsto_atTop_atTop.mpr (fun b => ⟨b, fun x hx => le_trans hx (by
        calc x = x * 1 := (mul_one x).symm
          _ ≤ x * r := Nat.mul_le_mul_left x hr1
          _ = r * x := Nat.mul_comm x r)⟩)
    have hcomp : Tendsto (fun m : ℕ => ∑ Q ∈ Finset.range (r * m), G Q) atTop
        (nhds (∑' Q : ℕ, G Q)) := h0.comp hmono
    rw [show (fun m : ℕ => ∑ Q ∈ Finset.range (r * m), G Q)
      = (fun m : ℕ => ∑ k ∈ Finset.range m, H k) from funext hpart] at hcomp
    exact hcomp
  exact tendsto_nhds_unique h1 hHs.hasSum.tendsto_sum_nat

/-- The term of the pair `(χ, χ)` at the source modulus, in closed form. -/
private lemma f81_Aq_self_closed {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (hreal : IsRealChar χ) (hprim : χ.IsPrimitive) (N : ℕ) (hdvd : r ∣ N) :
    Aq χ χ N r = χ (-1) * ((((r : ℝ) / (Nat.totient r : ℝ)) : ℝ) : ℂ) := by
  have hφ : ((Nat.totient r : ℝ)) ≠ 0 := by
    have hpos := Nat.totient_pos.mpr (NeZero.pos r)
    positivity
  rw [f81_Aq_self χ hreal (N : ℤ), f81_tauConj_sq hreal hprim, f81_ram_totient hdvd]
  push_cast
  field_simp

/-- The Gauss sum of a primitive real character has modulus the square root of its level. -/
private lemma f81_tauConj_norm {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r}
    (hreal : IsRealChar χ) (hprim : χ.IsPrimitive) : ‖tauConj χ‖ = Real.sqrt r := by
  have h := f81_gaussSum_norm_sq (N := r) hprim
  have hT : tauConj χ = gaussSum χ (ZMod.stdAddChar : AddChar (ZMod r) ℂ) := by
    rw [f81_tauConj_gaussSum, f81_inv_eq_self hreal]
  rw [hT, ← Real.sqrt_sq (norm_nonneg _), h]

/-- The twisted Ramanujan sum of any character is bounded by the totient. -/
private lemma f81_cChi_norm_le {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r) (N : ℤ) :
    ‖cChi χ N‖ ≤ (Nat.totient r : ℝ) := by
  rw [f81_cChi_int_gauss, f81_gaussSum_units]
  calc ‖∑ a : (ZMod r)ˣ, χ (a : ZMod r)
        * (ZMod.stdAddChar (N := r)) ((N : ZMod r) * (a : ZMod r))‖
      ≤ ∑ a : (ZMod r)ˣ, ‖χ (a : ZMod r)
          * (ZMod.stdAddChar (N := r)) ((N : ZMod r) * (a : ZMod r))‖ :=
        norm_sum_le _ _
    _ ≤ ∑ _a : (ZMod r)ˣ, (1 : ℝ) := by
        refine Finset.sum_le_sum (fun a _ => ?_)
        rw [norm_mul]
        have h1 : ‖χ (a : ZMod r)‖ = 1 := DirichletCharacter.unit_norm_eq_one (χ := χ) a
        have h2 : ‖(ZMod.stdAddChar (N := r)) ((N : ZMod r) * (a : ZMod r))‖ = 1 := by
          rw [ZMod.stdAddChar_apply]
          simp
        rw [h1, h2, one_mul]
    _ = (Nat.totient r : ℝ) := by
        rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
          ZMod.card_units_eq_totient]

/-- The term factorises in size through the source level and a coprime quotient. -/
private lemma f81_Aq_norm_le {r k N : ℕ} [NeZero r] [NeZero k] (χ : DirichletCharacter ℂ r)
    (hreal : IsRealChar χ) :
    ‖Aq χ χ (N : ℤ) (r * k)‖ ≤ ‖Aq χ χ (N : ℤ) r‖ *
      ‖(((moebius k : ℤ) : ℝ) ^ 2 / (Nat.totient k : ℝ) ^ 2 * (ramanujan k (N : ℤ)).re)‖ := by
  rw [f81_Aq_split χ hreal (N : ℤ)]
  by_cases hcop : Nat.Coprime k r
  · rw [if_pos hcop, f81_Aq_one_one_self, norm_mul, complex_term_eq N k, Complex.norm_real]
  · rw [if_neg hcop, norm_zero]
    positivity

/-- Pointwise size of the base summand against the `5/4` power of its index. -/
private lemma f81_B_norm_le {N k : ℕ} (hN : 1 ≤ N) :
    ‖(((moebius k : ℤ) : ℝ) ^ 2 / (Nat.totient k : ℝ) ^ 2 * (ramanujan k (N : ℤ)).re)‖ ≤
      (∑ e ∈ N.divisors, (e : ℝ)) * (32 : ℝ) ^ (1 / 4 : ℝ) * (1 / (k : ℝ) ^ (5 / 4 : ℝ)) := by
  have h1 : ‖(((moebius k : ℤ) : ℝ) ^ 2 / (Nat.totient k : ℝ) ^ 2
        * (ramanujan k (N : ℤ)).re)‖
      = ((moebius k : ℤ) : ℝ) ^ 2 / (Nat.totient k : ℝ) ^ 2
        * |(ramanujan k (N : ℤ)).re| := by
    rw [Real.norm_eq_abs, abs_mul, abs_div,
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ ((moebius k : ℤ) : ℝ) ^ 2),
      abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.totient k : ℝ) ^ 2)]
  rw [h1]
  calc ((moebius k : ℤ) : ℝ) ^ 2 / (Nat.totient k : ℝ) ^ 2 * |(ramanujan k (N : ℤ)).re|
      ≤ ((32 : ℝ) ^ (1 / 4 : ℝ) * (1 / (k : ℝ) ^ (5 / 4 : ℝ)))
          * (∑ e ∈ N.divisors, (e : ℝ)) :=
        mul_le_mul (phiSq_le k) (cN_abs_le N hN k) (abs_nonneg _) (by positivity)
    _ = (∑ e ∈ N.divisors, (e : ℝ)) * (32 : ℝ) ^ (1 / 4 : ℝ)
          * (1 / (k : ℝ) ^ (5 / 4 : ℝ)) := by ring

/-- The `5/4` power converts between an index and its multiple. -/
private lemma f81_rpow_div {r k : ℕ} [NeZero r] [NeZero k] :
    1 / (k : ℝ) ^ (5 / 4 : ℝ)
      = (r : ℝ) ^ (5 / 4 : ℝ) * (1 / (((r * k : ℕ)) : ℝ) ^ (5 / 4 : ℝ)) := by
  have hr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast NeZero.pos r
  have hk : (0 : ℝ) < (k : ℝ) := by exact_mod_cast NeZero.pos k
  have hcast : (((r * k : ℕ)) : ℝ) = (r : ℝ) * (k : ℝ) := by push_cast; ring
  rw [hcast, Real.mul_rpow hr.le hk.le, one_div, one_div, mul_inv]
  rw [← mul_assoc, mul_inv_cancel₀ (Real.rpow_pos_of_pos hr _).ne', one_mul]

/-- The term depends only on the value of its modulus. -/
private lemma f81_Aq_congr {r₁ r₂ : ℕ} {N : ℤ} {Q Q' : ℕ} [NeZero Q] [NeZero Q']
    (χ₁ : DirichletCharacter ℂ r₁) (χ₂ : DirichletCharacter ℂ r₂) (h : Q = Q') :
    Aq χ₁ χ₂ N Q = Aq χ₁ χ₂ N Q' := by
  subst h
  rfl

/-- Pointwise size of the term against the `5/4` power of the modulus. -/
private lemma f81_norm_bound {r k N : ℕ} [NeZero r] [NeZero k] (χ : DirichletCharacter ℂ r)
    (hreal : IsRealChar χ) (hN : 1 ≤ N) :
    ‖Aq χ χ (N : ℤ) (r * k)‖ ≤
      (‖Aq χ χ (N : ℤ) r‖
        * ((∑ e ∈ N.divisors, (e : ℝ)) * (32 : ℝ) ^ (1 / 4 : ℝ) * (r : ℝ) ^ (5 / 4 : ℝ)))
        * (1 / (((r * k : ℕ)) : ℝ) ^ (5 / 4 : ℝ)) := by
  refine (f81_Aq_norm_le (N := N) χ hreal).trans ?_
  have hBk := f81_B_norm_le (N := N) hN (k := k)
  have hCnn : (0 : ℝ) ≤ ‖Aq χ χ (N : ℤ) r‖ := norm_nonneg _
  calc ‖Aq χ χ (N : ℤ) r‖ * ‖(((moebius k : ℤ) : ℝ) ^ 2 / (Nat.totient k : ℝ) ^ 2
        * (ramanujan k (N : ℤ)).re)‖
      ≤ ‖Aq χ χ (N : ℤ) r‖ * ((∑ e ∈ N.divisors, (e : ℝ)) * (32 : ℝ) ^ (1 / 4 : ℝ)
          * (1 / (k : ℝ) ^ (5 / 4 : ℝ))) := mul_le_mul_of_nonneg_left hBk hCnn
    _ = _ := by rw [f81_rpow_div (r := r) (k := k)]; ring

/-- The zero-extended term of the pair `(χ, χ)` is summable in the modulus. -/
private lemma f81_summable_Aq {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (hreal : IsRealChar χ) (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun Q : ℕ => if h : Q = 0 then 0 else @Aq r r χ χ (N : ℤ) Q ⟨h⟩) := by
  classical
  have hsum : Summable (fun Q : ℕ => (‖Aq χ χ (N : ℤ) r‖
      * ((∑ e ∈ N.divisors, (e : ℝ)) * (32 : ℝ) ^ (1 / 4 : ℝ) * (r : ℝ) ^ (5 / 4 : ℝ)))
        * (1 / (Q : ℝ) ^ (5 / 4 : ℝ))) := by
    refine Summable.mul_left _ ?_
    exact Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 5 / 4)
  refine Summable.of_norm_bounded hsum (fun Q => ?_)
  by_cases h0 : Q = 0
  · subst h0
    simp
  · haveI : NeZero Q := ⟨h0⟩
    simp only [dif_neg h0]
    by_cases hdvd : r ∣ Q
    · have hkpos : 0 < Q / r :=
        Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd) (NeZero.pos r)
      haveI : NeZero (Q / r) := ⟨hkpos.ne'⟩
      have hQ : Q = r * (Q / r) := (Nat.mul_div_cancel' hdvd).symm
      rw [f81_Aq_congr (χ₁ := χ) (χ₂ := χ) (N := (N : ℤ)) hQ]
      refine (f81_norm_bound (k := Q / r) χ hreal hN).trans ?_
      rw [Nat.mul_div_cancel' hdvd]
    · rw [Aq, dif_neg (show ¬ (r ∣ Q ∧ r ∣ Q) from fun hc => hdvd hc.1), norm_zero]
      positivity



/- @@F81BLOCKEND@@ -/

/-! ### Term algebra for the two leaves: the base term of the series

`term k = μ(k)² c_k(N) / φ(k)²`, the modulus-`k` term of `singular N`, as a complex
number.  Multiplicative, sums at a prime over `1`, and summable in norm. -/

private lemma f81_ram_one (N : ℤ) : ramanujan 1 N = 1 := by
  unfold ramanujan
  simp [f81_ee_zero]

private lemma f81_div_sq_mul_div_sq_c (a b c d e k : ℂ) :
    (a * d) ^ 2 / ((b * e) ^ 2) * (c * k) = (a ^ 2 / b ^ 2 * c) * (d ^ 2 / e ^ 2 * k) := by
  by_cases hb : b = 0
  · simp [hb]
  by_cases he : e = 0
  · simp [he]
  field_simp

private lemma f81_term_zero (N : ℕ) :
    (moebius 0 : ℂ) ^ 2 * ramanujan 0 (N : ℤ) / (Nat.totient 0 : ℂ) ^ 2 = 0 := by
  simp

private lemma f81_term_one (N : ℕ) :
    (moebius 1 : ℂ) ^ 2 * ramanujan 1 (N : ℤ) / (Nat.totient 1 : ℂ) ^ 2 = 1 := by
  rw [f81_ram_one]
  simp

private lemma f81_term_mul (N : ℕ) {m n : ℕ} (hmn : m.Coprime n) :
    (moebius (m * n) : ℂ) ^ 2 * ramanujan (m * n) (N : ℤ) / (Nat.totient (m * n) : ℂ) ^ 2
      = ((moebius m : ℂ) ^ 2 * ramanujan m (N : ℤ) / (Nat.totient m : ℂ) ^ 2)
        * ((moebius n : ℂ) ^ 2 * ramanujan n (N : ℤ) / (Nat.totient n : ℂ) ^ 2) := by
  rw [complex_term_eq N (m * n), complex_term_eq N m, complex_term_eq N n, ← Complex.ofReal_mul,
    singTerm_mul N hmn]

private lemma f81_term_prime (N p : ℕ) (hp : p.Prime) :
    (moebius p : ℂ) ^ 2 * ramanujan p (N : ℤ) / (Nat.totient p : ℂ) ^ 2
      = (((ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2 : ℝ) : ℂ) := by
  have hmu : (moebius p : ℂ) ^ 2 = 1 := by
    rw [moebius_apply_prime hp]; norm_num
  rw [hmu, Nat.totient_prime hp, one_mul, ramanujan_eq_re N p]
  have hcast : (((p - 1 : ℕ)) : ℂ) = (p : ℂ) - 1 := by
    rw [Nat.cast_sub hp.one_lt.le]; push_cast; ring
  rw [hcast]
  push_cast
  rw [Complex.ofReal_re] <;> ring

private lemma f81_term_summable_norm (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun k : ℕ =>
      ‖(moebius k : ℂ) ^ 2 * ramanujan k (N : ℤ) / (Nat.totient k : ℂ) ^ 2‖) := by
  refine (summable_norm_singTerm N hN).congr (fun k => ?_)
  rw [complex_term_eq N k, Complex.norm_real]

private lemma f81_coprime_term_summable (r N : ℕ) (hN : 1 ≤ N) :
    Summable (fun k : ℕ =>
      if Nat.Coprime k r then
        (moebius k : ℂ) ^ 2 * ramanujan k (N : ℤ) / (Nat.totient k : ℂ) ^ 2 else 0) := by
  refine Summable.of_norm_bounded (f81_term_summable_norm N hN) (fun k => ?_)
  split_ifs with h
  · exact le_rfl
  · rw [norm_zero]
    exact norm_nonneg _

private lemma f81_coprime_norm_summable (r N : ℕ) (hN : 1 ≤ N) :
    Summable (fun k : ℕ => ‖if Nat.Coprime k r then
      (moebius k : ℂ) ^ 2 * ramanujan k (N : ℤ) / (Nat.totient k : ℂ) ^ 2 else 0‖) := by
  refine Summable.of_norm_bounded (f81_term_summable_norm N hN) (fun k => ?_)
  split_ifs with h
  · rw [norm_norm]
  · rw [norm_zero, norm_zero]
    exact norm_nonneg _

/-- The sum at a prime of the truncated multiplicative term: only `e = 0, 1` survive. -/
private lemma f81_tsum_coprime_prime (N r p : ℕ) (hp : p.Prime) :
    ∑' e : ℕ, (if Nat.Coprime (p ^ e) r then
        (moebius (p ^ e) : ℂ) ^ 2 * ramanujan (p ^ e) (N : ℤ)
          / (Nat.totient (p ^ e) : ℂ) ^ 2 else 0)
      = 1 + (if Nat.Coprime p r then (((ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2 : ℝ) : ℂ)
          else 0) := by
  have hsupp : ∀ e ∉ Finset.range 2,
      (if Nat.Coprime (p ^ e) r then
        (moebius (p ^ e) : ℂ) ^ 2 * ramanujan (p ^ e) (N : ℤ)
          / (Nat.totient (p ^ e) : ℂ) ^ 2 else 0) = 0 := by
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
  rw [h0, h1, if_pos (Nat.coprime_one_left r), f81_term_one]
  congr 1
  by_cases hp2 : Nat.Coprime p r
  · rw [if_pos hp2, if_pos hp2, f81_term_prime N p hp]
  · rw [if_neg hp2, if_neg hp2]

/-! ### The totient ratio `r / φ(r) = Π_{p | r} p/(p-1)` and the product splitting -/

private lemma f81_totient_ratio (r : ℕ) (hr : r ≠ 0) :
    (r : ℝ) / (Nat.totient r : ℝ) = ∏ p ∈ r.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
  have h := Nat.totient_mul_prod_primeFactors r
  have hcast : ∀ p ∈ r.primeFactors, (((p - 1 : ℕ)) : ℝ) = (p : ℝ) - 1 := by
    intro p hp
    have hp' := Nat.prime_of_mem_primeFactors hp
    rw [Nat.cast_sub hp'.one_lt.le]; norm_num
  have hR : (Nat.totient r : ℝ) * ∏ p ∈ r.primeFactors, (p : ℝ)
      = (r : ℝ) * ∏ p ∈ r.primeFactors, ((p : ℝ) - 1) := by
    have h2 := congrArg (fun z : ℕ => (z : ℝ)) h
    simp only [Nat.cast_mul, Nat.cast_prod] at h2
    rw [Finset.prod_congr rfl hcast] at h2
    exact h2
  rw [Finset.prod_div_distrib]
  have hφ0 : (Nat.totient r : ℝ) ≠ 0 := by
    have hpos := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hr)
    exact_mod_cast hpos.ne'
  have hP : (∏ p ∈ r.primeFactors, (p : ℝ)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun p hp => ?_)
    have := (Nat.prime_of_mem_primeFactors hp).ne_zero
    exact_mod_cast this
  have hQ : (∏ p ∈ r.primeFactors, ((p : ℝ) - 1)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun p hp => ?_)
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by
      have := (Nat.prime_of_mem_primeFactors hp).two_le
      exact_mod_cast this
    linarith
  rw [div_eq_div_iff hφ0 hQ]
  linarith [hR]

/-- For `p` a prime divisor of `r ∣ N` the local factor of `𝔖(N)` is `p/(p-1)`. -/
private lemma f81_local_factor_closed {r N p : ℕ} (hdvd : r ∣ N) (hp : p ∈ r.primeFactors) :
    1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2 = (p : ℝ) / ((p : ℝ) - 1) := by
  have hprime := Nat.prime_of_mem_primeFactors hp
  have hpdvd : p ∣ N := dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdvd
  rw [cN_prime N p hprime, if_pos hpdvd]
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hprime.two_le
  have hpos : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h1 : ((p : ℝ) - 1) ≠ 0 := ne_of_gt hpos
  have h2 : ((p : ℝ) - 1) ^ 2 ≠ 0 := pow_ne_zero 2 h1
  field_simp
  ring

private lemma f81_prod_primeFactors_closed (r N : ℕ) (hr : r ≠ 0) (hdvd : r ∣ N) :
    ∏ p ∈ r.primeFactors, (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2)
      = (r : ℝ) / (Nat.totient r : ℝ) := by
  rw [Finset.prod_congr rfl (fun p hp => f81_local_factor_closed hdvd hp),
    f81_totient_ratio r hr]

/-- The full Euler product of `𝔖(N)` is the product over the primes of `r` times the
product over the primes prime to `r`, once the truncation has passed `r`. -/
private lemma f81_prod_split (r N n : ℕ) (hr : 0 < r) (hrn : r < n) :
    ∏ p ∈ n.primesBelow, (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2)
      = (∏ p ∈ r.primeFactors, (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2))
        * ∏ p ∈ n.primesBelow,
            (1 + (if Nat.Coprime p r then
              (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2 else 0)) := by
  have hr0 : r ≠ 0 := hr.ne'
  have hsub : r.primeFactors ⊆ n.primesBelow := by
    intro p hp
    rw [Nat.mem_primesBelow]
    exact ⟨lt_of_le_of_lt (Nat.le_of_mem_primeFactors hp) hrn,
      Nat.prime_of_mem_primeFactors hp⟩
  have hfilter : n.primesBelow.filter (fun p => ¬ Nat.Coprime p r) = r.primeFactors := by
    ext p
    rw [Finset.mem_filter, Nat.mem_primesBelow, Nat.mem_primeFactors_of_ne_zero hr0]
    constructor
    · rintro ⟨⟨-, hpp⟩, hnc⟩
      exact ⟨hpp, by_contra (fun hd => hnc (hpp.coprime_iff_not_dvd.mpr hd))⟩
    · rintro ⟨hpp, hpdvd⟩
      exact ⟨⟨lt_of_le_of_lt (Nat.le_of_dvd hr hpdvd) hrn, hpp⟩,
        fun hc => hpp.coprime_iff_not_dvd.mp hc hpdvd⟩
  have hM := Finset.prod_filter_mul_prod_filter_not (s := n.primesBelow)
    (f := fun p => 1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2)
    (p := fun p => Nat.Coprime p r)
  rw [hfilter] at hM
  have hX : ((n.primesBelow.filter (fun p => Nat.Coprime p r)).prod
        (fun p => 1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2))
      = (n.primesBelow).prod (fun p => (1 + (if Nat.Coprime p r then
            (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2 else 0))) := by
    rw [Finset.prod_filter]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    by_cases hc : Nat.Coprime p r
    · rw [if_pos hc, if_pos hc]
    · rw [if_neg hc, if_neg hc] <;> norm_num
  rw [← hM, hX, mul_comm]

/-- The Euler product of the restricted function `k ↦ [k ⊥ r]·term k`. -/
private lemma f81_coprime_eulerProduct (r N : ℕ) (hN : 1 ≤ N) :
    Filter.Tendsto (fun n : ℕ => ∏ p ∈ n.primesBelow,
        (1 + (if Nat.Coprime p r then
          (((ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2 : ℝ) : ℂ) else 0)))
      Filter.atTop
      (nhds (∑' k : ℕ, if Nat.Coprime k r then
        (moebius k : ℂ) ^ 2 * ramanujan k (N : ℤ) / (Nat.totient k : ℂ) ^ 2 else 0)) := by
  let F : ArithmeticFunction ℂ :=
    ⟨fun k => if Nat.Coprime k r then
      (moebius k : ℂ) ^ 2 * ramanujan k (N : ℤ) / (Nat.totient k : ℂ) ^ 2 else 0, by
      by_cases h : Nat.Coprime 0 r
      · rw [if_pos h]
        exact f81_term_zero N
      · rw [if_neg h]⟩
  have hFone : F 1 = 1 := by
    show (if Nat.Coprime 1 r then
      (moebius 1 : ℂ) ^ 2 * ramanujan 1 (N : ℤ) / (Nat.totient 1 : ℂ) ^ 2 else 0) = 1
    rw [if_pos (Nat.coprime_one_left r), f81_term_one]
  have hFmul : ∀ {m n : ℕ}, m.Coprime n → F (m * n) = F m * F n := by
    intro m n hmn
    show (if Nat.Coprime (m * n) r then
        (moebius (m * n) : ℂ) ^ 2 * ramanujan (m * n) (N : ℤ)
          / (Nat.totient (m * n) : ℂ) ^ 2 else 0)
      = (if Nat.Coprime m r then
        (moebius m : ℂ) ^ 2 * ramanujan m (N : ℤ) / (Nat.totient m : ℂ) ^ 2 else 0)
        * (if Nat.Coprime n r then
        (moebius n : ℂ) ^ 2 * ramanujan n (N : ℤ) / (Nat.totient n : ℂ) ^ 2 else 0)
    by_cases hm : Nat.Coprime m r
    · by_cases hn : Nat.Coprime n r
      · rw [if_pos ((Nat.coprime_mul_iff_left).mpr ⟨hm, hn⟩), if_pos hm, if_pos hn,
          f81_term_mul N hmn]
      · rw [if_neg (fun hh => hn ((Nat.coprime_mul_iff_left.mp hh).2)), if_pos hm,
          if_neg hn, mul_zero]
    · rw [if_neg (fun hh => hm ((Nat.coprime_mul_iff_left.mp hh).1)), if_neg hm, zero_mul]
  have hFm : F.IsMultiplicative := ⟨hFone, fun {_ _} hmn => hFmul hmn⟩
  have hFs : Summable (fun k : ℕ => ‖F k‖) := by
    show Summable (fun k : ℕ => ‖if Nat.Coprime k r then
      (moebius k : ℂ) ^ 2 * ramanujan k (N : ℤ) / (Nat.totient k : ℂ) ^ 2 else 0‖)
    exact f81_coprime_norm_summable r N hN
  have h := IsMultiplicative.eulerProduct hFm hFs
  have h2 : (fun n : ℕ => ∏ p ∈ n.primesBelow, ∑' e : ℕ, F (p ^ e))
      = (fun n : ℕ => ∏ p ∈ n.primesBelow,
        (1 + (if Nat.Coprime p r then
          (((ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2 : ℝ) : ℂ) else 0))) := by
    funext n
    exact Finset.prod_congr rfl
      (fun p hp => f81_tsum_coprime_prime N r p (Nat.mem_primesBelow.mp hp).2)
  rw [h2] at h
  exact h

/-- The limit comparison: `𝔖(N)` is the local product over the primes of `r` times the
restricted sum over the moduli prime to `r`. -/
private lemma f81_restricted_lim (r N : ℕ) (hr : 0 < r) (hN : 1 ≤ N) :
    (((∏ p ∈ r.primeFactors,
        (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2) : ℝ) : ℂ) *
      (∑' k : ℕ, if Nat.Coprime k r then
        (moebius k : ℂ) ^ 2 * ramanujan k (N : ℤ) / (Nat.totient k : ℂ) ^ 2 else 0))
      = ((singular N : ℝ) : ℂ) := by
  have hA := eulerProduct_singTerm N hN
  have hA2 : Filter.Tendsto
      ((fun x : ℝ => (x : ℂ)) ∘ (fun n : ℕ => ∏ p ∈ n.primesBelow,
        (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2))) Filter.atTop
      (nhds ((singular N : ℝ) : ℂ)) := by
    have hcont : Filter.Tendsto (fun x : ℝ => (x : ℂ))
        (nhds (∑' q : ℕ, ((moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2
          * (ramanujan q (N : ℤ)).re))
        (nhds (((∑' q : ℕ, ((moebius q : ℤ) : ℝ) ^ 2 / (Nat.totient q : ℝ) ^ 2
          * (ramanujan q (N : ℤ)).re : ℝ) : ℂ))) :=
      Complex.continuous_ofReal.tendsto _
    have h' := hcont.comp hA
    simpa [singular, Function.comp] using h'
  have hB := f81_coprime_eulerProduct r N hN
  set Cc : ℂ := ((∏ p ∈ r.primeFactors,
      (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2) : ℝ) : ℂ) with hCc
  have hC : Filter.Tendsto (fun n : ℕ => Cc * ∏ p ∈ n.primesBelow,
        (1 + (if Nat.Coprime p r then
          (((ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2 : ℝ) : ℂ) else 0)))
      Filter.atTop
      (nhds (Cc * (∑' k : ℕ, if Nat.Coprime k r then
        (moebius k : ℂ) ^ 2 * ramanujan k (N : ℤ) / (Nat.totient k : ℂ) ^ 2 else 0))) :=
    hB.const_mul Cc
  have hEq : (fun n : ℕ => Cc * ∏ p ∈ n.primesBelow,
        (1 + (if Nat.Coprime p r then
          (((ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2 : ℝ) : ℂ) else 0)))
      =ᶠ[Filter.atTop]
      ((fun x : ℝ => (x : ℂ)) ∘ (fun n : ℕ => ∏ p ∈ n.primesBelow,
        (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2))) := by
    filter_upwards [Filter.eventually_gt_atTop r] with n hn
    rw [hCc, Function.comp_apply, f81_prod_split r N n hr hn, Complex.ofReal_mul,
      Complex.ofReal_prod]
    have hfac : ∀ p : ℕ, (1 + (if Nat.Coprime p r then
          (((ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2 : ℝ) : ℂ) else 0))
        = (((1 + (if Nat.Coprime p r then
          (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2 else 0) : ℝ) : ℂ)) := by
      intro p
      by_cases hc : Nat.Coprime p r
      · rw [if_pos hc, if_pos hc]
        push_cast
        ring
      · rw [if_neg hc, if_neg hc] <;> norm_num
    simp only [hfac, Complex.ofReal_prod]
  have huniq := tendsto_nhds_unique (hC.congr' hEq) hA2
  rw [hCc] at huniq
  exact huniq

/-- `𝔖(N) = (r/φ(r)) · Σ'_{k ⊥ r} term k` for `r ∣ N`: the key identity behind
`facts81_diag`. -/
private lemma f81_restricted_tsum (r N : ℕ) (hr : 0 < r) (hN : 1 ≤ N) (hdvd : r ∣ N) :
    (((r : ℝ) / (Nat.totient r : ℝ) : ℝ) : ℂ) *
      (∑' k : ℕ, if Nat.Coprime k r then
        (moebius k : ℂ) ^ 2 * ramanujan k (N : ℤ) / (Nat.totient k : ℂ) ^ 2 else 0)
      = ((singular N : ℝ) : ℂ) := by
  rw [← f81_prod_primeFactors_closed r N hr.ne' hdvd]
  exact f81_restricted_lim r N hr hN

/-- `Aq` for the pair `(χ₁, χ₂)` is supported on the multiples of the conductor. -/
private lemma f81_Aq_self_zero_of_not_dvd {r Q : ℕ} (χ : DirichletCharacter ℂ r) (N : ℤ)
    [NeZero Q] (h : ¬ r ∣ Q) : Aq χ χ N Q = 0 := by
  rw [Aq, dif_neg (fun hh => h hh.1)]

private lemma f81_Aq_chi1_zero_of_not_dvd {r Q : ℕ} (χ : DirichletCharacter ℂ r) (N : ℤ)
    [NeZero Q] (h : ¬ r ∣ Q) : Aq chi1 χ N Q = 0 := by
  rw [Aq, dif_neg (fun hh => h hh.2)]

/-- The generalised series of the pair `(χ, χ)` as a sum over its moduli, split off the
conductor `r`: `genSing χ χ N = Aq χ χ N r · Σ'_{k ⊥ r} term k`. -/
private lemma f81_genSing_self_split {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (hreal : IsRealChar χ) (N : ℕ) (hN : 1 ≤ N) :
    genSing χ χ (N : ℤ) =
      Aq χ χ (N : ℤ) r * (∑' k : ℕ, if Nat.Coprime k r then
        (moebius k : ℂ) ^ 2 * ramanujan k (N : ℤ) / (Nat.totient k : ℂ) ^ 2 else 0) := by
  have hr : 0 < r := NeZero.pos r
  have hGs := f81_summable_Aq χ hreal N hN
  have hA : (∑' n : ℕ, @Aq r r χ χ (N : ℤ) (n + 1) ⟨Nat.succ_ne_zero n⟩)
      = ∑' Q : ℕ, (if h : Q = 0 then 0 else @Aq r r χ χ (N : ℤ) Q ⟨h⟩) := by
    rw [hGs.tsum_eq_zero_add, dif_pos rfl, zero_add]
    have hpt : ∀ n : ℕ, @Aq r r χ χ (N : ℤ) (n + 1) ⟨Nat.succ_ne_zero n⟩
        = (if h : n + 1 = 0 then 0 else @Aq r r χ χ (N : ℤ) (n + 1) ⟨h⟩) := by
      intro n
      rw [dif_neg (Nat.succ_ne_zero n)]
    exact tsum_congr hpt
  have hB : genSing χ χ (N : ℤ)
      = ∑' n : ℕ, @Aq r r χ χ (N : ℤ) (n + 1) ⟨Nat.succ_ne_zero n⟩ := by
    rw [genSing]
  rw [hB.trans hA]
  have hmul : ∀ k : ℕ, (if h : r * k = 0 then 0
        else @Aq r r χ χ (N : ℤ) (r * k) ⟨h⟩)
      = Aq χ χ (N : ℤ) r * (if Nat.Coprime k r then
        (moebius k : ℂ) ^ 2 * ramanujan k (N : ℤ) / (Nat.totient k : ℂ) ^ 2 else 0) := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      rw [Nat.mul_zero, dif_pos rfl]
      by_cases hc : Nat.Coprime 0 r
      · rw [if_pos hc, f81_term_zero, mul_zero]
      · rw [if_neg hc, mul_zero]
    · haveI : NeZero k := ⟨hkpos.ne'⟩
      have hk : r * k ≠ 0 := Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne k)
      haveI : NeZero (r * k) := ⟨hk⟩
      rw [dif_neg hk, f81_Aq_split χ hreal (N : ℤ)]
      by_cases hc : Nat.Coprime k r
      · rw [if_pos hc, if_pos hc, f81_Aq_one_one_self]
      · rw [if_neg hc, if_neg hc, mul_zero]
  have hvan : ∀ Q : ℕ, ¬ r ∣ Q →
      (if h : Q = 0 then 0 else @Aq r r χ χ (N : ℤ) Q ⟨h⟩) = 0 := by
    intro Q hQ
    have hQ0 : Q ≠ 0 := fun h => hQ (by rw [h]; exact dvd_zero r)
    rw [dif_neg hQ0]
    exact @f81_Aq_self_zero_of_not_dvd r Q χ (N : ℤ) ⟨hQ0⟩ hQ
  have hHs : Summable (fun k : ℕ => Aq χ χ (N : ℤ) r * (if Nat.Coprime k r then
      (moebius k : ℂ) ^ 2 * ramanujan k (N : ℤ) / (Nat.totient k : ℂ) ^ 2 else 0)) :=
    (f81_coprime_term_summable r N hN).mul_left _
  rw [f81_tsum_multiples hr hmul hvan hGs hHs, tsum_mul_left]

private lemma f81_diag_aux {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (hprim : χ.IsPrimitive) (hreal : IsRealChar χ) (N : ℕ) (hN2 : 2 ≤ N) (hdvd : r ∣ N) :
    genSing χ χ (N : ℤ) = χ (-1) * ((singular N : ℝ) : ℂ) := by
  have hr : 0 < r := NeZero.pos r
  have hN1 : 1 ≤ N := by omega
  rw [f81_genSing_self_split χ hreal N hN1, f81_Aq_self_closed χ hreal hprim N hdvd,
    mul_assoc, f81_restricted_tsum r N hr hN1 hdvd]


/-! ### The saving leaf: the Gauss-sum bound, the split for `(χ₀, χ)`, and the local factors -/

private lemma f81_chi_norm_le_one {q : ℕ} [NeZero q] (χ : DirichletCharacter ℂ q) (a : ZMod q) :
    ‖χ a‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    rw [DirichletCharacter.unit_norm_eq_one (χ := χ) u]
  · rw [MulChar.map_nonunit χ ha, norm_zero]
    norm_num

/-- The twisted sum of a primitive real character is bounded by `√r`: it is a Gauss sum
divided by the Gauss sum of its own modulus. -/
private lemma f81_cChi_norm_le_sqrt {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r}
    (hreal : IsRealChar χ) (hprim : χ.IsPrimitive) (N : ℤ) :
    ‖cChi χ N‖ ≤ Real.sqrt r := by
  have hτ : tauConj χ = gaussSum χ (ZMod.stdAddChar : AddChar (ZMod r) ℂ) := by
    rw [f81_tauConj_gaussSum, f81_inv_eq_self hreal]
  have hτn : ‖tauConj χ‖ = Real.sqrt r := f81_tauConj_norm hreal hprim
  have hs : (0 : ℝ) < Real.sqrt r := Real.sqrt_pos.mpr (by exact_mod_cast NeZero.pos r)
  have hτne : tauConj χ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hτn
    linarith
  have hmul := f81_mul_gaussSum_mulShift (N := r) hprim (N : ZMod r)
  have hc : cChi χ N
      = gaussSum χ⁻¹ ((ZMod.stdAddChar (N := r)).mulShift (N : ZMod r)) := by
    rw [f81_cChi_int_gauss, f81_inv_eq_self hreal]
  have hval : gaussSum χ⁻¹ ((ZMod.stdAddChar (N := r)).mulShift (N : ZMod r))
      = ((r : ℂ) * χ (-(N : ZMod r))) / tauConj χ := by
    rw [eq_div_iff hτne, hτ, mul_comm]
    exact hmul.symm
  rw [hc, hval, norm_div, norm_mul]
  have hχ : ‖χ (-(N : ZMod r))‖ ≤ 1 := f81_chi_norm_le_one χ _
  have hrnn : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
  have hsq : Real.sqrt r * Real.sqrt r = (r : ℝ) := by
    rw [← pow_two, Real.sq_sqrt hrnn]
  have hnum : ‖(r : ℂ)‖ * ‖χ (-(N : ZMod r))‖ ≤ (r : ℝ) := by
    rw [Complex.norm_natCast]
    nlinarith [hχ, hrnn]
  rw [hτn, div_le_iff₀ hs]
  linarith [hnum, hsq]

/-- `Aq` of the pair `(χ₀, χ)` at a multiple `Q` of the conductor, in Gauss-sum form. -/
private lemma f81_Aq_chi1_form {r Q : ℕ} [NeZero r] [NeZero Q] (χ : DirichletCharacter ℂ r)
    (h : r ∣ Q) (N : ℤ) :
    Aq chi1 χ N Q = (moebius Q : ℂ) * tauConj (DirichletCharacter.changeLevel h χ)
      * cChi (DirichletCharacter.changeLevel h χ) N / (Nat.totient Q : ℂ) ^ 2 := by
  rw [Aq, dif_pos (show 1 ∣ Q ∧ r ∣ Q from ⟨one_dvd Q, h⟩)]
  simp only [chi1, map_one, one_mul, tauConj_one]

/-- The pair `(χ₀, χ)` vanishes at `r k` when `k` is not prime to `r`: the Gauss sum of the
induced character is then zero. -/
private lemma f81_Aq_chi1_vanish {r k : ℕ} [NeZero r] [NeZero k] (χ : DirichletCharacter ℂ r)
    (hreal : IsRealChar χ) (N : ℤ) (hbad : ¬ Nat.Coprime k r) :
    Aq chi1 χ N (r * k) = 0 := by
  obtain ⟨p, hp, hpk, hpr⟩ := Nat.Prime.not_coprime_iff_dvd.mp hbad
  haveI : NeZero (r * k) := ⟨Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne k)⟩
  have hdiv : (r * k) / r = k := by
    rw [Nat.mul_comm]
    exact Nat.mul_div_left k (NeZero.pos r)
  rw [f81_Aq_chi1_form χ (Nat.dvd_mul_right r k) N,
    f81_tau_lift_vanish χ hreal (Nat.dvd_mul_right r k) hp hpr (by rw [hdiv]; exact hpk)]
  simp

/-- The modulus-`r k` term of the pair `(χ₀, χ)` is the conductor term times the truncated
multiplicative term. -/
private lemma f81_Aq_chi1_step {r k N : ℕ} [NeZero r] [NeZero k]
    (χ : DirichletCharacter ℂ r) (hreal : IsRealChar χ) :
    ‖Aq chi1 χ (N : ℤ) (r * k)‖ ≤
      ‖Aq chi1 χ (N : ℤ) r‖ * ‖((moebius k : ℂ) ^ 2 * ramanujan k (N : ℤ)
        / (Nat.totient k : ℂ) ^ 2)‖ := by
  by_cases hc : Nat.Coprime k r
  · rw [f81_Aq_chi1_mul (r := r) (k := k) hc.symm χ (N : ℤ), f81_Aq_one_one_self, norm_mul]
  · rw [f81_Aq_chi1_vanish χ hreal (N : ℤ) hc, norm_zero]
    positivity

/-- The modulus-`r` term of the pair `(χ₀, χ)`: `‖Aq‖ ≤ r/φ(r)²`. -/
private lemma f81_Aq_chi1_norm_le {r : ℕ} [NeZero r] {χ : DirichletCharacter ℂ r}
    (hreal : IsRealChar χ) (hprim : χ.IsPrimitive) (N : ℤ) :
    ‖Aq chi1 χ N r‖ ≤ (r : ℝ) / (Nat.totient r : ℝ) ^ 2 := by
  have hφpos : (0 : ℝ) < (Nat.totient r : ℝ) ^ 2 := by
    have hpos := Nat.totient_pos.mpr (NeZero.pos r)
    have : (0 : ℝ) < (Nat.totient r : ℝ) := by exact_mod_cast hpos
    positivity
  have hmu : ‖(moebius r : ℂ)‖ ≤ 1 := by
    have h := abs_moebius_le_one (n := r)
    have h2 : ‖(moebius r : ℂ)‖ = (((|(moebius r : ℤ)| : ℤ)) : ℝ) := by
      rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs, Int.cast_abs]
    rw [h2]
    exact_mod_cast h
  have hs : (0 : ℝ) ≤ Real.sqrt r := Real.sqrt_nonneg r
  have hsq : Real.sqrt r * Real.sqrt r = (r : ℝ) := by
    rw [← pow_two, Real.sq_sqrt (Nat.cast_nonneg r)]
  have hc := f81_cChi_norm_le_sqrt hreal hprim N
  have hb : ‖(moebius r : ℂ) * tauConj χ * cChi χ N‖ ≤ (r : ℝ) := by
    rw [norm_mul, norm_mul]
    have hτ := f81_tauConj_norm hreal hprim
    have h1 : ‖(moebius r : ℂ)‖ * ‖tauConj χ‖ ≤ Real.sqrt r := by
      have hh := mul_le_mul hmu (le_of_eq hτ) (norm_nonneg _) zero_le_one
      simpa using hh
    calc ‖(moebius r : ℂ)‖ * ‖tauConj χ‖ * ‖cChi χ N‖
        ≤ Real.sqrt r * Real.sqrt r := mul_le_mul h1 hc (norm_nonneg _) hs
      _ = (r : ℝ) := hsq
  calc ‖Aq chi1 χ N r‖
      = ‖(moebius r : ℂ) * tauConj χ * cChi χ N‖ / (Nat.totient r : ℝ) ^ 2 := by
        rw [f81_Aq_chi1_chi_self, norm_div, norm_pow, Complex.norm_natCast]
    _ ≤ (r : ℝ) / (Nat.totient r : ℝ) ^ 2 :=
        div_le_div_of_nonneg_right hb (le_of_lt hφpos)

/-- The zero-extended term of the pair `(χ₀, χ)` is summable in the modulus. -/
private lemma f81_summable_Aq_chi1 {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (hreal : IsRealChar χ) (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun Q : ℕ => if h : Q = 0 then 0 else @Aq 1 r chi1 χ (N : ℤ) Q ⟨h⟩) := by
  classical
  have hsum : Summable (fun Q : ℕ => (‖Aq chi1 χ (N : ℤ) r‖
      * ((∑ e ∈ N.divisors, (e : ℝ)) * (32 : ℝ) ^ (1 / 4 : ℝ) * (r : ℝ) ^ (5 / 4 : ℝ)))
        * (1 / (Q : ℝ) ^ (5 / 4 : ℝ))) := by
    refine Summable.mul_left _ ?_
    exact Real.summable_one_div_nat_rpow.mpr (by norm_num : (1 : ℝ) < 5 / 4)
  refine Summable.of_norm_bounded hsum (fun Q => ?_)
  by_cases h0 : Q = 0
  · subst h0
    simp
  · haveI : NeZero Q := ⟨h0⟩
    simp only [dif_neg h0]
    by_cases hdvd : r ∣ Q
    · have hkpos : 0 < Q / r :=
        Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) hdvd) (NeZero.pos r)
      haveI : NeZero (Q / r) := ⟨hkpos.ne'⟩
      have hQ : Q = r * (Q / r) := (Nat.mul_div_cancel' hdvd).symm
      rw [f81_Aq_congr (χ₁ := chi1) (χ₂ := χ) (N := (N : ℤ)) hQ]
      refine (f81_Aq_chi1_step (k := Q / r) χ hreal).trans ?_
      rw [complex_term_eq (N := N) (Q := Q / r), Complex.norm_real]
      have hBk := f81_B_norm_le (N := N) hN (k := Q / r)
      have hAnn : (0 : ℝ) ≤ ‖Aq chi1 χ (N : ℤ) r‖ := norm_nonneg _
      calc ‖Aq chi1 χ (N : ℤ) r‖ * ‖(((moebius (Q / r) : ℤ) : ℝ) ^ 2
            / (Nat.totient (Q / r) : ℝ) ^ 2 * (ramanujan (Q / r) (N : ℤ)).re)‖
          ≤ ‖Aq chi1 χ (N : ℤ) r‖ * ((∑ e ∈ N.divisors, (e : ℝ)) * (32 : ℝ) ^ (1 / 4 : ℝ)
              * (1 / ((Q / r : ℕ) : ℝ) ^ (5 / 4 : ℝ))) :=
            mul_le_mul_of_nonneg_left hBk hAnn
        _ = (‖Aq chi1 χ (N : ℤ) r‖ * ((∑ e ∈ N.divisors, (e : ℝ)) * (32 : ℝ) ^ (1 / 4 : ℝ)
              * (r : ℝ) ^ (5 / 4 : ℝ))) * (1 / (Q : ℝ) ^ (5 / 4 : ℝ)) := by
            rw [f81_rpow_div (r := r) (k := Q / r), Nat.mul_div_cancel' hdvd]
            ring
    · rw [f81_Aq_chi1_zero_of_not_dvd χ (N : ℤ) hdvd, norm_zero]
      positivity

/-- The generalised series of the pair `(χ₀, χ)`, split at the conductor: the sum over the
moduli prime to `r` of the truncated multiplicative term, times the conductor term. -/
private lemma f81_genSing_chi1_split {r : ℕ} [NeZero r] (χ : DirichletCharacter ℂ r)
    (hreal : IsRealChar χ) (N : ℕ) (hN : 1 ≤ N) :
    genSing chi1 χ (N : ℤ) =
      Aq chi1 χ (N : ℤ) r * (∑' k : ℕ, if Nat.Coprime k r then
        (moebius k : ℂ) ^ 2 * ramanujan k (N : ℤ) / (Nat.totient k : ℂ) ^ 2 else 0) := by
  have hr : 0 < r := NeZero.pos r
  have hGs := f81_summable_Aq_chi1 χ hreal N hN
  have hA : (∑' n : ℕ, @Aq 1 r chi1 χ (N : ℤ) (n + 1) ⟨Nat.succ_ne_zero n⟩)
      = ∑' Q : ℕ, (if h : Q = 0 then 0 else @Aq 1 r chi1 χ (N : ℤ) Q ⟨h⟩) := by
    rw [hGs.tsum_eq_zero_add, dif_pos rfl, zero_add]
    have hpt : ∀ n : ℕ, @Aq 1 r chi1 χ (N : ℤ) (n + 1) ⟨Nat.succ_ne_zero n⟩
        = (if h : n + 1 = 0 then 0 else @Aq 1 r chi1 χ (N : ℤ) (n + 1) ⟨h⟩) := by
      intro n
      rw [dif_neg (Nat.succ_ne_zero n)]
    exact tsum_congr hpt
  have hB : genSing chi1 χ (N : ℤ)
      = ∑' n : ℕ, @Aq 1 r chi1 χ (N : ℤ) (n + 1) ⟨Nat.succ_ne_zero n⟩ := by
    rw [genSing]
  rw [hB.trans hA]
  have hmul : ∀ k : ℕ, (if h : r * k = 0 then 0
        else @Aq 1 r chi1 χ (N : ℤ) (r * k) ⟨h⟩)
      = Aq chi1 χ (N : ℤ) r * (if Nat.Coprime k r then
        (moebius k : ℂ) ^ 2 * ramanujan k (N : ℤ) / (Nat.totient k : ℂ) ^ 2 else 0) := by
    intro k
    rcases Nat.eq_zero_or_pos k with hk0 | hkpos
    · subst hk0
      rw [Nat.mul_zero, dif_pos rfl]
      by_cases hc : Nat.Coprime 0 r
      · rw [if_pos hc, f81_term_zero, mul_zero]
      · rw [if_neg hc, mul_zero]
    · haveI : NeZero k := ⟨hkpos.ne'⟩
      have hk : r * k ≠ 0 := Nat.mul_ne_zero (NeZero.ne r) (NeZero.ne k)
      haveI : NeZero (r * k) := ⟨hk⟩
      rw [dif_neg hk]
      by_cases hc : Nat.Coprime k r
      · rw [if_pos hc, f81_Aq_chi1_mul (r := r) (k := k) hc.symm χ (N : ℤ),
          f81_Aq_one_one_self]
      · rw [if_neg hc, f81_Aq_chi1_vanish χ hreal (N : ℤ) hc, mul_zero]
  have hvan : ∀ Q : ℕ, ¬ r ∣ Q →
      (if h : Q = 0 then 0 else @Aq 1 r chi1 χ (N : ℤ) Q ⟨h⟩) = 0 := by
    intro Q hQ
    have hQ0 : Q ≠ 0 := fun h => hQ (by rw [h]; exact dvd_zero r)
    rw [dif_neg hQ0]
    exact @f81_Aq_chi1_zero_of_not_dvd r Q χ (N : ℤ) ⟨hQ0⟩ hQ
  have hHs : Summable (fun k : ℕ => Aq chi1 χ (N : ℤ) r * (if Nat.Coprime k r then
      (moebius k : ℂ) ^ 2 * ramanujan k (N : ℤ) / (Nat.totient k : ℂ) ^ 2 else 0)) :=
    (f81_coprime_term_summable r N hN).mul_left _
  rw [f81_tsum_multiples hr hmul hvan hGs hHs, tsum_mul_left]

/-- The complex restricted sum is the image of the real restricted sum. -/
private lemma f81_restricted_real_cast (r N : ℕ) :
    (∑' k : ℕ, if Nat.Coprime k r then
        (moebius k : ℂ) ^ 2 * ramanujan k (N : ℤ) / (Nat.totient k : ℂ) ^ 2 else 0)
      = ((∑' k : ℕ, if Nat.Coprime k r then
        (((moebius k : ℤ) : ℝ) ^ 2 / (Nat.totient k : ℝ) ^ 2
          * (ramanujan k (N : ℤ)).re) else 0 : ℝ) : ℂ) := by
  rw [Complex.ofReal_tsum]
  refine tsum_congr (fun k => ?_)
  by_cases hc : Nat.Coprime k r
  · rw [if_pos hc, if_pos hc, complex_term_eq]
  · rw [if_neg hc, if_neg hc]
    simp

/-- The real form of the limit comparison. -/
private lemma f81_restricted_lim_real (r N : ℕ) (hr : 0 < r) (hN : 1 ≤ N) :
    (∏ p ∈ r.primeFactors, (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2))
      * (∑' k : ℕ, if Nat.Coprime k r then
        (((moebius k : ℤ) : ℝ) ^ 2 / (Nat.totient k : ℝ) ^ 2
          * (ramanujan k (N : ℤ)).re) else 0) = singular N := by
  refine Complex.ofReal_injective ?_
  rw [Complex.ofReal_mul, ← f81_restricted_real_cast r N, f81_restricted_lim r N hr hN]

/-- The product of the local factors over the odd primes of `r` is at least `1/2`. -/
private lemma f81_half_le_prod_rprime_odd (r : ℕ) (hr : 1 ≤ r) :
    (1 / 2 : ℝ) ≤ ∏ p ∈ r.primeFactors.erase 2, (1 - 1 / ((p : ℝ) - 1) ^ 2) := by
  have hprime : ∀ p ∈ r.primeFactors.erase 2, Nat.Prime p := fun p hp =>
    Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
  have h3le : ∀ p ∈ r.primeFactors.erase 2, 3 ≤ p := by
    intro p hp
    have h2 : 2 ≤ p := (hprime p hp).two_le
    have hne : p ≠ 2 := Finset.ne_of_mem_erase hp
    omega
  have hinj : Set.InjOn (fun (p : ℕ) => p - 1) ↑(r.primeFactors.erase 2) := by
    intro a ha b hb h
    have ha3 : 3 ≤ a := h3le a ha
    have hb3 : 3 ≤ b := h3le b hb
    simp only at h
    omega
  have hprod : ∏ p ∈ r.primeFactors.erase 2, (1 - 1 / ((p : ℝ) - 1) ^ 2)
      = ∏ a ∈ (r.primeFactors.erase 2).image (fun (p : ℕ) => p - 1),
          (1 - 1 / ((a : ℝ)) ^ 2) := by
    rw [Finset.prod_image (g := fun (p : ℕ) => p - 1)
      (f := fun a : ℕ => 1 - 1 / ((a : ℝ)) ^ 2) hinj]
    refine Finset.prod_congr rfl (fun p hp => ?_)
    have hp1 : 1 ≤ p := by have := h3le p hp; omega
    rw [Nat.cast_sub hp1]
    norm_num
  rw [hprod]
  set U : Finset ℕ := (r.primeFactors.erase 2).image (fun (p : ℕ) => p - 1) with hU
  have hsub : U ⊆ Finset.Icc 2 r := by
    intro a ha
    rw [hU] at ha
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ha
    have h3 : 3 ≤ p := h3le p hp
    have hpr : p ≤ r := Nat.le_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
    simp only [Finset.mem_Icc]
    omega
  have h0I : ∀ a ∈ Finset.Icc 2 r, (0 : ℝ) ≤ 1 - 1 / ((a : ℝ)) ^ 2 := by
    intro a ha
    have ha2 : (2 : ℝ) ≤ (a : ℝ) := by
      have : 2 ≤ a := (Finset.mem_Icc.mp ha).1
      exact_mod_cast this
    have h4 : (1 : ℝ) ≤ (a : ℝ) ^ 2 := by nlinarith [ha2]
    have h5 : 1 / ((a : ℝ)) ^ 2 ≤ 1 := by
      rw [div_le_one (by positivity)]
      exact h4
    rw [sub_nonneg]
    exact h5
  have h1I : ∀ a ∈ Finset.Icc 2 r, (1 - 1 / ((a : ℝ)) ^ 2) ≤ 1 := by
    intro a ha
    have h : (0 : ℝ) ≤ 1 / ((a : ℝ)) ^ 2 := by positivity
    linarith
  have hfill : ∏ a ∈ Finset.Icc 2 r \ U, (1 - 1 / ((a : ℝ)) ^ 2) ≤ 1 := by
    refine prod_le_one_of_le_one (fun a ha => ?_) (fun a ha => ?_)
    · exact h0I a (Finset.mem_sdiff.mp ha).1
    · exact h1I a (Finset.mem_sdiff.mp ha).1
  have hUprod0 : (0 : ℝ) ≤ ∏ a ∈ U, (1 - 1 / ((a : ℝ)) ^ 2) :=
    Finset.prod_nonneg (fun a ha => h0I a (hsub ha))
  have hle : ∏ a ∈ Finset.Icc 2 r, (1 - 1 / ((a : ℝ)) ^ 2)
      ≤ ∏ a ∈ U, (1 - 1 / ((a : ℝ)) ^ 2) := by
    rw [← Finset.prod_sdiff hsub]
    have h := mul_le_mul_of_nonneg_right hfill hUprod0
    linarith [h]
  calc (1 / 2 : ℝ) ≤ ∏ a ∈ Finset.Icc 2 r, (1 - 1 / ((a : ℝ)) ^ 2) :=
        half_le_prod_one_sub_inv_sq (M := r) hr
    _ ≤ ∏ a ∈ U, (1 - 1 / ((a : ℝ)) ^ 2) := hle

/-- The product of the local factors of `𝔖(N)` over the primes of `r` is at least `1/2`. -/
private lemma f81_prod_primeFactors_ge_half (r N : ℕ) (hr : 1 ≤ r) (hEven : Even N)
    (hN2 : 2 ≤ N) :
    (1 / 2 : ℝ) ≤ ∏ p ∈ r.primeFactors,
      (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2) := by
  have hodd := f81_half_le_prod_rprime_odd r hr
  have hnn : ∀ p ∈ r.primeFactors.erase 2, (0 : ℝ) ≤ 1 - 1 / ((p : ℝ) - 1) ^ 2 := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp)
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpp.two_le
    have h4 : (1 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by nlinarith
    have h5 : 1 / ((p : ℝ) - 1) ^ 2 ≤ 1 := by
      rw [div_le_one (by linarith)]
      linarith
    linarith
  have hstep : ∏ p ∈ r.primeFactors.erase 2, (1 - 1 / ((p : ℝ) - 1) ^ 2)
      ≤ ∏ p ∈ r.primeFactors.erase 2,
          (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2) := by
    refine prod_le_prod' hnn (fun p hp => ?_)
    exact local_factor_ge N p
      (Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_erase hp))
      (Finset.ne_of_mem_erase hp)
  have hhalf : (1 / 2 : ℝ) ≤ ∏ p ∈ r.primeFactors.erase 2,
      (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2) := le_trans hodd hstep
  by_cases h2 : (2 : ℕ) ∈ r.primeFactors
  · rw [← Finset.mul_prod_erase r.primeFactors
      (fun p => 1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2) h2]
    have h2val : (1 + (ramanujan 2 (N : ℤ)).re / (((2 : ℕ) : ℝ) - 1) ^ 2) = 2 := by
      rw [show (((2 : ℕ) : ℝ) - 1) ^ 2 = 1 by norm_num, cN_two N hEven]
      norm_num
    rw [h2val]
    nlinarith [hhalf]
  · have hsame : r.primeFactors.erase 2 = r.primeFactors := by
      ext p
      simp only [Finset.mem_erase]
      exact ⟨fun h => h.2, fun h => ⟨fun hh => h2 (hh ▸ h), h⟩⟩
    rwa [hsame] at hhalf


/-- LEAF. Step 3, the conductor saving: for a primitive real character `χ` of conductor `r`,
the generalised series of the pair consisting of the trivial character of conductor one and
`χ` is bounded by `r / φ(r)²` times the modulus of the base case series of step 2, with an
absolute constant. This is the loss the twist by `χ` costs, and it is the whole content of
the first formula of 8.1 once step 2 has been used. -/
theorem facts81_saving :
    ∃ K : ℝ, ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → IsRealChar χ →
      ∀ N : ℕ, Even N → 2 ≤ N →
        ‖genSing chi1 χ N‖ ≤ K * ‖genSing chi1 chi1 N‖ * r / (Nat.totient r : ℝ) ^ 2 := by
  refine ⟨2, ?_⟩
  intro r hr0 χ hprim hreal N hEven hN2
  have hr : 0 < r := NeZero.pos r
  have hN1 : 1 ≤ N := by omega
  have hφpos : (0 : ℝ) < (Nat.totient r : ℝ) ^ 2 := by
    have hpos := Nat.totient_pos.mpr hr
    have h' : (0 : ℝ) < (Nat.totient r : ℝ) := by exact_mod_cast hpos
    positivity
  have hlim := f81_restricted_lim_real r N hr hN1
  have hCge : (1 / 2 : ℝ) ≤ ∏ p ∈ r.primeFactors,
      (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2) :=
    f81_prod_primeFactors_ge_half r N hr hEven hN2
  have hCpos : (0 : ℝ) < ∏ p ∈ r.primeFactors,
      (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2) :=
    lt_of_lt_of_le (by norm_num) hCge
  have hsingnn : 0 ≤ singular N := facts81_pos N hEven hN2
  have hSrval : (∑' k : ℕ, if Nat.Coprime k r then
        (((moebius k : ℤ) : ℝ) ^ 2 / (Nat.totient k : ℝ) ^ 2
          * (ramanujan k (N : ℤ)).re) else 0)
      = singular N / (∏ p ∈ r.primeFactors,
          (1 + (ramanujan p (N : ℤ)).re / ((p : ℝ) - 1) ^ 2)) := by
    rw [eq_div_iff hCpos.ne']
    linarith [hlim]
  have hSrnn : 0 ≤ (∑' k : ℕ, if Nat.Coprime k r then
        (((moebius k : ℤ) : ℝ) ^ 2 / (Nat.totient k : ℝ) ^ 2
          * (ramanujan k (N : ℤ)).re) else 0) := by
    rw [hSrval]
    positivity
  have hSrle : (∑' k : ℕ, if Nat.Coprime k r then
        (((moebius k : ℤ) : ℝ) ^ 2 / (Nat.totient k : ℝ) ^ 2
          * (ramanujan k (N : ℤ)).re) else 0) ≤ 2 * singular N := by
    rw [hSrval, div_le_iff₀ hCpos]
    nlinarith [hCge, hsingnn]
  have hSc : ‖(∑' k : ℕ, if Nat.Coprime k r then
      (moebius k : ℂ) ^ 2 * ramanujan k (N : ℤ) / (Nat.totient k : ℂ) ^ 2 else 0)‖
      ≤ 2 * singular N := by
    rw [f81_restricted_real_cast r N, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hSrnn]
    exact hSrle
  have hAq := f81_Aq_chi1_norm_le hreal hprim (N : ℤ)
  have hbpos : (0 : ℝ) < (r : ℝ) / (Nat.totient r : ℝ) ^ 2 :=
    div_pos (by exact_mod_cast hr) hφpos
  calc ‖genSing chi1 χ N‖
      = ‖Aq chi1 χ (N : ℤ) r‖ * ‖(∑' k : ℕ, if Nat.Coprime k r then
          (moebius k : ℂ) ^ 2 * ramanujan k (N : ℤ) / (Nat.totient k : ℂ) ^ 2 else 0)‖ := by
        rw [f81_genSing_chi1_split χ hreal N hN1, norm_mul]
    _ ≤ ((r : ℝ) / (Nat.totient r : ℝ) ^ 2) * (2 * singular N) :=
        mul_le_mul hAq hSc (norm_nonneg _) (le_of_lt hbpos)
    _ = 2 * ‖genSing chi1 chi1 N‖ * r / (Nat.totient r : ℝ) ^ 2 := by
        rw [facts81_base N hEven hN2, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hsingnn]
        ring

/-- LEAF. Step 4, the diagonal factorisation: for a primitive real character `χ` of conductor
`r` dividing the even `N`, the generalised series of the pair `(χ, χ)` is `χ(-1)` times the
base case series of step 2. The factor is the product of the two Gauss factors of `χ`, which
is `χ(-1) r`, against the modulus of the principal character, whose square cancels the
`φ(r)²`, and the primitive induced characters agree at every modulus that is a multiple of
`r`, which every surviving modulus is. -/
theorem facts81_diag (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive)
    (hreal : IsRealChar χ) (N : ℕ) (hEven : Even N) (hN2 : 2 ≤ N) (hdvd : r ∣ N) :
    genSing χ χ N = χ (-1) * genSing chi1 chi1 N := by
  rw [f81_diag_aux χ hprim hreal N hN2 hdvd, facts81_base N hEven hN2]

/-- The two formulas of 8.1, assembled from the four leaves above. The first one is step 2
rewritten into step 3 and then turned back into a real comparison by step 1; the second one
is step 4 followed by step 2. -/
theorem facts81_split : Facts81 := by
  obtain ⟨K, hK⟩ := facts81_saving
  refine ⟨⟨K, ?_⟩, ?_⟩
  · intro r hr0 χ hprim hreal N hEven hN2
    have hnorm : ‖((singular N : ℝ) : ℂ)‖ = singular N := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (facts81_pos N hEven hN2)]
    calc ‖genSing chi1 χ N‖
        ≤ K * ‖genSing chi1 chi1 N‖ * r / (Nat.totient r : ℝ) ^ 2 :=
          hK r χ hprim hreal N hEven hN2
      _ = K * singular N * r / (Nat.totient r : ℝ) ^ 2 := by
          rw [facts81_base N hEven hN2, hnorm]
  · intro r hr0 χ hprim hreal N hEven hN2 hdvd
    calc genSing χ χ N = χ (-1) * genSing chi1 chi1 N :=
          facts81_diag r χ hprim hreal N hEven hN2 hdvd
      _ = χ (-1) * singular N := by rw [facts81_base N hEven hN2]

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.facts81_split
