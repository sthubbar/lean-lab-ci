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

/-- LEAF. Step 3, the conductor saving: for a primitive real character `χ` of conductor `r`,
the generalised series of the pair consisting of the trivial character of conductor one and
`χ` is bounded by `r / φ(r)²` times the modulus of the base case series of step 2, with an
absolute constant. This is the loss the twist by `χ` costs, and it is the whole content of
the first formula of 8.1 once step 2 has been used. -/
theorem facts81_saving :
    ∃ K : ℝ, ∀ (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r), χ.IsPrimitive → IsRealChar χ →
      ∀ N : ℕ, Even N → 2 ≤ N →
        ‖genSing chi1 χ N‖ ≤ K * ‖genSing chi1 chi1 N‖ * r / (Nat.totient r : ℝ) ^ 2 := by
  sorry

/-- LEAF. Step 4, the diagonal factorisation: for a primitive real character `χ` of conductor
`r` dividing the even `N`, the generalised series of the pair `(χ, χ)` is `χ(-1)` times the
base case series of step 2. The factor is the product of the two Gauss factors of `χ`, which
is `χ(-1) r`, against the modulus of the principal character, whose square cancels the
`φ(r)²`, and the primitive induced characters agree at every modulus that is a multiple of
`r`, which every surviving modulus is. -/
theorem facts81_diag (r : ℕ) [NeZero r] (χ : DirichletCharacter ℂ r) (hprim : χ.IsPrimitive)
    (hreal : IsRealChar χ) (N : ℕ) (hEven : Even N) (hN2 : 2 ≤ N) (hdvd : r ∣ N) :
    genSing χ χ N = χ (-1) * genSing chi1 chi1 N := by
  sorry

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
