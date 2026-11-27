/-
P0069 Baker Harman Pintz 1997, page 8, display 2.7, which cites Vaughan reference 31,
The Hardy-Littlewood Method, Cambridge 1981, chapter 3, book page 34, display 3.23.
Split of `Section2MS.leaf_vaughan_323_512` into two cited LEAF pieces of Vaughan's
proof of 3.23 and a CONDITIONAL assembly theorem with the verbatim statement.
Burst burst-20261122 session S64. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp512a
import LeanLab.BHP1997.TotientTailS72

namespace LeanLab.BHP1997.Section2MS
open Classical

section V323Helpers
open Complex

private lemma v323_e512_add (x y : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * ((x + y : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * (y : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma v323_e512_nat_mul (k : ℕ) (x : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (((k : ℝ) * x : ℝ) : ℂ)) =
      (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, v323_e512_add, ih, pow_succ]

private lemma v323_e512_int_mul (k : ℤ) (x : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (((k : ℝ) * x : ℝ) : ℂ)) =
      (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ k := by
  have harg : (2 * (Real.pi : ℂ) * Complex.I * (((k : ℝ) * x : ℝ) : ℂ))
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) := by push_cast; ring
  rw [harg, Complex.exp_int_mul]

private lemma v323_e512_int_cast (k : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) : ℂ)) = 1 := by
  have h2 : Complex.exp (2 * Real.pi * Complex.I * ((1 : ℝ) : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    exact ⟨1, by push_cast; ring⟩
  have h := v323_e512_int_mul k 1
  rw [mul_one] at h
  rw [h, h2, one_zpow]

private lemma v323_two_pi_I_ne_zero512 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have h1 : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  exact mul_ne_zero h1 Complex.I_ne_zero

private lemma v323_e512_eq_one_iff {x : ℝ} :
    Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) = 1 ↔ ∃ k : ℤ, x = (k : ℝ) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    refine ⟨n, ?_⟩
    have hx : (2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ)
        = (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℝ) : ℂ) := by rw [hn]; push_cast; ring
    exact Complex.ofReal_injective (mul_left_cancel₀ v323_two_pi_I_ne_zero512 hx)
  · rintro ⟨k, rfl⟩
    exact v323_e512_int_cast k

/-- The orthogonality relation `Σ_{b<m} e(bk/m) = m` if `m ∣ k`, else `0`. -/
private lemma v323_e512_sum_orth {m : ℕ} (hm : 0 < m) (k : ℤ) :
    ∑ b ∈ Finset.range m, Complex.exp (2 * Real.pi * Complex.I * (((b : ℝ) * (k : ℝ)) / m : ℝ))
      = if (m : ℤ) ∣ k then (m : ℂ) else 0 := by
  have hmR : ((m : ℝ)) ≠ 0 := by positivity
  set c : ℂ := Complex.exp (2 * Real.pi * Complex.I * (((k : ℝ)) / m : ℝ)) with hc
  have hterm : ∀ b ∈ Finset.range m,
      Complex.exp (2 * Real.pi * Complex.I * (((b : ℝ) * (k : ℝ)) / m : ℝ)) = c ^ b := by
    intro b _
    have harg : ((b : ℝ) * (k : ℝ)) / m = (b : ℝ) * ((k : ℝ) / m) := by field_simp
    rw [harg, v323_e512_nat_mul]
  rw [Finset.sum_congr rfl hterm]
  have hcm : c ^ m = 1 := by
    have h1 : c ^ m = Complex.exp (2 * Real.pi * Complex.I * (((m : ℝ) * ((k : ℝ) / m) : ℝ) : ℂ)) := by
      rw [hc]; exact (v323_e512_nat_mul m ((k : ℝ) / m)).symm
    rw [h1, mul_div_cancel₀ (k : ℝ) hmR, v323_e512_int_cast]
  have hiff : c = 1 ↔ (m : ℤ) ∣ k := by
    rw [hc, v323_e512_eq_one_iff]
    constructor
    · rintro ⟨j, hj⟩
      have h2 : (k : ℝ) = (j : ℝ) * (m : ℝ) := by
        rw [div_eq_iff hmR] at hj
        linarith [hj]
      have h3 : k = j * (m : ℤ) := by exact_mod_cast h2
      exact ⟨j, by rw [h3]; ring⟩
    · rintro ⟨j, rfl⟩
      refine ⟨j, ?_⟩
      push_cast
      field_simp
  by_cases h1 : c = 1
  · rw [ite_eq_left (hiff.mp h1)]
    simp [h1]
  · rw [ite_eq_right (fun h => h1 (hiff.mpr h))]
    rw [geom_sum_eq h1 m, hcm]
    simp

private lemma v323_filter_Icc_eq_range512 {q : ℕ} (hq : 2 ≤ q) :
    (Finset.Icc 1 q).filter (fun r => Nat.Coprime r q) =
      (Finset.range q).filter (fun r => Nat.Coprime r q) := by
  ext r
  simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
  constructor
  · rintro ⟨⟨h1, h2⟩, hc⟩
    refine ⟨?_, hc⟩
    rcases lt_or_eq_of_le h2 with h | h
    · exact h
    · exfalso
      subst h
      simp only [Nat.Coprime, Nat.gcd_self] at hc
      omega
  · rintro ⟨h1, hc⟩
    refine ⟨⟨?_, le_of_lt h1⟩, hc⟩
    rcases Nat.eq_zero_or_pos r with h | h
    · exfalso
      subst h
      simp only [Nat.Coprime, Nat.gcd_zero_left] at hc
      omega
    · exact h

private lemma v323_ramanujan512_one (N : ℕ) : ramanujan512 1 N = 1 := by
  unfold ramanujan512
  have h : (Finset.Icc 1 1).filter (fun r => Nat.Coprime r 1) = {1} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h1, h2⟩, -⟩
      omega
    · rintro rfl
      exact ⟨⟨le_rfl, le_rfl⟩, Nat.coprime_one_right 1⟩
  rw [h, Finset.sum_singleton]
  rw [fourier_coe_apply, Complex.exp_eq_one_iff]
  exact ⟨-(N : ℤ), by push_cast; ring⟩

private lemma v323_ramanujan512_exp_range (q N : ℕ) (hq : 2 ≤ q) :
    ramanujan512 q N =
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * ((-(N : ℤ) : ℤ) : ℝ)) / q : ℝ)) := by
  unfold ramanujan512
  rw [v323_filter_Icc_eq_range512 hq]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

private lemma v323_sum_moebius_divisors512 (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) = if n = 1 then 1 else 0 := by
  have h := ArithmeticFunction.coe_mul_zeta_apply (f := ArithmeticFunction.moebius) (x := n)
  rw [ArithmeticFunction.moebius_mul_coe_zeta] at h
  rw [← h]
  exact ArithmeticFunction.one_apply

private lemma v323_divisors_filter_dvd_eq_gcd512 {q a : ℕ} (hq : q ≠ 0) :
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

private lemma v323_indicator_coprime512 {q : ℕ} (hq : q ≠ 0) (a : ℕ) :
    (if a.gcd q = 1 then (1:ℂ) else 0)
      = ∑ d ∈ q.divisors, (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) := by
  rw [← Finset.sum_filter, v323_divisors_filter_dvd_eq_gcd512 hq]
  have h := congrArg (fun z : ℤ => (z : ℂ)) (v323_sum_moebius_divisors512 (a.gcd q))
  push_cast at h
  exact h.symm

private lemma v323_sum_range_filter_dvd512 {q d : ℕ} (hd : 0 < d) (hdq : d ∣ q) (g : ℕ → ℂ) :
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

/-- The general exponential sum as a divisor sum. -/
private lemma v323_ramanujan_exp_dvd (q : ℕ) (k : ℤ) (hq : 2 ≤ q) :
    (∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * (k : ℝ)) / q : ℝ)))
      = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
        (if ((q / d : ℕ) : ℤ) ∣ k then ((q / d : ℕ) : ℂ) else 0) := by
  have hq0 : q ≠ 0 := by omega
  have hqR : ((q : ℝ)) ≠ 0 := by positivity
  have hfilter : (Finset.range q).filter (fun a => Nat.Coprime a q)
      = (Finset.range q).filter (fun a => a.gcd q = 1) :=
    Finset.filter_congr (fun a _ => Nat.coprime_iff_gcd_eq_one)
  rw [hfilter, Finset.sum_filter]
  have hstep1 : ∑ a ∈ Finset.range q,
      (if a.gcd q = 1 then Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * (k : ℝ)) / q : ℝ)) else 0)
      = ∑ a ∈ Finset.range q,
          (∑ d ∈ q.divisors, (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0))
            * Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * (k : ℝ)) / q : ℝ)) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    have h1 : (if a.gcd q = 1 then (1:ℂ) else 0)
          * Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * (k : ℝ)) / q : ℝ))
        = (if a.gcd q = 1 then
            Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * (k : ℝ)) / q : ℝ)) else 0) := by
      by_cases h : a.gcd q = 1 <;> simp [h]
    rw [← h1, v323_indicator_coprime512 hq0 a]
  rw [hstep1]
  have hstep2 : ∀ a ∈ Finset.range q,
      (∑ d ∈ q.divisors, (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0))
        * Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * (k : ℝ)) / q : ℝ))
      = ∑ d ∈ q.divisors,
          (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0)
            * Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * (k : ℝ)) / q : ℝ)) := by
    intro a _
    rw [Finset.sum_mul]
  rw [Finset.sum_congr rfl hstep2, Finset.sum_comm]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  have hdvd : d ∣ q := (Nat.mem_divisors.mp hd).1
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdvd (by omega)
  have hm0 : 0 < q / d := Nat.div_pos (Nat.le_of_dvd (by omega) hdvd) hd0
  have hfac : ∑ a ∈ Finset.range q,
        (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0)
          * Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * (k : ℝ)) / q : ℝ))
      = ∑ a ∈ Finset.range q,
          (if d ∣ a then (ArithmeticFunction.moebius d : ℂ)
            * Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * (k : ℝ)) / q : ℝ)) else 0) := by
    refine Finset.sum_congr rfl (fun a _ => ?_)
    by_cases h : d ∣ a <;> simp [h]
  rw [hfac, ← Finset.sum_filter, v323_sum_range_filter_dvd512 hd0 hdvd, ← Finset.mul_sum]
  congr 1
  have hqd : d * (q / d) = q := Nat.mul_div_cancel' hdvd
  have harg : ∀ b : ℕ,
      Complex.exp (2 * Real.pi * Complex.I * (((d * b : ℕ) : ℝ) * (k : ℝ) / q : ℝ))
      = Complex.exp (2 * Real.pi * Complex.I *
          (((b : ℝ) * (k : ℝ)) / (((q / d : ℕ)) : ℝ) : ℝ)) := by
    intro b
    congr 1
    rw [Nat.cast_div hdvd (by positivity : ((d : ℕ) : ℝ) ≠ 0), ← hqd]
    push_cast
    have hdR : ((d : ℕ) : ℝ) ≠ 0 := by positivity
    have hmR : (((q / d : ℕ)) : ℝ) ≠ 0 := by positivity
    field_simp
  rw [Finset.sum_congr rfl (fun b _ => harg b), v323_e512_sum_orth hm0 k]

/-- The Ramanujan sum `c_q(N)` as an exact divisor sum. -/
private lemma v323_ramanujan512_dvd (q N : ℕ) (hq : 2 ≤ q) :
    ramanujan512 q N = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
      (if ((q / d : ℕ) : ℤ) ∣ (N : ℤ) then ((q / d : ℕ) : ℂ) else 0) := by
  rw [v323_ramanujan512_exp_range q N hq, v323_ramanujan_exp_dvd q (-(N : ℤ)) hq]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hd : (((q / d : ℕ)) : ℤ) ∣ -(N : ℤ) ↔ (((q / d : ℕ)) : ℤ) ∣ (N : ℤ) := Int.dvd_neg
  by_cases h : (((q / d : ℕ)) : ℤ) ∣ (N : ℤ)
  · simp only [if_pos (hd.mpr h), if_pos h]
  · simp only [if_neg (fun hh => h (hd.mp hh)), if_neg h]

open scoped ArithmeticFunction.Moebius

/-- The real divisor form of `c_q(N)`: `Σ_{d ∣ q} (q/d)·μ(d)` restricted to `(q/d) ∣ N`. -/
private lemma v323_c512_real_form (q N : ℕ) (hq : 1 ≤ q) :
    ramanujan512 q N =
      ((∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) : ℝ) : ℂ) := by
  rcases eq_or_lt_of_le hq with h | h
  · subst h
    rw [v323_ramanujan512_one]
    have h1 : (∑ d ∈ (1 : ℕ).divisors, (if (1 / d : ℕ) ∣ N then ((1 / d : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)) = 1 := by
      rw [Nat.divisors_one, Finset.sum_singleton]
      norm_num
    rw [h1]
    norm_num
  · have h2 : 2 ≤ q := h
    rw [v323_ramanujan512_dvd q N h2, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    by_cases hd : ((q / d : ℕ) : ℤ) ∣ (N : ℤ)
    · rw [if_pos hd, if_pos (Int.natCast_dvd_natCast.mp hd)]
      push_cast
      ring
    · rw [if_neg hd, if_neg (fun hh => hd (Int.natCast_dvd_natCast.mpr hh))]
      push_cast
      ring

/-- Reindex the divisor sum: the Möbius index can be put on `q / d`. -/
private lemma v323_c512_conv_form (q N : ℕ) (hq : 0 < q) :
    (∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ))
      = ∑ e ∈ q.divisors, (if e ∣ N then (e : ℝ) else 0) *
        ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ) := by
  have hq0 : q ≠ 0 := hq.ne'
  refine Finset.sum_nbij' (fun d => q / d) (fun e => q / e) ?_ ?_ ?_ ?_ ?_
  · intro d hd
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hd), hq0⟩
  · intro e he
    exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors he), hq0⟩
  · intro d hd
    exact Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hq0
  · intro e he
    exact Nat.div_div_self (Nat.dvd_of_mem_divisors he) hq0
  · intro d hd
    rw [Nat.div_div_self (Nat.dvd_of_mem_divisors hd) hq0]

/-- The weight `d ↦ d · 1_{d ∣ N}` is multiplicative. -/
private lemma v323_gDiv512_mult (N : ℕ) (g : ArithmeticFunction ℝ)
    (hg : ∀ d, g d = if d ∣ N then (d : ℝ) else 0) : g.IsMultiplicative := by
  refine ⟨?_, fun {a b} hab => ?_⟩
  · rw [hg]; simp
  · rw [hg, hg, hg]
    by_cases ha : a ∣ N
    · by_cases hb : b ∣ N
      · rw [if_pos (hab.mul_dvd_of_dvd_of_dvd ha hb), if_pos ha, if_pos hb]
        push_cast
        ring
      · rw [if_neg (fun h => hb (dvd_trans (dvd_mul_left b a) h)), if_neg hb, mul_zero]
    · rw [if_neg (fun h => ha (dvd_trans (dvd_mul_right a b) h)), if_neg ha, zero_mul]

/-- The Ramanujan divisor sum as the Dirichlet convolution `(d ↦ d·1_{d ∣ N}) * μ`. -/
private lemma v323_conv512 (N : ℕ) (g : ArithmeticFunction ℝ)
    (hg : ∀ d, g d = if d ∣ N then (d : ℝ) else 0) (q : ℕ) :
    (g * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) q
      = ∑ e ∈ q.divisors, (if e ∣ N then ((e : ℕ) : ℝ) else 0) *
          ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ) := by
  rw [ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal
      (fun a b => g a * (ArithmeticFunction.moebius : ArithmeticFunction ℝ) b)]
  refine Finset.sum_congr rfl (fun e _ => ?_)
  rw [hg, ArithmeticFunction.intCoe_apply]

/-- The real Ramanujan divisor sum is multiplicative in the modulus. -/
private lemma v323_c512_real_mul {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 0 < m) (hn : 0 < n) (N : ℕ) :
    (∑ d ∈ (m * n).divisors,
        (if (m * n / d : ℕ) ∣ N then ((m * n / d : ℕ) : ℝ) else 0) *
          ((ArithmeticFunction.moebius d : ℤ) : ℝ))
      = (∑ d ∈ m.divisors,
          (if (m / d : ℕ) ∣ N then ((m / d : ℕ) : ℝ) else 0) *
            ((ArithmeticFunction.moebius d : ℤ) : ℝ)) *
        (∑ d ∈ n.divisors,
          (if (n / d : ℕ) ∣ N then ((n / d : ℕ) : ℝ) else 0) *
            ((ArithmeticFunction.moebius d : ℤ) : ℝ)) := by
  set g : ArithmeticFunction ℝ := ⟨fun d => if d ∣ N then (d : ℝ) else 0, by simp⟩ with hgdef
  have hg : ∀ d, g d = if d ∣ N then (d : ℝ) else 0 := fun d => rfl
  have hmul : (g * (ArithmeticFunction.moebius : ArithmeticFunction ℝ)).IsMultiplicative :=
    (v323_gDiv512_mult N g hg).mul ArithmeticFunction.isMultiplicative_moebius.intCast
  rw [v323_c512_conv_form (m * n) N (Nat.mul_pos hm hn), v323_c512_conv_form m N hm,
    v323_c512_conv_form n N hn, ← v323_conv512 N g hg (m * n), ← v323_conv512 N g hg m,
    ← v323_conv512 N g hg n]
  exact hmul.map_mul_of_coprime hmn

/-- The Ramanujan sum at a prime. -/
private lemma v323_c512_prime {p : ℕ} (hp : p.Prime) (N : ℕ) :
    (∑ d ∈ p.divisors, (if (p / d : ℕ) ∣ N then ((p / d : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ))
      = if p ∣ N then ((p : ℝ) - 1) else -1 := by
  rw [hp.divisors, Finset.sum_insert (by simp [hp.ne_one.symm]), Finset.sum_singleton]
  have hμ1 : ((ArithmeticFunction.moebius 1 : ℤ) : ℝ) = 1 := by
    rw [ArithmeticFunction.moebius_apply_one]; norm_num
  have hμp : ((ArithmeticFunction.moebius p : ℤ) : ℝ) = -1 := by
    rw [ArithmeticFunction.moebius_apply_prime hp]; norm_num
  rw [hμ1, hμp, Nat.div_one, Nat.div_self hp.pos, if_pos (one_dvd N)]
  by_cases h : p ∣ N
  · rw [if_pos h, if_pos h]
    push_cast
    ring
  · rw [if_neg h, if_neg h]
    ring

/-- The real Ramanujan divisor sum `Σ_{d ∣ q} [q/d ∣ N] (q/d) μ(d)` has absolute value
`φ((q,N))` at every squarefree `q`: Vaughan 1981 chapter 3, display 3.14 evaluation
`c_q = μ(q/(q,N)) φ((q,N))`, by multiplicativity in `q` and the prime case. -/
private lemma v323_abs_c512_sqfree (N : ℕ) : ∀ q : ℕ, Squarefree q →
    |∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)| = (Nat.totient (Nat.gcd q N) : ℝ) := by
  intro q
  induction q using Nat.recOnPosPrimePosCoprime with
  | prime_pow p n hp hn =>
    intro hsq
    have hn1 : n = 1 := by
      by_contra hne
      have h2 : 2 ≤ n := by omega
      have hdvd : p * p ∣ p ^ n := by
        rw [← pow_two]; exact pow_dvd_pow p h2
      exact hp.one_lt.ne' (Nat.isUnit_iff.mp (hsq p hdvd))
    subst hn1
    rw [pow_one, v323_c512_prime hp N]
    by_cases h : p ∣ N
    · rw [if_pos h, Nat.gcd_eq_left h, Nat.totient_prime hp,
        Nat.cast_sub hp.one_le, Nat.cast_one]
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_le
      exact abs_of_nonneg (by linarith)
    · rw [if_neg h, ((Nat.Prime.coprime_iff_not_dvd hp).mpr h).gcd_eq_one]
      simp
  | zero => intro hsq; exact absurd hsq not_squarefree_zero
  | one =>
    intro _
    rw [Nat.divisors_one, Finset.sum_singleton]
    simp
  | coprime a b ha hb hab iha ihb =>
    intro hsq
    have hsa : Squarefree a := Squarefree.of_mul_left hsq
    have hsb : Squarefree b := Squarefree.of_mul_right hsq
    rw [v323_c512_real_mul hab (by omega) (by omega) N, abs_mul, iha hsa, ihb hsb]
    have hg : Nat.gcd (a * b) N = Nat.gcd a N * Nat.gcd b N := by
      rw [Nat.gcd_comm, Nat.Coprime.gcd_mul N hab, Nat.gcd_comm N a, Nat.gcd_comm N b]
    have hcop : Nat.Coprime (Nat.gcd a N) (Nat.gcd b N) :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left a N)
        (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left b N) hab)
    rw [hg, Nat.totient_mul hcop]
    push_cast
    ring

end V323Helpers

/-- LEAF: Vaughan 1981 chapter 3, display 3.14 and the evaluation of the Ramanujan sum used
in the proof of display 3.23 on book page 34: for squarefree q the Ramanujan sum
c_q(-m) = Σ_{(a,q)=1} e(-am/q) equals μ(q/(q,m)) φ((q,m)), so its absolute value is
φ((q,m)). Class EASY: the lab's private `c512_real_form` in Decomp512a writes c_q as
Σ_{d|q} [q/d ∣ m] (q/d) μ(d), and for squarefree q = g r with g = (q,m) this is
μ(r) Σ_{e|g} e μ(g/e) = μ(r) φ(g). -/
theorem leaf_ramanujan_sqfree_norm512 (q N : ℕ) (hq : Squarefree q) :
    ‖ramanujan512 q N‖ ≤ (Nat.totient (Nat.gcd q N) : ℝ) := by
  have hq0 : 1 ≤ q := Nat.pos_of_ne_zero (fun h => not_squarefree_zero (h ▸ hq))
  rw [v323_c512_real_form q N hq0, Complex.norm_real, Real.norm_eq_abs,
    v323_abs_c512_sqfree N q hq]

/-- LEAF: Vaughan 1981 chapter 3, book page 34, the elementary fact printed under display
3.23: Σ_{q>Z} φ(q)^{-2} ≪ Z^{-1}, together with the convergence of Σ_q φ(q)^{-2}, which
gives the bound min(Z^{-1}, 1) for every Z > 0, uniformly in the upper cutoff R.
Class MEDIUM: from Σ_{q≤R} (q/φ(q))² ≪ R, which follows from
q/φ(q) = Σ_{d|q} μ(d)²/φ(d), and partial summation. PROVED in `TotientTailS72`,
session S72, by an elementary Euler product argument. -/
theorem leaf_totient_sq_tail512 :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Z : ℝ, 0 < Z → ∀ R : ℕ,
      ∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => Z < (r : ℝ)),
          1 / (Nat.totient r : ℝ) ^ 2 ≤ K * min (1 / Z) 1 :=
  TotientTailS72.leaf_totient_sq_tail512

/-- Vaughan 1981 display 3.23 at m = N, verbatim statement of
`Section2MS.leaf_vaughan_323_512`, CONDITIONAL ON the two LEAFs above. The proof is Vaughan's:
drop the non squarefree q, bound the Ramanujan sum by φ((q,N)), sort q by g = (q,N),
write q = g r with (g,r) = 1 so φ(q) = φ(g) φ(r), and sum the tail over r > X/g. -/
theorem leaf_vaughan_323_512_of_leaves :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N → ∀ X : ℝ, 0 < X → ∀ M : ℕ,
      ‖∑ q ∈ Finset.Ioc ⌊X⌋₊ M,
          (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
            ramanujan512 q N‖ ≤
        K * ∑ d ∈ N.divisors,
          (ArithmeticFunction.moebius d : ℝ) ^ 2 / (Nat.totient d : ℝ) *
            min ((d : ℝ) / X) 1 := by
  obtain ⟨K, hK0, hK⟩ := leaf_totient_sq_tail512
  refine ⟨K, hK0, fun N hN X hX M => ?_⟩
  set S := Finset.Ioc ⌊X⌋₊ M with hS
  let f : ℕ → ℝ := fun q =>
    if Squarefree q then (Nat.totient (Nat.gcd q N) : ℝ) / (Nat.totient q : ℝ) ^ 2 else 0
  have hf0 : ∀ q, 0 ≤ f q := by
    intro q; simp only [f]; split_ifs <;> positivity
  -- step 1: triangle inequality and the Ramanujan bound
  have step1 : ‖∑ q ∈ S, (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
      ramanujan512 q N‖ ≤ ∑ q ∈ S, f q := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    by_cases hq : Squarefree q
    · have hmu : (ArithmeticFunction.moebius q : ℂ) ^ 2 = 1 := by
        have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hq
        exact_mod_cast this
      simp only [f, if_pos hq, hmu, norm_mul, norm_div, norm_one, norm_pow,
        Complex.norm_natCast]
      rw [one_div_mul_eq_div]
      exact div_le_div_of_nonneg_right (leaf_ramanujan_sqfree_norm512 q N hq) (by positivity)
    · have hmu : (ArithmeticFunction.moebius q : ℂ) = 0 := by
        have := ArithmeticFunction.moebius_eq_zero_of_not_squarefree hq
        exact_mod_cast this
      simp [f, hq]
  -- step 2: sort by g = gcd q N
  have hN0 : N ≠ 0 := by omega
  have hmaps : ∀ q ∈ S, Nat.gcd q N ∈ N.divisors := by
    intro q _
    exact Nat.mem_divisors.2 ⟨Nat.gcd_dvd_right q N, hN0⟩
  have step2 : ∑ q ∈ S, f q =
      ∑ g ∈ N.divisors, ∑ q ∈ S.filter (fun q => Nat.gcd q N = g), f q :=
    (Finset.sum_fiberwise_of_maps_to hmaps f).symm
  -- step 3: each fiber
  have step3 : ∀ g ∈ N.divisors, ∑ q ∈ S.filter (fun q => Nat.gcd q N = g), f q ≤
      K * ((ArithmeticFunction.moebius g : ℝ) ^ 2 / (Nat.totient g : ℝ) *
        min ((g : ℝ) / X) 1) := by
    intro g hg
    have hgpos : 0 < g := Nat.pos_of_mem_divisors hg
    by_cases hsg : Squarefree g
    · have hmu : (ArithmeticFunction.moebius g : ℝ) ^ 2 = 1 := by
        have := ArithmeticFunction.moebius_sq_eq_one_of_squarefree hsg
        exact_mod_cast this
      rw [hmu]
      have hphig : (0 : ℝ) < Nat.totient g := by exact_mod_cast Nat.totient_pos.2 hgpos
      let h : ℕ → ℝ := fun r => 1 / (Nat.totient r : ℝ) ^ 2
      have hle : ∀ q ∈ S.filter (fun q => Nat.gcd q N = g),
          f q ≤ 1 / (Nat.totient g : ℝ) * h (q / g) := by
        intro q hq
        rw [Finset.mem_filter] at hq
        by_cases hsq : Squarefree q
        · have hgq : g ∣ q := hq.2 ▸ Nat.gcd_dvd_left q N
          have hqe : q = g * (q / g) := (Nat.mul_div_cancel' hgq).symm
          have hcop : Nat.Coprime g (q / g) :=
            Nat.coprime_of_squarefree_mul (hqe ▸ hsq)
          have htot : (Nat.totient q : ℝ) =
              (Nat.totient g : ℝ) * (Nat.totient (q / g) : ℝ) := by
            conv_lhs => rw [hqe]
            rw [Nat.totient_mul hcop]; push_cast; ring
          simp only [f, h, if_pos hsq, hq.2, htot]
          have hr : (0 : ℝ) < Nat.totient (q / g) := by
            have hq0 : 0 < q := by
              rcases Nat.eq_zero_or_pos q with h0 | h0
              · exact absurd (h0 ▸ hsq) not_squarefree_zero
              · exact h0
            have : 0 < q / g := Nat.div_pos (Nat.le_of_dvd hq0 hgq) hgpos
            exact_mod_cast Nat.totient_pos.2 this
          field_simp
          ring_nf
          exact le_refl _
        · simp only [f, if_neg hsq]
          simp only [h]; positivity
      refine (Finset.sum_le_sum hle).trans ?_
      rw [← Finset.mul_sum]
      have hinj : Set.InjOn (fun q => q / g) ↑(S.filter (fun q => Nat.gcd q N = g)) := by
        intro a ha b hb hab
        simp only [Finset.coe_filter, Set.mem_setOf_eq] at ha hb
        have ha' : g ∣ a := ha.2 ▸ Nat.gcd_dvd_left a N
        have hb' : g ∣ b := hb.2 ▸ Nat.gcd_dvd_left b N
        simp only at hab
        rw [← Nat.mul_div_cancel' ha', ← Nat.mul_div_cancel' hb', hab]
      rw [← Finset.sum_image (f := h) hinj]
      have hsub : (S.filter (fun q => Nat.gcd q N = g)).image (fun q => q / g) ⊆
          (Finset.Icc 1 M).filter (fun r : ℕ => X / g < (r : ℝ)) := by
        intro r hr
        rw [Finset.mem_image] at hr
        obtain ⟨q, hq, rfl⟩ := hr
        rw [Finset.mem_filter, hS, Finset.mem_Ioc] at hq
        have hgq : g ∣ q := hq.2 ▸ Nat.gcd_dvd_left q N
        have hXq : X < (q : ℝ) := Nat.lt_of_floor_lt hq.1.1
        have hq0 : 0 < q := by
          have : (0 : ℝ) < q := lt_trans hX hXq
          exact_mod_cast this
        rw [Finset.mem_filter, Finset.mem_Icc]
        refine ⟨⟨Nat.div_pos (Nat.le_of_dvd hq0 hgq) hgpos,
          le_trans (Nat.div_le_self q g) hq.1.2⟩, ?_⟩
        have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
        rw [div_lt_iff₀ hgR]
        have : ((q / g : ℕ) : ℝ) * g = q := by
          rw [← Nat.cast_mul, Nat.div_mul_cancel hgq]
        rw [this]; exact hXq
      have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
      have htail := hK (X / g) (div_pos hX hgR) M
      have hmono := Finset.sum_le_sum_of_subset_of_nonneg (f := h) hsub
        (fun r _ _ => by simp only [h]; positivity)
      rw [one_div_div] at htail
      calc 1 / (Nat.totient g : ℝ) * ∑ r ∈ (S.filter (fun q => Nat.gcd q N = g)).image
              (fun q => q / g), h r
          ≤ 1 / (Nat.totient g : ℝ) * (K * min ((g : ℝ) / X) 1) := by
            apply mul_le_mul_of_nonneg_left (hmono.trans htail)
            positivity
        _ = K * (1 / (Nat.totient g : ℝ) * min ((g : ℝ) / X) 1) := by ring
    · have hzero : ∀ q ∈ S.filter (fun q => Nat.gcd q N = g), f q = 0 := by
        intro q hq
        rw [Finset.mem_filter] at hq
        have hgq : g ∣ q := hq.2 ▸ Nat.gcd_dvd_left q N
        have hsq : ¬ Squarefree q := fun hs => hsg (Squarefree.squarefree_of_dvd hgq hs)
        simp only [f, if_neg hsq]
      rw [Finset.sum_eq_zero hzero]
      apply mul_nonneg hK0
      positivity
  calc _ ≤ ∑ q ∈ S, f q := step1
    _ = _ := step2
    _ ≤ ∑ g ∈ N.divisors, K * ((ArithmeticFunction.moebius g : ℝ) ^ 2 /
          (Nat.totient g : ℝ) * min ((g : ℝ) / X) 1) := Finset.sum_le_sum step3
    _ = _ := by rw [Finset.mul_sum]

/-- Verbatim check: the assembly has exactly the type of `leaf_vaughan_323_512`. -/
example : type_of% leaf_vaughan_323_512 := leaf_vaughan_323_512_of_leaves

end LeanLab.BHP1997.Section2MS
