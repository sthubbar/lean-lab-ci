/-
P0069 Baker Harman Pintz 1997, page 8, display 2.7, citing Vaughan reference 31,
The Hardy-Littlewood Method, Cambridge 1981, chapter 3, display 3.14 and book page 34.
The Ramanujan sum c_q of P0069 page 6, `ramanujan512`, satisfies |c_q(N)| = φ((q,N))
for squarefree q. The private helpers below are copies of the private lemmas of
`Decomp512a`, renamed with suffix S72, since private lemmas cannot be used from another
file. Burst burst-20261122 session S72. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp512a

namespace LeanLab.BHP1997.Section2MS
open Classical Complex

private lemma e512_addS72 (x y : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * ((x + y : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * (y : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma e512_nat_mulS72 (k : ℕ) (x : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (((k : ℝ) * x : ℝ) : ℂ)) =
      (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, e512_addS72, ih, pow_succ]

private lemma e512_int_mulS72 (k : ℤ) (x : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (((k : ℝ) * x : ℝ) : ℂ)) =
      (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ k := by
  have harg : (2 * (Real.pi : ℂ) * Complex.I * (((k : ℝ) * x : ℝ) : ℂ))
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) := by push_cast; ring
  rw [harg, Complex.exp_int_mul]

private lemma e512_int_castS72 (k : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) : ℂ)) = 1 := by
  have h2 : Complex.exp (2 * Real.pi * Complex.I * ((1 : ℝ) : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    exact ⟨1, by push_cast; ring⟩
  have h := e512_int_mulS72 k 1
  rw [mul_one] at h
  rw [h, h2, one_zpow]

private lemma two_pi_I_ne_zero512S72 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have h1 : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  exact mul_ne_zero h1 Complex.I_ne_zero

private lemma e512_eq_one_iffS72 {x : ℝ} :
    Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) = 1 ↔ ∃ k : ℤ, x = (k : ℝ) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    refine ⟨n, ?_⟩
    have hx : (2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ)
        = (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℝ) : ℂ) := by rw [hn]; push_cast; ring
    exact Complex.ofReal_injective (mul_left_cancel₀ two_pi_I_ne_zero512S72 hx)
  · rintro ⟨k, rfl⟩
    exact e512_int_castS72 k

/-- The orthogonality relation `Σ_{b<m} e(bk/m) = m` if `m ∣ k`, else `0`. -/
private lemma e512_sum_orthS72 {m : ℕ} (hm : 0 < m) (k : ℤ) :
    ∑ b ∈ Finset.range m, Complex.exp (2 * Real.pi * Complex.I * (((b : ℝ) * (k : ℝ)) / m : ℝ))
      = if (m : ℤ) ∣ k then (m : ℂ) else 0 := by
  have hmR : ((m : ℝ)) ≠ 0 := by positivity
  set c : ℂ := Complex.exp (2 * Real.pi * Complex.I * (((k : ℝ)) / m : ℝ)) with hc
  have hterm : ∀ b ∈ Finset.range m,
      Complex.exp (2 * Real.pi * Complex.I * (((b : ℝ) * (k : ℝ)) / m : ℝ)) = c ^ b := by
    intro b _
    have harg : ((b : ℝ) * (k : ℝ)) / m = (b : ℝ) * ((k : ℝ) / m) := by field_simp
    rw [harg, e512_nat_mulS72]
  rw [Finset.sum_congr rfl hterm]
  have hcm : c ^ m = 1 := by
    have h1 : c ^ m = Complex.exp (2 * Real.pi * Complex.I * (((m : ℝ) * ((k : ℝ) / m) : ℝ) : ℂ)) := by
      rw [hc]; exact (e512_nat_mulS72 m ((k : ℝ) / m)).symm
    rw [h1, mul_div_cancel₀ (k : ℝ) hmR, e512_int_castS72]
  have hiff : c = 1 ↔ (m : ℤ) ∣ k := by
    rw [hc, e512_eq_one_iffS72]
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

private lemma filter_Icc_eq_range512S72 {q : ℕ} (hq : 2 ≤ q) :
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

private lemma ramanujan512_oneS72 (N : ℕ) : ramanujan512 1 N = 1 := by
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

private lemma ramanujan512_exp_rangeS72 (q N : ℕ) (hq : 2 ≤ q) :
    ramanujan512 q N =
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * ((-(N : ℤ) : ℤ) : ℝ)) / q : ℝ)) := by
  unfold ramanujan512
  rw [filter_Icc_eq_range512S72 hq]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

private lemma sum_moebius_divisors512S72 (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) = if n = 1 then 1 else 0 := by
  have h := ArithmeticFunction.coe_mul_zeta_apply (f := ArithmeticFunction.moebius) (x := n)
  rw [ArithmeticFunction.moebius_mul_coe_zeta] at h
  rw [← h]
  exact ArithmeticFunction.one_apply

private lemma divisors_filter_dvd_eq_gcd512S72 {q a : ℕ} (hq : q ≠ 0) :
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

private lemma indicator_coprime512S72 {q : ℕ} (hq : q ≠ 0) (a : ℕ) :
    (if a.gcd q = 1 then (1:ℂ) else 0)
      = ∑ d ∈ q.divisors, (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) := by
  rw [← Finset.sum_filter, divisors_filter_dvd_eq_gcd512S72 hq]
  have h := congrArg (fun z : ℤ => (z : ℂ)) (sum_moebius_divisors512S72 (a.gcd q))
  push_cast at h
  exact h.symm

private lemma sum_range_filter_dvd512S72 {q d : ℕ} (hd : 0 < d) (hdq : d ∣ q) (g : ℕ → ℂ) :
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
private lemma ramanujan_exp_dvdS72 (q : ℕ) (k : ℤ) (hq : 2 ≤ q) :
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
    rw [← h1, indicator_coprime512S72 hq0 a]
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
  rw [hfac, ← Finset.sum_filter, sum_range_filter_dvd512S72 hd0 hdvd, ← Finset.mul_sum]
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
  rw [Finset.sum_congr rfl (fun b _ => harg b), e512_sum_orthS72 hm0 k]

/-- The Ramanujan sum `c_q(N)` as an exact divisor sum. -/
private lemma ramanujan512_dvdS72 (q N : ℕ) (hq : 2 ≤ q) :
    ramanujan512 q N = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
      (if ((q / d : ℕ) : ℤ) ∣ (N : ℤ) then ((q / d : ℕ) : ℂ) else 0) := by
  rw [ramanujan512_exp_rangeS72 q N hq, ramanujan_exp_dvdS72 q (-(N : ℤ)) hq]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hd : (((q / d : ℕ)) : ℤ) ∣ -(N : ℤ) ↔ (((q / d : ℕ)) : ℤ) ∣ (N : ℤ) := Int.dvd_neg
  by_cases h : (((q / d : ℕ)) : ℤ) ∣ (N : ℤ)
  · simp only [if_pos (hd.mpr h), if_pos h]
  · simp only [if_neg (fun hh => h (hd.mp hh)), if_neg h]

open scoped ArithmeticFunction.Moebius

/-- The real divisor form of `c_q(N)`: `Σ_{d ∣ q} (q/d)·μ(d)` restricted to `(q/d) ∣ N`. -/
private lemma c512_real_formS72 (q N : ℕ) (hq : 1 ≤ q) :
    ramanujan512 q N =
      ((∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) : ℝ) : ℂ) := by
  rcases eq_or_lt_of_le hq with h | h
  · subst h
    rw [ramanujan512_oneS72]
    have h1 : (∑ d ∈ (1 : ℕ).divisors, (if (1 / d : ℕ) ∣ N then ((1 / d : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)) = 1 := by
      rw [Nat.divisors_one, Finset.sum_singleton]
      norm_num
    rw [h1]
    norm_num
  · have h2 : 2 ≤ q := h
    rw [ramanujan512_dvdS72 q N h2, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    by_cases hd : ((q / d : ℕ) : ℤ) ∣ (N : ℤ)
    · rw [if_pos hd, if_pos (Int.natCast_dvd_natCast.mp hd)]
      push_cast
      ring
    · rw [if_neg hd, if_neg (fun hh => hd (Int.natCast_dvd_natCast.mpr hh))]
      push_cast
      ring

/-- Reindex the divisor sum: the Möbius index can be put on `q / d`. -/
private lemma c512_conv_formS72 (q N : ℕ) (hq : 0 < q) :
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
private lemma gDiv512_multS72 (N : ℕ) (g : ArithmeticFunction ℝ)
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
private lemma conv512S72 (N : ℕ) (g : ArithmeticFunction ℝ)
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
private lemma c512_real_mulS72 {m n : ℕ} (hmn : Nat.Coprime m n) (hm : 0 < m) (hn : 0 < n) (N : ℕ) :
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
    (gDiv512_multS72 N g hg).mul ArithmeticFunction.isMultiplicative_moebius.intCast
  rw [c512_conv_formS72 (m * n) N (Nat.mul_pos hm hn), c512_conv_formS72 m N hm,
    c512_conv_formS72 n N hn, ← conv512S72 N g hg (m * n), ← conv512S72 N g hg m,
    ← conv512S72 N g hg n]
  exact hmul.map_mul_of_coprime hmn

/-- The Ramanujan sum at a prime. -/
private lemma c512_primeS72 {p : ℕ} (hp : p.Prime) (N : ℕ) :
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
φ((q,N)) for squarefree q. Vaughan 1981 display 3.14: c_q is multiplicative in q and
at a prime p it is p - 1 if p ∣ N and -1 otherwise. -/
private lemma c512_real_abs_sqfreeS72 (N : ℕ) : ∀ q : ℕ, Squarefree q →
    |∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)| = (Nat.totient (Nat.gcd q N) : ℝ) := by
  intro q
  induction q using Nat.recOnPosPrimePosCoprime with
  | prime_pow p k hp hk =>
    intro hsq
    have hk1 : k = 1 := by
      rcases Nat.squarefree_pow_iff hp.ne_one hk.ne' |>.mp hsq with ⟨_, h⟩
      exact h
    subst hk1
    rw [pow_one, c512_primeS72 hp N]
    by_cases h : p ∣ N
    · rw [if_pos h, Nat.gcd_eq_left h, Nat.totient_prime hp]
      have : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
      rw [abs_of_nonneg (by linarith), Nat.cast_sub hp.one_lt.le]
      simp
    · rw [if_neg h, ((Nat.Prime.coprime_iff_not_dvd hp).mpr h).gcd_eq_one]
      simp
  | zero => intro h; exact absurd h not_squarefree_zero
  | one =>
    intro _
    simp
  | coprime a b ha hb hab iha ihb =>
    intro hsq
    have hsa : Squarefree a := hsq.of_mul_left
    have hsb : Squarefree b := hsq.of_mul_right
    have hcop : Nat.Coprime (Nat.gcd a N) (Nat.gcd b N) :=
      Nat.Coprime.coprime_dvd_left (Nat.gcd_dvd_left a N)
        (Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left b N) hab)
    rw [c512_real_mulS72 hab (by omega) (by omega) N, abs_mul, iha hsa, ihb hsb,
      Nat.gcd_comm (a * b) N, Nat.Coprime.gcd_mul N hab, Nat.gcd_comm N a, Nat.gcd_comm N b,
      Nat.totient_mul hcop, Nat.cast_mul]

/-- Vaughan 1981 chapter 3, display 3.14, used in the proof of display 3.23 on book
page 34, cited by P0069 page 8 display 2.7: for squarefree q the Ramanujan sum
c_q(-N) = μ(q/(q,N)) φ((q,N)) has absolute value φ((q,N)). -/
theorem ramanujan_sqfree_normS72 (q N : ℕ) (hq : Squarefree q) :
    ‖ramanujan512 q N‖ ≤ (Nat.totient (Nat.gcd q N) : ℝ) := by
  have hq1 : 1 ≤ q := Nat.pos_of_ne_zero (fun h => not_squarefree_zero (h ▸ hq))
  rw [c512_real_formS72 q N hq1, Complex.norm_real, Real.norm_eq_abs,
    c512_real_abs_sqfreeS72 N q hq]

#print axioms ramanujan_sqfree_normS72

end LeanLab.BHP1997.Section2MS
