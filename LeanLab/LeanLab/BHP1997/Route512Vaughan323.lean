/-
P0069 Baker Harman Pintz 1997, page 8, display 2.7, which cites Vaughan reference 31,
The Hardy-Littlewood Method, Cambridge 1981, chapter 3, book page 34, display 3.23.
Split of `Section2MS.leaf_vaughan_323_512` into two cited LEAF pieces of Vaughan's
proof of 3.23 and a CONDITIONAL assembly theorem with the verbatim statement.
Burst burst-20261122 session S64. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp512a

namespace LeanLab.BHP1997.Section2MS
open Classical

/-! ### Private helpers (private in `Decomp512a`, restated here) -/

private lemma e512_add (x y : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * ((x + y : ℝ) : ℂ)) =
      Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) *
        Complex.exp (2 * Real.pi * Complex.I * (y : ℂ)) := by
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private lemma e512_nat_mul (k : ℕ) (x : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (((k : ℝ) * x : ℝ) : ℂ)) =
      (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.cast_succ, add_mul, one_mul, e512_add, ih, pow_succ]

private lemma e512_int_mul (k : ℤ) (x : ℝ) :
    Complex.exp (2 * Real.pi * Complex.I * (((k : ℝ) * x : ℝ) : ℂ)) =
      (Complex.exp (2 * Real.pi * Complex.I * (x : ℂ))) ^ k := by
  have harg : (2 * (Real.pi : ℂ) * Complex.I * (((k : ℝ) * x : ℝ) : ℂ))
      = (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I * (x : ℂ)) := by push_cast; ring
  rw [harg, Complex.exp_int_mul]

private lemma e512_int_cast (k : ℤ) :
    Complex.exp (2 * Real.pi * Complex.I * ((k : ℝ) : ℂ)) = 1 := by
  have h2 : Complex.exp (2 * Real.pi * Complex.I * ((1 : ℝ) : ℂ)) = 1 := by
    rw [Complex.exp_eq_one_iff]
    exact ⟨1, by push_cast; ring⟩
  have h := e512_int_mul k 1
  rw [mul_one] at h
  rw [h, h2, one_zpow]

private lemma two_pi_I_ne_zero512 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
  have h1 : (2 * (Real.pi : ℂ)) ≠ 0 :=
    mul_ne_zero two_ne_zero (by exact_mod_cast Real.pi_ne_zero)
  exact mul_ne_zero h1 Complex.I_ne_zero

private lemma e512_eq_one_iff {x : ℝ} :
    Complex.exp (2 * Real.pi * Complex.I * (x : ℂ)) = 1 ↔ ∃ k : ℤ, x = (k : ℝ) := by
  constructor
  · intro h
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp h
    refine ⟨n, ?_⟩
    have hx : (2 * (Real.pi : ℂ) * Complex.I) * (x : ℂ)
        = (2 * (Real.pi : ℂ) * Complex.I) * ((n : ℝ) : ℂ) := by rw [hn]; push_cast; ring
    exact Complex.ofReal_injective (mul_left_cancel₀ two_pi_I_ne_zero512 hx)
  · rintro ⟨k, rfl⟩
    exact e512_int_cast k

/-- The orthogonality relation `Σ_{b<m} e(bk/m) = m` if `m ∣ k`, else `0`. -/
private lemma e512_sum_orth {m : ℕ} (hm : 0 < m) (k : ℤ) :
    ∑ b ∈ Finset.range m, Complex.exp (2 * Real.pi * Complex.I * (((b : ℝ) * (k : ℝ)) / m : ℝ))
      = if (m : ℤ) ∣ k then (m : ℂ) else 0 := by
  have hmR : ((m : ℝ)) ≠ 0 := by positivity
  set c : ℂ := Complex.exp (2 * Real.pi * Complex.I * (((k : ℝ)) / m : ℝ)) with hc
  have hterm : ∀ b ∈ Finset.range m,
      Complex.exp (2 * Real.pi * Complex.I * (((b : ℝ) * (k : ℝ)) / m : ℝ)) = c ^ b := by
    intro b _
    have harg : ((b : ℝ) * (k : ℝ)) / m = (b : ℝ) * ((k : ℝ) / m) := by field_simp
    rw [harg, e512_nat_mul]
  rw [Finset.sum_congr rfl hterm]
  have hcm : c ^ m = 1 := by
    have h1 : c ^ m = Complex.exp (2 * Real.pi * Complex.I * (((m : ℝ) * ((k : ℝ) / m) : ℝ) : ℂ)) := by
      rw [hc]; exact (e512_nat_mul m ((k : ℝ) / m)).symm
    rw [h1, mul_div_cancel₀ (k : ℝ) hmR, e512_int_cast]
  have hiff : c = 1 ↔ (m : ℤ) ∣ k := by
    rw [hc, e512_eq_one_iff]
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

private lemma filter_Icc_eq_range512 {q : ℕ} (hq : 2 ≤ q) :
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

private lemma ramanujan512_one (N : ℕ) : ramanujan512 1 N = 1 := by
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

private lemma ramanujan512_exp_range (q N : ℕ) (hq : 2 ≤ q) :
    ramanujan512 q N =
      ∑ a ∈ (Finset.range q).filter (fun a => Nat.Coprime a q),
        Complex.exp (2 * Real.pi * Complex.I * (((a : ℝ) * ((-(N : ℤ) : ℤ) : ℝ)) / q : ℝ)) := by
  unfold ramanujan512
  rw [filter_Icc_eq_range512 hq]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  rw [fourier_coe_apply]
  congr 1
  push_cast
  ring

private lemma sum_moebius_divisors512 (n : ℕ) :
    ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℤ) = if n = 1 then 1 else 0 := by
  have h := ArithmeticFunction.coe_mul_zeta_apply (f := ArithmeticFunction.moebius) (x := n)
  rw [ArithmeticFunction.moebius_mul_coe_zeta] at h
  rw [← h]
  exact ArithmeticFunction.one_apply

private lemma divisors_filter_dvd_eq_gcd512 {q a : ℕ} (hq : q ≠ 0) :
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

private lemma indicator_coprime512 {q : ℕ} (hq : q ≠ 0) (a : ℕ) :
    (if a.gcd q = 1 then (1:ℂ) else 0)
      = ∑ d ∈ q.divisors, (if d ∣ a then (ArithmeticFunction.moebius d : ℂ) else 0) := by
  rw [← Finset.sum_filter, divisors_filter_dvd_eq_gcd512 hq]
  have h := congrArg (fun z : ℤ => (z : ℂ)) (sum_moebius_divisors512 (a.gcd q))
  push_cast at h
  exact h.symm

private lemma sum_range_filter_dvd512 {q d : ℕ} (hd : 0 < d) (hdq : d ∣ q) (g : ℕ → ℂ) :
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
private lemma ramanujan_exp_dvd (q : ℕ) (k : ℤ) (hq : 2 ≤ q) :
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
    rw [← h1, indicator_coprime512 hq0 a]
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
  rw [hfac, ← Finset.sum_filter, sum_range_filter_dvd512 hd0 hdvd, ← Finset.mul_sum]
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
  rw [Finset.sum_congr rfl (fun b _ => harg b), e512_sum_orth hm0 k]

/-- The Ramanujan sum `c_q(N)` as an exact divisor sum. -/
private lemma ramanujan512_dvd (q N : ℕ) (hq : 2 ≤ q) :
    ramanujan512 q N = ∑ d ∈ q.divisors, (ArithmeticFunction.moebius d : ℂ) *
      (if ((q / d : ℕ) : ℤ) ∣ (N : ℤ) then ((q / d : ℕ) : ℂ) else 0) := by
  rw [ramanujan512_exp_range q N hq, ramanujan_exp_dvd q (-(N : ℤ)) hq]
  refine Finset.sum_congr rfl (fun d _ => ?_)
  have hd : (((q / d : ℕ)) : ℤ) ∣ -(N : ℤ) ↔ (((q / d : ℕ)) : ℤ) ∣ (N : ℤ) := Int.dvd_neg
  by_cases h : (((q / d : ℕ)) : ℤ) ∣ (N : ℤ)
  · simp only [if_pos (hd.mpr h), if_pos h]
  · simp only [if_neg (fun hh => h (hd.mp hh)), if_neg h]

open scoped ArithmeticFunction.Moebius

/-- The real divisor form of `c_q(N)`: `Σ_{d ∣ q} (q/d)·μ(d)` restricted to `(q/d) ∣ N`. -/
private lemma c512_real_form (q N : ℕ) (hq : 1 ≤ q) :
    ramanujan512 q N =
      ((∑ d ∈ q.divisors, (if (q / d : ℕ) ∣ N then ((q / d : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ) : ℝ) : ℂ) := by
  rcases eq_or_lt_of_le hq with h | h
  · subst h
    rw [ramanujan512_one]
    have h1 : (∑ d ∈ (1 : ℕ).divisors, (if (1 / d : ℕ) ∣ N then ((1 / d : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius d : ℤ) : ℝ)) = 1 := by
      rw [Nat.divisors_one, Finset.sum_singleton]
      norm_num
    rw [h1]
    norm_num
  · have h2 : 2 ≤ q := h
    rw [ramanujan512_dvd q N h2, Complex.ofReal_sum]
    refine Finset.sum_congr rfl (fun d _ => ?_)
    by_cases hd : ((q / d : ℕ) : ℤ) ∣ (N : ℤ)
    · rw [if_pos hd, if_pos (Int.natCast_dvd_natCast.mp hd)]
      push_cast
      ring
    · rw [if_neg hd, if_neg (fun hh => hd (Int.natCast_dvd_natCast.mpr hh))]
      push_cast
      ring

/-- Reindex the divisor sum: the Möbius index can be put on `q / d`. -/
private lemma c512_conv_form (q N : ℕ) (hq : 0 < q) :
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

/-! ### The squarefree evaluation -/

/-- `Σ_{e ∣ g} e · μ(g/e) = φ(g)`, the Dirichlet convolution `id * μ = φ`. -/
private lemma totient_conv323 (g : ℕ) (hg : 0 < g) :
    (∑ e ∈ g.divisors, (e : ℝ) * ((ArithmeticFunction.moebius (g / e) : ℤ) : ℝ))
      = (Nat.totient g : ℝ) := by
  have hrev : (∑ e ∈ g.divisors, (e : ℝ) * ((ArithmeticFunction.moebius (g / e) : ℤ) : ℝ))
      = ∑ e ∈ g.divisors,
          ((g / e : ℕ) : ℝ) * ((ArithmeticFunction.moebius e : ℤ) : ℝ) := by
    refine Finset.sum_nbij' (fun e => g / e) (fun e => g / e) ?_ ?_ ?_ ?_ ?_
    · intro a ha
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors ha), hg.ne'⟩
    · intro b hb
      exact Nat.mem_divisors.mpr ⟨Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors hb), hg.ne'⟩
    · intro a ha
      exact Nat.div_div_self (Nat.dvd_of_mem_divisors ha) hg.ne'
    · intro b hb
      exact Nat.div_div_self (Nat.dvd_of_mem_divisors hb) hg.ne'
    · intro a ha
      rw [Nat.div_div_self (Nat.dvd_of_mem_divisors ha) hg.ne']
  have hinv : ∀ n : ℕ, 0 < n →
      (∑ x ∈ n.divisorsAntidiagonal,
          ((ArithmeticFunction.moebius x.1 : ℤ) : ℝ) * (x.2 : ℝ))
        = (Nat.totient n : ℝ) := by
    have hmain := (ArithmeticFunction.sum_eq_iff_sum_mul_moebius_eq
      (f := fun n : ℕ => (Nat.totient n : ℝ)) (g := fun n : ℕ => (n : ℝ))).mp (by
        intro n hn
        have h := congrArg (fun k : ℕ => (k : ℝ)) (Nat.sum_totient n)
        simpa [Nat.cast_sum] using h)
    intro n hn
    exact hmain n hn
  rw [hrev, ← Nat.sum_divisorsAntidiagonal (f := fun a b =>
    ((b : ℕ) : ℝ) * ((ArithmeticFunction.moebius a : ℤ) : ℝ))]
  have hcongr : (∑ i ∈ g.divisorsAntidiagonal,
      ((i.2 : ℕ) : ℝ) * ((ArithmeticFunction.moebius i.1 : ℤ) : ℝ))
      = ∑ i ∈ g.divisorsAntidiagonal,
          ((ArithmeticFunction.moebius i.1 : ℤ) : ℝ) * (i.2 : ℝ) :=
    Finset.sum_congr rfl (fun i _ => by ring)
  rw [hcongr, hinv g hg]

/-- LEAF: Vaughan 1981 chapter 3, display 3.14 and the evaluation of the Ramanujan sum used
in the proof of display 3.23 on book page 34: for squarefree q the Ramanujan sum
c_q(-m) = Σ_{(a,q)=1} e(-am/q) equals μ(q/(q,m)) φ((q,m)), so its absolute value is
φ((q,m)). Class EASY: the lab's private `c512_real_form` in Decomp512a writes c_q as
Σ_{d|q} [q/d ∣ m] (q/d) μ(d), and for squarefree q = g r with g = (q,m) this is
μ(r) Σ_{e|g} e μ(g/e) = μ(r) φ(g). -/
theorem leaf_ramanujan_sqfree_norm512 (q N : ℕ) (hq : Squarefree q) :
    ‖ramanujan512 q N‖ ≤ (Nat.totient (Nat.gcd q N) : ℝ) := by
  have hq0 : q ≠ 0 := hq.ne_zero
  have hq1 : 1 ≤ q := Nat.one_le_iff_ne_zero.mpr hq0
  have hqpos : 0 < q := Nat.pos_of_ne_zero hq0
  set g : ℕ := Nat.gcd q N with hgdef
  have hgq : g ∣ q := by rw [hgdef]; exact Nat.gcd_dvd_left q N
  have hgne : g ≠ 0 := by
    rintro h0
    rw [h0] at hgq
    exact hq0 (Nat.eq_zero_of_zero_dvd hgq)
  have hgpos : 0 < g := Nat.pos_of_ne_zero hgne
  set r : ℕ := q / g with hrdef
  have hqr : g * r = q := by
    rw [hrdef]; exact Nat.mul_div_cancel' hgq
  have hcop : Nat.Coprime r g := by
    set d : ℕ := Nat.gcd r g with hddef
    have hd1 : d ∣ g := Nat.gcd_dvd_right r g
    have hd2 : d ∣ r := Nat.gcd_dvd_left r g
    obtain ⟨g', hg'⟩ := hd1
    obtain ⟨r', hr'⟩ := hd2
    have hdvd : d * d ∣ q := by
      refine ⟨g' * r', ?_⟩
      rw [← hqr, hg', hr']
      ring
    have hunit : IsUnit d := (Squarefree.eq_1 q).mp hq d hdvd
    have hone : d = 1 := Nat.isUnit_iff.mp hunit
    exact Nat.coprime_iff_gcd_eq_one.mpr hone
  have hform : ramanujan512 q N = ((∑ e ∈ q.divisors,
      (if e ∣ N then ((e : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ) : ℝ) : ℂ) := by
    rw [c512_real_form q N hq1, c512_conv_form q N hqpos]
  have hsupp : (∑ e ∈ q.divisors, (if e ∣ N then ((e : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ))
      = ∑ e ∈ g.divisors,
          ((e : ℕ) : ℝ) * ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ) := by
    have hstep : (∑ e ∈ q.divisors, (if e ∣ N then ((e : ℕ) : ℝ) else 0) *
        ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ))
        = ∑ e ∈ q.divisors,
            (if e ∣ N then
              ((e : ℕ) : ℝ) * ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ) else 0) := by
      refine Finset.sum_congr rfl (fun e _ => ?_)
      by_cases h : e ∣ N <;> simp [h]
    rw [hstep, ← Finset.sum_filter]
    have hf : q.divisors.filter (fun e => e ∣ N) = g.divisors := by
      rw [hgdef, Nat.gcd_comm]
      exact divisors_filter_dvd_eq_gcd512 (q := q) (a := N) hq0
    rw [hf]
  have hsplit : ∀ e ∈ g.divisors, ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ)
      = ((ArithmeticFunction.moebius r : ℤ) : ℝ) *
        ((ArithmeticFunction.moebius (g / e) : ℤ) : ℝ) := by
    intro e he
    have hepos : 0 < e := Nat.pos_of_mem_divisors he
    have hge : g = e * (g / e) := (Nat.mul_div_cancel' (Nat.dvd_of_mem_divisors he)).symm
    have h1 : q / e = (g / e) * r := by
      have hq' : q = e * ((g / e) * r) := by
        rw [← Nat.mul_assoc, hge.symm, hqr]
      rw [hq', Nat.mul_div_cancel_left _ hepos]
    have hcopge : Nat.Coprime r (g / e) :=
      hcop.coprime_dvd_right (Nat.div_dvd_of_dvd (Nat.dvd_of_mem_divisors he))
    rw [h1, Nat.mul_comm (g / e) r,
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcopge.gcd_eq_one]
    push_cast
    ring
  have hfac : (∑ e ∈ g.divisors, ((e : ℕ) : ℝ) *
        ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ))
      = ((ArithmeticFunction.moebius r : ℤ) : ℝ) * (Nat.totient g : ℝ) := by
    have hterm : ∀ e ∈ g.divisors, ((e : ℕ) : ℝ) *
        ((ArithmeticFunction.moebius (q / e) : ℤ) : ℝ)
        = ((ArithmeticFunction.moebius r : ℤ) : ℝ) *
          (((e : ℕ) : ℝ) * ((ArithmeticFunction.moebius (g / e) : ℤ) : ℝ)) := by
      intro e he
      rw [hsplit e he]; ring
    rw [Finset.sum_congr rfl hterm, ← totient_conv323 g hgpos, Finset.mul_sum]
  rw [hform, hsupp, hfac, Complex.norm_real, Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (Nat.totient g : ℝ))]
  have hmu : |((ArithmeticFunction.moebius r : ℤ) : ℝ)| ≤ 1 := by
    rw [← Int.cast_abs]
    exact_mod_cast ArithmeticFunction.abs_moebius_le_one (n := r)
  calc |((ArithmeticFunction.moebius r : ℤ) : ℝ)| * (Nat.totient g : ℝ)
      ≤ 1 * (Nat.totient g : ℝ) :=
        mul_le_mul_of_nonneg_right hmu (by positivity)
    _ = (Nat.totient g : ℝ) := by rw [one_mul]

/-! ## 1. A product of distinct primes is squarefree -/

private lemma squarefree_prod_primes323 (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    Squarefree (∏ p ∈ s, p) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    have ha' : Nat.Prime a := hs a (Finset.mem_insert_self a s)
    have hs' : ∀ p ∈ s, Nat.Prime p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
    have hcop : a.Coprime (∏ p ∈ s, p) := by
      rw [ha'.coprime_iff_not_dvd]
      intro hdvd
      obtain ⟨p, hp, hap⟩ :=
        (Prime.dvd_finset_prod_iff (Nat.Prime.prime ha') (fun x : ℕ => x)).mp hdvd
      have hpp : Nat.Prime p := hs' p hp
      have hpa : p = a := (Nat.Prime.dvd_iff_eq hpp ha'.ne_one).mp hap
      exact ha (hpa ▸ hp)
    rw [Nat.squarefree_mul_iff]
    exact ⟨hcop, (Nat.Prime.prime ha').squarefree, ih hs'⟩

/-! ## 2. Euler product as a sum over squarefree divisors -/

private lemma sum_sqfree_divisors323 (n : ℕ) (hn : n ≠ 0) (w : ℕ → ℝ) :
    (∑ d ∈ n.divisors.filter (fun d => Squarefree d), ∏ p ∈ d.primeFactors, w p)
      = ∏ p ∈ n.primeFactors, (1 + w p) := by
  classical
  have hinj : Set.InjOn (fun t : Finset ℕ => ∏ p ∈ t, p) ↑(n.primeFactors.powerset) := by
    intro s hs t ht hst
    have hsp : ∀ p ∈ s, Nat.Prime p :=
      fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp hs hp)
    have htp : ∀ p ∈ t, Nat.Prime p :=
      fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp)
    have hst' : (∏ p ∈ s, p) = (∏ p ∈ t, p) := by simpa using hst
    rw [← Nat.primeFactors_prod hsp, ← Nat.primeFactors_prod htp, hst']
  have himage : (n.primeFactors.powerset).image (fun t : Finset ℕ => ∏ p ∈ t, p)
      = n.divisors.filter (fun d => Squarefree d) := by
    ext d
    constructor
    · intro hd
      obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hd
      have ht' : t ⊆ n.primeFactors := Finset.mem_powerset.mp ht
      have htp : ∀ p ∈ t, Nat.Prime p := fun p hp => Nat.prime_of_mem_primeFactors (ht' hp)
      refine Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨?_, hn⟩, squarefree_prod_primes323 t htp⟩
      exact (Finset.prod_dvd_prod_of_subset t n.primeFactors (fun p => p) ht').trans
        (Nat.prod_primeFactors_dvd n)
    · intro hd
      obtain ⟨hdv, hsq⟩ := Finset.mem_filter.mp hd
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hdv
      refine Finset.mem_image.mpr ⟨d.primeFactors, ?_, ?_⟩
      · rw [Finset.mem_powerset]
        intro p hp
        exact Nat.Prime.mem_primeFactors (Nat.prime_of_mem_primeFactors hp)
          (dvd_trans (Nat.dvd_of_mem_primeFactors hp) hdvd) hn
      · exact Nat.prod_primeFactors_of_squarefree hsq
  rw [← himage, Finset.sum_image (fun x hx y hy h => hinj hx hy h), Finset.prod_one_add]
  refine Finset.sum_congr rfl (fun t ht => ?_)
  rw [Nat.primeFactors_prod
    (fun p hp => Nat.prime_of_mem_primeFactors (Finset.mem_powerset.mp ht hp))]

/-! ## 3. `n / φ n` as a product over the primes -/

private lemma totient_ratio323 (n : ℕ) (hn : 1 ≤ n) :
    (n : ℝ) / (Nat.totient n : ℝ) = ∏ p ∈ n.primeFactors, ((p : ℝ) / ((p : ℝ) - 1)) := by
  have hn0 : n ≠ 0 := by omega
  have hφ : (0 : ℝ) < (Nat.totient n : ℝ) := by exact_mod_cast Nat.totient_pos.mpr hn
  have hcast : (Nat.totient n : ℝ) * ∏ p ∈ n.primeFactors, (p : ℝ)
      = (n : ℝ) * ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
    have h := congrArg (fun k : ℕ => (k : ℝ)) (Nat.totient_mul_prod_primeFactors n)
    push_cast at h
    have hQ : (∏ p ∈ n.primeFactors, ((p - 1 : ℕ) : ℝ))
        = ∏ p ∈ n.primeFactors, ((p : ℝ) - 1) := by
      refine Finset.prod_congr rfl (fun p hp => ?_)
      rw [Nat.cast_sub (Nat.Prime.one_le (Nat.prime_of_mem_primeFactors hp)), Nat.cast_one]
    rw [hQ] at h
    exact h
  have hQ0 : (∏ p ∈ n.primeFactors, ((p : ℝ) - 1)) ≠ 0 := by
    refine Finset.prod_ne_zero_iff.mpr (fun p hp => ?_)
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp))
    linarith
  rw [Finset.prod_div_distrib, div_eq_div_iff (ne_of_gt hφ) hQ0]
  rw [mul_comm (∏ p ∈ n.primeFactors, (p : ℝ)) (Nat.totient n : ℝ)]
  exact hcast.symm

/-! ## 4. The exact Dirichlet convolution identity -/

private lemma sq_div_totient_sq323 (n : ℕ) (hn : 1 ≤ n) :
    ((n : ℝ) / (Nat.totient n : ℝ)) ^ 2
      = ∑ d ∈ n.divisors.filter (fun d => Squarefree d),
          ∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) := by
  have hn0 : n ≠ 0 := by omega
  rw [totient_ratio323 n hn, ← Finset.prod_pow]
  have h1 : ∀ p ∈ n.primeFactors,
      ((p : ℝ) / ((p : ℝ) - 1)) ^ 2 = 1 + (2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2 := by
    intro p hp
    have h2 : (2 : ℝ) ≤ (p : ℝ) := by
      exact_mod_cast (Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp))
    have hp1 : ((p : ℝ) - 1) ≠ 0 := by linarith
    field_simp
    ring
  rw [Finset.prod_congr rfl h1]
  exact (sum_sqfree_divisors323 n hn0 _).symm

/-! ## 5. The reciprocal square tail -/

private lemma inv_sq_Ioo_le323 (t : ℝ) (ht : 0 < t) (N : ℕ) :
    (∑ k ∈ Finset.Ioo ⌊t⌋₊ N, ((k : ℝ) ^ 2)⁻¹) ≤ 2 / t := by
  have h1 : (∑ k ∈ Finset.Ioo ⌊t⌋₊ N, ((k : ℝ) ^ 2)⁻¹) ≤ 2 / ((⌊t⌋₊ : ℝ) + 1) :=
    sum_Ioo_inv_sq_le ⌊t⌋₊ N
  have h2 : (2 : ℝ) / ((⌊t⌋₊ : ℝ) + 1) ≤ 2 / t :=
    div_le_div_of_nonneg_left (by norm_num) ht (le_of_lt (Nat.lt_floor_add_one t))
  linarith

/-! ## 6. The per-prime weight against `p^{-3/2}` -/

private lemma wprime_le323 {p : ℕ} (hp : Nat.Prime p) (hp7 : 7 ≤ p) :
    (2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2) ≤ (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hpR : (7 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp7
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hpoly : (2 * (p : ℝ) - 1) ^ 2 * (p : ℝ) ≤ ((p : ℝ) - 1) ^ 4 := by
    have hfac : ((p : ℝ) - 1) ^ 4 - (2 * (p : ℝ) - 1) ^ 2 * (p : ℝ)
        = ((p : ℝ) - 7) * ((p : ℝ) ^ 3 - (p : ℝ) ^ 2 + 3 * (p : ℝ) + 16) + 113 := by ring
    have h1 : (0 : ℝ) ≤ (p : ℝ) - 7 := by linarith
    have h2 : (0 : ℝ) ≤ (p : ℝ) ^ 3 - (p : ℝ) ^ 2 + 3 * (p : ℝ) + 16 := by nlinarith [hp0]
    nlinarith
  have hmul : (2 * (p : ℝ) - 1) * Real.sqrt (p : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by
    have hsq1 : ((2 * (p : ℝ) - 1) * Real.sqrt (p : ℝ)) ^ 2
        = (2 * (p : ℝ) - 1) ^ 2 * (p : ℝ) := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]
    have h4 : (((p : ℝ) - 1) ^ 2) ^ 2 = ((p : ℝ) - 1) ^ 4 := by ring
    have ha0 : (0 : ℝ) ≤ (2 * (p : ℝ) - 1) * Real.sqrt (p : ℝ) := by
      have hs := Real.sqrt_nonneg (p : ℝ)
      nlinarith [hp0, hs]
    have hb0 : (0 : ℝ) ≤ ((p : ℝ) - 1) ^ 2 := by positivity
    nlinarith [hsq1, hpoly, ha0, hb0, sq_nonneg ((2 * (p : ℝ) - 1) * Real.sqrt (p : ℝ) - ((p : ℝ) - 1) ^ 2), h4]
  have hrpow : (p : ℝ) ^ (-(3 / 2 : ℝ)) = 1 / ((p : ℝ) * Real.sqrt (p : ℝ)) := by
    have h3 : (p : ℝ) ^ (1 / 2 : ℝ) = Real.sqrt (p : ℝ) := (Real.sqrt_eq_rpow (p : ℝ)).symm
    rw [Real.rpow_neg (le_of_lt hp0),
      show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num, Real.rpow_add hp0, Real.rpow_one, h3,
      one_div]
  rw [hrpow, div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hmul, hp0]

/-! ## 7. An `rpow` product identity -/

private lemma prod_rpow323 (s : Finset ℕ) (h : ∀ p ∈ s, 0 < p) :
    (∏ p ∈ s, (p : ℝ) ^ (-(3 / 2 : ℝ))) = ((∏ p ∈ s, p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
      have ha0 : (0 : ℝ) < (a : ℝ) := by exact_mod_cast h a (Finset.mem_insert_self a s)
      rw [Finset.prod_insert ha, Finset.prod_insert ha, Nat.cast_mul,
        Real.mul_rpow (le_of_lt ha0) (by positivity)]
      rw [ih (fun p hp => h p (Finset.mem_insert_of_mem hp))]

/-! ## 8. The small primes -/

private lemma wsmall_le323 {p : ℕ} (hp : 2 ≤ p) :
    (2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2) ≤ 3 / 2 := by
  have hpR : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hden : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) ^ 2 := by positivity
  rw [div_le_div_iff₀ hden (by norm_num : (0 : ℝ) < 2)]
  have hfac : 3 * ((p : ℝ) * ((p : ℝ) - 1) ^ 2) - (2 * (p : ℝ) - 1) * 2
      = ((p : ℝ) - 2) * (3 * (p : ℝ) ^ 2 - 1) := by ring
  have h1 : (0 : ℝ) ≤ (p : ℝ) - 2 := by linarith
  have h2 : (0 : ℝ) ≤ 3 * (p : ℝ) ^ 2 - 1 := by nlinarith
  have h3 : (0 : ℝ) ≤ ((p : ℝ) - 2) * (3 * (p : ℝ) ^ 2 - 1) := mul_nonneg h1 h2
  linarith

/-! ## 9. The weight of a squarefree `d` -/

private lemma weightd_nonneg323 (s : Finset ℕ) (hs : ∀ p ∈ s, Nat.Prime p) :
    0 ≤ ∏ p ∈ s, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)) := by
  refine Finset.prod_nonneg (fun p hp => ?_)
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast (hs p hp).two_le
  have h3 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h4 : (0 : ℝ) ≤ 2 * (p : ℝ) - 1 := by linarith
  have h5 : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) ^ 2 := by positivity
  exact div_nonneg h4 (le_of_lt h5)

/-- Product comparison for nonnegative real factors (induction form). -/
private lemma prod_le_prod_real323 (f g : ℕ → ℝ) :
    ∀ s : Finset ℕ, (∀ p ∈ s, f p ≤ g p) → (∀ p ∈ s, 0 ≤ f p) → (∀ p ∈ s, 0 ≤ g p) →
      (∏ p ∈ s, f p) ≤ ∏ p ∈ s, g p := by
  intro s
  induction s using Finset.induction_on with
  | empty => intro _ _ _; simp
  | insert a s ha ih =>
      intro hs hs0 hg0
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      have ha1 : f a ≤ g a := hs a (Finset.mem_insert_self a s)
      have ha0 : 0 ≤ f a := hs0 a (Finset.mem_insert_self a s)
      have hga0 : 0 ≤ g a := hg0 a (Finset.mem_insert_self a s)
      have hs1 : ∀ p ∈ s, f p ≤ g p := fun p hp => hs p (Finset.mem_insert_of_mem hp)
      have hs2 : ∀ p ∈ s, 0 ≤ f p := fun p hp => hs0 p (Finset.mem_insert_of_mem hp)
      have hs3 : ∀ p ∈ s, 0 ≤ g p := fun p hp => hg0 p (Finset.mem_insert_of_mem hp)
      exact mul_le_mul ha1 (ih hs1 hs2 hs3) (Finset.prod_nonneg hs2) hga0

private lemma weight_le323 (d : ℕ) (hd : Squarefree d) :
    (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)))
      ≤ 1000 * (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
  classical
  rcases Nat.eq_zero_or_pos d with h0 | hpos
  · rw [h0] at hd
    exact absurd hd (by simp)
  have hd0 : d ≠ 0 := hpos.ne'
  set A : Finset ℕ := d.primeFactors.filter (fun p => p < 7) with hA
  set B : Finset ℕ := d.primeFactors.filter (fun p => ¬ p < 7) with hB
  have hsplit : (∏ p ∈ d.primeFactors,
        ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)))
      = (∏ p ∈ A, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2))) *
        (∏ p ∈ B, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2))) := by
    rw [hA, hB, Finset.prod_filter_mul_prod_filter_not]
  have hAsub : A ⊆ ({2, 3, 5} : Finset ℕ) := by
    intro p hp
    rw [hA, Finset.mem_filter] at hp
    obtain ⟨hpd, hp7⟩ := hp
    have hp' : Nat.Prime p := Nat.prime_of_mem_primeFactors hpd
    have hmem : p ∈ Finset.filter Nat.Prime (Finset.range 7) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨hp7, hp'⟩
    have hsub : Finset.filter Nat.Prime (Finset.range 7) ⊆ ({2, 3, 5} : Finset ℕ) := by
      decide
    exact hsub hmem
  have hAsmall : (∏ p ∈ A, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)))
      ≤ 3.375 := by
    have h1 : ∀ p ∈ A, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)) ≤ 3 / 2 := by
      intro p hp
      rw [hA] at hp
      obtain ⟨hpd, hp7⟩ := Finset.mem_filter.mp hp
      exact wsmall_le323 (Nat.prime_of_mem_primeFactors hpd).two_le
    have h0 : ∀ p ∈ A, (0 : ℝ) ≤ (2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2) := by
      intro p hp
      rw [hA] at hp
      obtain ⟨hpd, hp7⟩ := Finset.mem_filter.mp hp
      have hp' : Nat.Prime p := Nat.prime_of_mem_primeFactors hpd
      have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp'.two_le
      have : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by
        have : (0 : ℝ) < (p : ℝ) - 1 := by linarith
        positivity
      have : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) ^ 2 := by positivity
      have : (0 : ℝ) ≤ 2 * (p : ℝ) - 1 := by linarith
      exact div_nonneg this (le_of_lt ‹(0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) ^ 2›)
    calc (∏ p ∈ A, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)))
        ≤ ∏ p ∈ A, (3 / 2 : ℝ) :=
          prod_le_prod_real323 _ _ A h1 h0 (fun p _ => by norm_num)
      _ = (3 / 2 : ℝ) ^ A.card := Finset.prod_const (3 / 2 : ℝ)
      _ ≤ (3 / 2 : ℝ) ^ 3 := by
          apply pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 3 / 2)
          calc A.card ≤ ({2, 3, 5} : Finset ℕ).card := Finset.card_le_card hAsub
            _ = 3 := by decide
      _ = 3.375 := by norm_num
  have hBbig : (∏ p ∈ B, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)))
      ≤ ((∏ p ∈ B, p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have h1 : ∀ p ∈ B, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2))
        ≤ (p : ℝ) ^ (-(3 / 2 : ℝ)) := by
      intro p hp
      rw [hB] at hp
      obtain ⟨hpd, hp7⟩ := Finset.mem_filter.mp hp
      exact wprime_le323 (Nat.prime_of_mem_primeFactors hpd) (by omega)
    have h0 : ∀ p ∈ B, (0 : ℝ) ≤ (2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2) := by
      intro p hp
      rw [hB] at hp
      obtain ⟨hpd, hp7⟩ := Finset.mem_filter.mp hp
      have hp' : Nat.Prime p := Nat.prime_of_mem_primeFactors hpd
      have h2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp'.two_le
      have h3 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
      have h4 : (0 : ℝ) ≤ 2 * (p : ℝ) - 1 := by linarith
      have : (0 : ℝ) < (p : ℝ) * ((p : ℝ) - 1) ^ 2 := by positivity
      exact div_nonneg h4 (le_of_lt this)
    calc (∏ p ∈ B, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)))
        ≤ ∏ p ∈ B, (p : ℝ) ^ (-(3 / 2 : ℝ)) :=
          prod_le_prod_real323 _ _ B h1 h0
            (fun p hp => Real.rpow_nonneg (by positivity) _)
      _ = ((∏ p ∈ B, p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) :=
          prod_rpow323 B (fun p hp => by
            rw [hB] at hp
            exact Nat.Prime.pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1))
  have hd_eq : d = (∏ p ∈ A, p) * (∏ p ∈ B, p) := by
    rw [hA, hB, Finset.prod_filter_mul_prod_filter_not,
      Nat.prod_primeFactors_of_squarefree hd]
  have hB30 : ((∏ p ∈ B, p : ℕ) : ℝ) ≥ (d : ℝ) / 30 := by
    have hAle : (∏ p ∈ A, p) ≤ 30 := by
      have hdvd : (∏ p ∈ A, p) ∣ ∏ p ∈ ({2, 3, 5} : Finset ℕ), p :=
        Finset.prod_dvd_prod_of_subset A _ (fun p => p) hAsub
      have hval : (∏ p ∈ ({2, 3, 5} : Finset ℕ), p) = 30 := by decide
      rw [hval] at hdvd
      exact Nat.le_of_dvd (by norm_num) hdvd
    have hBpos : 0 < (∏ p ∈ B, p) := by
      refine Finset.prod_pos (fun p hp => ?_)
      rw [hB] at hp
      exact Nat.Prime.pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hp).1)
    have hBposR : (0 : ℝ) < ((∏ p ∈ B, p : ℕ) : ℝ) := by exact_mod_cast hBpos
    have hcast : (d : ℝ) = ((∏ p ∈ A, p : ℕ) : ℝ) * ((∏ p ∈ B, p : ℕ) : ℝ) := by
      rw [hd_eq]; push_cast; ring
    have hAleR : ((∏ p ∈ A, p : ℕ) : ℝ) ≤ 30 := by exact_mod_cast hAle
    rw [hcast, ge_iff_le, div_le_iff₀ (by norm_num : (0 : ℝ) < 30)]
    nlinarith [hAleR, hBposR]
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hpos
  have hm32 : ((∏ p ∈ B, p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))
      ≤ (180 : ℝ) * (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have hd30 : (0 : ℝ) < (d : ℝ) / 30 := by positivity
    have h1 := Real.rpow_le_rpow_of_nonpos hd30 hB30 (by norm_num : (-(3 / 2 : ℝ)) ≤ 0)
    have h2 : ((d : ℝ) / 30) ^ (-(3 / 2 : ℝ))
        = (30 : ℝ) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
      rw [Real.div_rpow (le_of_lt hdR) (by norm_num : (0 : ℝ) ≤ 30),
        Real.rpow_neg (le_of_lt hdR), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 30)]
      field_simp
    have h3 : (30 : ℝ) ^ (3 / 2 : ℝ) ≤ 180 := by
      have h : (30 : ℝ) ^ (3 / 2 : ℝ) = 30 * Real.sqrt 30 := by
        rw [show (3 / 2 : ℝ) = 1 + 1 / 2 by norm_num,
          Real.rpow_add (by norm_num : (0 : ℝ) < 30), Real.rpow_one, ← Real.sqrt_eq_rpow]
      rw [h]
      have hsq : Real.sqrt 30 ≤ 6 := by
        have hle := Real.sqrt_le_sqrt (show (30 : ℝ) ≤ 36 by norm_num)
        have h36 : (36 : ℝ) = 6 ^ 2 := by norm_num
        rw [h36, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 6)] at hle
        exact hle
      nlinarith
    calc ((∏ p ∈ B, p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ))
        ≤ ((d : ℝ) / 30) ^ (-(3 / 2 : ℝ)) := h1
      _ = (30 : ℝ) ^ (3 / 2 : ℝ) * (d : ℝ) ^ (-(3 / 2 : ℝ)) := h2
      _ ≤ 180 * (d : ℝ) ^ (-(3 / 2 : ℝ)) :=
          mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg (le_of_lt hdR) _)
  have hd_nn : (0 : ℝ) ≤ (d : ℝ) ^ (-(3 / 2 : ℝ)) := Real.rpow_nonneg (le_of_lt hdR) _
  calc (∏ p ∈ d.primeFactors,
        ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)))
      = (∏ p ∈ A, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2))) *
        (∏ p ∈ B, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2))) := hsplit
    _ ≤ 3.375 * ((∏ p ∈ B, p : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) :=
        mul_le_mul hAsmall hBbig
          (weightd_nonneg323 B (fun p hp => by
            rw [hB, Finset.mem_filter] at hp
            exact Nat.prime_of_mem_primeFactors hp.1))
          (by norm_num)
    _ ≤ 3.375 * (180 * (d : ℝ) ^ (-(3 / 2 : ℝ))) :=
        mul_le_mul_of_nonneg_left hm32 (by norm_num)
    _ = 607.5 * (d : ℝ) ^ (-(3 / 2 : ℝ)) := by ring
    _ ≤ 1000 * (d : ℝ) ^ (-(3 / 2 : ℝ)) :=
        mul_le_mul_of_nonneg_right (by norm_num) hd_nn

/-! ## 10. Multiples of `d` in the tail -/

private lemma multiples_tail323 (Z : ℝ) (hZ : 0 < Z) (R d : ℕ) (hd : 1 ≤ d) :
    (∑ n ∈ ((Finset.Icc 1 R).filter (fun n : ℕ => Z < (n : ℝ))).filter (fun n => d ∣ n),
        1 / (n : ℝ) ^ 2)
      ≤ (1 / (d : ℝ) ^ 2) * (2 / (Z / (d : ℝ))) := by
  classical
  have hdpos : 0 < d := hd
  have hdR : (0 : ℝ) < (d : ℝ) := by exact_mod_cast hdpos
  set S : Finset ℕ :=
    ((Finset.Icc 1 R).filter (fun n : ℕ => Z < (n : ℝ))).filter (fun n => d ∣ n) with hS
  have hmem : ∀ n ∈ S, 1 ≤ n ∧ n ≤ R ∧ Z < (n : ℝ) ∧ d ∣ n := by
    intro n hn
    rw [hS, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hn
    exact ⟨hn.1.1.1, hn.1.1.2, hn.1.2, hn.2⟩
  have hinj : Set.InjOn (fun n : ℕ => n / d) ↑S := by
    intro a ha b hb hab
    obtain ⟨-, -, -, hadvd⟩ := hmem a ha
    obtain ⟨-, -, -, hbdvd⟩ := hmem b hb
    simp only at hab
    rw [← Nat.mul_div_cancel' hadvd, ← Nat.mul_div_cancel' hbdvd, hab]
  have hterm : ∀ n ∈ S, 1 / (n : ℝ) ^ 2 = (1 / (d : ℝ) ^ 2) * (1 / ((n / d : ℕ) : ℝ) ^ 2) := by
    intro n hn
    obtain ⟨hn1, -, -, hdvd⟩ := hmem n hn
    have hn0 : 0 < n := hn1
    have hn_eq : n = d * (n / d) := (Nat.mul_div_cancel' hdvd).symm
    have h2 : ((n : ℝ)) = (d : ℝ) * ((n / d : ℕ) : ℝ) := by
      conv_lhs => rw [hn_eq]
      push_cast
      ring
    rw [h2, mul_pow]
    ring
  have hsub : S.image (fun n => n / d) ⊆ Finset.Ioo ⌊Z / (d : ℝ)⌋₊ (R + 1) := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    obtain ⟨hn1, hnR, hnZ, hdvd⟩ := hmem n hn
    have hn0 : 0 < n := hn1
    have hn_eq : n = d * (n / d) := (Nat.mul_div_cancel' hdvd).symm
    have he : ((n : ℝ)) = (d : ℝ) * ((n / d : ℕ) : ℝ) := by
      conv_lhs => rw [hn_eq]
      push_cast
      ring
    have h1 : Z / (d : ℝ) < ((n / d : ℕ) : ℝ) := by
      rw [div_lt_iff₀ hdR]
      linarith [hnZ, he]
    have h2 : ((⌊Z / (d : ℝ)⌋₊ : ℕ) : ℝ) < ((n / d : ℕ) : ℝ) :=
      lt_of_le_of_lt (Nat.floor_le (by positivity : (0 : ℝ) ≤ Z / (d : ℝ))) h1
    have h2' : ⌊Z / (d : ℝ)⌋₊ < n / d := by exact_mod_cast h2
    have h3 : n / d ≤ R := Nat.le_trans (Nat.div_le_self n d) hnR
    exact Finset.mem_Ioo.mpr ⟨h2', by omega⟩
  calc (∑ n ∈ S, 1 / (n : ℝ) ^ 2)
      = ∑ n ∈ S, (1 / (d : ℝ) ^ 2) * (1 / ((n / d : ℕ) : ℝ) ^ 2) :=
        Finset.sum_congr rfl hterm
    _ = (1 / (d : ℝ) ^ 2) * ∑ n ∈ S, 1 / ((n / d : ℕ) : ℝ) ^ 2 := by
        rw [Finset.mul_sum]
    _ = (1 / (d : ℝ) ^ 2) * ∑ k ∈ S.image (fun n => n / d), 1 / (k : ℝ) ^ 2 := by
        rw [← Finset.sum_image (f := fun k : ℕ => 1 / (k : ℝ) ^ 2) (g := fun n : ℕ => n / d)
          (fun x hx y hy h => hinj hx hy h)]
    _ ≤ (1 / (d : ℝ) ^ 2) * ∑ k ∈ Finset.Ioo ⌊Z / (d : ℝ)⌋₊ (R + 1), 1 / (k : ℝ) ^ 2 := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact Finset.sum_le_sum_of_subset_of_nonneg hsub (fun k _ _ => by positivity)
    _ ≤ (1 / (d : ℝ) ^ 2) * (2 / (Z / (d : ℝ))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        have h := inv_sq_Ioo_le323 (Z / (d : ℝ)) (by positivity) (R + 1)
        simpa [one_div] using h

/-! ## 11. The Euler product gives `n / φ n` with coefficients `2/p` -/

private lemma weight_nonneg323 (d : ℕ) :
    0 ≤ ∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) := by
  refine Finset.prod_nonneg (fun p hp => ?_)
  have h2 : (2 : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp))
  have h3 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have h4 : (0 : ℝ) ≤ 2 * (p : ℝ) - 1 := by linarith
  have h5 : (0 : ℝ) < ((p : ℝ) - 1) ^ 2 := by positivity
  exact div_nonneg h4 (le_of_lt h5)

/-! ## 12. The leaf -/

private lemma tail_bound323 (Z : ℝ) (hZ : 0 < Z) (R : ℕ) :
    (∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => Z < (r : ℝ)),
        1 / (Nat.totient r : ℝ) ^ 2)
      ≤ 2 * (1000 * (∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)))) / Z := by
  classical
  set T : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) with hTdef
  have hTsum : Summable (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) :=
    Real.summable_nat_rpow.mpr (by norm_num)
  set D : Finset ℕ := Finset.Icc 1 R with hD
  set S : Finset ℕ := D.filter (fun n : ℕ => Z < (n : ℝ)) with hS
  have hSmem : ∀ n ∈ S, 1 ≤ n ∧ n ≤ R := by
    intro n hn
    rw [hS, hD, Finset.mem_filter, Finset.mem_Icc] at hn
    exact hn.1
  -- (A) the pointwise convolution bound
  have hA : ∀ n ∈ S, 1 / (Nat.totient n : ℝ) ^ 2
      ≤ (1 / (n : ℝ) ^ 2) * (∑ d ∈ D, if (d ∣ n ∧ Squarefree d) then
          (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0) := by
    intro n hn
    obtain ⟨hn1, hnR⟩ := hSmem n hn
    have hn0 : n ≠ 0 := by omega
    have hdiv : (n.divisors.filter (fun d => Squarefree d))
        = D.filter (fun d => d ∣ n ∧ Squarefree d) := by
      ext d
      simp only [hD, Finset.mem_filter, Finset.mem_Icc]
      constructor
      · rintro ⟨hdv, hsq⟩
        have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hdv
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdvd (by omega),
          le_trans (Nat.le_of_dvd (by omega) hdvd) hnR⟩, hdvd, hsq⟩
      · rintro ⟨⟨h1, h2⟩, hdvd, hsq⟩
        exact ⟨Nat.mem_divisors.mpr ⟨hdvd, hn0⟩, hsq⟩
    have htwo : (∑ d ∈ D, if (d ∣ n ∧ Squarefree d) then
          (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0)
        = ∑ d ∈ n.divisors.filter (fun d => Squarefree d),
            ∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) := by
      rw [← Finset.sum_filter, hdiv]
    have hkey : 1 / (Nat.totient n : ℝ) ^ 2
        = (1 / (n : ℝ) ^ 2) * ((n : ℝ) / (Nat.totient n : ℝ)) ^ 2 := by
      rw [div_pow]
      field_simp
    rw [hkey, sq_div_totient_sq323 n hn1, htwo]
  -- (B) exchange the two sums
  have hB : (∑ n ∈ S, 1 / (Nat.totient n : ℝ) ^ 2)
      ≤ ∑ d ∈ D, (if Squarefree d then
          (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0) *
          (∑ n ∈ S.filter (fun n => d ∣ n), 1 / (n : ℝ) ^ 2) := by
    calc (∑ n ∈ S, 1 / (Nat.totient n : ℝ) ^ 2)
        ≤ ∑ n ∈ S, (1 / (n : ℝ) ^ 2) * (∑ d ∈ D, if (d ∣ n ∧ Squarefree d) then
            (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0) :=
          Finset.sum_le_sum hA
      _ = ∑ n ∈ S, ∑ d ∈ D, (1 / (n : ℝ) ^ 2) *
            (if (d ∣ n ∧ Squarefree d) then
              (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0) := by
          refine Finset.sum_congr rfl (fun n _ => ?_)
          rw [Finset.mul_sum]
      _ = ∑ d ∈ D, ∑ n ∈ S, (1 / (n : ℝ) ^ 2) *
            (if (d ∣ n ∧ Squarefree d) then
              (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0) :=
          Finset.sum_comm
      _ = ∑ d ∈ D, (if Squarefree d then
            (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0) *
            (∑ n ∈ S.filter (fun n => d ∣ n), 1 / (n : ℝ) ^ 2) := by
          refine Finset.sum_congr rfl (fun d _ => ?_)
          by_cases hsq : Squarefree d
          · rw [if_pos hsq]
            have hL : (∑ n ∈ S, (1 / (n : ℝ) ^ 2) * (if (d ∣ n ∧ Squarefree d) then
                (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0))
                = ∑ n ∈ S.filter (fun n => d ∣ n),
                    (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) *
                      (1 / (n : ℝ) ^ 2) := by
              have hstep : ∀ n ∈ S, (1 / (n : ℝ) ^ 2) * (if (d ∣ n ∧ Squarefree d) then
                    (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0)
                  = (if d ∣ n then
                    (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) *
                      (1 / (n : ℝ) ^ 2) else 0) := by
                intro n _
                by_cases h : d ∣ n
                · rw [if_pos ⟨h, hsq⟩, if_pos h]; ring
                · rw [if_neg (fun hh => h hh.1), if_neg h, mul_zero]
              rw [Finset.sum_congr rfl hstep, ← Finset.sum_filter]
            rw [hL, Finset.mul_sum]
          · rw [if_neg hsq, zero_mul]
            refine Finset.sum_eq_zero (fun n _ => ?_)
            rw [if_neg (fun h => hsq h.2), mul_zero]
  -- (C) the bound for each `d`
  have hC : ∀ d ∈ D, (if Squarefree d then
        (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0) *
        (∑ n ∈ S.filter (fun n => d ∣ n), 1 / (n : ℝ) ^ 2)
      ≤ (if Squarefree d then
          (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)))
          else 0) * (2 / Z) := by
    intro d hd
    have hd1 : 1 ≤ d := (Finset.mem_Icc.mp hd).1
    have hinner := multiples_tail323 Z hZ R d hd1
    by_cases hsq : Squarefree d
    · rw [if_pos hsq, if_pos hsq]
      have hGn : 0 ≤ ∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) :=
        weight_nonneg323 d
      have hdR : (0 : ℝ) < (d : ℝ) := by
        have h0 : 0 < d := by omega
        exact_mod_cast h0
      have hsplit : (∏ p ∈ d.primeFactors,
            ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2))) * (d : ℝ)
          = ∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2) := by
        have hd_cast : (d : ℝ) = ∏ p ∈ d.primeFactors, (p : ℝ) := by
          rw [← Nat.cast_prod, Nat.prod_primeFactors_of_squarefree hsq]
        rw [hd_cast, ← Finset.prod_mul_distrib]
        refine Finset.prod_congr rfl (fun p hp => ?_)
        have h2 : (2 : ℝ) ≤ (p : ℝ) := by
          exact_mod_cast (Nat.Prime.two_le (Nat.prime_of_mem_primeFactors hp))
        have hp0 : (p : ℝ) ≠ 0 := by linarith
        have hp1 : ((p : ℝ) - 1) ≠ 0 := by linarith
        field_simp
      have hZd : (0 : ℝ) < Z / (d : ℝ) := by positivity
      calc (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) *
              (∑ n ∈ S.filter (fun n => d ∣ n), 1 / (n : ℝ) ^ 2)
          ≤ (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) *
              ((1 / (d : ℝ) ^ 2) * (2 / (Z / (d : ℝ)))) :=
            mul_le_mul_of_nonneg_left hinner hGn
        _ = (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2))) *
              (2 / Z) := by
            rw [← hsplit]
            field_simp
    · rw [if_neg hsq, if_neg hsq, zero_mul, zero_mul]
  -- (D) bound the `d`-sum
  have hDsum : (∑ d ∈ D, (if Squarefree d then
        (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2))) else 0))
      ≤ 1000 * T := by
    have h1 : ∀ d ∈ D, (if Squarefree d then
        (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2))) else 0)
        ≤ 1000 * (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
      intro d hd
      by_cases hsq : Squarefree d
      · rw [if_pos hsq]
        exact weight_le323 d hsq
      · rw [if_neg hsq]
        have hdR : (0 : ℝ) < (d : ℝ) := by
          have h0 : 0 < d := by
            have := hd
            rw [hD, Finset.mem_Icc] at this
            omega
          exact_mod_cast h0
        have hnn := Real.rpow_nonneg (le_of_lt hdR) (-(3 / 2 : ℝ))
        nlinarith
    calc (∑ d ∈ D, (if Squarefree d then
          (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2))) else 0))
        ≤ ∑ d ∈ D, 1000 * (d : ℝ) ^ (-(3 / 2 : ℝ)) := Finset.sum_le_sum h1
      _ = 1000 * ∑ d ∈ D, (d : ℝ) ^ (-(3 / 2 : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ 1000 * T := by
          apply mul_le_mul_of_nonneg_left _ (by norm_num)
          exact hTsum.sum_le_tsum D (fun i _ => Real.rpow_nonneg (by positivity) _)
  have key : (∑ r ∈ S, 1 / (Nat.totient r : ℝ) ^ 2) ≤ 2 * (1000 * T) / Z := by
    calc (∑ r ∈ S, 1 / (Nat.totient r : ℝ) ^ 2)
        ≤ ∑ d ∈ D, (if Squarefree d then
              (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) - 1) ^ 2)) else 0) *
              (∑ n ∈ S.filter (fun n => d ∣ n), 1 / (n : ℝ) ^ 2) := hB
      _ ≤ ∑ d ∈ D, (if Squarefree d then
              (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)))
              else 0) * (2 / Z) := Finset.sum_le_sum hC
      _ = (2 / Z) * ∑ d ∈ D, (if Squarefree d then
              (∏ p ∈ d.primeFactors, ((2 * (p : ℝ) - 1) / ((p : ℝ) * ((p : ℝ) - 1) ^ 2)))
              else 0) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl (fun d _ => ?_)
          ring
      _ ≤ (2 / Z) * (1000 * T) := mul_le_mul_of_nonneg_left hDsum (by positivity)
      _ = 2 * (1000 * T) / Z := by ring
  exact key

/-- LEAF: Vaughan 1981 chapter 3, book page 34, the elementary fact printed under display
3.23: Σ_{q>Z} φ(q)^{-2} ≪ Z^{-1}, together with the convergence of Σ_q φ(q)^{-2}, which
gives the bound min(Z^{-1}, 1) for every Z > 0, uniformly in the upper cutoff R.
Class MEDIUM: from Σ_{q≤R} (q/φ(q))² ≪ R, which follows from
q/φ(q) = Σ_{d|q} μ(d)²/φ(d), and partial summation. -/
theorem leaf_totient_sq_tail512 :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ Z : ℝ, 0 < Z → ∀ R : ℕ,
      ∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => Z < (r : ℝ)),
          1 / (Nat.totient r : ℝ) ^ 2 ≤ K * min (1 / Z) 1 := by
  classical
  set T : ℝ := ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) with hTdef
  have hT0 : 0 ≤ T := tsum_nonneg (fun n => Real.rpow_nonneg (by positivity) _)
  refine ⟨2 * (1000 * T) + 2, by linarith, ?_⟩
  intro Z hZ R
  by_cases hZ1 : Z ≤ 1
  · -- `min (1/Z) 1 = 1`: bound the whole range by `1 + Σ_{r>1}`
    have hstep1 : (∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => Z < (r : ℝ)),
        1 / (Nat.totient r : ℝ) ^ 2) ≤ ∑ r ∈ Finset.Icc 1 R, 1 / (Nat.totient r : ℝ) ^ 2 :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
        (fun i _ _ => by positivity)
    have hsub2 : Finset.Icc 1 R ⊆
        insert 1 ((Finset.Icc 1 R).filter (fun r : ℕ => 1 < (r : ℝ))) := by
      intro r hr
      rw [Finset.mem_Icc] at hr
      rcases eq_or_lt_of_le hr.1 with h | h
      · rw [← h]; exact Finset.mem_insert_self _ _
      · refine Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr hr, ?_⟩)
        have : (1 : ℝ) < (r : ℝ) := by exact_mod_cast h
        exact this
    have hnin : (1 : ℕ) ∉ (Finset.Icc 1 R).filter (fun r : ℕ => 1 < (r : ℝ)) := by
      simp
    have hstep2 : (∑ r ∈ Finset.Icc 1 R, 1 / (Nat.totient r : ℝ) ^ 2)
        ≤ 1 + ∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => 1 < (r : ℝ)),
            1 / (Nat.totient r : ℝ) ^ 2 := by
      calc (∑ r ∈ Finset.Icc 1 R, 1 / (Nat.totient r : ℝ) ^ 2)
          ≤ ∑ r ∈ insert 1 ((Finset.Icc 1 R).filter (fun r : ℕ => 1 < (r : ℝ))),
              1 / (Nat.totient r : ℝ) ^ 2 :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub2 (fun i _ _ => by positivity)
        _ = 1 / (Nat.totient 1 : ℝ) ^ 2 +
              ∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => 1 < (r : ℝ)),
                1 / (Nat.totient r : ℝ) ^ 2 := Finset.sum_insert hnin
        _ = 1 + ∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => 1 < (r : ℝ)),
                1 / (Nat.totient r : ℝ) ^ 2 := by
            rw [Nat.totient_one]; norm_num
    have hstep3 : (∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => 1 < (r : ℝ)),
        1 / (Nat.totient r : ℝ) ^ 2) ≤ 2 * (1000 * T) / 1 := tail_bound323 1 one_pos R
    have hmin : min (1 / Z) 1 = 1 := by
      apply min_eq_right
      rw [le_div_iff₀ hZ]
      linarith
    rw [hmin]
    linarith
  · have hZgt : 1 < Z := not_le.mp hZ1
    have hmin : min (1 / Z) 1 = 1 / Z := by
      apply min_eq_left
      rw [div_le_one hZ]
      linarith
    rw [hmin]
    have hstep1 : (∑ r ∈ (Finset.Icc 1 R).filter (fun r : ℕ => Z < (r : ℝ)),
        1 / (Nat.totient r : ℝ) ^ 2) ≤ 2 * (1000 * T) / Z := tail_bound323 Z hZ R
    have hstep2 : 2 * (1000 * T) / Z ≤ (2 * (1000 * T) + 2) / Z := by
      rw [add_div]
      have : (0 : ℝ) ≤ 2 / Z := by positivity
      linarith
    have hstep3 : (2 * (1000 * T) + 2) / Z = (2 * (1000 * T) + 2) * (1 / Z) := by
      rw [mul_one_div]
    linarith

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

/-- Verbatim check: the assembly has exactly the type of `leaf_vaughan_323_512`.
The original `type_of%` form does not elaborate in this environment, so the statement of
`leaf_vaughan_323_512` is written out verbatim. -/
example :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N → ∀ X : ℝ, 0 < X → ∀ M : ℕ,
      ‖∑ q ∈ Finset.Ioc ⌊X⌋₊ M,
          (ArithmeticFunction.moebius q : ℂ) ^ 2 / (Nat.totient q : ℂ) ^ 2 *
            ramanujan512 q N‖ ≤
        K * ∑ d ∈ N.divisors,
          (ArithmeticFunction.moebius d : ℝ) ^ 2 / (Nat.totient d : ℝ) *
            min ((d : ℝ) / X) 1 := leaf_vaughan_323_512_of_leaves

end LeanLab.BHP1997.Section2MS
