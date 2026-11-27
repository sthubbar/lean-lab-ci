/-
FALSE. The leaf mellin_prime_power_series1622 of Linnik1951/SPLIT_mellin_lnL_expansion1622
is false as formalized.

On the line 1/2 + 1/ln N + i t with N at least 8 the real part sigma lies strictly between
1/2 and 1, since ln 8 > 2. The prime power double series inside the Mellin integral is
written with the unconditional sum tsum. For each prime p the inner sum over exponents
converges, its first term is chi of p times p to the minus s, and the rest is at most a
constant times p to the minus 2 sigma, which is summable over primes. So if the outer sum
over primes were summable, the sum of p to the minus sigma over primes would converge,
which fails for sigma at most 1, Nat.Primes.summable_rpow of Mathlib. Hence the outer tsum
is 0 for every t, and the left side of the leaf is the Mellin integral of 0, which is 0.
The right side carries the damping exp of minus p^k over N and is absolutely summable; at
q = 1, chi = 1, alpha = 0 every term is a positive real, so the right side is not 0.
The witness is N = 8, q = 1, chi = 1, alpha = 0.

The paper identity needs the series in the conditionally convergent or analytically
continued sense, or the integral taken on a line with real part above 1; the lab tsum gives
neither. This file imports the leaf file only so that the negated statement elaborates in
the same environment; no theorem here uses the leaf.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.SPLIT_mellin_lnL_expansion1622

namespace LeanLab.Linnik1951

/-- e^2 < 8, so ln 8 > 2: the line 1/2 + 1/ln 8 + i t lies left of the line of real part 1. -/
theorem two_lt_log_eight1622F : 2 < Real.log 8 := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  have h := Real.exp_one_lt_d9
  have hpos := Real.exp_pos 1
  have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
    rw [← Real.exp_nat_mul]; norm_num
  rw [h2]; nlinarith

/-- The real part of the line at N = 8. -/
theorem re_line_eight1622F (t : ℝ) :
    (mellinLine1622 8 t).re = 1 / 2 + 1 / Real.log 8 := by
  rw [mellinLine1622, Complex.add_re, Complex.ofReal_re]
  simp

/-- At N = 8 the real part of the line lies strictly between 1/2 and 1. -/
theorem sigma_eight_bounds1622F : 1 / 2 < 1 / 2 + 1 / Real.log 8 ∧ 1 / 2 + 1 / Real.log 8 < 1 := by
  have h := two_lt_log_eight1622F
  have hpos : 0 < Real.log 8 := by linarith
  have h0 : 0 < 1 / Real.log 8 := by positivity
  refine ⟨by linarith, ?_⟩
  have : 1 / Real.log 8 < 1 / 2 := by
    rw [div_lt_div_iff₀ hpos (by norm_num)]; linarith
  linarith

/-- The trivial character modulo 1 takes the value 1 at every natural number. -/
theorem chi_one_apply1622F (n : ℕ) : (1 : DirichletCharacter ℂ 1) (n : ZMod 1) = 1 :=
  MulChar.one_apply (isUnit_of_subsingleton _)

/-- The norm of the prime power p^(m+1) to the minus s is (p to the minus Re s)^(m+1). -/
theorem norm_term1622F (p : Nat.Primes) (m : ℕ) (s : ℂ) :
    ‖(((p : ℕ) : ℂ) ^ (m + 1)) ^ (-s)‖ = (((p : ℕ) : ℝ) ^ (-s.re)) ^ (m + 1) := by
  have hp : 0 < (p : ℕ) ^ (m + 1) := pow_pos p.prop.pos _
  have hc : (((p : ℕ) : ℂ) ^ (m + 1)) = (((p : ℕ) ^ (m + 1) : ℕ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.norm_natCast_cpow_of_pos hp, Complex.neg_re, Nat.cast_pow,
    Real.rpow_pow_comm (by positivity)]

/-- On the line at N = 8 the prime power double series of the trivial character modulo 1
is not summable over the primes, so its lab tsum is 0 at every height. -/
theorem not_summable_line_eight1622F (t : ℝ) :
    ¬ Summable (fun p : Nat.Primes => ∑' m : ℕ,
      ((m : ℂ) + 1)⁻¹ * (1 : DirichletCharacter ℂ 1) ((p : ℕ) ^ (m + 1)) *
        (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-(mellinLine1622 8 t))) := by
  intro hS
  set s := mellinLine1622 8 t with hs
  set σ := 1 / 2 + 1 / Real.log 8 with hσ
  have hre : s.re = σ := re_line_eight1622F t
  obtain ⟨hσ1, hσ2⟩ := sigma_eight_bounds1622F
  set c : ℝ := (2 : ℝ) ^ (-σ) with hc
  have hc1 : c < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  have hc0 : 0 < c := by positivity
  let a : Nat.Primes → ℕ → ℂ := fun p m =>
    ((m : ℂ) + 1)⁻¹ * (1 : DirichletCharacter ℂ 1) ((p : ℕ) ^ (m + 1)) *
        (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-s)
  let x : Nat.Primes → ℝ := fun p => ((p : ℕ) : ℝ) ^ (-σ)
  have hx0 : ∀ p, 0 ≤ x p := fun p => by positivity
  have hxc : ∀ p, x p ≤ c := fun p =>
    Real.rpow_le_rpow_of_nonpos (by norm_num) (by exact_mod_cast p.prop.two_le) (by linarith)
  have hnorm : ∀ p m, ‖a p m‖ = ((m : ℝ) + 1)⁻¹ * x p ^ (m + 1) := by
    intro p m
    show ‖((m : ℂ) + 1)⁻¹ * (1 : DirichletCharacter ℂ 1) ((p : ℕ) ^ (m + 1)) *
        (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-s)‖ = _
    rw [norm_mul, norm_mul, norm_term1622F, hre]
    have h1 : (1 : DirichletCharacter ℂ 1) (((p : ℕ) ^ (m + 1) : ℕ) : ZMod 1) = 1 :=
      chi_one_apply1622F _
    push_cast at h1
    rw [h1, norm_one, mul_one, norm_inv]
    congr 1
    have : (m : ℂ) + 1 = (((m : ℝ) + 1 : ℝ) : ℂ) := by push_cast; rfl
    rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
  have hle : ∀ p m, ‖a p m‖ ≤ x p ^ (m + 1) := by
    intro p m
    rw [hnorm]
    have : ((m : ℝ) + 1)⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) m])
    calc ((m : ℝ) + 1)⁻¹ * x p ^ (m + 1) ≤ 1 * x p ^ (m + 1) := by
          gcongr
      _ = _ := one_mul _
  have hgeo : ∀ p, Summable (fun m : ℕ => x p ^ (m + 1)) := fun p => by
    have := summable_geometric_of_lt_one (hx0 p) (lt_of_le_of_lt (hxc p) hc1)
    have h0 := this.mul_left (x p)
    have he : (fun m : ℕ => x p * x p ^ m) = fun m : ℕ => x p ^ (m + 1) := by
      funext m; ring
    rw [he] at h0; exact h0
  have hsa : ∀ p, Summable (a p) := fun p =>
    Summable.of_norm_bounded (hgeo p) (hle p)
  -- the tail beyond the first exponent
  let R : Nat.Primes → ℂ := fun p => ∑' m, a p (m + 1)
  have hR : ∀ p, ‖R p‖ ≤ (1 - c)⁻¹ * ((p : ℕ) : ℝ) ^ (-(2 * σ)) := by
    intro p
    have hxp := hx0 p
    have hx1 : x p < 1 := lt_of_le_of_lt (hxc p) hc1
    have hsum2 : Summable (fun m : ℕ => x p ^ (m + 2)) := by
      have h0 := (summable_geometric_of_lt_one hxp hx1).mul_left (x p ^ 2)
      have he : (fun m : ℕ => x p ^ 2 * x p ^ m) = fun m : ℕ => x p ^ (m + 2) := by
        funext m; ring
      rw [he] at h0; exact h0
    have h1 : ‖R p‖ ≤ ∑' m : ℕ, x p ^ (m + 2) :=
      tsum_of_norm_bounded hsum2.hasSum (fun m => hle p (m + 1))
    have h2 : ∑' m : ℕ, x p ^ (m + 2) = x p ^ 2 * (1 - x p)⁻¹ := by
      rw [← tsum_geometric_of_lt_one hxp hx1, ← tsum_mul_left]
      congr 1; funext m; ring
    have h3 : x p ^ 2 = ((p : ℕ) : ℝ) ^ (-(2 * σ)) := by
      simp only [x]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      congr 1; push_cast; ring
    have h4 : (1 - x p)⁻¹ ≤ (1 - c)⁻¹ := by
      apply inv_anti₀ (by linarith) (by linarith [hxc p])
    rw [h2, h3] at h1
    calc ‖R p‖ ≤ _ := h1
      _ ≤ ((p : ℕ) : ℝ) ^ (-(2 * σ)) * (1 - c)⁻¹ := by
          gcongr
      _ = _ := mul_comm _ _
  have hRs : Summable R := by
    refine Summable.of_norm_bounded ?_ hR
    exact (Nat.Primes.summable_rpow.mpr (by linarith)).mul_left _
  have hhead : Summable (fun p => a p 0) := by
    have : (fun p => a p 0) = fun p => (∑' m, a p m) - R p := by
      funext p
      rw [(hsa p).tsum_eq_zero_add]; ring
    rw [this]; exact hS.sub hRs
  have hn := hhead.norm
  have : (fun p => ‖a p 0‖) = fun p : Nat.Primes => ((p : ℕ) : ℝ) ^ (-σ) := by
    funext p; rw [hnorm]; simp [x]
  rw [this] at hn
  have := Nat.Primes.summable_rpow.mp hn
  linarith

/-- The damped double series at q = 1, chi = 1, alpha = 0 is a sum of positive reals and
is not 0. -/
theorem rhs_pos1622F (hdamp : Summable (fun x : Nat.Primes × ℕ =>
      Real.exp (-(((x.1 : ℕ) : ℝ) ^ (x.2 + 1) / ((8 : ℕ) : ℝ))))) :
    (∑' p : Nat.Primes, ∑' m : ℕ,
        ((m : ℂ) + 1)⁻¹ * (1 : DirichletCharacter ℂ 1) ((p : ℕ) ^ (m + 1)) *
          (Real.exp (-(((p : ℕ) : ℝ) ^ (m + 1) / ((8 : ℕ) : ℝ))) : ℂ) *
            Complex.exp
              ((-(2 * Real.pi * (0 : ℝ) * (((p : ℕ) : ℝ) ^ (m + 1))) : ℝ) * Complex.I)) ≠ 0 := by
  let r : Nat.Primes → ℕ → ℝ := fun p m =>
    ((m : ℝ) + 1)⁻¹ * Real.exp (-(((p : ℕ) : ℝ) ^ (m + 1) / ((8 : ℕ) : ℝ)))
  have hterm : ∀ (p : Nat.Primes) (m : ℕ),
      ((m : ℂ) + 1)⁻¹ * (1 : DirichletCharacter ℂ 1) ((p : ℕ) ^ (m + 1)) *
          (Real.exp (-(((p : ℕ) : ℝ) ^ (m + 1) / ((8 : ℕ) : ℝ))) : ℂ) *
            Complex.exp
              ((-(2 * Real.pi * (0 : ℝ) * (((p : ℕ) : ℝ) ^ (m + 1))) : ℝ) * Complex.I)
        = ((r p m : ℝ) : ℂ) := by
    intro p m
    have h1 : (1 : DirichletCharacter ℂ 1) (((p : ℕ) ^ (m + 1) : ℕ) : ZMod 1) = 1 :=
      chi_one_apply1622F _
    push_cast at h1
    rw [h1]
    simp only [r, mul_zero, zero_mul, neg_zero, Complex.ofReal_zero, Complex.exp_zero,
      mul_one]
    push_cast; ring
  have hr0 : ∀ p m, 0 ≤ r p m := fun p m => by positivity
  have hrs : Summable (fun x : Nat.Primes × ℕ => r x.1 x.2) := by
    refine Summable.of_nonneg_of_le (fun x => hr0 x.1 x.2) (fun x => ?_) hdamp
    have : ((x.2 : ℝ) + 1)⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (by linarith [Nat.cast_nonneg (α := ℝ) x.2])
    calc r x.1 x.2 ≤ 1 * Real.exp (-(((x.1 : ℕ) : ℝ) ^ (x.2 + 1) / ((8 : ℕ) : ℝ))) := by
          show ((x.2 : ℝ) + 1)⁻¹ * _ ≤ _
          gcongr
      _ = _ := one_mul _
  have hinner : ∀ p, Summable (r p) := fun p => hrs.prod_factor p
  have houter : Summable (fun p => ∑' m, r p m) := hrs.prod
  have htwo : 0 < ∑' m, r ⟨2, Nat.prime_two⟩ m :=
    (hinner _).tsum_pos (hr0 _) 0 (by positivity)
  have hpos : 0 < ∑' p, ∑' m, r p m :=
    houter.tsum_pos (fun p => tsum_nonneg (hr0 p)) ⟨2, Nat.prime_two⟩ htwo
  have heq : (∑' p : Nat.Primes, ∑' m : ℕ, ((r p m : ℝ) : ℂ))
      = ((∑' p, ∑' m, r p m : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    congr 1; funext p
    rw [Complex.ofReal_tsum]
  simp_rw [hterm]
  rw [heq]
  exact_mod_cast hpos.ne'

/-- The Mellin integral of the zero coefficient is 0. -/
theorem mellinU_zero1622F (N : ℕ) (α : ℝ) : mellinU1622 N (fun _ => 0) α = 0 := by
  simp [mellinU1622]


/-- FALSE witness for mellin_prime_power_series1622: its statement, verbatim, fails at
N = 8, q = 1, chi = 1, alpha = 0. The left side is the Mellin integral of a lab tsum that is
0 at every height, the right side is a positive real. -/
theorem not_mellin_prime_power_series1622 : ¬ (∀ N : ℕ, 2 ≤ N → ∀ (q : ℕ) [NeZero q],
    ∀ χ : DirichletCharacter ℂ q, ∀ α : ℝ,
      mellinU1622 N
          (fun t : ℝ => ∑' p : Nat.Primes, ∑' m : ℕ,
            ((m : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (m + 1)) *
              (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-(mellinLine1622 N t))) α
        = ∑' p : Nat.Primes, ∑' m : ℕ,
            ((m : ℂ) + 1)⁻¹ * χ ((p : ℕ) ^ (m + 1)) *
              (Real.exp (-(((p : ℕ) : ℝ) ^ (m + 1) / (N : ℝ))) : ℂ) *
                Complex.exp
                  ((-(2 * Real.pi * α * (((p : ℕ) : ℝ) ^ (m + 1))) : ℝ) * Complex.I)) := by
  intro h
  have h8 := h 8 (by norm_num) 1 1 0
  have hzero : (fun t : ℝ => ∑' p : Nat.Primes, ∑' m : ℕ,
      ((m : ℂ) + 1)⁻¹ * (1 : DirichletCharacter ℂ 1) ((p : ℕ) ^ (m + 1)) *
        (((p : ℕ) : ℂ) ^ (m + 1)) ^ (-(mellinLine1622 8 t))) = fun _ => 0 := by
    funext t
    exact tsum_eq_zero_of_not_summable (not_summable_line_eight1622F t)
  rw [hzero, mellinU_zero1622F] at h8
  exact rhs_pos1622F (prime_power_damping_summable473 8 (by norm_num)) h8.symm

end LeanLab.Linnik1951
