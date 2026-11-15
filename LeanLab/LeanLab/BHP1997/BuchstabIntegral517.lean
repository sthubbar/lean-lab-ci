/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character.
The paper proves 5.17 with the words "a straightforward consequence of the prime number
theorem". For the rough cofactor `n3` or `n5` of display 5.15 that consequence rests on the
Buchstab identity for integers without small prime factors, and on its continuous counterpart,
the integral equation of Buchstab's function. This file proves the continuous counterpart from
the defining equations `IsBuchstab`:

* `buchstab_integral_equation`: `u ω(u) = 1 + ∫_1^{u-1} ω` for `u ≥ 2`;
* `buchstab_half_le`, `buchstab_le_one_of_one_le`, `buchstab_bounds`: `1/2 ≤ ω ≤ 1` on `[1, ∞)`;
* `buchstab_lipschitz_abs`: `ω` is 1-Lipschitz on `[1, ∞)`;
* `buchstab_multiplicative`: for `z > 1` and `n ≥ z^2`,
  `ω(log n / log z) / log z = 1 / log n + ∫_z^{√n} ω(log (n/k) / log k) / (k log^2 k) dk`,
  the density form of the Buchstab identity, the sum over the least prime factor `k`;
* `buchstab_multiplicative_low`: for `z ≤ n ≤ z^2` the density is `1 / log n`.
* `buchstab_multiplicative_all`: both ranges in one statement, upper limit `max z √n`;
* `buchstab_cofactor_change`: the dilation `s = p t` for the cofactor integral at level `p`;
* `sum_sub_integral_le_of_lipschitz`, `sum_sub_integral_le_of_local`,
  `buchstab_density_sum_integral`: sums over the integers of an interval against integrals;
* `buchstab_density_lipschitz`, `buchstab_cofactor_lipschitz`, `buchstab_integrand_lipschitz`:
  the regularity in `n` and in the least prime factor `k` that those comparisons need.

Everything here is PROVED from `IsBuchstab` and, where stated, `ZeroBelowOne`. No sorry.

No new definition. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Decomp514a

namespace LeanLab.BHP1997.LowerShortC165
open LeanLab.ChenDoubleSieve.Wu04Functional
open MeasureTheory Set

/-- P0069 page 51 display 5.17, Buchstab function input. The integral equation of Buchstab's
function, `u ω(u) = 1 + ∫_1^{u-1} ω(t) dt` for `u ≥ 2`, from the delay differential equation
`(u ω(u))' = ω(u - 1)` and `ω(2) = 1/2` by the fundamental theorem of calculus. -/
theorem buchstab_integral_equation {ω : ℝ → ℝ} (hω : IsBuchstab ω) {u : ℝ} (hu : 2 ≤ u) :
    u * ω u = 1 + ∫ t in (1:ℝ)..(u - 1), ω t := by
  have hcont : ContinuousOn (fun v : ℝ => v * ω v) (Icc 2 u) :=
    continuousOn_id.mul (hω.1.mono (fun t ht => by change 1 ≤ t; linarith [ht.1]))
  have hci : ContinuousOn (fun t : ℝ => ω (t - 1)) (uIcc 2 u) := by
    rw [uIcc_of_le hu]
    apply hω.1.comp (by fun_prop)
    intro t ht
    change 1 ≤ t - 1
    linarith [ht.1]
  have h : (∫ t in (2:ℝ)..u, ω (t - 1)) = u * ω u - 2 * ω 2 :=
    intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le (f := fun v : ℝ => v * ω v) hu hcont
      (fun v hv => hω.2.2 v hv.1) hci.intervalIntegrable
  have h2 : ω 2 = 1 / 2 := hω.2.1 2 (by norm_num) le_rfl
  have hs : (∫ t in (2:ℝ)..u, ω (t - 1)) = ∫ t in (1:ℝ)..(u - 1), ω t := by
    rw [intervalIntegral.integral_comp_sub_right (fun t => ω t) 1]
    norm_num
  rw [← hs, h, h2]
  ring

/-- P0069 page 51 display 5.17, Buchstab function input. Buchstab's function is at least `1/2`
on `[1, ∞)`: it is `1/u ≥ 1/2` on `[1, 2]`, and the integral equation propagates the bound,
`u ω(u) ≥ 1 + (u - 2)/2 = u/2`. -/
theorem buchstab_half_le {ω : ℝ → ℝ} (hω : IsBuchstab ω) {u : ℝ} (hu : 1 ≤ u) :
    1 / 2 ≤ ω u := by
  have step : ∀ n : ℕ, ∀ u : ℝ, 1 ≤ u → u ≤ (n : ℝ) + 2 → 1 / 2 ≤ ω u := by
    intro n
    induction n with
    | zero =>
      intro u hu hu2
      have hu2' : u ≤ 2 := by simpa using hu2
      rw [hω.2.1 u hu hu2']
      rw [div_le_div_iff₀ (by norm_num) (by linarith)]
      linarith
    | succ n ih =>
      intro u hu huMax
      push_cast at huMax
      by_cases h2 : u ≤ 2
      · exact ih u hu (by linarith [Nat.cast_nonneg (α := ℝ) n])
      have h2' : 2 ≤ u := (lt_of_not_ge h2).le
      have heq := buchstab_integral_equation hω h2'
      have hle : (1:ℝ) ≤ u - 1 := by linarith
      have hint : (∫ _t in (1:ℝ)..(u - 1), (1 / 2 : ℝ)) ≤ ∫ t in (1:ℝ)..(u - 1), ω t := by
        apply intervalIntegral.integral_mono_on hle intervalIntegrable_const
        · apply ContinuousOn.intervalIntegrable
          rw [uIcc_of_le hle]
          exact hω.1.mono (fun t ht => ht.1)
        · intro t ht
          exact ih t ht.1 (by linarith [ht.2])
      rw [intervalIntegral.integral_const, smul_eq_mul] at hint
      have hu0 : 0 < u := by linarith
      have hmul : u * (1 / 2) ≤ u * ω u := by
        rw [heq]
        linarith
      exact le_of_mul_le_mul_left hmul hu0
  exact step ⌈u⌉₊ u hu (by linarith [Nat.le_ceil u])

/-- P0069 page 51 display 5.17, Buchstab function input. Buchstab's function is at most `1` on
`[1, ∞)`, with no extension convention needed. -/
theorem buchstab_le_one_of_one_le {ω : ℝ → ℝ} (hω : IsBuchstab ω) {u : ℝ} (hu : 1 ≤ u) :
    ω u ≤ 1 := by
  by_cases h2 : u ≤ 2
  · rw [hω.2.1 u hu h2]
    exact (div_le_one (by linarith : 0 < u)).mpr hu
  · exact (LeanLab.ChenDoubleSieve.Wu04Buchstab.buchstab_le_567144 hω (by linarith)).trans
      (by norm_num)

/-- P0069 page 51 display 5.17, Buchstab function input. The two sided bound
`1/2 ≤ ω(u) ≤ 1` for `u ≥ 1`. -/
theorem buchstab_bounds {ω : ℝ → ℝ} (hω : IsBuchstab ω) {u : ℝ} (hu : 1 ≤ u) :
    1 / 2 ≤ ω u ∧ ω u ≤ 1 :=
  ⟨buchstab_half_le hω hu, buchstab_le_one_of_one_le hω hu⟩

/-- P0069 page 51 display 5.17, Buchstab function input. Buchstab's function is 1-Lipschitz on
`[1, ∞)`, in the symmetric form `|ω u - ω v| ≤ |u - v|`. -/
theorem buchstab_lipschitz_abs {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {u v : ℝ} (hu : 1 ≤ u) (hv : 1 ≤ v) : |ω u - ω v| ≤ |u - v| := by
  rcases le_total u v with h | h
  · have := Decomp514a.two_density_buchstab_lipschitz hω hz hu h
    rw [abs_sub_comm u v, abs_of_nonneg (by linarith : 0 ≤ v - u)]
    exact this
  · have := Decomp514a.two_density_buchstab_lipschitz hω hz hv h
    rw [abs_sub_comm (ω u) (ω v), abs_of_nonneg (by linarith : 0 ≤ u - v)]
    exact this

/-- P0069 page 51 display 5.17, Buchstab function input. Change of variables
`w = L / t - 1` in the integral equation, in the logarithmic variable `t = log k`:
for `0 < l` and `2 l ≤ L`, `∫_l^{L/2} ω((L - t)/t) / t^2 dt = (1/L) ∫_1^{L/l - 1} ω(w) dw`. -/
theorem buchstab_log_change {ω : ℝ → ℝ} (hω : IsBuchstab ω) {l L : ℝ} (hl : 0 < l)
    (hL : 2 * l ≤ L) :
    (∫ t in l..(L / 2), ω ((L - t) / t) / t ^ 2) =
      (∫ w in (1:ℝ)..(L / l - 1), ω w) / L := by
  have hL0 : 0 < L := by linarith
  have hle : l ≤ L / 2 := by linarith
  have hd : ∀ t ∈ uIcc l (L / 2),
      HasDerivAt (fun t : ℝ => L / t - 1) (-L / t ^ 2) t := by
    intro t ht
    rw [uIcc_of_le hle] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have h1 := ((hasDerivAt_const t L).div (hasDerivAt_id t) ht0.ne').sub_const 1
    refine h1.congr_deriv ?_
    simp
  have hf' : ContinuousOn (fun t : ℝ => -L / t ^ 2) (uIcc l (L / 2)) := by
    rw [uIcc_of_le hle]
    apply continuousOn_const.div (continuousOn_id.pow 2)
    intro t ht
    have ht0 : 0 < t := by linarith [ht.1]
    exact pow_ne_zero 2 ht0.ne'
  have hg : ContinuousOn ω ((fun t : ℝ => L / t - 1) '' uIcc l (L / 2)) := by
    apply hω.1.mono
    rintro _ ⟨t, ht, rfl⟩
    rw [uIcc_of_le hle] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    change 1 ≤ L / t - 1
    have : 2 ≤ L / t := by
      rw [le_div_iff₀ ht0]
      linarith [ht.2]
    linarith
  have hcv := intervalIntegral.integral_comp_mul_deriv' hd hf' hg
  have hcongr : (∫ t in l..(L / 2), ω ((L - t) / t) / t ^ 2) =
      ∫ t in l..(L / 2), (-1 / L) * ((ω ∘ fun t : ℝ => L / t - 1) t * (-L / t ^ 2)) := by
    apply intervalIntegral.integral_congr
    intro t ht
    rw [uIcc_of_le hle] at ht
    have ht0 : 0 < t := by linarith [ht.1]
    have he : (L - t) / t = L / t - 1 := by field_simp
    dsimp only [Function.comp]
    rw [he]
    field_simp
  have h1 : L / (L / 2) - 1 = 1 := by field_simp; norm_num
  rw [hcongr, intervalIntegral.integral_const_mul, hcv]
  rw [h1, intervalIntegral.integral_symm]
  field_simp

/-- P0069 page 51 display 5.17, Buchstab function input. The change of variables
`w = log n / log k - 1` in the variable `k` of the least prime factor: for `z > 1` and
`n ≥ z^2`, `∫_z^{√n} ω(log (n/k) / log k) / (k log^2 k) dk = (1 / log n) ∫_1^{u - 1} ω`
with `u = log n / log z`. -/
theorem buchstab_prime_variable_change {ω : ℝ → ℝ} (hω : IsBuchstab ω) {z n : ℝ}
    (hz1 : 1 < z) (hn : z ^ 2 ≤ n) :
    (∫ k in z..Real.sqrt n, ω (Real.log (n / k) / Real.log k) / (k * Real.log k ^ 2)) =
      (∫ w in (1:ℝ)..(Real.log n / Real.log z - 1), ω w) / Real.log n := by
  have hz0 : 0 < z := by linarith
  have hl : 0 < Real.log z := Real.log_pos hz1
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hzs : z ≤ Real.sqrt n := Real.le_sqrt_of_sq_le hn
  have hLs : Real.log (Real.sqrt n) = Real.log n / 2 := Real.log_sqrt hn0.le
  have hL2 : 2 * Real.log z ≤ Real.log n := by
    have := Real.log_le_log hz0 hzs
    rw [hLs] at this
    linarith
  have hL0 : 0 < Real.log n := by linarith
  have hd : ∀ k ∈ uIcc z (Real.sqrt n),
      HasDerivAt (fun k : ℝ => Real.log n / Real.log k - 1)
        (-Real.log n / (k * Real.log k ^ 2)) k := by
    intro k hk
    rw [uIcc_of_le hzs] at hk
    have hk0 : 0 < k := by linarith [hk.1]
    have hlk : 0 < Real.log k := Real.log_pos (by linarith [hk.1])
    have h1 := ((hasDerivAt_const k (Real.log n)).div (Real.hasDerivAt_log hk0.ne')
      hlk.ne').sub_const 1
    refine h1.congr_deriv ?_
    simp only [zero_mul, zero_sub]
    field_simp
  have hf' : ContinuousOn (fun k : ℝ => -Real.log n / (k * Real.log k ^ 2))
      (uIcc z (Real.sqrt n)) := by
    rw [uIcc_of_le hzs]
    have hlogc : ContinuousOn Real.log (Icc z (Real.sqrt n)) :=
      Real.continuousOn_log.mono (fun k hk => by
        have : 0 < k := by linarith [hk.1]
        exact this.ne')
    apply continuousOn_const.div (continuousOn_id.mul (hlogc.pow 2))
    intro k hk
    have hk0 : 0 < k := by linarith [hk.1]
    have hlk : 0 < Real.log k := Real.log_pos (by linarith [hk.1])
    exact (mul_pos hk0 (pow_pos hlk 2)).ne'
  have hg : ContinuousOn ω
      ((fun k : ℝ => Real.log n / Real.log k - 1) '' uIcc z (Real.sqrt n)) := by
    apply hω.1.mono
    rintro _ ⟨k, hk, rfl⟩
    rw [uIcc_of_le hzs] at hk
    have hk0 : 0 < k := by linarith [hk.1]
    have hlk : 0 < Real.log k := Real.log_pos (by linarith [hk.1])
    have hlk2 := Real.log_le_log hk0 hk.2
    rw [hLs] at hlk2
    change 1 ≤ Real.log n / Real.log k - 1
    have : 2 ≤ Real.log n / Real.log k := by
      rw [le_div_iff₀ hlk]
      linarith
    linarith
  have hcv := intervalIntegral.integral_comp_mul_deriv' hd hf' hg
  have hcongr :
      (∫ k in z..Real.sqrt n, ω (Real.log (n / k) / Real.log k) / (k * Real.log k ^ 2)) =
      ∫ k in z..Real.sqrt n, (-1 / Real.log n) *
        ((ω ∘ fun k : ℝ => Real.log n / Real.log k - 1) k *
          (-Real.log n / (k * Real.log k ^ 2))) := by
    apply intervalIntegral.integral_congr
    intro k hk
    rw [uIcc_of_le hzs] at hk
    have hk0 : 0 < k := by linarith [hk.1]
    have hlk : 0 < Real.log k := Real.log_pos (by linarith [hk.1])
    have he : Real.log (n / k) / Real.log k = Real.log n / Real.log k - 1 := by
      rw [Real.log_div hn0.ne' hk0.ne']
      field_simp
    dsimp only [Function.comp]
    rw [he]
    field_simp
  have h1 : Real.log n / Real.log (Real.sqrt n) - 1 = 1 := by
    rw [hLs]
    field_simp
    norm_num
  rw [hcongr, intervalIntegral.integral_const_mul, hcv]
  rw [h1, intervalIntegral.integral_symm]
  field_simp

/-- P0069 page 51 display 5.17, Buchstab function input. The density form of the Buchstab
identity for integers `n` with no prime factor below `z`, summed over the least prime factor
`k`: for `z > 1` and `n ≥ z^2`,
`ω(log n / log z) / log z = 1 / log n + ∫_z^{√n} ω(log (n/k) / log k) / (k log^2 k) dk`.
The term `1 / log n` is the density of the primes, the integral that of the products `k m`
with `k` prime in `[z, √n]` and `m` free of prime factors below `k`. -/
theorem buchstab_multiplicative {ω : ℝ → ℝ} (hω : IsBuchstab ω) {z n : ℝ}
    (hz1 : 1 < z) (hn : z ^ 2 ≤ n) :
    ω (Real.log n / Real.log z) / Real.log z =
      1 / Real.log n +
        ∫ k in z..Real.sqrt n, ω (Real.log (n / k) / Real.log k) / (k * Real.log k ^ 2) := by
  have hz0 : 0 < z := by linarith
  have hl : 0 < Real.log z := Real.log_pos hz1
  have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hn
  have hL2 : 2 * Real.log z ≤ Real.log n := by
    have := Real.log_le_log (by positivity : (0:ℝ) < z ^ 2) hn
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hL0 : 0 < Real.log n := by linarith
  have hu : 2 ≤ Real.log n / Real.log z := by
    rw [le_div_iff₀ hl]
    linarith
  have heq := buchstab_integral_equation hω hu
  have hI : (∫ w in (1:ℝ)..(Real.log n / Real.log z - 1), ω w) =
      Real.log n / Real.log z * ω (Real.log n / Real.log z) - 1 := by linarith
  rw [buchstab_prime_variable_change hω hz1 hn, hI]
  field_simp
  ring

/-- P0069 page 51 display 5.17, Buchstab function input. In the range `z ≤ n ≤ z^2` an integer
with no prime factor below `z` is prime, and accordingly the Buchstab density
`ω(log n / log z) / log z` is the prime density `1 / log n`. -/
theorem buchstab_multiplicative_low {ω : ℝ → ℝ} (hω : IsBuchstab ω) {z n : ℝ}
    (hz1 : 1 < z) (hzn : z ≤ n) (hn : n ≤ z ^ 2) :
    ω (Real.log n / Real.log z) / Real.log z = 1 / Real.log n := by
  have hz0 : 0 < z := by linarith
  have hl : 0 < Real.log z := Real.log_pos hz1
  have hn0 : 0 < n := by linarith
  have hL1 : Real.log z ≤ Real.log n := Real.log_le_log hz0 hzn
  have hL2 : Real.log n ≤ 2 * Real.log z := by
    have := Real.log_le_log hn0 hn
    rw [Real.log_pow] at this
    push_cast at this
    linarith
  have hL0 : 0 < Real.log n := by linarith
  have hu1 : 1 ≤ Real.log n / Real.log z := by
    rw [le_div_iff₀ hl]
    linarith
  have hu2 : Real.log n / Real.log z ≤ 2 := by
    rw [div_le_iff₀ hl]
    linarith
  rw [hω.2.1 _ hu1 hu2]
  field_simp

/-- P0069 page 51 display 5.17, Buchstab function input. The integrand of the Buchstab
identity in the least prime factor variable is nonnegative and at most `1 / (k log^2 k)`,
for `k > 1` and any positive `n`, with the zero extension below one. -/
theorem buchstab_integrand_bounds {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {k : ℝ} (hk : 1 < k) (n : ℝ) :
    0 ≤ ω (Real.log (n / k) / Real.log k) / (k * Real.log k ^ 2) ∧
      ω (Real.log (n / k) / Real.log k) / (k * Real.log k ^ 2) ≤
        1 / (k * Real.log k ^ 2) := by
  have hlk : 0 < Real.log k := Real.log_pos hk
  have hpos : 0 < k * Real.log k ^ 2 := by positivity
  have h0 := Decomp514a.two_density_buchstab_nonneg hω hz (Real.log (n / k) / Real.log k)
  have h1 := extended_buchstab_le_one hω hz (Real.log (n / k) / Real.log k)
  exact ⟨div_nonneg h0 hpos.le, div_le_div_of_nonneg_right h1 hpos.le⟩

/-- P0069 page 51 display 5.17, passage from sums over integers to integrals. A function that
is `K`-Lipschitz and continuous on `[a, b]` has `∑_{a < n ≤ b} g(n)` within `K (b - a)` of
`∫_a^b g`. This is the comparison used when the densities of display 5.17 are summed over the
integers of an interval. -/
theorem sum_sub_integral_le_of_lipschitz (g : ℝ → ℝ) {K : ℝ} (a : ℕ) :
    ∀ b : ℕ, a ≤ b → ContinuousOn g (Icc (a:ℝ) b) →
      (∀ x ∈ Icc (a:ℝ) b, ∀ y ∈ Icc (a:ℝ) b, |g x - g y| ≤ K * |x - y|) →
      |(∑ n ∈ Finset.Ioc a b, g n) - ∫ t in (a:ℝ)..b, g t| ≤ K * ((b:ℝ) - a) := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base =>
    intro _ _
    simp
  | succ b hab ih =>
    intro hc hK
    have hab' : (a:ℝ) ≤ b := by exact_mod_cast hab
    have hsub : Icc (a:ℝ) b ⊆ Icc (a:ℝ) ((b + 1 : ℕ) : ℝ) := by
      apply Icc_subset_Icc_right
      push_cast
      linarith
    have ih' := ih (hc.mono hsub) (fun x hx y hy => hK x (hsub hx) y (hsub hy))
    have hb1 : ((b + 1 : ℕ) : ℝ) = (b:ℝ) + 1 := by push_cast; ring
    have hbm : (b:ℝ) ∈ Icc (a:ℝ) ((b + 1 : ℕ) : ℝ) := ⟨hab', by rw [hb1]; linarith⟩
    have hb1m : ((b + 1 : ℕ) : ℝ) ∈ Icc (a:ℝ) ((b + 1 : ℕ) : ℝ) :=
      ⟨by rw [hb1]; linarith, le_rfl⟩
    have hK0 : 0 ≤ K := by
      have h := hK _ hb1m _ hbm
      rw [hb1] at h
      have h' : |(b:ℝ) + 1 - b| = 1 := by norm_num
      rw [h', mul_one] at h
      exact (abs_nonneg _).trans h
    have hi1 : IntervalIntegrable g volume (a:ℝ) b := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hab']
      exact hc.mono hsub
    have hsub2 : Icc (b:ℝ) ((b + 1 : ℕ) : ℝ) ⊆ Icc (a:ℝ) ((b + 1 : ℕ) : ℝ) :=
      Icc_subset_Icc_left hab'
    have hbb : (b:ℝ) ≤ ((b + 1 : ℕ) : ℝ) := by rw [hb1]; linarith
    have hi2 : IntervalIntegrable g volume (b:ℝ) ((b + 1 : ℕ) : ℝ) := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hbb]
      exact hc.mono hsub2
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hlast : |g ((b + 1 : ℕ) : ℝ) - ∫ t in (b:ℝ)..((b + 1 : ℕ) : ℝ), g t| ≤ K := by
      have hconst : (∫ _t in (b:ℝ)..((b + 1 : ℕ) : ℝ), g ((b + 1 : ℕ) : ℝ)) =
          g ((b + 1 : ℕ) : ℝ) := by
        rw [intervalIntegral.integral_const, hb1]
        simp
      have hdiff : g ((b + 1 : ℕ) : ℝ) - ∫ t in (b:ℝ)..((b + 1 : ℕ) : ℝ), g t =
          ∫ t in (b:ℝ)..((b + 1 : ℕ) : ℝ), (g ((b + 1 : ℕ) : ℝ) - g t) := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const hi2, hconst]
      rw [hdiff]
      have hbd := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (b:ℝ)) (b := ((b + 1 : ℕ) : ℝ)) (C := K)
        (f := fun t => g ((b + 1 : ℕ) : ℝ) - g t) (by
          intro t ht
          rw [uIoc_of_le hbb] at ht
          have htm : t ∈ Icc (a:ℝ) ((b + 1 : ℕ) : ℝ) := ⟨by linarith [ht.1], ht.2⟩
          have h := hK _ hb1m t htm
          rw [Real.norm_eq_abs]
          have h1 : |((b + 1 : ℕ) : ℝ) - t| ≤ 1 := by
            rw [abs_of_nonneg (by linarith [ht.2])]
            rw [hb1]
            linarith [ht.1]
          exact h.trans (by nlinarith [abs_nonneg (((b + 1 : ℕ) : ℝ) - t)]))
      rw [Real.norm_eq_abs] at hbd
      have h1 : |((b + 1 : ℕ) : ℝ) - (b:ℝ)| = 1 := by rw [hb1]; norm_num
      rw [h1, mul_one] at hbd
      exact hbd
    rw [Finset.sum_Ioc_succ_top hab, ← hsplit]
    have ht := abs_add_le ((∑ n ∈ Finset.Ioc a b, g n) - ∫ t in (a:ℝ)..b, g t)
      (g ((b + 1 : ℕ) : ℝ) - ∫ t in (b:ℝ)..((b + 1 : ℕ) : ℝ), g t)
    have he : (∑ n ∈ Finset.Ioc a b, g n) + g ((b + 1 : ℕ) : ℝ) -
        ((∫ t in (a:ℝ)..b, g t) + ∫ t in (b:ℝ)..((b + 1 : ℕ) : ℝ), g t) =
        ((∑ n ∈ Finset.Ioc a b, g n) - ∫ t in (a:ℝ)..b, g t) +
        (g ((b + 1 : ℕ) : ℝ) - ∫ t in (b:ℝ)..((b + 1 : ℕ) : ℝ), g t) := by ring
    have hr : K * (((b + 1 : ℕ) : ℝ) - a) = K * ((b:ℝ) - a) + K := by
      rw [hb1]
      ring
    rw [he, hr]
    linarith

/-- P0069 page 51 display 5.17, Buchstab function input. The local density
`ω(log t / log z) / log z` of the integers with no prime factor below `z` is Lipschitz in `t`
on `[z, ∞)` with constant `1 / (z log^2 z)`. -/
theorem buchstab_density_lipschitz {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {z : ℝ} (hz1 : 1 < z) {s t : ℝ} (hs : z ≤ s) (ht : z ≤ t) :
    |ω (Real.log s / Real.log z) / Real.log z - ω (Real.log t / Real.log z) / Real.log z| ≤
      1 / (z * Real.log z ^ 2) * |s - t| := by
  have hz0 : 0 < z := by linarith
  have hl : 0 < Real.log z := Real.log_pos hz1
  have key : ∀ s t : ℝ, z ≤ s → s ≤ t →
      |ω (Real.log s / Real.log z) / Real.log z - ω (Real.log t / Real.log z) / Real.log z| ≤
        1 / (z * Real.log z ^ 2) * (t - s) := by
    intro s t hs hst
    have hs0 : 0 < s := by linarith
    have ht0 : 0 < t := by linarith
    have hus : 1 ≤ Real.log s / Real.log z := by
      rw [le_div_iff₀ hl, one_mul]
      exact Real.log_le_log hz0 hs
    have hust : Real.log s / Real.log z ≤ Real.log t / Real.log z :=
      div_le_div_of_nonneg_right (Real.log_le_log hs0 hst) hl.le
    have hlip := Decomp514a.two_density_buchstab_lipschitz hω hz hus hust
    have hlog : Real.log t - Real.log s ≤ (t - s) / z := by
      have h1 := Real.log_le_sub_one_of_pos (div_pos ht0 hs0)
      rw [Real.log_div ht0.ne' hs0.ne'] at h1
      have h2 : t / s - 1 = (t - s) / s := by field_simp
      rw [h2] at h1
      exact h1.trans (div_le_div_of_nonneg_left (by linarith) hz0 hs)
    rw [← sub_div, abs_div, abs_of_pos hl, div_le_iff₀ hl]
    have h3 : Real.log t / Real.log z - Real.log s / Real.log z ≤ (t - s) / z / Real.log z := by
      rw [← sub_div]
      exact div_le_div_of_nonneg_right hlog hl.le
    have h4 : 1 / (z * Real.log z ^ 2) * (t - s) * Real.log z = (t - s) / z / Real.log z := by
      field_simp
    rw [h4]
    linarith
  rcases le_total s t with h | h
  · rw [abs_sub_comm s t, abs_of_nonneg (by linarith : 0 ≤ t - s)]
    exact key s t hs h
  · rw [abs_sub_comm (ω (Real.log s / Real.log z) / Real.log z),
      abs_of_nonneg (by linarith : 0 ≤ s - t)]
    exact key t s ht h

/-- P0069 page 51 display 5.17, Buchstab function input. The local density
`ω(log t / log z) / log z` is continuous in `t` on `[z, ∞)`. -/
theorem buchstab_density_continuousOn {ω : ℝ → ℝ} (hω : IsBuchstab ω) {z : ℝ} (hz1 : 1 < z) :
    ContinuousOn (fun t : ℝ => ω (Real.log t / Real.log z) / Real.log z) (Ici z) := by
  have hz0 : 0 < z := by linarith
  have hl : 0 < Real.log z := Real.log_pos hz1
  have hlog : ContinuousOn (fun t : ℝ => Real.log t / Real.log z) (Ici z) :=
    (Real.continuousOn_log.mono (fun t ht => by
      have : 0 < t := lt_of_lt_of_le hz0 ht
      exact this.ne')).div_const _
  have hcomp : ContinuousOn (fun t : ℝ => ω (Real.log t / Real.log z)) (Ici z) := by
    apply hω.1.comp hlog
    intro t ht
    change 1 ≤ Real.log t / Real.log z
    rw [le_div_iff₀ hl, one_mul]
    exact Real.log_le_log hz0 ht
  exact hcomp.div_const _

/-- P0069 page 51 display 5.17, Buchstab function input, in the form used for sums over the
integers of an interval: for `z > 1` and integers `z ≤ a ≤ b`, the sum of the Buchstab density
`ω(log n / log z) / log z` over `a < n ≤ b` is within `(b - a) / (z log^2 z)` of its
integral. -/
theorem buchstab_density_sum_integral {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {z : ℝ} (hz1 : 1 < z) {a b : ℕ} (hza : z ≤ (a:ℝ)) (hab : a ≤ b) :
    |(∑ n ∈ Finset.Ioc a b, ω (Real.log (n:ℝ) / Real.log z) / Real.log z) -
        ∫ t in (a:ℝ)..b, ω (Real.log t / Real.log z) / Real.log z| ≤
      1 / (z * Real.log z ^ 2) * ((b:ℝ) - a) :=
  sum_sub_integral_le_of_lipschitz (fun t : ℝ => ω (Real.log t / Real.log z) / Real.log z)
    a b hab
    ((buchstab_density_continuousOn hω hz1).mono (fun _ ht => hza.trans ht.1))
    (fun _ hx _ hy => buchstab_density_lipschitz hω hz hz1 (hza.trans hx.1) (hza.trans hy.1))

/-- P0069 page 51 display 5.17, Buchstab function input. The Buchstab factor
`ω(log (n/k) / log k)` of the cofactor `n / k` at level `k` is Lipschitz in the least prime
factor variable `k` on `[z, √n]`, with constant `log n / (z log^2 z)`. This is the regularity
needed to sum it over primes `k` by the prime number theorem. -/
theorem buchstab_cofactor_lipschitz {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {z n : ℝ} (hz1 : 1 < z) {k k' : ℝ} (hk : z ≤ k) (hk' : z ≤ k') (hkn : k ^ 2 ≤ n)
    (hkn' : k' ^ 2 ≤ n) :
    |ω (Real.log (n / k) / Real.log k) - ω (Real.log (n / k') / Real.log k')| ≤
      Real.log n / (z * Real.log z ^ 2) * |k - k'| := by
  have hz0 : 0 < z := by linarith
  have hl : 0 < Real.log z := Real.log_pos hz1
  have key : ∀ k k' : ℝ, z ≤ k → k ≤ k' → k' ^ 2 ≤ n →
      |ω (Real.log (n / k) / Real.log k) - ω (Real.log (n / k') / Real.log k')| ≤
        Real.log n / (z * Real.log z ^ 2) * (k' - k) := by
    intro k k' hk hkk hkn'
    have hk0 : 0 < k := by linarith
    have hk'0 : 0 < k' := by linarith
    have hn0 : 0 < n := lt_of_lt_of_le (by positivity) hkn'
    have hlk : Real.log z ≤ Real.log k := Real.log_le_log hz0 hk
    have hlkk : Real.log k ≤ Real.log k' := Real.log_le_log hk0 hkk
    have hlk0 : 0 < Real.log k := by linarith
    have hlk'0 : 0 < Real.log k' := by linarith
    have hL2 : 2 * Real.log k' ≤ Real.log n := by
      have := Real.log_le_log (by positivity : (0:ℝ) < k' ^ 2) hkn'
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    have hL0 : 0 < Real.log n := by linarith
    have he : Real.log (n / k) / Real.log k = Real.log n / Real.log k - 1 := by
      rw [Real.log_div hn0.ne' hk0.ne']
      field_simp
    have he' : Real.log (n / k') / Real.log k' = Real.log n / Real.log k' - 1 := by
      rw [Real.log_div hn0.ne' hk'0.ne']
      field_simp
    have hv1 : 1 ≤ Real.log n / Real.log k' - 1 := by
      have : 2 ≤ Real.log n / Real.log k' := by
        rw [le_div_iff₀ hlk'0]
        linarith
      linarith
    have hvv : Real.log n / Real.log k' - 1 ≤ Real.log n / Real.log k - 1 := by
      have := div_le_div_of_nonneg_left hL0.le hlk0 hlkk
      linarith
    have hlip := Decomp514a.two_density_buchstab_lipschitz hω hz hv1 hvv
    have hlog : Real.log k' - Real.log k ≤ (k' - k) / z := by
      have h1 := Real.log_le_sub_one_of_pos (div_pos hk'0 hk0)
      rw [Real.log_div hk'0.ne' hk0.ne'] at h1
      have h2 : k' / k - 1 = (k' - k) / k := by field_simp
      rw [h2] at h1
      exact h1.trans (div_le_div_of_nonneg_left (by linarith) hz0 hk)
    have hdiff : (Real.log n / Real.log k - 1) - (Real.log n / Real.log k' - 1) =
        Real.log n * (Real.log k' - Real.log k) / (Real.log k * Real.log k') := by
      field_simp
      ring
    have hden : Real.log z ^ 2 ≤ Real.log k * Real.log k' := by nlinarith
    have hnum : Real.log n * (Real.log k' - Real.log k) ≤ Real.log n * ((k' - k) / z) :=
      mul_le_mul_of_nonneg_left hlog hL0.le
    have hnum0 : 0 ≤ Real.log n * ((k' - k) / z) :=
      mul_nonneg hL0.le (div_nonneg (by linarith) hz0.le)
    have hbound : Real.log n * (Real.log k' - Real.log k) / (Real.log k * Real.log k') ≤
        Real.log n * ((k' - k) / z) / Real.log z ^ 2 :=
      (div_le_div_of_nonneg_right hnum (by positivity)).trans
        (div_le_div_of_nonneg_left hnum0 (by positivity) hden)
    have hfin : Real.log n * ((k' - k) / z) / Real.log z ^ 2 =
        Real.log n / (z * Real.log z ^ 2) * (k' - k) := by
      field_simp
    rw [he, he', abs_sub_comm]
    linarith
  rcases le_total k k' with h | h
  · rw [abs_sub_comm k k', abs_of_nonneg (by linarith : 0 ≤ k' - k)]
    exact key k k' hk h hkn'
  · rw [abs_sub_comm (ω (Real.log (n / k) / Real.log k)),
      abs_of_nonneg (by linarith : 0 ≤ k - k')]
    exact key k' k hk' h hkn

/-- P0069 page 51 display 5.17, Buchstab function input. The density form of the Buchstab
identity in one statement for every `n ≥ z`: the integral over the least prime factor `k` runs
over `[z, √n]`, which is empty when `n < z^2`. -/
theorem buchstab_multiplicative_all {ω : ℝ → ℝ} (hω : IsBuchstab ω) {z n : ℝ}
    (hz1 : 1 < z) (hzn : z ≤ n) :
    ω (Real.log n / Real.log z) / Real.log z =
      1 / Real.log n +
        ∫ k in z..max z (Real.sqrt n),
          ω (Real.log (n / k) / Real.log k) / (k * Real.log k ^ 2) := by
  have hz0 : 0 < z := by linarith
  by_cases h : z ^ 2 ≤ n
  · rw [max_eq_right (Real.le_sqrt_of_sq_le h)]
    exact buchstab_multiplicative hω hz1 h
  · have h' : n ≤ z ^ 2 := (lt_of_not_ge h).le
    have hs : Real.sqrt n ≤ z := by
      have := Real.sqrt_le_sqrt h'
      rwa [Real.sqrt_sq hz0.le] at this
    rw [max_eq_left hs, intervalIntegral.integral_same, add_zero]
    exact buchstab_multiplicative_low hω hz1 hzn h'

/-- P0069 page 51 display 5.17, Buchstab function input. The dilation `s = p t` that turns the
integral of the Buchstab density at level `p` over the cofactor range `(lo / p, hi / p]` into an
integral over the range `(lo, hi]` of the product `s = p t`. -/
theorem buchstab_cofactor_change (ω : ℝ → ℝ) {p : ℝ} (hp : 1 < p) (lo hi : ℝ) :
    (∫ t in (lo / p)..(hi / p), ω (Real.log t / Real.log p) / Real.log p) =
      ∫ s in lo..hi, ω (Real.log (s / p) / Real.log p) / (p * Real.log p) := by
  have hp0 : 0 < p := by linarith
  have hl : 0 < Real.log p := Real.log_pos hp
  have h := intervalIntegral.integral_comp_div (a := lo) (b := hi)
    (fun t : ℝ => ω (Real.log t / Real.log p) / Real.log p) hp0.ne'
  have he : (∫ s in lo..hi, ω (Real.log (s / p) / Real.log p) / (p * Real.log p)) =
      ∫ s in lo..hi, (1 / p) * (ω (Real.log (s / p) / Real.log p) / Real.log p) := by
    apply intervalIntegral.integral_congr
    intro s _
    dsimp only
    field_simp
  rw [he, intervalIntegral.integral_const_mul, h, smul_eq_mul]
  field_simp

/-- P0069 page 51 display 5.17, passage from sums over integers to integrals, local form. If
`g` is continuous on `[a, b]` and on each unit interval `[n, n + 1]` it stays within `K n` of
its value at the right end, then `∑_{a < n ≤ b} g(n)` is within `∑_{a ≤ n < b} K n` of
`∫_a^b g`. This form keeps the decay of the local constants, as needed for the sum over the
least prime factor in the Buchstab identity. -/
theorem sum_sub_integral_le_of_local (g : ℝ → ℝ) (K : ℕ → ℝ) (a : ℕ) :
    ∀ b : ℕ, a ≤ b → ContinuousOn g (Icc (a:ℝ) b) →
      (∀ n : ℕ, a ≤ n → n < b → ∀ t ∈ Icc (n:ℝ) ((n:ℝ) + 1),
        |g ((n:ℝ) + 1) - g t| ≤ K n) →
      |(∑ n ∈ Finset.Ioc a b, g n) - ∫ t in (a:ℝ)..b, g t| ≤ ∑ n ∈ Finset.Ico a b, K n := by
  intro b hab
  induction b, hab using Nat.le_induction with
  | base =>
    intro _ _
    simp
  | succ b hab ih =>
    intro hc hK
    have hab' : (a:ℝ) ≤ b := by exact_mod_cast hab
    have hb1 : ((b + 1 : ℕ) : ℝ) = (b:ℝ) + 1 := by push_cast; ring
    have hsub : Icc (a:ℝ) b ⊆ Icc (a:ℝ) ((b + 1 : ℕ) : ℝ) := by
      apply Icc_subset_Icc_right
      rw [hb1]
      linarith
    have ih' := ih (hc.mono hsub) (fun n han hnb t ht => hK n han (by omega) t ht)
    have hi1 : IntervalIntegrable g volume (a:ℝ) b := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hab']
      exact hc.mono hsub
    have hsub2 : Icc (b:ℝ) ((b + 1 : ℕ) : ℝ) ⊆ Icc (a:ℝ) ((b + 1 : ℕ) : ℝ) :=
      Icc_subset_Icc_left hab'
    have hbb : (b:ℝ) ≤ ((b + 1 : ℕ) : ℝ) := by rw [hb1]; linarith
    have hi2 : IntervalIntegrable g volume (b:ℝ) ((b + 1 : ℕ) : ℝ) := by
      apply ContinuousOn.intervalIntegrable
      rw [uIcc_of_le hbb]
      exact hc.mono hsub2
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have hlast : |g ((b + 1 : ℕ) : ℝ) - ∫ t in (b:ℝ)..((b + 1 : ℕ) : ℝ), g t| ≤ K b := by
      have hconst : (∫ _t in (b:ℝ)..((b + 1 : ℕ) : ℝ), g ((b + 1 : ℕ) : ℝ)) =
          g ((b + 1 : ℕ) : ℝ) := by
        rw [intervalIntegral.integral_const, hb1]
        simp
      have hdiff : g ((b + 1 : ℕ) : ℝ) - ∫ t in (b:ℝ)..((b + 1 : ℕ) : ℝ), g t =
          ∫ t in (b:ℝ)..((b + 1 : ℕ) : ℝ), (g ((b + 1 : ℕ) : ℝ) - g t) := by
        rw [intervalIntegral.integral_sub intervalIntegrable_const hi2, hconst]
      rw [hdiff]
      have hbd := intervalIntegral.norm_integral_le_of_norm_le_const
        (a := (b:ℝ)) (b := ((b + 1 : ℕ) : ℝ)) (C := K b)
        (f := fun t => g ((b + 1 : ℕ) : ℝ) - g t) (by
          intro t ht
          rw [uIoc_of_le hbb] at ht
          rw [Real.norm_eq_abs, hb1]
          exact hK b hab (Nat.lt_succ_self b) t ⟨ht.1.le, by rw [← hb1]; exact ht.2⟩)
      rw [Real.norm_eq_abs] at hbd
      have h1 : |((b + 1 : ℕ) : ℝ) - (b:ℝ)| = 1 := by rw [hb1]; norm_num
      rw [h1, mul_one] at hbd
      exact hbd
    rw [Finset.sum_Ioc_succ_top hab, Finset.sum_Ico_succ_top hab, ← hsplit]
    have ht := abs_add_le ((∑ n ∈ Finset.Ioc a b, g n) - ∫ t in (a:ℝ)..b, g t)
      (g ((b + 1 : ℕ) : ℝ) - ∫ t in (b:ℝ)..((b + 1 : ℕ) : ℝ), g t)
    have he : (∑ n ∈ Finset.Ioc a b, g n) + g ((b + 1 : ℕ) : ℝ) -
        ((∫ t in (a:ℝ)..b, g t) + ∫ t in (b:ℝ)..((b + 1 : ℕ) : ℝ), g t) =
        ((∑ n ∈ Finset.Ioc a b, g n) - ∫ t in (a:ℝ)..b, g t) +
        (g ((b + 1 : ℕ) : ℝ) - ∫ t in (b:ℝ)..((b + 1 : ℕ) : ℝ), g t) := by ring
    rw [he]
    linarith

/-- P0069 page 51 display 5.17, Buchstab function input. The integrand
`ω(log (n/k) / log k) / (k log^2 k)` of the Buchstab identity is Lipschitz in the least prime
factor variable `k` on `[z, √n]`, with constant
`(log n / log^2 z + 1 + 2 / log z) / (z^2 log^2 z)`, which decays like `1 / z^2`. -/
theorem buchstab_integrand_lipschitz {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {z n : ℝ} (hz1 : 1 < z) {k k' : ℝ} (hk : z ≤ k) (hk' : z ≤ k') (hkn : k ^ 2 ≤ n)
    (hkn' : k' ^ 2 ≤ n) :
    |ω (Real.log (n / k) / Real.log k) / (k * Real.log k ^ 2) -
        ω (Real.log (n / k') / Real.log k') / (k' * Real.log k' ^ 2)| ≤
      (Real.log n / Real.log z ^ 2 + 1 + 2 / Real.log z) / (z ^ 2 * Real.log z ^ 2) *
        |k - k'| := by
  have hz0 : 0 < z := by linarith
  have hl : 0 < Real.log z := Real.log_pos hz1
  have key : ∀ k k' : ℝ, z ≤ k → k ≤ k' → k ^ 2 ≤ n → k' ^ 2 ≤ n →
      |ω (Real.log (n / k) / Real.log k) / (k * Real.log k ^ 2) -
          ω (Real.log (n / k') / Real.log k') / (k' * Real.log k' ^ 2)| ≤
        (Real.log n / Real.log z ^ 2 + 1 + 2 / Real.log z) / (z ^ 2 * Real.log z ^ 2) *
          (k' - k) := by
    intro k k' hk hkk hkn hkn'
    have hk0 : 0 < k := by linarith
    have hk'0 : 0 < k' := by linarith
    have hlk : Real.log z ≤ Real.log k := Real.log_le_log hz0 hk
    have hlkk : Real.log k ≤ Real.log k' := Real.log_le_log hk0 hkk
    have hlk0 : 0 < Real.log k := by linarith
    have hlk'0 : 0 < Real.log k' := by linarith
    have hL0 : 0 ≤ Real.log n := by
      have := Real.log_le_log (by positivity : (0:ℝ) < k' ^ 2) hkn'
      rw [Real.log_pow] at this
      push_cast at this
      linarith
    have hd0 : 0 ≤ k' - k := by linarith
    have hA := buchstab_cofactor_lipschitz hω hz hz1 hk (hk.trans hkk) hkn hkn'
    rw [abs_sub_comm k k', abs_of_nonneg hd0] at hA
    have hA'0 := Decomp514a.two_density_buchstab_nonneg hω hz
      (Real.log (n / k') / Real.log k')
    have hA'1 := extended_buchstab_le_one hω hz (Real.log (n / k') / Real.log k')
    have hB0 : 0 < 1 / (k * Real.log k ^ 2) := by positivity
    have hBz : 1 / (k * Real.log k ^ 2) ≤ 1 / (z * Real.log z ^ 2) := by gcongr
    have hlog : k * (Real.log k' - Real.log k) ≤ k' - k := by
      have h1 := Real.log_le_sub_one_of_pos (div_pos hk'0 hk0)
      rw [Real.log_div hk'0.ne' hk0.ne'] at h1
      have h2 : k' / k - 1 = (k' - k) / k := by field_simp
      rw [h2, le_div_iff₀ hk0] at h1
      linarith
    have hnum : k' * Real.log k' ^ 2 - k * Real.log k ^ 2 ≤
        (k' - k) * (Real.log k' ^ 2 + 2 * Real.log k') := by
      have hm := mul_le_mul hlog (by linarith : Real.log k' + Real.log k ≤ 2 * Real.log k')
        (by linarith) hd0
      nlinarith
    have hBB0 : 0 ≤ 1 / (k * Real.log k ^ 2) - 1 / (k' * Real.log k' ^ 2) := by
      have : 1 / (k' * Real.log k' ^ 2) ≤ 1 / (k * Real.log k ^ 2) := by gcongr
      linarith
    have hBB : 1 / (k * Real.log k ^ 2) - 1 / (k' * Real.log k' ^ 2) ≤
        (1 + 2 / Real.log z) / (z ^ 2 * Real.log z ^ 2) * (k' - k) := by
      have e1 : 1 / (k * Real.log k ^ 2) - 1 / (k' * Real.log k' ^ 2) =
          (k' * Real.log k' ^ 2 - k * Real.log k ^ 2) /
            (k * Real.log k ^ 2 * (k' * Real.log k' ^ 2)) := by
        field_simp
      have e2 : (k' - k) * (Real.log k' ^ 2 + 2 * Real.log k') /
            (k * Real.log k ^ 2 * (k' * Real.log k' ^ 2)) =
          (k' - k) * (1 / (k * k' * Real.log k ^ 2) +
            2 / (k * k' * Real.log k ^ 2 * Real.log k')) := by
        field_simp
      have e3 : (1 + 2 / Real.log z) / (z ^ 2 * Real.log z ^ 2) * (k' - k) =
          (k' - k) * (1 / (z * z * Real.log z ^ 2) +
            2 / (z * z * Real.log z ^ 2 * Real.log z)) := by
        field_simp
      have hk'z : z ≤ k' := hk.trans hkk
      have hlk'z : Real.log z ≤ Real.log k' := hlk.trans hlkk
      have b1 : 1 / (k * k' * Real.log k ^ 2) ≤ 1 / (z * z * Real.log z ^ 2) := by gcongr
      have b2 : 2 / (k * k' * Real.log k ^ 2 * Real.log k') ≤
          2 / (z * z * Real.log z ^ 2 * Real.log z) := by gcongr
      rw [e1, e3]
      refine (div_le_div_of_nonneg_right hnum (by positivity)).trans ?_
      rw [e2]
      exact mul_le_mul_of_nonneg_left (add_le_add b1 b2) hd0
    have e : ω (Real.log (n / k) / Real.log k) / (k * Real.log k ^ 2) -
        ω (Real.log (n / k') / Real.log k') / (k' * Real.log k' ^ 2) =
        (ω (Real.log (n / k) / Real.log k) - ω (Real.log (n / k') / Real.log k')) *
            (1 / (k * Real.log k ^ 2)) +
          ω (Real.log (n / k') / Real.log k') *
            (1 / (k * Real.log k ^ 2) - 1 / (k' * Real.log k' ^ 2)) := by
      ring
    rw [e]
    calc _ ≤ |(ω (Real.log (n / k) / Real.log k) - ω (Real.log (n / k') / Real.log k')) *
            (1 / (k * Real.log k ^ 2))| +
          |ω (Real.log (n / k') / Real.log k') *
            (1 / (k * Real.log k ^ 2) - 1 / (k' * Real.log k' ^ 2))| := abs_add_le _ _
      _ = |ω (Real.log (n / k) / Real.log k) - ω (Real.log (n / k') / Real.log k')| *
            (1 / (k * Real.log k ^ 2)) +
          ω (Real.log (n / k') / Real.log k') *
            (1 / (k * Real.log k ^ 2) - 1 / (k' * Real.log k' ^ 2)) := by
        rw [abs_mul, abs_mul, abs_of_pos hB0, abs_of_nonneg hA'0, abs_of_nonneg hBB0]
      _ ≤ Real.log n / (z * Real.log z ^ 2) * (k' - k) * (1 / (z * Real.log z ^ 2)) +
          1 * ((1 + 2 / Real.log z) / (z ^ 2 * Real.log z ^ 2) * (k' - k)) :=
        add_le_add (mul_le_mul hA hBz hB0.le (by positivity))
          (mul_le_mul hA'1 hBB hBB0 zero_le_one)
      _ = _ := by
        field_simp
        ring
  rcases le_total k k' with h | h
  · rw [abs_sub_comm k k', abs_of_nonneg (by linarith : 0 ≤ k' - k)]
    exact key k k' hk h hkn hkn'
  · rw [abs_sub_comm (ω (Real.log (n / k) / Real.log k) / (k * Real.log k ^ 2)),
      abs_of_nonneg (by linarith : 0 ≤ k - k')]
    exact key k' k hk' h hkn' hkn

end LeanLab.BHP1997.LowerShortC165

#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_integral_equation
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_half_le
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_bounds
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_lipschitz_abs
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_log_change
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_prime_variable_change
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_multiplicative
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_multiplicative_low
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_integrand_bounds
#print axioms LeanLab.BHP1997.LowerShortC165.sum_sub_integral_le_of_lipschitz
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_density_lipschitz
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_density_continuousOn
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_density_sum_integral
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_cofactor_lipschitz
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_multiplicative_all
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_cofactor_change
#print axioms LeanLab.BHP1997.LowerShortC165.sum_sub_integral_le_of_local
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_integrand_lipschitz
