/-
P0069 Baker, Harman and Pintz 1997, Section 5, page 51, display 5.17 with no character.
The paper proves 5.17 with the words "a straightforward consequence of the prime number
theorem". For the rough cofactor `n3` or `n5` of display 5.15 the main term of that consequence
is the Buchstab identity for densities. `BuchstabIntegral517` proves it for one real `n`, with
an integral over the least prime factor. This file sums it over the integers of an interval and
replaces that integral by a sum over the integers `k`:

* `buchstab_identity_discrete`: for a level `z ≥ 3` and an integer `1 ≤ n ≤ b`,
  `ω(log n / log z) / log z = [z ≤ n] / log n + ∑_{z ≤ k ≤ b} ω(log (n/k) / log k) / (k log^2 k)`
  up to `(2 log n + 8) / z`;
* `buchstab_cofactor_pair_compare`, `buchstab_cofactor_pair_zero`: at one level `k` the sum over
  the products `n = k m` in `(a, b]` of the product density equals the sum over the cofactors
  `m` in `(a / k, b / k]` of the Buchstab density at level `k`, up to `2 b / k^2 + 4`, and both
  vanish when `k^2 > b`;
* `buchstab_main_term_integers`: the Buchstab density sum at level `z` over `(a, b]` equals the
  sum over the integers `k ≥ z`, weighted by the prime density `1 / log k`, of the indicator of
  `a < k ≤ b` plus the Buchstab density sum at level `k` over the cofactors, up to
  `b (2 log b + 12) / z + 4 √b`. No prime occurs in it. This is the same statement shape as
  `leaf_buchstab_main_term` of `RoughDensity517` with each prime `p` replaced by an integer `k`
  of weight `1 / log k`, so what separates the two is the prime number theorem in `k` alone.

This is a second, integral based route to the main term; `RoughDensity517b` and
`RoughDensity517c` reach the same end by telescoping the level. Everything here is PROVED from
`IsBuchstab` and `ZeroBelowOne`, with no open step. No new definition. AI wrote the Lean code.
Goldbach is open.
-/
import LeanLab.BHP1997.BuchstabIntegral517

namespace LeanLab.BHP1997.LowerShortC165
open LeanLab.ChenDoubleSieve.Wu04Functional
open MeasureTheory Set

/-- P0069 page 51 display 5.17, bookkeeping for the sum over the least prime factor: the tail
of `∑ 1 / k^2` from `z ≥ 2` is at most `2 / z`. -/
theorem inv_sq_sum_le {z : ℕ} (hz : 2 ≤ z) (w : ℕ) (hzw : z ≤ w) :
    ∑ k ∈ Finset.Ico z w, 1 / (k:ℝ) ^ 2 ≤ 2 / (z:ℝ) := by
  have hz2 : (2:ℝ) ≤ z := by exact_mod_cast hz
  have key : ∀ w : ℕ, z ≤ w →
      ∑ k ∈ Finset.Ico z w, 1 / (k:ℝ) ^ 2 ≤ 1 / ((z:ℝ) - 1) - 1 / ((w:ℝ) - 1) := by
    intro w hzw
    induction w, hzw using Nat.le_induction with
    | base => simp
    | succ w hzw ih =>
      have hw2 : (2:ℝ) ≤ w := hz2.trans (by exact_mod_cast hzw)
      have hstep : 1 / (w:ℝ) ^ 2 ≤ 1 / ((w:ℝ) - 1) - 1 / (w:ℝ) := by
        rw [div_sub_div _ _ (by linarith : (w:ℝ) - 1 ≠ 0) (by linarith : (w:ℝ) ≠ 0),
          div_le_div_iff₀ (by positivity) (mul_pos (by linarith) (by linarith))]
        nlinarith
      rw [Finset.sum_Ico_succ_top hzw]
      push_cast
      have : (w:ℝ) + 1 - 1 = w := by ring
      rw [this]
      linarith
  have h1 := key w hzw
  have hw1 : (0:ℝ) ≤ 1 / ((w:ℝ) - 1) := by
    have : (2:ℝ) ≤ w := hz2.trans (by exact_mod_cast hzw)
    exact div_nonneg zero_le_one (by linarith)
  have h2 : 1 / ((z:ℝ) - 1) ≤ 2 / (z:ℝ) := by
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    linarith
  linarith

/-- P0069 page 51 display 5.17, passage from sums over integers to integrals, with a cutoff.
A function that vanishes at the integers below `κ`, and is continuous and `K`-Lipschitz on
`[κ, ∞)`, has `∑_{a < n ≤ b} g(n)` within `K (b - a) + |g(κ)|` of the integral of `g` over
`[max a κ, max b κ]`. The cutoff is the jump of the Buchstab density at the level. -/
theorem sum_sub_integral_cutoff (g : ℝ → ℝ) {K M : ℝ} (κ : ℕ) (hK : 0 ≤ K)
    (hc : ContinuousOn g (Ici (κ:ℝ)))
    (hL : ∀ x : ℝ, (κ:ℝ) ≤ x → ∀ y : ℝ, (κ:ℝ) ≤ y → |g x - g y| ≤ K * |x - y|)
    (h0 : ∀ n : ℕ, n < κ → g n = 0) (hM : |g κ| ≤ M) {a b : ℕ} (hab : a ≤ b) :
    |(∑ n ∈ Finset.Ioc a b, g n) - ∫ t in ((max a κ : ℕ) : ℝ)..((max b κ : ℕ) : ℝ), g t| ≤
      K * ((b:ℝ) - a) + M := by
  have hM0 : 0 ≤ M := (abs_nonneg _).trans hM
  have hab' : (a:ℝ) ≤ b := by exact_mod_cast hab
  rcases le_or_gt κ a with h | h
  · rw [max_eq_left h, max_eq_left (h.trans hab)]
    have hκa : (κ:ℝ) ≤ a := by exact_mod_cast h
    have := sum_sub_integral_le_of_lipschitz g a b hab
      (hc.mono (fun t ht => hκa.trans ht.1))
      (fun x hx y hy => hL x (hκa.trans hx.1) y (hκa.trans hy.1))
    linarith
  · rcases le_or_gt κ b with h2 | h2
    · rw [max_eq_right h.le, max_eq_left h2]
      have hs := Finset.sum_Ioc_consecutive (fun n : ℕ => g n) h.le h2
      have h1 : ∑ n ∈ Finset.Ioc a κ, g n = g κ := by
        apply Finset.sum_eq_single_of_mem κ (Finset.mem_Ioc.2 ⟨h, le_rfl⟩)
        intro n hn hne
        exact h0 n (lt_of_le_of_ne (Finset.mem_Ioc.1 hn).2 hne)
      have h3 := sum_sub_integral_le_of_lipschitz g κ b h2
        (hc.mono (fun t ht => ht.1))
        (fun x hx y hy => hL x hx.1 y hy.1)
      rw [← hs, h1]
      have haκ : (a:ℝ) ≤ κ := by exact_mod_cast h.le
      have hmono : K * ((b:ℝ) - κ) ≤ K * ((b:ℝ) - a) :=
        mul_le_mul_of_nonneg_left (by linarith) hK
      have habs := abs_add_le (g κ)
        ((∑ n ∈ Finset.Ioc κ b, g n) - ∫ t in (κ:ℝ)..(b:ℝ), g t)
      have e : g κ + ∑ n ∈ Finset.Ioc κ b, g n - ∫ t in (κ:ℝ)..(b:ℝ), g t =
          g κ + ((∑ n ∈ Finset.Ioc κ b, g n) - ∫ t in (κ:ℝ)..(b:ℝ), g t) := by ring
      rw [e]
      linarith
    · rw [max_eq_right h.le, max_eq_right h2.le, intervalIntegral.integral_same, sub_zero]
      have hz : ∑ n ∈ Finset.Ioc a b, g n = 0 :=
        Finset.sum_eq_zero (fun n hn => h0 n (lt_of_le_of_lt (Finset.mem_Ioc.1 hn).2 h2))
      rw [hz, abs_zero]
      exact add_nonneg (mul_nonneg hK (by linarith)) hM0

/-- P0069 page 51 display 5.17, bookkeeping for integer parts: moving the two end points of
the integral of a bounded function changes it by at most the bound times the moves. -/
theorem integral_endpoint_shift (f : ℝ → ℝ) {M : ℝ}
    (hf : ∀ x y : ℝ, IntervalIntegrable f volume x y) (hM : ∀ t : ℝ, |f t| ≤ M)
    (x y x' y' : ℝ) :
    |(∫ t in x..y, f t) - ∫ t in x'..y', f t| ≤ M * (|x - x'| + |y - y'|) := by
  rw [intervalIntegral.integral_interval_sub_interval_comm (hf x y) (hf x' y') (hf x x')]
  have h1 := intervalIntegral.norm_integral_le_of_norm_le_const (a := x) (b := x') (C := M)
    (f := f) (fun t _ => by rw [Real.norm_eq_abs]; exact hM t)
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const (a := y) (b := y') (C := M)
    (f := f) (fun t _ => by rw [Real.norm_eq_abs]; exact hM t)
  rw [Real.norm_eq_abs] at h1 h2
  have h3 := abs_sub (∫ t in x..x', f t) (∫ t in y..y', f t)
  rw [abs_sub_comm x x', abs_sub_comm y y']
  linarith

/-- P0069 page 51 display 5.17, Buchstab function input. The Buchstab density at level `k`
lies between `0` and `1 / log k`, with the zero extension below one. -/
theorem buchstab_density_bounds {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {k : ℝ} (hk : 1 < k) (t : ℝ) :
    0 ≤ ω (Real.log t / Real.log k) / Real.log k ∧
      ω (Real.log t / Real.log k) / Real.log k ≤ 1 / Real.log k := by
  have hl : 0 < Real.log k := Real.log_pos hk
  exact ⟨div_nonneg (Decomp514a.two_density_buchstab_nonneg hω hz _) hl.le,
    div_le_div_of_nonneg_right (extended_buchstab_le_one hω hz _) hl.le⟩

/-- P0069 page 51 display 5.17, Buchstab function input. The Buchstab density at level `k`
vanishes below the level: an integer below `k` with no prime factor below `k` does not occur
among the cofactors. -/
theorem buchstab_density_zero {ω : ℝ → ℝ} (hz : ZeroBelowOne ω)
    {k : ℝ} (hk : 1 < k) {t : ℝ} (ht0 : 0 ≤ t) (htk : t < k) :
    ω (Real.log t / Real.log k) / Real.log k = 0 := by
  have hl : 0 < Real.log k := Real.log_pos hk
  have harg : Real.log t / Real.log k < 1 := by
    rw [div_lt_one hl]
    rcases eq_or_lt_of_le ht0 with h | h
    · rw [← h, Real.log_zero]
      exact hl
    · exact Real.log_lt_log h htk
  rw [hz _ harg, zero_div]

/-- P0069 page 51 display 5.17, Buchstab function input. The Buchstab density at level `k`
is integrable on every interval. -/
theorem buchstab_density_intervalIntegrable {ω : ℝ → ℝ} (hω : IsBuchstab ω)
    (hz : ZeroBelowOne ω) {k : ℝ} (hk : 1 < k) (x y : ℝ) :
    IntervalIntegrable (fun t : ℝ => ω (Real.log t / Real.log k) / Real.log k) volume x y := by
  have hm : Measurable (fun t : ℝ => ω (Real.log t / Real.log k) / Real.log k) :=
    ((Decomp514a.two_density_buchstab_measurable hω hz).comp
      (Real.measurable_log.div_const _)).div_const _
  have hb : ∀ s : Set ℝ, ∀ᵐ t ∂(volume.restrict s),
      ‖ω (Real.log t / Real.log k) / Real.log k‖ ≤ 1 / Real.log k := by
    intro s
    refine Filter.Eventually.of_forall (fun t => ?_)
    have h := buchstab_density_bounds hω hz hk t
    rw [Real.norm_eq_abs, abs_of_nonneg h.1]
    exact h.2
  exact ⟨Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hm.aestronglyMeasurable (hb _),
    Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne hm.aestronglyMeasurable (hb _)⟩

/-- P0069 page 51 display 5.17, bookkeeping: `log 3 ≥ 1`, so that powers of `log k` can be
dropped from the error terms for levels `k ≥ 3`. -/
theorem one_le_log_three : (1:ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have := Real.exp_one_lt_d9
  linarith

/-- P0069 page 51 display 5.17, bookkeeping for integer parts: the integer quotient `a / k`
and the real quotient differ by less than one. -/
theorem natDiv_real_bounds (a : ℕ) {k : ℕ} (hk : 0 < k) :
    ((a / k : ℕ) : ℝ) ≤ (a:ℝ) / k ∧ (a:ℝ) / k < ((a / k : ℕ) : ℝ) + 1 := by
  have hk0 : (0:ℝ) < k := by exact_mod_cast hk
  constructor
  · exact Nat.cast_div_le
  · rw [div_lt_iff₀ hk0]
    have := Nat.lt_mul_div_succ a hk
    have h : (a:ℝ) < (k:ℝ) * (((a / k : ℕ) : ℝ) + 1) := by exact_mod_cast this
    linarith

/-- P0069 page 51 display 5.17, bookkeeping for integer parts: a real number in `[q, q + 1)`
is within one of `max q 1`. -/
theorem abs_sub_max_one_le {q : ℕ} {r : ℝ} (h1 : (q:ℝ) ≤ r) (h2 : r < (q:ℝ) + 1) :
    |r - ((max q 1 : ℕ) : ℝ)| ≤ 1 := by
  rcases Nat.eq_zero_or_pos q with h | h
  · subst h
    rw [show max 0 1 = 1 from rfl]
    push_cast at h1 h2 ⊢
    rw [abs_le]
    constructor <;> linarith
  · rw [max_eq_left h, abs_le]
    constructor <;> linarith

/-- P0069 page 51 display 5.17, Buchstab function input. The density of the products `s = k m`
with cofactor `m` free of prime factors below `k`, as a function of `s`, is continuous on
`[k^2, ∞)`. -/
theorem buchstab_product_continuousOn {ω : ℝ → ℝ} (hω : IsBuchstab ω) {k : ℝ} (hk : 1 < k) :
    ContinuousOn (fun s : ℝ => ω (Real.log (s / k) / Real.log k) / (k * Real.log k))
      (Ici (k ^ 2)) := by
  have hk0 : 0 < k := by linarith
  have hl : 0 < Real.log k := Real.log_pos hk
  have hsk : ∀ s ∈ Ici (k ^ 2), k ≤ s / k := by
    intro s hs
    rw [le_div_iff₀ hk0, ← sq]
    exact hs
  have h1 : ContinuousOn (fun s : ℝ => Real.log (s / k) / Real.log k) (Ici (k ^ 2)) :=
    (ContinuousOn.log (continuousOn_id.div_const _) (fun s hs => by
      have : 0 < s / k := lt_of_lt_of_le hk0 (hsk s hs)
      exact this.ne')).div_const _
  have h2 : ContinuousOn (fun s : ℝ => ω (Real.log (s / k) / Real.log k)) (Ici (k ^ 2)) := by
    apply hω.1.comp h1
    intro s hs
    change 1 ≤ Real.log (s / k) / Real.log k
    rw [le_div_iff₀ hl, one_mul]
    exact Real.log_le_log hk0 (hsk s hs)
  exact h2.div_const _

/-- P0069 page 51 display 5.17, Buchstab function input. The density of the products `s = k m`
is Lipschitz in `s` on `[k^2, ∞)` with constant `1 / (k^3 log^2 k)`. -/
theorem buchstab_product_lipschitz {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {k : ℝ} (hk : 1 < k) {x y : ℝ} (hx : k ^ 2 ≤ x) (hy : k ^ 2 ≤ y) :
    |ω (Real.log (x / k) / Real.log k) / (k * Real.log k) -
        ω (Real.log (y / k) / Real.log k) / (k * Real.log k)| ≤
      1 / (k ^ 3 * Real.log k ^ 2) * |x - y| := by
  have hk0 : 0 < k := by linarith
  have hl : 0 < Real.log k := Real.log_pos hk
  have hxk : k ≤ x / k := by rw [le_div_iff₀ hk0, ← sq]; exact hx
  have hyk : k ≤ y / k := by rw [le_div_iff₀ hk0, ← sq]; exact hy
  have h := buchstab_density_lipschitz hω hz hk hxk hyk
  have e : ∀ s : ℝ, ω (Real.log (s / k) / Real.log k) / (k * Real.log k) =
      ω (Real.log (s / k) / Real.log k) / Real.log k / k := fun s => by field_simp
  have e2 : x / k - y / k = (x - y) / k := by ring
  rw [e2, abs_div, abs_of_pos hk0] at h
  rw [e x, e y, ← sub_div, abs_div, abs_of_pos hk0, div_le_iff₀ hk0]
  have e3 : 1 / (k ^ 3 * Real.log k ^ 2) * |x - y| * k =
      1 / (k * Real.log k ^ 2) * (|x - y| / k) := by field_simp
  rw [e3]
  exact h

/-- P0069 page 51 display 5.17, Buchstab function input. The density of the products `s = k m`
lies between `0` and `1 / (k log k)` and vanishes for `0 ≤ s < k^2`. -/
theorem buchstab_product_bounds {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {k : ℝ} (hk : 1 < k) (s : ℝ) :
    0 ≤ ω (Real.log (s / k) / Real.log k) / (k * Real.log k) ∧
      ω (Real.log (s / k) / Real.log k) / (k * Real.log k) ≤ 1 / (k * Real.log k) ∧
      (0 ≤ s → s < k ^ 2 → ω (Real.log (s / k) / Real.log k) / (k * Real.log k) = 0) := by
  have hk0 : 0 < k := by linarith
  have hl : 0 < Real.log k := Real.log_pos hk
  have hpos : 0 < k * Real.log k := by positivity
  refine ⟨div_nonneg (Decomp514a.two_density_buchstab_nonneg hω hz _) hpos.le,
    div_le_div_of_nonneg_right (extended_buchstab_le_one hω hz _) hpos.le, fun hs0 hsk => ?_⟩
  have hlt : s / k < k := by rw [div_lt_iff₀ hk0, ← sq]; exact hsk
  have h := buchstab_density_zero hz hk (div_nonneg hs0 hk0.le) hlt
  have e : ω (Real.log (s / k) / Real.log k) / (k * Real.log k) =
      ω (Real.log (s / k) / Real.log k) / Real.log k / k := by field_simp
  rw [e, h, zero_div]

/-- P0069 page 51 display 5.17, the two ways to count the products `n = k m` in `(a, b]` with
cofactor `m` free of prime factors below `k`, at one level `k ≥ 3`: the sum over `n` of the
product density, and the sum over the cofactors `m` in `(a / k, b / k]`, cofactor above `1`,
of the Buchstab density at level `k`. They differ by at most `2 b / k^2 + 4`. -/
theorem buchstab_cofactor_pair_compare {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {k : ℕ} (hk : 3 ≤ k) {a b : ℕ} (hab : a ≤ b) :
    |(∑ n ∈ Finset.Ioc a b,
          ω (Real.log ((n:ℝ) / k) / Real.log k) / ((k:ℝ) * Real.log k)) -
        ∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
          ω (Real.log (m:ℝ) / Real.log k) / Real.log k| ≤
      2 * (b:ℝ) / (k:ℝ) ^ 2 + 4 := by
  have hk3 : (3:ℝ) ≤ k := by exact_mod_cast hk
  have hk1 : (1:ℝ) < k := by linarith
  have hk0 : (0:ℝ) < k := by linarith
  have hkpos : 0 < k := by omega
  have hl1 : 1 ≤ Real.log k := one_le_log_three.trans (Real.log_le_log (by norm_num) hk3)
  have hl : 0 < Real.log k := by linarith
  have hab' : (a:ℝ) ≤ b := by exact_mod_cast hab
  have ha0 : (0:ℝ) ≤ a := Nat.cast_nonneg a
  -- the sum over the products
  have hPb := fun s : ℝ => buchstab_product_bounds hω hz hk1 s
  have hP := sum_sub_integral_cutoff
    (fun s : ℝ => ω (Real.log (s / k) / Real.log k) / ((k:ℝ) * Real.log k))
    (K := 1 / ((k:ℝ) ^ 3 * Real.log k ^ 2)) (M := 1 / ((k:ℝ) * Real.log k)) (k ^ 2)
    (by positivity)
    (by rw [Nat.cast_pow]; exact buchstab_product_continuousOn hω hk1)
    (fun x hx y hy => buchstab_product_lipschitz hω hz hk1
      (by rw [Nat.cast_pow] at hx; exact hx) (by rw [Nat.cast_pow] at hy; exact hy))
    (fun n hn => (hPb n).2.2 (Nat.cast_nonneg n) (by exact_mod_cast hn))
    (by rw [abs_of_nonneg (hPb _).1]; exact (hPb _).2.1) hab
  -- the sum over the cofactors
  have hQb := fun t : ℝ => buchstab_density_bounds hω hz hk1 t
  have hMB : max (a / k) 1 ≤ max (b / k) 1 := max_le_max (Nat.div_le_div_right hab) le_rfl
  have hQ := sum_sub_integral_cutoff
    (fun t : ℝ => ω (Real.log t / Real.log k) / Real.log k)
    (K := 1 / ((k:ℝ) * Real.log k ^ 2)) (M := 1 / Real.log k) k
    (by positivity) (buchstab_density_continuousOn hω hk1)
    (fun x hx y hy => buchstab_density_lipschitz hω hz hk1 hx hy)
    (fun n hn => buchstab_density_zero hz hk1 (Nat.cast_nonneg n) (by exact_mod_cast hn))
    (by rw [abs_of_nonneg (hQb _).1]; exact (hQb _).2) hMB
  have hIoc : ∀ q qb : ℕ, Finset.Ioc (max q 1) qb = Finset.Ioc (max q 1) (max qb 1) := by
    intro q qb
    ext m
    simp only [Finset.mem_Ioc]
    omega
  rw [hIoc]
  -- the two integrals
  have hcv := buchstab_cofactor_change ω hk1 ((max a (k ^ 2) : ℕ) : ℝ)
    ((max b (k ^ 2) : ℕ) : ℝ)
  have hshift := integral_endpoint_shift
    (fun t : ℝ => ω (Real.log t / Real.log k) / Real.log k)
    (fun x y => buchstab_density_intervalIntegrable hω hz hk1 x y)
    (fun t => by rw [abs_of_nonneg (hQb t).1]; exact (hQb t).2)
    (((max a (k ^ 2) : ℕ) : ℝ) / k) (((max b (k ^ 2) : ℕ) : ℝ) / k)
    ((max (max (a / k) 1) k : ℕ) : ℝ) ((max (max (b / k) 1) k : ℕ) : ℝ)
  have hend : ∀ c : ℕ, |((max c (k ^ 2) : ℕ) : ℝ) / k - ((max (max (c / k) 1) k : ℕ) : ℝ)| ≤ 1 := by
    intro c
    have e1 : ((max c (k ^ 2) : ℕ) : ℝ) / k = max ((c:ℝ) / k) k := by
      rw [Nat.cast_max, Nat.cast_pow, ← max_div_div_right hk0.le]
      congr 1
      field_simp
    have e2 : ((max (max (c / k) 1) k : ℕ) : ℝ) = max (((max (c / k) 1 : ℕ) : ℝ)) (k:ℝ) :=
      Nat.cast_max _ _
    rw [e1, e2]
    have hb := natDiv_real_bounds c hkpos
    exact (abs_max_sub_max_le_abs _ _ _).trans (abs_sub_max_one_le hb.1 hb.2)
  have hd1 := hend a
  have hd2 := hend b
  have hBM : ((max (b / k) 1 : ℕ) : ℝ) - ((max (a / k) 1 : ℕ) : ℝ) ≤ (b:ℝ) / k := by
    have hnat : ∀ q qb : ℕ, max qb 1 ≤ max q 1 + qb := by
      intro q qb
      omega
    have h := hnat (a / k) (b / k)
    have h' : ((max (b / k) 1 : ℕ) : ℝ) ≤ ((max (a / k) 1 : ℕ) : ℝ) + ((b / k : ℕ) : ℝ) := by
      exact_mod_cast h
    have := (natDiv_real_bounds b hkpos).1
    linarith
  have hBM0 : (0:ℝ) ≤ ((max (b / k) 1 : ℕ) : ℝ) - ((max (a / k) 1 : ℕ) : ℝ) := by
    have : ((max (a / k) 1 : ℕ) : ℝ) ≤ ((max (b / k) 1 : ℕ) : ℝ) := by exact_mod_cast hMB
    linarith
  -- sizes of the constants
  have hl2 : 1 ≤ Real.log k ^ 2 := one_le_pow₀ hl1
  have hk23 : (k:ℝ) ^ 2 ≤ (k:ℝ) ^ 3 := pow_le_pow_right₀ hk1.le (by norm_num)
  have hKP : 1 / ((k:ℝ) ^ 3 * Real.log k ^ 2) ≤ 1 / (k:ℝ) ^ 2 := by
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith [pow_pos hk0 3]
  have hMP : 1 / ((k:ℝ) * Real.log k) ≤ 1 := by
    rw [div_le_one (by positivity)]
    nlinarith
  have hKQ : 1 / ((k:ℝ) * Real.log k ^ 2) ≤ 1 / (k:ℝ) := by
    apply one_div_le_one_div_of_le hk0
    nlinarith
  have hMQ : 1 / Real.log k ≤ 1 := by
    rw [div_le_one hl]
    exact hl1
  have hMQ0 : 0 ≤ 1 / Real.log k := by positivity
  have c1 : 1 / ((k:ℝ) ^ 3 * Real.log k ^ 2) * ((b:ℝ) - a) ≤ (b:ℝ) / (k:ℝ) ^ 2 := by
    have h1 := mul_le_mul hKP (by linarith : (b:ℝ) - a ≤ b) (by linarith) (by positivity)
    have e : 1 / (k:ℝ) ^ 2 * (b:ℝ) = (b:ℝ) / (k:ℝ) ^ 2 := by ring
    linarith
  have c2 : 1 / ((k:ℝ) * Real.log k ^ 2) *
      (((max (b / k) 1 : ℕ) : ℝ) - ((max (a / k) 1 : ℕ) : ℝ)) ≤ (b:ℝ) / (k:ℝ) ^ 2 := by
    have h1 := mul_le_mul hKQ hBM hBM0 (by positivity)
    have e : 1 / (k:ℝ) * ((b:ℝ) / k) = (b:ℝ) / (k:ℝ) ^ 2 := by
      field_simp
    linarith
  have c3 : 1 / Real.log k *
      (|((max a (k ^ 2) : ℕ) : ℝ) / k - ((max (max (a / k) 1) k : ℕ) : ℝ)| +
        |((max b (k ^ 2) : ℕ) : ℝ) / k - ((max (max (b / k) 1) k : ℕ) : ℝ)|) ≤ 2 := by
    have h1 := mul_le_mul hMQ (add_le_add hd1 hd2) (by positivity) zero_le_one
    linarith
  rw [hcv] at hshift
  have hP' := abs_le.mp hP
  have hQ' := abs_le.mp hQ
  have hS' := abs_le.mp (hshift.trans c3)
  have e2 : (2:ℝ) * b / (k:ℝ) ^ 2 = (b:ℝ) / (k:ℝ) ^ 2 + (b:ℝ) / (k:ℝ) ^ 2 := by ring
  rw [abs_le, e2]
  constructor <;> linarith [hP'.1, hP'.2, hQ'.1, hQ'.2, hS'.1, hS'.2]

/-- P0069 page 51 display 5.17: at a level `k` with `k^2 > b` no product `k m` with cofactor
`m ≥ k` lies in `(a, b]`, and both counts of `buchstab_cofactor_pair_compare` vanish. -/
theorem buchstab_cofactor_pair_zero {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {k : ℕ} (hk : 2 ≤ k) {a b : ℕ} (hb : b < k ^ 2) :
    (∑ n ∈ Finset.Ioc a b,
          ω (Real.log ((n:ℝ) / k) / Real.log k) / ((k:ℝ) * Real.log k)) = 0 ∧
      (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
          ω (Real.log (m:ℝ) / Real.log k) / Real.log k) = 0 := by
  have hk1 : (1:ℝ) < k := by exact_mod_cast (by omega : 1 < k)
  constructor
  · apply Finset.sum_eq_zero
    intro n hn
    have hnb : n < k ^ 2 := lt_of_le_of_lt (Finset.mem_Ioc.1 hn).2 hb
    exact (buchstab_product_bounds hω hz hk1 n).2.2 (Nat.cast_nonneg n)
      (by exact_mod_cast hnb)
  · apply Finset.sum_eq_zero
    intro m hm
    have hmk : m < k := by
      have h1 : b / k < k := Nat.div_lt_of_lt_mul (by rw [← sq]; exact hb)
      exact lt_of_le_of_lt (Finset.mem_Ioc.1 hm).2 h1
    exact buchstab_density_zero hz hk1 (Nat.cast_nonneg m) (by exact_mod_cast hmk)

/-- P0069 page 51 display 5.17, Buchstab function input. The integrand of the Buchstab
identity is continuous in the least prime factor variable `k` on `[z, √n]`. -/
theorem buchstab_integrand_continuousOn {ω : ℝ → ℝ} (hω : IsBuchstab ω) {z n : ℝ}
    (hz1 : 1 < z) :
    ContinuousOn (fun k : ℝ => ω (Real.log (n / k) / Real.log k) / (k * Real.log k ^ 2))
      (Icc z (Real.sqrt n)) := by
  have hz0 : 0 < z := by linarith
  have hk0 : ∀ k ∈ Icc z (Real.sqrt n), 0 < k := fun k hk => lt_of_lt_of_le hz0 hk.1
  have hlk : ∀ k ∈ Icc z (Real.sqrt n), 0 < Real.log k :=
    fun k hk => Real.log_pos (lt_of_lt_of_le hz1 hk.1)
  have hkn : ∀ k ∈ Icc z (Real.sqrt n), k ≤ n / k := by
    intro k hk
    rw [le_div_iff₀ (hk0 k hk), ← sq]
    exact (Real.le_sqrt' (hk0 k hk)).1 hk.2
  have hlog : ContinuousOn (fun k : ℝ => Real.log k) (Icc z (Real.sqrt n)) :=
    ContinuousOn.log continuousOn_id (fun k hk => (hk0 k hk).ne')
  have h1 : ContinuousOn (fun k : ℝ => Real.log (n / k) / Real.log k)
      (Icc z (Real.sqrt n)) :=
    (ContinuousOn.log (continuousOn_const.div continuousOn_id (fun k hk => (hk0 k hk).ne'))
      (fun k hk => (lt_of_lt_of_le (hk0 k hk) (hkn k hk)).ne')).div hlog
      (fun k hk => (hlk k hk).ne')
  have h2 : ContinuousOn (fun k : ℝ => ω (Real.log (n / k) / Real.log k))
      (Icc z (Real.sqrt n)) := by
    apply hω.1.comp h1
    intro k hk
    change 1 ≤ Real.log (n / k) / Real.log k
    rw [le_div_iff₀ (hlk k hk), one_mul]
    exact Real.log_le_log (hk0 k hk) (hkn k hk)
  exact h2.div (continuousOn_id.mul (hlog.pow 2))
    (fun k hk => (mul_pos (hk0 k hk) (pow_pos (hlk k hk) 2)).ne')

/-- P0069 page 51 display 5.17, the Buchstab identity for the density with the integral over
the least prime factor replaced by a sum over the integers `k` in `[z, b]`: for a level
`z ≥ 3` and an integer `1 ≤ n ≤ b`,
`ω(log n / log z) / log z = [z ≤ n] / log n + ∑_{z ≤ k ≤ b} ω(log (n/k) / log k) / (k log^2 k)`
up to `(2 log n + 8) / z`. The terms with `k^2 > n` vanish. -/
theorem buchstab_identity_discrete {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {z : ℕ} (hz3 : 3 ≤ z) {n b : ℕ} (hn1 : 1 ≤ n) (hnb : n ≤ b) :
    |ω (Real.log n / Real.log z) / Real.log z - (if z ≤ n then 1 / Real.log n else 0) -
        ∑ k ∈ Finset.Icc z b, ω (Real.log ((n:ℝ) / (k:ℝ)) / Real.log (k:ℝ)) / ((k:ℝ) * Real.log (k:ℝ) ^ 2)| ≤
      (2 * Real.log n + 8) / z := by
  have hzr3 : (3:ℝ) ≤ z := by exact_mod_cast hz3
  have hz1 : (1:ℝ) < z := by linarith
  have hz0 : (0:ℝ) < z := by linarith
  have hlz1 : 1 ≤ Real.log z := one_le_log_three.trans (Real.log_le_log (by norm_num) hzr3)
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn1
  have hlogn : 0 ≤ Real.log n := Real.log_nonneg (by exact_mod_cast hn1)
  have hbound0 : 0 ≤ (2 * Real.log n + 8) / z := by positivity
  have Fzero : ∀ k : ℕ, z ≤ k → n < k ^ 2 → ω (Real.log ((n:ℝ) / (k:ℝ)) / Real.log (k:ℝ)) / ((k:ℝ) * Real.log (k:ℝ) ^ 2) = 0 := by
    intro k hk hnk
    have hk1 : (1:ℝ) < k := lt_of_lt_of_le hz1 (by exact_mod_cast hk)
    have hk0 : (0:ℝ) < k := by linarith
    have harg : Real.log ((n:ℝ) / k) / Real.log k < 1 := by
      rw [div_lt_one (Real.log_pos hk1)]
      apply Real.log_lt_log (div_pos hn0 hk0)
      rw [div_lt_iff₀ hk0, ← sq]
      exact_mod_cast hnk
    rw [hz _ harg, zero_div]
  have Fbd : ∀ k : ℝ, (z:ℝ) ≤ k → 0 ≤ ω (Real.log ((n:ℝ) / k) / Real.log k) / (k * Real.log k ^ 2) ∧ ω (Real.log ((n:ℝ) / k) / Real.log k) / (k * Real.log k ^ 2) ≤ 1 / z := by
    intro k hk
    have hk3 : (3:ℝ) ≤ k := hzr3.trans hk
    have hk1 : (1:ℝ) < k := by linarith
    have hlk1 : 1 ≤ Real.log k := one_le_log_three.trans (Real.log_le_log (by norm_num) hk3)
    have hb := buchstab_integrand_bounds hω hz hk1 (n:ℝ)
    refine ⟨hb.1, hb.2.trans ?_⟩
    apply one_div_le_one_div_of_le hz0
    nlinarith [one_le_pow₀ hlk1 (n := 2)]
  by_cases hw : z ^ 2 ≤ n
  · have hzw : z ≤ Nat.sqrt n := Nat.le_sqrt'.2 hw
    have hwn : Nat.sqrt n ^ 2 ≤ n := Nat.sqrt_le' n
    have hwb : Nat.sqrt n ≤ b := (Nat.sqrt_le_self n).trans hnb
    have hwr : ((Nat.sqrt n : ℕ) : ℝ) ≤ Real.sqrt n := Real.nat_sqrt_le_real_sqrt
    have hwr2 : Real.sqrt n < ((Nat.sqrt n : ℕ) : ℝ) + 1 := Real.real_sqrt_lt_nat_sqrt_succ
    have hzwr : (z:ℝ) ≤ ((Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast hzw
    have hwn' : (((Nat.sqrt n : ℕ) : ℝ)) ^ 2 ≤ n := by exact_mod_cast hwn
    have hzn2 : (z:ℝ) ^ 2 ≤ n := by exact_mod_cast hw
    have hzn : z ≤ n := (Nat.le_self_pow two_ne_zero z).trans hw
    have hid := buchstab_multiplicative hω hz1 hzn2
    have hsum : ∑ k ∈ Finset.Icc z b, ω (Real.log ((n:ℝ) / (k:ℝ)) / Real.log (k:ℝ)) / ((k:ℝ) * Real.log (k:ℝ) ^ 2) =
        ω (Real.log ((n:ℝ) / (z:ℝ)) / Real.log (z:ℝ)) / ((z:ℝ) * Real.log (z:ℝ) ^ 2) + ∑ k ∈ Finset.Ioc z (Nat.sqrt n), ω (Real.log ((n:ℝ) / (k:ℝ)) / Real.log (k:ℝ)) / ((k:ℝ) * Real.log (k:ℝ) ^ 2) := by
      rw [← Finset.sum_Ioc_add_eq_sum_Icc (hzw.trans hwb),
        ← Finset.sum_Ioc_consecutive _ hzw hwb]
      have h0 : ∑ k ∈ Finset.Ioc (Nat.sqrt n) b, ω (Real.log ((n:ℝ) / (k:ℝ)) / Real.log (k:ℝ)) / ((k:ℝ) * Real.log (k:ℝ) ^ 2) = 0 :=
        Finset.sum_eq_zero (fun k hk =>
          Fzero k (hzw.trans (Finset.mem_Ioc.1 hk).1.le)
            (Nat.sqrt_lt'.1 (Finset.mem_Ioc.1 hk).1))
      rw [h0]
      ring
    have hcont := buchstab_integrand_continuousOn hω (z := (z:ℝ)) (n := (n:ℝ)) hz1
    have hKloc : ∀ k : ℕ, z ≤ k → k < Nat.sqrt n → ∀ t ∈ Icc (k:ℝ) ((k:ℝ) + 1),
        |(fun k : ℝ => ω (Real.log ((n:ℝ) / k) / Real.log k) / (k * Real.log k ^ 2)) ((k:ℝ) + 1) - (fun k : ℝ => ω (Real.log ((n:ℝ) / k) / Real.log k) / (k * Real.log k ^ 2)) t| ≤ (Real.log n + 3) * (1 / (k:ℝ) ^ 2) := by
      intro k hzk hkw t ht
      have hk3 : (3:ℝ) ≤ k := hzr3.trans (by exact_mod_cast hzk)
      have hk1 : (1:ℝ) < k := by linarith
      have hk0 : (0:ℝ) < k := by linarith
      have hlk1 : 1 ≤ Real.log k := one_le_log_three.trans (Real.log_le_log (by norm_num) hk3)
      have hk1w : (k:ℝ) + 1 ≤ ((Nat.sqrt n : ℕ) : ℝ) := by exact_mod_cast hkw
      have h1 : ((k:ℝ) + 1) ^ 2 ≤ n := (pow_le_pow_left₀ (by linarith) hk1w 2).trans hwn'
      have h2 : t ^ 2 ≤ n :=
        (pow_le_pow_left₀ (by linarith [ht.1]) (ht.2.trans hk1w) 2).trans hwn'
      have hL := buchstab_integrand_lipschitz hω hz hk1 (k := (k:ℝ) + 1) (k' := t)
        (n := (n:ℝ)) (by linarith) ht.1 h1 h2
      have habs : |(k:ℝ) + 1 - t| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith [ht.1, ht.2]
      have hl2 : 1 ≤ Real.log k ^ 2 := one_le_pow₀ hlk1
      have a1 : Real.log n / Real.log k ^ 2 ≤ Real.log n := div_le_self hlogn hl2
      have a2 : 2 / Real.log k ≤ 2 := div_le_self (by norm_num) hlk1
      have hk2 : 0 < (k:ℝ) ^ 2 := by positivity
      have hc : (Real.log n / Real.log k ^ 2 + 1 + 2 / Real.log k) /
          ((k:ℝ) ^ 2 * Real.log k ^ 2) ≤ (Real.log n + 3) * (1 / (k:ℝ) ^ 2) := by
        calc _ ≤ (Real.log n + 3) / ((k:ℝ) ^ 2 * Real.log k ^ 2) :=
              div_le_div_of_nonneg_right (by linarith) (by positivity)
          _ ≤ (Real.log n + 3) / (k:ℝ) ^ 2 :=
              div_le_div_of_nonneg_left (by linarith) hk2 (by nlinarith)
          _ = _ := by ring
      have hc0 : 0 ≤ (Real.log n / Real.log k ^ 2 + 1 + 2 / Real.log k) /
          ((k:ℝ) ^ 2 * Real.log k ^ 2) := by positivity
      calc _ ≤ (Real.log n / Real.log k ^ 2 + 1 + 2 / Real.log k) /
            ((k:ℝ) ^ 2 * Real.log k ^ 2) * |(k:ℝ) + 1 - t| := hL
        _ ≤ (Real.log n / Real.log k ^ 2 + 1 + 2 / Real.log k) /
            ((k:ℝ) ^ 2 * Real.log k ^ 2) * 1 := mul_le_mul_of_nonneg_left habs hc0
        _ ≤ _ := by rw [mul_one]; exact hc
    have hloc := sum_sub_integral_le_of_local (fun k : ℝ => ω (Real.log ((n:ℝ) / k) / Real.log k) / (k * Real.log k ^ 2))
      (fun k : ℕ => (Real.log n + 3) * (1 / (k:ℝ) ^ 2)) z (Nat.sqrt n) hzw
      (hcont.mono (Icc_subset_Icc_right hwr)) hKloc
    have hKsum : ∑ k ∈ Finset.Ico z (Nat.sqrt n), (Real.log n + 3) * (1 / (k:ℝ) ^ 2) ≤
        (Real.log n + 3) * (2 / (z:ℝ)) := by
      rw [← Finset.mul_sum]
      exact mul_le_mul_of_nonneg_left (inv_sq_sum_le (by omega) _ hzw) (by linarith)
    have hi1 : IntervalIntegrable (fun k : ℝ => ω (Real.log ((n:ℝ) / k) / Real.log k) / (k * Real.log k ^ 2)) volume (z:ℝ) ((Nat.sqrt n : ℕ) : ℝ) :=
      ContinuousOn.intervalIntegrable_of_Icc hzwr (hcont.mono (Icc_subset_Icc_right hwr))
    have hi2 : IntervalIntegrable (fun k : ℝ => ω (Real.log ((n:ℝ) / k) / Real.log k) / (k * Real.log k ^ 2)) volume ((Nat.sqrt n : ℕ) : ℝ) (Real.sqrt n) :=
      ContinuousOn.intervalIntegrable_of_Icc hwr (hcont.mono (Icc_subset_Icc_left hzwr))
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hi1 hi2
    have htail := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := ((Nat.sqrt n : ℕ) : ℝ)) (b := Real.sqrt n) (C := 1 / (z:ℝ)) (f := (fun k : ℝ => ω (Real.log ((n:ℝ) / k) / Real.log k) / (k * Real.log k ^ 2))) (by
        intro k hk
        rw [uIoc_of_le hwr] at hk
        have hb := Fbd k (hzwr.trans hk.1.le)
        rw [Real.norm_eq_abs, abs_of_nonneg hb.1]
        exact hb.2)
    rw [Real.norm_eq_abs] at htail
    have htail2 : 1 / (z:ℝ) * |Real.sqrt n - ((Nat.sqrt n : ℕ) : ℝ)| ≤ 1 / (z:ℝ) := by
      have : |Real.sqrt n - ((Nat.sqrt n : ℕ) : ℝ)| ≤ 1 := by
        rw [abs_le]
        constructor <;> linarith
      have h := mul_le_mul_of_nonneg_left this (by positivity : (0:ℝ) ≤ 1 / (z:ℝ))
      linarith
    have hFz := Fbd (z:ℝ) le_rfl
    have hloc' := abs_le.mp hloc
    have htail' := abs_le.mp (htail.trans htail2)
    have e : (2 * Real.log n + 8) / (z:ℝ) =
        (Real.log n + 3) * (2 / (z:ℝ)) + 1 / (z:ℝ) + 1 / (z:ℝ) := by
      field_simp
      ring
    rw [ite_eq_left hzn, hsum, hid, ← hsplit, e, abs_le]
    constructor <;> linarith [hloc'.1, hloc'.2, htail'.1, htail'.2, hFz.1, hFz.2]
  · have hlt : n < z ^ 2 := lt_of_not_ge hw
    have h0 : ∑ k ∈ Finset.Icc z b, ω (Real.log ((n:ℝ) / (k:ℝ)) / Real.log (k:ℝ)) / ((k:ℝ) * Real.log (k:ℝ) ^ 2) = 0 :=
      Finset.sum_eq_zero (fun k hk => Fzero k (Finset.mem_Icc.1 hk).1
        (lt_of_lt_of_le hlt (Nat.pow_le_pow_left (Finset.mem_Icc.1 hk).1 2)))
    by_cases hzn : z ≤ n
    · rw [ite_eq_left hzn, h0, buchstab_multiplicative_low hω hz1 (by exact_mod_cast hzn)
        (by exact_mod_cast hlt.le), sub_self, sub_zero, abs_zero]
      exact hbound0
    · rw [ite_eq_right hzn, h0, buchstab_density_zero hz hz1 (Nat.cast_nonneg n)
        (by exact_mod_cast (lt_of_not_ge hzn)), sub_zero, sub_zero, abs_zero]
      exact hbound0

/-- P0069 page 51 display 5.17, "a straightforward consequence of the prime number theorem",
the main term with the primes replaced by their density. For a level `z ≥ 3` and `1 ≤ a ≤ b`
the Buchstab density sum at level `z` over `(a, b]` equals the sum over the integers `k ≥ z`,
weighted by the prime density `1 / log k`, of the indicator of `a < k ≤ b` plus the Buchstab
density sum at level `k` over the cofactor range `(a / k, b / k]`, cofactor above `1`, up to
`b (2 log b + 12) / z + 4 √b`. This is the integral equation `u ω(u) = 1 + ∫_1^{u-1} ω` in
the multiplicative variables, summed over the interval. No prime occurs in it: what is left
of `leaf_buchstab_main_term` is the prime number theorem in the variable `k`. -/
theorem buchstab_main_term_integers {ω : ℝ → ℝ} (hω : IsBuchstab ω) (hz : ZeroBelowOne ω)
    {z : ℕ} (hz3 : 3 ≤ z) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    |(∑ n ∈ Finset.Ioc a b, ω (Real.log n / Real.log z) / Real.log z) -
        ∑ k ∈ (Finset.Icc 1 b).filter (fun k => z ≤ k),
          1 / Real.log k * ((if a < k then (1:ℝ) else 0) +
            ∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k),
              ω (Real.log m / Real.log k) / Real.log k)| ≤
      (b:ℝ) * (2 * Real.log b + 12) / z + 4 * Real.sqrt b := by
  have hzr3 : (3:ℝ) ≤ z := by exact_mod_cast hz3
  have hz0 : (0:ℝ) < z := by linarith
  have hb1 : (1:ℝ) ≤ b := by exact_mod_cast ha.trans hab
  have hab' : (a:ℝ) ≤ b := by exact_mod_cast hab
  have ha0 : (0:ℝ) ≤ a := Nat.cast_nonneg a
  have hlogb : 0 ≤ Real.log b := Real.log_nonneg hb1
  have hfilt : (Finset.Icc 1 b).filter (fun k => z ≤ k) = Finset.Icc z b := by
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc]
    omega
  rw [hfilt]
  have hT : (∑ k ∈ Finset.Icc z b, 1 / Real.log (k:ℝ) * ((if a < k then (1:ℝ) else 0) + (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k), ω (Real.log (m:ℝ) / Real.log k) / Real.log k))) =
      (∑ n ∈ Finset.Ioc a b, (if z ≤ n then 1 / Real.log (n:ℝ) else 0)) + (∑ k ∈ Finset.Icc z b, 1 / Real.log (k:ℝ) * (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k), ω (Real.log (m:ℝ) / Real.log k) / Real.log k)) := by
    have hadd : (∑ k ∈ Finset.Icc z b,
          1 / Real.log (k:ℝ) * ((if a < k then (1:ℝ) else 0) + (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k), ω (Real.log (m:ℝ) / Real.log k) / Real.log k))) =
        (∑ k ∈ Finset.Icc z b, 1 / Real.log (k:ℝ) * (if a < k then (1:ℝ) else 0)) + (∑ k ∈ Finset.Icc z b, 1 / Real.log (k:ℝ) * (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k), ω (Real.log (m:ℝ) / Real.log k) / Real.log k)) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl (fun k _ => mul_add _ _ _)
    rw [hadd]
    congr 1
    have e1 : ∀ k : ℕ, 1 / Real.log (k:ℝ) * (if a < k then (1:ℝ) else 0) =
        if a < k then 1 / Real.log (k:ℝ) else 0 := by
      intro k
      split_ifs <;> simp
    simp_rw [e1]
    rw [← Finset.sum_filter, ← Finset.sum_filter]
    congr 1
    ext k
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_Ioc]
    omega
  have hswap : (∑ n ∈ Finset.Ioc a b, ∑ k ∈ Finset.Icc z b, ω (Real.log ((n:ℝ) / (k:ℝ)) / Real.log (k:ℝ)) / ((k:ℝ) * Real.log (k:ℝ) ^ 2)) = (∑ k ∈ Finset.Icc z b, 1 / Real.log (k:ℝ) * (∑ n ∈ Finset.Ioc a b, ω (Real.log ((n:ℝ) / k) / Real.log k) / ((k:ℝ) * Real.log k))) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl (fun k _ => ?_)
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    rw [div_mul_div_comm, one_mul]
    congr 1
    ring
  have h4 : |(∑ n ∈ Finset.Ioc a b, ω (Real.log (n:ℝ) / Real.log (z:ℝ)) / Real.log (z:ℝ)) - (∑ n ∈ Finset.Ioc a b, (if z ≤ n then 1 / Real.log (n:ℝ) else 0)) - (∑ n ∈ Finset.Ioc a b, ∑ k ∈ Finset.Icc z b, ω (Real.log ((n:ℝ) / (k:ℝ)) / Real.log (k:ℝ)) / ((k:ℝ) * Real.log (k:ℝ) ^ 2))| ≤ ((b:ℝ) - a) * ((2 * Real.log b + 8) / z) := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hn : ∀ n ∈ Finset.Ioc a b,
        |ω (Real.log (n:ℝ) / Real.log (z:ℝ)) / Real.log (z:ℝ) - (if z ≤ n then 1 / Real.log (n:ℝ) else 0) - ∑ k ∈ Finset.Icc z b, ω (Real.log ((n:ℝ) / (k:ℝ)) / Real.log (k:ℝ)) / ((k:ℝ) * Real.log (k:ℝ) ^ 2)| ≤ (2 * Real.log b + 8) / z := by
      intro n hn
      have hn' := Finset.mem_Ioc.1 hn
      have h := buchstab_identity_discrete hω hz hz3 (n := n) (b := b) (by omega) hn'.2
      refine h.trans ?_
      apply div_le_div_of_nonneg_right _ hz0.le
      have hn0 : (0:ℝ) < n := by exact_mod_cast (by omega : 0 < n)
      have : Real.log n ≤ Real.log b := Real.log_le_log hn0 (by exact_mod_cast hn'.2)
      linarith
    refine (Finset.sum_le_sum hn).trans ?_
    rw [Finset.sum_const, Nat.card_Ioc, nsmul_eq_mul, Nat.cast_sub hab]
  have h5 : |(∑ k ∈ Finset.Icc z b, 1 / Real.log (k:ℝ) * (∑ n ∈ Finset.Ioc a b, ω (Real.log ((n:ℝ) / k) / Real.log k) / ((k:ℝ) * Real.log k))) - (∑ k ∈ Finset.Icc z b, 1 / Real.log (k:ℝ) * (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k), ω (Real.log (m:ℝ) / Real.log k) / Real.log k))| ≤ 4 * (b:ℝ) / z + 4 * Real.sqrt b := by
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hterm : ∀ k ∈ Finset.Icc z b,
        |1 / Real.log (k:ℝ) * (∑ n ∈ Finset.Ioc a b, ω (Real.log ((n:ℝ) / k) / Real.log k) / ((k:ℝ) * Real.log k)) - 1 / Real.log (k:ℝ) * (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k), ω (Real.log (m:ℝ) / Real.log k) / Real.log k)| ≤
          if k ^ 2 ≤ b then 2 * (b:ℝ) * (1 / (k:ℝ) ^ 2) + 4 else 0 := by
      intro k hk
      have hzk := (Finset.mem_Icc.1 hk).1
      have hk3 : 3 ≤ k := hz3.trans hzk
      have hkr3 : (3:ℝ) ≤ k := by exact_mod_cast hk3
      have hl1 : 1 ≤ Real.log k := one_le_log_three.trans (Real.log_le_log (by norm_num) hkr3)
      by_cases hkb : k ^ 2 ≤ b
      · rw [ite_eq_left hkb, ← mul_sub, abs_mul, abs_of_nonneg (by positivity)]
        have h := buchstab_cofactor_pair_compare hω hz hk3 hab
        have h1 : 1 / Real.log k ≤ 1 := (div_le_one (by linarith)).2 hl1
        calc _ ≤ 1 * |(∑ n ∈ Finset.Ioc a b, ω (Real.log ((n:ℝ) / k) / Real.log k) / ((k:ℝ) * Real.log k)) - (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k), ω (Real.log (m:ℝ) / Real.log k) / Real.log k)| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
          _ ≤ _ := by
            rw [one_mul]
            refine h.trans (le_of_eq ?_)
            ring
      · have h := buchstab_cofactor_pair_zero hω hz (by omega : 2 ≤ k) (a := a)
          (lt_of_not_ge hkb)
        rw [ite_eq_right hkb, h.1, h.2]
        simp
    refine (Finset.sum_le_sum hterm).trans ?_
    rw [← Finset.sum_filter, Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const,
      nsmul_eq_mul]
    have hsub1 : (Finset.Icc z b).filter (fun k => k ^ 2 ≤ b) ⊆
        Finset.Ico z (max z (b + 1)) := by
      intro k hk
      have hk' := Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1
      exact Finset.mem_Ico.2 ⟨hk'.1, by omega⟩
    have hs1 : ∑ k ∈ (Finset.Icc z b).filter (fun k => k ^ 2 ≤ b), 1 / (k:ℝ) ^ 2 ≤
        2 / (z:ℝ) :=
      (Finset.sum_le_sum_of_subset_of_nonneg hsub1 (fun k _ _ => by positivity)).trans
        (inv_sq_sum_le (by omega) _ (le_max_left _ _))
    have hsub2 : (Finset.Icc z b).filter (fun k => k ^ 2 ≤ b) ⊆
        Finset.Icc 1 (Nat.sqrt b) := by
      intro k hk
      have hk' := Finset.mem_Icc.1 (Finset.mem_filter.1 hk).1
      exact Finset.mem_Icc.2 ⟨by omega, Nat.le_sqrt'.2 (Finset.mem_filter.1 hk).2⟩
    have hcard : (((Finset.Icc z b).filter (fun k => k ^ 2 ≤ b)).card : ℝ) ≤ Real.sqrt b := by
      have h1 := Finset.card_le_card hsub2
      rw [Nat.card_Icc] at h1
      have h2 : (((Finset.Icc z b).filter (fun k => k ^ 2 ≤ b)).card : ℝ) ≤
          ((Nat.sqrt b : ℕ) : ℝ) := by exact_mod_cast (h1.trans (by omega))
      exact h2.trans Real.nat_sqrt_le_real_sqrt
    have hA : 2 * (b:ℝ) * ∑ k ∈ (Finset.Icc z b).filter (fun k => k ^ 2 ≤ b), 1 / (k:ℝ) ^ 2 ≤
        2 * (b:ℝ) * (2 / (z:ℝ)) := mul_le_mul_of_nonneg_left hs1 (by positivity)
    have e : 2 * (b:ℝ) * (2 / (z:ℝ)) = 4 * (b:ℝ) / z := by ring
    linarith
  rw [← hswap] at h5
  rw [hT]
  have e : (∑ n ∈ Finset.Ioc a b, ω (Real.log (n:ℝ) / Real.log (z:ℝ)) / Real.log (z:ℝ)) - ((∑ n ∈ Finset.Ioc a b, (if z ≤ n then 1 / Real.log (n:ℝ) else 0)) + (∑ k ∈ Finset.Icc z b, 1 / Real.log (k:ℝ) * (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k), ω (Real.log (m:ℝ) / Real.log k) / Real.log k))) = ((∑ n ∈ Finset.Ioc a b, ω (Real.log (n:ℝ) / Real.log (z:ℝ)) / Real.log (z:ℝ)) - (∑ n ∈ Finset.Ioc a b, (if z ≤ n then 1 / Real.log (n:ℝ) else 0)) - (∑ n ∈ Finset.Ioc a b, ∑ k ∈ Finset.Icc z b, ω (Real.log ((n:ℝ) / (k:ℝ)) / Real.log (k:ℝ)) / ((k:ℝ) * Real.log (k:ℝ) ^ 2))) + ((∑ n ∈ Finset.Ioc a b, ∑ k ∈ Finset.Icc z b, ω (Real.log ((n:ℝ) / (k:ℝ)) / Real.log (k:ℝ)) / ((k:ℝ) * Real.log (k:ℝ) ^ 2)) - (∑ k ∈ Finset.Icc z b, 1 / Real.log (k:ℝ) * (∑ m ∈ Finset.Ioc (max (a / k) 1) (b / k), ω (Real.log (m:ℝ) / Real.log k) / Real.log k))) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  have h6 : ((b:ℝ) - a) * ((2 * Real.log b + 8) / z) ≤ (b:ℝ) * ((2 * Real.log b + 8) / z) :=
    mul_le_mul_of_nonneg_right (by linarith) (by positivity)
  have e2 : (b:ℝ) * (2 * Real.log b + 12) / z =
      (b:ℝ) * ((2 * Real.log b + 8) / z) + 4 * (b:ℝ) / z := by ring
  linarith

end LeanLab.BHP1997.LowerShortC165

#print axioms LeanLab.BHP1997.LowerShortC165.inv_sq_sum_le
#print axioms LeanLab.BHP1997.LowerShortC165.sum_sub_integral_cutoff
#print axioms LeanLab.BHP1997.LowerShortC165.integral_endpoint_shift
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_density_bounds
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_density_zero
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_density_intervalIntegrable
#print axioms LeanLab.BHP1997.LowerShortC165.one_le_log_three
#print axioms LeanLab.BHP1997.LowerShortC165.natDiv_real_bounds
#print axioms LeanLab.BHP1997.LowerShortC165.abs_sub_max_one_le
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_product_continuousOn
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_product_lipschitz
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_product_bounds
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_cofactor_pair_compare
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_cofactor_pair_zero
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_integrand_continuousOn
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_identity_discrete
#print axioms LeanLab.BHP1997.LowerShortC165.buchstab_main_term_integers
