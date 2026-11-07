import LeanLab.RamareSaouter2003.Circle419
import LeanLab.RamareSaouter2003.Decomp378c

/-!
Rosser 1941 p. 224 and Backlund pp. 361 to 374.
The original circle_gamma_bound splits into zeta growth on the circle,
a gamma remainder bound and a real integral budget.
The original target and the actual zeta center are unchanged.
The three source leaves are OPEN. Their assembly is CONDITIONAL ON them.
AI wrote the Lean code. Binary Goldbach is OPEN.
-/

namespace LeanLab.RamareSaouter2003.Decomp419a
open Real Complex MeasureTheory Decomp359g Circle419

/-! ### Helpers for `envelope_budget`

The branch-one chord estimate and the Dirichlet-series machinery are the compiled development of an
earlier pass recorded in `results/RamareSaouter2003-Decomp419a-wip-0600Z.lean` (session 20261107T0549Z);
the branch 2-4 piecewise integrals, the numeric constants and the final assembly are this session's
(20261107T1428Z).  All of it is `private` and sits above its only user, `envelope_budget`.
-/
set_option maxHeartbeats 3000000




/-- The Dirichlet series dominates the zeta modulus on `Re > 1`. -/
private lemma zeta_norm_le_tsum (s : ℝ) (hs : 1 < s) :
    ‖riemannZeta (s : ℂ)‖ ≤ ∑' n : ℕ, (n : ℝ) ^ (-s) := by
  have hre : 1 < ((s : ℂ)).re := by simpa using hs
  have hterm : ∀ n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ (s : ℂ)‖ = (n : ℝ) ^ (-s) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have h0 : ((0 : ℂ)) ^ (s : ℂ) = 0 := by
        rw [Complex.zero_cpow]
        simp only [Complex.ofReal_ne_zero]
        linarith
      simp [h0, Real.zero_rpow (by linarith : (-s) ≠ 0)]
    · have hn' : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_pos hn, Complex.ofReal_re, one_div,
        Real.rpow_neg hn']
  have hsummable : Summable fun n : ℕ => ‖(1 : ℂ) / (n : ℂ) ^ (s : ℂ)‖ := by
    have h : Summable fun n : ℕ => (n : ℝ) ^ (-s) :=
      Real.summable_nat_rpow.2 (by linarith)
    exact h.congr (fun n => (hterm n).symm)
  calc ‖riemannZeta (s : ℂ)‖
      = ‖∑' n : ℕ, (1 : ℂ) / (n : ℂ) ^ (s : ℂ)‖ := by
        rw [zeta_eq_tsum_one_div_nat_cpow hre]
    _ ≤ ∑' n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ (s : ℂ)‖ := norm_tsum_le_tsum_norm hsummable
    _ = ∑' n : ℕ, (n : ℝ) ^ (-s) := tsum_congr hterm

/-- Rational upper bound for `n ^ (-(p/k))`, from the rational inequality `1 ≤ c ^ k * n ^ p`. -/
private lemma rpow_rat_le {n c : ℝ} (hn : 0 < n) {p k : ℕ} (hp : 0 < p) (hk : 0 < k) (hc : 0 < c)
    (h : 1 ≤ c ^ k * n ^ p) : n ^ (-((p : ℝ) / k)) ≤ c := by
  rw [← neg_div]
  have hn0 : (0 : ℝ) ≤ n := le_of_lt hn
  have hc0 : (0 : ℝ) ≤ c := le_of_lt hc
  have hk0 : (0 : ℝ) < (k : ℝ) := by exact_mod_cast hk
  have hexp : (-(p : ℝ) / k) = (-(p : ℝ)) * (1 / (k : ℝ)) := by field_simp
  rw [hexp, Real.rpow_mul hn0]
  have key : n ^ (-(p : ℝ)) ≤ c ^ (k : ℝ) := by
    rw [Real.rpow_neg hn0, Real.rpow_natCast, Real.rpow_natCast, ← one_div, div_le_iff₀ (pow_pos hn p)]
    simpa only [mul_comm] using h
  calc (n ^ (-(p : ℝ))) ^ (1 / (k : ℝ))
      ≤ (c ^ (k : ℝ)) ^ (1 / (k : ℝ)) := Real.rpow_le_rpow (Real.rpow_nonneg hn0 _) key (by positivity)
    _ = c := by
        rw [← Real.rpow_mul hc0, show (k : ℝ) * (1 / (k : ℝ)) = 1 by field_simp, Real.rpow_one]

/-- The tail of `∑ n ^ (-s)` past twenty terms, bounded by the integral from nineteen. -/
private lemma tsum_rpow_le_of (s : ℝ) (hs : 1 < s) {S : ℝ}
    (hS : ∑ n ∈ Finset.range 20, (n : ℝ) ^ (-s) ≤ S) :
    ∑' n : ℕ, (n : ℝ) ^ (-s) ≤ S + (19 : ℝ) ^ (1 - s) / (s - 1) := by
  have hs0 : (0 : ℝ) < s - 1 := by linarith
  have hsumm : Summable fun n : ℕ => (n : ℝ) ^ (-s) := Real.summable_nat_rpow.2 (by linarith)
  have hle : ∑ n ∈ Finset.range 20, (n : ℝ) ^ (-s) ≤ ∑' n : ℕ, (n : ℝ) ^ (-s) :=
    hsumm.sum_le_tsum (Finset.range 20) fun i _ => by positivity
  have hcast : (((20 : ℕ) : ℝ) - 1) = 19 := by norm_num
  have hanti : AntitoneOn (fun t : ℝ => t ^ (-s)) (Set.Ici (((20 : ℕ) : ℝ) - 1)) := by
    intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    have hx0 : (0 : ℝ) ≤ x := le_trans (by norm_num [hcast]) hx
    have hy0 : (0 : ℝ) ≤ y := le_trans hx0 hxy
    have hxy' : x ^ s ≤ y ^ s := Real.rpow_le_rpow hx0 hxy (le_of_lt (by linarith))
    show y ^ (-s) ≤ x ^ (-s)
    rw [Real.rpow_neg hx0, Real.rpow_neg hy0]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0:ℝ) < x ^ s) hxy'
  have hint : IntegrableOn (fun t : ℝ => t ^ (-s)) (Set.Ioi (((20 : ℕ) : ℝ) - 1)) := by
    rw [hcast]
    exact integrableOn_Ioi_rpow_of_lt (by linarith : -s < -1) (by norm_num)
  have hnn : ∀ t ∈ Set.Ioi (((20 : ℕ) : ℝ) - 1), 0 ≤ t ^ (-s) := by
    intro t ht
    simp only [Set.mem_Ioi] at ht
    exact Real.rpow_nonneg (le_of_lt (lt_of_le_of_lt (by norm_num [hcast]) ht)) _
  have hkey := AntitoneOn.abs_tsum_sub_sum_range_le_integral (f := fun t : ℝ => t ^ (-s))
    (N := 20) (by norm_num) hanti hint hnn
  have hval : (∫ x : ℝ in Set.Ioi (((20 : ℕ) : ℝ) - 1), x ^ (-s)) = (19 : ℝ) ^ (1 - s) / (s - 1) := by
    rw [hcast, integral_Ioi_rpow_of_lt (by linarith : -s < -1) (by norm_num : (0 : ℝ) < 19),
      show (-s + 1) = -(s - 1) by ring, Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 19)]
    field_simp
    rw [← Real.rpow_add (by norm_num : (0 : ℝ) < 19), show (s - 1) + (1 - s) = 0 by ring,
      Real.rpow_zero]
  rw [hval] at hkey
  have h2 := abs_le.mp hkey
  linarith [h2.1, h2.2, hle]

/-- Upper bound for `∑' n, n ^ (-((5 : ℝ) / 4))` from twenty terms and the integral test. -/
private lemma zsum_54 : ∑' n : ℕ, (n : ℝ) ^ (-((5 : ℝ) / 4)) ≤ 4.609 := by
  have t2 : (2 : ℝ) ^ (-((5 : ℝ) / 4)) ≤ 0.4205 := by
    simpa using rpow_rat_le (n := 2) (p := 5) (k := 4) (c := 0.4205) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t3 : (3 : ℝ) ^ (-((5 : ℝ) / 4)) ≤ 0.2533 := by
    simpa using rpow_rat_le (n := 3) (p := 5) (k := 4) (c := 0.2533) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t4 : (4 : ℝ) ^ (-((5 : ℝ) / 4)) ≤ 0.1768 := by
    simpa using rpow_rat_le (n := 4) (p := 5) (k := 4) (c := 0.1768) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t5 : (5 : ℝ) ^ (-((5 : ℝ) / 4)) ≤ 0.1338 := by
    simpa using rpow_rat_le (n := 5) (p := 5) (k := 4) (c := 0.1338) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t6 : (6 : ℝ) ^ (-((5 : ℝ) / 4)) ≤ 0.1065 := by
    simpa using rpow_rat_le (n := 6) (p := 5) (k := 4) (c := 0.1065) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t7 : (7 : ℝ) ^ (-((5 : ℝ) / 4)) ≤ 0.0879 := by
    simpa using rpow_rat_le (n := 7) (p := 5) (k := 4) (c := 0.0879) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t8 : (8 : ℝ) ^ (-((5 : ℝ) / 4)) ≤ 0.0744 := by
    simpa using rpow_rat_le (n := 8) (p := 5) (k := 4) (c := 0.0744) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t9 : (9 : ℝ) ^ (-((5 : ℝ) / 4)) ≤ 0.0642 := by
    simpa using rpow_rat_le (n := 9) (p := 5) (k := 4) (c := 0.0642) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t10 : (10 : ℝ) ^ (-((5 : ℝ) / 4)) ≤ 0.0563 := by
    simpa using rpow_rat_le (n := 10) (p := 5) (k := 4) (c := 0.0563) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t11 : (11 : ℝ) ^ (-((5 : ℝ) / 4)) ≤ 0.05 := by
    simpa using rpow_rat_le (n := 11) (p := 5) (k := 4) (c := 0.05) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t12 : (12 : ℝ) ^ (-((5 : ℝ) / 4)) ≤ 0.0448 := by
    simpa using rpow_rat_le (n := 12) (p := 5) (k := 4) (c := 0.0448) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t13 : (13 : ℝ) ^ (-((5 : ℝ) / 4)) ≤ 0.0406 := by
    simpa using rpow_rat_le (n := 13) (p := 5) (k := 4) (c := 0.0406) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t14 : (14 : ℝ) ^ (-((5 : ℝ) / 4)) ≤ 0.037 := by
    simpa using rpow_rat_le (n := 14) (p := 5) (k := 4) (c := 0.037) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t15 : (15 : ℝ) ^ (-((5 : ℝ) / 4)) ≤ 0.0339 := by
    simpa using rpow_rat_le (n := 15) (p := 5) (k := 4) (c := 0.0339) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t16 : (16 : ℝ) ^ (-((5 : ℝ) / 4)) ≤ 0.0313 := by
    simpa using rpow_rat_le (n := 16) (p := 5) (k := 4) (c := 0.0313) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t17 : (17 : ℝ) ^ (-((5 : ℝ) / 4)) ≤ 0.029 := by
    simpa using rpow_rat_le (n := 17) (p := 5) (k := 4) (c := 0.029) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t18 : (18 : ℝ) ^ (-((5 : ℝ) / 4)) ≤ 0.027 := by
    simpa using rpow_rat_le (n := 18) (p := 5) (k := 4) (c := 0.027) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t19 : (19 : ℝ) ^ (-((5 : ℝ) / 4)) ≤ 0.0253 := by
    simpa using rpow_rat_le (n := 19) (p := 5) (k := 4) (c := 0.0253) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hS : ∑ n ∈ Finset.range 20, (n : ℝ) ^ (-((5 : ℝ) / 4)) ≤ 2.693 := by
    have z0 : (0:ℝ) ^ (-((5 : ℝ) / 4)) = 0 := Real.zero_rpow (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, z0, Real.one_rpow, zero_add]
    linarith
  have hI := tsum_rpow_le_of (s := (5 : ℝ) / 4) (by norm_num) hS
  have hT : (19:ℝ) ^ (1 - (5 : ℝ) / 4) / ((5 : ℝ) / 4 - 1) ≤ 1.916 := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < (5 : ℝ) / 4 - 1)]
    have h19 : (19:ℝ) ^ (-((1 : ℝ) / 4)) ≤ 1.916 * ((5 : ℝ) / 4 - 1) := by
      simpa using rpow_rat_le (n := 19) (p := 1) (k := 4) (c := 1.916 * ((5 : ℝ) / 4 - 1)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rwa [show (1:ℝ) - (5 : ℝ) / 4 = -((1 : ℝ) / 4) by norm_num]
  linarith

/-- Upper bound for `∑' n, n ^ (-((3 : ℝ) / 2))` from twenty terms and the integral test. -/
private lemma zsum_32 : ∑' n : ℕ, (n : ℝ) ^ (-((3 : ℝ) / 2)) ≤ 2.620 := by
  have t2 : (2 : ℝ) ^ (-((3 : ℝ) / 2)) ≤ 0.3536 := by
    simpa using rpow_rat_le (n := 2) (p := 3) (k := 2) (c := 0.3536) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t3 : (3 : ℝ) ^ (-((3 : ℝ) / 2)) ≤ 0.1925 := by
    simpa using rpow_rat_le (n := 3) (p := 3) (k := 2) (c := 0.1925) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t4 : (4 : ℝ) ^ (-((3 : ℝ) / 2)) ≤ 0.125 := by
    simpa using rpow_rat_le (n := 4) (p := 3) (k := 2) (c := 0.125) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t5 : (5 : ℝ) ^ (-((3 : ℝ) / 2)) ≤ 0.0895 := by
    simpa using rpow_rat_le (n := 5) (p := 3) (k := 2) (c := 0.0895) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t6 : (6 : ℝ) ^ (-((3 : ℝ) / 2)) ≤ 0.0681 := by
    simpa using rpow_rat_le (n := 6) (p := 3) (k := 2) (c := 0.0681) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t7 : (7 : ℝ) ^ (-((3 : ℝ) / 2)) ≤ 0.054 := by
    simpa using rpow_rat_le (n := 7) (p := 3) (k := 2) (c := 0.054) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t8 : (8 : ℝ) ^ (-((3 : ℝ) / 2)) ≤ 0.0442 := by
    simpa using rpow_rat_le (n := 8) (p := 3) (k := 2) (c := 0.0442) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t9 : (9 : ℝ) ^ (-((3 : ℝ) / 2)) ≤ 0.0371 := by
    simpa using rpow_rat_le (n := 9) (p := 3) (k := 2) (c := 0.0371) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t10 : (10 : ℝ) ^ (-((3 : ℝ) / 2)) ≤ 0.0317 := by
    simpa using rpow_rat_le (n := 10) (p := 3) (k := 2) (c := 0.0317) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t11 : (11 : ℝ) ^ (-((3 : ℝ) / 2)) ≤ 0.0275 := by
    simpa using rpow_rat_le (n := 11) (p := 3) (k := 2) (c := 0.0275) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t12 : (12 : ℝ) ^ (-((3 : ℝ) / 2)) ≤ 0.0241 := by
    simpa using rpow_rat_le (n := 12) (p := 3) (k := 2) (c := 0.0241) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t13 : (13 : ℝ) ^ (-((3 : ℝ) / 2)) ≤ 0.0214 := by
    simpa using rpow_rat_le (n := 13) (p := 3) (k := 2) (c := 0.0214) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t14 : (14 : ℝ) ^ (-((3 : ℝ) / 2)) ≤ 0.0191 := by
    simpa using rpow_rat_le (n := 14) (p := 3) (k := 2) (c := 0.0191) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t15 : (15 : ℝ) ^ (-((3 : ℝ) / 2)) ≤ 0.0173 := by
    simpa using rpow_rat_le (n := 15) (p := 3) (k := 2) (c := 0.0173) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t16 : (16 : ℝ) ^ (-((3 : ℝ) / 2)) ≤ 0.0157 := by
    simpa using rpow_rat_le (n := 16) (p := 3) (k := 2) (c := 0.0157) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t17 : (17 : ℝ) ^ (-((3 : ℝ) / 2)) ≤ 0.0143 := by
    simpa using rpow_rat_le (n := 17) (p := 3) (k := 2) (c := 0.0143) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t18 : (18 : ℝ) ^ (-((3 : ℝ) / 2)) ≤ 0.0131 := by
    simpa using rpow_rat_le (n := 18) (p := 3) (k := 2) (c := 0.0131) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t19 : (19 : ℝ) ^ (-((3 : ℝ) / 2)) ≤ 0.0121 := by
    simpa using rpow_rat_le (n := 19) (p := 3) (k := 2) (c := 0.0121) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hS : ∑ n ∈ Finset.range 20, (n : ℝ) ^ (-((3 : ℝ) / 2)) ≤ 2.161 := by
    have z0 : (0:ℝ) ^ (-((3 : ℝ) / 2)) = 0 := Real.zero_rpow (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, z0, Real.one_rpow, zero_add]
    linarith
  have hI := tsum_rpow_le_of (s := (3 : ℝ) / 2) (by norm_num) hS
  have hT : (19:ℝ) ^ (1 - (3 : ℝ) / 2) / ((3 : ℝ) / 2 - 1) ≤ 0.459 := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < (3 : ℝ) / 2 - 1)]
    have h19 : (19:ℝ) ^ (-((1 : ℝ) / 2)) ≤ 0.459 * ((3 : ℝ) / 2 - 1) := by
      simpa using rpow_rat_le (n := 19) (p := 1) (k := 2) (c := 0.459 * ((3 : ℝ) / 2 - 1)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rwa [show (1:ℝ) - (3 : ℝ) / 2 = -((1 : ℝ) / 2) by norm_num]
  linarith

/-- Upper bound for `∑' n, n ^ (-((7 : ℝ) / 4))` from twenty terms and the integral test. -/
private lemma zsum_74 : ∑' n : ℕ, (n : ℝ) ^ (-((7 : ℝ) / 4)) ≤ 1.967 := by
  have t2 : (2 : ℝ) ^ (-((7 : ℝ) / 4)) ≤ 0.2974 := by
    simpa using rpow_rat_le (n := 2) (p := 7) (k := 4) (c := 0.2974) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t3 : (3 : ℝ) ^ (-((7 : ℝ) / 4)) ≤ 0.1463 := by
    simpa using rpow_rat_le (n := 3) (p := 7) (k := 4) (c := 0.1463) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t4 : (4 : ℝ) ^ (-((7 : ℝ) / 4)) ≤ 0.0884 := by
    simpa using rpow_rat_le (n := 4) (p := 7) (k := 4) (c := 0.0884) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t5 : (5 : ℝ) ^ (-((7 : ℝ) / 4)) ≤ 0.0599 := by
    simpa using rpow_rat_le (n := 5) (p := 7) (k := 4) (c := 0.0599) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t6 : (6 : ℝ) ^ (-((7 : ℝ) / 4)) ≤ 0.0435 := by
    simpa using rpow_rat_le (n := 6) (p := 7) (k := 4) (c := 0.0435) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t7 : (7 : ℝ) ^ (-((7 : ℝ) / 4)) ≤ 0.0332 := by
    simpa using rpow_rat_le (n := 7) (p := 7) (k := 4) (c := 0.0332) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t8 : (8 : ℝ) ^ (-((7 : ℝ) / 4)) ≤ 0.0263 := by
    simpa using rpow_rat_le (n := 8) (p := 7) (k := 4) (c := 0.0263) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t9 : (9 : ℝ) ^ (-((7 : ℝ) / 4)) ≤ 0.0214 := by
    simpa using rpow_rat_le (n := 9) (p := 7) (k := 4) (c := 0.0214) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t10 : (10 : ℝ) ^ (-((7 : ℝ) / 4)) ≤ 0.0178 := by
    simpa using rpow_rat_le (n := 10) (p := 7) (k := 4) (c := 0.0178) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t11 : (11 : ℝ) ^ (-((7 : ℝ) / 4)) ≤ 0.0151 := by
    simpa using rpow_rat_le (n := 11) (p := 7) (k := 4) (c := 0.0151) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t12 : (12 : ℝ) ^ (-((7 : ℝ) / 4)) ≤ 0.013 := by
    simpa using rpow_rat_le (n := 12) (p := 7) (k := 4) (c := 0.013) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t13 : (13 : ℝ) ^ (-((7 : ℝ) / 4)) ≤ 0.0113 := by
    simpa using rpow_rat_le (n := 13) (p := 7) (k := 4) (c := 0.0113) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t14 : (14 : ℝ) ^ (-((7 : ℝ) / 4)) ≤ 0.0099 := by
    simpa using rpow_rat_le (n := 14) (p := 7) (k := 4) (c := 0.0099) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t15 : (15 : ℝ) ^ (-((7 : ℝ) / 4)) ≤ 0.0088 := by
    simpa using rpow_rat_le (n := 15) (p := 7) (k := 4) (c := 0.0088) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t16 : (16 : ℝ) ^ (-((7 : ℝ) / 4)) ≤ 0.0079 := by
    simpa using rpow_rat_le (n := 16) (p := 7) (k := 4) (c := 0.0079) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t17 : (17 : ℝ) ^ (-((7 : ℝ) / 4)) ≤ 0.0071 := by
    simpa using rpow_rat_le (n := 17) (p := 7) (k := 4) (c := 0.0071) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t18 : (18 : ℝ) ^ (-((7 : ℝ) / 4)) ≤ 0.0064 := by
    simpa using rpow_rat_le (n := 18) (p := 7) (k := 4) (c := 0.0064) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t19 : (19 : ℝ) ^ (-((7 : ℝ) / 4)) ≤ 0.0058 := by
    simpa using rpow_rat_le (n := 19) (p := 7) (k := 4) (c := 0.0058) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hS : ∑ n ∈ Finset.range 20, (n : ℝ) ^ (-((7 : ℝ) / 4)) ≤ 1.82 := by
    have z0 : (0:ℝ) ^ (-((7 : ℝ) / 4)) = 0 := Real.zero_rpow (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, z0, Real.one_rpow, zero_add]
    linarith
  have hI := tsum_rpow_le_of (s := (7 : ℝ) / 4) (by norm_num) hS
  have hT : (19:ℝ) ^ (1 - (7 : ℝ) / 4) / ((7 : ℝ) / 4 - 1) ≤ 0.147 := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < (7 : ℝ) / 4 - 1)]
    have h19 : (19:ℝ) ^ (-((3 : ℝ) / 4)) ≤ 0.147 * ((7 : ℝ) / 4 - 1) := by
      simpa using rpow_rat_le (n := 19) (p := 3) (k := 4) (c := 0.147 * ((7 : ℝ) / 4 - 1)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rwa [show (1:ℝ) - (7 : ℝ) / 4 = -((3 : ℝ) / 4) by norm_num]
  linarith

/-- Upper bound for `∑' n, n ^ (-((2 : ℝ) / 1))` from twenty terms and the integral test. -/
private lemma zsum_2 : ∑' n : ℕ, (n : ℝ) ^ (-((2 : ℝ) / 1)) ≤ 1.648 := by
  have t2 : (2 : ℝ) ^ (-((2 : ℝ) / 1)) ≤ 0.25 := by
    simpa using rpow_rat_le (n := 2) (p := 2) (k := 1) (c := 0.25) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t3 : (3 : ℝ) ^ (-((2 : ℝ) / 1)) ≤ 0.1112 := by
    simpa using rpow_rat_le (n := 3) (p := 2) (k := 1) (c := 0.1112) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t4 : (4 : ℝ) ^ (-((2 : ℝ) / 1)) ≤ 0.0625 := by
    simpa using rpow_rat_le (n := 4) (p := 2) (k := 1) (c := 0.0625) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t5 : (5 : ℝ) ^ (-((2 : ℝ) / 1)) ≤ 0.04 := by
    simpa using rpow_rat_le (n := 5) (p := 2) (k := 1) (c := 0.04) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t6 : (6 : ℝ) ^ (-((2 : ℝ) / 1)) ≤ 0.0278 := by
    simpa using rpow_rat_le (n := 6) (p := 2) (k := 1) (c := 0.0278) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t7 : (7 : ℝ) ^ (-((2 : ℝ) / 1)) ≤ 0.0205 := by
    simpa using rpow_rat_le (n := 7) (p := 2) (k := 1) (c := 0.0205) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t8 : (8 : ℝ) ^ (-((2 : ℝ) / 1)) ≤ 0.0157 := by
    simpa using rpow_rat_le (n := 8) (p := 2) (k := 1) (c := 0.0157) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t9 : (9 : ℝ) ^ (-((2 : ℝ) / 1)) ≤ 0.0124 := by
    simpa using rpow_rat_le (n := 9) (p := 2) (k := 1) (c := 0.0124) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t10 : (10 : ℝ) ^ (-((2 : ℝ) / 1)) ≤ 0.01 := by
    simpa using rpow_rat_le (n := 10) (p := 2) (k := 1) (c := 0.01) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t11 : (11 : ℝ) ^ (-((2 : ℝ) / 1)) ≤ 0.0083 := by
    simpa using rpow_rat_le (n := 11) (p := 2) (k := 1) (c := 0.0083) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t12 : (12 : ℝ) ^ (-((2 : ℝ) / 1)) ≤ 0.007 := by
    simpa using rpow_rat_le (n := 12) (p := 2) (k := 1) (c := 0.007) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t13 : (13 : ℝ) ^ (-((2 : ℝ) / 1)) ≤ 0.006 := by
    simpa using rpow_rat_le (n := 13) (p := 2) (k := 1) (c := 0.006) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t14 : (14 : ℝ) ^ (-((2 : ℝ) / 1)) ≤ 0.0052 := by
    simpa using rpow_rat_le (n := 14) (p := 2) (k := 1) (c := 0.0052) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t15 : (15 : ℝ) ^ (-((2 : ℝ) / 1)) ≤ 0.0045 := by
    simpa using rpow_rat_le (n := 15) (p := 2) (k := 1) (c := 0.0045) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t16 : (16 : ℝ) ^ (-((2 : ℝ) / 1)) ≤ 0.004 := by
    simpa using rpow_rat_le (n := 16) (p := 2) (k := 1) (c := 0.004) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t17 : (17 : ℝ) ^ (-((2 : ℝ) / 1)) ≤ 0.0035 := by
    simpa using rpow_rat_le (n := 17) (p := 2) (k := 1) (c := 0.0035) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t18 : (18 : ℝ) ^ (-((2 : ℝ) / 1)) ≤ 0.0031 := by
    simpa using rpow_rat_le (n := 18) (p := 2) (k := 1) (c := 0.0031) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t19 : (19 : ℝ) ^ (-((2 : ℝ) / 1)) ≤ 0.0028 := by
    simpa using rpow_rat_le (n := 19) (p := 2) (k := 1) (c := 0.0028) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hS : ∑ n ∈ Finset.range 20, (n : ℝ) ^ (-((2 : ℝ) / 1)) ≤ 1.595 := by
    have z0 : (0:ℝ) ^ (-((2 : ℝ) / 1)) = 0 := Real.zero_rpow (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, z0, Real.one_rpow, zero_add]
    linarith
  have hI := tsum_rpow_le_of (s := (2 : ℝ) / 1) (by norm_num) hS
  have hT : (19:ℝ) ^ (1 - (2 : ℝ) / 1) / ((2 : ℝ) / 1 - 1) ≤ 0.053 := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < (2 : ℝ) / 1 - 1)]
    have h19 : (19:ℝ) ^ (-((1 : ℝ) / 1)) ≤ 0.053 * ((2 : ℝ) / 1 - 1) := by
      simpa using rpow_rat_le (n := 19) (p := 1) (k := 1) (c := 0.053 * ((2 : ℝ) / 1 - 1)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rwa [show (1:ℝ) - (2 : ℝ) / 1 = -((1 : ℝ) / 1) by norm_num]
  linarith

/-- Upper bound for `∑' n, n ^ (-((9 : ℝ) / 4))` from twenty terms and the integral test. -/
private lemma zsum_94 : ∑' n : ℕ, (n : ℝ) ^ (-((9 : ℝ) / 4)) ≤ 1.463 := by
  have t2 : (2 : ℝ) ^ (-((9 : ℝ) / 4)) ≤ 0.2103 := by
    simpa using rpow_rat_le (n := 2) (p := 9) (k := 4) (c := 0.2103) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t3 : (3 : ℝ) ^ (-((9 : ℝ) / 4)) ≤ 0.0845 := by
    simpa using rpow_rat_le (n := 3) (p := 9) (k := 4) (c := 0.0845) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t4 : (4 : ℝ) ^ (-((9 : ℝ) / 4)) ≤ 0.0442 := by
    simpa using rpow_rat_le (n := 4) (p := 9) (k := 4) (c := 0.0442) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t5 : (5 : ℝ) ^ (-((9 : ℝ) / 4)) ≤ 0.0268 := by
    simpa using rpow_rat_le (n := 5) (p := 9) (k := 4) (c := 0.0268) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t6 : (6 : ℝ) ^ (-((9 : ℝ) / 4)) ≤ 0.0178 := by
    simpa using rpow_rat_le (n := 6) (p := 9) (k := 4) (c := 0.0178) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t7 : (7 : ℝ) ^ (-((9 : ℝ) / 4)) ≤ 0.0126 := by
    simpa using rpow_rat_le (n := 7) (p := 9) (k := 4) (c := 0.0126) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t8 : (8 : ℝ) ^ (-((9 : ℝ) / 4)) ≤ 0.0093 := by
    simpa using rpow_rat_le (n := 8) (p := 9) (k := 4) (c := 0.0093) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t9 : (9 : ℝ) ^ (-((9 : ℝ) / 4)) ≤ 0.0072 := by
    simpa using rpow_rat_le (n := 9) (p := 9) (k := 4) (c := 0.0072) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t10 : (10 : ℝ) ^ (-((9 : ℝ) / 4)) ≤ 0.0057 := by
    simpa using rpow_rat_le (n := 10) (p := 9) (k := 4) (c := 0.0057) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t11 : (11 : ℝ) ^ (-((9 : ℝ) / 4)) ≤ 0.0046 := by
    simpa using rpow_rat_le (n := 11) (p := 9) (k := 4) (c := 0.0046) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t12 : (12 : ℝ) ^ (-((9 : ℝ) / 4)) ≤ 0.0038 := by
    simpa using rpow_rat_le (n := 12) (p := 9) (k := 4) (c := 0.0038) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t13 : (13 : ℝ) ^ (-((9 : ℝ) / 4)) ≤ 0.0032 := by
    simpa using rpow_rat_le (n := 13) (p := 9) (k := 4) (c := 0.0032) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t14 : (14 : ℝ) ^ (-((9 : ℝ) / 4)) ≤ 0.0027 := by
    simpa using rpow_rat_le (n := 14) (p := 9) (k := 4) (c := 0.0027) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t15 : (15 : ℝ) ^ (-((9 : ℝ) / 4)) ≤ 0.0023 := by
    simpa using rpow_rat_le (n := 15) (p := 9) (k := 4) (c := 0.0023) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t16 : (16 : ℝ) ^ (-((9 : ℝ) / 4)) ≤ 0.002 := by
    simpa using rpow_rat_le (n := 16) (p := 9) (k := 4) (c := 0.002) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t17 : (17 : ℝ) ^ (-((9 : ℝ) / 4)) ≤ 0.0018 := by
    simpa using rpow_rat_le (n := 17) (p := 9) (k := 4) (c := 0.0018) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t18 : (18 : ℝ) ^ (-((9 : ℝ) / 4)) ≤ 0.0015 := by
    simpa using rpow_rat_le (n := 18) (p := 9) (k := 4) (c := 0.0015) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t19 : (19 : ℝ) ^ (-((9 : ℝ) / 4)) ≤ 0.0014 := by
    simpa using rpow_rat_le (n := 19) (p := 9) (k := 4) (c := 0.0014) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hS : ∑ n ∈ Finset.range 20, (n : ℝ) ^ (-((9 : ℝ) / 4)) ≤ 1.442 := by
    have z0 : (0:ℝ) ^ (-((9 : ℝ) / 4)) = 0 := Real.zero_rpow (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, z0, Real.one_rpow, zero_add]
    linarith
  have hI := tsum_rpow_le_of (s := (9 : ℝ) / 4) (by norm_num) hS
  have hT : (19:ℝ) ^ (1 - (9 : ℝ) / 4) / ((9 : ℝ) / 4 - 1) ≤ 0.021 := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < (9 : ℝ) / 4 - 1)]
    have h19 : (19:ℝ) ^ (-((5 : ℝ) / 4)) ≤ 0.021 * ((9 : ℝ) / 4 - 1) := by
      simpa using rpow_rat_le (n := 19) (p := 5) (k := 4) (c := 0.021 * ((9 : ℝ) / 4 - 1)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rwa [show (1:ℝ) - (9 : ℝ) / 4 = -((5 : ℝ) / 4) by norm_num]
  linarith

/-- Upper bound for `∑' n, n ^ (-((5 : ℝ) / 2))` from twenty terms and the integral test. -/
private lemma zsum_52 : ∑' n : ℕ, (n : ℝ) ^ (-((5 : ℝ) / 2)) ≤ 1.344 := by
  have t2 : (2 : ℝ) ^ (-((5 : ℝ) / 2)) ≤ 0.1768 := by
    simpa using rpow_rat_le (n := 2) (p := 5) (k := 2) (c := 0.1768) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t3 : (3 : ℝ) ^ (-((5 : ℝ) / 2)) ≤ 0.0642 := by
    simpa using rpow_rat_le (n := 3) (p := 5) (k := 2) (c := 0.0642) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t4 : (4 : ℝ) ^ (-((5 : ℝ) / 2)) ≤ 0.0313 := by
    simpa using rpow_rat_le (n := 4) (p := 5) (k := 2) (c := 0.0313) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t5 : (5 : ℝ) ^ (-((5 : ℝ) / 2)) ≤ 0.0179 := by
    simpa using rpow_rat_le (n := 5) (p := 5) (k := 2) (c := 0.0179) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t6 : (6 : ℝ) ^ (-((5 : ℝ) / 2)) ≤ 0.0114 := by
    simpa using rpow_rat_le (n := 6) (p := 5) (k := 2) (c := 0.0114) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t7 : (7 : ℝ) ^ (-((5 : ℝ) / 2)) ≤ 0.0078 := by
    simpa using rpow_rat_le (n := 7) (p := 5) (k := 2) (c := 0.0078) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t8 : (8 : ℝ) ^ (-((5 : ℝ) / 2)) ≤ 0.0056 := by
    simpa using rpow_rat_le (n := 8) (p := 5) (k := 2) (c := 0.0056) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t9 : (9 : ℝ) ^ (-((5 : ℝ) / 2)) ≤ 0.0042 := by
    simpa using rpow_rat_le (n := 9) (p := 5) (k := 2) (c := 0.0042) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t10 : (10 : ℝ) ^ (-((5 : ℝ) / 2)) ≤ 0.0032 := by
    simpa using rpow_rat_le (n := 10) (p := 5) (k := 2) (c := 0.0032) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t11 : (11 : ℝ) ^ (-((5 : ℝ) / 2)) ≤ 0.0025 := by
    simpa using rpow_rat_le (n := 11) (p := 5) (k := 2) (c := 0.0025) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t12 : (12 : ℝ) ^ (-((5 : ℝ) / 2)) ≤ 0.0021 := by
    simpa using rpow_rat_le (n := 12) (p := 5) (k := 2) (c := 0.0021) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t13 : (13 : ℝ) ^ (-((5 : ℝ) / 2)) ≤ 0.0017 := by
    simpa using rpow_rat_le (n := 13) (p := 5) (k := 2) (c := 0.0017) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t14 : (14 : ℝ) ^ (-((5 : ℝ) / 2)) ≤ 0.0014 := by
    simpa using rpow_rat_le (n := 14) (p := 5) (k := 2) (c := 0.0014) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t15 : (15 : ℝ) ^ (-((5 : ℝ) / 2)) ≤ 0.0012 := by
    simpa using rpow_rat_le (n := 15) (p := 5) (k := 2) (c := 0.0012) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t16 : (16 : ℝ) ^ (-((5 : ℝ) / 2)) ≤ 0.001 := by
    simpa using rpow_rat_le (n := 16) (p := 5) (k := 2) (c := 0.001) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t17 : (17 : ℝ) ^ (-((5 : ℝ) / 2)) ≤ 0.0009 := by
    simpa using rpow_rat_le (n := 17) (p := 5) (k := 2) (c := 0.0009) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t18 : (18 : ℝ) ^ (-((5 : ℝ) / 2)) ≤ 0.0008 := by
    simpa using rpow_rat_le (n := 18) (p := 5) (k := 2) (c := 0.0008) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t19 : (19 : ℝ) ^ (-((5 : ℝ) / 2)) ≤ 0.0007 := by
    simpa using rpow_rat_le (n := 19) (p := 5) (k := 2) (c := 0.0007) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hS : ∑ n ∈ Finset.range 20, (n : ℝ) ^ (-((5 : ℝ) / 2)) ≤ 1.335 := by
    have z0 : (0:ℝ) ^ (-((5 : ℝ) / 2)) = 0 := Real.zero_rpow (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one, Nat.cast_ofNat, z0, Real.one_rpow, zero_add]
    linarith
  have hI := tsum_rpow_le_of (s := (5 : ℝ) / 2) (by norm_num) hS
  have hT : (19:ℝ) ^ (1 - (5 : ℝ) / 2) / ((5 : ℝ) / 2 - 1) ≤ 0.009 := by
    rw [div_le_iff₀ (by norm_num : (0:ℝ) < (5 : ℝ) / 2 - 1)]
    have h19 : (19:ℝ) ^ (-((3 : ℝ) / 2)) ≤ 0.009 * ((5 : ℝ) / 2 - 1) := by
      simpa using rpow_rat_le (n := 19) (p := 3) (k := 2) (c := 0.009 * ((5 : ℝ) / 2 - 1)) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    rwa [show (1:ℝ) - (5 : ℝ) / 2 = -((3 : ℝ) / 2) by norm_num]
  linarith



/-- `∑ n ^ (-t) ≤ ∑ n ^ (-s)` for `1 < s ≤ t`. -/
private lemma zsum_mono {s t : ℝ} (hs : 1 < s) (hst : s ≤ t) :
    ∑' n : ℕ, (n : ℝ) ^ (-t) ≤ ∑' n : ℕ, (n : ℝ) ^ (-s) := by
  have ht : 1 < t := lt_of_lt_of_le hs hst
  refine (Real.summable_nat_rpow.2 (show -t < -1 by linarith)).tsum_le_tsum (fun n => ?_)
    (Real.summable_nat_rpow.2 (show -s < -1 by linarith))
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn; simp [Real.zero_rpow (by linarith : -t ≠ 0), Real.zero_rpow (by linarith : -s ≠ 0)]
  · have hn0 : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have h1 : (1:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
    have hst' : (n:ℝ) ^ s ≤ (n:ℝ) ^ t := Real.rpow_le_rpow_of_exponent_le h1 hst
    rw [Real.rpow_neg hn0.le, Real.rpow_neg hn0.le]
    simpa only [one_div] using
      one_div_le_one_div_of_le (by positivity : (0:ℝ) < (n:ℝ) ^ s) hst'







/-- Log-convexity of `log ‖ζ‖` on `(1, ∞)` in the form of a chord between two points,
from Hölder's inequality, with explicit upper bounds `Ua`, `Ub` for the two series. -/
private lemma log_zeta_chord {a b θ : ℝ} (ha : 1 < a) (hab : a ≤ b) (hθ0 : 0 ≤ θ) (hθ1 : θ ≤ 1)
    {Ua Ub : ℝ} (hUa : 0 < Ua) (hUb : 0 < Ub)
    (hA : ∑' n : ℕ, (n : ℝ) ^ (-a) ≤ Ua) (hB : ∑' n : ℕ, (n : ℝ) ^ (-b) ≤ Ub) :
    Real.log ‖riemannZeta (((1 - θ) * a + θ * b : ℝ) : ℂ)‖ ≤
      (1 - θ) * Real.log Ua + θ * Real.log Ub := by
  have hb : 1 < b := lt_of_lt_of_le ha hab
  have hA0 : (0 : ℝ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-a) := tsum_nonneg fun n => by positivity
  have hB0 : (0 : ℝ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-b) := tsum_nonneg fun n => by positivity
  rcases eq_or_lt_of_le hθ0 with h0 | h0
  · -- θ = 0 : the left endpoint
    subst h0
    have h1 : ‖riemannZeta ((a : ℝ) : ℂ)‖ ≤ ∑' n : ℕ, (n : ℝ) ^ (-a) := zeta_norm_le_tsum a ha
    have h2 : (0 : ℝ) < ‖riemannZeta ((a : ℝ) : ℂ)‖ :=
      norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using ha))
    have h3 := Real.log_le_log h2 (h1.trans hA)
    simpa using h3
  rcases eq_or_lt_of_le hθ1 with h1' | h1'
  · -- θ = 1 : the right endpoint
    subst h1'
    have key : ‖riemannZeta ((b : ℝ) : ℂ)‖ ≤ ∑' n : ℕ, (n : ℝ) ^ (-b) := zeta_norm_le_tsum b hb
    have hpos : (0 : ℝ) < ‖riemannZeta ((b : ℝ) : ℂ)‖ :=
      norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using hb))
    have h3 := Real.log_le_log hpos (key.trans hB)
    simpa using h3
  -- 0 < θ < 1
  set σ : ℝ := (1 - θ) * a + θ * b with hσdef
  have hσ1 : 1 < σ := by
    have : σ = a + θ * (b - a) := by rw [hσdef]; ring
    rw [this]; nlinarith
  have hstep : ‖riemannZeta (σ : ℂ)‖ ≤ ∑' n : ℕ, (n : ℝ) ^ (-σ) := zeta_norm_le_tsum σ hσ1
  have hposσ : (0 : ℝ) < ‖riemannZeta (σ : ℂ)‖ :=
    norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by simpa using hσ1))
  set p : ℝ := 1 / (1 - θ) with hpdef
  set q : ℝ := 1 / θ with hqdef
  have hp0 : 0 < p := by rw [hpdef]; positivity
  have hq0 : 0 < q := by rw [hqdef]; positivity
  have hinv : p⁻¹ + q⁻¹ = 1 := by
    rw [hpdef, hqdef]
    field_simp
    ring
  have hpq : p.HolderConjugate q := ⟨by simpa using hinv, hp0, hq0⟩
  set f : ℕ → ℝ := fun n => (n : ℝ) ^ ((-a) * (1 - θ)) with hfdef
  set g : ℕ → ℝ := fun n => (n : ℝ) ^ ((-b) * θ) with hgdef
  have hf0 : ∀ n, 0 ≤ f n := fun n => by positivity
  have hg0 : ∀ n, 0 ≤ g n := fun n => by positivity
  have hfp : ∀ n : ℕ, f n ^ p = (n : ℝ) ^ (-a) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have e1 : ((-a) * (1 - θ)) ≠ 0 := by
        intro hh; rcases mul_eq_zero.mp hh with hh | hh
        · linarith
        · linarith
      have e2 : (-a) ≠ 0 := by linarith
      simp only [hfdef, Nat.cast_zero, Real.zero_rpow e1, Real.zero_rpow e2, Real.zero_rpow (ne_of_gt hp0)]
    · have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hnp : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [hfdef, ← Real.rpow_mul hn0, hpdef]
      have : (-a) * (1 - θ) * (1 / (1 - θ)) = -a := by field_simp
      rw [this]
  have hgq : ∀ n : ℕ, g n ^ q = (n : ℝ) ^ (-b) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have e1 : ((-b) * θ) ≠ 0 := by
        intro hh; rcases mul_eq_zero.mp hh with hh | hh
        · linarith
        · linarith
      have e2 : (-b) ≠ 0 := by linarith
      simp only [hgdef, Nat.cast_zero, Real.zero_rpow e1, Real.zero_rpow e2, Real.zero_rpow (ne_of_gt hq0)]
    · have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      have hnp : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [hgdef, ← Real.rpow_mul hn0, hqdef]
      have : (-b) * θ * (1 / θ) = -b := by field_simp
      rw [this]
  have hfg : ∀ n : ℕ, f n * g n = (n : ℝ) ^ (-σ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with hn | hn
    · subst hn
      have e1 : ((-a) * (1 - θ)) ≠ 0 := by
        intro hh; rcases mul_eq_zero.mp hh with hh | hh
        · linarith
        · linarith
      have e2 : ((-b) * θ) ≠ 0 := by
        intro hh; rcases mul_eq_zero.mp hh with hh | hh
        · linarith
        · linarith
      have e3 : (-σ) ≠ 0 := by
        intro hh; rw [neg_eq_zero] at hh; linarith
      simp only [hfdef, hgdef, Nat.cast_zero, Real.zero_rpow e1, Real.zero_rpow e2,
        Real.zero_rpow e3, mul_zero]
    · have hnp : (0 : ℝ) < (n : ℝ) := by exact_mod_cast hn
      rw [hfdef, hgdef, ← Real.rpow_add hnp]
      have : (-a) * (1 - θ) + (-b) * θ = -σ := by rw [hσdef]; ring
      rw [this]
  have hsum_a : Summable fun n : ℕ => f n ^ p := by
    have h : Summable fun n : ℕ => (n : ℝ) ^ (-a) := Real.summable_nat_rpow.2 (by linarith)
    exact h.congr (fun n => (hfp n).symm)
  have hsum_b : Summable fun n : ℕ => g n ^ q := by
    have h : Summable fun n : ℕ => (n : ℝ) ^ (-b) := Real.summable_nat_rpow.2 (by linarith)
    exact h.congr (fun n => (hgq n).symm)
  have hholder := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg hpq hf0 hg0 hsum_a hsum_b
  rw [tsum_congr hfg] at hholder
  have hpa : (∑' n : ℕ, f n ^ p) ^ (1 / p) ≤ Ua ^ (1 / p) := by
    have hE : (∑' n : ℕ, f n ^ p) = ∑' n : ℕ, (n : ℝ) ^ (-a) := tsum_congr hfp
    rw [hE]
    exact Real.rpow_le_rpow hA0 hA (by positivity)
  have hpb : (∑' n : ℕ, g n ^ q) ^ (1 / q) ≤ Ub ^ (1 / q) := by
    have hE : (∑' n : ℕ, g n ^ q) = ∑' n : ℕ, (n : ℝ) ^ (-b) := tsum_congr hgq
    rw [hE]
    exact Real.rpow_le_rpow hB0 hB (by positivity)
  have hmul := mul_le_mul hpa hpb (by positivity) (by positivity)
  have hp1 : Ua ^ (1 / p) = Ua ^ (1 - θ) := by rw [hpdef, one_div_one_div]
  have hq1 : Ub ^ (1 / q) = Ub ^ θ := by rw [hqdef, one_div_one_div]
  rw [hp1, hq1] at hmul
  have hfin : ∑' n : ℕ, (n : ℝ) ^ (-σ) ≤ Ua ^ (1 - θ) * Ub ^ θ := hholder.trans hmul
  have hlog : Real.log (∑' n : ℕ, (n : ℝ) ^ (-σ)) ≤
      (1 - θ) * Real.log Ua + θ * Real.log Ub := by
    have hsumpos : (0:ℝ) < ∑' n : ℕ, (n : ℝ) ^ (-σ) := by linarith [hstep, hposσ]
    refine (Real.log_le_log hsumpos hfin).trans (le_of_eq ?_)
    rw [Real.log_mul (by positivity) (by positivity), Real.log_rpow hUa, Real.log_rpow hUb]
  exact (Real.log_le_log hposσ hstep).trans hlog

/-- On `[0, π/2]` the envelope takes its first branch. -/
private lemma logEnvelope_branch1 {T φ : ℝ} (hφ : φ ∈ Set.Icc (0 : ℝ) (π / 2)) :
    logEnvelope T φ = Real.log (max 1 ‖riemannZeta (((5 : ℝ) / 4 + 1.32 * Real.cos φ : ℝ))‖) := by
  have hcos : 0 ≤ Real.cos φ :=
    Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [hφ.1, Real.pi_pos]) hφ.2
  have h : (5 : ℝ) / 4 ≤ 5 / 4 + 1.32 * Real.cos φ := by linarith
  unfold logEnvelope
  dsimp only
  rw [if_pos h, max_eq_right h]

/-- Upper bound for an `arcsin` increment. -/
private lemma arcsin_sub_le_sqrt {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) :
    Real.arcsin b - Real.arcsin a ≤ 2 * (Real.sqrt (1 - a) - Real.sqrt (1 - b)) / Real.sqrt (1 + a) := by
  have hpa : (0:ℝ) < Real.sqrt (1 + a) := Real.sqrt_pos.mpr (by linarith)
  have hmem : ∀ x ∈ Set.uIcc a b, x < 1 := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    linarith [hx.2]
  have hmem0 : ∀ x ∈ Set.uIcc a b, a ≤ x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    linarith [hx.1]
  have hme1 : ∀ x ∈ Set.uIcc a b, -1 < x := by
    intro x hx
    linarith [hmem0 x hx]
  have hInt1 : IntervalIntegrable (fun x : ℝ => 1 / √(1 - x ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact (Real.continuous_sqrt.comp (by fun_prop : Continuous fun x : ℝ => 1 - x ^ 2)).continuousOn
    · intro x hx
      exact ne_of_gt (Real.sqrt_pos.mpr (by nlinarith [hmem x hx, hme1 x hx]))
  have hInt2 : IntervalIntegrable (fun x : ℝ => 1 / (√(1 - x) * √(1 + a))) volume a b := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact ContinuousOn.mul (ContinuousOn.sqrt (by fun_prop)) continuousOn_const
    · intro x hx
      have h1 : (0:ℝ) < √(1 - x) := Real.sqrt_pos.mpr (by linarith [hmem x hx])
      positivity
  have hfund : (∫ x in a..b, 1 / √(1 - x ^ 2)) = Real.arcsin b - Real.arcsin a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) hInt1
    exact Real.hasDerivAt_arcsin (ne_of_gt (hme1 x hx)) (ne_of_lt (hmem x hx))
  rw [← hfund]
  have hmono : (∫ x in a..b, 1 / √(1 - x ^ 2)) ≤ ∫ x in a..b, 1 / (√(1 - x) * √(1 + a)) := by
    apply intervalIntegral.integral_mono_on hab hInt1 hInt2
    intro x hx
    have hx1 : (0:ℝ) < 1 - x := by linarith [hx.2]
    have e : (1:ℝ) - x ^ 2 = (1 - x) * (1 + x) := by ring
    rw [e, Real.sqrt_mul hx1.le]
    have hp : (0:ℝ) < √(1 - x) := Real.sqrt_pos.mpr hx1
    have hle : Real.sqrt (1 + a) ≤ Real.sqrt (1 + x) := Real.sqrt_le_sqrt (by linarith [hx.1])
    have hprod : √(1 - x) * √(1 + a) ≤ √(1 - x) * √(1 + x) :=
      mul_le_mul_of_nonneg_left hle hp.le
    exact one_div_le_one_div_of_le (by positivity) hprod
  refine hmono.trans (le_of_eq ?_)
  rw [show (fun x : ℝ => 1 / (√(1 - x) * √(1 + a))) = (fun x : ℝ => (1 / √(1 + a)) * (1 / √(1 - x))) by
    funext x; field_simp, intervalIntegral.integral_const_mul]
  have hder : ∀ x ∈ Set.uIcc a b, HasDerivAt (fun y : ℝ => -2 * Real.sqrt (1 - y)) (1 / √(1 - x)) x := by
    intro x hx
    have hx1 : (0:ℝ) < 1 - x := by linarith [hmem x hx]
    have hcomp : HasDerivAt (fun y : ℝ => Real.sqrt (1 - y)) (-(1 / (2 * Real.sqrt (1 - x)))) x := by
      have h1 : HasDerivAt (fun y : ℝ => 1 - y) (-1) x := by
        simpa using (hasDerivAt_id x).const_sub (1:ℝ)
      have h2 : HasDerivAt Real.sqrt (1 / (2 * Real.sqrt (1 - x))) (1 - x) :=
        Real.hasDerivAt_sqrt (ne_of_gt hx1)
      have h3 := h2.comp x h1
      convert h3 using 1
      · funext y; rfl
      · ring
    have h3 := hcomp.const_mul (-2)
    have hv : -2 * -(1 / (2 * Real.sqrt (1 - x))) = 1 / Real.sqrt (1 - x) := by
      field_simp
    rw [hv] at h3
    exact h3
  have hIntv : IntervalIntegrable (fun x : ℝ => 1 / √(1 - x)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.div continuousOn_const (ContinuousOn.sqrt (by fun_prop)) ?_
    · intro x hx
      exact ne_of_gt (Real.sqrt_pos.mpr (by linarith [hmem x hx]))
  have hval : (∫ x in a..b, 1 / √(1 - x)) = 2 * (Real.sqrt (1 - a) - Real.sqrt (1 - b)) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hder hIntv]
    ring
  rw [hval, div_eq_mul_inv]
  ring

/-- One-step bound for an `arcsin` increment: on `[a, b]` the derivative is at most `w`. -/
private lemma arcsin_step {a b w : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b < 1) (hw0 : 0 < w)
    (hw : 1 ≤ w ^ 2 * (1 - b ^ 2)) : Real.arcsin b - Real.arcsin a ≤ (b - a) * w := by
  have hmem : ∀ x ∈ Set.uIcc a b, x < 1 := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    linarith [hx.2]
  have hme1 : ∀ x ∈ Set.uIcc a b, -1 < x := by
    intro x hx
    rw [Set.uIcc_of_le hab] at hx
    linarith [hx.1]
  have hInt : IntervalIntegrable (fun x : ℝ => 1 / √(1 - x ^ 2)) volume a b := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact (Real.continuous_sqrt.comp (by fun_prop : Continuous fun x : ℝ => 1 - x ^ 2)).continuousOn
    · intro x hx
      exact ne_of_gt (Real.sqrt_pos.mpr (by nlinarith [hmem x hx, hme1 x hx]))
  have hfund : (∫ x in a..b, 1 / √(1 - x ^ 2)) = Real.arcsin b - Real.arcsin a := by
    refine intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x hx => ?_) hInt
    exact Real.hasDerivAt_arcsin (ne_of_gt (hme1 x hx)) (ne_of_lt (hmem x hx))
  rw [← hfund]
  have hmono : (∫ x in a..b, 1 / √(1 - x ^ 2)) ≤ ∫ x in a..b, w := by
    apply intervalIntegral.integral_mono_on hab hInt intervalIntegrable_const
    intro x hx
    have hx1 : x < 1 := by linarith [hx.2]
    have hposb : (0:ℝ) < √(1 - b ^ 2) := Real.sqrt_pos.mpr (by nlinarith [hb, ha, hab])
    have h1 : 1 / √(1 - x ^ 2) ≤ 1 / √(1 - b ^ 2) := by
      apply one_div_le_one_div_of_le hposb
      apply Real.sqrt_le_sqrt
      nlinarith [hx.1, hx.2, ha, hab]
    have h2 : 1 / √(1 - b ^ 2) ≤ w := by
      rw [div_le_iff₀ hposb]
      have hs : √(1 - b ^ 2) * √(1 - b ^ 2) = 1 - b ^ 2 := Real.mul_self_sqrt (by nlinarith [hb, ha, hab])
      nlinarith [hs, mul_nonneg hw0.le (Real.sqrt_nonneg (1 - b ^ 2))]
    linarith
  calc (∫ x in a..b, 1 / √(1 - x ^ 2)) ≤ ∫ x in a..b, w := hmono
    _ = (b - a) * w := by rw [intervalIntegral.integral_const]; ring

-- `arcsin` increments on the grid `25 m / 528`, `m = 0 .. 19`.

/-- `arcsin` increment on the grid step `[0/528, 25/528]`. -/
private lemma asub_0 : Real.arcsin ((25 : ℝ)/528) - Real.arcsin ((0 : ℝ)/528) ≤ 0.04793 := by
  have h := arcsin_sub_le_sqrt (a := (0 : ℝ)/528) (b := (25 : ℝ)/528)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : Real.sqrt (1 - (0 : ℝ)/528) ≤ (1.0000000 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB : (0.9760386 : ℝ) ≤ Real.sqrt (1 - (25 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (1.0000000 : ℝ) ≤ Real.sqrt (1 + (0 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 + (0 : ℝ)/528) := Real.sqrt_pos.mpr (by norm_num)
  have hkey : 2 * (Real.sqrt (1 - (0 : ℝ)/528) - Real.sqrt (1 - (25 : ℝ)/528)) /
      Real.sqrt (1 + (0 : ℝ)/528) ≤ (0.04793 : ℝ) := by
    rw [div_le_iff₀ hpos]
    have e1 : 2 * (Real.sqrt (1 - (0 : ℝ)/528) - Real.sqrt (1 - (25 : ℝ)/528)) ≤
        2 * ((1.0000000 : ℝ) - (0.9760386 : ℝ)) := by linarith
    have e2 : 2 * ((1.0000000 : ℝ) - (0.9760386 : ℝ)) ≤ (0.04793 : ℝ) * (1.0000000 : ℝ) := by norm_num
    have e3 : (0.04793 : ℝ) * (1.0000000 : ℝ) ≤
        (0.04793 : ℝ) * Real.sqrt (1 + (0 : ℝ)/528) := by nlinarith [hC]
    linarith
  linarith

/-- `arcsin` increment on the grid step `[25/528, 50/528]`. -/
private lemma asub_1 : Real.arcsin ((50 : ℝ)/528) - Real.arcsin ((25 : ℝ)/528) ≤ 0.04801 := by
  have h := arcsin_sub_le_sqrt (a := (25 : ℝ)/528) (b := (50 : ℝ)/528)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : Real.sqrt (1 - (25 : ℝ)/528) ≤ (0.9760387 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB : (0.9514741 : ℝ) ≤ Real.sqrt (1 - (50 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (1.0234004 : ℝ) ≤ Real.sqrt (1 + (25 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 + (25 : ℝ)/528) := Real.sqrt_pos.mpr (by norm_num)
  have hkey : 2 * (Real.sqrt (1 - (25 : ℝ)/528) - Real.sqrt (1 - (50 : ℝ)/528)) /
      Real.sqrt (1 + (25 : ℝ)/528) ≤ (0.04801 : ℝ) := by
    rw [div_le_iff₀ hpos]
    have e1 : 2 * (Real.sqrt (1 - (25 : ℝ)/528) - Real.sqrt (1 - (50 : ℝ)/528)) ≤
        2 * ((0.9760387 : ℝ) - (0.9514741 : ℝ)) := by linarith
    have e2 : 2 * ((0.9760387 : ℝ) - (0.9514741 : ℝ)) ≤ (0.04801 : ℝ) * (1.0234004 : ℝ) := by norm_num
    have e3 : (0.04801 : ℝ) * (1.0234004 : ℝ) ≤
        (0.04801 : ℝ) * Real.sqrt (1 + (25 : ℝ)/528) := by nlinarith [hC]
    linarith
  linarith

/-- `arcsin` increment on the grid step `[50/528, 75/528]`. -/
private lemma asub_2 : Real.arcsin ((75 : ℝ)/528) - Real.arcsin ((50 : ℝ)/528) ≤ 0.04821 := by
  have h := arcsin_sub_le_sqrt (a := (50 : ℝ)/528) (b := (75 : ℝ)/528)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : Real.sqrt (1 - (50 : ℝ)/528) ≤ (0.9514742 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB : (0.9262583 : ℝ) ≤ Real.sqrt (1 - (75 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (1.0462776 : ℝ) ≤ Real.sqrt (1 + (50 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 + (50 : ℝ)/528) := Real.sqrt_pos.mpr (by norm_num)
  have hkey : 2 * (Real.sqrt (1 - (50 : ℝ)/528) - Real.sqrt (1 - (75 : ℝ)/528)) /
      Real.sqrt (1 + (50 : ℝ)/528) ≤ (0.04821 : ℝ) := by
    rw [div_le_iff₀ hpos]
    have e1 : 2 * (Real.sqrt (1 - (50 : ℝ)/528) - Real.sqrt (1 - (75 : ℝ)/528)) ≤
        2 * ((0.9514742 : ℝ) - (0.9262583 : ℝ)) := by linarith
    have e2 : 2 * ((0.9514742 : ℝ) - (0.9262583 : ℝ)) ≤ (0.04821 : ℝ) * (1.0462776 : ℝ) := by norm_num
    have e3 : (0.04821 : ℝ) * (1.0462776 : ℝ) ≤
        (0.04821 : ℝ) * Real.sqrt (1 + (50 : ℝ)/528) := by nlinarith [hC]
    linarith
  linarith

/-- `arcsin` increment on the grid step `[75/528, 100/528]`. -/
private lemma asub_3 : Real.arcsin ((100 : ℝ)/528) - Real.arcsin ((75 : ℝ)/528) ≤ 0.04852 := by
  have h := arcsin_sub_le_sqrt (a := (75 : ℝ)/528) (b := (100 : ℝ)/528)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : Real.sqrt (1 - (75 : ℝ)/528) ≤ (0.9262584 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB : (0.9003366 : ℝ) ≤ Real.sqrt (1 - (100 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (1.0686652 : ℝ) ≤ Real.sqrt (1 + (75 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 + (75 : ℝ)/528) := Real.sqrt_pos.mpr (by norm_num)
  have hkey : 2 * (Real.sqrt (1 - (75 : ℝ)/528) - Real.sqrt (1 - (100 : ℝ)/528)) /
      Real.sqrt (1 + (75 : ℝ)/528) ≤ (0.04852 : ℝ) := by
    rw [div_le_iff₀ hpos]
    have e1 : 2 * (Real.sqrt (1 - (75 : ℝ)/528) - Real.sqrt (1 - (100 : ℝ)/528)) ≤
        2 * ((0.9262584 : ℝ) - (0.9003366 : ℝ)) := by linarith
    have e2 : 2 * ((0.9262584 : ℝ) - (0.9003366 : ℝ)) ≤ (0.04852 : ℝ) * (1.0686652 : ℝ) := by norm_num
    have e3 : (0.04852 : ℝ) * (1.0686652 : ℝ) ≤
        (0.04852 : ℝ) * Real.sqrt (1 + (75 : ℝ)/528) := by nlinarith [hC]
    linarith
  linarith

/-- `arcsin` increment on the grid step `[100/528, 125/528]`. -/
private lemma asub_4 : Real.arcsin ((125 : ℝ)/528) - Real.arcsin ((100 : ℝ)/528) ≤ 0.04895 := by
  have h := arcsin_sub_le_sqrt (a := (100 : ℝ)/528) (b := (125 : ℝ)/528)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : Real.sqrt (1 - (100 : ℝ)/528) ≤ (0.9003367 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB : (0.8736461 : ℝ) ≤ Real.sqrt (1 - (125 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (1.0905933 : ℝ) ≤ Real.sqrt (1 + (100 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 + (100 : ℝ)/528) := Real.sqrt_pos.mpr (by norm_num)
  have hkey : 2 * (Real.sqrt (1 - (100 : ℝ)/528) - Real.sqrt (1 - (125 : ℝ)/528)) /
      Real.sqrt (1 + (100 : ℝ)/528) ≤ (0.04895 : ℝ) := by
    rw [div_le_iff₀ hpos]
    have e1 : 2 * (Real.sqrt (1 - (100 : ℝ)/528) - Real.sqrt (1 - (125 : ℝ)/528)) ≤
        2 * ((0.9003367 : ℝ) - (0.8736461 : ℝ)) := by linarith
    have e2 : 2 * ((0.9003367 : ℝ) - (0.8736461 : ℝ)) ≤ (0.04895 : ℝ) * (1.0905933 : ℝ) := by norm_num
    have e3 : (0.04895 : ℝ) * (1.0905933 : ℝ) ≤
        (0.04895 : ℝ) * Real.sqrt (1 + (100 : ℝ)/528) := by nlinarith [hC]
    linarith
  linarith

/-- `arcsin` increment on the grid step `[125/528, 150/528]`. -/
private lemma asub_5 : Real.arcsin ((150 : ℝ)/528) - Real.arcsin ((125 : ℝ)/528) ≤ 0.04952 := by
  have h := arcsin_sub_le_sqrt (a := (125 : ℝ)/528) (b := (150 : ℝ)/528)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : Real.sqrt (1 - (125 : ℝ)/528) ≤ (0.8736462 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB : (0.8461141 : ℝ) ≤ Real.sqrt (1 - (150 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (1.1120892 : ℝ) ≤ Real.sqrt (1 + (125 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 + (125 : ℝ)/528) := Real.sqrt_pos.mpr (by norm_num)
  have hkey : 2 * (Real.sqrt (1 - (125 : ℝ)/528) - Real.sqrt (1 - (150 : ℝ)/528)) /
      Real.sqrt (1 + (125 : ℝ)/528) ≤ (0.04952 : ℝ) := by
    rw [div_le_iff₀ hpos]
    have e1 : 2 * (Real.sqrt (1 - (125 : ℝ)/528) - Real.sqrt (1 - (150 : ℝ)/528)) ≤
        2 * ((0.8736462 : ℝ) - (0.8461141 : ℝ)) := by linarith
    have e2 : 2 * ((0.8736462 : ℝ) - (0.8461141 : ℝ)) ≤ (0.04952 : ℝ) * (1.1120892 : ℝ) := by norm_num
    have e3 : (0.04952 : ℝ) * (1.1120892 : ℝ) ≤
        (0.04952 : ℝ) * Real.sqrt (1 + (125 : ℝ)/528) := by nlinarith [hC]
    linarith
  linarith

/-- `arcsin` increment on the grid step `[150/528, 175/528]`. -/
private lemma asub_6 : Real.arcsin ((175 : ℝ)/528) - Real.arcsin ((150 : ℝ)/528) ≤ 0.05023 := by
  have h := arcsin_sub_le_sqrt (a := (150 : ℝ)/528) (b := (175 : ℝ)/528)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : Real.sqrt (1 - (150 : ℝ)/528) ≤ (0.8461142 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB : (0.8176555 : ℝ) ≤ Real.sqrt (1 - (175 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (1.1331773 : ℝ) ≤ Real.sqrt (1 + (150 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 + (150 : ℝ)/528) := Real.sqrt_pos.mpr (by norm_num)
  have hkey : 2 * (Real.sqrt (1 - (150 : ℝ)/528) - Real.sqrt (1 - (175 : ℝ)/528)) /
      Real.sqrt (1 + (150 : ℝ)/528) ≤ (0.05023 : ℝ) := by
    rw [div_le_iff₀ hpos]
    have e1 : 2 * (Real.sqrt (1 - (150 : ℝ)/528) - Real.sqrt (1 - (175 : ℝ)/528)) ≤
        2 * ((0.8461142 : ℝ) - (0.8176555 : ℝ)) := by linarith
    have e2 : 2 * ((0.8461142 : ℝ) - (0.8176555 : ℝ)) ≤ (0.05023 : ℝ) * (1.1331773 : ℝ) := by norm_num
    have e3 : (0.05023 : ℝ) * (1.1331773 : ℝ) ≤
        (0.05023 : ℝ) * Real.sqrt (1 + (150 : ℝ)/528) := by nlinarith [hC]
    linarith
  linarith

/-- `arcsin` increment on the grid step `[175/528, 200/528]`. -/
private lemma asub_7 : Real.arcsin ((200 : ℝ)/528) - Real.arcsin ((175 : ℝ)/528) ≤ 0.05111 := by
  have h := arcsin_sub_le_sqrt (a := (175 : ℝ)/528) (b := (200 : ℝ)/528)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : Real.sqrt (1 - (175 : ℝ)/528) ≤ (0.8176556 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB : (0.7881701 : ℝ) ≤ Real.sqrt (1 - (200 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (1.1538801 : ℝ) ≤ Real.sqrt (1 + (175 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 + (175 : ℝ)/528) := Real.sqrt_pos.mpr (by norm_num)
  have hkey : 2 * (Real.sqrt (1 - (175 : ℝ)/528) - Real.sqrt (1 - (200 : ℝ)/528)) /
      Real.sqrt (1 + (175 : ℝ)/528) ≤ (0.05111 : ℝ) := by
    rw [div_le_iff₀ hpos]
    have e1 : 2 * (Real.sqrt (1 - (175 : ℝ)/528) - Real.sqrt (1 - (200 : ℝ)/528)) ≤
        2 * ((0.8176556 : ℝ) - (0.7881701 : ℝ)) := by linarith
    have e2 : 2 * ((0.8176556 : ℝ) - (0.7881701 : ℝ)) ≤ (0.05111 : ℝ) * (1.1538801 : ℝ) := by norm_num
    have e3 : (0.05111 : ℝ) * (1.1538801 : ℝ) ≤
        (0.05111 : ℝ) * Real.sqrt (1 + (175 : ℝ)/528) := by nlinarith [hC]
    linarith
  linarith

/-- `arcsin` increment on the grid step `[200/528, 225/528]`. -/
private lemma asub_8 : Real.arcsin ((225 : ℝ)/528) - Real.arcsin ((200 : ℝ)/528) ≤ 0.05218 := by
  have h := arcsin_sub_le_sqrt (a := (200 : ℝ)/528) (b := (225 : ℝ)/528)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : Real.sqrt (1 - (200 : ℝ)/528) ≤ (0.7881702 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB : (0.7575378 : ℝ) ≤ Real.sqrt (1 - (225 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (1.1742179 : ℝ) ≤ Real.sqrt (1 + (200 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 + (200 : ℝ)/528) := Real.sqrt_pos.mpr (by norm_num)
  have hkey : 2 * (Real.sqrt (1 - (200 : ℝ)/528) - Real.sqrt (1 - (225 : ℝ)/528)) /
      Real.sqrt (1 + (200 : ℝ)/528) ≤ (0.05218 : ℝ) := by
    rw [div_le_iff₀ hpos]
    have e1 : 2 * (Real.sqrt (1 - (200 : ℝ)/528) - Real.sqrt (1 - (225 : ℝ)/528)) ≤
        2 * ((0.7881702 : ℝ) - (0.7575378 : ℝ)) := by linarith
    have e2 : 2 * ((0.7881702 : ℝ) - (0.7575378 : ℝ)) ≤ (0.05218 : ℝ) * (1.1742179 : ℝ) := by norm_num
    have e3 : (0.05218 : ℝ) * (1.1742179 : ℝ) ≤
        (0.05218 : ℝ) * Real.sqrt (1 + (200 : ℝ)/528) := by nlinarith [hC]
    linarith
  linarith

/-- `arcsin` increment on the grid step `[225/528, 250/528]`. -/
private lemma asub_9 : Real.arcsin ((250 : ℝ)/528) - Real.arcsin ((225 : ℝ)/528) ≤ 0.05347 := by
  have h := arcsin_sub_le_sqrt (a := (225 : ℝ)/528) (b := (250 : ℝ)/528)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : Real.sqrt (1 - (225 : ℝ)/528) ≤ (0.7575379 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB : (0.7256136 : ℝ) ≤ Real.sqrt (1 - (250 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (1.1942095 : ℝ) ≤ Real.sqrt (1 + (225 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 + (225 : ℝ)/528) := Real.sqrt_pos.mpr (by norm_num)
  have hkey : 2 * (Real.sqrt (1 - (225 : ℝ)/528) - Real.sqrt (1 - (250 : ℝ)/528)) /
      Real.sqrt (1 + (225 : ℝ)/528) ≤ (0.05347 : ℝ) := by
    rw [div_le_iff₀ hpos]
    have e1 : 2 * (Real.sqrt (1 - (225 : ℝ)/528) - Real.sqrt (1 - (250 : ℝ)/528)) ≤
        2 * ((0.7575379 : ℝ) - (0.7256136 : ℝ)) := by linarith
    have e2 : 2 * ((0.7575379 : ℝ) - (0.7256136 : ℝ)) ≤ (0.05347 : ℝ) * (1.1942095 : ℝ) := by norm_num
    have e3 : (0.05347 : ℝ) * (1.1942095 : ℝ) ≤
        (0.05347 : ℝ) * Real.sqrt (1 + (225 : ℝ)/528) := by nlinarith [hC]
    linarith
  linarith

/-- `arcsin` increment on the grid step `[250/528, 275/528]`. -/
private lemma asub_10 : Real.arcsin ((275 : ℝ)/528) - Real.arcsin ((250 : ℝ)/528) ≤ 0.05503 := by
  have h := arcsin_sub_le_sqrt (a := (250 : ℝ)/528) (b := (275 : ℝ)/528)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : Real.sqrt (1 - (250 : ℝ)/528) ≤ (0.7256137 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB : (0.6922186 : ℝ) ≤ Real.sqrt (1 - (275 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (1.2138718 : ℝ) ≤ Real.sqrt (1 + (250 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 + (250 : ℝ)/528) := Real.sqrt_pos.mpr (by norm_num)
  have hkey : 2 * (Real.sqrt (1 - (250 : ℝ)/528) - Real.sqrt (1 - (275 : ℝ)/528)) /
      Real.sqrt (1 + (250 : ℝ)/528) ≤ (0.05503 : ℝ) := by
    rw [div_le_iff₀ hpos]
    have e1 : 2 * (Real.sqrt (1 - (250 : ℝ)/528) - Real.sqrt (1 - (275 : ℝ)/528)) ≤
        2 * ((0.7256137 : ℝ) - (0.6922186 : ℝ)) := by linarith
    have e2 : 2 * ((0.7256137 : ℝ) - (0.6922186 : ℝ)) ≤ (0.05503 : ℝ) * (1.2138718 : ℝ) := by norm_num
    have e3 : (0.05503 : ℝ) * (1.2138718 : ℝ) ≤
        (0.05503 : ℝ) * Real.sqrt (1 + (250 : ℝ)/528) := by nlinarith [hC]
    linarith
  linarith

/-- `arcsin` increment on the grid step `[275/528, 300/528]`. -/
private lemma asub_11 : Real.arcsin ((300 : ℝ)/528) - Real.arcsin ((275 : ℝ)/528) ≤ 0.05691 := by
  have h := arcsin_sub_le_sqrt (a := (275 : ℝ)/528) (b := (300 : ℝ)/528)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : Real.sqrt (1 - (275 : ℝ)/528) ≤ (0.6922187 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB : (0.6571287 : ℝ) ≤ Real.sqrt (1 - (300 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (1.2332207 : ℝ) ≤ Real.sqrt (1 + (275 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 + (275 : ℝ)/528) := Real.sqrt_pos.mpr (by norm_num)
  have hkey : 2 * (Real.sqrt (1 - (275 : ℝ)/528) - Real.sqrt (1 - (300 : ℝ)/528)) /
      Real.sqrt (1 + (275 : ℝ)/528) ≤ (0.05691 : ℝ) := by
    rw [div_le_iff₀ hpos]
    have e1 : 2 * (Real.sqrt (1 - (275 : ℝ)/528) - Real.sqrt (1 - (300 : ℝ)/528)) ≤
        2 * ((0.6922187 : ℝ) - (0.6571287 : ℝ)) := by linarith
    have e2 : 2 * ((0.6922187 : ℝ) - (0.6571287 : ℝ)) ≤ (0.05691 : ℝ) * (1.2332207 : ℝ) := by norm_num
    have e3 : (0.05691 : ℝ) * (1.2332207 : ℝ) ≤
        (0.05691 : ℝ) * Real.sqrt (1 + (275 : ℝ)/528) := by nlinarith [hC]
    linarith
  linarith

/-- `arcsin` increment on the grid step `[300/528, 325/528]`. -/
private lemma asub_12 : Real.arcsin ((325 : ℝ)/528) - Real.arcsin ((300 : ℝ)/528) ≤ 0.05921 := by
  have h := arcsin_sub_le_sqrt (a := (300 : ℝ)/528) (b := (325 : ℝ)/528)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : Real.sqrt (1 - (300 : ℝ)/528) ≤ (0.6571288 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB : (0.6200562 : ℝ) ≤ Real.sqrt (1 - (325 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (1.2522706 : ℝ) ≤ Real.sqrt (1 + (300 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 + (300 : ℝ)/528) := Real.sqrt_pos.mpr (by norm_num)
  have hkey : 2 * (Real.sqrt (1 - (300 : ℝ)/528) - Real.sqrt (1 - (325 : ℝ)/528)) /
      Real.sqrt (1 + (300 : ℝ)/528) ≤ (0.05921 : ℝ) := by
    rw [div_le_iff₀ hpos]
    have e1 : 2 * (Real.sqrt (1 - (300 : ℝ)/528) - Real.sqrt (1 - (325 : ℝ)/528)) ≤
        2 * ((0.6571288 : ℝ) - (0.6200562 : ℝ)) := by linarith
    have e2 : 2 * ((0.6571288 : ℝ) - (0.6200562 : ℝ)) ≤ (0.05921 : ℝ) * (1.2522706 : ℝ) := by norm_num
    have e3 : (0.05921 : ℝ) * (1.2522706 : ℝ) ≤
        (0.05921 : ℝ) * Real.sqrt (1 + (300 : ℝ)/528) := by nlinarith [hC]
    linarith
  linarith

/-- `arcsin` increment on the grid step `[325/528, 350/528]`. -/
private lemma asub_13 : Real.arcsin ((350 : ℝ)/528) - Real.arcsin ((325 : ℝ)/528) ≤ 0.06206 := by
  have h := arcsin_sub_le_sqrt (a := (325 : ℝ)/528) (b := (350 : ℝ)/528)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : Real.sqrt (1 - (325 : ℝ)/528) ≤ (0.6200563 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB : (0.5806214 : ℝ) ≤ Real.sqrt (1 - (350 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (1.2710351 : ℝ) ≤ Real.sqrt (1 + (325 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 + (325 : ℝ)/528) := Real.sqrt_pos.mpr (by norm_num)
  have hkey : 2 * (Real.sqrt (1 - (325 : ℝ)/528) - Real.sqrt (1 - (350 : ℝ)/528)) /
      Real.sqrt (1 + (325 : ℝ)/528) ≤ (0.06206 : ℝ) := by
    rw [div_le_iff₀ hpos]
    have e1 : 2 * (Real.sqrt (1 - (325 : ℝ)/528) - Real.sqrt (1 - (350 : ℝ)/528)) ≤
        2 * ((0.6200563 : ℝ) - (0.5806214 : ℝ)) := by linarith
    have e2 : 2 * ((0.6200563 : ℝ) - (0.5806214 : ℝ)) ≤ (0.06206 : ℝ) * (1.2710351 : ℝ) := by norm_num
    have e3 : (0.06206 : ℝ) * (1.2710351 : ℝ) ≤
        (0.06206 : ℝ) * Real.sqrt (1 + (325 : ℝ)/528) := by nlinarith [hC]
    linarith
  linarith

/-- `arcsin` increment on the grid step `[350/528, 375/528]`. -/
private lemma asub_14 : Real.arcsin ((375 : ℝ)/528) - Real.arcsin ((350 : ℝ)/528) ≤ 0.06564 := by
  have h := arcsin_sub_le_sqrt (a := (350 : ℝ)/528) (b := (375 : ℝ)/528)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : Real.sqrt (1 - (350 : ℝ)/528) ≤ (0.5806215 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB : (0.5383054 : ℝ) ≤ Real.sqrt (1 - (375 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (1.2895265 : ℝ) ≤ Real.sqrt (1 + (350 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 + (350 : ℝ)/528) := Real.sqrt_pos.mpr (by norm_num)
  have hkey : 2 * (Real.sqrt (1 - (350 : ℝ)/528) - Real.sqrt (1 - (375 : ℝ)/528)) /
      Real.sqrt (1 + (350 : ℝ)/528) ≤ (0.06564 : ℝ) := by
    rw [div_le_iff₀ hpos]
    have e1 : 2 * (Real.sqrt (1 - (350 : ℝ)/528) - Real.sqrt (1 - (375 : ℝ)/528)) ≤
        2 * ((0.5806215 : ℝ) - (0.5383054 : ℝ)) := by linarith
    have e2 : 2 * ((0.5806215 : ℝ) - (0.5383054 : ℝ)) ≤ (0.06564 : ℝ) * (1.2895265 : ℝ) := by norm_num
    have e3 : (0.06564 : ℝ) * (1.2895265 : ℝ) ≤
        (0.06564 : ℝ) * Real.sqrt (1 + (350 : ℝ)/528) := by nlinarith [hC]
    linarith
  linarith

/-- `arcsin` increment on the grid step `[375/528, 400/528]`. -/
private lemma asub_15 : Real.arcsin ((400 : ℝ)/528) - Real.arcsin ((375 : ℝ)/528) ≤ 0.07026 := by
  have h := arcsin_sub_le_sqrt (a := (375 : ℝ)/528) (b := (400 : ℝ)/528)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : Real.sqrt (1 - (375 : ℝ)/528) ≤ (0.5383055 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB : (0.4923659 : ℝ) ≤ Real.sqrt (1 - (400 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (1.3077565 : ℝ) ≤ Real.sqrt (1 + (375 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 + (375 : ℝ)/528) := Real.sqrt_pos.mpr (by norm_num)
  have hkey : 2 * (Real.sqrt (1 - (375 : ℝ)/528) - Real.sqrt (1 - (400 : ℝ)/528)) /
      Real.sqrt (1 + (375 : ℝ)/528) ≤ (0.07026 : ℝ) := by
    rw [div_le_iff₀ hpos]
    have e1 : 2 * (Real.sqrt (1 - (375 : ℝ)/528) - Real.sqrt (1 - (400 : ℝ)/528)) ≤
        2 * ((0.5383055 : ℝ) - (0.4923659 : ℝ)) := by linarith
    have e2 : 2 * ((0.5383055 : ℝ) - (0.4923659 : ℝ)) ≤ (0.07026 : ℝ) * (1.3077565 : ℝ) := by norm_num
    have e3 : (0.07026 : ℝ) * (1.3077565 : ℝ) ≤
        (0.07026 : ℝ) * Real.sqrt (1 + (375 : ℝ)/528) := by nlinarith [hC]
    linarith
  linarith

/-- `arcsin` increment on the grid step `[400/528, 425/528]`. -/
private lemma asub_16 : Real.arcsin ((425 : ℝ)/528) - Real.arcsin ((400 : ℝ)/528) ≤ 0.07648 := by
  have h := arcsin_sub_le_sqrt (a := (400 : ℝ)/528) (b := (425 : ℝ)/528)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : Real.sqrt (1 - (400 : ℝ)/528) ≤ (0.4923660 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB : (0.4416738 : ℝ) ≤ Real.sqrt (1 - (425 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (1.3257359 : ℝ) ≤ Real.sqrt (1 + (400 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 + (400 : ℝ)/528) := Real.sqrt_pos.mpr (by norm_num)
  have hkey : 2 * (Real.sqrt (1 - (400 : ℝ)/528) - Real.sqrt (1 - (425 : ℝ)/528)) /
      Real.sqrt (1 + (400 : ℝ)/528) ≤ (0.07648 : ℝ) := by
    rw [div_le_iff₀ hpos]
    have e1 : 2 * (Real.sqrt (1 - (400 : ℝ)/528) - Real.sqrt (1 - (425 : ℝ)/528)) ≤
        2 * ((0.4923660 : ℝ) - (0.4416738 : ℝ)) := by linarith
    have e2 : 2 * ((0.4923660 : ℝ) - (0.4416738 : ℝ)) ≤ (0.07648 : ℝ) * (1.3257359 : ℝ) := by norm_num
    have e3 : (0.07648 : ℝ) * (1.3257359 : ℝ) ≤
        (0.07648 : ℝ) * Real.sqrt (1 + (400 : ℝ)/528) := by nlinarith [hC]
    linarith
  linarith

/-- `arcsin` increment on the grid step `[425/528, 450/528]`. -/
private lemma asub_17 : Real.arcsin ((450 : ℝ)/528) - Real.arcsin ((425 : ℝ)/528) ≤ 0.08534 := by
  have h := arcsin_sub_le_sqrt (a := (425 : ℝ)/528) (b := (450 : ℝ)/528)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : Real.sqrt (1 - (425 : ℝ)/528) ≤ (0.4416739 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB : (0.3843530 : ℝ) ≤ Real.sqrt (1 - (450 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (1.3434746 : ℝ) ≤ Real.sqrt (1 + (425 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 + (425 : ℝ)/528) := Real.sqrt_pos.mpr (by norm_num)
  have hkey : 2 * (Real.sqrt (1 - (425 : ℝ)/528) - Real.sqrt (1 - (450 : ℝ)/528)) /
      Real.sqrt (1 + (425 : ℝ)/528) ≤ (0.08534 : ℝ) := by
    rw [div_le_iff₀ hpos]
    have e1 : 2 * (Real.sqrt (1 - (425 : ℝ)/528) - Real.sqrt (1 - (450 : ℝ)/528)) ≤
        2 * ((0.4416739 : ℝ) - (0.3843530 : ℝ)) := by linarith
    have e2 : 2 * ((0.4416739 : ℝ) - (0.3843530 : ℝ)) ≤ (0.08534 : ℝ) * (1.3434746 : ℝ) := by norm_num
    have e3 : (0.08534 : ℝ) * (1.3434746 : ℝ) ≤
        (0.08534 : ℝ) * Real.sqrt (1 + (425 : ℝ)/528) := by nlinarith [hC]
    linarith
  linarith

/-- `arcsin` increment on the grid step `[450/528, 475/528]`. -/
private lemma asub_18 : Real.arcsin ((475 : ℝ)/528) - Real.arcsin ((450 : ℝ)/528) ≤ 0.09924 := by
  have h := arcsin_sub_le_sqrt (a := (450 : ℝ)/528) (b := (475 : ℝ)/528)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : Real.sqrt (1 - (450 : ℝ)/528) ≤ (0.3843531 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB : (0.3168261 : ℝ) ≤ Real.sqrt (1 - (475 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (1.3609822 : ℝ) ≤ Real.sqrt (1 + (450 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 + (450 : ℝ)/528) := Real.sqrt_pos.mpr (by norm_num)
  have hkey : 2 * (Real.sqrt (1 - (450 : ℝ)/528) - Real.sqrt (1 - (475 : ℝ)/528)) /
      Real.sqrt (1 + (450 : ℝ)/528) ≤ (0.09924 : ℝ) := by
    rw [div_le_iff₀ hpos]
    have e1 : 2 * (Real.sqrt (1 - (450 : ℝ)/528) - Real.sqrt (1 - (475 : ℝ)/528)) ≤
        2 * ((0.3843531 : ℝ) - (0.3168261 : ℝ)) := by linarith
    have e2 : 2 * ((0.3843531 : ℝ) - (0.3168261 : ℝ)) ≤ (0.09924 : ℝ) * (1.3609822 : ℝ) := by norm_num
    have e3 : (0.09924 : ℝ) * (1.3609822 : ℝ) ≤
        (0.09924 : ℝ) * Real.sqrt (1 + (450 : ℝ)/528) := by nlinarith [hC]
    linarith
  linarith

/-- `arcsin` increment on the grid step `[475/528, 500/528]`. -/
private lemma asub_19 : Real.arcsin ((500 : ℝ)/528) - Real.arcsin ((475 : ℝ)/528) ≤ 0.12559 := by
  have h := arcsin_sub_le_sqrt (a := (475 : ℝ)/528) (b := (500 : ℝ)/528)
    (by norm_num) (by norm_num) (by norm_num)
  have hA : Real.sqrt (1 - (475 : ℝ)/528) ≤ (0.3168262 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have hB : (0.2302830 : ℝ) ≤ Real.sqrt (1 - (500 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hC : (1.3782674 : ℝ) ≤ Real.sqrt (1 + (475 : ℝ)/528) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have hpos : (0 : ℝ) < Real.sqrt (1 + (475 : ℝ)/528) := Real.sqrt_pos.mpr (by norm_num)
  have hkey : 2 * (Real.sqrt (1 - (475 : ℝ)/528) - Real.sqrt (1 - (500 : ℝ)/528)) /
      Real.sqrt (1 + (475 : ℝ)/528) ≤ (0.12559 : ℝ) := by
    rw [div_le_iff₀ hpos]
    have e1 : 2 * (Real.sqrt (1 - (475 : ℝ)/528) - Real.sqrt (1 - (500 : ℝ)/528)) ≤
        2 * ((0.3168262 : ℝ) - (0.2302830 : ℝ)) := by linarith
    have e2 : 2 * ((0.3168262 : ℝ) - (0.2302830 : ℝ)) ≤ (0.12559 : ℝ) * (1.3782674 : ℝ) := by norm_num
    have e3 : (0.12559 : ℝ) * (1.3782674 : ℝ) ≤
        (0.12559 : ℝ) * Real.sqrt (1 + (475 : ℝ)/528) := by nlinarith [hC]
    linarith
  linarith

-- lengths of the chord pieces
/-- Length of the `j = 0` chord piece of the branch one integral. -/
private lemma len_0 : Real.arccos ((0 : ℝ)/132) - Real.arccos ((25 : ℝ)/132) ≤ 0.19267 := by
  rw [Real.arccos_eq_pi_div_two_sub_arcsin, Real.arccos_eq_pi_div_two_sub_arcsin]
  linarith [asub_0, asub_1, asub_2, asub_3]

/-- Length of the `j = 1` chord piece of the branch one integral. -/
private lemma len_1 : Real.arccos ((25 : ℝ)/132) - Real.arccos ((50 : ℝ)/132) ≤ 0.19981 := by
  rw [Real.arccos_eq_pi_div_two_sub_arcsin, Real.arccos_eq_pi_div_two_sub_arcsin]
  linarith [asub_4, asub_5, asub_6, asub_7]

/-- Length of the `j = 2` chord piece of the branch one integral. -/
private lemma len_2 : Real.arccos ((50 : ℝ)/132) - Real.arccos ((75 : ℝ)/132) ≤ 0.21759 := by
  rw [Real.arccos_eq_pi_div_two_sub_arcsin, Real.arccos_eq_pi_div_two_sub_arcsin]
  linarith [asub_8, asub_9, asub_10, asub_11]

/-- Length of the `j = 3` chord piece of the branch one integral. -/
private lemma len_3 : Real.arccos ((75 : ℝ)/132) - Real.arccos ((100 : ℝ)/132) ≤ 0.25717 := by
  rw [Real.arccos_eq_pi_div_two_sub_arcsin, Real.arccos_eq_pi_div_two_sub_arcsin]
  linarith [asub_12, asub_13, asub_14, asub_15]

/-- Length of the `j = 4` chord piece of the branch one integral. -/
private lemma len_4 : Real.arccos ((100 : ℝ)/132) - Real.arccos ((125 : ℝ)/132) ≤ 0.38665 := by
  rw [Real.arccos_eq_pi_div_two_sub_arcsin, Real.arccos_eq_pi_div_two_sub_arcsin]
  linarith [asub_16, asub_17, asub_18, asub_19]

-- `sin` increments on the chord pieces

/-- `sin` increment on the `j = 0` chord piece. -/
private lemma sinj_0 : (0.01808 : ℝ) ≤ Real.sqrt (1 - ((0 : ℝ)/132)^2) -
    Real.sqrt (1 - ((25 : ℝ)/132)^2) := by
  have s1 : (1.0000000 : ℝ) ≤ Real.sqrt (1 - ((0 : ℝ)/132)^2) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have s2 : Real.sqrt (1 - ((25 : ℝ)/132)^2) ≤ (0.9819012 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

/-- `sin` increment on the `j = 1` chord piece. -/
private lemma sinj_1 : (0.05641 : ℝ) ≤ Real.sqrt (1 - ((25 : ℝ)/132)^2) -
    Real.sqrt (1 - ((50 : ℝ)/132)^2) := by
  have s1 : (0.9819011 : ℝ) ≤ Real.sqrt (1 - ((25 : ℝ)/132)^2) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have s2 : Real.sqrt (1 - ((50 : ℝ)/132)^2) ≤ (0.9254836 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

/-- `sin` increment on the `j = 2` chord piece. -/
private lemma sinj_2 : (0.10256 : ℝ) ≤ Real.sqrt (1 - ((50 : ℝ)/132)^2) -
    Real.sqrt (1 - ((75 : ℝ)/132)^2) := by
  have s1 : (0.9254835 : ℝ) ≤ Real.sqrt (1 - ((50 : ℝ)/132)^2) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have s2 : Real.sqrt (1 - ((75 : ℝ)/132)^2) ≤ (0.8229031 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

/-- `sin` increment on the `j = 3` chord piece. -/
private lemma sinj_3 : (0.17015 : ℝ) ≤ Real.sqrt (1 - ((75 : ℝ)/132)^2) -
    Real.sqrt (1 - ((100 : ℝ)/132)^2) := by
  have s1 : (0.8229030 : ℝ) ≤ Real.sqrt (1 - ((75 : ℝ)/132)^2) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have s2 : Real.sqrt (1 - ((100 : ℝ)/132)^2) ≤ (0.6527473 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

/-- `sin` increment on the `j = 4` chord piece. -/
private lemma sinj_4 : (0.33141 : ℝ) ≤ Real.sqrt (1 - ((100 : ℝ)/132)^2) -
    Real.sqrt (1 - ((125 : ℝ)/132)^2) := by
  have s1 : (0.6527472 : ℝ) ≤ Real.sqrt (1 - ((100 : ℝ)/132)^2) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have s2 : Real.sqrt (1 - ((125 : ℝ)/132)^2) ≤ (0.3213229 : ℝ) := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  linarith

/-- Length of the final piece: `arccos (125/132) = arcsin (√(1 - (125/132)^2))`. -/
private lemma len_last : Real.arccos ((125 : ℝ)/132) ≤ 0.3524 := by
  have hb0 : (0:ℝ) ≤ Real.sqrt (1 - ((125 : ℝ)/132)^2) := Real.sqrt_nonneg _
  have hb1 : Real.sqrt (1 - ((125 : ℝ)/132)^2) ≤ 0.32134 := by
    rw [Real.sqrt_le_left (by norm_num)]; norm_num
  have harccos : Real.arccos ((125 : ℝ)/132) = Real.arcsin (Real.sqrt (1 - ((125 : ℝ)/132)^2)) :=
    Real.arccos_eq_arcsin (by norm_num)
  rw [harccos]
  have hlt : Real.sqrt (1 - ((125 : ℝ)/132)^2) < 1 := by nlinarith [hb1]
  have h := arcsin_sub_le_sqrt (a := (0:ℝ)) (b := Real.sqrt (1 - ((125 : ℝ)/132)^2))
    (ha := by norm_num) (hab := hb0) (hb := hlt)
  have hB : (0.82380 : ℝ) ≤ Real.sqrt (1 - Real.sqrt (1 - ((125 : ℝ)/132)^2)) := by
    have hsq : (0.82380 : ℝ)^2 ≤ 1 - Real.sqrt (1 - ((125 : ℝ)/132)^2) := by nlinarith [hb1]
    calc (0.82380 : ℝ) = Real.sqrt ((0.82380 : ℝ)^2) := (Real.sqrt_sq (by norm_num)).symm
      _ ≤ Real.sqrt (1 - Real.sqrt (1 - ((125 : ℝ)/132)^2)) := Real.sqrt_le_sqrt hsq
  have hkey : 2 * (Real.sqrt (1 - 0) - Real.sqrt (1 - Real.sqrt (1 - ((125 : ℝ)/132)^2))) ≤
      (0.3524 : ℝ) := by
    have h1 : Real.sqrt (1 - 0) = (1:ℝ) := by norm_num
    linarith [h1, hB]
  have hz : Real.arcsin (0:ℝ) = 0 := Real.arcsin_zero
  linarith [h, hkey, hz]

/-- One chord step: the branch one envelope lies below the chord through two knot values
whenever `cos φ` lies between the knots. -/
private lemma chord_pt {u₀ u₁ La Lb Ua Ub : ℝ} {φ : ℝ} (hu0 : 0 ≤ u₀) (hu : u₀ < u₁)
    (hLa0 : 0 ≤ La) (hLb0 : 0 ≤ Lb) (hUa0 : 0 < Ua) (hUb0 : 0 < Ub)
    (hUa : ∑' n : ℕ, (n : ℝ) ^ (-((5 : ℝ)/4 + 1.32 * u₀)) ≤ Ua)
    (hUb : ∑' n : ℕ, (n : ℝ) ^ (-((5 : ℝ)/4 + 1.32 * u₁)) ≤ Ub)
    (hla : Real.log Ua ≤ La) (hlb : Real.log Ub ≤ Lb)
    (hc : Real.cos φ ∈ Set.Icc u₀ u₁) :
    Real.log (max 1 ‖riemannZeta (((5 : ℝ)/4 + 1.32 * Real.cos φ : ℝ) : ℂ)‖) ≤
      La + (Lb - La) / (u₁ - u₀) * (Real.cos φ - u₀) := by
  have hpos : (0:ℝ) < u₁ - u₀ := by linarith
  have hne : u₁ - u₀ ≠ 0 := ne_of_gt hpos
  set θ : ℝ := (Real.cos φ - u₀) / (u₁ - u₀) with hθ
  have hθ0 : 0 ≤ θ := div_nonneg (by linarith [hc.1]) hpos.le
  have hθ1 : θ ≤ 1 := by rw [hθ, div_le_one hpos]; linarith [hc.2]
  have hkey := log_zeta_chord (a := (5:ℝ)/4 + 1.32*u₀) (b := (5:ℝ)/4 + 1.32*u₁) (θ := θ)
    (by linarith) (by linarith) hθ0 hθ1 hUa0 hUb0 hUa hUb
  have hσ : (1 - θ) * ((5:ℝ)/4 + 1.32*u₀) + θ * ((5:ℝ)/4 + 1.32*u₁)
      = (5:ℝ)/4 + 1.32 * Real.cos φ := by
    rw [hθ]; field_simp; ring
  rw [hσ] at hkey
  have hbound : (1 - θ) * Real.log Ua + θ * Real.log Ub ≤ (1 - θ) * La + θ * Lb := by
    have h1 := mul_le_mul_of_nonneg_left hla (by linarith : (0:ℝ) ≤ 1 - θ)
    have h2 := mul_le_mul_of_nonneg_left hlb hθ0
    linarith
  have hnonneg : (0:ℝ) ≤ (1 - θ) * La + θ * Lb := by
    have h1 := mul_nonneg (by linarith : (0:ℝ) ≤ 1 - θ) hLa0
    have h2 := mul_nonneg hθ0 hLb0
    linarith
  have hmax : Real.log (max 1 ‖riemannZeta (((5 : ℝ)/4 + 1.32 * Real.cos φ : ℝ) : ℂ)‖)
      = max 0 (Real.log ‖riemannZeta (((5 : ℝ)/4 + 1.32 * Real.cos φ : ℝ) : ℂ)‖) := by
    generalize hz : riemannZeta (((5 : ℝ)/4 + 1.32 * Real.cos φ : ℝ) : ℂ) = z
    have hz0 : (0:ℝ) ≤ ‖z‖ := norm_nonneg z
    rcases le_or_gt ‖z‖ 1 with h1 | h1
    · rw [max_eq_left h1, Real.log_one, max_eq_left (Real.log_nonpos hz0 h1)]
    · rw [max_eq_right h1.le, max_eq_right (Real.log_nonneg h1.le)]
  rw [hmax]
  refine le_trans (max_le hnonneg (le_trans hkey hbound)) (le_of_eq ?_)
  rw [hθ]; field_simp; ring

/-- One chord piece of the branch one integral, integrated. -/
private lemma branch_one_piece {u₀ u₁ La Lb D S : ℝ} (T : ℝ)
    (hu0 : 0 ≤ u₀) (hu : u₀ < u₁) (hLa0 : 0 ≤ La) (hLb0 : 0 ≤ Lb) (hba : Lb ≤ La)
    (hD : Real.arccos u₀ - Real.arccos u₁ ≤ D)
    (hS : S ≤ Real.sqrt (1 - u₀ ^ 2) - Real.sqrt (1 - u₁ ^ 2))
    (hpt : ∀ φ ∈ Set.Icc (Real.arccos u₁) (Real.arccos u₀),
      logEnvelope T φ ≤ La + (Lb - La) / (u₁ - u₀) * (Real.cos φ - u₀)) :
    ∫ φ in (Real.arccos u₁)..(Real.arccos u₀), logEnvelope T φ ≤
      La * D + (Lb - La) / (u₁ - u₀) * (S - u₀ * D) := by
  set c : ℝ := (Lb - La) / (u₁ - u₀) with hc
  have hc0 : c ≤ 0 := div_nonpos_of_nonpos_of_nonneg (by linarith) (by linarith)
  have hab : Real.arccos u₁ ≤ Real.arccos u₀ := by
    rw [Real.arccos_eq_pi_div_two_sub_arcsin, Real.arccos_eq_pi_div_two_sub_arcsin]
    linarith [Real.arcsin_le_arcsin hu.le]
  have hInt : IntervalIntegrable (logEnvelope T) volume (Real.arccos u₁) (Real.arccos u₀) := by
    refine (Circle419.logEnvelope_integrable T).mono_set ?_
    intro x hx
    simp only [Set.uIcc_of_le hab, Set.uIcc_of_le Real.pi_pos.le] at hx ⊢
    exact ⟨le_trans (Real.arccos_nonneg u₁) hx.1, le_trans hx.2 (Real.arccos_le_pi u₀)⟩
  have hcont : IntervalIntegrable (fun x : ℝ => La + c * (Real.cos x - u₀)) volume
      (Real.arccos u₁) (Real.arccos u₀) := by
    apply Continuous.intervalIntegrable; fun_prop
  have hderiv : ∀ x ∈ Set.uIcc (Real.arccos u₁) (Real.arccos u₀),
      HasDerivAt (fun y : ℝ => La * y + c * (Real.sin y - u₀ * y)) (La + c * (Real.cos x - u₀)) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => La * y) La x := by
      simpa using (hasDerivAt_id x).const_mul La
    have h2 : HasDerivAt (fun y : ℝ => c * (Real.sin y - u₀ * y)) (c * (Real.cos x - u₀)) x := by
      have hs : HasDerivAt Real.sin (Real.cos x) x := Real.hasDerivAt_sin x
      have hl : HasDerivAt (fun y : ℝ => u₀ * y) u₀ x := by
        simpa using (hasDerivAt_id x).const_mul u₀
      exact (hs.sub hl).const_mul c
    exact h1.add h2
  have hval : (∫ φ in (Real.arccos u₁)..(Real.arccos u₀), (La + c * (Real.cos φ - u₀)))
      = La * (Real.arccos u₀ - Real.arccos u₁) +
        c * ((Real.sqrt (1 - u₀ ^ 2) - Real.sqrt (1 - u₁ ^ 2)) -
          u₀ * (Real.arccos u₀ - Real.arccos u₁)) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hcont, Real.sin_arccos, Real.sin_arccos]
    ring
  have hmono : (∫ φ in (Real.arccos u₁)..(Real.arccos u₀), logEnvelope T φ)
      ≤ ∫ φ in (Real.arccos u₁)..(Real.arccos u₀), (La + c * (Real.cos φ - u₀)) := by
    apply intervalIntegral.integral_mono_on hab hInt hcont
    intro φ hφ
    exact hpt φ hφ
  rw [hval] at hmono
  refine le_trans hmono ?_
  have hA : Real.arccos u₀ - Real.arccos u₁ - D ≤ 0 := by linarith
  have hB : S - (Real.sqrt (1 - u₀ ^ 2) - Real.sqrt (1 - u₁ ^ 2)) ≤ 0 := by linarith
  have p1 : (0:ℝ) ≤ La * (D - (Real.arccos u₀ - Real.arccos u₁)) :=
    mul_nonneg hLa0 (by linarith)
  have p2 : (0:ℝ) ≤ c * (S - (Real.sqrt (1 - u₀ ^ 2) - Real.sqrt (1 - u₁ ^ 2))) :=
    mul_nonneg_of_nonpos_of_nonpos hc0 hB
  have p3 : (0:ℝ) ≤ c * u₀ * (Real.arccos u₀ - Real.arccos u₁ - D) := by
    exact mul_nonneg_of_nonpos_of_nonpos (mul_nonpos_of_nonpos_of_nonneg hc0 hu0) hA
  have hp1 : La * (Real.arccos u₀ - Real.arccos u₁) + c * ((Real.sqrt (1 - u₀ ^ 2) - Real.sqrt (1 - u₁ ^ 2)) - u₀ * (Real.arccos u₀ - Real.arccos u₁))
      ≤ La * D + c * (S - u₀ * D) := by nlinarith [p1, p2, p3]
  simpa only [hc] using hp1

/-- `log U ≤ L` from a finite exponential series lower bound. -/
private lemma log_le_of_exp_series {U L : ℝ} (hU : 0 < U) (hL : 0 < L) (n : ℕ)
    (h : U ≤ ∑ i ∈ Finset.range n, L^i / (Nat.factorial i : ℝ)) : Real.log U ≤ L := by
  rw [Real.log_le_iff_le_exp hU]
  exact h.trans (Real.sum_le_exp_of_nonneg hL.le n)

/-- `log 4.609 ≤ 1.5284`. -/
private lemma lU0 : Real.log 4.609 ≤ 1.5284 := by
  refine log_le_of_exp_series (by norm_num) (by norm_num) 14 ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- `log 2.620 ≤ 0.9633`. -/
private lemma lU1 : Real.log 2.620 ≤ 0.9633 := by
  refine log_le_of_exp_series (by norm_num) (by norm_num) 14 ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- `log 1.967 ≤ 0.6767`. -/
private lemma lU2 : Real.log 1.967 ≤ 0.6767 := by
  refine log_le_of_exp_series (by norm_num) (by norm_num) 14 ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- `log 1.648 ≤ 0.4997`. -/
private lemma lU3 : Real.log 1.648 ≤ 0.4997 := by
  refine log_le_of_exp_series (by norm_num) (by norm_num) 14 ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- `log 1.463 ≤ 0.3806`. -/
private lemma lU4 : Real.log 1.463 ≤ 0.3806 := by
  refine log_le_of_exp_series (by norm_num) (by norm_num) 14 ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

/-- `log 1.344 ≤ 0.2958`. -/
private lemma lU5 : Real.log 1.344 ≤ 0.2958 := by
  refine log_le_of_exp_series (by norm_num) (by norm_num) 14 ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]


/-- `cos` maps `[arccos u₁, arccos u₀]` into `[u₀, u₁]` when `0 ≤ u₀ ≤ u₁ ≤ 1`. -/
private lemma cos_mem_Icc_of_mem_Icc_arccos {u₀ u₁ φ : ℝ} (hu0 : 0 ≤ u₀) (hu : u₀ ≤ u₁)
    (hu1 : u₁ ≤ 1) (hφ : φ ∈ Set.Icc (Real.arccos u₁) (Real.arccos u₀)) :
    Real.cos φ ∈ Set.Icc u₀ u₁ := by
  have h0 : 0 ≤ Real.arccos u₁ := Real.arccos_nonneg u₁
  have hpi : Real.arccos u₀ ≤ π := Real.arccos_le_pi u₀
  constructor
  · have hc := Real.cos_le_cos_of_nonneg_of_le_pi (x := φ) (y := Real.arccos u₀)
      (by linarith [hφ.1]) hpi hφ.2
    rwa [Real.cos_arccos (x := u₀) (by linarith) (by linarith)] at hc
  · have hc := Real.cos_le_cos_of_nonneg_of_le_pi (x := Real.arccos u₁) (y := φ) h0
      (by linarith [hφ.2, hpi]) hφ.1
    rwa [Real.cos_arccos (x := u₁) (by linarith) (by linarith)] at hc

/-- `sin` increment on the final piece: `√(1 - (125/132)^2)` down to `sin 0 = 0`. -/
private lemma sinj_last : (0.32132 : ℝ) ≤ Real.sqrt (1 - ((125 : ℝ)/132)^2) - Real.sqrt (1 - (1:ℝ)^2) := by
  have s1 : (0.32132 : ℝ) ≤ Real.sqrt (1 - ((125 : ℝ)/132)^2) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]; norm_num
  have s2 : Real.sqrt (1 - (1:ℝ)^2) = 0 := by norm_num
  linarith [s1, s2]


/-- Branch one of `envelope_budget`: on `[0, π/2]` the envelope is `log (max 1 ‖ζ (σ φ)‖)`
with `σ φ = 5/4 + 1.32 cos φ`, and the log-convexity chord of `log ζ` between the knots
`σ = 5/4, 3/2, 7/4, 2, 9/4, 5/2, 2.57` bounds its integral by `0.8809`. -/
private lemma integral_branch1 (T : ℝ) :
    ∫ φ in (0 : ℝ)..(π/2), logEnvelope T φ ≤ 0.8809 := by
  have hsub : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b → a ≤ π → b ≤ π →
      IntervalIntegrable (logEnvelope T) volume a b := by
    intro a b ha hb haπ hbπ
    refine (Circle419.logEnvelope_integrable T).mono_set ?_
    intro x hx
    rw [Set.mem_uIcc] at hx
    rw [Set.uIcc_of_le Real.pi_pos.le]
    rcases hx with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith, by linarith⟩
    · exact ⟨by linarith, by linarith⟩
  have hA : ∀ u : ℝ, 0 ≤ u → u ≤ 132 → 0 ≤ Real.arccos u ∧ Real.arccos u ≤ π := fun u hu _ =>
    ⟨Real.arccos_nonneg u, Real.arccos_le_pi u⟩
  -- piece 0: `u` from `((0 : ℝ)/132)` to `((25 : ℝ)/132)`
  have hpt0 : ∀ φ ∈ Set.Icc (Real.arccos ((25 : ℝ)/132)) (Real.arccos ((0 : ℝ)/132)),
      logEnvelope T φ ≤ 1.5284 + (0.9633 - 1.5284) / (((25 : ℝ)/132) - ((0 : ℝ)/132)) * (Real.cos φ - ((0 : ℝ)/132)) := by
    intro φ hφ
    have hmem := cos_mem_Icc_of_mem_Icc_arccos (u₀ := ((0 : ℝ)/132)) (u₁ := ((25 : ℝ)/132))
      (by norm_num) (by norm_num) (by norm_num) hφ
    have hbnd := chord_pt (u₀ := ((0 : ℝ)/132)) (u₁ := ((25 : ℝ)/132)) (La := 1.5284) (Lb := 0.9633)
      (Ua := 4.609) (Ub := 2.620) (φ := φ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by
        have e : (5:ℝ)/4 + 1.32 * ((0 : ℝ)/132) = 5 / 4 := by norm_num
        rw [e]; exact zsum_54) (by
        have e : (5:ℝ)/4 + 1.32 * ((25 : ℝ)/132) = 3 / 2 := by norm_num
        rw [e]; exact zsum_32) lU0 lU1 hmem
    rw [logEnvelope_branch1 (T := T) (φ := φ) ⟨by linarith [hφ.1, Real.arccos_nonneg ((25 : ℝ)/132)],
      by linarith [hφ.2, Real.arccos_le_pi_div_two.mpr (by norm_num : (0:ℝ) ≤ ((0 : ℝ)/132))]⟩]
    exact hbnd

  have hbnd0 : ∫ φ in (Real.arccos ((25 : ℝ)/132))..(Real.arccos ((0 : ℝ)/132)), logEnvelope T φ ≤ 0.2405311 := by
    have h := branch_one_piece (T := T) (u₀ := ((0 : ℝ)/132)) (u₁ := ((25 : ℝ)/132)) (La := 1.5284) (Lb := 0.9633)
      (D := 0.19267) (S := 0.01808)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (len_0) (sinj_0) hpt0
    refine h.trans ?_
    norm_num


  -- piece 1: `u` from `((25 : ℝ)/132)` to `((50 : ℝ)/132)`
  have hpt1 : ∀ φ ∈ Set.Icc (Real.arccos ((50 : ℝ)/132)) (Real.arccos ((25 : ℝ)/132)),
      logEnvelope T φ ≤ 0.9633 + (0.6767 - 0.9633) / (((50 : ℝ)/132) - ((25 : ℝ)/132)) * (Real.cos φ - ((25 : ℝ)/132)) := by
    intro φ hφ
    have hmem := cos_mem_Icc_of_mem_Icc_arccos (u₀ := ((25 : ℝ)/132)) (u₁ := ((50 : ℝ)/132))
      (by norm_num) (by norm_num) (by norm_num) hφ
    have hbnd := chord_pt (u₀ := ((25 : ℝ)/132)) (u₁ := ((50 : ℝ)/132)) (La := 0.9633) (Lb := 0.6767)
      (Ua := 2.620) (Ub := 1.967) (φ := φ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by
        have e : (5:ℝ)/4 + 1.32 * ((25 : ℝ)/132) = 3 / 2 := by norm_num
        rw [e]; exact zsum_32) (by
        have e : (5:ℝ)/4 + 1.32 * ((50 : ℝ)/132) = 7 / 4 := by norm_num
        rw [e]; exact zsum_74) lU1 lU2 hmem
    rw [logEnvelope_branch1 (T := T) (φ := φ) ⟨by linarith [hφ.1, Real.arccos_nonneg ((50 : ℝ)/132)],
      by linarith [hφ.2, Real.arccos_le_pi_div_two.mpr (by norm_num : (0:ℝ) ≤ ((25 : ℝ)/132))]⟩]
    exact hbnd

  have hbnd1 : ∫ φ in (Real.arccos ((50 : ℝ)/132))..(Real.arccos ((25 : ℝ)/132)), logEnvelope T φ ≤ 0.1643802 := by
    have h := branch_one_piece (T := T) (u₀ := ((25 : ℝ)/132)) (u₁ := ((50 : ℝ)/132)) (La := 0.9633) (Lb := 0.6767)
      (D := 0.19981) (S := 0.05641)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (len_1) (sinj_1) hpt1
    refine h.trans ?_
    norm_num


  -- piece 2: `u` from `((50 : ℝ)/132)` to `((75 : ℝ)/132)`
  have hpt2 : ∀ φ ∈ Set.Icc (Real.arccos ((75 : ℝ)/132)) (Real.arccos ((50 : ℝ)/132)),
      logEnvelope T φ ≤ 0.6767 + (0.4997 - 0.6767) / (((75 : ℝ)/132) - ((50 : ℝ)/132)) * (Real.cos φ - ((50 : ℝ)/132)) := by
    intro φ hφ
    have hmem := cos_mem_Icc_of_mem_Icc_arccos (u₀ := ((50 : ℝ)/132)) (u₁ := ((75 : ℝ)/132))
      (by norm_num) (by norm_num) (by norm_num) hφ
    have hbnd := chord_pt (u₀ := ((50 : ℝ)/132)) (u₁ := ((75 : ℝ)/132)) (La := 0.6767) (Lb := 0.4997)
      (Ua := 1.967) (Ub := 1.648) (φ := φ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by
        have e : (5:ℝ)/4 + 1.32 * ((50 : ℝ)/132) = 7 / 4 := by norm_num
        rw [e]; exact zsum_74) (by
        have e : (5:ℝ)/4 + 1.32 * ((75 : ℝ)/132) = (2:ℝ) / 1 := by norm_num
        rw [e]; exact zsum_2) lU2 lU3 hmem
    rw [logEnvelope_branch1 (T := T) (φ := φ) ⟨by linarith [hφ.1, Real.arccos_nonneg ((75 : ℝ)/132)],
      by linarith [hφ.2, Real.arccos_le_pi_div_two.mpr (by norm_num : (0:ℝ) ≤ ((50 : ℝ)/132))]⟩]
    exact hbnd

  have hbnd2 : ∫ φ in (Real.arccos ((75 : ℝ)/132))..(Real.arccos ((50 : ℝ)/132)), logEnvelope T φ ≤ 0.1284216 := by
    have h := branch_one_piece (T := T) (u₀ := ((50 : ℝ)/132)) (u₁ := ((75 : ℝ)/132)) (La := 0.6767) (Lb := 0.4997)
      (D := 0.21759) (S := 0.10256)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (len_2) (sinj_2) hpt2
    refine h.trans ?_
    norm_num


  -- piece 3: `u` from `((75 : ℝ)/132)` to `((100 : ℝ)/132)`
  have hpt3 : ∀ φ ∈ Set.Icc (Real.arccos ((100 : ℝ)/132)) (Real.arccos ((75 : ℝ)/132)),
      logEnvelope T φ ≤ 0.4997 + (0.3806 - 0.4997) / (((100 : ℝ)/132) - ((75 : ℝ)/132)) * (Real.cos φ - ((75 : ℝ)/132)) := by
    intro φ hφ
    have hmem := cos_mem_Icc_of_mem_Icc_arccos (u₀ := ((75 : ℝ)/132)) (u₁ := ((100 : ℝ)/132))
      (by norm_num) (by norm_num) (by norm_num) hφ
    have hbnd := chord_pt (u₀ := ((75 : ℝ)/132)) (u₁ := ((100 : ℝ)/132)) (La := 0.4997) (Lb := 0.3806)
      (Ua := 1.648) (Ub := 1.463) (φ := φ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by
        have e : (5:ℝ)/4 + 1.32 * ((75 : ℝ)/132) = (2:ℝ) / 1 := by norm_num
        rw [e]; exact zsum_2) (by
        have e : (5:ℝ)/4 + 1.32 * ((100 : ℝ)/132) = 9 / 4 := by norm_num
        rw [e]; exact zsum_94) lU3 lU4 hmem
    rw [logEnvelope_branch1 (T := T) (φ := φ) ⟨by linarith [hφ.1, Real.arccos_nonneg ((100 : ℝ)/132)],
      by linarith [hφ.2, Real.arccos_le_pi_div_two.mpr (by norm_num : (0:ℝ) ≤ ((75 : ℝ)/132))]⟩]
    exact hbnd

  have hbnd3 : ∫ φ in (Real.arccos ((100 : ℝ)/132))..(Real.arccos ((75 : ℝ)/132)), logEnvelope T φ ≤ 0.1133963 := by
    have h := branch_one_piece (T := T) (u₀ := ((75 : ℝ)/132)) (u₁ := ((100 : ℝ)/132)) (La := 0.4997) (Lb := 0.3806)
      (D := 0.25717) (S := 0.17015)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (len_3) (sinj_3) hpt3
    refine h.trans ?_
    norm_num


  -- piece 4: `u` from `((100 : ℝ)/132)` to `((125 : ℝ)/132)`
  have hpt4 : ∀ φ ∈ Set.Icc (Real.arccos ((125 : ℝ)/132)) (Real.arccos ((100 : ℝ)/132)),
      logEnvelope T φ ≤ 0.3806 + (0.2958 - 0.3806) / (((125 : ℝ)/132) - ((100 : ℝ)/132)) * (Real.cos φ - ((100 : ℝ)/132)) := by
    intro φ hφ
    have hmem := cos_mem_Icc_of_mem_Icc_arccos (u₀ := ((100 : ℝ)/132)) (u₁ := ((125 : ℝ)/132))
      (by norm_num) (by norm_num) (by norm_num) hφ
    have hbnd := chord_pt (u₀ := ((100 : ℝ)/132)) (u₁ := ((125 : ℝ)/132)) (La := 0.3806) (Lb := 0.2958)
      (Ua := 1.463) (Ub := 1.344) (φ := φ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by
        have e : (5:ℝ)/4 + 1.32 * ((100 : ℝ)/132) = 9 / 4 := by norm_num
        rw [e]; exact zsum_94) (by
        have e : (5:ℝ)/4 + 1.32 * ((125 : ℝ)/132) = 5 / 2 := by norm_num
        rw [e]; exact zsum_52) lU4 lU5 hmem
    rw [logEnvelope_branch1 (T := T) (φ := φ) ⟨by linarith [hφ.1, Real.arccos_nonneg ((125 : ℝ)/132)],
      by linarith [hφ.2, Real.arccos_le_pi_div_two.mpr (by norm_num : (0:ℝ) ≤ ((100 : ℝ)/132))]⟩]
    exact hbnd

  have hbnd4 : ∫ φ in (Real.arccos ((125 : ℝ)/132))..(Real.arccos ((100 : ℝ)/132)), logEnvelope T φ ≤ 0.1299239 := by
    have h := branch_one_piece (T := T) (u₀ := ((100 : ℝ)/132)) (u₁ := ((125 : ℝ)/132)) (La := 0.3806) (Lb := 0.2958)
      (D := 0.38665) (S := 0.33141)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (len_4) (sinj_4) hpt4
    refine h.trans ?_
    norm_num


  -- piece 5: `u` from `((125 : ℝ)/132)` to `1`
  have hpt5 : ∀ φ ∈ Set.Icc (Real.arccos 1) (Real.arccos ((125 : ℝ)/132)),
      logEnvelope T φ ≤ 0.2958 + (0.2958 - 0.2958) / (1 - ((125 : ℝ)/132)) * (Real.cos φ - ((125 : ℝ)/132)) := by
    intro φ hφ
    have hmem := cos_mem_Icc_of_mem_Icc_arccos (u₀ := ((125 : ℝ)/132)) (u₁ := 1)
      (by norm_num) (by norm_num) (by norm_num) hφ
    have hbnd := chord_pt (u₀ := ((125 : ℝ)/132)) (u₁ := 1) (La := 0.2958) (Lb := 0.2958)
      (Ua := 1.344) (Ub := 1.344) (φ := φ)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by
        have e : (5:ℝ)/4 + 1.32 * ((125 : ℝ)/132) = 5 / 2 := by norm_num
        rw [e]; exact zsum_52) (by
        have e : (5:ℝ)/4 + 1.32 * (1:ℝ) = 257 / 100 := by norm_num
        rw [e]
        exact (zsum_mono (by norm_num : (1:ℝ) < 5 / 2) (by norm_num : (5:ℝ) / 2 ≤ 257 / 100)).trans zsum_52) lU5 lU5 hmem
    rw [logEnvelope_branch1 (T := T) (φ := φ) ⟨by linarith [hφ.1, Real.arccos_nonneg 1],
      by linarith [hφ.2, Real.arccos_le_pi_div_two.mpr (by norm_num : (0:ℝ) ≤ ((125 : ℝ)/132))]⟩]
    exact hbnd

  have hbnd5 : ∫ φ in (0:ℝ)..(Real.arccos ((125 : ℝ)/132)), logEnvelope T φ ≤ 0.1042400 := by
    have h := branch_one_piece (T := T) (u₀ := ((125 : ℝ)/132)) (u₁ := 1) (La := 0.2958) (Lb := 0.2958)
      (D := 0.3524) (S := 0.32132)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      ((by linarith [len_last, Real.arccos_one])) (sinj_last) hpt5
    rw [Real.arccos_one] at h
    refine h.trans ?_
    norm_num


  rw [← Real.arccos_zero]
  have E5 := intervalIntegral.integral_add_adjacent_intervals
    (hsub 0 (Real.arccos ((125 : ℝ)/132)) le_rfl (Real.arccos_nonneg _) Real.pi_pos.le
      (Real.arccos_le_pi _))
    (hsub (Real.arccos ((125 : ℝ)/132)) (Real.arccos 0) (Real.arccos_nonneg _) (Real.arccos_nonneg _)
      (Real.arccos_le_pi _) (Real.arccos_le_pi _))
  have E4 := intervalIntegral.integral_add_adjacent_intervals
    (hsub (Real.arccos ((125 : ℝ)/132)) (Real.arccos ((100 : ℝ)/132)) (Real.arccos_nonneg _) (Real.arccos_nonneg _)
      (Real.arccos_le_pi _) (Real.arccos_le_pi _))
    (hsub (Real.arccos ((100 : ℝ)/132)) (Real.arccos 0) (Real.arccos_nonneg _) (Real.arccos_nonneg _)
      (Real.arccos_le_pi _) (Real.arccos_le_pi _))
  have E3 := intervalIntegral.integral_add_adjacent_intervals
    (hsub (Real.arccos ((100 : ℝ)/132)) (Real.arccos ((75 : ℝ)/132)) (Real.arccos_nonneg _) (Real.arccos_nonneg _)
      (Real.arccos_le_pi _) (Real.arccos_le_pi _))
    (hsub (Real.arccos ((75 : ℝ)/132)) (Real.arccos 0) (Real.arccos_nonneg _) (Real.arccos_nonneg _)
      (Real.arccos_le_pi _) (Real.arccos_le_pi _))
  have E2 := intervalIntegral.integral_add_adjacent_intervals
    (hsub (Real.arccos ((75 : ℝ)/132)) (Real.arccos ((50 : ℝ)/132)) (Real.arccos_nonneg _) (Real.arccos_nonneg _)
      (Real.arccos_le_pi _) (Real.arccos_le_pi _))
    (hsub (Real.arccos ((50 : ℝ)/132)) (Real.arccos 0) (Real.arccos_nonneg _) (Real.arccos_nonneg _)
      (Real.arccos_le_pi _) (Real.arccos_le_pi _))
  have E1 := intervalIntegral.integral_add_adjacent_intervals
    (hsub (Real.arccos ((50 : ℝ)/132)) (Real.arccos ((25 : ℝ)/132)) (Real.arccos_nonneg _) (Real.arccos_nonneg _)
      (Real.arccos_le_pi _) (Real.arccos_le_pi _))
    (hsub (Real.arccos ((25 : ℝ)/132)) (Real.arccos 0) (Real.arccos_nonneg _) (Real.arccos_nonneg _)
      (Real.arccos_le_pi _) (Real.arccos_le_pi _))
  have e0 : Real.arccos ((0 : ℝ)/132) = Real.arccos 0 := by norm_num
  rw [e0] at hbnd0
  have E5' : (∫ φ in (0:ℝ)..(Real.arccos ((125 : ℝ)/132)), logEnvelope T φ) +
      ∫ φ in (Real.arccos ((125 : ℝ)/132))..(Real.arccos 0), logEnvelope T φ
      = ∫ φ in (0:ℝ)..(Real.arccos 0), logEnvelope T φ := E5
  have E4' : (∫ φ in (Real.arccos ((125 : ℝ)/132))..(Real.arccos ((100 : ℝ)/132)), logEnvelope T φ) +
      ∫ φ in (Real.arccos ((100 : ℝ)/132))..(Real.arccos 0), logEnvelope T φ
      = ∫ φ in (Real.arccos ((125 : ℝ)/132))..(Real.arccos 0), logEnvelope T φ := E4
  have E3' : (∫ φ in (Real.arccos ((100 : ℝ)/132))..(Real.arccos ((75 : ℝ)/132)), logEnvelope T φ) +
      ∫ φ in (Real.arccos ((75 : ℝ)/132))..(Real.arccos 0), logEnvelope T φ
      = ∫ φ in (Real.arccos ((100 : ℝ)/132))..(Real.arccos 0), logEnvelope T φ := E3
  have E2' : (∫ φ in (Real.arccos ((75 : ℝ)/132))..(Real.arccos ((50 : ℝ)/132)), logEnvelope T φ) +
      ∫ φ in (Real.arccos ((50 : ℝ)/132))..(Real.arccos 0), logEnvelope T φ
      = ∫ φ in (Real.arccos ((75 : ℝ)/132))..(Real.arccos 0), logEnvelope T φ := E2
  have E1' : (∫ φ in (Real.arccos ((50 : ℝ)/132))..(Real.arccos ((25 : ℝ)/132)), logEnvelope T φ) +
      ∫ φ in (Real.arccos ((25 : ℝ)/132))..(Real.arccos 0), logEnvelope T φ
      = ∫ φ in (Real.arccos ((50 : ℝ)/132))..(Real.arccos 0), logEnvelope T φ := E1
  linarith [E1', E2', E3', E4', E5', hbnd0, hbnd1, hbnd2, hbnd3, hbnd4, hbnd5]



/-! ## `q = log(1.76)` and `1/(2 π q)` -/

private lemma q_lo : 0.56531 ≤ Real.log 1.76 := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h := Real.exp_bound' (x := 0.56531) (by norm_num) (by norm_num) (n := 12) (by norm_num)
  refine h.trans ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

private lemma q_hi : Real.log 1.76 ≤ 0.56532 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  refine (by norm_num : (1.76 : ℝ) ≤
    ∑ m ∈ Finset.range 12, (0.56532 : ℝ) ^ m / (m.factorial : ℝ)).trans ?_
  exact Real.sum_le_exp_of_nonneg (by norm_num) 12

private lemma four_r_three : (4 * 1.32 / 3 : ℝ) = 1.76 := by norm_num

private lemma q_lo' : 0.56531 ≤ Real.log (4 * 1.32 / 3) := by
  rw [four_r_three]; exact q_lo

private lemma q_hi' : Real.log (4 * 1.32 / 3) ≤ 0.56532 := by
  rw [four_r_three]; exact q_hi

private lemma two_pi_q_lo : 3.5519 ≤ 2 * Real.pi * Real.log (4 * 1.32 / 3) := by
  have h1 : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have h2 : (0.56531 : ℝ) ≤ Real.log (4 * 1.32 / 3) := q_lo'
  nlinarith

private lemma s_hi : 1 / (2 * Real.pi * Real.log (4 * 1.32 / 3)) ≤ 0.28154 := by
  have h := two_pi_q_lo
  have hp : (0:ℝ) < 2 * Real.pi * Real.log (4 * 1.32 / 3) := by
    have := q_lo'
    nlinarith [Real.pi_pos]
  rw [div_le_iff₀ hp]
  nlinarith

private lemma two_q_hi : 2 * Real.log (4 * 1.32 / 3) ≤ 1.13064 := by
  have := q_hi'
  linarith

/-! ## `exp` bound helpers for arguments in `[0,1]` -/

private lemma exp_le_rat {x c : ℝ} (hx0 : 0 ≤ x) (hx1 : x ≤ 1) {n : ℕ} (hn : 0 < n)
    (h : (∑ m ∈ Finset.range n, x ^ m / (m.factorial : ℝ)) +
      x ^ n * ((n : ℝ) + 1) / ((n.factorial : ℝ) * (n : ℝ)) ≤ c) :
    Real.exp x ≤ c :=
  (Real.exp_bound' hx0 hx1 hn).trans h

private lemma log_ge_of_exp_le {x y : ℝ} (hy : 0 < y) (h : Real.exp x ≤ y) : x ≤ Real.log y :=
  (Real.le_log_iff_exp_le hy).mpr h

private lemma log_le_of_le_exp {x y : ℝ} (hx : 0 < x) (h : x ≤ Real.exp y) : Real.log x ≤ y :=
  (Real.log_le_iff_le_exp hx).mpr h

/-! ## `log 1400 ≥ 7.244`, `log log T ≥ 1.98`, `log (2π) ≥ 1.837` -/

private lemma exp_7244 : Real.exp 0.7244 ≤ 2.0635 := by
  refine exp_le_rat (x := 0.7244) (c := 2.0635) (by norm_num) (by norm_num) (n := 20)
    (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

private lemma pow_20635 : (2.0635 : ℝ) ^ 10 ≤ 1400 := by norm_num

private lemma log_1400_ge : 7.244 ≤ Real.log 1400 := by
  refine log_ge_of_exp_le (by norm_num) ?_
  have h : Real.exp (7.244 : ℝ) = Real.exp (0.7244 : ℝ) ^ 10 := by
    rw [show (7.244 : ℝ) = (10 : ℕ) * 0.7244 by norm_num, Real.exp_nat_mul]
  rw [h]
  calc Real.exp 0.7244 ^ 10 ≤ (2.0635 : ℝ) ^ 10 :=
        pow_le_pow_left₀ (Real.exp_pos _).le exp_7244 10
    _ ≤ 1400 := pow_20635

private lemma log_T_ge {T : ℝ} (hT : 1400 ≤ T) : 7.244 ≤ Real.log T :=
  log_1400_ge.trans (Real.log_le_log (by norm_num) hT)

private lemma exp_099 : Real.exp 0.99 ≤ 2.6914 := by
  refine exp_le_rat (x := 0.99) (c := 2.6914) (by norm_num) (by norm_num) (n := 18)
    (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

private lemma exp_198_le : Real.exp 1.98 ≤ 7.244 := by
  have h : Real.exp (1.98 : ℝ) = Real.exp (0.99 : ℝ) ^ 2 := by
    rw [show (1.98 : ℝ) = (2 : ℕ) * 0.99 by norm_num, Real.exp_nat_mul]
  rw [h]
  calc Real.exp 0.99 ^ 2 ≤ (2.6914 : ℝ) ^ 2 := pow_le_pow_left₀ (Real.exp_pos _).le exp_099 2
    _ ≤ 7.244 := by norm_num

private lemma log_log_T_ge {T : ℝ} (hT : 1400 ≤ T) : 1.98 ≤ Real.log (Real.log T) :=
  (log_ge_of_exp_le (by norm_num : (0:ℝ) < 7.244) exp_198_le).trans
    (Real.log_le_log (by norm_num) (log_T_ge hT))

private lemma exp_1837 : Real.exp 0.1837 ≤ 1.20166 := by
  refine exp_le_rat (x := 0.1837) (c := 1.20166) (by norm_num) (by norm_num) (n := 18)
    (by norm_num) ?_
  norm_num [Finset.sum_range_succ, Nat.factorial]

private lemma pow_12017 : (1.20166 : ℝ) ^ 10 ≤ 6.2795 := by norm_num

private lemma log_two_pi_ge : 1.837 ≤ Real.log (2 * Real.pi) := by
  refine log_ge_of_exp_le (by have := Real.pi_pos; positivity) ?_
  have hpi : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have h2 : Real.exp (1.837 : ℝ) = Real.exp (0.1837 : ℝ) ^ 10 := by
    rw [show (1.837 : ℝ) = (10 : ℕ) * 0.1837 by norm_num, Real.exp_nat_mul]
  rw [h2]
  calc Real.exp 0.1837 ^ 10 ≤ (1.20166 : ℝ) ^ 10 :=
        pow_le_pow_left₀ (Real.exp_pos _).le exp_1837 10
    _ ≤ 6.2795 := pow_12017
    _ ≤ 2 * Real.pi := by nlinarith

/-! ## `log log (T+1.32) ≤ log log T + 0.00014` -/

private lemma log_one_add_le_div {T : ℝ} (hT : 1400 ≤ T) :
    Real.log (T + 1.32) ≤ Real.log T + 0.000943 := by
  have hT0 : (0:ℝ) < T := by linarith
  have h1 : Real.log (T + 1.32) = Real.log T + Real.log (1 + 1.32 / T) := by
    rw [← Real.log_mul hT0.ne' (by positivity)]
    congr 1
    field_simp
  rw [h1]
  have h2 : Real.log (1 + 1.32 / T) ≤ 1.32 / T := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < 1 + 1.32 / T by positivity)
    linarith
  have h3 : 1.32 / T ≤ 0.000943 := by
    rw [div_le_iff₀ hT0]; nlinarith
  linarith

private lemma loglog_shift_le {T : ℝ} (hT : 1400 ≤ T) :
    Real.log (Real.log (T + 1.32)) ≤ Real.log (Real.log T) + 0.00014 := by
  have hT0 : (0:ℝ) < T := by linarith
  have hlog := log_T_ge hT
  have h1 : Real.log (T + 1.32) ≤ Real.log T + 0.000943 := log_one_add_le_div hT
  have hLT : (0:ℝ) < Real.log (T + 1.32) := by
    have := Real.log_pos (by linarith : (1:ℝ) < T + 1.32)
    linarith
  have hB : (0:ℝ) < Real.log T := by linarith
  have hratio : Real.log (T + 1.32) / Real.log T ≤ Real.exp (0.000943 / Real.log T) := by
    rw [div_le_iff₀ hB]
    have h3 : 1 + 0.000943 / Real.log T ≤ Real.exp (0.000943 / Real.log T) := by
      have := Real.add_one_le_exp (0.000943 / Real.log T)
      linarith
    have h4 : Real.log (T + 1.32) ≤ Real.log T * (1 + 0.000943 / Real.log T) := by
      rw [mul_add, mul_one, mul_div_cancel₀ _ hB.ne']
      linarith
    exact h4.trans (by simpa [mul_comm] using mul_le_mul_of_nonneg_left h3 hB.le)
  have h2 : Real.log (Real.log (T + 1.32)) - Real.log (Real.log T) ≤ 0.000943 / Real.log T := by
    rw [← Real.log_div hLT.ne' hB.ne']
    calc Real.log (Real.log (T + 1.32) / Real.log T) ≤ Real.log (Real.exp (0.000943 / Real.log T)) :=
          Real.log_le_log (by positivity) hratio
      _ = 0.000943 / Real.log T := Real.log_exp _
  have h5 : 0.000943 / Real.log T ≤ 0.00014 := by
    rw [div_le_iff₀ hB]
    nlinarith
  linarith

/-! ## The third-branch constant and the `log ((T+1.32)/(2π))` bound -/

private lemma c3_le {T : ℝ} (hT : 1400 ≤ T) :
    Real.log ((T - 1.32) ^ 2 / ((T - 1.32) ^ 2 - 4)) ≤ 2.045e-6 := by
  have hd : (0:ℝ) < (T - 1.32) ^ 2 - 4 := by nlinarith
  have h1 : (T - 1.32) ^ 2 / ((T - 1.32) ^ 2 - 4) = 1 + 4 / ((T - 1.32) ^ 2 - 4) := by
    field_simp
    ring
  rw [h1, Real.log_le_iff_le_exp (by positivity)]
  have h2 : 1 + 4 / ((T - 1.32) ^ 2 - 4) ≤ Real.exp (2.045e-6 : ℝ) := by
    have h4 : 4 / ((T - 1.32) ^ 2 - 4) ≤ 2.045e-6 := by
      rw [div_le_iff₀ hd]
      nlinarith
    have h5 := Real.add_one_le_exp (2.045e-6 : ℝ)
    linarith
  exact h2

private lemma L_le {T : ℝ} (hT : 1400 ≤ T) :
    Real.log ((T + 1.32) / (2 * Real.pi)) ≤ Real.log T - 1.836 := by
  have hT0 : (0:ℝ) < T := by linarith
  rw [Real.log_div (by linarith) (by have := Real.pi_pos; positivity)]
  have h1 := log_one_add_le_div hT
  have h2 := log_two_pi_ge
  linarith

/-! ## Zeta values: `‖ζ(5/4)‖ ≤ 4.609` and `‖ζ(5/2)‖ ≥ 1.3406` -/

/-- Rational lower bound for `n ^ (-(p/k))`, from `c ^ k * n ^ p ≤ 1`. -/
private lemma rpow_rat_ge {n c : ℝ} (hn : 0 < n) {p k : ℕ} (hp : 0 < p) (hk : 0 < k) (hc : 0 < c)
    (h : c ^ k * n ^ p ≤ 1) : c ≤ n ^ (-((p : ℝ) / k)) := by
  rw [← neg_div]
  have hn0 : (0 : ℝ) ≤ n := le_of_lt hn
  have hc0 : (0 : ℝ) ≤ c := le_of_lt hc
  have hexp : (-(p : ℝ) / k) = (-(p : ℝ)) * (1 / (k : ℝ)) := by field_simp
  rw [hexp, Real.rpow_mul hn0]
  have key : c ^ (k : ℝ) ≤ n ^ (-(p : ℝ)) := by
    rw [Real.rpow_neg hn0, Real.rpow_natCast, Real.rpow_natCast, ← one_div,
      le_div_iff₀ (pow_pos hn p)]
    simpa only [mul_comm] using h
  calc c = (c ^ (k : ℝ)) ^ (1 / (k : ℝ)) := by
        rw [← Real.rpow_mul hc0, show (k : ℝ) * (1 / (k : ℝ)) = 1 by field_simp, Real.rpow_one]
    _ ≤ (n ^ (-(p : ℝ))) ^ (1 / (k : ℝ)) :=
        Real.rpow_le_rpow (Real.rpow_nonneg hc0 _) key (by positivity)

/-- `‖ζ(5/4)‖ ≤ 4.609`, from the Dirichlet series. -/
private lemma zeta_54_le : ‖riemannZeta (Complex.ofReal ((5:ℝ)/4))‖ ≤ 4.609 :=
  (zeta_norm_le_tsum ((5:ℝ)/4) (by norm_num)).trans zsum_54

/-- The real part of `ζ(5/2)` is the Dirichlet series. -/
private lemma zeta_re_52 : (riemannZeta (Complex.ofReal ((5:ℝ)/2))).re =
    ∑' n : ℕ, (n : ℝ) ^ (-((5:ℝ)/2)) := by
  have hp : Complex.ofReal ((5:ℝ)/2) = ((5:ℂ)/2) := by push_cast; ring
  have hre : 1 < (Complex.ofReal ((5:ℝ)/2)).re := by
    rw [hp]; norm_num
  have hsumm : Summable fun n : ℕ => (1:ℂ)/(n:ℂ)^(Complex.ofReal ((5:ℝ)/2)) :=
    Complex.summable_one_div_nat_cpow.mpr hre
  rw [zeta_eq_tsum_one_div_nat_cpow hre, Complex.re_tsum hsumm]
  refine tsum_congr (fun n => ?_)
  rcases Nat.eq_zero_or_pos n with hn | hn
  · subst hn
    have h0 : ((0:ℂ))^(Complex.ofReal ((5:ℝ)/2)) = 0 :=
      Complex.zero_cpow (x := Complex.ofReal ((5:ℝ)/2)) (by
        rw [Complex.ofReal_ne_zero]; norm_num)
    simp only [Nat.cast_zero, h0, div_zero, Complex.zero_re,
      Real.zero_rpow (x := -((5:ℝ)/2)) (by norm_num)]
  · have hn' : (0:ℝ) < (n:ℝ) := by exact_mod_cast hn
    have h1 : ((n:ℂ))^(Complex.ofReal ((5:ℝ)/2)) = Complex.ofReal ((n:ℝ)^((5:ℝ)/2)) := by
      have := (Complex.ofReal_cpow (x := (n:ℝ)) (le_of_lt hn') ((5:ℝ)/2)).symm
      simpa using this
    rw [h1, one_div, ← Complex.ofReal_inv, Complex.ofReal_re, Real.rpow_neg (le_of_lt hn')]

/-- `1.3406 ≤ ∑' n, n ^ (-(5/2))`, from twenty-one terms and the integral test. -/
private lemma zsum_52_ge : (1.3406:ℝ) ≤ ∑' n : ℕ, (n : ℝ) ^ (-((5:ℝ)/2)) := by
  have hsumm : Summable fun n : ℕ => (n:ℝ)^(-((5:ℝ)/2)) := Real.summable_nat_rpow.2 (by norm_num)
  have t2 : (0.176776:ℝ) ≤ (2:ℝ)^(-((5:ℝ)/2)) := by
    simpa using rpow_rat_ge (n := 2) (p := 5) (k := 2) (c := 0.176776) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t3 : (0.06415:ℝ) ≤ (3:ℝ)^(-((5:ℝ)/2)) := by
    simpa using rpow_rat_ge (n := 3) (p := 5) (k := 2) (c := 0.06415) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t4 : (0.03125:ℝ) ≤ (4:ℝ)^(-((5:ℝ)/2)) := by
    simpa using rpow_rat_ge (n := 4) (p := 5) (k := 2) (c := 0.03125) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t5 : (0.017888:ℝ) ≤ (5:ℝ)^(-((5:ℝ)/2)) := by
    simpa using rpow_rat_ge (n := 5) (p := 5) (k := 2) (c := 0.017888) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t6 : (0.01134:ℝ) ≤ (6:ℝ)^(-((5:ℝ)/2)) := by
    simpa using rpow_rat_ge (n := 6) (p := 5) (k := 2) (c := 0.01134) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t7 : (0.007713:ℝ) ≤ (7:ℝ)^(-((5:ℝ)/2)) := by
    simpa using rpow_rat_ge (n := 7) (p := 5) (k := 2) (c := 0.007713) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t8 : (0.005524:ℝ) ≤ (8:ℝ)^(-((5:ℝ)/2)) := by
    simpa using rpow_rat_ge (n := 8) (p := 5) (k := 2) (c := 0.005524) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t9 : (0.004115:ℝ) ≤ (9:ℝ)^(-((5:ℝ)/2)) := by
    simpa using rpow_rat_ge (n := 9) (p := 5) (k := 2) (c := 0.004115) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t10 : (0.003162:ℝ) ≤ (10:ℝ)^(-((5:ℝ)/2)) := by
    simpa using rpow_rat_ge (n := 10) (p := 5) (k := 2) (c := 0.003162) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t11 : (0.002491:ℝ) ≤ (11:ℝ)^(-((5:ℝ)/2)) := by
    simpa using rpow_rat_ge (n := 11) (p := 5) (k := 2) (c := 0.002491) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t12 : (0.002004:ℝ) ≤ (12:ℝ)^(-((5:ℝ)/2)) := by
    simpa using rpow_rat_ge (n := 12) (p := 5) (k := 2) (c := 0.002004) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t13 : (0.001641:ℝ) ≤ (13:ℝ)^(-((5:ℝ)/2)) := by
    simpa using rpow_rat_ge (n := 13) (p := 5) (k := 2) (c := 0.001641) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t14 : (0.001363:ℝ) ≤ (14:ℝ)^(-((5:ℝ)/2)) := by
    simpa using rpow_rat_ge (n := 14) (p := 5) (k := 2) (c := 0.001363) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t15 : (0.001147:ℝ) ≤ (15:ℝ)^(-((5:ℝ)/2)) := by
    simpa using rpow_rat_ge (n := 15) (p := 5) (k := 2) (c := 0.001147) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t16 : (0.000976:ℝ) ≤ (16:ℝ)^(-((5:ℝ)/2)) := by
    simpa using rpow_rat_ge (n := 16) (p := 5) (k := 2) (c := 0.000976) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t17 : (0.000839:ℝ) ≤ (17:ℝ)^(-((5:ℝ)/2)) := by
    simpa using rpow_rat_ge (n := 17) (p := 5) (k := 2) (c := 0.000839) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t18 : (0.000727:ℝ) ≤ (18:ℝ)^(-((5:ℝ)/2)) := by
    simpa using rpow_rat_ge (n := 18) (p := 5) (k := 2) (c := 0.000727) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t19 : (0.000635:ℝ) ≤ (19:ℝ)^(-((5:ℝ)/2)) := by
    simpa using rpow_rat_ge (n := 19) (p := 5) (k := 2) (c := 0.000635) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have t20 : (0.000559:ℝ) ≤ (20:ℝ)^(-((5:ℝ)/2)) := by
    simpa using rpow_rat_ge (n := 20) (p := 5) (k := 2) (c := 0.000559) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hS : (1.3343:ℝ) ≤ ∑ n ∈ Finset.range 21, (n:ℝ)^(-((5:ℝ)/2)) := by
    have z0 : (0:ℝ)^(-((5:ℝ)/2)) = 0 := Real.zero_rpow (x := -((5:ℝ)/2)) (by norm_num)
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.cast_zero, Nat.cast_one,
      Nat.cast_ofNat, z0, Real.one_rpow, zero_add]
    norm_num
    linarith
  have hanti : AntitoneOn (fun t : ℝ => t^(-((5:ℝ)/2))) (Set.Ici (21:ℝ)) := by
    intro x hx y hy hxy
    simp only [Set.mem_Ici] at hx hy
    have hx0 : (0:ℝ) < x := by linarith
    have hy0 : (0:ℝ) < y := by linarith
    have hxy' : x ^ ((5:ℝ)/2) ≤ y ^ ((5:ℝ)/2) :=
      Real.rpow_le_rpow hx0.le hxy (by norm_num)
    show y ^ (-((5:ℝ)/2)) ≤ x ^ (-((5:ℝ)/2))
    rw [Real.rpow_neg hx0.le, Real.rpow_neg hy0.le]
    simpa only [one_div] using one_div_le_one_div_of_le (by positivity : (0:ℝ) < x ^ ((5:ℝ)/2)) hxy'
  have hnn : ∀ t ∈ Set.Ioi (21:ℝ), 0 ≤ t^(-((5:ℝ)/2)) := by
    intro t ht
    simp only [Set.mem_Ioi] at ht
    exact Real.rpow_nonneg (by linarith) _
  have htail := AntitoneOn.integral_le_tsum_comp_add (f := fun t : ℝ => t^(-((5:ℝ)/2))) 21 hanti hsumm hnn
  have hval : (∫ x : ℝ in Set.Ioi (21:ℝ), x^(-((5:ℝ)/2))) = (2/3) * (21:ℝ)^(-((3:ℝ)/2)) := by
    rw [integral_Ioi_rpow_of_lt (a := -((5:ℝ)/2)) (by norm_num) (by norm_num : (0:ℝ) < 21)]
    rw [show (-((5:ℝ)/2) + 1) = -((3:ℝ)/2) by norm_num]
    field_simp
  have h21 : (0.010391:ℝ) ≤ (21:ℝ)^(-((3:ℝ)/2)) := by
    simpa using rpow_rat_ge (n := 21) (p := 3) (k := 2) (c := 0.010391) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have hsp := hsumm.sum_add_tsum_nat_add 21
  linarith [hsp, htail, hval, h21, hS]

/-- `1.3406 ≤ ‖ζ(5/2)‖`. -/
private lemma zeta_52_ge : (1.3406:ℝ) ≤ ‖riemannZeta (Complex.ofReal ((5:ℝ)/2))‖ := by
  have h1 : (1.3406:ℝ) ≤ (riemannZeta (Complex.ofReal ((5:ℝ)/2))).re := by
    rw [zeta_re_52]; exact zsum_52_ge
  exact h1.trans (Complex.re_le_norm _)

/-- `π/2 ≤ arccos (-(25/132))`. -/
private lemma arccos_neg_25_ge : π/2 ≤ Real.arccos ((-(25:ℝ))/132) := by
  rw [Real.arccos_eq_pi_div_two_sub_arcsin,
    show ((-(25:ℝ))/132) = -((25:ℝ)/132) by ring, Real.arcsin_neg]
  have h : (0:ℝ) ≤ Real.arcsin ((25:ℝ)/132) := (Real.arcsin_nonneg).mpr (by norm_num)
  linarith

private lemma loglog_nonneg {T : ℝ} (hT : 1400 ≤ T) : 0 ≤ Real.log (Real.log (T + 1.32)) := by
  apply Real.log_nonneg
  exact (by norm_num : (1:ℝ) ≤ 7.244).trans (log_T_ge (by linarith : 1400 ≤ T + 1.32))

private lemma loglog_ge_15284 {T : ℝ} (hT : 1400 ≤ T) : (1.5284:ℝ) ≤ Real.log (Real.log (T + 1.32)) := by
  have h1 : (1.5284:ℝ) ≤ Real.log (Real.log T) := (by norm_num : (1.5284:ℝ) ≤ 1.98).trans (log_log_T_ge hT)
  have h2 : (0:ℝ) < Real.log T := by linarith [log_T_ge hT]
  refine h1.trans (Real.log_le_log h2 ?_)
  exact Real.log_le_log (by linarith [hT]) (by linarith)

private lemma c3_nonneg {T : ℝ} (hT : 1400 ≤ T) :
    0 ≤ Real.log ((T - 1.32) ^ 2 / ((T - 1.32) ^ 2 - 4)) := by
  apply Real.log_nonneg
  have hd : (0:ℝ) < (T - 1.32) ^ 2 - 4 := by nlinarith
  rw [one_le_div hd]
  nlinarith

private lemma Lbranch_nonneg {T : ℝ} (hT : 1400 ≤ T) :
    0 ≤ Real.log ((T + 1.32) / (2 * Real.pi)) := by
  apply Real.log_nonneg
  rw [one_le_div (by have := Real.pi_pos; positivity)]
  nlinarith [Real.pi_lt_four]

private lemma sin_arccos_neg_25 : Real.sin (Real.arccos ((-(25:ℝ))/132)) = Real.sqrt (1 - (25/132)^2) := by
  rw [Real.sin_arccos]
  norm_num

private lemma sin_arccos_neg_125 : Real.sin (Real.arccos ((-(125:ℝ))/132)) = Real.sqrt (1 - (125/132)^2) := by
  rw [Real.sin_arccos]
  norm_num

private lemma arccos_neg_le_neg : Real.arccos ((-(25:ℝ))/132) ≤ Real.arccos ((-(125:ℝ))/132) := by
  apply Real.arccos_le_arccos
  norm_num

private lemma arccos_neg25_le_pi : Real.arccos ((-(25:ℝ))/132) ≤ π := Real.arccos_le_pi _

private lemma arccos_neg125_le_pi : Real.arccos ((-(125:ℝ))/132) ≤ π := Real.arccos_le_pi _

/-- Pointwise bound for the third branch on `[arccos (-(25/132)), arccos (-(125/132))]`. -/
private lemma piece3_pt {T : ℝ} (hT : 1400 ≤ T)
    {φ : ℝ} (hφ : φ ∈ Set.Icc (Real.arccos ((-(25:ℝ))/132)) (Real.arccos ((-(125:ℝ))/132))) :
    logEnvelope T φ ≤
      Real.log ((T - 1.32) ^ 2 / ((T - 1.32) ^ 2 - 4)) + Real.log (Real.log (T + 1.32)) +
        (1 - (5/4 + 1.32 * Real.cos φ)) / 2 * Real.log ((T + 1.32) / (2 * Real.pi)) := by
  obtain ⟨h1, h2⟩ := hφ
  have hcos_le : Real.cos φ ≤ -(25:ℝ)/132 := by
    have hc : Real.cos φ ≤ Real.cos (Real.arccos ((-(25:ℝ))/132)) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (x := Real.arccos ((-(25:ℝ))/132)) (y := φ)
        (Real.arccos_nonneg _) (by linarith [h2, arccos_neg125_le_pi]) h1
    rwa [Real.cos_arccos (by norm_num) (by norm_num)] at hc
  have hcos_ge : -(125:ℝ)/132 ≤ Real.cos φ := by
    have hc : Real.cos (Real.arccos ((-(125:ℝ))/132)) ≤ Real.cos φ :=
      Real.cos_le_cos_of_nonneg_of_le_pi (x := φ) (y := Real.arccos ((-(125:ℝ))/132))
        (by linarith [h1, arccos_neg_25_ge, Real.pi_pos]) arccos_neg125_le_pi h2
    rwa [Real.cos_arccos (by norm_num) (by norm_num)] at hc
  have hσle : 5/4 + 1.32 * Real.cos φ ≤ 1 := by nlinarith
  have hσ2 : ¬ ((5:ℝ)/4 ≤ 5/4 + 1.32 * Real.cos φ) := by
    intro h; linarith
  have hσ3 : (0:ℝ) ≤ 5/4 + 1.32 * Real.cos φ := by nlinarith
  unfold logEnvelope
  dsimp only
  rw [if_neg hσ2]
  by_cases hcase : (1:ℝ) ≤ 5/4 + 1.32 * Real.cos φ
  · rw [if_pos hcase]
    have hσeq : 5/4 + 1.32 * Real.cos φ = 1 := le_antisymm hσle hcase
    have hc3 := c3_nonneg hT
    rw [hσeq]
    linarith
  · rw [if_neg hcase, if_pos hσ3]
    linarith

/-- `∫_{φa}^{φb}` bound for the third branch. -/
private lemma piece3 {T : ℝ} (hT : 1400 ≤ T) :
    ∫ φ in (Real.arccos ((-(25:ℝ))/132))..(Real.arccos ((-(125:ℝ))/132)), logEnvelope T φ ≤
      (Real.arccos ((-(125:ℝ))/132) - Real.arccos ((-(25:ℝ))/132)) *
        (Real.log ((T - 1.32) ^ 2 / ((T - 1.32) ^ 2 - 4)) + Real.log (Real.log (T + 1.32))) +
      Real.log ((T + 1.32) / (2 * Real.pi)) *
        (-(Real.arccos ((-(125:ℝ))/132) - Real.arccos ((-(25:ℝ))/132)) / 8 +
          0.66 * (Real.sqrt (1 - (25/132)^2) - Real.sqrt (1 - (125/132)^2))) := by
  set a := Real.arccos ((-(25:ℝ))/132) with ha
  set b := Real.arccos ((-(125:ℝ))/132) with hb
  set c3 := Real.log ((T - 1.32) ^ 2 / ((T - 1.32) ^ 2 - 4)) with hc3
  set L2 := Real.log (Real.log (T + 1.32)) with hL2
  set L := Real.log ((T + 1.32) / (2 * Real.pi)) with hL
  have hab : a ≤ b := arccos_neg_le_neg
  have hInt1 : IntervalIntegrable (logEnvelope T) volume a b := by
    refine (logEnvelope_integrable T).mono_set ?_
    intro x hx
    simp only [Set.uIcc_of_le hab, Set.uIcc_of_le Real.pi_pos.le] at hx ⊢
    have ha0 : (0:ℝ) ≤ a := by rw [ha]; exact Real.arccos_nonneg _
    exact ⟨by linarith [hx.1, ha0], by linarith [hx.2, arccos_neg125_le_pi]⟩
  have hInt2 : IntervalIntegrable
      (fun φ : ℝ => c3 + L2 + ((1 - (5/4 + 1.32 * Real.cos φ)) / 2) * L) volume a b :=
    (by fun_prop : Continuous fun φ : ℝ => c3 + L2 + ((1 - (5/4 + 1.32 * Real.cos φ)) / 2) * L)
      |>.intervalIntegrable _ _
  have hmono : (∫ φ in a..b, logEnvelope T φ) ≤
      ∫ φ in a..b, (c3 + L2 + ((1 - (5/4 + 1.32 * Real.cos φ)) / 2) * L) := by
    apply intervalIntegral.integral_mono_on hab hInt1 hInt2
    intro φ hφ
    have := piece3_pt hT hφ
    simpa [ha, hb, hc3, hL2, hL] using this
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (fun y : ℝ => (c3 + L2) * y + (-(1/8)) * L * y - 0.66 * L * Real.sin y)
        (c3 + L2 + ((1 - (5/4 + 1.32 * Real.cos x)) / 2) * L) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => (c3 + L2) * y) (c3 + L2) x := by
      simpa using (hasDerivAt_id x).const_mul (c3 + L2)
    have h2 : HasDerivAt (fun y : ℝ => (-(1/8)) * L * y) ((-(1/8)) * L) x := by
      simpa using (hasDerivAt_id x).const_mul ((-(1/8)) * L)
    have h3 : HasDerivAt (fun y : ℝ => 0.66 * L * Real.sin y) (0.66 * L * Real.cos x) x :=
      (Real.hasDerivAt_sin x).const_mul (0.66 * L)
    have h4 := (h1.add h2).sub h3
    have heq : (c3 + L2) + (-(1/8)) * L - 0.66 * L * Real.cos x
        = c3 + L2 + ((1 - (5/4 + 1.32 * Real.cos x)) / 2) * L := by ring
    rw [heq] at h4
    exact h4
  have hval : (∫ φ in a..b, (c3 + L2 + ((1 - (5/4 + 1.32 * Real.cos φ)) / 2) * L)) =
      (c3 + L2) * (b - a) + (-(1/8)) * L * (b - a) - 0.66 * L * (Real.sin b - Real.sin a) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt2]
    ring
  rw [hval] at hmono
  have hsa : Real.sin a = Real.sqrt (1 - (25/132)^2) := by
    rw [ha]; exact sin_arccos_neg_25
  have hsb : Real.sin b = Real.sqrt (1 - (125/132)^2) := by
    rw [hb]; exact sin_arccos_neg_125
  rw [hsa, hsb] at hmono
  calc (∫ φ in a..b, logEnvelope T φ) ≤
        (c3 + L2) * (b - a) + (-(1/8)) * L * (b - a) -
          0.66 * L * (Real.sqrt (1 - (125/132)^2) - Real.sqrt (1 - (25/132)^2)) := hmono
    _ = (b - a) * (c3 + L2) + L * (-(b - a) / 8 + 0.66 * (Real.sqrt (1 - (25/132)^2) -
          Real.sqrt (1 - (125/132)^2))) := by ring

/-- Pointwise bound for the fourth branch on `[arccos (-(125/132)), π]`. -/
private lemma piece4_pt {T : ℝ} (hT : 1400 ≤ T)
    {φ : ℝ} (hφ : φ ∈ Set.Icc (Real.arccos ((-(125:ℝ))/132)) π) :
    logEnvelope T φ ≤
      Real.log ((T - 1.32) ^ 2 / ((T - 1.32) ^ 2 - 4)) + Real.log (Real.log (T + 1.32)) +
        (1/2 - (5/4 + 1.32 * Real.cos φ)) * Real.log ((T + 1.32) / (2 * Real.pi)) := by
  obtain ⟨h1, h2⟩ := hφ
  have hcos_le : Real.cos φ ≤ -(125:ℝ)/132 := by
    have hc : Real.cos φ ≤ Real.cos (Real.arccos ((-(125:ℝ))/132)) :=
      Real.cos_le_cos_of_nonneg_of_le_pi (x := Real.arccos ((-(125:ℝ))/132)) (y := φ)
        (Real.arccos_nonneg _) h2 h1
    rwa [Real.cos_arccos (by norm_num) (by norm_num)] at hc
  have hσle : 5/4 + 1.32 * Real.cos φ ≤ 0 := by nlinarith
  have hσ1 : ¬ ((5:ℝ)/4 ≤ 5/4 + 1.32 * Real.cos φ) := by
    intro h; linarith
  have hσ2 : ¬ ((1:ℝ) ≤ 5/4 + 1.32 * Real.cos φ) := by
    intro h; linarith
  unfold logEnvelope
  dsimp only
  rw [if_neg hσ1, if_neg hσ2]
  by_cases hcase : (0:ℝ) ≤ 5/4 + 1.32 * Real.cos φ
  · rw [if_pos hcase]
    have hσeq : 5/4 + 1.32 * Real.cos φ = 0 := le_antisymm hσle hcase
    have hc3 := c3_nonneg hT
    rw [hσeq]
    linarith
  · rw [if_neg hcase]
    have hc3 := c3_nonneg hT
    linarith

/-- `∫_{φb}^{π}` bound for the fourth branch. -/
private lemma piece4 {T : ℝ} (hT : 1400 ≤ T) :
    ∫ φ in (Real.arccos ((-(125:ℝ))/132))..π, logEnvelope T φ ≤
      (π - Real.arccos ((-(125:ℝ))/132)) *
        (Real.log ((T - 1.32) ^ 2 / ((T - 1.32) ^ 2 - 4)) + Real.log (Real.log (T + 1.32))) +
      Real.log ((T + 1.32) / (2 * Real.pi)) *
        (-(3/4) * (π - Real.arccos ((-(125:ℝ))/132)) + 1.32 * Real.sqrt (1 - (125/132)^2)) := by
  set b := Real.arccos ((-(125:ℝ))/132) with hb
  set c3 := Real.log ((T - 1.32) ^ 2 / ((T - 1.32) ^ 2 - 4)) with hc3
  set L2 := Real.log (Real.log (T + 1.32)) with hL2
  set L := Real.log ((T + 1.32) / (2 * Real.pi)) with hL
  have hbpi : b ≤ π := arccos_neg125_le_pi
  have hInt1 : IntervalIntegrable (logEnvelope T) volume b π := by
    refine (logEnvelope_integrable T).mono_set ?_
    intro x hx
    simp only [Set.uIcc_of_le hbpi, Set.uIcc_of_le Real.pi_pos.le] at hx ⊢
    have hb0 : (0:ℝ) ≤ b := by rw [hb]; exact Real.arccos_nonneg _
    exact ⟨by linarith [hx.1, hb0], hx.2⟩
  have hInt2 : IntervalIntegrable
      (fun φ : ℝ => c3 + L2 + (1/2 - (5/4 + 1.32 * Real.cos φ)) * L) volume b π :=
    (by fun_prop : Continuous fun φ : ℝ => c3 + L2 + (1/2 - (5/4 + 1.32 * Real.cos φ)) * L)
      |>.intervalIntegrable _ _
  have hmono : (∫ φ in b..π, logEnvelope T φ) ≤
      ∫ φ in b..π, (c3 + L2 + (1/2 - (5/4 + 1.32 * Real.cos φ)) * L) := by
    apply intervalIntegral.integral_mono_on hbpi hInt1 hInt2
    intro φ hφ
    have := piece4_pt hT hφ
    simpa [hb, hc3, hL2, hL] using this
  have hderiv : ∀ x ∈ Set.uIcc b π,
      HasDerivAt (fun y : ℝ => (c3 + L2) * y + (-(3/4)) * L * y - 1.32 * L * Real.sin y)
        (c3 + L2 + (1/2 - (5/4 + 1.32 * Real.cos x)) * L) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => (c3 + L2) * y) (c3 + L2) x := by
      simpa using (hasDerivAt_id x).const_mul (c3 + L2)
    have h2 : HasDerivAt (fun y : ℝ => (-(3/4)) * L * y) ((-(3/4)) * L) x := by
      simpa using (hasDerivAt_id x).const_mul ((-(3/4)) * L)
    have h3 : HasDerivAt (fun y : ℝ => 1.32 * L * Real.sin y) (1.32 * L * Real.cos x) x :=
      (Real.hasDerivAt_sin x).const_mul (1.32 * L)
    have h4 := (h1.add h2).sub h3
    have heq : (c3 + L2) + (-(3/4)) * L - 1.32 * L * Real.cos x
        = c3 + L2 + (1/2 - (5/4 + 1.32 * Real.cos x)) * L := by ring
    rw [heq] at h4
    exact h4
  have hval : (∫ φ in b..π, (c3 + L2 + (1/2 - (5/4 + 1.32 * Real.cos φ)) * L)) =
      (c3 + L2) * (π - b) + (-(3/4)) * L * (π - b) - 1.32 * L * (Real.sin π - Real.sin b) := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt2]
    ring
  rw [hval] at hmono
  have hsb : Real.sin b = Real.sqrt (1 - (125/132)^2) := by
    rw [hb]; exact sin_arccos_neg_125
  rw [hsb, Real.sin_pi] at hmono
  calc (∫ φ in b..π, logEnvelope T φ) ≤
        (c3 + L2) * (π - b) + (-(3/4)) * L * (π - b) - 1.32 * L * (0 - Real.sqrt (1 - (125/132)^2)) := hmono
    _ = (π - b) * (c3 + L2) + L * (-(3/4) * (π - b) + 1.32 * Real.sqrt (1 - (125/132)^2)) := by ring

/-- Pointwise comparison for the `arcsin` integrals, both directions. -/
private lemma arcsin_sandwich {x : ℝ} (hx0 : 0 ≤ x) (hx2 : x ≤ 1/2) :
    x + x ^ 3 / 6 ≤ Real.arcsin x ∧ Real.arcsin x ≤ x + x ^ 3 / 3 := by
  have hx1 : x < 1 := by linarith
  have hmem : ∀ t ∈ Set.uIcc (0:ℝ) x, t < 1 := by
    intro t ht
    simp only [Set.uIcc_of_le hx0, Set.mem_Icc] at ht
    linarith [ht.2]
  have hmem0 : ∀ t ∈ Set.uIcc (0:ℝ) x, -1 < t := by
    intro t ht
    simp only [Set.uIcc_of_le hx0, Set.mem_Icc] at ht
    linarith [ht.1]
  have hInt1 : IntervalIntegrable (fun t : ℝ => 1 / Real.sqrt (1 - t ^ 2)) volume 0 x := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.div continuousOn_const ?_ ?_
    · exact (Real.continuous_sqrt.comp (by fun_prop : Continuous fun t : ℝ => 1 - t ^ 2)).continuousOn
    · intro t ht
      exact ne_of_gt (Real.sqrt_pos.mpr (by nlinarith [hmem t ht, hmem0 t ht]))
  have hfund : (∫ t in (0:ℝ)..x, 1 / Real.sqrt (1 - t ^ 2)) = Real.arcsin x := by
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (f := Real.arcsin)
      (fun t ht => Real.hasDerivAt_arcsin (ne_of_gt (hmem0 t ht)) (ne_of_lt (hmem t ht))) hInt1, Real.arcsin_zero,
      sub_zero]
  constructor
  · have hInt2 : IntervalIntegrable (fun t : ℝ => 1 + t ^ 2 / 2) volume 0 x :=
      (by fun_prop : Continuous fun t : ℝ => 1 + t ^ 2 / 2).intervalIntegrable _ _
    have hmono : (∫ t in (0:ℝ)..x, (1 + t ^ 2 / 2)) ≤
        ∫ t in (0:ℝ)..x, 1 / Real.sqrt (1 - t ^ 2) := by
      apply intervalIntegral.integral_mono_on hx0 hInt2 hInt1
      intro t ht
      simp only [Set.uIcc_of_le hx0, Set.mem_Icc] at ht
      have ht1 : (0:ℝ) < 1 - t ^ 2 := by nlinarith [ht.2]
      have hu : (0:ℝ) < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr ht1
      have hkey : (1 + t ^ 2 / 2) * Real.sqrt (1 - t ^ 2) ≤ 1 := by
        have hsq : ((1 + t ^ 2 / 2) * Real.sqrt (1 - t ^ 2)) ^ 2 ≤ 1 ^ 2 := by
          rw [mul_pow, Real.sq_sqrt ht1.le]
          nlinarith [sq_nonneg t, sq_nonneg (t^2), sq_nonneg (t^3), sq_nonneg (t^4)]
        nlinarith [hsq, Real.sqrt_nonneg (1 - t ^ 2), ht1]
      exact (le_div_iff₀ hu).mpr hkey
    have hval : (∫ t in (0:ℝ)..x, (1 + t ^ 2 / 2)) = x + x ^ 3 / 6 := by
      have hderiv : ∀ y ∈ Set.uIcc (0:ℝ) x,
          HasDerivAt (fun y : ℝ => y + y ^ 3 / 6) (1 + y ^ 2 / 2) y := by
        intro y hy
        have h1 : HasDerivAt (fun y : ℝ => y) 1 y := hasDerivAt_id y
        have h2 : HasDerivAt (fun y : ℝ => y ^ 3 / 6) (y ^ 2 / 2) y := by
          have := hasDerivAt_pow 3 y
          have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 6) ((3 : ℕ) * y ^ 2 / 6) y := this.div_const 6
          convert h3 using 1
          ring
        exact h1.add h2
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt2]
      norm_num
    rw [← hfund, ← hval]
    exact hmono
  · have hInt2 : IntervalIntegrable (fun t : ℝ => 1 + t ^ 2) volume 0 x :=
      (by fun_prop : Continuous fun t : ℝ => 1 + t ^ 2).intervalIntegrable _ _
    have hmono : (∫ t in (0:ℝ)..x, 1 / Real.sqrt (1 - t ^ 2)) ≤
        ∫ t in (0:ℝ)..x, (1 + t ^ 2) := by
      apply intervalIntegral.integral_mono_on hx0 hInt1 hInt2
      intro t ht
      simp only [Set.uIcc_of_le hx0, Set.mem_Icc] at ht
      have ht1 : (0:ℝ) < 1 - t ^ 2 := by nlinarith [ht.2]
      have hu : (0:ℝ) < Real.sqrt (1 - t ^ 2) := Real.sqrt_pos.mpr ht1
      have hkey : 1 ≤ (1 + t ^ 2) * Real.sqrt (1 - t ^ 2) := by
        have hp : (0:ℝ) ≤ (1 + t ^ 2) * Real.sqrt (1 - t ^ 2) := by positivity
        have ht2 : t ^ 2 ≤ 1/4 := by nlinarith [ht.2, hx2, sq_nonneg t]
        have ht4 : t ^ 4 ≤ 1/16 := by nlinarith [ht2, sq_nonneg t]
        have hfac : (1 + t ^ 2) ^ 2 * (1 - t ^ 2) = 1 + t ^ 2 * (1 - t ^ 2 - t ^ 4) := by ring
        have hsq : (1:ℝ) ^ 2 ≤ ((1 + t ^ 2) * Real.sqrt (1 - t ^ 2)) ^ 2 := by
          rw [mul_pow, Real.sq_sqrt ht1.le, hfac]
          have h2 : (0:ℝ) ≤ 1 - t ^ 2 - t ^ 4 := by linarith
          have h3 := mul_nonneg (sq_nonneg t) h2
          linarith
        nlinarith [hsq, hp]
      exact (div_le_iff₀ hu).mpr (by linarith)
    have hval : (∫ t in (0:ℝ)..x, (1 + t ^ 2)) = x + x ^ 3 / 3 := by
      have hderiv : ∀ y ∈ Set.uIcc (0:ℝ) x,
          HasDerivAt (fun y : ℝ => y + y ^ 3 / 3) (1 + y ^ 2) y := by
        intro y hy
        have h1 : HasDerivAt (fun y : ℝ => y) 1 y := hasDerivAt_id y
        have h2 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (y ^ 2) y := by
          have := hasDerivAt_pow 3 y
          have h3 : HasDerivAt (fun y : ℝ => y ^ 3 / 3) ((3 : ℕ) * y ^ 2 / 3) y := this.div_const 3
          convert h3 using 1
          ring
        exact h1.add h2
      rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hInt2]
      norm_num
    rw [← hfund, ← hval]
    exact hmono

private lemma sqrt_sa_le : Real.sqrt (1 - ((25:ℝ)/132)^2) ≤ 0.98191 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

private lemma sqrt_sb_le : Real.sqrt (1 - ((125:ℝ)/132)^2) ≤ 0.32133 := by
  rw [Real.sqrt_le_left (by norm_num)]
  norm_num

/-- `ℓ₂ ≤ 0.19167`: the length of the second piece. -/
private lemma len2_le : Real.arccos ((-(25:ℝ))/132) - π/2 ≤ 0.19167 := by
  have h1 : Real.arccos ((-(25:ℝ))/132) = π/2 + Real.arcsin ((25:ℝ)/132) := by
    rw [show ((-(25:ℝ))/132) = -((25:ℝ)/132) by ring, Real.arccos_neg,
      Real.arccos_eq_pi_div_two_sub_arcsin]
    ring
  rw [h1]
  have h2 := (arcsin_sandwich (x := (25:ℝ)/132) (by norm_num) (by norm_num)).2
  have h3 : (25:ℝ)/132 + ((25:ℝ)/132)^3/3 ≤ 0.19167 := by norm_num
  linarith

/-- `ℓ₄ ≥ 0.3268`: the length of the fourth piece. -/
private lemma len4_ge : (0.3268:ℝ) ≤ π - Real.arccos ((-(125:ℝ))/132) := by
  have h1 : Real.arccos ((-(125:ℝ))/132) = π - Real.arccos ((125:ℝ)/132) := by
    rw [show ((-(125:ℝ))/132) = -((125:ℝ)/132) by ring, Real.arccos_neg]
  rw [h1]
  have hπ : π - (π - Real.arccos ((125:ℝ)/132)) = Real.arccos ((125:ℝ)/132) := by ring
  rw [hπ]
  have h2 : Real.arccos ((125:ℝ)/132) = Real.arcsin (Real.sqrt (1 - ((125:ℝ)/132)^2)) :=
    Real.arccos_eq_arcsin (by norm_num)
  rw [h2]
  have hsb0 : (0:ℝ) ≤ Real.sqrt (1 - ((125:ℝ)/132)^2) := Real.sqrt_nonneg _
  have hsbl : (0.32132:ℝ) ≤ Real.sqrt (1 - ((125:ℝ)/132)^2) := by
    rw [Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hsb1 : Real.sqrt (1 - ((125:ℝ)/132)^2) < 1 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hsb2 : Real.sqrt (1 - ((125:ℝ)/132)^2) ≤ 1/2 := by
    have h := sqrt_sb_le
    linarith
  have h3 := (arcsin_sandwich hsb0 hsb2).1
  have h4 : (0.32132:ℝ) + (0.32132)^3/6 ≤
      Real.sqrt (1 - ((125:ℝ)/132)^2) + (Real.sqrt (1 - ((125:ℝ)/132)^2))^3/6 := by
    have h5 : (0.32132:ℝ)^3/6 ≤ (Real.sqrt (1 - ((125:ℝ)/132)^2))^3/6 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact pow_le_pow_left₀ (by norm_num) hsbl 3
    linarith
  have h6 : (0.3268:ℝ) ≤ 0.32132 + (0.32132)^3/6 := by norm_num
  linarith

/-- `log 4.609 ≤ 1.5284`. -/
private lemma log_4609 : Real.log 4.609 ≤ 1.5284 := by
  rw [Real.log_le_iff_le_exp (by norm_num)]
  have h1 : (4.609:ℝ) ≤ (2.147:ℝ)^2 := by norm_num
  have h2 : (2.147:ℝ)^2 ≤ (Real.exp 0.7642)^2 := by
    apply pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 2.147)
    calc (2.147:ℝ) ≤ ∑ m ∈ Finset.range 10, (0.7642:ℝ)^m / (m.factorial:ℝ) := by
          norm_num [Finset.sum_range_succ, Nat.factorial]
      _ ≤ Real.exp 0.7642 := Real.sum_le_exp_of_nonneg (by norm_num) 10
  have h3 : (Real.exp 0.7642)^2 = Real.exp 1.5284 := by
    rw [show (1.5284:ℝ) = (2:ℕ)*0.7642 by norm_num, Real.exp_nat_mul]
  calc (4.609:ℝ) ≤ (2.147:ℝ)^2 := h1
    _ ≤ (Real.exp 0.7642)^2 := h2
    _ = Real.exp 1.5284 := h3

/-- Pointwise bound on the second branch, on `[π/2, arccos (-(25/132))]`. -/
private lemma piece2_pt {T : ℝ} (hT : 1400 ≤ T)
    (hz54 : ‖riemannZeta (Complex.ofReal ((5:ℝ)/4))‖ ≤ 4.609)
    {φ : ℝ} (hφ : φ ∈ Set.Icc (π/2) (Real.arccos ((-(25:ℝ))/132))) :
    logEnvelope T φ ≤ Real.log (Real.log (T + 1.32)) := by
  obtain ⟨h1, h2⟩ := hφ
  have hcos_ge : -(25:ℝ)/132 ≤ Real.cos φ := by
    have hc : Real.cos (Real.arccos ((-(25:ℝ))/132)) ≤ Real.cos φ :=
      Real.cos_le_cos_of_nonneg_of_le_pi (x := φ) (y := Real.arccos ((-(25:ℝ))/132))
        (by linarith [Real.pi_pos]) arccos_neg25_le_pi h2
    rwa [Real.cos_arccos (by norm_num) (by norm_num)] at hc
  by_cases heq : φ = π/2
  · subst heq
    have hσ : (5:ℝ)/4 ≤ 5/4 + 1.32 * Real.cos (π/2) := by
      rw [Real.cos_pi_div_two]; norm_num
    have hcos0 : Real.cos (π/2) = 0 := Real.cos_pi_div_two
    unfold logEnvelope
    dsimp only
    rw [if_pos hσ, hcos0]
    have hmax : max ((5:ℝ)/4) (5/4 + 1.32 * 0) = 5/4 := by norm_num
    rw [hmax]
    exact ((Real.log_le_log (by norm_num) (max_le (by norm_num) hz54)).trans log_4609).trans
      (loglog_ge_15284 hT)
  · have hlt : π/2 < φ := lt_of_le_of_ne h1 (Ne.symm heq)
    have hcos_lt : Real.cos φ < 0 := Real.cos_neg_of_pi_div_two_lt_of_lt hlt (by linarith [h2, arccos_neg25_le_pi])
    have hσ1 : (1:ℝ) ≤ 5/4 + 1.32 * Real.cos φ := by nlinarith
    have hσ2 : ¬ ((5:ℝ)/4 ≤ 5/4 + 1.32 * Real.cos φ) := by
      intro h; linarith
    unfold logEnvelope
    dsimp only
    rw [if_neg hσ2, if_pos hσ1]

/-- `∫_{π/2}^{arccos (-(25/132))}` bound for the second branch. -/
private lemma piece2 {T : ℝ} (hT : 1400 ≤ T)
    (hz54 : ‖riemannZeta (Complex.ofReal ((5:ℝ)/4))‖ ≤ 4.609) :
    ∫ φ in (π/2)..(Real.arccos ((-(25:ℝ))/132)), logEnvelope T φ ≤
      (Real.arccos ((-(25:ℝ))/132) - π/2) * Real.log (Real.log (T + 1.32)) := by
  have hle : π/2 ≤ Real.arccos ((-(25:ℝ))/132) := arccos_neg_25_ge
  have hInt1 : IntervalIntegrable (logEnvelope T) volume (π/2) (Real.arccos ((-(25:ℝ))/132)) := by
    refine (logEnvelope_integrable T).mono_set ?_
    intro x hx
    simp only [Set.uIcc_of_le hle, Set.uIcc_of_le Real.pi_pos.le] at hx ⊢
    exact ⟨by linarith [hx.1, Real.pi_pos], by linarith [hx.2, arccos_neg25_le_pi]⟩
  have hInt2 : IntervalIntegrable (fun _ : ℝ => Real.log (Real.log (T + 1.32)))
      volume (π/2) (Real.arccos ((-(25:ℝ))/132)) := intervalIntegrable_const
  have h := intervalIntegral.integral_mono_on hle hInt1 hInt2 (fun φ hφ => piece2_pt hT hz54 hφ)
  rw [intervalIntegral.integral_const] at h
  simpa using h

/-- `log (1.3406 / 4.609) ≥ -1.2351`. -/
private lemma log_ratio_ge : (-1.2351:ℝ) ≤ Real.log (1.3406 / 4.609) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have hexp : (3.4386:ℝ) ≤ Real.exp 1.2351 := by
    refine (by norm_num : (3.4386:ℝ) ≤ ∑ m ∈ Finset.range 15,
      (1.2351:ℝ)^m / (m.factorial:ℝ)).trans ?_
    exact Real.sum_le_exp_of_nonneg (by norm_num) 15
  rw [Real.exp_neg, inv_eq_one_div]
  exact (one_div_le_one_div_of_le (by norm_num : (0:ℝ) < 3.4386) hexp).trans (by norm_num)

/-- `217/(48 π T) ≤ 0.001028` for `T ≥ 1400`. -/
private lemma tail_ge {T : ℝ} (hT : 1400 ≤ T) : 217 / (48 * Real.pi * T) ≤ 0.001028 := by
  have hπ : (3.141592:ℝ) < Real.pi := Real.pi_gt_d6
  have hT0 : (0:ℝ) < T := by linarith
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hπ, hT0]

/-- The core inequality of `envelope_budget`: the integral and gamma budget against the
right-hand side, conditional on the branch-one bound and the two zeta values. -/
private lemma envelope_core {T : ℝ} (hT : 1400 ≤ T)
    (hI1 : ∫ φ in (0:ℝ)..(π/2), logEnvelope T φ ≤ 0.8809)
    (hz54 : ‖riemannZeta (Complex.ofReal ((5:ℝ)/4))‖ ≤ 4.609)
    (hz25 : (1.3406:ℝ) ≤ ‖riemannZeta (Complex.ofReal ((5:ℝ)/2))‖) :
    (∫ φ in (0:ℝ)..π, logEnvelope T φ) / (2 * Real.pi * Real.log (4 * 1.32 / 3)) +
      1/2 + 217/(48*Real.pi*T) ≤
      0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 +
        Real.log ‖riemannZeta (Complex.ofReal ((5:ℝ)/2)) /
          riemannZeta (Complex.ofReal ((5:ℝ)/4))‖ / (2 * Real.log (4 * 1.32 / 3)) := by
  set a := Real.arccos ((-(25:ℝ))/132) with ha
  set b := Real.arccos ((-(125:ℝ))/132) with hb
  set L2 := Real.log (Real.log (T + 1.32)) with hL2
  set c3 := Real.log ((T - 1.32) ^ 2 / ((T - 1.32) ^ 2 - 4)) with hc3
  set L := Real.log ((T + 1.32) / (2 * Real.pi)) with hL
  set sa := Real.sqrt (1 - (25/132)^2) with hsa
  set sb := Real.sqrt (1 - (125/132)^2) with hsb
  have hmid : π/2 ≤ a := arccos_neg_25_ge
  have hab : a ≤ b := arccos_neg_le_neg
  have hbpi : b ≤ π := arccos_neg125_le_pi
  have hI0 : IntervalIntegrable (logEnvelope T) volume (0:ℝ) π := logEnvelope_integrable T
  have hint : ∀ u v : ℝ, 0 ≤ u → v ≤ π → u ≤ v →
      IntervalIntegrable (logEnvelope T) volume u v := by
    intro u v hu hv huv
    refine hI0.mono_set ?_
    intro x hx
    simp only [Set.uIcc_of_le huv, Set.uIcc_of_le Real.pi_pos.le] at hx ⊢
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have e1 : (∫ φ in (0:ℝ)..(π/2), logEnvelope T φ) + ∫ φ in (π/2)..π, logEnvelope T φ
      = ∫ φ in (0:ℝ)..π, logEnvelope T φ :=
    intervalIntegral.integral_add_adjacent_intervals
      (hint 0 (π/2) le_rfl (by linarith [Real.pi_pos]) (by linarith [Real.pi_pos]))
      (hint (π/2) π (by linarith [Real.pi_pos]) le_rfl (by linarith [Real.pi_pos]))
  have e2 : (∫ φ in (π/2)..a, logEnvelope T φ) + ∫ φ in a..π, logEnvelope T φ
      = ∫ φ in (π/2)..π, logEnvelope T φ :=
    intervalIntegral.integral_add_adjacent_intervals
      (hint (π/2) a (by linarith [Real.pi_pos]) (by linarith [hab, hbpi]) hmid)
      (hint a π (by linarith [hmid, Real.pi_pos]) le_rfl (by linarith [hab, hbpi]))
  have e3 : (∫ φ in a..b, logEnvelope T φ) + ∫ φ in b..π, logEnvelope T φ
      = ∫ φ in a..π, logEnvelope T φ :=
    intervalIntegral.integral_add_adjacent_intervals
      (hint a b (by linarith [hmid, Real.pi_pos]) (by linarith [hbpi]) hab)
      (hint b π (by linarith [hmid, hab, Real.pi_pos]) le_rfl hbpi)
  have p2 : (∫ φ in (π/2)..a, logEnvelope T φ) ≤ (a - π/2) * L2 := by
    simpa [ha, hL2] using piece2 hT hz54
  have p3 : (∫ φ in a..b, logEnvelope T φ) ≤
      (b - a) * (c3 + L2) + L * (-(b - a) / 8 + 0.66 * (sa - sb)) := by
    have h := piece3 hT
    rw [← ha, ← hb, ← hc3, ← hL2, ← hL] at h
    have hsa' : Real.sqrt (1 - (25/132)^2) = sa := hsa.symm
    have hsb' : Real.sqrt (1 - (125/132)^2) = sb := hsb.symm
    rw [hsa', hsb'] at h
    exact h
  have p4 : (∫ φ in b..π, logEnvelope T φ) ≤
      (π - b) * (c3 + L2) + L * (-(3/4) * (π - b) + 1.32 * sb) := by
    have h := piece4 hT
    rw [← hb, ← hc3, ← hL2, ← hL] at h
    have hsb' : Real.sqrt (1 - (125/132)^2) = sb := hsb.symm
    rw [hsb'] at h
    exact h
  have hL2b : L2 ≤ Real.log (Real.log T) + 0.00014 := by
    rw [hL2]; exact loglog_shift_le hT
  have hc3b : c3 ≤ 2.045e-6 := by rw [hc3]; exact c3_le hT
  have hLb : L ≤ Real.log T - 1.836 := by rw [hL]; exact L_le hT
  have hℓ2 : a - π/2 ≤ 0.19167 := by rw [ha]; exact len2_le
  have hℓ4 : (0.3268:ℝ) ≤ π - b := by rw [hb]; exact len4_ge
  have hsa' : sa ≤ 0.98191 := by rw [hsa]; exact sqrt_sa_le
  have hsb' : sb ≤ 0.32133 := by rw [hsb]; exact sqrt_sb_le
  have hc3nn : (0:ℝ) ≤ c3 := by rw [hc3]; exact c3_nonneg hT
  have hLnn : (0:ℝ) ≤ L := by rw [hL]; exact Lbranch_nonneg hT
  have hL2nn : (0:ℝ) ≤ L2 := by rw [hL2]; exact loglog_nonneg hT
  have hπ : (3.141592:ℝ) < π := Real.pi_gt_d6
  have hπu : π ≤ 3.141593 := le_of_lt Real.pi_lt_d6
  have hLT : (7.244:ℝ) ≤ Real.log T := log_T_ge hT
  have hLLT : (1.98:ℝ) ≤ Real.log (Real.log T) := log_log_T_ge hT
  have hstep1 : (∫ φ in (0:ℝ)..π, logEnvelope T φ) ≤ 0.8809 +
      ((a - π/2) * L2 + ((b - a) * (c3 + L2) + L * (-(b - a) / 8 + 0.66 * (sa - sb))) +
        ((π - b) * (c3 + L2) + L * (-(3/4) * (π - b) + 1.32 * sb))) := by
    linarith [e1, e2, e3, hI1, p2, p3, p4]
  have hcoef : -(b - a) / 8 + 0.66 * (sa - sb) + (-(3/4) * (π - b) + 1.32 * sb) ≤ 0.48353 := by
    linarith [hℓ2, hℓ4, hsa', hsb', hπ, hπu, hab, hmid]
  have hLin : L * (-(b - a) / 8 + 0.66 * (sa - sb) + (-(3/4) * (π - b) + 1.32 * sb))
      ≤ 0.48353 * L := by
    calc L * (-(b - a) / 8 + 0.66 * (sa - sb) + (-(3/4) * (π - b) + 1.32 * sb))
        ≤ L * 0.48353 := by
          apply mul_le_mul_of_nonneg_left hcoef hLnn
      _ = 0.48353 * L := by ring
  have hfrac : (π - a) * c3 ≤ 1.570797 * 2.045e-6 := by
    have h1 : π - a ≤ 1.570797 := by linarith [hmid, hπu]
    have h2 : (0:ℝ) ≤ π - a := by linarith [hmid, Real.pi_pos]
    calc (π - a) * c3 ≤ 1.570797 * c3 := by
          apply mul_le_mul_of_nonneg_right h1 hc3nn
      _ ≤ 1.570797 * 2.045e-6 := by
          apply mul_le_mul_of_nonneg_left hc3b (by norm_num)
  have hB : (∫ φ in (0:ℝ)..π, logEnvelope T φ) ≤
      0.8809 + 1.570797 * Real.log (Real.log T) + 0.0002232 + 0.48353 * (Real.log T - 1.836) := by
    have hkey : ((a - π/2) * L2 + ((b - a) * (c3 + L2) + L * (-(b - a) / 8 + 0.66 * (sa - sb))) +
        ((π - b) * (c3 + L2) + L * (-(3/4) * (π - b) + 1.32 * sb)))
        = (π/2) * L2 + (π - a) * c3 +
          L * (-(b - a) / 8 + 0.66 * (sa - sb) + (-(3/4) * (π - b) + 1.32 * sb)) := by ring
    rw [hkey] at hstep1
    have h1 : (π/2) * L2 ≤ 1.570797 * (Real.log (Real.log T) + 0.00014) := by
      calc (π/2) * L2 ≤ 1.570797 * L2 := by
            apply mul_le_mul_of_nonneg_right (by linarith [hπu]) hL2nn
        _ ≤ 1.570797 * (Real.log (Real.log T) + 0.00014) := by
            apply mul_le_mul_of_nonneg_left hL2b (by norm_num)
    linarith [hstep1, h1, hLin, hfrac]
  have hBnn : (0:ℝ) ≤ 0.8809 + 1.570797 * Real.log (Real.log T) + 0.0002232 +
      0.48353 * (Real.log T - 1.836) := by linarith [hLT, hLLT]
  have hden : (0:ℝ) < 2 * Real.pi * Real.log (4 * 1.32 / 3) := by
    have h1 := Real.pi_pos
    have h2 : (0:ℝ) < Real.log (4 * 1.32 / 3) := Real.log_pos (by norm_num)
    positivity
  have hinv_le : (2 * Real.pi * Real.log (4 * 1.32 / 3))⁻¹ ≤ 0.28154 := by
    rw [inv_eq_one_div]
    exact s_hi
  have hBC : (0.8809 + 1.570797 * Real.log (Real.log T) + 0.0002232 +
      0.48353 * (Real.log T - 1.836)) * 0.28154 ≤
      0.248009 + 0.442243 * Real.log (Real.log T) + 0.0000629 +
        0.136134 * Real.log T - 0.249943 := by
    have hLLT0 : (0:ℝ) ≤ Real.log (Real.log T) := by linarith
    have hLT0 : (0:ℝ) ≤ Real.log T - 1.836 := by linarith
    have hexp : (0.8809 + 1.570797 * Real.log (Real.log T) + 0.0002232 +
        0.48353 * (Real.log T - 1.836)) * 0.28154 =
        0.28154 * 0.8809 + (0.28154 * 1.570797) * Real.log (Real.log T) +
          0.28154 * 0.0002232 + (0.28154 * 0.48353) * (Real.log T - 1.836) := by ring
    have step1 : ((0.28154:ℝ) * 1.570797) * Real.log (Real.log T) ≤ 0.442243 * Real.log (Real.log T) :=
      mul_le_mul_of_nonneg_right (by norm_num : (0.28154:ℝ) * 1.570797 ≤ 0.442243) hLLT0
    have step2 : ((0.28154:ℝ) * 0.48353) * (Real.log T - 1.836) ≤ 0.136134 * (Real.log T - 1.836) :=
      mul_le_mul_of_nonneg_right (by norm_num : (0.28154:ℝ) * 0.48353 ≤ 0.136134) hLT0
    have c1 : (0.28154:ℝ) * 0.8809 ≤ 0.248009 := by norm_num
    have c3 : (0.28154:ℝ) * 0.0002232 ≤ 0.0000629 := by norm_num
    have c5 : (0.136134:ℝ) * 1.836 ≤ 0.249943 := by norm_num
    rw [hexp]
    linarith [step1, step2, c1, c3, c5]
  have hdiv : (∫ φ in (0:ℝ)..π, logEnvelope T φ) / (2 * Real.pi * Real.log (4 * 1.32 / 3))
      ≤ 0.248009 + 0.442243 * Real.log (Real.log T) + 0.0000629 +
        0.136134 * Real.log T - 0.249943 := by
    rw [div_eq_mul_inv]
    exact ((mul_le_mul_of_nonneg_right hB (inv_nonneg.mpr hden.le)).trans
      (mul_le_mul_of_nonneg_left hinv_le hBnn)).trans hBC
  have htail : 217 / (48 * Real.pi * T) ≤ 0.001028 := tail_ge hT
  have hzl : (-1.09244:ℝ) ≤ Real.log ‖riemannZeta (Complex.ofReal ((5:ℝ)/2)) /
      riemannZeta (Complex.ofReal ((5:ℝ)/4))‖ / (2 * Real.log (4 * 1.32 / 3)) := by
    have hz54pos : (0:ℝ) < ‖riemannZeta (Complex.ofReal ((5:ℝ)/4))‖ :=
      norm_pos_iff.mpr (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
    have hlt1 : (1.3406:ℝ) / 4.609 ≤ ‖riemannZeta (Complex.ofReal ((5:ℝ)/2)) /
        riemannZeta (Complex.ofReal ((5:ℝ)/4))‖ := by
      rw [norm_div]
      have h1 : (1.3406:ℝ) / ‖riemannZeta (Complex.ofReal ((5:ℝ)/4))‖ ≤
          ‖riemannZeta (Complex.ofReal ((5:ℝ)/2))‖ /
            ‖riemannZeta (Complex.ofReal ((5:ℝ)/4))‖ :=
        div_le_div_of_nonneg_right hz25 hz54pos.le
      have h2 : (1.3406:ℝ) / 4.609 ≤ 1.3406 / ‖riemannZeta (Complex.ofReal ((5:ℝ)/4))‖ :=
        div_le_div_of_nonneg_left (by norm_num) hz54pos hz54
      linarith
    have hlog : (-1.2351:ℝ) ≤ Real.log ‖riemannZeta (Complex.ofReal ((5:ℝ)/2)) /
        riemannZeta (Complex.ofReal ((5:ℝ)/4))‖ := by
      refine log_ratio_ge.trans (Real.log_le_log (by norm_num) hlt1)
    have h2q : (1.13062:ℝ) ≤ 2 * Real.log (4 * 1.32 / 3) := by
      have := q_lo'
      linarith
    have h2qp : (0:ℝ) < 2 * Real.log (4 * 1.32 / 3) := by linarith
    have hmono : (-1.2351:ℝ) / (2 * Real.log (4 * 1.32 / 3)) ≤
        Real.log ‖riemannZeta (Complex.ofReal ((5:ℝ)/2)) /
          riemannZeta (Complex.ofReal ((5:ℝ)/4))‖ / (2 * Real.log (4 * 1.32 / 3)) :=
      div_le_div_of_nonneg_right hlog h2qp.le
    have hQ : (1.2351:ℝ) / (2 * Real.log (4 * 1.32 / 3)) ≤ 1.2351 / 1.13062 :=
      div_le_div_of_nonneg_left (by norm_num) (by norm_num : (0:ℝ) < 1.13062) h2q
    have hA : (1.2351:ℝ) / (2 * Real.log (4 * 1.32 / 3)) ≤ 1.09244 :=
      hQ.trans (by norm_num)
    have hmono2 : -(1.2351 / (2 * Real.log (4 * 1.32 / 3))) ≤
        Real.log ‖riemannZeta (Complex.ofReal ((5:ℝ)/2)) /
          riemannZeta (Complex.ofReal ((5:ℝ)/4))‖ / (2 * Real.log (4 * 1.32 / 3)) := by
      have he : (-1.2351:ℝ) / (2 * Real.log (4 * 1.32 / 3)) =
          -(1.2351 / (2 * Real.log (4 * 1.32 / 3))) := by ring
      rwa [he] at hmono
    linarith only [hmono2, hA]
  have key1 : (∫ φ in (0:ℝ)..π, logEnvelope T φ) / (2 * Real.pi * Real.log (4 * 1.32 / 3)) +
      1/2 + 217/(48*Real.pi*T) ≤
      0.248009 + 0.442243 * Real.log (Real.log T) + 0.0000629 + 0.136134 * Real.log T -
        0.249943 + 1/2 + 0.001028 := by
    linarith only [hdiv, htail]
  have key2 : (0.248009 + 0.442243 * Real.log (Real.log T) + 0.0000629 +
      0.136134 * Real.log T - 0.249943 + 1/2 + 0.001028 : ℝ) ≤
      0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 +
        Real.log ‖riemannZeta (Complex.ofReal ((5:ℝ)/2)) /
          riemannZeta (Complex.ofReal ((5:ℝ)/4))‖ / (2 * Real.log (4 * 1.32 / 3)) := by
    linarith only [hzl, hLT, hLLT]
  linarith only [key1, key2]



/-- LEAF. Rosser p. 224, the bounds on G from Backlund pp. 361 to 369.
Backlund display 54 bounds the right strip, display 56 the critical strip,
and display 77 the short left strip. The Dirichlet series bounds the far right.
The two heights are bounded separately by T plus the radius. -/
theorem zeta_circle_bound (T φ : ℝ) (hT : 1400 ≤ T) (hφ : φ ∈ Set.Icc (0 : ℝ) π) :
    ‖riemannZeta ((1.32 : ℂ) * Complex.exp (φ * I) + 5 / 4 + T * I)‖ ≤
      Real.exp (logEnvelope T φ) ∧
    ‖riemannZeta ((1.32 : ℂ) * Complex.exp (φ * I) + 5 / 4 - T * I)‖ ≤
      Real.exp (logEnvelope T φ) := by
  sorry

/-- LEAF. Backlund p. 374, the three final gamma remainder estimates.
Their sum is 1 over 3T plus 1 over 16T plus 1 over 8T, equal to 25 over 48T.
The gamma argument has the same continuous normalization as Rosser p. 224. -/
theorem gamma_remainder_bound (T : ℝ) (hT : 1400 ≤ T) :
    |gammaRemainder T| ≤ 25 / (48 * T) := by
  sorry

/-- LEAF. Backlund pp. 371 to 373, displays 82 and the real integral budget,
with Rosser p. 224 radius 1.32 and exact Euler product center cost.
Only a real piecewise envelope occurs. There are no powers or gamma functions.
The correction 217 over 48piT combines 4 over piT with 25 over 48piT. -/
theorem envelope_budget (T : ℝ) (hT : 1400 ≤ T) :
    (∫ φ in (0 : ℝ)..π, logEnvelope T φ) / (2 * π * Real.log (4 * 1.32 / 3)) +
      1 / 2 + 217 / (48 * π * T) ≤
      0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 +
        Real.log ‖riemannZeta (5 / 2) / riemannZeta (5 / 4)‖ /
          (2 * Real.log (4 * 1.32 / 3)) := by
  have h2 : Complex.ofReal ((5 : ℝ) / 2) = (5 : ℂ) / 2 := by push_cast; ring
  have h4 : Complex.ofReal ((5 : ℝ) / 4) = (5 : ℂ) / 4 := by push_cast; ring
  have h := envelope_core hT (integral_branch1 T) zeta_54_le zeta_52_ge
  rw [h2, h4] at h
  exact h

/-- Rosser p. 224, exactly the existing circle_gamma_bound statement.
CONDITIONAL ON zeta_circle_bound, gamma_remainder_bound and envelope_budget.
The averaged powers, integration and center comparison are proved. -/
theorem circle_gamma_bound (A T : ℝ) (hA : 1400 ≤ A)
    (hFA : (A / (2 * π) * Real.log (A / (2 * π)) - A / (2 * π) + 7 / 8) = 1041)
    (hT : A ≤ T) (N : ℕ) (hN : 0 < N) :
    (∫ φ in (0 : ℝ)..π,
      Real.log ‖poweredZeta T N ((1.32 : ℂ) * Complex.exp (φ * Complex.I))‖) /
        (2 * π * Real.log (4 * 1.32 / 3) * N) +
      1 / 2 + 4 / (π * T) + |gammaRemainder T| / π ≤
        0.137 * Real.log T + 0.443 * Real.log (Real.log T) + 1.588 + Real.log ‖riemannZeta (5 / 4 + T * Complex.I)‖ /
            (2 * Real.log (4 * 1.32 / 3)) := by
  have ht : 1400 ≤ T := hA.trans hT
  have hq : 0 < Real.log (4 * 1.32 / 3) := Real.log_pos (by norm_num)
  have hNR : (0 : ℝ) < N := by exact_mod_cast hN
  have hden : 0 < 2 * π * Real.log (4 * 1.32 / 3) := by positivity
  have hi := intervalIntegral.integral_mono_on Real.pi_pos.le
    (powered_log_integrable T ht N) ((logEnvelope_integrable T).const_mul (N : ℝ))
    (fun φ hφ => by
      obtain ⟨hp, hm⟩ := zeta_circle_bound T φ ht hφ
      exact log_average_pow_le _ _ N _ (logEnvelope_nonneg T φ ht) hp hm)
  rw [intervalIntegral.integral_const_mul] at hi
  have hdiv := div_le_div_of_nonneg_right hi (mul_pos hden hNR).le
  have hcancel : ((N : ℝ) * ∫ φ in (0 : ℝ)..π, logEnvelope T φ) /
      (2 * π * Real.log (4 * 1.32 / 3) * N) =
      (∫ φ in (0 : ℝ)..π, logEnvelope T φ) /
        (2 * π * Real.log (4 * 1.32 / 3)) := by field_simp
  rw [hcancel] at hdiv
  have hc := center_euler_lower (5 / 4) T (by norm_num)
  norm_num only [show (2 : ℝ) * (5 / 4) = 5 / 2 by norm_num,
    Complex.ofReal_div, Complex.ofReal_ofNat] at hc
  have hcz : 0 < ‖riemannZeta (5 / 2) / riemannZeta (5 / 4)‖ := by
    apply norm_pos_iff.mpr
    exact div_ne_zero (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
      (riemannZeta_ne_zero_of_one_lt_re (by norm_num))
  have hlog := div_le_div_of_nonneg_right (Real.log_le_log hcz hc) (by positivity : 0 ≤ 2 * Real.log (4 * 1.32 / 3))
  have hg := div_le_div_of_nonneg_right (gamma_remainder_bound T ht) Real.pi_pos.le
  have hid : 4 / (π * T) + (25 / (48 * T)) / π = 217 / (48 * π * T) := by ring
  have hb := envelope_budget T ht
  rw [← hid] at hb
  linarith

end LeanLab.RamareSaouter2003.Decomp419a

#print axioms LeanLab.RamareSaouter2003.Decomp419a.zeta_circle_bound
#print axioms LeanLab.RamareSaouter2003.Decomp419a.gamma_remainder_bound
#print axioms LeanLab.RamareSaouter2003.Decomp419a.envelope_budget
#print axioms LeanLab.RamareSaouter2003.Decomp419a.circle_gamma_bound
