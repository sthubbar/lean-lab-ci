/-
P0069 Baker, Harman, Pintz 1997, Theorem 2, page 3. ROUTE BURST session 7, step
`section2_circle_method-p2`, QUESTION 2: the formal `Thm2.Theorem2` quantifies over all
real u, v, including u = v = 0, while the paper fixes positive constants u, v by display
1.5 on page 2: u₀ > 0.99, v₀ > 0.05, and the four correlations are applied only to these.

With u = v = 0 the threshold `K |uv| Y/(ℒℒ') 𝔖(2n)/ℒ` of 1.6 is zero, so the formal
conclusion demands that the convolution Σ_{k+m=N} a(k)b(m) vanish at all but fewer than
x^{θ₁θ₂}/ℒ^A even N, see `Section2MS.conclusion_u_zero_iff`. The paper's own proof gives
only that the convolution is ≪ Y ℒ^{-3} there, page 6, which is not zero.

Falsifier, formalized below. Write Y = x^{θ₁}, H = x^{θ₁θ₂}, W = x - Y - 1. Let p = p(x) be a
prime in [W - W^{0.525}, W], which exists for large x by the cited theorem of Baker, Harman
and Pintz 2001, `PrimesInShortIntervals`. Put a(k) = 1 if k = p and 0 otherwise, and
b(m) = 1 if m is odd and ⌈x⌉ ≤ p + m ≤ ⌊x + H⌋, and 0 otherwise. Then with u = v = 0:
* i holds since the sum in 1.7 has norm at most 1, below Y ℒ^{-A};
* ii holds with B = 0 since |a|, |b| ≤ 1, and a is rough since p > x/2 > ℒ^A;
* iii holds since b has at most H + 1 nonzero values, below Y ℒ^{-A};
* iv holds with E_q empty: the inner sum over J_y has at most 18qQ + 1 terms and vanishes
  unless y lies in a window of length H + 18qQ, so the left side of 1.9 is at most
  q (H + 18qQ)(18qQ + 1)² ≪ (qQ)² H², below (qQ)² Y ℒ^{-A};
* yet the convolution is exactly 1 at every even N in [x, x + H], at least (H - 3)/2 > H/ℒ
  of them, so the conclusion fails with A = 1.

Main results, all PROVED, the last two CONDITIONAL ON `PrimesInShortIntervals`:
* `not_theorem2`: ¬ Thm2.Theorem2 ε 0 for every 0 < ε < 1/4.
* `not_theorem2Paper`: ¬ Thm2.Theorem2Paper.
Proposed fix, a NEW def, no existing statement changed:
* `Theorem2Pos`: Theorem 2 with 0 < u and 0 < v added, and `theorem2Pos_of_theorem2`.
* `theorem2Pos_paper_of_leaf`: the positive form follows from the OPEN leaf
  `Section2MS.section2_mean_square`, CONDITIONAL on it.

This is a QUESTION about the formal statement, not a FINDING against the paper. AI wrote the
Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.Section2Question1

namespace LeanLab.BHP1997.Section2Q2
open Classical Complex Thm2 Section2MS Filter MeasureTheory

/-- CITED INPUT, not proved here. R. C. Baker, G. Harman and J. Pintz, "The difference
between consecutive primes, II", Proc. London Math. Soc. 83 (2001), 532 to 562, Theorem 1:
for all x larger than an absolute x₀ the interval [x - x^{0.525}, x] contains a prime. -/
def PrimesInShortIntervals : Prop :=
  ∃ X₀ : ℝ, ∀ x : ℝ, X₀ ≤ x → ∃ p : ℕ, p.Prime ∧ x - x ^ (21 / 40 : ℝ) ≤ p ∧ (p : ℝ) ≤ x

/-- The point W = x - Y - 1 below which the falsifier's prime is taken. -/
noncomputable def W (ε x : ℝ) : ℝ := x - x ^ (11 / 20 + ε) - 1

/-- The falsifier's prime p(x) in [W - W^{0.525}, W], when one exists, else 0. -/
noncomputable def p0 (ε x : ℝ) : ℕ :=
  if h : ∃ p : ℕ, p.Prime ∧ W ε x - W ε x ^ (21 / 40 : ℝ) ≤ p ∧ (p : ℝ) ≤ W ε x then
    Classical.choose h else 0

/-- The falsifier's a: the indicator of the one prime p(x). -/
noncomputable def fa (ε : ℝ) : ℝ → ℕ → ℂ := fun x k => if k = p0 ε x then 1 else 0

/-- The falsifier's b: the indicator of the odd m with ⌈x⌉ ≤ p(x) + m ≤ ⌊x + x^{θ₁θ₂}⌋. -/
noncomputable def fb (ε : ℝ) : ℝ → ℕ → ℂ := fun x m =>
  if Odd m ∧ ⌈x⌉₊ ≤ p0 ε x + m ∧
      p0 ε x + m ≤ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊ then 1 else 0

/-! ### Elementary pieces -/

/-- For a < b, eventually c x^a ℒ^A ≤ x^b: the only growth fact the falsifier uses. -/
theorem eventually_mul_rpow_log_le {a b : ℝ} (hab : a < b) (c A : ℝ) :
    ∀ᶠ x : ℝ in atTop, c * x ^ a * Real.log x ^ A ≤ x ^ b := by
  have h := (isLittleO_log_rpow_rpow_atTop A (sub_pos.mpr hab)).bound
    (show (0 : ℝ) < 1 / (|c| + 1) by positivity)
  filter_upwards [h, eventually_gt_atTop 1] with x hx hx1
  have hx0 : 0 < x := by linarith
  have hL : 0 ≤ Real.log x ^ A := Real.rpow_nonneg (Real.log_nonneg hx1.le) _
  rw [Real.norm_of_nonneg hL, Real.norm_of_nonneg (Real.rpow_nonneg hx0.le _)] at hx
  have hxa : 0 < x ^ a := Real.rpow_pos_of_pos hx0 a
  have hsplit : x ^ b = x ^ a * x ^ (b - a) := by
    rw [← Real.rpow_add hx0]; ring_nf
  have hc1 : 0 < |c| + 1 := by positivity
  calc c * x ^ a * Real.log x ^ A ≤ (|c| + 1) * x ^ a * Real.log x ^ A := by
        have : c ≤ |c| + 1 := by linarith [le_abs_self c]
        have := mul_le_mul_of_nonneg_right this (mul_nonneg hxa.le hL)
        nlinarith
    _ ≤ (|c| + 1) * x ^ a * (1 / (|c| + 1) * x ^ (b - a)) := by gcongr
    _ = x ^ b := by rw [hsplit]; field_simp

/-- The count of naturals in a real window [y, y + w] is at most w + 1. -/
theorem card_Icc_ceil_floor_le {y w : ℝ} (hy : 0 ≤ y) (hw : 0 ≤ w) :
    ((Finset.Icc ⌈y⌉₊ ⌊y + w⌋₊).card : ℝ) ≤ w + 1 := by
  rw [Nat.card_Icc]
  have h1 : (⌊y + w⌋₊ : ℝ) ≤ y + w := Nat.floor_le (by linarith)
  have h2 : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
  rcases le_or_gt ⌈y⌉₊ (⌊y + w⌋₊ + 1) with h | h
  · rw [Nat.cast_sub h]; push_cast; linarith
  · rw [Nat.sub_eq_zero_of_le h.le]; simp; linarith

/-- At least (b - a - 1)/2 of the naturals in [a, b] are even. -/
theorem card_even_Icc (a b : ℕ) :
    b - a ≤ 2 * ((Finset.Icc a b).filter Even).card + 1 := by
  have h : (Finset.Icc ((a + 1) / 2) (b / 2)).card ≤ ((Finset.Icc a b).filter Even).card := by
    apply Finset.card_le_card_of_injOn (fun k => 2 * k)
    · intro k hk
      simp only [Finset.coe_Icc, Set.mem_Icc] at hk
      simp only [Finset.coe_filter, Finset.mem_Icc, Set.mem_setOf_eq]
      exact ⟨⟨by omega, by omega⟩, even_two_mul k⟩
    · intro k1 _ k2 _ h
      simp only at h
      omega
  rw [Nat.card_Icc] at h
  omega

/-- A sum of products f m c m with |f|, |c| ≤ 1 and f supported in T has norm ≤ |T|. -/
theorem norm_sum_le_card_support (S T : Finset ℕ) (f c : ℕ → ℂ) (hf : ∀ m, ‖f m‖ ≤ 1)
    (hc : ∀ m, ‖c m‖ ≤ 1) (hT : ∀ m ∈ S, f m ≠ 0 → m ∈ T) :
    ‖∑ m ∈ S, f m * c m‖ ≤ T.card := by
  rw [← Finset.sum_filter_of_ne (p := fun m => m ∈ T) (by
    intro m hm hne
    apply hT m hm
    intro h0
    apply hne
    simp [h0])]
  calc ‖∑ m ∈ S.filter (fun m => m ∈ T), f m * c m‖
      ≤ ∑ m ∈ S.filter (fun m => m ∈ T), ‖f m * c m‖ := norm_sum_le _ _
    _ ≤ ∑ m ∈ S.filter (fun m => m ∈ T), (1 : ℝ) := by
        apply Finset.sum_le_sum
        intro m _
        rw [norm_mul]
        nlinarith [norm_nonneg (f m), norm_nonneg (c m), hf m, hc m]
    _ = ((S.filter (fun m => m ∈ T)).card : ℝ) := by simp
    _ ≤ T.card := by
        exact_mod_cast Finset.card_le_card (fun m hm => (Finset.mem_filter.mp hm).2)

/-- An interval integral of a nonnegative function dominated on (a, b] by M times the
indicator of [lo, hi] is at most (hi - lo) M. -/
theorem intervalIntegral_le_of_indicator {a b lo hi M : ℝ} (hab : a ≤ b) (hlh : lo ≤ hi)
    (hM : 0 ≤ M) (F : ℝ → ℝ) (hF0 : ∀ y, 0 ≤ F y)
    (hF : ∀ y ∈ Set.Ioc a b, F y ≤ Set.indicator (Set.Icc lo hi) (fun _ => M) y) :
    ∫ y in a..b, F y ≤ (hi - lo) * M := by
  rw [intervalIntegral.integral_of_le hab]
  calc ∫ y in Set.Ioc a b, F y
      ≤ ∫ y in Set.Ioc a b, Set.indicator (Set.Icc lo hi) (fun _ => M) y := by
        apply integral_mono_of_nonneg
        · exact Filter.Eventually.of_forall hF0
        · exact (integrableOn_const (C := M) measure_Ioc_lt_top.ne).indicator measurableSet_Icc
        · exact ae_restrict_of_forall_mem measurableSet_Ioc hF
    _ = (volume.restrict (Set.Ioc a b)).real (Set.Icc lo hi) * M := by
        rw [integral_indicator_const _ measurableSet_Icc, smul_eq_mul]
    _ ≤ (hi - lo) * M := by
        rw [measureReal_restrict_apply measurableSet_Icc]
        have hle : volume.real (Set.Icc lo hi ∩ Set.Ioc a b) ≤ hi - lo := by
          calc volume.real (Set.Icc lo hi ∩ Set.Ioc a b) ≤ volume.real (Set.Icc lo hi) :=
                measureReal_mono Set.inter_subset_left measure_Icc_lt_top.ne
            _ = hi - lo := Real.volume_real_Icc_of_le hlh
        exact mul_le_mul_of_nonneg_right hle hM

/-- The convolution of the indicator of one point p ∈ I with b, at N with N - p ∈ J. -/
theorem conv_single (I J : Finset ℕ) (p N : ℕ) (b : ℕ → ℂ) (hp : p ∈ I) (hN : p ≤ N)
    (hJ : N - p ∈ J) :
    (∑ k ∈ I, ∑ m ∈ J, if k + m = N then (if k = p then (1 : ℂ) else 0) * b m else 0) =
      b (N - p) := by
  rw [Finset.sum_eq_single p]
  · rw [Finset.sum_eq_single (N - p)]
    · simp [Nat.add_sub_cancel' hN]
    · intro m _ hm
      rw [if_neg]
      omega
    · intro h; exact absurd hJ h
  · intro k _ hk
    apply Finset.sum_eq_zero
    intro m _
    simp [hk]
  · intro h; exact absurd hp h


/-! ### The falsifier at large x -/

/-- The eventual size facts used by the falsifier, for 0 < ε < 1/4: Y ≤ x/8,
x^{0.525} ≤ Y/4, H ≤ Y/4, H ≥ 8, ℒ ≥ 4, and W ≥ X₀. -/
theorem eventually_base (ε X0 : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 4) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ 4 ≤ Real.log x ∧ 8 * x ^ (11 / 20 + ε) ≤ x ∧
      4 * x ^ (21 / 40 : ℝ) ≤ x ^ (11 / 20 + ε) ∧
      4 * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) ≤ x ^ (11 / 20 + ε) ∧
      8 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) ∧ X0 ≤ W ε x := by
  have e1 := eventually_mul_rpow_log_le (a := 11 / 20 + ε) (b := 1) (by linarith) 8 0
  have e2 := eventually_mul_rpow_log_le (a := 21 / 40) (b := 11 / 20 + ε) (by linarith) 4 0
  have e3 := eventually_mul_rpow_log_le (a := (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))
    (b := 11 / 20 + ε) (by nlinarith) 4 0
  have e4 := eventually_mul_rpow_log_le (a := 0)
    (b := (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) (by positivity) 8 0
  have e5 := Real.tendsto_log_atTop.eventually_ge_atTop 4
  filter_upwards [e1, e2, e3, e4, e5, eventually_ge_atTop (2 * |X0| + 2)]
    with x h1 h2 h3 h4 h5 h6
  simp only [Real.rpow_zero, mul_one, Real.rpow_one] at h1 h2 h3 h4
  have hx1 : 1 ≤ x := by linarith [abs_nonneg X0]
  refine ⟨hx1, h5, h1, h2, h3, h4, ?_⟩
  unfold W
  linarith [le_abs_self X0]

/-- The cited prime p(x) of the falsifier and its position, for x with the base facts:
p is prime, p + Y + 1 ≤ x, x + H - 2Y + 1 ≤ p and x/2 ≤ p. -/
theorem p0_window {ε X0 x : ℝ}
    (hP : ∀ x : ℝ, X0 ≤ x → ∃ p : ℕ, p.Prime ∧ x - x ^ (21 / 40 : ℝ) ≤ p ∧ (p : ℝ) ≤ x)
    (hx1 : 1 ≤ x) (h1 : 8 * x ^ (11 / 20 + ε) ≤ x)
    (h2 : 4 * x ^ (21 / 40 : ℝ) ≤ x ^ (11 / 20 + ε))
    (h3 : 4 * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) ≤ x ^ (11 / 20 + ε))
    (h4 : 8 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (hW : X0 ≤ W ε x) :
    (p0 ε x).Prime ∧ (p0 ε x : ℝ) + x ^ (11 / 20 + ε) + 1 ≤ x ∧
      x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) - 2 * x ^ (11 / 20 + ε) + 1 ≤
        (p0 ε x : ℝ) ∧ x / 2 ≤ (p0 ε x : ℝ) := by
  have h := hP _ hW
  have hspec : (p0 ε x).Prime ∧ W ε x - W ε x ^ (21 / 40 : ℝ) ≤ p0 ε x ∧
      (p0 ε x : ℝ) ≤ W ε x := by
    unfold p0; rw [dif_pos h]; exact Classical.choose_spec h
  obtain ⟨hpr, hlo, hhi⟩ := hspec
  have hW0 : 0 ≤ W ε x := by unfold W; linarith
  have hWx : W ε x ≤ x := by
    unfold W; linarith [Real.rpow_nonneg (show (0 : ℝ) ≤ x by linarith) (11 / 20 + ε)]
  have hpow : W ε x ^ (21 / 40 : ℝ) ≤ x ^ (21 / 40 : ℝ) :=
    Real.rpow_le_rpow hW0 hWx (by norm_num)
  unfold W at hlo hhi hpow
  refine ⟨hpr, by linarith, by linarith, by linarith⟩

/-- Page 2 display 1.6 read through `conclusion_u_zero_iff`: at every even N in
[⌈x⌉, ⌊x + H⌋] the falsifier's convolution is exactly 1. -/
theorem conv_eq_one {ε X0 x : ℝ}
    (hP : ∀ x : ℝ, X0 ≤ x → ∃ p : ℕ, p.Prime ∧ x - x ^ (21 / 40 : ℝ) ≤ p ∧ (p : ℝ) ≤ x)
    (hx1 : 1 ≤ x) (h1 : 8 * x ^ (11 / 20 + ε) ≤ x)
    (h2 : 4 * x ^ (21 / 40 : ℝ) ≤ x ^ (11 / 20 + ε))
    (h3 : 4 * x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) ≤ x ^ (11 / 20 + ε))
    (h4 : 8 ≤ x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))) (hW : X0 ≤ W ε x)
    (N : ℕ) (hN : N ∈ Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊)
    (hev : Even N) :
    (∑ k ∈ Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊,
      ∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
        if k + m = N then fa ε x k * fb ε x m else 0) = 1 := by
  obtain ⟨hpr, hp1, hp2, hp3⟩ := p0_window hP hx1 h1 h2 h3 h4 hW
  set p := p0 ε x with hpdef
  set Y := x ^ (11 / 20 + ε) with hY
  set H := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) with hH
  rw [Finset.mem_Icc] at hN
  have hx0 : 0 ≤ x := by linarith
  have hNlo : x ≤ (N : ℝ) := le_trans (Nat.le_ceil x) (by exact_mod_cast hN.1)
  have hNhi : (N : ℝ) ≤ x + H :=
    le_trans (by exact_mod_cast hN.2) (Nat.floor_le (by positivity))
  have hpN : p ≤ N := by
    have : (p : ℝ) ≤ N := by linarith
    exact_mod_cast this
  have hcast : ((N - p : ℕ) : ℝ) = (N : ℝ) - p := by rw [Nat.cast_sub hpN]
  have hpI : p ∈ Finset.Ioc ⌊x - 2 * Y⌋₊ ⌊x⌋₊ := by
    rw [Finset.mem_Ioc]
    refine ⟨(Nat.floor_lt' hpr.ne_zero).mpr (by linarith), Nat.le_floor (by linarith)⟩
  have hJ : N - p ∈ Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊ := by
    rw [Finset.mem_Ioc]
    constructor
    · have : Y < ((N - p : ℕ) : ℝ) := by rw [hcast]; linarith
      exact (Nat.floor_lt (by positivity)).mpr this
    · apply Nat.le_floor
      rw [hcast]; linarith
  have hconv := conv_single (Finset.Ioc ⌊x - 2 * Y⌋₊ ⌊x⌋₊) (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊) p N
    (fb ε x) hpI hpN hJ
  have hfa : ∀ k, fa ε x k = if k = p then (1 : ℂ) else 0 := fun k => rfl
  simp only [hfa]
  rw [hconv]
  -- b(N - p) = 1
  have hpodd : Odd p := by
    rcases hpr.eq_two_or_odd' with h | h
    · exfalso
      have : (p : ℝ) = 2 := by exact_mod_cast h
      linarith
    · exact h
  have hodd : Odd (N - p) := by
    rcases hev with ⟨r, hr⟩
    rcases hpodd with ⟨s, hs⟩
    exact ⟨r - s - 1, by omega⟩
  unfold fb
  rw [if_pos]
  refine ⟨hodd, ?_, ?_⟩ <;> rw [← hpdef, Nat.add_sub_cancel' hpN]
  · exact hN.1
  · exact hN.2


/-- Where the falsifier's b lives: b(m) ≠ 0 forces x ≤ p + m ≤ x + H. -/
theorem fb_support {ε x : ℝ} (hx : 0 ≤ x) (m : ℕ) (hm : fb ε x m ≠ 0) :
    x ≤ (p0 ε x : ℝ) + m ∧
      (p0 ε x : ℝ) + m ≤ x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) := by
  unfold fb at hm
  split_ifs at hm with h
  · obtain ⟨_, h1, h2⟩ := h
    refine ⟨?_, ?_⟩
    · have := Nat.ceil_le.mp h1
      exact_mod_cast this
    · have h3 : ((p0 ε x + m : ℕ) : ℝ) ≤ x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) :=
        le_trans (by exact_mod_cast h2) (Nat.floor_le (by positivity))
      exact_mod_cast h3
  · exact absurd rfl hm

theorem norm_fa_le (ε x : ℝ) (k : ℕ) : ‖fa ε x k‖ ≤ 1 := by
  unfold fa; split_ifs <;> simp

theorem norm_fb_le (ε x : ℝ) (m : ℕ) : ‖fb ε x m‖ ≤ 1 := by
  unfold fb; split_ifs <;> simp

/-- A bound c ≤ C Y ℒ^{-A} from c ℒ^A ≤ Y and C ≥ 1. -/
theorem le_C_mul {C Y L A c : ℝ} (hL : 0 < L) (hC : 1 ≤ C) (hc : 0 ≤ c)
    (h : c * L ^ A ≤ Y) : c ≤ C * Y * L ^ (-A) := by
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hL A
  rw [Real.rpow_neg hL.le, ← div_eq_mul_inv, le_div_iff₀ hLA]
  have hY : 0 ≤ Y := le_trans (by positivity) h
  nlinarith

/-- Hypothesis i of Theorem 2, display 1.7 of page 3, for the falsifier's a with u = 0. -/
theorem hyp_i (ε : ℝ) (hε0 : 0 < ε) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ x →
        ‖∑ k ∈ (Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊).filter (fun k : ℕ => (k : ℝ) ≤ t),
          (fa ε x k * χ (k : ZMod q) - delta χ * ((0 : ℝ) : ℂ) / (Real.log x : ℂ))‖ ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A _
  have e := eventually_mul_rpow_log_le (a := 0) (b := 11 / 20 + ε) (by linarith) 1 A
  obtain ⟨X, hX⟩ := eventually_atTop.mp
    (e.and (Real.tendsto_log_atTop.eventually_ge_atTop 1))
  refine ⟨max X 3, fun x hx q _ _ χ t _ => ?_⟩
  obtain ⟨h1, hL⟩ := hX x (le_trans (le_max_left _ _) hx)
  have hx0 : 0 < x := by linarith [le_max_right X 3]
  simp only [Real.rpow_zero, mul_one, Complex.ofReal_zero, mul_zero, zero_div, sub_zero] at h1 ⊢
  have hcard := norm_sum_le_card_support
    ((Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊).filter (fun k : ℕ => (k : ℝ) ≤ t)) {p0 ε x} (fa ε x) (fun k => χ (k : ZMod q))
    (norm_fa_le ε x) (fun k => DirichletCharacter.norm_le_one χ _)
    (by intro k _ hk; unfold fa at hk; split_ifs at hk with h
        · simp [h]
        · exact absurd rfl hk)
  simp only [Finset.card_singleton, Nat.cast_one] at hcard
  exact le_trans hcard (le_C_mul (by linarith) (le_trans (by norm_num) (le_max_right X 3))
    zero_le_one h1)


/-- Hypothesis ii of Theorem 2, page 3, the divisor bound, with B = 0. -/
theorem hyp_ii (ε : ℝ) :
    ∃ C : ℝ, ∀ x k, ‖fa ε x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ (0 : ℝ) ∧
      ‖fb ε x k‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ (0 : ℝ) :=
  ⟨1, fun x k => by simp only [Real.rpow_zero, mul_one]; exact ⟨norm_fa_le ε x k, norm_fb_le ε x k⟩⟩

/-- Hypothesis ii of Theorem 2, page 3, the roughness of a: the falsifier's a lives on the
prime p(x) > x/2 > ℒ^A, which has no factor below ℒ^A. -/
theorem hyp_rough (ε X0 : ℝ)
    (hP : ∀ x : ℝ, X0 ≤ x → ∃ p : ℕ, p.Prime ∧ x - x ^ (21 / 40 : ℝ) ≤ p ∧ (p : ℝ) ≤ x)
    (hε0 : 0 < ε) (hε1 : ε < 1 / 4) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
      Nat.gcd k (primorialBelow (Real.log x ^ A)) ≠ 1 → fa ε x k = 0 := by
  intro A _
  have e := eventually_mul_rpow_log_le (a := 0) (b := 1) (by norm_num) 4 A
  obtain ⟨X, hX⟩ := eventually_atTop.mp (e.and (eventually_base ε X0 hε0 hε1))
  refine ⟨X, fun x hx k hk => ?_⟩
  obtain ⟨h0, hx1, _, h1, h2, h3, h4, hW⟩ := hX x hx
  simp only [Real.rpow_zero, mul_one, Real.rpow_one] at h0
  obtain ⟨hpr, _, _, hp3⟩ := p0_window hP hx1 h1 h2 h3 h4 hW
  unfold fa
  rw [if_neg]
  intro hkp
  subst hkp
  apply hk
  by_contra hcop
  have hdvd : p0 ε x ∣ primorialBelow (Real.log x ^ A) := by
    by_contra hnd
    exact hcop ((Nat.Prime.coprime_iff_not_dvd hpr).mpr hnd)
  unfold primorialBelow at hdvd
  obtain ⟨r, hr, hpr'⟩ := (Nat.Prime.prime hpr).dvd_finsetProd_iff _ |>.mp hdvd
  rw [Finset.mem_filter] at hr
  have hrp : p0 ε x = r := (Nat.prime_dvd_prime_iff_eq hpr hr.2.1).mp hpr'
  have : (r : ℝ) < Real.log x ^ A := hr.2.2
  rw [← hrp] at this
  linarith

/-- Hypothesis iii of Theorem 2, display 1.8 of page 3, for the falsifier's b with v = 0:
b has at most H + 1 nonzero values, below Y ℒ^{-A}. -/
theorem hyp_iii (ε X0 : ℝ)
    (hP : ∀ x : ℝ, X0 ≤ x → ∃ p : ℕ, p.Prime ∧ x - x ^ (21 / 40 : ℝ) ≤ p ∧ (p : ℝ) ≤ x)
    (hε0 : 0 < ε) (hε1 : ε < 1 / 4) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
        ‖∑ m ∈ (Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊).filter
            (fun m : ℕ => (m : ℝ) ≤ t),
          (fb ε x m * χ (m : ZMod q) - delta χ * ((0 : ℝ) : ℂ) /
            (Real.log (x ^ (11 / 20 + ε)) : ℂ))‖ ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A _
  have e := eventually_mul_rpow_log_le (a := (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))
    (b := 11 / 20 + ε) (by nlinarith) 2 A
  obtain ⟨X, hX⟩ := eventually_atTop.mp (e.and (eventually_base ε X0 hε0 hε1))
  refine ⟨max X 1, fun x hx q _ _ χ t _ => ?_⟩
  obtain ⟨h0, hx1, hL, h1, h2, h3, h4, hW⟩ := hX x (le_trans (le_max_left _ _) hx)
  obtain ⟨hpr, hp1, _, _⟩ := p0_window hP hx1 h1 h2 h3 h4 hW
  have hx0 : 0 ≤ x := by linarith
  set H := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) with hH
  have hY0 : 0 ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg hx0 _
  simp only [Complex.ofReal_zero, mul_zero, zero_div, sub_zero]
  have hcard := norm_sum_le_card_support
    ((Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊).filter (fun m : ℕ => (m : ℝ) ≤ t))
    (Finset.Icc ⌈x - p0 ε x⌉₊ ⌊(x - p0 ε x) + H⌋₊) (fb ε x) (fun m => χ (m : ZMod q))
    (norm_fb_le ε x) (fun m => DirichletCharacter.norm_le_one χ _)
    (by
      intro m _ hm
      obtain ⟨hm1, hm2⟩ := fb_support hx0 m hm
      rw [Finset.mem_Icc]
      exact ⟨Nat.ceil_le.mpr (by linarith), Nat.le_floor (by linarith)⟩)
  have hc2 := card_Icc_ceil_floor_le (y := x - p0 ε x) (w := H) (by linarith)
    (by positivity)
  have hfin := le_C_mul (C := max X 1) (A := A) (by linarith) (le_max_right _ _)
    (show (0 : ℝ) ≤ 2 * H by positivity) h0
  linarith


/-- Hypothesis iv of Theorem 2, display 1.9 of page 3, one character: for y ≤ 3Y the window
J_y = [y, y + yz] has length yz ≤ 18qQ, and it meets the support of b only for y in a
window of length H + 18qQ, so the integral is at most (H + 18qQ)(18qQ + 1)². -/
theorem integral_window_le {ε x : ℝ} (hx0 : 0 ≤ x) (hp : (p0 ε x : ℝ) ≤ x)
    (hY : 0 < x ^ (11 / 20 + ε)) (q Q : ℕ)
    (z : ℝ) (hz1 : (q * Q : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z)
    (hz2 : z ≤ 6 * q * Q / x ^ (11 / 20 + ε)) (χ : DirichletCharacter ℂ q) :
    ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
      ‖∑ m ∈ (Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
        (fb ε x m * χ (m : ZMod q) - delta χ * ((0 : ℝ) : ℂ) /
          (Real.log (x ^ (11 / 20 + ε)) : ℂ))‖ ^ 2 ≤
      (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) + 18 * q * Q) *
        (18 * q * Q + 1) ^ 2 := by
  set Y := x ^ (11 / 20 + ε) with hYdef
  set H := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) with hH
  set p := p0 ε x with hpdef
  have hqQ : (0 : ℝ) ≤ q * Q := by positivity
  have hz0 : 0 ≤ z := le_trans (by positivity) hz1
  have hH0 : 0 ≤ H := by positivity
  simp only [Complex.ofReal_zero, mul_zero, zero_div, sub_zero]
  have key := intervalIntegral_le_of_indicator (a := Y / 2) (b := 3 * Y)
    (lo := x - p - 18 * q * Q) (hi := x + H - p) (M := (18 * q * Q + 1) ^ 2)
    (by linarith) (by linarith) (by positivity)
    (fun y => ‖∑ m ∈ (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter
          (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
        fb ε x m * χ (m : ZMod q)‖ ^ 2) (fun y => by positivity) (by
      intro y hy
      obtain ⟨hy1, hy2⟩ := hy
      have hy0 : 0 ≤ y := by linarith
      have hyz : y * z ≤ 18 * q * Q := by
        calc y * z ≤ (3 * Y) * (6 * q * Q / Y) := by gcongr
          _ = 18 * q * Q := by field_simp; ring
      by_cases hin : y ∈ Set.Icc (x - p - 18 * q * Q) (x + H - p)
      · rw [Set.indicator_of_mem hin]
        have hc := norm_sum_le_card_support ((Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z)) (Finset.Icc ⌈y⌉₊ ⌊y + y * z⌋₊) (fb ε x)
          (fun m => χ (m : ZMod q)) (norm_fb_le ε x) (fun m => DirichletCharacter.norm_le_one χ _)
          (by
            intro m hm _
            rw [Finset.mem_filter] at hm
            rw [Finset.mem_Icc]
            exact ⟨Nat.ceil_le.mpr hm.2.1, Nat.le_floor hm.2.2⟩)
        have hc2 := card_Icc_ceil_floor_le hy0 (mul_nonneg hy0 hz0)
        have hb : ‖∑ m ∈ (Finset.Ioc ⌊Y⌋₊ ⌊2 * Y⌋₊).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
            fb ε x m * χ (m : ZMod q)‖ ≤ 18 * q * Q + 1 := by linarith
        exact pow_le_pow_left₀ (norm_nonneg _) hb 2
      · rw [Set.indicator_of_notMem hin]
        rw [Finset.sum_eq_zero]
        · simp
        intro m hm
        rw [Finset.mem_filter] at hm
        by_cases hfm : fb ε x m = 0
        · simp [hfm]
        · exfalso
          obtain ⟨h1, h2⟩ := fb_support hx0 m hfm
          apply hin
          rw [Set.mem_Icc]
          constructor <;> linarith [hm.2.1, hm.2.2])
  have hlen : x + H - p - (x - p - 18 * q * Q) = H + 18 * q * Q := by ring
  rw [hlen] at key
  exact key

/-- Pure arithmetic for display 1.9: with 1 ≤ q ≤ Q ≤ s/2, s² = H ≥ 1 and
3000 H² ℒ^A ≤ Y, q (H + 18qQ)(18qQ + 1)² ≤ C (qQ)² Y ℒ^{-A} for C ≥ 1. -/
theorem iv_arith {q Q s H Y L A C : ℝ} (hq : 1 ≤ q) (hqQ : q ≤ Q) (hQs : Q ≤ s / 2)
    (hs0 : 0 ≤ s) (hs2 : s ^ 2 = H) (hH : 1 ≤ H) (hL : 0 < L) (hC : 1 ≤ C)
    (hY : 3000 * H ^ 2 * L ^ A ≤ Y) :
    q * (H + 18 * q * Q) * (18 * q * Q + 1) ^ 2 ≤ C * (q * Q) ^ 2 * Y * L ^ (-A) := by
  have hQ1 : 1 ≤ Q := le_trans hq hqQ
  have hP1 : 1 ≤ q * Q := by nlinarith
  have hs1 : 1 ≤ s := by nlinarith
  have hsH : s ≤ H := by nlinarith
  have hqH : q ≤ H := by linarith
  have hPQ : q * Q ≤ H / 4 := by nlinarith
  have hM : 18 * q * Q + 1 ≤ 19 * (q * Q) := by linarith
  have hLA : 0 < L ^ A := Real.rpow_pos_of_pos hL A
  have step1 : q * (H + 18 * q * Q) * (18 * q * Q + 1) ^ 2 ≤
      H * (6 * H) * (19 * (q * Q)) ^ 2 := by
    have h1 : H + 18 * q * Q ≤ 6 * H := by nlinarith
    have h2 : (18 * q * Q + 1) ^ 2 ≤ (19 * (q * Q)) ^ 2 :=
      pow_le_pow_left₀ (by positivity) hM 2
    have h3 : 0 ≤ H + 18 * q * Q := by positivity
    calc q * (H + 18 * q * Q) * (18 * q * Q + 1) ^ 2
        ≤ H * (6 * H) * (18 * q * Q + 1) ^ 2 := by gcongr
      _ ≤ H * (6 * H) * (19 * (q * Q)) ^ 2 := by gcongr
  have step2 : H * (6 * H) * (19 * (q * Q)) ^ 2 ≤ (q * Q) ^ 2 * (Y / L ^ A) := by
    have hYL : 3000 * H ^ 2 ≤ Y / L ^ A := by rw [le_div_iff₀ hLA]; linarith
    nlinarith [mul_le_mul_of_nonneg_left hYL (sq_nonneg (q * Q)), sq_nonneg H,
      sq_nonneg (q * Q)]
  calc q * (H + 18 * q * Q) * (18 * q * Q + 1) ^ 2 ≤ (q * Q) ^ 2 * (Y / L ^ A) :=
        step1.trans step2
    _ ≤ C * (q * Q) ^ 2 * Y * L ^ (-A) := by
        rw [Real.rpow_neg hL.le, ← div_eq_mul_inv]
        have hY0 : 0 ≤ Y := le_trans (by positivity) hY
        have : (q * Q) ^ 2 * (Y / L ^ A) ≤ C * ((q * Q) ^ 2 * (Y / L ^ A)) :=
          le_mul_of_one_le_left (by positivity) hC
        calc (q * Q) ^ 2 * (Y / L ^ A) ≤ C * ((q * Q) ^ 2 * (Y / L ^ A)) := this
          _ = C * (q * Q) ^ 2 * Y / L ^ A := by ring


/-- The Q = ⌊H^{1/2}/2⌋ of page 3, with H = Y^{θ₂}, as `Thm2.Theorem2` writes it. -/
noncomputable def Qf (ε x : ℝ) : ℕ :=
  ⌊((x ^ (11 / 20 + ε)) ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ (1 / 2 : ℝ) / 2⌋₊

/-- There are at most q Dirichlet characters mod q. -/
theorem card_chars_le (q : ℕ) (hq : 1 ≤ q) :
    (((Finset.univ : Finset (DirichletCharacter ℂ q)) \ ∅).card : ℝ) ≤ q := by
  haveI : NeZero q := ⟨by omega⟩
  have h1 : ((Finset.univ : Finset (DirichletCharacter ℂ q)) \ ∅).card ≤
      (Finset.univ : Finset (DirichletCharacter ℂ q)).card :=
    Finset.card_le_card Finset.sdiff_subset
  rw [Finset.card_univ, ← Nat.card_eq_fintype_card,
    DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q] at h1
  exact_mod_cast h1.trans (Nat.totient_le q)

/-- Hypothesis iv of Theorem 2, display 1.9 of page 3, for the falsifier's b with v = 0 and
every exceptional set E_q empty. -/
theorem hyp_iv (ε X0 : ℝ)
    (hP : ∀ x : ℝ, X0 ≤ x → ∃ p : ℕ, p.Prime ∧ x - x ^ (21 / 40 : ℝ) ≤ p ∧ (p : ℝ) ≤ x)
    (hε0 : 0 < ε) (hε1 : ε < 1 / 4) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ Qf ε x →
      (((∅ : Finset (DirichletCharacter ℂ q))).card : ℝ) ≤
          C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A) ∧
      ∀ z : ℝ, ((q : ℝ) * (Qf ε x : ℝ)) / (6 * x ^ (11 / 20 + ε)) ≤ z →
        z ≤ 6 * (q : ℝ) * (Qf ε x : ℝ) / x ^ (11 / 20 + ε) →
        ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ ∅,
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
            ‖∑ m ∈ (Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (fb ε x m * χ (m : ZMod q) - delta χ * ((0 : ℝ) : ℂ) /
                (Real.log (x ^ (11 / 20 + ε)) : ℂ))‖ ^ 2 ≤
          C * ((q : ℝ) * (Qf ε x : ℝ)) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A _
  have e := eventually_mul_rpow_log_le (a := (11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) * 2)
    (b := 11 / 20 + ε) (by nlinarith) 3000 A
  obtain ⟨X, hX⟩ := eventually_atTop.mp (e.and (eventually_base ε X0 hε0 hε1))
  refine ⟨max X 1, fun x hx q hq1 hqQ => ⟨?_, fun z hz1 hz2 => ?_⟩⟩
  · have hx1 : 1 ≤ x := le_trans (le_max_right _ _) hx
    have hL : 0 ≤ Real.log x := Real.log_nonneg hx1
    have h1 : 0 ≤ max X 1 := le_trans zero_le_one (le_max_right _ _)
    have h2 : 0 ≤ (q : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_nonneg (by positivity) _
    have h3 : 0 ≤ Real.log x ^ (-2 * A) := Real.rpow_nonneg hL _
    simp only [Finset.card_empty, Nat.cast_zero]
    positivity
  obtain ⟨h0, hx1, hL, h1, h2, h3, h4, hW⟩ := hX x (le_trans (le_max_left _ _) hx)
  obtain ⟨hpr, hp1, _, _⟩ := p0_window hP hx1 h1 h2 h3 h4 hW
  have hx0 : 0 ≤ x := by linarith
  set H := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) with hH
  have hYpos : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hB0 : 0 ≤ (H + 18 * q * Qf ε x) * (18 * q * Qf ε x + 1) ^ 2 := by positivity
  calc ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ ∅,
          ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
            ‖∑ m ∈ (Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              (fb ε x m * χ (m : ZMod q) - delta χ * ((0 : ℝ) : ℂ) /
                (Real.log (x ^ (11 / 20 + ε)) : ℂ))‖ ^ 2
      ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ ∅,
          (H + 18 * q * Qf ε x) * (18 * q * Qf ε x + 1) ^ 2 :=
        Finset.sum_le_sum (fun χ _ =>
          integral_window_le hx0 (by linarith [hYpos.le]) hYpos q (Qf ε x) z hz1 hz2 χ)
    _ = (((Finset.univ : Finset (DirichletCharacter ℂ q)) \ ∅).card : ℝ) *
          ((H + 18 * q * Qf ε x) * (18 * q * Qf ε x + 1) ^ 2) := by
        rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ (q : ℝ) * ((H + 18 * q * Qf ε x) * (18 * q * Qf ε x + 1) ^ 2) :=
        mul_le_mul_of_nonneg_right (card_chars_le q hq1) hB0
    _ = (q : ℝ) * (H + 18 * q * Qf ε x) * (18 * q * Qf ε x + 1) ^ 2 := by ring
    _ ≤ max X 1 * ((q : ℝ) * (Qf ε x : ℝ)) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
        set s := ((x ^ (11 / 20 + ε)) ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ)) ^ (1 / 2 : ℝ) with hs
        have hYH : (x ^ (11 / 20 + ε)) ^ (2 * (1 / 16 - 1 / 10 ^ 5) : ℝ) = H :=
          (Real.rpow_mul hx0 (11 / 20 + ε) (2 * (1 / 16 - 1 / 10 ^ 5))).symm.trans hH.symm
        have hs0 : 0 ≤ s := Real.rpow_nonneg (by positivity) _
        have hs2 : s ^ 2 = H := by
          rw [hs, ← Real.sqrt_eq_rpow, Real.sq_sqrt (by positivity), hYH]
        have hQs : (Qf ε x : ℝ) ≤ s / 2 := by
          unfold Qf; exact Nat.floor_le (by positivity)
        have hH2 : x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)) * 2) = H ^ 2 := by
          rw [Real.rpow_mul hx0, ← hH, Real.rpow_two]
        rw [hH2] at h0
        exact iv_arith (by exact_mod_cast hq1) (by exact_mod_cast hqQ) hQs hs0 hs2
          (by linarith) (by linarith) (le_max_right _ _) h0

/-! ### The falsifier -/

/-- QUESTION 2 falsifier, CONDITIONAL ON `PrimesInShortIntervals`, Baker Harman Pintz 2001.
For every 0 < ε < 1/4, `Thm2.Theorem2 ε 0` fails: the falsifier's a, b with u = v = 0 and
every E_q empty satisfy hypotheses i to iv of page 3, yet the convolution is 1 at every even
N in [x, x + H], more than H/ℒ of them. PROVED from the cited input. -/
theorem not_theorem2 (hP : PrimesInShortIntervals) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε < 1 / 4) :
    ¬ Theorem2 ε 0 := by
  obtain ⟨X0, hX0⟩ := hP
  intro hT
  have hcon : Conclusion ε (fa ε) (fb ε) 0 0 :=
    (theorem2_iff_with ε 0).mp hT (fa ε) (fb ε) 0 0 (fun _ _ _ => ∅)
      (hyp_i ε hε0) (hyp_ii ε) (hyp_rough ε X0 hX0 hε0 hε1) (hyp_iii ε X0 hX0 hε0 hε1)
      (hyp_iv ε X0 hX0 hε0 hε1)
  obtain ⟨C, hC⟩ := (conclusion_u_zero_iff ε (fa ε) (fb ε) 0).mp hcon 1 one_pos
  obtain ⟨X, hX⟩ := eventually_atTop.mp (eventually_base ε X0 hε0 hε1)
  have hx := hC (max C X) (le_max_left _ _)
  obtain ⟨hx1, hL, h1, h2, h3, h4, hW⟩ := hX (max C X) (le_max_right _ _)
  set x := max C X with hxdef
  set H := x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) with hH
  have hx0 : 0 ≤ x := by linarith
  have hfilt : (Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).filter (fun N : ℕ => Even N ∧
      (∑ k ∈ Finset.Ioc ⌊x - 2 * x ^ (11 / 20 + ε)⌋₊ ⌊x⌋₊,
        ∑ m ∈ Finset.Ioc ⌊x ^ (11 / 20 + ε)⌋₊ ⌊2 * x ^ (11 / 20 + ε)⌋₊,
          if k + m = N then fa ε x k * fb ε x m else 0) ≠ 0) =
      (Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).filter (fun N : ℕ => Even N) := by
    apply Finset.filter_congr
    intro N hN
    constructor
    · exact fun h => h.1
    · intro hev
      refine ⟨hev, ?_⟩
      rw [conv_eq_one hX0 hx1 h1 h2 h3 h4 hW N hN hev]
      exact one_ne_zero
  rw [hfilt, Real.rpow_one] at hx
  have hev := card_even_Icc ⌈x⌉₊ ⌊x + H⌋₊
  have hc1 : (⌈x⌉₊ : ℝ) < x + 1 := Nat.ceil_lt_add_one hx0
  have hf1 : x + H < (⌊x + H⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
  have hsub : (⌊x + H⌋₊ : ℝ) - ⌈x⌉₊ ≤ ((⌊x + H⌋₊ - ⌈x⌉₊ : ℕ) : ℝ) := by
    rcases le_total ⌈x⌉₊ ⌊x + H⌋₊ with h | h
    · rw [Nat.cast_sub h]
    · rw [Nat.sub_eq_zero_of_le h]
      have : (⌊x + H⌋₊ : ℝ) ≤ ⌈x⌉₊ := by exact_mod_cast h
      simp only [Nat.cast_zero]; linarith
  have hev' : ((⌊x + H⌋₊ - ⌈x⌉₊ : ℕ) : ℝ) ≤
      2 * (((Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).filter Even).card : ℝ) + 1 := by exact_mod_cast hev
  have hLpos : 0 < Real.log x := by linarith
  rw [lt_div_iff₀ hLpos] at hx
  set n := (((Finset.Icc ⌈x⌉₊ ⌊x + H⌋₊).filter Even).card : ℝ)
  -- n ≥ (H - 3)/2 and n ℒ < H with ℒ ≥ 4, H ≥ 8
  have hn : H - 3 ≤ 2 * n := by linarith
  nlinarith

/-- QUESTION 2, CONDITIONAL ON `PrimesInShortIntervals`: the sealed statement
`Thm2.Theorem2Paper` is false as formalized, because it allows u = v = 0. Take B = 0; for
every ε₀ > 0 the value ε = min (ε₀/2) (1/8) lies in the window and `not_theorem2` applies.
PROVED from the cited input. -/
theorem not_theorem2Paper (hP : PrimesInShortIntervals) : ¬ Theorem2Paper := by
  intro h
  obtain ⟨ε₀, hε₀, hε⟩ := h 0
  have hpos : 0 < min (ε₀ / 2) (1 / 8) := lt_min (by linarith) (by norm_num)
  exact not_theorem2 hP (min (ε₀ / 2) (1 / 8)) hpos
    (lt_of_le_of_lt (min_le_right _ _) (by norm_num))
    (hε _ hpos (lt_of_le_of_lt (min_le_left _ _) (by linarith)))

/-! ### The proposed fix, a NEW def -/

/-- Proposed fix for QUESTION 2, a NEW def, no existing statement changed: Theorem 2 of
page 3 with the paper's standing assumption that u and v are positive constants, page 2
display 1.5, added as hypotheses 0 < u and 0 < v. -/
def Theorem2Pos (ε B : ℝ) : Prop :=
  Theorem2With ε B (fun a b u v _ => 0 < u → 0 < v → Conclusion ε a b u v)

/-- The positive form is weaker than `Thm2.Theorem2`. PROVED. -/
theorem theorem2Pos_of_theorem2 {ε B : ℝ} (h : Theorem2 ε B) : Theorem2Pos ε B :=
  theorem2With_mono (fun _ _ _ _ _ hc _ _ => hc) ((theorem2_iff_with ε B).mp h)

/-- The positive form of Theorem 2 in the window of ε, from the OPEN leaf
`Section2MS.section2_mean_square` through `theorem2_paper_nondegenerate`. PROVED from the
leaf; CONDITIONAL on it. -/
theorem theorem2Pos_paper_of_leaf :
    ∀ B : ℝ, ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ ε : ℝ, 0 < ε → ε < ε₀ → Theorem2Pos ε B := by
  intro B
  obtain ⟨ε₀, hε₀, h⟩ := theorem2_paper_nondegenerate B
  refine ⟨ε₀, hε₀, fun ε hε hεε => ?_⟩
  exact theorem2With_mono (fun _ _ u v _ hc hu hv => hc (mul_ne_zero hu.ne' hv.ne'))
    (h ε hε hεε)

end LeanLab.BHP1997.Section2Q2
