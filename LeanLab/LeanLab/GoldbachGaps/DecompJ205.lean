import LeanLab.GoldbachGaps.Goldston1990Cor1
import LeanLab.LZPowersOfTwo.Burst8PNT
import Mathlib
import LeanLab.GoldbachGaps.Goldston1990Main
import LeanLab.GoldbachGaps.Goldston1990Sec5
import LeanLab.GoldbachGaps.Goldston1990Display10
import LeanLab.GoldbachGaps.VarianceTransfer

namespace LeanLab.GoldbachGaps.DecompJ205
open Real Chebyshev Finset Filter Topology
open LeanLab.GoldbachGaps.Goldston1990

lemma fejer_eq (N K : ℕ) (hNK : K ≤ N) :
    fejer N K = ∑ n ∈ Icc (N - K) (N + K), ((K : ℝ) - |(n : ℝ) - N|) * Rg n := by
  unfold fejer
  apply sum_bij (fun j _ => j + N - K)
  case hi =>
    intro a ha
    simp only [mem_range] at ha
    simp only [mem_Icc]
    have h1 : N - K ≤ a + N - K := by omega
    have h2 : a + N - K ≤ N + K := by omega
    exact ⟨h1, h2⟩
  case h =>
    intro a ha
    simp only [mem_range] at ha
    congr 2
    · have h1 : ((a + N - K : ℕ) : ℝ) = (a : ℝ) + (N : ℝ) - (K : ℝ) := by
        have : a + N ≥ K := by omega
        rw [Nat.cast_sub this, Nat.cast_add]
      rw [h1]
      have : (a : ℝ) + (N : ℝ) - (K : ℝ) - (N : ℝ) = (a : ℝ) - (K : ℝ) := by ring
      rw [this]
    · have h1 : N + a - K = a + N - K := by omega
      rw [h1]
  case i_inj =>
    intro a1 ha1 a2 ha2 heq
    omega
  case i_surj =>
    intro b hb
    simp only [mem_Icc] at hb
    use b - (N - K)
    have h1 : N - K ≤ b := hb.1
    have h2 : b ≤ N + K := hb.2
    refine ⟨?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega

/-- `Σ_{|n| ≤ K} R(N + n)` in both spellings, for `K ≤ N`. -/
lemma Rsum_eq_Icc (N K : ℕ) (hKN : K ≤ N) :
    ∑ n ∈ Icc (N - K) (N + K), Rg n = Rsum N K := by
  symm
  unfold Rsum
  apply sum_bij (fun j _ => j + N - K)
  case hi =>
    intro a ha
    simp only [mem_range] at ha
    simp only [mem_Icc]
    omega
  case h =>
    intro a ha
    congr 1
    omega
  case i_inj =>
    intro a1 ha1 a2 ha2 heq
    omega
  case i_surj =>
    intro b hb
    simp only [mem_Icc] at hb
    refine ⟨b - (N - K), ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega

/-- LEAF p. 291, display (7) and the line above it: `S(K) ~ K² N` from the Theorem when
`J(N, K) = o(K² N)`. The range is the Theorem's, `1 ≤ K ≤ N / log³ N`, which also excludes
`K = 0`, where both quotients are `0`. `K → ∞` is needed for the Theorem's `O(K N)` term. It is
implied in the paper: for bounded `K` most `x ≤ N` have no prime in `(x, x + K]`, so `J` is about
`K² N`. -/
theorem leaf_fejer_asymp (K : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ (K N : ℝ) ≤ N / Real.log N ^ 3)
    (hinf : Tendsto K atTop atTop) :
    Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0) →
    Tendsto (fun N : ℕ => fejer N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 1) := by
  intro hJ
  obtain ⟨C, hC, hT⟩ := theorem6_proved
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨N0, hN0⟩ := hT (δ / 3) (by positivity)
  have e1 : ∀ᶠ N : ℕ in atTop, Jg N (K N) / ((K N : ℝ) ^ 2 * N) < δ / 3 :=
    hJ.eventually (Iio_mem_nhds (by positivity))
  have e2 : ∀ᶠ N : ℕ in atTop, C * ((K N : ℝ))⁻¹ < δ / 3 := by
    have h1 : Tendsto (fun N : ℕ => ((K N : ℝ))⁻¹) atTop (nhds 0) :=
      tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.comp hinf)
    have h2 : Tendsto (fun N : ℕ => C * ((K N : ℝ))⁻¹) atTop (nhds (C * 0)) :=
      tendsto_const_nhds.mul h1
    rw [mul_zero] at h2
    exact h2.eventually (Iio_mem_nhds (by positivity))
  have e3 : ∀ᶠ N : ℕ in atTop, N0 ≤ N := eventually_ge_atTop N0
  obtain ⟨M, hM⟩ := eventually_atTop.1 (e1.and (e2.and (e3.and hK)))
  refine ⟨M, fun N hN => ?_⟩
  obtain ⟨h1, h2, h3, h4a, h4b⟩ := hM N hN
  have hKpos : (0 : ℝ) < K N := by exact_mod_cast h4a
  -- the range `1 ≤ K ≤ N / log³ N` forces `N > 1`
  have hq : (1 : ℝ) ≤ (N : ℝ) / Real.log N ^ 3 := le_trans (by exact_mod_cast h4a) h4b
  have hL3 : 0 < Real.log N ^ 3 := by
    rcases lt_trichotomy (Real.log N ^ 3) 0 with h | h | h
    · have hle : (N : ℝ) / Real.log N ^ 3 ≤ 0 :=
        div_nonpos_of_nonneg_of_nonpos (Nat.cast_nonneg N) h.le
      linarith
    · rw [h, div_zero] at h4b
      linarith
    · exact h
  have hlogpos : 0 < Real.log N := by
    by_contra h
    push_neg at h
    exact absurd hL3 (not_lt.mpr ((by decide : Odd 3).pow_nonpos h))
  have hN1 : (1 : ℝ) < N := (Real.log_pos_iff (Nat.cast_nonneg N)).mp hlogpos
  have hNpos : (0 : ℝ) < N := by linarith
  have hD : 0 < (K N : ℝ) ^ 2 * N := by positivity
  rw [Real.dist_eq]
  have hrw : fejer N (K N) / ((K N : ℝ) ^ 2 * N) - 1 =
      (fejer N (K N) - (K N : ℝ) ^ 2 * N) / ((K N : ℝ) ^ 2 * N) := by
    field_simp
  rw [hrw, abs_div, abs_of_pos hD, div_lt_iff₀ hD]
  have hJ' : Jg N (K N) < δ / 3 * ((K N : ℝ) ^ 2 * N) := by
    rwa [div_lt_iff₀ hD] at h1
  have hCK : C * (K N : ℝ) * N < δ / 3 * ((K N : ℝ) ^ 2 * N) := by
    have hm := mul_lt_mul_of_pos_right h2 hD
    have he : C * ((K N : ℝ))⁻¹ * ((K N : ℝ) ^ 2 * N) = C * (K N : ℝ) * N := by
      field_simp
    rwa [he] at hm
  have hT' := hN0 N h3 (K N) h4a h4b
  have heps : δ / 3 * ((K N : ℝ) ^ 2 * N) * 3 = δ * ((K N : ℝ) ^ 2 * N) := by ring
  linarith

/-- PROVED p. 292: `S(K) - S(K - h) ≤ h Σ_{|n| ≤ K} R(N + n)`, so the backward difference quotient
is the lower bound. The old leaf ran the forward difference this way and was false. -/
theorem leaf_sum_R_lower (N K h : ℕ) (hpos : 0 < h) (hK : h ≤ K) (hKN : K ≤ N) :
    (fejer N K - fejer N (K - h)) / (h : ℝ) ≤ ∑ n ∈ Icc (N - K) (N + K), Rg n := by
  rw [Rsum_eq_Icc N K hKN, div_le_iff₀ (by exact_mod_cast hpos), mul_comm]
  exact fejer_diff_lower N K h hK

/-- PROVED p. 292: `h Σ_{|n| ≤ K} R(N + n) ≤ S(K + h) - S(K)`, so the forward difference quotient
is the upper bound. -/
theorem leaf_sum_R_upper (N K h : ℕ) (hpos : 0 < h) (hKN : K ≤ N) :
    ∑ n ∈ Icc (N - K) (N + K), Rg n ≤ (fejer N (K + h) - fejer N K) / (h : ℝ) := by
  rw [Rsum_eq_Icc N K hKN, le_div_iff₀ (by exact_mod_cast hpos), mul_comm]
  exact fejer_diff_upper N K h

/-- The shape of the conclusion of `leaf_sum_R_asymp`, at one `K`: the hypotheses of Corollary 1
give `Σ_{|n| ≤ K} R(N + n) ~ 2 K N`. -/
def SumRAsymp (K : ℕ → ℕ) : Prop :=
  (∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ (K N : ℝ) ≤ N / Real.log N ^ 3) →
    Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0) →
    Tendsto (fun N : ℕ => (∑ n ∈ Icc (N - K N) (N + K N), Rg n) / (2 * (K N : ℝ) * N)) atTop (nhds 1)

/-- LEAF p. 292: `Σ_{|n| ≤ K} R(N + n) ~ 2 K N`, under the Theorem's range and `J(N, K) = o(K² N)`.
OPEN. Q-1610 answered by U-1613: true as stated, by hand, unformalized. J at K only is enough. The
printed differencing needs J at K plus or minus h, which needs a sieve bound `J(M, h) ≪ h² M`. The
better route is the trapezoid leaf in the docstring of `leaf_relabel`, at M = N and M = N - K,
using that J is monotone in its first argument. -/
theorem leaf_sum_R_asymp (K : ℕ → ℕ) : SumRAsymp K := sorry

/-- LEAF p. 292, Corollary 1. OPEN. Q-1610, U-1613: `Corollary1` is true as stated, by hand, but
not by relabeling: the moved centre wants J at K/2, which J at K does not bound. Hypothesis
`h_asymp` is then unused. Route: `∫ (θ(x+K)-θ(x)) (θ(N-x+h)-θ(N-x)) dx` over [1, N] is a trapezoid
sum of R on [N, N+K+h], h = ε K. Its error is at most `√(J(N,K) J(N,h))` by Cauchy, with
`J(N,h) ≪ h²N` from the pair sieve. The edges take the sieve bound for R. -/
theorem leaf_relabel (h_asymp : ∀ K : ℕ → ℕ, SumRAsymp K) : Corollary1 := sorry

theorem assembly_corollary1 : Corollary1 :=
  leaf_relabel leaf_sum_R_asymp

/-- P0030 page 287 display 10: vanishing normalized variance forces K above log N / 4. -/
theorem width_eventually_gt_log (K : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N)
    (hJ : Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0)) :
    ∀ᶠ N : ℕ in atTop, Real.log N / 4 < K N := by
  obtain ⟨N0, hN0⟩ := no_detection_below_log_proved (1 / 4) (by norm_num) (by norm_num)
  have he : ∀ᶠ N : ℕ in atTop,
      Jg N (K N) / ((K N : ℝ) ^ 2 * N) < 1 :=
    hJ.eventually (Iio_mem_nhds (by norm_num))
  filter_upwards [hK, he, eventually_ge_atTop N0, eventually_ge_atTop 1] with N hK1 hJ1 hN hN1
  have hD : 0 < (K N : ℝ) ^ 2 * N := by
    have hk : (0 : ℝ) < K N := by exact_mod_cast hK1
    have hn : (0 : ℝ) < N := by exact_mod_cast hN1
    positivity
  have hJlt : Jg N (K N) < (K N : ℝ) ^ 2 * N := by
    simpa using (div_lt_iff₀ hD).mp hJ1
  by_contra h
  have hc := hN0 N hN (K N) hK1 (by push Not at h; linarith)
  exact hc hJlt

/-- P0030 p. 287 display 10 and p. 292 Fejer asymptotic. An eventually positive natural width with J divided by K squared N tending to zero tends to infinity. -/
theorem width_tendsto_atTop (K : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N)
    (hJ : Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0)) :
    Tendsto K atTop atTop := by
  have he := width_eventually_gt_log K hK hJ
  have hl : Tendsto (fun N : ℕ => Real.log N / 4) atTop atTop :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).atTop_div_const (by norm_num)
  have hk : Tendsto (fun N : ℕ => (K N : ℝ)) atTop atTop :=
    tendsto_atTop_mono' atTop (he.mono fun _ h => h.le) hl
  exact tendsto_atTop.2 fun b => (hk.eventually_ge_atTop (b : ℝ)).mono fun N h => by
    exact_mod_cast h

/-- P0030 p. 292 first display. The Fejer sum divided by K squared N tends to one under the sealed range and variance premises, without an extra growth premise. -/
theorem fejer_asymp_of_variance (K : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ (K N : ℝ) ≤ N / Real.log N ^ 3)
    (hJ : Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => fejer N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 1) := by
  exact leaf_fejer_asymp K hK (width_tendsto_atTop K (hK.mono fun _ h => h.1) hJ) hJ

/-- P0030 p. 292 and U-1613 trapezoid support. The number of a below K with a at most s and s minus a below h is min of K and s plus one, minus the natural difference of s plus one and h. -/
theorem rectangle_fiber_card (K h s : ℕ) :
    ((range K).filter (fun a => a ≤ s ∧ s - a < h)).card =
      min K (s + 1) - (s + 1 - h) := by
  have he : (range K).filter (fun a => a ≤ s ∧ s - a < h) =
      Ico (s + 1 - h) (min K (s + 1)) := by
    ext a
    simp only [mem_filter, mem_range, mem_Ico, lt_min_iff]
    omega
  rw [he, Nat.card_Ico]

/-- P0030 p. 292 and U-1613 trapezoid support. A rectangular double sum of f at a plus b is the single sum of f times the exact trapezoid pair count. -/
theorem rectangle_group (K h : ℕ) (f : ℕ → ℝ) :
    ∑ a ∈ range K, ∑ b ∈ range h, f (a + b) =
      ∑ s ∈ range (K + h),
        ((min K (s + 1) - (s + 1 - h) : ℕ) : ℝ) * f s := by
  have hi : ∀ a ∈ range K, ∑ b ∈ range h, f (a + b) =
      ∑ s ∈ range (K + h), if a ≤ s ∧ s - a < h then f s else 0 := by
    intro a ha
    rw [← sum_filter]
    apply sum_bij (fun b _ => a + b)
    · intro b hb
      simp only [mem_filter, mem_range] at hb ⊢
      have := mem_range.mp ha
      omega
    case h =>
      intro b hb
      simp
    case i_inj =>
      intro b hb c hc he
      omega
    case i_surj =>
      intro s hs
      simp only [mem_filter, mem_range] at hs
      refine ⟨s - a, mem_range.mpr hs.2.2, ?_⟩
      omega
  rw [sum_congr rfl hi]
  rw [sum_comm]
  apply sum_congr rfl
  intro s hs
  rw [← sum_filter, sum_const, nsmul_eq_mul, rectangle_fiber_card]

/-- P0030 p. 292 and U-1613 trapezoid support. Every trapezoid pair count is at most h. -/
theorem trapezoid_weight_le (K h s : ℕ) :
    min K (s + 1) - (s + 1 - h) ≤ h := by
  omega

/-- P0030 p. 292 and U-1613 trapezoid support. The pair count equals h on the plateau where h is at most s plus one and s is below K. -/
theorem trapezoid_weight_plateau (K h s : ℕ) (hhs : h ≤ s + 1) (hsK : s < K) :
    min K (s + 1) - (s + 1 - h) = h := by
  omega

/-- P0030 p. 292 and U-1613 reflected trapezoid support. The centered reflected theta product equals the uncentered product minus both first moment terms plus K h times N minus one. -/
theorem trapezoid_covariance_expansion (N K h : ℕ) (hN : 1 ≤ N) :
    (∑ m ∈ Ico 1 N, (θ ((m : ℝ) + K) - θ m - K) *
      (θ (((N - m : ℕ) : ℝ) + h) - θ (N - m : ℕ) - h)) =
      (∑ m ∈ Ico 1 N, (θ ((m : ℝ) + K) - θ m) * (θ (((N - m : ℕ) : ℝ) + h) - θ (N - m : ℕ))) -
      h * (∑ m ∈ Ico 1 N, (θ ((m : ℝ) + K) - θ m)) - K * (∑ m ∈ Ico 1 N, (θ ((m : ℝ) + h) - θ m)) +
      (K : ℝ) * h * ((N : ℝ) - 1) := by
  let X : ℕ → ℝ := fun m => θ ((m : ℝ) + K) - θ m
  let Y : ℕ → ℝ := fun m => θ ((m : ℝ) + h) - θ m
  change (∑ m ∈ Ico 1 N, (X m - K) * (Y (N - m) - h)) =
    (∑ m ∈ Ico 1 N, X m * Y (N - m)) -
    h * (∑ m ∈ Ico 1 N, X m) - K * (∑ m ∈ Ico 1 N, Y m) +
    (K : ℝ) * h * ((N : ℝ) - 1)
  have hr : ∑ m ∈ Ico 1 N, Y (N - m) = ∑ m ∈ Ico 1 N, Y m := by
    simpa using (Finset.sum_Ico_reflect Y 1 (n := N) (m := N) (by omega))
  simp_rw [sub_mul, mul_sub, sum_sub_distrib]
  simp only [← sum_mul, ← mul_sum, sum_const, Nat.card_Ico, nsmul_eq_mul,
    Nat.cast_sub hN, Nat.cast_one, hr]
  ring

/-- P0030 p. 292 and U-1613 reflected trapezoid support. The reflected covariance divided by K squared N is at most the square root of j times twice j plus two, where j is J divided by K squared N and h is at most K. -/
theorem trapezoid_covariance_normalized_le (N K h : ℕ) (hN : 1 ≤ N)
    (hK : 1 ≤ K) (hhK : h ≤ K) :
    |(∑ m ∈ Ico 1 N, (θ ((m : ℝ) + K) - θ m - K) *
      (θ (((N - m : ℕ) : ℝ) + h) - θ (N - m : ℕ) - h))| / ((K : ℝ) ^ 2 * N) ≤
      Real.sqrt ((Jg N K / ((K : ℝ) ^ 2 * N)) *
        (2 * (Jg N K / ((K : ℝ) ^ 2 * N)) + 2)) := by
  let E : ℝ := (∑ m ∈ Ico 1 N, (θ ((m : ℝ) + K) - θ m - K) *
      (θ (((N - m : ℕ) : ℝ) + h) - θ (N - m : ℕ) - h))
  let D : ℝ := (K : ℝ) ^ 2 * N
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  have hk : (0 : ℝ) < K := by exact_mod_cast hK
  have hD : 0 < D := by dsimp [D]; positivity
  have hJN : 1 ≤ (N : ℝ) := by exact_mod_cast hN
  have hJ : 0 ≤ Jg N K := jg_nonneg hJN _
  have hH : 0 ≤ Jg N h := jg_nonneg hJN _
  have hc : |E| ≤ Real.sqrt (Jg N K) * Real.sqrt (Jg N h) :=
    reflected_window_covariance_le N K h hN
  have hh : Jg N h ≤ 2 * Jg N K + 2 * D := by
    have hs := jg_small_width_le hJN (Nat.cast_nonneg h)
      (show (h : ℝ) ≤ K by exact_mod_cast hhK)
    dsimp [D]
    nlinarith [sq_nonneg (K : ℝ)]
  have hc2 : E ^ 2 ≤ Jg N K * Jg N h := by
    have hs := mul_self_le_mul_self (abs_nonneg E) hc
    simpa only [← sq, sq_abs, mul_pow, Real.sq_sqrt hJ, Real.sq_sqrt hH] using hs
  change |E| / D ≤ Real.sqrt ((Jg N K / D) * (2 * (Jg N K / D) + 2))
  apply Real.le_sqrt_of_sq_le
  rw [div_pow, sq_abs, div_le_iff₀ (sq_pos_of_pos hD)]
  calc E ^ 2 ≤ Jg N K * Jg N h := hc2
       _ ≤ Jg N K * (2 * Jg N K + 2 * D) := mul_le_mul_of_nonneg_left hh hJ
       _ = Jg N K / D * (2 * (Jg N K / D) + 2) * D ^ 2 := by field_simp

/-- P0030 p. 292 and U-1613 reflected trapezoid support. Vanishing normalized variance at K makes the covariance at widths K and any h at most K vanish after division by K squared N. -/
theorem trapezoid_covariance_tendsto_zero (K h : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ h N ≤ K N)
    (hJ : Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => |(∑ m ∈ Ico 1 N, (θ ((m : ℝ) + K N) - θ m - K N) *
      (θ (((N - m : ℕ) : ℝ) + h N) - θ (N - m : ℕ) - h N))| / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0) := by
  have hs : Tendsto (fun N : ℕ => Real.sqrt
      ((Jg N (K N) / ((K N : ℝ) ^ 2 * N)) *
        (2 * (Jg N (K N) / ((K N : ℝ) ^ 2 * N)) + 2))) atTop (nhds 0) := by
    have ht : Tendsto (fun N : ℕ => 2 * (Jg N (K N) / ((K N : ℝ) ^ 2 * N)) + 2)
        atTop (nhds (2 * 0 + 2)) := (hJ.const_mul 2).add_const 2
    simpa using (hJ.mul ht).sqrt
  apply squeeze_zero' (Eventually.of_forall fun N => by positivity) _ hs
  filter_upwards [hK, eventually_ge_atTop 1] with N hk hn
  exact trapezoid_covariance_normalized_le N (K N) (h N) hn hk.1 hk.2

/-- P0030 p. 292 and U-1613 reflected trapezoid support. At a fixed positive fractional width h, the reflected covariance is little o of K h N using only variance at K and the existing crude width comparison. -/
theorem trapezoid_covariance_scaled_tendsto_zero (K h : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ ε * K N ≤ h N ∧ h N ≤ K N)
    (hJ : Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => |(∑ m ∈ Ico 1 N, (θ ((m : ℝ) + K N) - θ m - K N) *
      (θ (((N - m : ℕ) : ℝ) + h N) - θ (N - m : ℕ) - h N))| / ((K N : ℝ) * h N * N)) atTop (nhds 0) := by
  let E : ℕ → ℝ := fun N => (∑ m ∈ Ico 1 N, (θ ((m : ℝ) + K N) - θ m - K N) *
      (θ (((N - m : ℕ) : ℝ) + h N) - θ (N - m : ℕ) - h N))
  have hE : Tendsto (fun N : ℕ => |E N| / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0) :=
    trapezoid_covariance_tendsto_zero K h (hK.mono fun _ hk => ⟨hk.1, hk.2.2⟩) hJ
  have hu : Tendsto (fun N : ℕ => (|E N| / ((K N : ℝ) ^ 2 * N)) / ε) atTop (nhds 0) := by
    simpa using hE.div_const ε
  apply squeeze_zero' (Eventually.of_forall fun N => by positivity) _ hu
  filter_upwards [hK, eventually_ge_atTop 1] with N hk hn
  have hkpos : (0 : ℝ) < K N := by exact_mod_cast hk.1
  have hnpos : (0 : ℝ) < N := by exact_mod_cast hn
  have hD : 0 < (K N : ℝ) ^ 2 * N := by positivity
  have hden : ε * ((K N : ℝ) ^ 2 * N) ≤ (K N : ℝ) * h N * N := by
    have hp := mul_le_mul_of_nonneg_right hk.2.1 (mul_nonneg hkpos.le hnpos.le)
    nlinarith
  calc |E N| / ((K N : ℝ) * h N * N)
      ≤ |E N| / (ε * ((K N : ℝ) ^ 2 * N)) :=
        div_le_div_of_nonneg_left (abs_nonneg _) (mul_pos hε hD) hden
    _ = (|E N| / ((K N : ℝ) ^ 2 * N)) / ε := by ring

/-- P0030 pp. 290 and 292, range bookkeeping. The theorem range K at most N divided by log cubed N implies K divided by N tends to zero. -/
theorem width_div_center_tendsto_zero (K : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, (K N : ℝ) ≤ N / Real.log N ^ 3) :
    Tendsto (fun N : ℕ => (K N : ℝ) / N) atTop (nhds 0) := by
  have hi : Tendsto (fun N : ℕ => (Real.log N)⁻¹ ^ 3) atTop (nhds 0) := by
    simpa using (tendsto_inv_atTop_zero.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)).pow 3
  apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) _ hi
  filter_upwards [hK, eventually_ge_atTop 2] with N hKN hN
  have hn : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hl : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  rw [inv_pow, inv_eq_one_div, div_le_div_iff₀ hn (by positivity)]
  simpa only [one_mul] using (le_div_iff₀ (by positivity : 0 < Real.log N ^ 3)).mp hKN

/-- P0030 p. 290 display 25, first moment evaluation. For eventually positive K with K divided by N tending to zero, the sum of theta increments over integer m from one to N minus one is asymptotic to K N. -/
theorem theta_window_mean_asymp (K : ℕ → ℕ)
    (hK1 : ∀ᶠ N : ℕ in atTop, 1 ≤ K N)
    (hKN : Tendsto (fun N : ℕ => (K N : ℝ) / N) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => (∑ m ∈ Ico 1 N, (θ ((m : ℝ) + K N) - θ m)) /
      ((K N : ℝ) * N)) atTop (nhds 1) := by
  let t : ℕ → ℝ := fun N => θ (N : ℝ)
  let S : ℕ → ℕ → ℝ := fun N k => ∑ m ∈ Ico 1 N, (θ ((m : ℝ) + k) - θ m)
  change Tendsto (fun N : ℕ => S N (K N) / ((K N : ℝ) * N)) atTop (nhds 1)
  let C : ℝ := Real.log 4
  have ht : Tendsto (fun N : ℕ => t N / N) atTop (nhds 1) :=
    LeanLab.LZPowersOfTwo.Burst8P2.theta_div_tendsto_one_p2.comp tendsto_natCast_atTop_atTop
  have ht0 : ∀ N, 0 ≤ t N := fun N => theta_nonneg _
  have htC : ∀ N, t N ≤ C * N := fun N => theta_le_log4_mul_x (by positivity)

  have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hsmall : Tendsto (fun N : ℕ => t (1 + K N) / N) atTop (nhds 0) := by
    have hu : Tendsto (fun N : ℕ => C * ((K N : ℝ) / N + (N : ℝ)⁻¹)) atTop (nhds 0) := by
      simpa using (hKN.add hinv).const_mul C
    apply squeeze_zero' (Eventually.of_forall fun N => div_nonneg (ht0 _) (Nat.cast_nonneg _)) _ hu
    filter_upwards [eventually_ge_atTop 1] with N hn
    have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    calc t (1 + K N) / N ≤ C * (1 + K N) / N :=
           div_le_div_of_nonneg_right (by simpa only [Nat.cast_add, Nat.cast_one] using htC (1 + K N)) (Nat.cast_nonneg N)
         _ = C * ((K N : ℝ) / N + (N : ℝ)⁻¹) := by field_simp <;> ring
  have hlarge : Tendsto (fun N : ℕ => t (N + K N) / N) atTop (nhds 1) := by
    have hc : Tendsto (fun N : ℕ => N + K N) atTop atTop :=
      tendsto_atTop_mono (fun N => Nat.le_add_right N (K N)) tendsto_id
    have hp := (ht.comp hc).mul ((tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (nhds 1)).add hKN)
    have hp' : Tendsto (fun N : ℕ => t (N + K N) / (N + K N) * (1 + (K N : ℝ) / N))
        atTop (nhds 1) := by simpa using hp
    apply hp'.congr'
    filter_upwards [eventually_ge_atTop 1] with N hn
    have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    have hnk0 : (N : ℝ) + K N ≠ 0 := by positivity
    field_simp
  have hlo : Tendsto (fun N : ℕ => t N / N - t (1 + K N) / N) atTop (nhds 1) := by
    simpa using ht.sub hsmall
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' hlo hlarge
  · filter_upwards [hK1, eventually_ge_atTop 1] with N hk hn
    have hk0 : (K N : ℝ) ≠ 0 := by exact_mod_cast (show K N ≠ 0 by omega)
    have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    calc t N / N - t (1 + K N) / N =
           ((K N : ℝ) * (t N - t (1 + K N))) / ((K N : ℝ) * N) := by field_simp
         _ ≤ S N (K N) / ((K N : ℝ) * N) :=
           div_le_div_of_nonneg_right (D10.sumX_ge N 1 (K N) (by omega)) (by positivity)
  · filter_upwards [hK1, eventually_ge_atTop 1] with N hk hn
    have hk0 : (K N : ℝ) ≠ 0 := by exact_mod_cast (show K N ≠ 0 by omega)
    have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    calc S N (K N) / ((K N : ℝ) * N) ≤
           ((K N : ℝ) * t (N + K N)) / ((K N : ℝ) * N) :=
           div_le_div_of_nonneg_right (D10.sumX_le N 1 (K N) (by omega)) (by positivity)
         _ = t (N + K N) / N := by field_simp

/-- P0030 p. 292 and U-1613 trapezoid route, discrete reflected version. The discrete reflected theta product is asymptotic to K h N when K is little o of N, h lies between epsilon K and K, and normalized variance vanishes at K alone. -/
theorem trapezoid_asymp_of_variance (K h : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ ε * K N ≤ h N ∧ h N ≤ K N)
    (hKN : Tendsto (fun N : ℕ => (K N : ℝ) / N) atTop (nhds 0))
    (hJ : Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ =>
      (∑ m ∈ Ico 1 N, (θ ((m : ℝ) + K N) - θ m) *
        (θ (((N - m : ℕ) : ℝ) + h N) - θ (N - m : ℕ))) /
      ((K N : ℝ) * h N * N)) atTop (nhds 1) := by
  let E : ℕ → ℝ := fun N => ∑ m ∈ Ico 1 N,
    (θ ((m : ℝ) + K N) - θ m - K N) *
    (θ (((N - m : ℕ) : ℝ) + h N) - θ (N - m : ℕ) - h N)
  have hha : ∀ᶠ N : ℕ in atTop, 1 ≤ h N := by
    filter_upwards [hK] with N hk
    have hkpos : (0 : ℝ) < K N := by exact_mod_cast hk.1
    have hhpos : (0 : ℝ) < h N := lt_of_lt_of_le (mul_pos hε hkpos) hk.2.1
    have : 0 < h N := by exact_mod_cast hhpos
    omega
  have hhN : Tendsto (fun N : ℕ => (h N : ℝ) / N) atTop (nhds 0) := by
    apply squeeze_zero' (Eventually.of_forall fun N => by positivity) _ hKN
    filter_upwards [hK] with N hk
    exact div_le_div_of_nonneg_right (by exact_mod_cast hk.2.2) (Nat.cast_nonneg N)
  have hkmean := theta_window_mean_asymp K (hK.mono fun _ hk => hk.1) hKN
  have hhmean := theta_window_mean_asymp h hha hhN
  have hcovabs : Tendsto (fun N : ℕ => |E N| / ((K N : ℝ) * h N * N))
      atTop (nhds 0) := trapezoid_covariance_scaled_tendsto_zero K h ε hε hK hJ
  have hcov : Tendsto (fun N : ℕ => E N / ((K N : ℝ) * h N * N)) atTop (nhds 0) := by
    rw [tendsto_zero_iff_norm_tendsto_zero]
    have he : (fun N : ℕ => ‖E N / ((K N : ℝ) * h N * N)‖) =
        (fun N : ℕ => |E N| / ((K N : ℝ) * h N * N)) := by
      funext N
      rw [Real.norm_eq_abs, abs_div, abs_of_nonneg
        (show 0 ≤ (K N : ℝ) * h N * N by positivity)]
    rw [he]
    exact hcovabs
  have hinv : Tendsto (fun N : ℕ => (N : ℝ)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hnratio : Tendsto (fun N : ℕ => ((N : ℝ) - 1) / N) atTop (nhds 1) := by
    have ht : Tendsto (fun N : ℕ => 1 - (N : ℝ)⁻¹) atTop (nhds 1) := by
      simpa using tendsto_const_nhds.sub hinv
    apply ht.congr'
    filter_upwards [eventually_ge_atTop 1] with N hn
    have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
    field_simp
  have ht := ((hcov.add hkmean).add hhmean).sub hnratio
  have ht' : Tendsto (fun N : ℕ =>
      E N / ((K N : ℝ) * h N * N) +
      (∑ m ∈ Ico 1 N, (θ ((m : ℝ) + K N) - θ m)) / ((K N : ℝ) * N) +
      (∑ m ∈ Ico 1 N, (θ ((m : ℝ) + h N) - θ m)) / ((h N : ℝ) * N) -
      ((N : ℝ) - 1) / N) atTop (nhds 1) := by simpa using ht
  apply ht'.congr'
  filter_upwards [hK, hha, eventually_ge_atTop 1] with N hk hh hn
  have hk0 : (K N : ℝ) ≠ 0 := by exact_mod_cast (show K N ≠ 0 by omega)
  have hh0 : (h N : ℝ) ≠ 0 := by exact_mod_cast (show h N ≠ 0 by omega)
  have hn0 : (N : ℝ) ≠ 0 := by exact_mod_cast (show N ≠ 0 by omega)
  dsimp [E]
  rw [trapezoid_covariance_expansion N (K N) (h N) hn]
  field_simp <;> ring

/-- P0030 p. 286 display 5, ordered prime representations. The full convolution of log p on primes equals the weighted ordered representation function R. -/
theorem Rg_eq_prime_convolution (n : ℕ) : Thm6.conv Thm6.lp n = Rg n := by
  unfold Thm6.conv
  rw [sum_range_succ]
  have hz : Thm6.lp n * Thm6.lp (n-n) = 0 := by simp [Thm6.lp]
  rw [hz, add_zero]
  unfold Rg
  apply sum_congr rfl
  intro p hp
  unfold Thm6.lp
  by_cases h1 : p.Prime <;> by_cases h2 : (n-p).Prime <;> simp [h1,h2]

/-- P0030 p. 292 and U-1613 finite trapezoid convolution support. The inner reflected window sum reindexes to the middle interval of the full convolution at N plus a plus b plus two. -/
theorem trapezoid_window_reindex (N a b : ℕ) (F : ℕ → ℝ) :
    ∑ m ∈ Ico 1 N, F (m + 1 + a) * F (N - m + 1 + b) =
      ∑ p ∈ Ico (a + 2) (N + a + 1), F p * F (N + a + b + 2 - p) := by
  apply sum_bij (fun m _ => m + 1 + a)
  case hi =>
    intro m hm
    simp only [mem_Ico] at hm ⊢
    omega
  case i_inj =>
    intro m hm m' hm' he
    omega
  case i_surj =>
    intro p hp
    simp only [mem_Ico] at hp
    refine ⟨p - (a + 1), ?_, ?_⟩
    · simp only [mem_Ico]; omega
    · omega
  case h =>
    intro m hm
    have := mem_Ico.mp hm
    congr 2
    omega

/-- P0030 p. 292 and U-1613 finite trapezoid convolution support. For r at most l at most n plus one, removing the middle interval from a sum whose terms on zero through n lie between zero and B leaves a nonnegative error bounded by the removed index count times B. -/
theorem trapezoid_chunk_error (f : ℕ → ℝ) (n l r : ℕ) (hrl : r ≤ l) (hln : l ≤ n + 1)
    (B : ℝ) (hf : ∀ p < n + 1, 0 ≤ f p ∧ f p ≤ B) :
    0 ≤ (∑ p ∈ range (n + 1), f p) - ∑ p ∈ Ico r l, f p ∧
    (∑ p ∈ range (n + 1), f p) - ∑ p ∈ Ico r l, f p ≤
      ((r : ℝ) + (n + 1 - l : ℕ)) * B := by
  have he : (∑ p ∈ range (n + 1), f p) - ∑ p ∈ Ico r l, f p =
      (∑ p ∈ range r, f p) + ∑ p ∈ Ico l (n + 1), f p := by
    rw [← sum_range_add_sum_Ico f (hrl.trans hln),
      ← sum_Ico_consecutive f hrl hln]
    ring
  rw [he]
  constructor
  · exact add_nonneg
      (sum_nonneg fun p hp => (hf p ((mem_range.mp hp).trans_le (hrl.trans hln))).1)
      (sum_nonneg fun p hp => (hf p (mem_Ico.mp hp).2).1)
  · have h1 : ∑ p ∈ range r, f p ≤ (r : ℝ) * B := by
      calc _ ≤ ∑ p ∈ range r, B := sum_le_sum fun p hp =>
             (hf p ((mem_range.mp hp).trans_le (hrl.trans hln))).2
           _ = _ := by simp
    have h2 : ∑ p ∈ Ico l (n + 1), f p ≤ ((n + 1 - l : ℕ) : ℝ) * B := by
      calc _ ≤ ∑ p ∈ Ico l (n + 1), B := sum_le_sum fun p hp =>
             (hf p (mem_Ico.mp hp).2).2
           _ = _ := by simp
    nlinarith

/-- P0030 p. 290 display 25 and p. 292, U-1613 discrete trapezoid support. For N at least one and coefficients between zero and nonnegative L on zero through N plus K plus h plus two, the full rectangular convolution exceeds the reflected window product by at most K h times K plus h plus two times L squared. -/
theorem trapezoid_convolution_error (N K h : ℕ) (hN : 1 ≤ N) (F : ℕ → ℝ) (L : ℝ)
    (hL : 0 ≤ L) (hF : ∀ p ≤ N + K + h + 2, 0 ≤ F p ∧ F p ≤ L) :
    0 ≤ (∑ a ∈ range K, ∑ b ∈ range h, Thm6.conv F (N + a + b + 2)) -
      (∑ m ∈ Ico 1 N, (∑ a ∈ range K, F (m + 1 + a)) *
        (∑ b ∈ range h, F (N - m + 1 + b))) ∧
    (∑ a ∈ range K, ∑ b ∈ range h, Thm6.conv F (N + a + b + 2)) -
      (∑ m ∈ Ico 1 N, (∑ a ∈ range K, F (m + 1 + a)) *
        (∑ b ∈ range h, F (N - m + 1 + b))) ≤
      (K : ℝ) * h * (K + h + 2) * L ^ 2 := by
  let B : ℝ := (K + h + 2) * L ^ 2
  have hi : ∀ a ∈ range K, ∀ b ∈ range h,
      0 ≤ Thm6.conv F (N + a + b + 2) -
        (∑ m ∈ Ico 1 N, F (m + 1 + a) * F (N - m + 1 + b)) ∧
      Thm6.conv F (N + a + b + 2) -
        (∑ m ∈ Ico 1 N, F (m + 1 + a) * F (N - m + 1 + b)) ≤ B := by
    intro a ha b hb
    have haK := mem_range.mp ha
    have hbh := mem_range.mp hb
    let n := N + a + b + 2
    let f : ℕ → ℝ := fun p => F p * F (n - p)
    have hf : ∀ p < n + 1, 0 ≤ f p ∧ f p ≤ L ^ 2 := by
      intro p hp
      have hpM : p ≤ N + K + h + 2 := by dsimp [n] at hp; omega
      have hqM : n - p ≤ N + K + h + 2 := by dsimp [n]; omega
      obtain ⟨hp0, hpL⟩ := hF p hpM
      obtain ⟨hq0, hqL⟩ := hF (n - p) hqM
      refine ⟨mul_nonneg hp0 hq0, ?_⟩
      exact (mul_le_mul hpL hqL hq0 hL).trans_eq (pow_two L).symm
    have hc := trapezoid_chunk_error f n (N + a + 1) (a + 2) (by omega) (by dsimp [n]; omega) (L ^ 2) hf
    have he := trapezoid_window_reindex N a b F
    change 0 ≤ Thm6.conv F n - (∑ p ∈ Ico (a + 2) (N + a + 1), f p) ∧
      Thm6.conv F n - (∑ p ∈ Ico (a + 2) (N + a + 1), f p) ≤
        ((a + 2 : ℕ) + ((n + 1 - (N + a + 1) : ℕ) : ℝ)) * L ^ 2 at hc
    have hh : n + 1 - (N + a + 1) = b + 2 := by dsimp [n]; omega
    rw [hh] at hc
    change (∑ m ∈ Ico 1 N, F (m + 1 + a) * F (N - m + 1 + b)) =
      ∑ p ∈ Ico (a + 2) (N + a + 1), f p at he
    rw [← he] at hc
    refine ⟨hc.1, hc.2.trans ?_⟩
    dsimp [B]
    have hw : (a : ℝ) + 2 + (b + 2) ≤ K + h + 2 := by
      have haR : (a : ℝ) + 1 ≤ K := by exact_mod_cast haK
      have hbR : (b : ℝ) + 1 ≤ h := by exact_mod_cast hbh
      linarith
    push_cast
    exact mul_le_mul_of_nonneg_right hw (sq_nonneg L)
  have hT : (∑ m ∈ Ico 1 N, (∑ a ∈ range K, F (m + 1 + a)) *
      (∑ b ∈ range h, F (N - m + 1 + b))) =
      ∑ a ∈ range K, ∑ b ∈ range h, ∑ m ∈ Ico 1 N,
        F (m + 1 + a) * F (N - m + 1 + b) := by
    simp_rw [sum_mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro a ha
    rw [sum_comm]
  rw [hT]
  have he : (∑ a ∈ range K, ∑ b ∈ range h, Thm6.conv F (N + a + b + 2)) -
      (∑ a ∈ range K, ∑ b ∈ range h, ∑ m ∈ Ico 1 N,
        F (m + 1 + a) * F (N - m + 1 + b)) =
      ∑ a ∈ range K, ∑ b ∈ range h, (Thm6.conv F (N + a + b + 2) -
        ∑ m ∈ Ico 1 N, F (m + 1 + a) * F (N - m + 1 + b)) := by
    simp_rw [sum_sub_distrib]
  rw [he]
  constructor
  · exact sum_nonneg fun a ha => sum_nonneg fun b hb => (hi a ha b hb).1
  · calc _ ≤ ∑ a ∈ range K, ∑ b ∈ range h, B :=
           sum_le_sum fun a ha => sum_le_sum fun b hb => (hi a ha b hb).2
         _ = (K : ℝ) * h * (K + h + 2) * L ^ 2 := by simp [B]; ring

/-- P0030 p. 290 display 25 and p. 292, U-1613 discrete trapezoid support. For N at least one, the weighted representation rectangle exceeds the discrete theta product by a nonnegative truncation error at most K h times K plus h plus two times log squared of N plus K plus h plus two. -/
theorem prime_trapezoid_edge_bound (N K h : ℕ) (hN : 1 ≤ N) :
    0 ≤ (∑ a ∈ range K, ∑ b ∈ range h, Rg (N + a + b + 2)) -
      (∑ m ∈ Ico 1 N, (θ ((m : ℝ) + K) - θ m) *
        (θ (((N - m : ℕ) : ℝ) + h) - θ (N - m : ℕ))) ∧
    (∑ a ∈ range K, ∑ b ∈ range h, Rg (N + a + b + 2)) -
      (∑ m ∈ Ico 1 N, (θ ((m : ℝ) + K) - θ m) *
        (θ (((N - m : ℕ) : ℝ) + h) - θ (N - m : ℕ))) ≤
      (K : ℝ) * h * (K + h + 2) * Real.log ((N + K + h + 2 : ℕ) : ℝ) ^ 2 := by
  have hc := trapezoid_convolution_error N K h hN Thm6.lp
    (Real.log ((N + K + h + 2 : ℕ) : ℝ))
    (Real.log_natCast_nonneg _) (fun p hp => ⟨Thm6.lp_nonneg p, Thm6.lp_le hp⟩)
  simp_rw [Rg_eq_prime_convolution, ← D10.win_eq] at hc
  exact hc

/-- P0030 p. 292 and U-1613 trapezoid route. The normalized convolution truncation factor tends to zero in the sealed logarithmic range for h at most K. -/
theorem trapezoid_edge_factor_tendsto_zero (K h : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ (K N : ℝ) ≤ N / Real.log N ^ 3)
    (hhK : ∀ᶠ N : ℕ in atTop, h N ≤ K N) :
    Tendsto (fun N : ℕ => ((K N : ℝ) + h N + 2) *
      Real.log ((N + K N + h N + 2 : ℕ) : ℝ) ^ 2 / N) atTop (nhds 0) := by
  have hi : Tendsto (fun N : ℕ => (Real.log N)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hlim : Tendsto (fun N : ℕ => 16 / Real.log N) atTop (nhds 0) := by
    simpa only [div_eq_mul_inv, mul_zero] using hi.const_mul (16 : ℝ)
  apply squeeze_zero' (Eventually.of_forall fun N => by positivity) _ hlim
  filter_upwards [hK, hhK, eventually_ge_atTop 4] with N hk hh hn
  have hnpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hL : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hkN : K N ≤ N := K_le_N (by omega) hk.2
  have hn4 : (4 : ℝ) ≤ N := by exact_mod_cast hn
  have hk1 : (1 : ℝ) ≤ K N := by exact_mod_cast hk.1
  have hhR : (h N : ℝ) ≤ K N := by exact_mod_cast hh
  have hkNR : (K N : ℝ) ≤ N := by exact_mod_cast hkN
  have hM : ((N + K N + h N + 2 : ℕ) : ℝ) ≤ (N : ℝ) ^ 2 := by
    push_cast
    nlinarith [sq_nonneg ((N : ℝ) - 4)]
  have hlog : Real.log ((N + K N + h N + 2 : ℕ) : ℝ) ≤ 2 * Real.log N := by
    calc _ ≤ Real.log ((N : ℝ) ^ 2) := Real.log_le_log (by positivity) hM
         _ = _ := by rw [Real.log_pow]; norm_num
  have hlog0 : 0 ≤ Real.log ((N + K N + h N + 2 : ℕ) : ℝ) := Real.log_natCast_nonneg _
  have hs : Real.log ((N + K N + h N + 2 : ℕ) : ℝ) ^ 2 ≤ 4 * Real.log N ^ 2 := by
    nlinarith [mul_self_le_mul_self hlog0 hlog]
  have hw : (K N : ℝ) + h N + 2 ≤ 4 * K N := by linarith
  have hup : ((K N : ℝ) + h N + 2) *
      Real.log ((N + K N + h N + 2 : ℕ) : ℝ) ^ 2 ≤
      16 * K N * Real.log N ^ 2 := by
    calc _ ≤ (4 * K N) * (4 * Real.log N ^ 2) :=
           mul_le_mul hw hs (sq_nonneg _) (by positivity)
         _ = _ := by ring
  calc _ ≤ 16 * K N * Real.log N ^ 2 / N := div_le_div_of_nonneg_right hup hnpos.le
       _ ≤ 16 / Real.log N := by
         rw [div_le_div_iff₀ hnpos hL]
         have hp := (le_div_iff₀ (by positivity : 0 < Real.log N ^ 3)).mp hk.2
         nlinarith

/-- P0030 p. 292 and U-1613 trapezoid route. For fixed positive epsilon and epsilon K at most h at most K, the rectangular double sum of R at N plus a plus b plus two is asymptotic to K h N under variance at K alone and the sealed size range. -/
theorem rectangle_Rg_asymp_of_variance (K h : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ (K N : ℝ) ≤ N / Real.log N ^ 3)
    (hh : ∀ᶠ N : ℕ in atTop, ε * K N ≤ h N ∧ h N ≤ K N)
    (hJ : Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ => (∑ a ∈ range (K N), ∑ b ∈ range (h N),
      Rg (N + a + b + 2)) / ((K N : ℝ) * h N * N)) atTop (nhds 1) := by
  let T : ℕ → ℝ := fun N => ∑ m ∈ Ico 1 N,
    (θ ((m : ℝ) + K N) - θ m) *
    (θ (((N - m : ℕ) : ℝ) + h N) - θ (N - m : ℕ))
  let Q : ℕ → ℝ := fun N => ∑ a ∈ range (K N), ∑ b ∈ range (h N), Rg (N + a + b + 2)
  have hrange : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ ε * K N ≤ h N ∧ h N ≤ K N := by
    filter_upwards [hK, hh] with N hk hh
    exact ⟨hk.1, hh⟩
  have hT : Tendsto (fun N : ℕ => T N / ((K N : ℝ) * h N * N)) atTop (nhds 1) :=
    trapezoid_asymp_of_variance K h ε hε hrange
      (width_div_center_tendsto_zero K (hK.mono fun _ hk => hk.2)) hJ
  have hf := trapezoid_edge_factor_tendsto_zero K h hK (hh.mono fun _ hn => hn.2)
  have herr : Tendsto (fun N : ℕ => (Q N - T N) / ((K N : ℝ) * h N * N))
      atTop (nhds 0) := by
    apply squeeze_zero' _ _ hf
    · filter_upwards [eventually_ge_atTop 1] with N hn
      exact div_nonneg (prime_trapezoid_edge_bound N (K N) (h N) hn).1 (by positivity)
    · filter_upwards [hrange, eventually_ge_atTop 1] with N hk hn
      have hkpos : (0 : ℝ) < K N := by exact_mod_cast hk.1
      have hhpos : (0 : ℝ) < h N := lt_of_lt_of_le (mul_pos hε hkpos) hk.2.1
      have hnpos : (0 : ℝ) < N := by exact_mod_cast hn
      have hc := (prime_trapezoid_edge_bound N (K N) (h N) hn).2
      calc (Q N - T N) / ((K N : ℝ) * h N * N)
          ≤ ((K N : ℝ) * h N * (K N + h N + 2) *
            Real.log ((N + K N + h N + 2 : ℕ) : ℝ) ^ 2) / ((K N : ℝ) * h N * N) :=
            div_le_div_of_nonneg_right hc (by positivity)
        _ = ((K N : ℝ) + h N + 2) *
            Real.log ((N + K N + h N + 2 : ℕ) : ℝ) ^ 2 / N := by
          field_simp
  have ht : Tendsto (fun N : ℕ => (Q N - T N) / ((K N : ℝ) * h N * N) +
      T N / ((K N : ℝ) * h N * N)) atTop (nhds 1) := by simpa using herr.add hT
  convert ht using 1
  funext N
  dsimp [Q]
  ring

/-- P0030 p. 292 and U-1613 trapezoid route. For fixed positive epsilon and epsilon K at most h at most K, the exact trapezoid weighted sum of R is asymptotic to K h N under the sealed range and variance at K alone. -/
theorem weighted_trapezoid_Rg_asymp (K h : ℕ → ℕ) (ε : ℝ) (hε : 0 < ε)
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ (K N : ℝ) ≤ N / Real.log N ^ 3)
    (hh : ∀ᶠ N : ℕ in atTop, ε * K N ≤ h N ∧ h N ≤ K N)
    (hJ : Tendsto (fun N : ℕ => Jg N (K N) / ((K N : ℝ) ^ 2 * N)) atTop (nhds 0)) :
    Tendsto (fun N : ℕ =>
      (∑ s ∈ range (K N + h N),
        ((min (K N) (s + 1) - (s + 1 - h N) : ℕ) : ℝ) * Rg (N + s + 2)) /
      ((K N : ℝ) * h N * N)) atTop (nhds 1) := by
  have ht := rectangle_Rg_asymp_of_variance K h ε hε hK hh hJ
  convert ht using 1
  funext N
  congr 1
  simpa only [Nat.add_assoc] using
    (rectangle_group (K N) (h N) (fun s => Rg (N + s + 2))).symm

/-- P0030 p. 292, passage from R to r in Corollary 1. The forward weighted sum divided by log squared of N plus K is at most the forward count of ordered prime pairs. -/
theorem rg_interval_ge (N K : ℕ) :
    (∑ n ∈ Icc N (N + K), Rg n) / Real.log (N + K) ^ 2 ≤
      ∑ n ∈ Icc N (N + K), (rg n : ℝ) := by
  rcases eq_or_lt_of_le (sq_nonneg (Real.log (N + K))) with h0 | hpos
  · rw [← h0, div_zero]
    exact sum_nonneg fun _ _ => Nat.cast_nonneg _
  rw [div_le_iff₀ hpos, sum_mul]
  apply sum_le_sum
  intro n hn
  have hb := Rg_le_rg (n := n) (M := N + K) (mem_Icc.mp hn).2
  push_cast at hb
  exact hb

/-- P0030 p. 292, passage from R to r in Corollary 1. For y greater than one, the forward prime pair count is at most the weighted sum divided by log squared y plus two times the product of K plus one and y plus one. -/
theorem rg_interval_le (N K : ℕ) {y : ℝ} (hy : 1 < y) :
    (∑ n ∈ Icc N (N + K), (rg n : ℝ)) ≤
      (∑ n ∈ Icc N (N + K), Rg n) / Real.log y ^ 2 +
        ((K : ℝ) + 1) * (2 * (y + 1)) := by
  calc _ ≤ ∑ n ∈ Icc N (N + K), (Rg n / Real.log y ^ 2 + 2 * (y + 1)) :=
         sum_le_sum fun n _ => rg_le_Rg n hy
       _ = _ := by
         rw [sum_add_distrib, ← sum_div, sum_const, nsmul_eq_mul, Nat.card_Icc]
         have he : N + K + 1 - N = K + 1 := by omega
         rw [he]
         push_cast
         ring

set_option maxHeartbeats 1000000 in
/-- P0030 p. 292, passage from R to r in Corollary 1. In the sealed size range, a forward R asymptotic implies the forward r asymptotic with log squared N removed. -/
theorem rg_interval_asymp_of_Rg (K : ℕ → ℕ)
    (hK : ∀ᶠ N : ℕ in atTop, 1 ≤ K N ∧ (K N : ℝ) ≤ N / Real.log N ^ 3)
    (hR : Tendsto (fun N : ℕ => (∑ n ∈ Icc N (N + K N), Rg n) /
      ((K N : ℝ) * N)) atTop (nhds 1)) :
    Tendsto (fun N : ℕ => (∑ n ∈ Icc N (N + K N), (rg n : ℝ)) /
      ((K N : ℝ) * N / Real.log N ^ 2)) atTop (nhds 1) := by
  let S : ℕ → ℕ → ℝ := fun N k => ∑ n ∈ Icc N (N + k), Rg n
  let T : ℕ → ℕ → ℝ := fun N k => ∑ n ∈ Icc N (N + k), (rg n : ℝ)
  change Tendsto (fun N : ℕ => T N (K N) / ((K N : ℝ) * N / Real.log N ^ 2)) atTop (nhds 1)

  rw [Metric.tendsto_atTop]
  intro δ0 hδ0
  set δ := min δ0 1 with hδdef
  have hδ : 0 < δ := lt_min hδ0 one_pos
  have hδ1 : δ ≤ 1 := min_le_right _ _
  set ε := min (1 / 5 : ℝ) (δ / 10) with hεdef
  have hε : 0 < ε := lt_min (by norm_num) (by positivity)
  have hε5 : ε ≤ 1 / 5 := min_le_left _ _
  have hεδ : ε ≤ δ / 10 := min_le_right _ _
  have aR : Tendsto (fun N : ℕ => S N (K N) / ((K N : ℝ) * N)) atTop (nhds 1) := hR
  rw [Metric.tendsto_atTop] at aR
  obtain ⟨A1, hA1⟩ := aR (δ / 4) (by positivity)
  have tL := Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have eL : ∀ᶠ N : ℕ in atTop, max (max 1 (64 / ε ^ 2)) (max (8 / δ) (48 / δ)) ≤ Real.log N :=
    tL.eventually_ge_atTop _
  have t4 : Tendsto (fun N : ℕ => Real.log N ^ 4 / (1 * (N : ℝ) + 0)) atTop (nhds 0) :=
    (Real.tendsto_pow_log_div_mul_add_atTop 1 0 4 one_ne_zero).comp tendsto_natCast_atTop_atTop
  have e4 : ∀ᶠ N : ℕ in atTop, Real.log N ^ 4 / (1 * (N : ℝ) + 0) < δ / 48 :=
    t4.eventually (Iio_mem_nhds (by positivity))
  have eN : ∀ᶠ N : ℕ in atTop, A1 ≤ N := eventually_ge_atTop A1
  obtain ⟨M, hM⟩ := eventually_atTop.1 (eL.and (e4.and (eN.and (hK.and (eventually_ge_atTop 3)))))
  refine ⟨M, fun N hNM => ?_⟩
  obtain ⟨hLb, h4, hNA, ⟨hK1, hKupper⟩, hN3⟩ := hM N hNM
  set L := Real.log N with hLdef
  have hL1 : 1 ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hLb
  have hL64 : 64 / ε ^ 2 ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hLb
  have hL8 : 8 / δ ≤ L := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hLb
  have hL24 : 48 / δ ≤ L := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hLb
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hkpos : (0 : ℝ) < K N := by exact_mod_cast hK1
  have hKN : (K N : ℝ) ≤ N := by exact_mod_cast K_le_N hN3 hKupper
  have hL0 : 0 < L := by linarith
  -- the R sum
  have hR := hA1 N hNA
  have hD : (0 : ℝ) < K N * N := by positivity
  rw [Real.dist_eq, abs_lt] at hR
  have hRlo : (1 - δ / 4) * (K N * N) ≤ S N (K N) := by
    have := hR.1; rw [lt_sub_iff_add_lt, lt_div_iff₀ hD] at this; nlinarith
  have hRhi : S N (K N) ≤ (1 + δ / 4) * (K N * N) := by
    have := hR.2; rw [sub_lt_iff_lt_add, div_lt_iff₀ hD] at this; nlinarith
  have hδδ : δ ≤ δ0 := min_le_left _ _
  have hL24' : 24 ≤ δ * L := by rw [div_le_iff₀ hδ] at hL24; linarith
  have hR0 : 0 ≤ S N (K N) := le_trans (by nlinarith) hRlo
  rw [show T N (K N) / (K N * N / L ^ 2) = T N (K N) * L ^ 2 / (K N * N) by
    field_simp]
  rw [Real.dist_eq, abs_lt]
  constructor
  · -- lower bound
    have hlog2 : Real.log ((N : ℝ) + K N) ≤ L + 1 := by
      have h2N : (N : ℝ) + K N ≤ 2 * N := by linarith
      have := Real.log_le_log (by positivity) h2N
      rw [Real.log_mul (by norm_num) hNpos.ne'] at this
      have : Real.log 2 ≤ 1 := by have := Real.log_two_lt_d9; linarith
      linarith
    have hlog0 : 0 < Real.log ((N : ℝ) + K N) := by
      have hN1 : (1 : ℝ) < N := by
        by_contra h; push_neg at h
        have : L ≤ 0 := by rw [hLdef]; exact Real.log_nonpos hNpos.le h
        linarith
      exact Real.log_pos (by linarith)
    have hge := rg_interval_ge N (K N)
    have := cor1_lower hδ hδ1 hL1 hL24' hD hRlo hge hlog0 hlog2
    linarith only [this, hδδ]
  · -- upper bound
    set y : ℝ := N / L ^ 4 with hydef
    have hL4 : 0 < L ^ 4 := by positivity
    have h4' : L ^ 4 / N < δ / 48 := by simpa using h4
    have h4'' : L ^ 4 < δ / 48 * N := by rwa [div_lt_iff₀ hNpos] at h4'
    have hy2 : 2 ≤ y := by
      rw [hydef, le_div_iff₀ hL4]; nlinarith
    have hy1 : 1 < y := by linarith
    have hlogy : (1 - ε) * L ≤ Real.log y := by
      rw [hydef, Real.log_div hNpos.ne' hL4.ne', Real.log_pow]
      have hll : Real.log L ≤ 2 * Real.sqrt L := LeanLab.GoldbachAverage.log_le_two_sqrt hL0
      have hL64' : 64 ≤ ε ^ 2 * L := by rw [div_le_iff₀ (by positivity)] at hL64; linarith
      have hsq : 8 ≤ ε * Real.sqrt L := by
        have hsL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
        have h0 : 0 ≤ ε * Real.sqrt L := by positivity
        nlinarith
      have hsL : Real.sqrt L * Real.sqrt L = L := Real.mul_self_sqrt hL0.le
      have : 8 * Real.sqrt L ≤ ε * L := by nlinarith [Real.sqrt_nonneg L]
      push_cast
      linarith
    have hle := rg_interval_le N (K N) hy1
    have hL48' : 24 ≤ (δ / 2) * L := by
      rw [div_le_iff₀ hδ] at hL24
      linarith
    have hEc := cor1_E (k := (K N : ℝ)) (n := (N : ℝ)) (L := L) (δ := δ / 2)
      (y := y) (by exact_mod_cast hK1) hNpos hL1 hL48' (by positivity)
      (by rw [hydef]; field_simp) (by linarith)
    have hE : ((K N : ℝ) + 1) * (2 * (y + 1)) * L ^ 2 ≤ δ / 4 * (K N * N) := by
      calc _ = ((K N : ℝ) + 1) * (2 * (y + 1) * L ^ 2) := by ring
           _ ≤ (2 * K N + 1) * (2 * (y + 1) * L ^ 2) :=
             mul_le_mul_of_nonneg_right (by linarith) (by positivity)
           _ = (2 * K N + 1) * (2 * (y + 1)) * L ^ 2 := by ring
           _ ≤ (δ / 2) / 4 * (2 * K N * N) := hEc
           _ = δ / 4 * (K N * N) := by ring
    have := cor1_upper hδ hδ1 hε hε5 hεδ hL0 hlogy hD hRhi hR0 hle hE
    linarith only [this, hδδ]

/-- P0030 p. 293 display 26, supporting audit of the attempted edge estimate. For every fixed positive epsilon, the square root of epsilon squared plus epsilon log N grows without bound. This is the scalar square mean edge majorant at the logarithmic scale. -/
theorem square_mean_edge_majorant_diverges (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun N : ℕ => Real.sqrt (ε ^ 2 + ε * Real.log N)) atTop atTop := by
  have hl : Tendsto (fun N : ℕ => ε * Real.log N) atTop atTop :=
    Filter.Tendsto.const_mul_atTop hε
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hs : Tendsto (fun N : ℕ => ε ^ 2 + ε * Real.log N) atTop atTop :=
    tendsto_atTop_mono (fun _ => le_add_of_nonneg_left (sq_nonneg ε)) hl
  exact Real.tendsto_sqrt_atTop.comp hs

end LeanLab.GoldbachGaps.DecompJ205
