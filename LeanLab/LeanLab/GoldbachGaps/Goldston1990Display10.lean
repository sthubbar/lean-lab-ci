import LeanLab.GoldbachGaps.Goldston1990Thm6PNT
import LeanLab.GoldbachGaps.Goldston1990Barrier

/-!
# Goldston 1990, display 10 on short windows, PROVED unconditionally

Lab proof, unit U-6450, CLOUD 20261020T1318Z-cloud43, T3 route R-5200, P0030. AI wrote this file.
Known mathematics in substance, Goldston 1984, the paper's reference [4]; the elementary route
here is the lab's own and is almost surely folklore.

Goldston's display 10, cited as `Display10` in `Goldston1990Barrier.lean`, says
`J(N, h) > (1/2 - ε) h N log N` for `1 ≤ h < log^A N`. On the short range `h ≤ (log N)/2`, the
only range the barrier uses, it has a two line proof with no zero of ζ in sight:

* every prime in a window `(m, m + h]` with `m ≥ M` has `log p ≥ log M`, so the window sum
  `X = θ(m + h) - θ(m)` is `0` or at least `log M`, hence `X² ≥ X log M` and
  `(X - h)² ≥ (log M - 2h) X + h²`, `sq_ge_of_window`;
* summing over `M ≤ m < N`, `jsum_ge`, and counting each prime in `h` windows, `sumX_ge` and
  `sumX_le`, gives `J(N, h) ≥ (log M - 2h) S + h² (N - M)` with `S` about `h N`;
* `M = N/T` with `T` large and the lab's prime number theorem `theta_pnt_nat` give
  `J(N, h) ≥ (1/2 - ε) h N log N` uniformly for `1 ≤ h ≤ (log N)/2`: `display10_short`.

So `no_detection_below_log_proved`: the Theorem's certificate `J(N, K) < K² N` fails for every
`1 ≤ K ≤ (1/2 - ε) log N`, with no hypothesis. The Fejér, variance, mean square method of
display 6 cannot see windows shorter than about `log N`, unconditionally. Binary Goldbach needs a
window of length 2 at every even `N`. A map entry for route R-5200, not progress on Goldbach,
which is OPEN.

AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
-/

namespace LeanLab.GoldbachGaps.Goldston1990
open Real Chebyshev Finset

namespace D10
open Thm6

/-- The window sum as a sum of `lp`. -/
lemma win_eq (m : ℕ) : ∀ h : ℕ, θ ((m : ℝ) + h) - θ (m : ℝ) = ∑ a ∈ range h, lp (m + 1 + a)
  | 0 => by simp
  | h + 1 => by
    rw [sum_range_succ, ← win_eq m h]
    have := theta_nat_succ (m + h)
    push_cast at this
    rw [show (m : ℝ) + ((h + 1 : ℕ) : ℝ) = (m + h) + 1 by push_cast; ring, this,
      show m + 1 + h = m + h + 1 by omega]
    ring

lemma win_nonneg (m h : ℕ) : 0 ≤ θ ((m : ℝ) + h) - θ (m : ℝ) := by
  rw [win_eq]; exact sum_nonneg fun a _ => lp_nonneg _

/-- A window above `M` holding a prime has sum at least `log M`, so `X log M ≤ X²`. -/
lemma window_dich {m M h : ℕ} (hM : M ≤ m) :
    (θ ((m : ℝ) + h) - θ (m : ℝ)) * Real.log M ≤
      (θ ((m : ℝ) + h) - θ (m : ℝ)) * (θ ((m : ℝ) + h) - θ (m : ℝ)) := by
  set X := θ ((m : ℝ) + h) - θ (m : ℝ) with hX
  have hX0 : 0 ≤ X := win_nonneg m h
  rcases hX0.lt_or_eq with hpos | hzero
  · apply mul_le_mul_of_nonneg_left _ hX0
    rw [hX, win_eq] at hpos ⊢
    obtain ⟨a, ha, hla⟩ : ∃ a ∈ range h, 0 < lp (m + 1 + a) := by
      by_contra hc
      push_neg at hc
      have : ∑ a ∈ range h, lp (m + 1 + a) ≤ 0 := sum_nonpos hc
      linarith
    have hp : (m + 1 + a).Prime := by
      by_contra hn; simp [Thm6.lp, hn] at hla
    have hle : lp (m + 1 + a) ≤ ∑ a ∈ range h, lp (m + 1 + a) :=
      single_le_sum (fun b _ => lp_nonneg (m + 1 + b)) ha
    have hlog : Real.log M ≤ lp (m + 1 + a) := by
      rw [show Thm6.lp (m + 1 + a) = Real.log ((m + 1 + a : ℕ) : ℝ) by simp [Thm6.lp, hp]]
      rcases Nat.eq_zero_or_pos M with h0 | h0
      · subst h0; simp only [Nat.cast_zero, Real.log_zero]; exact Real.log_natCast_nonneg _
      · exact Real.log_le_log (by exact_mod_cast h0) (by exact_mod_cast (show M ≤ m + 1 + a by omega))
    linarith
  · rw [← hzero]; simp

/-- Termwise: `(X - h)² ≥ (log M - 2h) X + h²` for a window above `M`. -/
lemma sq_ge_of_window {m M h : ℕ} (hM : M ≤ m) :
    (Real.log M - 2 * h) * (θ ((m : ℝ) + h) - θ (m : ℝ)) + (h : ℝ) ^ 2 ≤
      (θ ((m : ℝ) + h) - θ (m : ℝ) - h) ^ 2 := by
  have := window_dich (h := h) hM
  nlinarith

/-- **The elementary lower bound for the discrete `J`.** -/
theorem jsum_ge (N M h : ℕ) (hM1 : 1 ≤ M) (hMN : M ≤ N) :
    (Real.log M - 2 * h) * ∑ m ∈ Ico M N, (θ ((m : ℝ) + h) - θ (m : ℝ)) + (h : ℝ) ^ 2 * (N - M) ≤
      ∑ m ∈ Ico 1 N, (θ ((m : ℝ) + h) - θ (m : ℝ) - h) ^ 2 := by
  have hsub : Ico M N ⊆ Ico 1 N := Ico_subset_Ico_left hM1
  refine le_trans ?_ (sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => sq_nonneg _))
  have hcard : ((Ico M N).card : ℝ) = (N : ℝ) - M := by
    rw [Nat.card_Ico, Nat.cast_sub hMN]
  have e : ∑ m ∈ Ico M N, ((Real.log M - 2 * h) * (θ ((m : ℝ) + h) - θ (m : ℝ)) + (h : ℝ) ^ 2) =
      (Real.log M - 2 * h) * ∑ m ∈ Ico M N, (θ ((m : ℝ) + h) - θ (m : ℝ)) + (h : ℝ) ^ 2 * (N - M) := by
    rw [sum_add_distrib, ← mul_sum, sum_const, nsmul_eq_mul, hcard]; ring
  rw [← e]
  exact sum_le_sum fun m hm => sq_ge_of_window (mem_Ico.mp hm).1

/-- The window sums over `[M, N)` as `h` differences of `θ`. -/
lemma sumX_eq (N M h : ℕ) (hMN : M ≤ N) :
    ∑ m ∈ Ico M N, (θ ((m : ℝ) + h) - θ (m : ℝ)) =
      ∑ a ∈ range h, (θ ((N + a : ℕ) : ℝ) - θ ((M + a : ℕ) : ℝ)) := by
  simp_rw [win_eq]
  rw [sum_comm]
  apply sum_congr rfl
  intro a _
  have hN : N + a = (M + a) + (N - M) := by omega
  rw [hN, show (((M + a) + (N - M) : ℕ) : ℝ) = ((M + a : ℕ) : ℝ) + ((N - M : ℕ) : ℝ) by push_cast; ring,
    win_eq, sum_Ico_eq_sum_range]
  apply sum_congr rfl
  intro b _
  congr 1; omega

lemma sumX_ge (N M h : ℕ) (hMN : M ≤ N) :
    (h : ℝ) * (θ (N : ℝ) - θ ((M + h : ℕ) : ℝ)) ≤ ∑ m ∈ Ico M N, (θ ((m : ℝ) + h) - θ (m : ℝ)) := by
  rw [sumX_eq N M h hMN]
  have : ∀ a ∈ range h, θ (N : ℝ) - θ ((M + h : ℕ) : ℝ) ≤ θ ((N + a : ℕ) : ℝ) - θ ((M + a : ℕ) : ℝ) := by
    intro a ha
    have ha' := mem_range.mp ha
    have h1 : θ (N : ℝ) ≤ θ ((N + a : ℕ) : ℝ) := theta_mono (by exact_mod_cast (show N ≤ N + a by omega))
    have h2 : θ ((M + a : ℕ) : ℝ) ≤ θ ((M + h : ℕ) : ℝ) :=
      theta_mono (by exact_mod_cast (show M + a ≤ M + h by omega))
    linarith
  have := sum_le_sum this
  rwa [sum_const, card_range, nsmul_eq_mul] at this

lemma sumX_le (N M h : ℕ) (hMN : M ≤ N) :
    ∑ m ∈ Ico M N, (θ ((m : ℝ) + h) - θ (m : ℝ)) ≤ (h : ℝ) * θ ((N + h : ℕ) : ℝ) := by
  rw [sumX_eq N M h hMN]
  have : ∀ a ∈ range h, θ ((N + a : ℕ) : ℝ) - θ ((M + a : ℕ) : ℝ) ≤ θ ((N + h : ℕ) : ℝ) := by
    intro a ha
    have ha' := mem_range.mp ha
    have h1 : θ ((N + a : ℕ) : ℝ) ≤ θ ((N + h : ℕ) : ℝ) :=
      theta_mono (by exact_mod_cast (show N + a ≤ N + h by omega))
    have h2 := theta_nonneg ((M + a : ℕ) : ℝ)
    linarith
  have := sum_le_sum this
  rwa [sum_const, card_range, nsmul_eq_mul] at this

/-- The algebra of the final step. -/
lemma alg {J S a h N L c0 δ D : ℝ} (hh : 0 ≤ h) (hN : 0 ≤ N) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hc0 : 0 ≤ c0) (hhL : h ≤ L / 2) (ha : L - c0 - 2 * h ≤ a) (hS1 : h * N * (1 - δ) ≤ S)
    (hS2 : S ≤ h * N * (1 + δ)) (hD : (1 - δ) * N ≤ D) (hJ : a * S + h ^ 2 * D ≤ J) :
    h * N * ((1 / 2 - δ / 2) * L - 2 * c0) ≤ J := by
  have hhN : 0 ≤ h * N := mul_nonneg hh hN
  have hDh : h ^ 2 * ((1 - δ) * N) ≤ h ^ 2 * D := mul_le_mul_of_nonneg_left hD (sq_nonneg h)
  rcases le_or_gt 0 a with ha0 | ha0
  · have haS : a * (h * N * (1 - δ)) ≤ a * S := mul_le_mul_of_nonneg_left hS1 ha0
    have hk : (1 - δ) * (L / 2 - c0) ≤ (1 - δ) * (a + h) :=
      mul_le_mul_of_nonneg_left (by linarith) (by linarith)
    have hk2 : h * N * ((1 - δ) * (L / 2 - c0)) ≤ h * N * ((1 - δ) * (a + h)) :=
      mul_le_mul_of_nonneg_left hk hhN
    have hk3 : h * N * ((1 / 2 - δ / 2) * L - 2 * c0) ≤ h * N * ((1 - δ) * (L / 2 - c0)) :=
      mul_le_mul_of_nonneg_left (by nlinarith) hhN
    nlinarith
  · have haS : a * (h * N * (1 + δ)) ≤ a * S := mul_le_mul_of_nonpos_left hS2 ha0.le
    have hk : (1 / 2 - δ / 2) * L - 2 * c0 ≤ (1 + δ) * a + (1 - δ) * h := by
      have e1 : (1 + δ) * (L - c0 - 2 * h) ≤ (1 + δ) * a := mul_le_mul_of_nonneg_left ha (by linarith)
      have e2 : (1 + 3 * δ) * h ≤ (1 + 3 * δ) * (L / 2) := mul_le_mul_of_nonneg_left hhL (by linarith)
      nlinarith
    have hk2 := mul_le_mul_of_nonneg_left hk hhN
    nlinarith

/-- The prime number theorem for `θ` in relative form. -/
lemma theta_rel {δ : ℝ} (hδ : 0 < δ) : ∃ N1 : ℕ, ∀ n : ℕ, N1 ≤ n → |θ (n : ℝ) - n| ≤ δ * n := by
  obtain ⟨A, C, hA, hC, hθ⟩ := theta_pnt_nat
  set S : ℝ := 2 * C / δ + 1 with hS
  refine ⟨⌈Real.exp (2 * A / δ + 1)⌉₊ + ⌈S ^ 2⌉₊ + 2, fun n hn => ?_⟩
  have hn2 : 2 ≤ n := by omega
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (show 0 < n by omega)
  have hne : Real.exp (2 * A / δ + 1) ≤ n := by
    have := Nat.le_ceil (Real.exp (2 * A / δ + 1))
    have h' : (⌈Real.exp (2 * A / δ + 1)⌉₊ : ℝ) ≤ n := by exact_mod_cast (show _ ≤ n by omega)
    linarith
  have hnS : S ^ 2 ≤ n := by
    have := Nat.le_ceil (S ^ 2)
    have h' : (⌈S ^ 2⌉₊ : ℝ) ≤ n := by exact_mod_cast (show ⌈S ^ 2⌉₊ ≤ n by omega)
    linarith
  have hL : 2 * A / δ + 1 ≤ Real.log n := by
    rw [← Real.log_exp (2 * A / δ + 1)]; exact Real.log_le_log (Real.exp_pos _) hne
  have hLpos : 0 < Real.log n := by have : 0 ≤ 2 * A / δ := by positivity
                                    linarith
  have h1 : A * n / Real.log n ≤ δ / 2 * n := by
    rw [div_le_iff₀ hLpos]
    have : 2 * A ≤ δ * Real.log n := by
      have := (div_le_iff₀ hδ).mp (show 2 * A / δ ≤ Real.log n by linarith)
      linarith
    nlinarith
  have hS0 : 0 ≤ S := by rw [hS]; positivity
  have hsq : S ≤ Real.sqrt n := by rw [← Real.sqrt_sq hS0]; exact Real.sqrt_le_sqrt hnS
  have h2 : C * Real.sqrt n ≤ δ / 2 * n := by
    have hs : 2 * C ≤ δ * Real.sqrt n := by
      have : 2 * C / δ ≤ Real.sqrt n := by linarith
      rw [div_le_iff₀ hδ] at this; linarith
    have hss : Real.sqrt n * Real.sqrt n = n := Real.mul_self_sqrt hnpos.le
    have := mul_le_mul_of_nonneg_right hs (Real.sqrt_nonneg (n : ℝ))
    nlinarith
  have := hθ n hn2
  linarith

end D10

set_option maxHeartbeats 2000000 in
open D10 in
/-- **Display 10 on the short range, PROVED unconditionally.** For every `ε > 0` and all large `N`,
`J(N, h) > (1/2 - ε) h N log N` for every `1 ≤ h ≤ (log N)/2`. -/
theorem display10_short (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 1) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ h : ℕ, 1 ≤ h → (h : ℝ) ≤ Real.log N / 2 →
      (1 / 2 - ε) * h * N * Real.log N < Jg N h := by
  set δ : ℝ := ε / 4 with hδ
  have hδ0 : 0 < δ := by positivity
  obtain ⟨N1, hN1⟩ := theta_rel (δ := δ / 4) (by positivity)
  -- `T` with `4 / δ ≤ T`
  set T : ℕ := ⌈4 / δ⌉₊ + 1 with hT
  have hT1 : (1 : ℝ) ≤ T := by rw [hT]; push_cast; linarith [Nat.cast_nonneg (α := ℝ) ⌈4 / δ⌉₊]
  have hT4 : 4 / δ ≤ T := by rw [hT]; push_cast; linarith [Nat.le_ceil (4 / δ)]
  have hTpos : (0 : ℝ) < T := by linarith
  have hδT : 4 ≤ δ * T := by rw [div_le_iff₀ hδ0] at hT4; linarith
  set c0 : ℝ := Real.log (2 * T) with hc0
  have hc00 : 0 ≤ c0 := Real.log_nonneg (by linarith)
  -- `N` large
  set B : ℝ := Real.exp (8 * c0 / ε + 1) + 4 * T * (T + 1) + 2 * T * Real.log T + 4 with hB
  refine ⟨max N1 ⌈B⌉₊, fun N hN h hh1 hhL => ?_⟩
  have hNB : B ≤ N := le_trans (Nat.le_ceil B) (by exact_mod_cast le_trans (le_max_right _ _) hN)
  have hN1' : N1 ≤ N := le_trans (le_max_left _ _) hN
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hexp0 := Real.exp_pos (8 * c0 / ε + 1)
  have hTT : 0 ≤ 4 * (T : ℝ) * (T + 1) := by positivity
  have hTl : 0 ≤ 2 * (T : ℝ) * Real.log T := by positivity
  have hN4 : (4 : ℝ) ≤ N := by
    have : 0 ≤ 4 * (T : ℝ) * (T + 1) := by positivity
    have : 0 ≤ 2 * (T : ℝ) * Real.log T := by positivity
    linarith
  have hNpos : (0 : ℝ) < N := by linarith
  set L := Real.log N with hL
  have hLbig : 8 * c0 / ε + 1 ≤ L := by
    rw [hL, ← Real.log_exp (8 * c0 / ε + 1)]
    exact Real.log_le_log hexp0 (by linarith)
  have hL0 : 0 < L := by have : 0 ≤ 8 * c0 / ε := by positivity
                         linarith
  have hhR : (1 : ℝ) ≤ h := by exact_mod_cast hh1
  -- `M = N / T`
  set M : ℕ := N / T with hM
  have hTN : T ≤ N := by
    have : (T : ℝ) ≤ N := by
      have : (T : ℝ) ≤ 4 * T * (T + 1) := by nlinarith
      have : 0 ≤ 2 * (T : ℝ) * Real.log T := by positivity
      linarith
    exact_mod_cast this
  have hTn0 : 0 < T := by omega
  have hM1 : 1 ≤ M := by rw [hM]; exact (Nat.one_le_div_iff hTn0).mpr hTN
  have hMN : M ≤ N := Nat.div_le_self N T
  have hMle : (M : ℝ) ≤ N / T := by rw [hM]; exact Nat.cast_div_le
  have hMge : (N : ℝ) / T - 1 ≤ M := by
    have h0 : N < M * T + T := by rw [hM]; exact Nat.lt_div_mul_add hTn0
    have h1 : (N : ℝ) < M * T + T := by exact_mod_cast h0
    rw [div_sub_one hTpos.ne', div_le_iff₀ hTpos]; linarith
  -- log M ≥ L - c0
  have hlogM : L - c0 ≤ Real.log M := by
    have hM2 : (N : ℝ) / (2 * T) ≤ M := by
      have : (N : ℝ) / (2 * T) ≤ N / T - 1 := by
        rw [div_sub_one hTpos.ne', div_le_div_iff₀ (by positivity) hTpos]
        nlinarith
      linarith
    have hpos : 0 < (N : ℝ) / (2 * T) := by positivity
    have := Real.log_le_log hpos hM2
    rw [Real.log_div hNpos.ne' (by positivity)] at this
    rw [hc0]; linarith
  -- h ≤ N / T
  have hhT : (h : ℝ) ≤ N / T := by
    have hlogN : Real.log N ≤ N / T + Real.log T := by
      have := Real.log_le_sub_one_of_pos (show 0 < (N : ℝ) / T by positivity)
      rw [Real.log_div hNpos.ne' hTpos.ne'] at this; linarith
    have : 2 * Real.log T ≤ N / T := by
      rw [le_div_iff₀ hTpos]
      have : 0 ≤ 4 * (T : ℝ) * (T + 1) := by positivity
      nlinarith
    have : L / 2 ≤ N / T := by rw [hL]; linarith
    linarith
  -- the window sum bounds
  have hθN := hN1 N hN1'
  have hθNh := hN1 (N + h) (by omega)
  rw [abs_le] at hθN hθNh
  push_cast at hθNh
  have hθMh : θ ((M + h : ℕ) : ℝ) ≤ Real.log 4 * (2 * (N / T)) := by
    have := theta_le_log4_mul_x (x := ((M + h : ℕ) : ℝ)) (by positivity)
    have hl4 : 0 ≤ Real.log 4 := Real.log_nonneg (by norm_num)
    push_cast at this ⊢
    nlinarith
  have hl4 : Real.log 4 < 1.3863 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; push_cast
    linarith [Real.log_two_lt_d9]
  have hNT : (N : ℝ) / T ≤ δ / 4 * N := by
    rw [div_le_iff₀ hTpos]; nlinarith
  set S := ∑ m ∈ Ico M N, (θ ((m : ℝ) + h) - θ (m : ℝ)) with hSdef
  have hS1 : (h : ℝ) * N * (1 - δ) ≤ S := by
    have h1 := sumX_ge N M h hMN
    have hq : Real.log 4 * (2 * ((N : ℝ) / T)) ≤ 1.3863 * (2 * (δ / 4 * N)) :=
      mul_le_mul hl4.le (by linarith) (mul_nonneg (by norm_num) (div_nonneg hNpos.le hTpos.le)) (by norm_num)
    have : (N : ℝ) * (1 - δ) ≤ θ (N : ℝ) - θ ((M + h : ℕ) : ℝ) := by nlinarith
    have := mul_le_mul_of_nonneg_left this (show (0 : ℝ) ≤ h by linarith)
    linarith
  have hS2 : S ≤ (h : ℝ) * N * (1 + δ) := by
    have h1 := sumX_le N M h hMN
    have hhδ : (h : ℝ) ≤ δ / 4 * N := le_trans hhT hNT
    have hδ1 : δ ≤ 1 / 4 := by rw [hδ]; linarith
    have hq : δ / 4 * ((N : ℝ) + h) ≤ δ / 4 * (N + δ / 4 * N) :=
      mul_le_mul_of_nonneg_left (by linarith) (by positivity)
    have hq2 : δ / 4 * (δ / 4 * (N : ℝ)) ≤ δ / 4 * (1 / 16 * N) :=
      mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
    have : θ ((N + h : ℕ) : ℝ) ≤ N * (1 + δ) := by push_cast; nlinarith
    have := mul_le_mul_of_nonneg_left this (show (0 : ℝ) ≤ h by linarith)
    linarith
  have hD : (1 - δ) * N ≤ (N : ℝ) - M := by nlinarith
  have hJ := jsum_ge N M h hM1 hMN
  rw [← jg_eq_sum (by omega)] at hJ
  have key := alg (J := Jg N h) (S := S) (a := Real.log M - 2 * h) (h := h) (N := N) (L := L) (c0 := c0)
    (δ := δ) (D := (N : ℝ) - M) (by linarith) hNpos.le hδ0.le (by rw [hδ]; linarith) hc00 hhL
    (by linarith) hS1 hS2 hD hJ
  -- (1/2 - δ/2) L - 2 c0 > (1/2 - ε) L
  have hfin : (1 / 2 - ε) * L < (1 / 2 - δ / 2) * L - 2 * c0 := by
    have : 8 * c0 < ε * L := by
      have := (div_le_iff₀ hε).mp (show 8 * c0 / ε ≤ L - 1 by linarith)
      nlinarith
    rw [hδ]; nlinarith
  have hhN : 0 < (h : ℝ) * N := by positivity
  have := mul_lt_mul_of_pos_left hfin hhN
  nlinarith

/-- **The barrier, unconditional.** For large `N` and `1 ≤ K ≤ (1/2 - ε) log N`, the Theorem's
certificate `J(N, K) < K² N` fails. This is `no_detection_below_log` with `Display10` replaced
by `display10_short`. -/
theorem no_detection_below_log_proved (ε : ℝ) (hε : 0 < ε) (hε1 : ε < 1 / 2) :
    ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → ∀ K : ℕ, 1 ≤ K →
      (K : ℝ) ≤ (1 / 2 - ε) * Real.log N → ¬ Jg N K < (K : ℝ) ^ 2 * N := by
  obtain ⟨N0, hN0⟩ := display10_short ε hε (by linarith)
  refine ⟨max N0 2, fun N hN K hK1 hKL => ?_⟩
  have hN2 : (2 : ℝ) ≤ N := by exact_mod_cast le_trans (le_max_right _ _) hN
  have hL0 : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  have hJ := hN0 N (le_trans (le_max_left _ _) hN) K hK1 (by nlinarith)
  exact barrier (Nat.cast_nonneg K) (Nat.cast_nonneg N) hJ.le hKL

end LeanLab.GoldbachGaps.Goldston1990
