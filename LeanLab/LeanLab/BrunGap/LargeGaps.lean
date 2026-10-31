/-
I-0055: a positive proportion of the primes below N are followed by a gap longer than c log N.
From the averaged Brun bound `sum_gapCount_le`, pairs (p, p + h) with p < N and h ≤ H number at
most 9 C₀ H N / log² N, and Mathlib's Chebyshev bound `Chebyshev.theta_ge`. With
c = 1/(30 C₀): for all large N, at least N/(4 log N) primes p < N have no prime in
(p, p + c log N]. The mathematics is Erdős 1940; KNOWN. The constant c is tiny, C₀ = 128 + 5·17⁸.
AI-written Lean code, Claude, run 20261017T0903Z-2557. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.BrunGap.Uniform

open Finset Filter Real

namespace LeanLab.BrunGap

/-- Primes `p < N` with a prime in `(p, p + H]`. -/
def badPrimes (N H : ℕ) : Finset ℕ :=
  (range N).filter (fun p => p.Prime ∧ ∃ q ∈ Ioc p (p + H), q.Prime)

/-- Primes `p < N` with no prime in `(p, p + H]`. -/
def goodPrimes (N H : ℕ) : Finset ℕ :=
  (range N).filter (fun p => p.Prime ∧ ∀ q ∈ Ioc p (p + H), ¬ q.Prime)

theorem card_primesBelow_le (N H : ℕ) :
    (Nat.primesBelow N).card ≤ (goodPrimes N H).card + (badPrimes N H).card := by
  have : Nat.primesBelow N ⊆ goodPrimes N H ∪ badPrimes N H := by
    intro p hp
    rw [Nat.primesBelow, mem_filter] at hp
    by_cases h : ∃ q ∈ Ioc p (p + H), q.Prime
    · exact mem_union_right _ (mem_filter.mpr ⟨hp.1, hp.2, h⟩)
    · push Not at h
      exact mem_union_left _ (mem_filter.mpr ⟨hp.1, hp.2, h⟩)
  exact (card_le_card this).trans (card_union_le _ _)

/-- Bad primes are at most `1 + Σ_{h ≤ H even} gapCount h N`. -/
theorem card_bad_le (N H : ℕ) :
    ((badPrimes N H).card : ℝ) ≤ 1 + ∑ h ∈ (Icc 1 H).filter Even, (gapCount h N : ℝ) := by
  have hsub : badPrimes N H ⊆ {2} ∪ ((Icc 1 H).filter Even).biUnion
      (fun h => (range N).filter (fun p => p.Prime ∧ (p + h).Prime)) := by
    intro p hp
    obtain ⟨hpN, hpr, q, hqI, hq⟩ := mem_filter.mp hp
    obtain ⟨hpq, hqH⟩ := mem_Ioc.mp hqI
    by_cases h2 : p = 2
    · exact mem_union_left _ (mem_singleton.mpr h2)
    · apply mem_union_right
      have hpo : Odd p := hpr.odd_of_ne_two h2
      have hq2 : q ≠ 2 := by have := hpr.two_le; omega
      have hqo : Odd q := hq.odd_of_ne_two hq2
      have hev : Even (q - p) := Nat.Odd.sub_odd hqo hpo
      refine mem_biUnion.mpr ⟨q - p, ?_, ?_⟩
      · simp only [mem_filter, mem_Icc]; exact ⟨⟨by omega, by omega⟩, hev⟩
      · simp only [mem_filter]
        exact ⟨hpN, hpr, by rwa [show p + (q - p) = q by omega]⟩
  have h1 := card_le_card hsub
  have h2 := card_union_le ({2} : Finset ℕ) (((Icc 1 H).filter Even).biUnion
      (fun h => (range N).filter (fun p => p.Prime ∧ (p + h).Prime)))
  have h3 := card_biUnion_le (s := (Icc 1 H).filter Even)
      (t := fun h => (range N).filter (fun p => p.Prime ∧ (p + h).Prime))
  rw [card_singleton] at h2
  have : (badPrimes N H).card ≤ 1 + ∑ h ∈ (Icc 1 H).filter Even, gapCount h N := by
    unfold gapCount; omega
  exact_mod_cast this

/-- `θ(N − 1) ≤ π(N − 1) log N`. -/
theorem theta_le_card_mul_log (N : ℕ) (hN : 1 ≤ N) :
    Chebyshev.theta ((N - 1 : ℕ) : ℝ) ≤ (Nat.primesBelow N).card * Real.log N := by
  rw [Chebyshev.theta_eq_sum_primesLE_log]
  have hle : Nat.primesLE (N - 1) = Nat.primesBelow N := by
    unfold Nat.primesLE; rw [show N - 1 + 1 = N by omega]
  rw [hle]
  calc ∑ p ∈ Nat.primesBelow N, Real.log p ≤ ∑ p ∈ Nat.primesBelow N, Real.log N := by
        apply sum_le_sum
        intro p hp
        have hpN : p < N := Nat.lt_of_mem_primesBelow hp
        have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (Nat.prime_of_mem_primesBelow hp).one_lt.le
        exact Real.log_le_log (by linarith) (by exact_mod_cast hpN.le)
    _ = (Nat.primesBelow N).card * Real.log N := by rw [sum_const, nsmul_eq_mul]

/-- The gap constant. -/
noncomputable def cGap : ℝ := 1 / (30 * C₀)

theorem cGap_pos : 0 < cGap := by unfold cGap; have := C₀_pos; positivity

/-- **I-0055, Erdős 1940 type**: for all large `N`, at least `N/(4 log N)` primes `p < N` have no
prime in `(p, p + c log N]`, with `c = 1/(30 C₀)`. -/
theorem many_large_gaps : ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
    (N : ℝ) / (4 * Real.log N) ≤ (goodPrimes N ⌊cGap * Real.log N⌋₊).card := by
  have G1 : ∀ᶠ y : ℝ in atTop, 2 * Real.sqrt y * Real.log y ≤ y / 50 := by
    have h := (isLittleO_log_rpow_atTop (show (0 : ℝ) < 1 / 2 by norm_num)).bound
      (show (0 : ℝ) < 1 / 100 by norm_num)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with y hy hy1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hy1),
      abs_of_nonneg (Real.rpow_nonneg (by linarith) _), ← Real.sqrt_eq_rpow] at hy
    have hs : Real.sqrt y * Real.sqrt y = y := Real.mul_self_sqrt (by linarith)
    have hs0 : 0 ≤ Real.sqrt y := Real.sqrt_nonneg y
    nlinarith
  have G2 : ∀ᶠ y : ℝ in atTop, Real.log y ≤ y / 100 := by
    have h := Real.isLittleO_log_id_atTop.bound (show (0 : ℝ) < 1 / 100 by norm_num)
    filter_upwards [h, eventually_ge_atTop (1 : ℝ)] with y hy hy1
    simp only [Real.norm_eq_abs, id] at hy
    rw [abs_of_nonneg (Real.log_nonneg hy1), abs_of_nonneg (by linarith : (0 : ℝ) ≤ y)] at hy
    linarith
  have G3 : ∀ᶠ y : ℝ in atTop, 1 / cGap ≤ Real.log y :=
    Real.tendsto_log_atTop.eventually_ge_atTop _
  have hev : ∀ᶠ y : ℝ in atTop, 100 ≤ y ∧ 2 * Real.sqrt y * Real.log y ≤ y / 50 ∧
      Real.log y ≤ y / 100 ∧ 1 / cGap ≤ Real.log y :=
    (eventually_ge_atTop 100).and (G1.and (G2.and G3))
  obtain ⟨N0, hN0⟩ := eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨N0, fun N hN => ?_⟩
  obtain ⟨h100, hsq, hlog, hc⟩ := hN0 N hN
  have hN1 : 1 ≤ N := by have : (1 : ℝ) ≤ N := by linarith
                         exact_mod_cast this
  set L := Real.log N with hL
  have hL1 : 1 ≤ L := by
    have := Real.add_one_le_exp 1
    rw [hL, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hL0 : 0 < L := by linarith
  set H := ⌊cGap * L⌋₊ with hH
  have hcpos := cGap_pos
  have hH1 : 1 ≤ H := by
    rw [hH, Nat.one_le_floor_iff]
    have : 1 ≤ cGap * L := by rw [div_le_iff₀ hcpos] at hc; linarith
    exact this
  have hHle : (H : ℝ) ≤ cGap * L := Nat.floor_le (by positivity)
  -- primes below N
  have hθ := Chebyshev.theta_ge (N - 1)
  have hθ2 := theta_le_card_mul_log N hN1
  have hcast : ((N - 1 : ℕ) : ℝ) = N - 1 := by rw [Nat.cast_sub hN1]; simp
  rw [hcast] at hθ hθ2
  have hlog2 : (0.693 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
  have hsqrt : Real.sqrt (N - 1) * Real.log (N - 1) ≤ Real.sqrt N * L := by
    apply mul_le_mul (Real.sqrt_le_sqrt (by linarith)) (Real.log_le_log (by linarith) (by linarith))
      (Real.log_nonneg (by linarith)) (Real.sqrt_nonneg _)
  have hl1 : Real.log (N - 1 + 1) = L := by rw [hL]; ring_nf
  have hpi : 0.6 * (N : ℝ) ≤ (Nat.primesBelow N).card * L := by
    rw [hl1] at hθ
    rw [← hL] at hθ2
    have h693 : (N - 1) * Real.log 2 ≥ (N - 1) * 0.693 := by
      apply mul_le_mul_of_nonneg_left hlog2.le; linarith
    have hs2 : 2 * Real.sqrt (N - 1) * Real.log (N - 1) ≤ (N : ℝ) / 50 := by nlinarith
    linarith
  -- bad primes
  have hbad := card_bad_le N H
  have hsum := sum_gapCount_le H N hH1 (by exact_mod_cast (show (3 : ℝ) ≤ N by linarith))
  rw [← hL] at hsum
  have hC0 := C₀_pos
  have hbad2 : ((badPrimes N H).card : ℝ) ≤ 1 + 0.3 * N / L := by
    have : 9 * C₀ * H * N / L ^ 2 ≤ 0.3 * N / L := by
      rw [div_le_div_iff₀ (by positivity) hL0]
      have h1 : 9 * C₀ * H ≤ 0.3 * L := by
        have : 9 * C₀ * H ≤ 9 * C₀ * (cGap * L) := by
          apply mul_le_mul_of_nonneg_left hHle; positivity
        have e : 9 * C₀ * (cGap * L) = 0.3 * L := by unfold cGap; field_simp; ring
        linarith
      have hNL : 0 ≤ (N : ℝ) * L := by positivity
      have h2 := mul_le_mul_of_nonneg_right h1 hNL
      calc 9 * C₀ * H * N * L = (9 * C₀ * H) * (N * L) := by ring
        _ ≤ (0.3 * L) * (N * L) := h2
        _ = 0.3 * N * L ^ 2 := by ring
    linarith
  have hsplit := card_primesBelow_le (H := H) N
  have hsplit' : ((Nat.primesBelow N).card : ℝ) ≤ (goodPrimes N H).card + (badPrimes N H).card := by
    exact_mod_cast hsplit
  -- assemble
  have hmain : 0.6 * (N : ℝ) / L ≤ (Nat.primesBelow N).card := by
    rw [div_le_iff₀ hL0]; linarith
  have hfin : (N : ℝ) / (4 * L) ≤ 0.3 * (N : ℝ) / L - 1 := by
    have hNL : 4 * L ≤ N := by linarith
    rw [div_le_iff₀ (by positivity)]
    have : (0.3 * (N : ℝ) / L - 1) * (4 * L) = 1.2 * (N : ℝ) - 4 * L := by field_simp; ring
    rw [this]; linarith
  have : 0.3 * (N : ℝ) / L - 1 ≤ (goodPrimes N H).card := by
    have e : 0.6 * (N : ℝ) / L = 0.3 * (N : ℝ) / L + 0.3 * (N : ℝ) / L := by ring
    linarith
  linarith

end LeanLab.BrunGap
