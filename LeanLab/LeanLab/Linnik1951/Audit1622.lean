/-
Audit1622, unit U-1622. Lean refutations and implications for three dead splits of P0093.
AI wrote the Lean code. Binary Goldbach is open.

not_leafLocalMass has a written proof with no analytic input beyond the Chebyshev bound of
Mathlib. Status at return of U-1622: UNBUILT, not yet PROVED, check the build log first.
It refutes the conclusion of local_prime_mass357 at q equal to 2 and a equal to 1.
not_farSup_of_peak is CONDITIONAL on the named input FarPeak1622, which is the peak of
page 155 equation 2.3 at the rational 1 over 3 m and needs primes in progressions.
near_negative_of_positive shows that near_negative_sup357 adds nothing to near_positive_sup357.
-/
import LeanLab.Linnik1951.SPLIT_exceptional_prime_mass357
import LeanLab.Linnik1951.SPLIT_mellin_near357
import LeanLab.Linnik1951.SPLIT_mellin_positive_far357
import Mathlib.NumberTheory.Chebyshev

namespace LeanLab.Linnik1951.Audit1622

open MeasureTheory Filter Asymptotics
open scoped Topology

/-- The conclusion of local_prime_mass357, as a Prop. -/
def LeafLocalMass : Prop :=
  ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
    ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
      ∀ a : ℤ, ¬ ((q : ℤ) ∣ a) →
        (∫ α in Set.Icc ((a : ℝ) / (q : ℝ) - 1 / ((q : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))))
            ((a : ℝ) / (q : ℝ) + 1 / ((q : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ)))),
          ‖primeFourier111 N α‖ ^ 2) ≤
        B * (N : ℝ) / ((q : ℝ) * ((N : ℝ) ^ (1 / 7 : ℝ))) * Real.log (N : ℝ) ^ 13

/-- local_prime_mass357 has exactly the type GRH implies LeafLocalMass. -/
example : LeanLab.DERZ1997.GRH → LeafLocalMass := local_prime_mass357

/-- At an odd integer the half phase flips the sign of the cosine. -/
theorem cos_half_phase {p : ℕ} (hp : Odd p) (z : ℝ) :
    Real.cos (2 * Real.pi * (1 / 2 + z) * (p : ℝ)) =
      - Real.cos (2 * Real.pi * z * (p : ℝ)) := by
  obtain ⟨j, rfl⟩ := hp
  have h : 2 * Real.pi * (1 / 2 + z) * (((2 * j + 1 : ℕ)) : ℝ) =
      (2 * Real.pi * z * (((2 * j + 1 : ℕ)) : ℝ) + Real.pi) + (j : ℝ) * (2 * Real.pi) := by
    push_cast; ring
  rw [h, Real.cos_add_nat_mul_two_pi, Real.cos_add_pi]

/-- The tail series with ratio exp of minus one over 2 N sums to at most 8 N. -/
theorem half_damping_tsum (N : ℕ) (hN : 1 ≤ N) :
    Summable (fun n : ℕ => Real.exp (-(n : ℝ) / (2 * N))) ∧
      (∑' n : ℕ, Real.exp (-(n : ℝ) / (2 * N))) ≤ 8 * N := by
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hr : Real.exp (-1 / (2 * (N : ℝ))) < 1 :=
    Real.exp_lt_one_iff.mpr (div_neg_of_neg_of_pos (by norm_num) (by positivity))
  have heq : (fun n : ℕ => Real.exp (-(n : ℝ) / (2 * N))) =
      fun n : ℕ => Real.exp (-1 / (2 * (N : ℝ))) ^ n := by
    funext n
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [heq]
  refine ⟨summable_geometric_of_lt_one (Real.exp_pos _).le hr, ?_⟩
  rw [tsum_geometric_of_lt_one (Real.exp_pos _).le hr]
  have h := exponential_denominator111 (4 * (N : ℝ))
    (by have : (1 : ℝ) ≤ N := by exact_mod_cast hN
        linarith)
  have he : (-2 / (4 * (N : ℝ))) = -1 / (2 * (N : ℝ)) := by
    field_simp
    ring
  rw [he, one_div] at h
  have : (1 - Real.exp (-1 / (2 * (N : ℝ))))⁻¹ ≤ 2 * (4 * (N : ℝ)) := h
  linarith

/-- The lower bound for the prime series on a window about one half. The only
input is the elementary phase bound and the geometric tail. -/
theorem half_arc_lower (N : ℕ) (hN : 1 ≤ N) (L M : ℕ) (hM : M = 2 * N * L)
    (hL : (N : ℝ) * Real.exp (-(L : ℝ)) ≤ 1) (z : ℝ)
    (hz : |z| ≤ 1 / (8 * (M : ℝ))) (hMpos : 0 < M) :
    ((Nat.primeCounting N : ℝ) - 1) * (Real.exp (-1) / 2) - 9 ≤
      ‖primeFourier111 N (1 / 2 + z)‖ := by
  classical
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hMp : (0 : ℝ) < M := by exact_mod_cast hMpos
  set α : ℝ := 1 / 2 + z with hα
  set c : ℕ → ℝ := fun n => Real.exp (-(n : ℝ) / N) with hc
  have hcpos : ∀ n, 0 < c n := fun n => Real.exp_pos _
  -- real parts over the naturals
  let G : ℕ → ℝ := fun n =>
    if n.Prime then -(c n * Real.cos (2 * Real.pi * α * (n : ℝ))) else 0
  let E : ℕ → ℝ := fun n => Real.exp (-(n : ℝ) / (2 * N))
  let Bd : ℕ → ℝ := fun n => (if n = 2 then 1 else 0) + Real.exp (-(L : ℝ)) * E n
  obtain ⟨hEs, hEt⟩ := half_damping_tsum N hN
  have hcs : Summable c := damping_summable111 N hN
  have hGs : Summable G := by
    refine Summable.of_norm_bounded hcs ?_
    intro n
    by_cases hn : n.Prime
    · simp only [G, if_pos hn, norm_neg, norm_mul, Real.norm_eq_abs, abs_of_pos (hcpos n)]
      exact mul_le_of_le_one_right (hcpos n).le (Real.abs_cos_le_one _)
    · simp only [G, if_neg hn, norm_zero]
      exact (hcpos n).le
  have hsingle : Summable (fun n : ℕ => (if n = 2 then (1 : ℝ) else 0)) :=
    summable_of_ne_finset_zero (s := {2}) (fun n hn => by
      simp only [Finset.mem_singleton] at hn
      simp [hn])
  have hBs : Summable Bd := hsingle.add (hEs.mul_left _)
  have hBt : (∑' n, Bd n) ≤ 9 := by
    have h1 : (∑' n : ℕ, (if n = 2 then (1 : ℝ) else 0)) = 1 := by
      rw [tsum_eq_single 2 (fun n hn => by simp [hn])]
      simp
    have h2 : (∑' n, Real.exp (-(L : ℝ)) * E n) ≤ 8 := by
      rw [tsum_mul_left]
      have := mul_le_mul_of_nonneg_left hEt (Real.exp_pos (-(L : ℝ))).le
      calc _ ≤ Real.exp (-(L : ℝ)) * (8 * (N : ℝ)) := this
        _ = 8 * ((N : ℝ) * Real.exp (-(L : ℝ))) := by ring
        _ ≤ 8 := by linarith
    calc (∑' n, Bd n) = 1 + ∑' n, Real.exp (-(L : ℝ)) * E n := by
          simp only [Bd]
          rw [Summable.tsum_add hsingle (hEs.mul_left _), h1]
      _ ≤ 9 := by linarith
  -- cosine lower bound for small phase
  have hcos : ∀ n : ℕ, n ≤ M → (1 / 2 : ℝ) ≤ Real.cos (2 * Real.pi * z * (n : ℝ)) := by
    intro n hn
    have hnr : (n : ℝ) ≤ M := by exact_mod_cast hn
    have hy : |2 * Real.pi * z * (n : ℝ)| ≤ 1 := by
      have hpi := Real.pi_lt_d2
      have hpi0 := Real.pi_pos
      rw [show 2 * Real.pi * z * (n : ℝ) = (2 * Real.pi * (n : ℝ)) * z by ring, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ 2 * Real.pi * (n : ℝ))]
      calc 2 * Real.pi * (n : ℝ) * |z| ≤ 2 * Real.pi * (M : ℝ) * (1 / (8 * (M : ℝ))) := by
            gcongr
        _ = Real.pi / 4 := by field_simp; ring
        _ ≤ 1 := by linarith
    have h := Real.one_sub_sq_div_two_le_cos (x := 2 * Real.pi * z * (n : ℝ))
    have hsq : (2 * Real.pi * z * (n : ℝ)) ^ 2 ≤ 1 := by
      have := sq_abs (2 * Real.pi * z * (n : ℝ))
      nlinarith [abs_nonneg (2 * Real.pi * z * (n : ℝ))]
    linarith
  -- prime odd term
  have hodd : ∀ n : ℕ, n.Prime → n ≠ 2 → n ≤ M → c n / 2 ≤ G n := by
    intro n hn h2 hnM
    have ho : Odd n := hn.odd_of_ne_two h2
    simp only [G, if_pos hn]
    rw [hα, cos_half_phase ho z]
    have := hcos n hnM
    nlinarith [hcpos n]
  -- the tail comparison
  have hE : ∀ n : ℕ, M < n → c n ≤ Real.exp (-(L : ℝ)) * E n := by
    intro n hn
    have hnr : (M : ℝ) < n := by exact_mod_cast hn
    have hMr : (M : ℝ) = 2 * N * L := by rw [hM]; push_cast; ring
    simp only [c, E]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hd : (L : ℝ) ≤ (n : ℝ) / (2 * N) := by
      rw [le_div_iff₀ (by positivity)]
      nlinarith
    have e1 : -(n : ℝ) / N = -((n : ℝ) / (2 * N)) - (n : ℝ) / (2 * N) := by
      field_simp
      ring
    have e2 : -(n : ℝ) / (2 * N) = -((n : ℝ) / (2 * N)) := by ring
    rw [e1, e2]
    linarith
  let s : Finset ℕ := (Finset.range (N + 1)).filter (fun n => n.Prime ∧ n ≠ 2)
  have hNM : N ≤ M := by
    rcases Nat.eq_zero_or_pos L with h0 | h0
    · subst h0; simp at hM; omega
    · rw [hM]; nlinarith
  have hnonneg : ∀ n, n ∉ s → 0 ≤ G n + Bd n := by
    intro n _
    have hBd0 : 0 ≤ Bd n := by
      simp only [Bd]
      have : 0 ≤ Real.exp (-(L : ℝ)) * E n := by positivity
      split_ifs <;> linarith
    by_cases hp : n.Prime
    · by_cases h2 : n = 2
      · subst h2
        have hG2 : -(c 2) ≤ G 2 := by
          simp only [G, if_pos hp]
          have := Real.cos_le_one (2 * Real.pi * α * ((2 : ℕ) : ℝ))
          nlinarith [hcpos 2]
        have hc2 : c 2 ≤ 1 := by
          simp only [c]
          apply Real.exp_le_one_iff.mpr
          exact div_nonpos_of_nonpos_of_nonneg (by norm_num) hNp.le
        have hB2 : 1 ≤ Bd 2 := by
          simp only [Bd, if_true]
          have : 0 ≤ Real.exp (-(L : ℝ)) * E 2 := by positivity
          linarith
        linarith
      · by_cases hnM : n ≤ M
        · have := hodd n hp h2 hnM
          have := hcpos n
          linarith
        · have hlt : M < n := by omega
          have hG : -(c n) ≤ G n := by
            simp only [G, if_pos hp]
            have := Real.cos_le_one (2 * Real.pi * α * (n : ℝ))
            nlinarith [hcpos n]
          have hB : Real.exp (-(L : ℝ)) * E n ≤ Bd n := by
            simp only [Bd]
            split_ifs <;> linarith
          linarith [hE n hlt]
    · simp only [G, if_neg hp, zero_add]
      exact hBd0
  have hsum := (hGs.add hBs).sum_le_tsum s hnonneg
  rw [Summable.tsum_add hGs hBs] at hsum
  have hlower : ((s.card : ℝ)) * (Real.exp (-1) / 2) ≤ ∑ n ∈ s, (G n + Bd n) := by
    rw [← nsmul_eq_mul]
    apply Finset.card_nsmul_le_sum
    intro n hn
    have hn' := Finset.mem_filter.mp hn
    have hnN : n ≤ N := by have := Finset.mem_range.mp hn'.1; omega
    have hg := hodd n hn'.2.1 hn'.2.2 (hnN.trans hNM)
    have hce : Real.exp (-1) ≤ c n := by
      simp only [c]
      apply Real.exp_le_exp.mpr
      have hnr : (n : ℝ) ≤ N := by exact_mod_cast hnN
      rw [le_div_iff₀ hNp]
      linarith
    have hBd0 : 0 ≤ Bd n := by
      simp only [Bd]
      have : 0 ≤ Real.exp (-(L : ℝ)) * E n := by positivity
      split_ifs <;> linarith
    linarith
  have hcard : (Nat.primeCounting N : ℝ) - 1 ≤ s.card := by
    have hsub : (Finset.range (N + 1)).filter Nat.Prime ⊆ insert 2 s := by
      intro n hn
      have hn' := Finset.mem_filter.mp hn
      by_cases h2 : n = 2
      · simp [h2]
      · exact Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨hn'.1, hn'.2, h2⟩)
    have h1 := (Finset.card_le_card hsub).trans (Finset.card_insert_le _ _)
    have h2 : Nat.primeCounting N = ((Finset.range (N + 1)).filter Nat.Prime).card := by
      simp only [Nat.primeCounting, Nat.primeCounting', Nat.count_eq_card_filter_range]
    rw [h2]
    have h3 : (((Finset.range (N + 1)).filter Nat.Prime).card : ℝ) ≤ s.card + 1 := by
      exact_mod_cast h1
    linarith
  -- identify the real part
  have hre : (primeFourier111 N α).re = -(∑' n, G n) := by
    have hsS := prime_fourier_summable111 N hN α
    unfold primeFourier111
    rw [Complex.re_tsum hsS, ← tsum_neg]
    have hinj : Function.Injective (fun p : Nat.Primes => (p : ℕ)) := Nat.Primes.coe_nat_injective
    have hsupp : Function.support (fun n => -G n) ⊆ Set.range (fun p : Nat.Primes => (p : ℕ)) := by
      intro n hn
      by_cases hp : n.Prime
      · exact ⟨⟨n, hp⟩, rfl⟩
      · exact absurd (by simp [G, hp] : (fun n => -G n) n = 0) hn
    rw [← hinj.tsum_eq hsupp]
    apply tsum_congr
    intro p
    simp only [G, if_pos p.2, neg_neg]
    rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, Real.cos_neg]
  have hnorm : -(primeFourier111 N α).re ≤ ‖primeFourier111 N α‖ :=
    (neg_le_abs _).trans (Complex.abs_re_le_norm _)
  rw [hre, neg_neg] at hnorm
  have he0 : 0 ≤ Real.exp (-1) / 2 := by positivity
  have hstep : ((Nat.primeCounting N : ℝ) - 1) * (Real.exp (-1) / 2) ≤
      (s.card : ℝ) * (Real.exp (-1) / 2) := mul_le_mul_of_nonneg_right hcard he0
  linarith

/-- Eventual size facts for the final comparison, on the natural numbers. -/
theorem eventual_facts (B : ℝ) (hB : 0 < B) :
    ∀ᶠ N : ℕ in atTop,
      1 ≤ Real.log N ∧ 240 * Real.log N ≤ (N : ℝ) ∧ (2 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) ∧
      Real.log ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) / 10 ∧
      6912 * B * Real.log N ^ 16 < (N : ℝ) ^ (1 / 7 : ℝ) := by
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have h1 : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp hcast).eventually_ge_atTop 1
  have hlog : ∀ c : ℝ, 0 < c → ∀ᶠ x : ℝ in atTop, Real.log x ≤ c * x := by
    intro c hc
    have := Real.isLittleO_log_id_atTop.bound hc
    filter_upwards [this, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    simpa [Real.norm_eq_abs, abs_of_pos (Real.log_pos hx1), abs_of_pos (by linarith : 0 < x)]
      using hx
  have h2 : ∀ᶠ N : ℕ in atTop, 240 * Real.log N ≤ (N : ℝ) := by
    filter_upwards [hcast.eventually (hlog (1 / 240) (by norm_num))] with N hN
    linarith
  have h3 : ∀ᶠ N : ℕ in atTop, (2 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 7)).comp hcast).eventually_ge_atTop 2
  have h4 : ∀ᶠ N : ℕ in atTop, Real.log ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) / 10 := by
    have ht : Tendsto (fun N : ℕ => (N : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ hcast
    filter_upwards [ht.eventually (hlog (1 / 10) (by norm_num))] with N hN
    linarith
  have h5 : ∀ᶠ N : ℕ in atTop, 6912 * B * Real.log N ^ 16 < (N : ℝ) ^ (1 / 7 : ℝ) := by
    have hlo := isLittleO_log_rpow_rpow_atTop (16 : ℝ) (by norm_num : (0 : ℝ) < 1 / 7)
    have hb := hlo.bound (show 0 < 1 / (6912 * B + 1) by positivity)
    filter_upwards [hcast.eventually hb, hcast.eventually (eventually_gt_atTop (1 : ℝ))] with N hN hN1
    have hl : 0 < Real.log N := Real.log_pos hN1
    have hp : 0 < (N : ℝ) ^ (1 / 7 : ℝ) := by positivity
    have hpow : Real.log N ^ (16 : ℝ) = Real.log N ^ (16 : ℕ) := by
      exact_mod_cast Real.rpow_natCast (Real.log N) 16
    rw [hpow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp,
      abs_of_pos (by positivity : 0 < Real.log N ^ 16)] at hN
    have hd : 0 < 6912 * B + 1 := by positivity
    have h6 : (6912 * B + 1) * Real.log N ^ 16 ≤ (N : ℝ) ^ (1 / 7 : ℝ) := by
      rw [div_mul_eq_mul_div, one_mul, le_div_iff₀ hd] at hN
      linarith
    have : 0 < Real.log N ^ 16 := by positivity
    nlinarith
  exact h1.and (h2.and (h3.and (h4.and h5))) |>.mono fun N h =>
    ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2⟩

/-- UNBUILT at return of U-1622. The conclusion of local_prime_mass357 is false. Take q equal to 2
and a equal to 1. The prime series near one half has size N over log N on a
window of width 1 over N log N, so the arc about 1 over 2 carries mass of order
N over log cubed N at least, while the leaf allows B N to the six sevenths times
log to the thirteenth. The input is pi_ge of Mathlib, not any prime number theorem
in progressions and not GRH. -/
theorem not_leafLocalMass : ¬ LeafLocalMass := by
  rintro ⟨B, hB, N0, hleaf⟩
  obtain ⟨N, hfacts, hN0⟩ :=
    ((eventual_facts B hB).and (eventually_gt_atTop N0)).exists
  obtain ⟨hl1, hl240, hτ2, hlogs, hfinal⟩ := hfacts
  set ℓ := Real.log N with hℓ
  have hNgt : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h | h
    · subst h; simp [hℓ] at hl1; linarith
    · exact h
  have hNr : (0 : ℝ) < N := by exact_mod_cast hNgt
  have hN1 : 1 ≤ N := hNgt
  have hℓ0 : 0 < ℓ := by linarith
  have hNbig : 240 ≤ (N : ℝ) := by nlinarith
  -- parameters
  set L := Nat.log 2 N + 1 with hLdef
  set M := 2 * N * L with hMdef
  have hLpos : 0 < L := by omega
  have hMpos : 0 < M := by positivity
  have hLe : (N : ℝ) * Real.exp (-(L : ℝ)) ≤ 1 := by
    have h2 : N < 2 ^ L := Nat.lt_pow_succ_log_self (by norm_num) N
    have h2r : (N : ℝ) < 2 ^ L := by exact_mod_cast h2
    have he : (2 : ℝ) ^ L ≤ Real.exp L := by
      rw [show (L : ℝ) = (L : ℝ) * 1 by ring, Real.exp_nat_mul]
      exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) L
    rw [Real.exp_neg, ← div_eq_mul_inv, div_le_one (Real.exp_pos _)]
    linarith
  have hLle : (L : ℝ) ≤ 3 * ℓ := by
    have h1 : (2 : ℝ) ^ (Nat.log 2 N) ≤ N := by
      exact_mod_cast Nat.pow_log_le_self 2 hNgt.ne'
    have h2 := Real.log_le_log (by positivity) h1
    rw [Real.log_pow] at h2
    have hl2 : (1 / 2 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hk : ((Nat.log 2 N : ℕ) : ℝ) ≤ 2 * ℓ := by
      have h0 : (0 : ℝ) ≤ (Nat.log 2 N : ℕ) := Nat.cast_nonneg _
      nlinarith
    simp only [hLdef]
    push_cast
    linarith
  have hMr : (M : ℝ) = 2 * N * L := by simp only [hMdef]; push_cast; ring
  have hMle : (M : ℝ) ≤ 6 * N * ℓ := by rw [hMr]; nlinarith
  set δ : ℝ := 1 / (8 * (M : ℝ)) with hδ
  have hMrpos : (0 : ℝ) < M := by exact_mod_cast hMpos
  have hδpos : 0 < δ := by positivity
  -- prime count
  have hpi : (N : ℝ) / (2 * ℓ) ≤ Nat.primeCounting N := by
    have h := Chebyshev.pi_ge N
    refine le_trans ?_ h
    apply (div_le_div_iff₀ (by positivity) hℓ0).mpr
    have hl2 : (0.69 : ℝ) ≤ Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have : (N : ℝ) * (1 / 2) ≤ (N : ℝ) * Real.log 2 - Real.log ((N : ℝ) + 1) := by
      nlinarith
    nlinarith
  -- pointwise lower bound on the window
  have hX : (N : ℝ) / (24 * ℓ) ≤ ((Nat.primeCounting N : ℝ) - 1) * (Real.exp (-1) / 2) - 9 := by
    have he : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
      rw [Real.exp_neg, ← one_div]
      exact one_div_le_one_div_of_le (Real.exp_pos 1) (Real.exp_one_lt_d9.le.trans (by norm_num))
    have hq : (10 : ℝ) ≤ (N : ℝ) / (24 * ℓ) := by
      rw [le_div_iff₀ (by positivity)]
      linarith
    have hhalf : (N : ℝ) / (2 * ℓ) = 12 * ((N : ℝ) / (24 * ℓ)) := by
      field_simp
      ring
    have hpi2 : 12 * ((N : ℝ) / (24 * ℓ)) ≤ Nat.primeCounting N := by rw [← hhalf]; exact hpi
    set Y := (N : ℝ) / (24 * ℓ)
    have h1 : 0 ≤ (Nat.primeCounting N : ℝ) - 1 := by linarith
    have h2 : ((Nat.primeCounting N : ℝ) - 1) * (1 / 6) ≤
        ((Nat.primeCounting N : ℝ) - 1) * (Real.exp (-1) / 2) :=
      mul_le_mul_of_nonneg_left (by linarith) h1
    linarith
  set Y := (N : ℝ) / (24 * ℓ) with hY
  have hYpos : 0 < Y := by positivity
  have hpoint : ∀ α ∈ Set.Icc ((1 : ℝ) / 2 - δ) (1 / 2 + δ), Y ^ 2 ≤ ‖primeFourier111 N α‖ ^ 2 := by
    intro α hα
    have hz : |α - 1 / 2| ≤ 1 / (8 * (M : ℝ)) := by
      rw [abs_le]
      constructor <;> linarith [hα.1, hα.2]
    have h := half_arc_lower N hN1 L M rfl hLe (α - 1 / 2) hz hMpos
    rw [show (1 / 2 + (α - 1 / 2) : ℝ) = α by ring] at h
    exact pow_le_pow_left₀ hYpos.le (hX.trans h) 2
  -- apply the leaf
  set τ : ℝ := (N : ℝ) ^ (1 / 7 : ℝ) with hτ
  have hτpos : 0 < τ := by positivity
  have hq : ((2 : ℕ) : ℝ) ≤ τ := by simpa using hτ2
  have hleaf' := hleaf N hN0 2 (by norm_num) hq 1 (by norm_num)
  have hA : ((1 : ℤ) : ℝ) / ((2 : ℕ) : ℝ) = 1 / 2 := by norm_num
  rw [hA] at hleaf'
  set ρ : ℝ := 1 / (((2 : ℕ) : ℝ) * τ) with hρ
  have hτN : τ ≤ N := by
    have h := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ N)
      (by norm_num : (1 / 7 : ℝ) ≤ 1)
    rw [Real.rpow_one] at h
    exact h
  have hδρ : δ ≤ ρ := by
    rw [hδ, hρ]
    apply one_div_le_one_div_of_le (by positivity)
    push_cast
    rw [hMr]
    have h1L : (1 : ℝ) ≤ L := by exact_mod_cast hLpos
    nlinarith
  have hcont : Continuous (fun α : ℝ => ‖primeFourier111 N α‖ ^ 2) :=
    (continuous_prime_fourier111 N hN1).norm.pow 2
  have hsub : Set.Icc ((1 : ℝ) / 2 - δ) (1 / 2 + δ) ⊆ Set.Icc ((1 : ℝ) / 2 - ρ) (1 / 2 + ρ) :=
    Set.Icc_subset_Icc (by linarith) (by linarith)
  have hmono : (∫ α in Set.Icc ((1 : ℝ) / 2 - δ) (1 / 2 + δ), ‖primeFourier111 N α‖ ^ 2) ≤
      ∫ α in Set.Icc ((1 : ℝ) / 2 - ρ) (1 / 2 + ρ), ‖primeFourier111 N α‖ ^ 2 :=
    setIntegral_mono_set hcont.integrableOn_Icc
      (ae_of_all _ fun α => by positivity) (ae_of_all _ fun x hx => hsub hx)
  have hconst := setIntegral_ge_of_const_le_real (μ := volume) (measurableSet_Icc)
    (by simp [Real.volume_Icc] : volume (Set.Icc ((1 : ℝ) / 2 - δ) (1 / 2 + δ)) ≠ ⊤)
    hpoint hcont.integrableOn_Icc
  have hvol : volume.real (Set.Icc ((1 : ℝ) / 2 - δ) (1 / 2 + δ)) = 2 * δ := by
    rw [Real.volume_real_Icc_of_le (by linarith)]
    ring
  rw [hvol] at hconst
  -- arithmetic contradiction
  have hkey : 2 * δ * Y ^ 2 ≤ B * (N : ℝ) / (((2 : ℕ) : ℝ) * τ) * ℓ ^ 13 := by
    linarith
  have hδlow : 1 / (48 * (N : ℝ) * ℓ) ≤ δ := by
    rw [hδ]
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  have hlow : (N : ℝ) / (13824 * ℓ ^ 3) ≤ 2 * δ * Y ^ 2 := by
    have : 2 * (1 / (48 * (N : ℝ) * ℓ)) * Y ^ 2 ≤ 2 * δ * Y ^ 2 := by
      gcongr
    refine le_trans (le_of_eq ?_) this
    rw [hY]
    field_simp
    ring
  have hup : B * (N : ℝ) / (((2 : ℕ) : ℝ) * τ) * ℓ ^ 13 < (N : ℝ) / (13824 * ℓ ^ 3) := by
    push_cast
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    have hℓ3 : 0 < ℓ ^ 3 := by positivity
    have hNτ : 0 < (N : ℝ) := hNr
    have : 6912 * B * ℓ ^ 16 * (N : ℝ) * 2 < τ * (N : ℝ) * 2 := by
      have := mul_lt_mul_of_pos_right hfinal (by positivity : 0 < (N : ℝ) * 2)
      linarith
    nlinarith
  linarith

/-- UNBUILT at return of U-1622. If GRH implies LeafLocalMass then GRH fails. So
local_prime_mass357 can be proved only by refuting GRH. -/
theorem leaf_refutes_GRH (h : LeanLab.DERZ1997.GRH → LeafLocalMass) :
    ¬ LeanLab.DERZ1997.GRH := fun hG => not_leafLocalMass (h hG)

/-- The conclusion of far_positive_sup357, as a Prop. -/
def FarSup1622 : Prop :=
  ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
    ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
      ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ α : ℝ,
        4 / (N : ℝ) ≤ α → α ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) →
          ‖characterPrime280 χ N α‖ ^ 2 ≤ C * (N : ℝ) * Real.log N ^ 10

/-- far_positive_sup357 has exactly the type GRH implies FarSup1622. -/
example : LeanLab.DERZ1997.GRH → FarSup1622 := far_positive_sup357

/-- Named input, not proved here. P0093 page 155 equation 2.3 at a over q equal to
1 over 3 m, with the prime number theorem in progressions to modulus 3 m. For
primes m greater than 3 the character sum modulo 3 at phase 1 over 3 m has a peak
of size square root of 3 times N over phi of 3 m log N. Under GRH this follows from
the explicit formula. Numerics at m equal to 11: norm 1.05 times 10 to the 5,
predicted 1.01 times 10 to the 5, square root of N about 4.4 times 10 to the 3. -/
def FarPeak1622 : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ N0 : ℕ, ∃ m : ℕ, 3 < m ∧ m.Prime ∧ N0 < m ^ 7 ∧
    ∃ χ : DirichletCharacter ℂ 3, χ ≠ 1 ∧
      c * (((m ^ 7 : ℕ) : ℝ) ^ (6 / 7 : ℝ)) / Real.log ((m ^ 7 : ℕ) : ℝ) ≤
        ‖characterPrime280 χ (m ^ 7) (1 / (3 * (m : ℝ)))‖

/-- CONDITIONAL on FarPeak1622. The conclusion of far_positive_sup357 fails.
Not proved unconditionally: the lower bound needs primes in progressions to a
modulus of size N to the one seventh. -/
theorem not_farSup_of_peak (hP : FarPeak1622) : ¬ FarSup1622 := by
  rintro ⟨C, hC, N0, hsup⟩
  obtain ⟨c, hc, hpeak⟩ := hP
  have hcast : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hlo := isLittleO_log_rpow_rpow_atTop (12 : ℝ) (by norm_num : (0 : ℝ) < 5 / 7)
  have hb := hlo.bound (show 0 < c ^ 2 / (C + 1) by positivity)
  have hev : ∀ᶠ N : ℕ in atTop, ‖Real.log N ^ (12 : ℝ)‖ ≤
      c ^ 2 / (C + 1) * ‖(N : ℝ) ^ (5 / 7 : ℝ)‖ := hcast.eventually hb
  obtain ⟨N1, hN1⟩ := eventually_atTop.mp
    (hev.and (hcast.eventually (eventually_gt_atTop (3 : ℝ))))
  obtain ⟨m, hm3, _, hmN, χ, hχ, hbound⟩ := hpeak (max N0 N1)
  set N : ℕ := m ^ 7 with hN
  have hmr : (3 : ℝ) < m := by exact_mod_cast hm3
  have hNr : (0 : ℝ) < N := by rw [hN]; positivity
  have hτ : (N : ℝ) ^ (1 / 7 : ℝ) = m := by
    rw [hN]
    push_cast
    rw [← Real.rpow_natCast (m : ℝ) 7, ← Real.rpow_mul (by positivity)]
    norm_num
  have hNbig : (N : ℝ) = (m : ℝ) ^ 7 := by rw [hN]; push_cast; ring
  have hleft : 4 / (N : ℝ) ≤ 1 / (3 * (m : ℝ)) := by
    rw [div_le_div_iff₀ hNr (by positivity), hNbig]
    have : (m : ℝ) ^ 6 ≥ 12 := by
      have : (3 : ℝ) ^ 6 ≤ (m : ℝ) ^ 6 := pow_le_pow_left₀ (by norm_num) hmr.le 6
      linarith
    nlinarith
  have hright : (1 / (3 * (m : ℝ))) ≤ 1 / (((3 : ℕ) : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    rw [hτ]; push_cast; exact le_rfl
  have hup := hsup N (lt_of_le_of_lt (le_max_left _ _) hmN) 3 (by norm_num)
    (by rw [hτ]; push_cast; exact hmr.le) χ hχ _ hleft hright
  obtain ⟨hN2, hN3⟩ := hN1 N (le_trans (le_max_right _ _) (le_of_lt hmN))
  have hl : 0 < Real.log N := Real.log_pos (by linarith)
  have hp57 : 0 < (N : ℝ) ^ (5 / 7 : ℝ) := by positivity
  have hpow : Real.log N ^ (12 : ℝ) = Real.log N ^ (12 : ℕ) := by
    exact_mod_cast Real.rpow_natCast (Real.log N) 12
  rw [hpow, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos hp57,
    abs_of_pos (by positivity : 0 < Real.log N ^ 12)] at hN2
  have hsq := pow_le_pow_left₀ (by positivity) hbound 2
  have hmain : (c * (N : ℝ) ^ (6 / 7 : ℝ) / Real.log N) ^ 2 ≤ C * (N : ℝ) * Real.log N ^ 10 :=
    hsq.trans hup
  have h127 : ((N : ℝ) ^ (6 / 7 : ℝ)) ^ 2 = (N : ℝ) * (N : ℝ) ^ (5 / 7 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hNr.le]
    nth_rewrite 2 [← Real.rpow_one (N : ℝ)]
    rw [← Real.rpow_add hNr]
    norm_num
  rw [div_pow, mul_pow, h127, div_le_iff₀ (by positivity)] at hmain
  have hmain2 : c ^ 2 * (N : ℝ) ^ (5 / 7 : ℝ) ≤ C * Real.log N ^ 12 := by
    have : (N : ℝ) * (c ^ 2 * (N : ℝ) ^ (5 / 7 : ℝ)) ≤ (N : ℝ) * (C * Real.log N ^ 12) := by
      nlinarith
    exact le_of_mul_le_mul_left this hNr
  have h12 : (C + 1) * Real.log N ^ 12 ≤ c ^ 2 * (N : ℝ) ^ (5 / 7 : ℝ) := by
    have hd : 0 < C + 1 := by positivity
    have := mul_le_mul_of_nonneg_left hN2 hd.le
    calc (C + 1) * Real.log N ^ 12 ≤ (C + 1) * (c ^ 2 / (C + 1) * (N : ℝ) ^ (5 / 7 : ℝ)) := this
      _ = _ := by field_simp
  have : 0 < Real.log N ^ 12 := by positivity
  nlinarith

/-- UNBUILT at return of U-1622. The conclusion of near_negative_sup357 follows from the conclusion of
near_positive_sup357 by conjugate reflection, so the two pointwise leaves of the
split are one leaf. The positive leaf implies mellin_near357 by the assembly in
SPLIT_mellin_near357, so that split reduces nothing. -/
theorem near_negative_of_positive
    (h : ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ α : ℝ, 0 ≤ α → α ≤ 4 / (N : ℝ) →
          ‖characterPrime280 χ N α‖ ^ 2 ≤ C * (N : ℝ) / (q : ℝ) * Real.log N ^ 5) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ q : ℕ, 1 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ α : ℝ, -(4 / (N : ℝ)) ≤ α →
          α ≤ 0 →
          ‖characterPrime280 χ N α‖ ^ 2 ≤ C * (N : ℝ) / (q : ℝ) * Real.log N ^ 5 := by
  obtain ⟨C, hC, N0, hp⟩ := h
  refine ⟨C, hC, N0, ?_⟩
  intro N hN q hq hqt χ hχ α h1 h2
  have hstar : star χ ≠ 1 := by
    intro h
    apply hχ
    simpa only [star_star, star_one] using congrArg star h
  have := hp N hN q hq hqt (star χ) hstar (-α) (by linarith) (by linarith)
  have hr := character_norm_reflect357 χ N (-α)
  rw [neg_neg] at hr
  rw [hr]
  exact this

end LeanLab.Linnik1951.Audit1622

#print axioms LeanLab.Linnik1951.Audit1622.not_leafLocalMass
#print axioms LeanLab.Linnik1951.Audit1622.leaf_refutes_GRH
#print axioms LeanLab.Linnik1951.Audit1622.not_farSup_of_peak
#print axioms LeanLab.Linnik1951.Audit1622.near_negative_of_positive
