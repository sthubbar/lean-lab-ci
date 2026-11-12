/-
P0070. A. Perelli and J. Pintz, On the exceptional set for the 2k-twin primes problem,
Compositio Math. 82, 1992, pp. 355 to 372, Section 5, pp. 363 and 364.

ROUTE BURST session 9, 2026-11-12. The Parseval cost of the end blocks, the route of
`Decomp1624.reduction27A`, PROVED here as `parseval_cost_proved`; it was first stated as a
leaf in `Burst9Leaves.lean` and is used by `Burst9Main.rpart_block_bound_p3`:

* `gsum_parseval`: Parseval on any interval of length `1` for `Σ_{n ∈ D} c_n e(nα)`, from
  `Common/CircleOrth.parseval_norm`.
* `arc_mult_le`: a point lies on at most `9` of the arcs `|α - a/q| ≤ 1/(qQ)` with
  `M ≤ q ≤ 2M ≤ 2Q` and `(a, q) = 1`, as the fractions are `1/(4M²)` apart, by
  `Section6.separated_interval_card_le`.
* `arc_sum_le`: the sum over these arcs of the integral of a continuous nonnegative function of
  period `1` is at most `27` times its integral over a period.
* `parseval_cost_proved`: the `R` part over `D ⊆ [N, 2N]` summed over the arcs of one dyadic
  block is `≤ 344 |D| L²`.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.Burst9Pieces
import LeanLab.PerelliPintz1992.FareyWindow

namespace LeanLab.PerelliPintz1992.Burst9
open Real ArithmeticFunction MeasureTheory Set Filter Topology
open LeanLab.PerelliPintz1992 LeanLab.PerelliPintz1992.Decomp97 LeanLab.PerelliPintz1992.Decomp1624
open LeanLab.PerelliPintz1992.Burst8P2

noncomputable section

/-! ### Parseval for a finite exponential sum -/

/-- `Σ_{n ∈ D} c_n e(nα)`. -/
def gsum (D : Finset ℕ) (c : ℕ → ℂ) (α : ℝ) : ℂ := ∑ n ∈ D, c n * e (n * α)

theorem e_natCast (n : ℕ) : e (n : ℝ) = 1 := by
  unfold e
  convert Complex.exp_nat_mul_two_pi_mul_I n using 1
  push_cast; ring

theorem gsum_periodic (D : Finset ℕ) (c : ℕ → ℂ) : Function.Periodic (gsum D c) 1 := by
  intro α
  unfold gsum
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [show (n : ℝ) * (α + 1) = n * α + n by ring, e_add, e_natCast, mul_one]

theorem continuous_gsum (D : Finset ℕ) (c : ℕ → ℂ) : Continuous (gsum D c) := by
  unfold gsum e
  fun_prop

/-- **Parseval** on `[t, t + 1]`: `∫ |Σ_{n ∈ D} c_n e(nα)|² = Σ |c_n|²`. PROVED. -/
theorem gsum_parseval (D : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) :
    ∫ α in t..t + 1, ‖gsum D c α‖ ^ 2 = ∑ n ∈ D, ‖c n‖ ^ 2 := by
  have hper : Function.Periodic (fun α => ‖gsum D c α‖ ^ 2) 1 := fun α => by
    simp only [gsum_periodic D c α]
  rw [hper.intervalIntegral_add_eq t 0, zero_add]
  set s : Finset ℤ := D.map Nat.castEmbedding with hs
  set a : ℤ → ℂ := fun z => c z.toNat with ha
  have hS : ∀ α, gsum D c α = LeanLab.CircleOrth.S s a α := by
    intro α
    unfold gsum LeanLab.CircleOrth.S
    rw [hs, Finset.sum_map]
    refine Finset.sum_congr rfl fun n _ => ?_
    simp only [ha, Nat.castEmbedding_apply, Int.toNat_natCast, Int.cast_natCast]
    rfl
  simp_rw [hS]
  rw [LeanLab.CircleOrth.parseval_norm, hs, Finset.sum_map]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [ha, Nat.castEmbedding_apply, Int.toNat_natCast]

/-! ### The arcs of one dyadic block overlap at most nine times -/

/-- Distinct reduced fractions with denominators `≤ 2M` are `1/(4M²)` apart, so a point lies on
at most `8M/Q + 1 ≤ 9` arcs of radius `≤ 1/(MQ)`. PROVED. -/
theorem arc_mult_le (F : Finset (Σ _ : ℕ+, ℕ)) {M : ℕ} (hM : 1 ≤ M) {Qr : ℝ}
    (hMQ : (M : ℝ) ≤ Qr)
    (hF : ∀ i ∈ F, M ≤ (i.1 : ℕ) ∧ (i.1 : ℕ) ≤ 2 * M ∧ Nat.Coprime i.2 i.1) (α : ℝ)
    (hα : ∀ i ∈ F, |α - (i.2 : ℝ) / (i.1 : ℕ)| ≤ 1 / (((i.1 : ℕ) : ℝ) * Qr)) :
    (F.card : ℝ) ≤ 9 := by
  classical
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hQ0 : 0 < Qr := by linarith
  set w := 1 / ((M : ℝ) * Qr) with hw
  have hw0 : 0 < w := by positivity
  have hsepδ : (0 : ℝ) < 1 / (4 * (M : ℝ) ^ 2) := by positivity
  have hbounds : ∀ i ∈ F, α - w ≤ (i.2 : ℝ) / (i.1 : ℕ) ∧ (i.2 : ℝ) / (i.1 : ℕ) ≤ α + w := by
    intro i hi
    obtain ⟨hMq, -, -⟩ := hF i hi
    have hq : (M : ℝ) ≤ ((i.1 : ℕ) : ℝ) := by exact_mod_cast hMq
    have h1 := hα i hi
    have h2 : 1 / (((i.1 : ℕ) : ℝ) * Qr) ≤ w :=
      one_div_le_one_div_of_le (by positivity) (mul_le_mul_of_nonneg_right hq hQ0.le)
    have := abs_le.mp (h1.trans h2)
    constructor <;> linarith [this.1, this.2]
  have hsep : ∀ i ∈ F, ∀ j ∈ F, i ≠ j →
      1 / (4 * (M : ℝ) ^ 2) ≤ |(i.2 : ℝ) / (i.1 : ℕ) - (j.2 : ℝ) / (j.1 : ℕ)| := by
    intro i hi j hj hne
    obtain ⟨hMi, hiM, hci⟩ := hF i hi
    obtain ⟨hMj, hjM, hcj⟩ := hF j hj
    set q := (i.1 : ℕ)
    set q' := (j.1 : ℕ)
    set r := i.2
    set r' := j.2
    have hq0 : 0 < q := i.1.pos
    have hq0' : 0 < q' := j.1.pos
    have hne' : r * q' ≠ r' * q := by
      intro heq
      have h1 : q ∣ q' := by
        have : q ∣ r * q' := ⟨r', by rw [heq]; ring⟩
        exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hci) this)
      have h2 : q' ∣ q := by
        have : q' ∣ r' * q := ⟨r, by rw [← heq]; ring⟩
        exact (Nat.Coprime.dvd_of_dvd_mul_left (Nat.Coprime.symm hcj) this)
      have hqq : q = q' := Nat.dvd_antisymm h1 h2
      have hrr : r = r' := by
        rw [hqq] at heq
        exact Nat.eq_of_mul_eq_mul_right hq0' heq
      apply hne
      have h1' : i.1 = j.1 := PNat.eq hqq
      exact Sigma.ext h1' (heq_of_eq hrr)
    have hqr : (0 : ℝ) < q := by exact_mod_cast hq0
    have hqr' : (0 : ℝ) < q' := by exact_mod_cast hq0'
    have e1 : (r : ℝ) / q - (r' : ℝ) / q' = (((r * q' : ℕ) : ℝ) - ((r' * q : ℕ) : ℝ)) / (q * q') := by
      push_cast; field_simp
    rw [e1, abs_div, abs_of_pos (mul_pos hqr hqr')]
    have hnum : (1 : ℝ) ≤ |((r * q' : ℕ) : ℝ) - ((r' * q : ℕ) : ℝ)| := by
      have : ((r * q' : ℕ) : ℤ) ≠ ((r' * q : ℕ) : ℤ) := by exact_mod_cast hne'
      have h := Int.one_le_abs (sub_ne_zero.mpr this)
      have : ((|((r * q' : ℕ) : ℤ) - ((r' * q : ℕ) : ℤ)| : ℤ) : ℝ) =
          |((r * q' : ℕ) : ℝ) - ((r' * q : ℕ) : ℝ)| := by push_cast; rfl
      rw [← this]; exact_mod_cast h
    have hden : (q : ℝ) * q' ≤ 4 * (M : ℝ) ^ 2 := by
      have a1 : (q : ℝ) ≤ 2 * M := by exact_mod_cast hiM
      have a2 : (q' : ℝ) ≤ 2 * M := by exact_mod_cast hjM
      nlinarith
    rw [div_le_div_iff₀ (by positivity) (mul_pos hqr hqr')]
    have hM4 : (0 : ℝ) ≤ 4 * (M : ℝ) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hnum hM4]
  have hcard := Section6.separated_interval_card_le F (fun i => (i.2 : ℝ) / (i.1 : ℕ))
    (by linarith : α - w ≤ α + w) hsepδ hbounds hsep
  have e2 : (α + w - (α - w)) / (1 / (4 * (M : ℝ) ^ 2)) + 1 = 8 * M / Qr + 1 := by
    rw [hw]; field_simp; ring
  rw [e2] at hcard
  have : 8 * (M : ℝ) / Qr ≤ 8 := by rw [div_le_iff₀ hQ0]; linarith
  linarith

/-- The sum over the arcs of one dyadic block of the integral of a continuous nonnegative
function of period `1` is at most `27` times its integral over a period. PROVED. -/
theorem arc_sum_le (F : Finset (Σ _ : ℕ+, ℕ)) {M : ℕ} (hM : 1 ≤ M) {Qr : ℝ}
    (hMQ : (M : ℝ) ≤ Qr)
    (hF : ∀ i ∈ F, M ≤ (i.1 : ℕ) ∧ (i.1 : ℕ) ≤ 2 * M ∧ Nat.Coprime i.2 i.1 ∧
      1 ≤ i.2 ∧ i.2 ≤ (i.1 : ℕ))
    (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x) (hper : Function.Periodic f 1) :
    ∑ i ∈ F, (∫ η in (-(1 / (((i.1 : ℕ) : ℝ) * Qr)))..(1 / (((i.1 : ℕ) : ℝ) * Qr)),
        f ((i.2 : ℝ) / (i.1 : ℕ) + η)) ≤ 27 * ∫ α in (0 : ℝ)..1, f α := by
  classical
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hQ1 : 1 ≤ Qr := by linarith
  set x : (Σ _ : ℕ+, ℕ) → ℝ := fun i => (i.2 : ℝ) / (i.1 : ℕ) with hx
  set d : (Σ _ : ℕ+, ℕ) → ℝ := fun i => 1 / (((i.1 : ℕ) : ℝ) * Qr) with hd
  set g : (Σ _ : ℕ+, ℕ) → Set ℝ := fun i => Ioc (x i - d i) (x i + d i) with hg
  have hd0 : ∀ i : (Σ _ : ℕ+, ℕ), 0 < d i := fun i => by
    have : (0 : ℝ) < ((i.1 : ℕ) : ℝ) := by exact_mod_cast i.1.pos
    simp only [hd]; positivity
  have hd1 : ∀ i : (Σ _ : ℕ+, ℕ), d i ≤ 1 := fun i => by
    have : (1 : ℝ) ≤ ((i.1 : ℕ) : ℝ) := by exact_mod_cast i.1.pos
    simp only [hd]
    rw [div_le_one (by positivity)]; nlinarith
  have hxI : ∀ i ∈ F, 0 ≤ x i ∧ x i ≤ 1 := fun i hi => by
    obtain ⟨-, -, -, h1, h2⟩ := hF i hi
    have hq : (0 : ℝ) < ((i.1 : ℕ) : ℝ) := by exact_mod_cast i.1.pos
    have h2' : (i.2 : ℝ) ≤ ((i.1 : ℕ) : ℝ) := by exact_mod_cast h2
    simp only [hx]
    exact ⟨by positivity, (div_le_one hq).mpr h2'⟩
  have hgI : ∀ i ∈ F, g i ⊆ Icc (-1) 2 := fun i hi y hy => by
    have := hxI i hi
    have := hd1 i
    simp only [hg, mem_Ioc] at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hfi : ∀ s : Set ℝ, s ⊆ Icc (-1) 2 → IntegrableOn f s := fun s hs =>
    (hf.integrableOn_Icc).mono_set hs
  -- each arc integral as a set integral
  have harc : ∀ i ∈ F, (∫ η in (-(d i))..(d i), f (x i + η)) = ∫ y, (g i).indicator f y := by
    intro i hi
    rw [intervalIntegral.integral_comp_add_left f (x i), integral_indicator measurableSet_Ioc,
      intervalIntegral.integral_of_le (by linarith [hd0 i])]
    rfl
  rw [Finset.sum_congr rfl harc]
  rw [← integral_finset_sum _ fun i hi =>
    (hfi _ (hgI i hi)).integrable_indicator measurableSet_Ioc]
  -- the pointwise multiplicity bound
  have hpt : ∀ y, ∑ i ∈ F, (g i).indicator f y ≤ 9 * (Icc (-1 : ℝ) 2).indicator f y := by
    intro y
    have e1 : ∑ i ∈ F, (g i).indicator f y = ((F.filter (fun i => y ∈ g i)).card : ℝ) * f y := by
      rw [Finset.card_eq_sum_ones, Nat.cast_sum, Finset.sum_mul, Finset.sum_filter]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases h : y ∈ g i
      · rw [indicator_of_mem h, if_pos h]; push_cast; ring
      · rw [indicator_of_notMem h, if_neg h]
    rw [e1]
    by_cases hy : y ∈ Icc (-1 : ℝ) 2
    · rw [indicator_of_mem hy]
      have hc := arc_mult_le (F.filter (fun i => y ∈ g i)) hM hMQ
        (fun i hi => by
          obtain ⟨h1, h2, h3, -, -⟩ := hF i (Finset.mem_filter.mp hi).1
          exact ⟨h1, h2, h3⟩)
        y (fun i hi => by
          have hy' := (Finset.mem_filter.mp hi).2
          simp only [hg, mem_Ioc] at hy'
          rw [abs_le]
          constructor <;> simp only [hx, hd] at hy' ⊢ <;> linarith [hy'.1, hy'.2])
      exact mul_le_mul_of_nonneg_right hc (hf0 y)
    · rw [indicator_of_notMem hy, mul_zero]
      have : (F.filter (fun i => y ∈ g i)).card = 0 := by
        rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
        intro i hi hyi
        exact hy (hgI i hi hyi)
      rw [this]; simp
  have hint9 : Integrable (fun y => 9 * (Icc (-1 : ℝ) 2).indicator f y) :=
    ((hfi _ subset_rfl).integrable_indicator measurableSet_Icc).const_mul 9
  refine (integral_mono (integrable_finset_sum _ fun i hi =>
    (hfi _ (hgI i hi)).integrable_indicator measurableSet_Ioc) hint9 hpt).trans (le_of_eq ?_)
  rw [integral_const_mul, integral_indicator measurableSet_Icc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num)]
  have h1 : ∫ α in (-1 : ℝ)..2, f α =
      (∫ α in (-1 : ℝ)..(-1) + 1, f α) + (∫ α in (0 : ℝ)..0 + 1, f α) +
        ∫ α in (1 : ℝ)..1 + 1, f α := by
    norm_num
    rw [intervalIntegral.integral_add_adjacent_intervals (hf.intervalIntegrable _ _)
      (hf.intervalIntegrable _ _), intervalIntegral.integral_add_adjacent_intervals
      (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)]
  rw [h1, hper.intervalIntegral_add_eq (-1) 0, hper.intervalIntegral_add_eq 1 0, zero_add]
  ring

/-! ### The Parseval cost -/

/-- `1/φ(q)² ≤ 4(1 + ℓ)²/M²` for `M ≤ q`, `log q ≤ ℓ`, from `φ(q) ≫ q/log q`. PROVED. -/
theorem inv_totient_sq_le {q : ℕ} (hq : 0 < q) {ℓ : ℝ} (hlq : Real.log q ≤ ℓ) {M : ℝ}
    (hM0 : 0 < M) (hqM : M ≤ q) :
    1 / (Nat.totient q : ℝ) ^ 2 ≤ 4 * (1 + ℓ) ^ 2 / M ^ 2 := by
  have hq1 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hlq0 : 0 ≤ Real.log (q : ℝ) := Real.log_nonneg hq1
  have hφ0 : (0 : ℝ) < Nat.totient q := by exact_mod_cast Nat.totient_pos.mpr hq
  have hφ : (q : ℝ) / (2 * (1 + ℓ)) ≤ (Nat.totient q : ℝ) := by
    have h1 := totient_ge_log_two_mul_div hq
    refine le_trans ?_ h1
    have hlog2 : (1 / 2 : ℝ) < Real.log 2 := by have := Real.log_two_gt_d9; linarith
    rw [div_le_div_iff₀ (by linarith) (by linarith)]
    have h3 : 1 + Real.log (q : ℝ) ≤ 2 * Real.log 2 * (1 + ℓ) := by nlinarith
    have h4 := mul_le_mul_of_nonneg_left h3 (by linarith : (0 : ℝ) ≤ (q : ℝ))
    linarith
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have h5 : (q : ℝ) ≤ 2 * (1 + ℓ) * (Nat.totient q : ℝ) := by
    rw [div_le_iff₀ (by linarith)] at hφ; linarith
  have h6 : M ≤ 2 * (1 + ℓ) * (Nat.totient q : ℝ) := hqM.trans h5
  have h7 := pow_le_pow_left₀ hM0.le h6 2
  nlinarith

/-- `|Y(M)| ≤ 2M`: its moduli are distinct integers in `[M, 2M]`. PROVED. -/
theorem card_Y_le_two_M (N : ℕ) (ε ξ : ℝ) {M : ℕ} (hM : 1 ≤ M) :
    ((Y N ε ξ M).card : ℝ) ≤ 2 * M := by
  have h1 : (Y N ε ξ M).card ≤ (Finset.Icc M (2 * M)).card := by
    refine Finset.card_le_card_of_injOn (fun q : ℕ+ => (q : ℕ)) (fun q hq => ?_)
      (fun q _ q' _ h => PNat.eq h)
    obtain ⟨-, hMq, hqM, -⟩ := of_mem_filter hq
    exact Finset.mem_Icc.mpr ⟨hMq, hqM⟩
  rw [Nat.card_Icc] at h1
  have : ((Y N ε ξ M).card : ℝ) ≤ ((2 * M + 1 - M : ℕ) : ℝ) := by exact_mod_cast h1
  have e : ((2 * M + 1 - M : ℕ) : ℝ) = M + 1 := by
    rw [show 2 * M + 1 - M = M + 1 by omega]; push_cast; ring
  have hMr : (1 : ℝ) ≤ M := by exact_mod_cast hM
  linarith


/-- **The Parseval cost of the end blocks, PROVED**, the route of `Decomp1624.reduction27A`
for display 27, p. 364: for any `D ⊆ [N, 2N]`, the `R` part over `D`, integrated over the arcs
`|η| < 1/(qQ)` of one dyadic block `Y(M)` of p. 363 and the numerators `a'` of display 25, is at
most `344 |D| L²`; by `|R|² ≤ 2|S|² + 2μ²/φ² |T|²`, `arc_sum_le` with Parseval for `S`,
Parseval for `T`, `|a'| ≤ 2`, `|Y(M)| ≤ 2M` and `φ(q) ≫ q/log q`. -/
theorem parseval_cost_proved :
    ∃ C₀ N₁ : ℝ, 0 < C₀ ∧ ∀ N : ℕ, N₁ ≤ N → ∀ ε ξ : ℝ, 0 < ε → ∀ M : ℕ, 1 ≤ M →
      (M : ℝ) ≤ Q N → ∀ D : Finset ℕ, D ⊆ Finset.Icc N (2 * N) →
        ∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ),
          (∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), ‖Rx D q r η‖ ^ 2) ≤
            C₀ * D.card * L N ^ 2 := by
  refine ⟨344, 64, by norm_num, fun N hN ε ξ hε M hM1 hMQ D hD => ?_⟩
  have hN64 : 64 ≤ N := by exact_mod_cast hN
  have hNr : (64 : ℝ) ≤ N := hN
  have hNpos : (0 : ℝ) < N := by linarith
  set ℓ := L N with hℓdef
  have hℓ1 : 1 ≤ ℓ := by
    simp only [hℓdef, L]
    have : Real.log 64 ≤ Real.log N := Real.log_le_log (by norm_num) hNr
    have h64 : (1 : ℝ) ≤ Real.log 64 := by
      rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]
      have := Real.log_two_gt_d9; push_cast; linarith
    linarith
  have hQ4 : 4 ≤ Q N := by
    unfold Q; rw [← Real.sqrt_eq_rpow]
    have : (8 : ℝ) ≤ √(N : ℝ) := by
      rw [show (8 : ℝ) = √64 by rw [show (64 : ℝ) = 8 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]]
      exact Real.sqrt_le_sqrt hNr
    linarith
  have hQ0 : 0 < Q N := by linarith
  have hQN : Q N ≤ N := by
    unfold Q; rw [← Real.sqrt_eq_rpow]
    have := Real.sqrt_le_sqrt (show (N : ℝ) ≤ (N : ℝ) ^ 2 by nlinarith)
    rw [Real.sqrt_sq hNpos.le] at this; linarith
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM1
  set fS : ℝ → ℝ := fun α => ‖gsum D (fun n => (Λ n : ℂ)) α‖ ^ 2 with hfS
  set fT : ℝ → ℝ := fun η => ‖gsum D (fun _ => (1 : ℂ)) η‖ ^ 2 with hfT
  have cS : Continuous fS := (continuous_gsum _ _).norm.pow 2
  have cT : Continuous fT := (continuous_gsum _ _).norm.pow 2
  -- the pointwise split
  have hpt : ∀ (q r : ℕ) (η : ℝ), ‖Rx D q r η‖ ^ 2 ≤
      2 * fS ((r : ℝ) / q + η) + 2 * (Decomp1519.muφ q ^ 2 * fT η) := by
    intro q r η
    have e1 : Rx D q r η = gsum D (fun n => (Λ n : ℂ)) ((r : ℝ) / q + η) +
        (-((Decomp1519.muφ q : ℂ)) * gsum D (fun _ => (1 : ℂ)) η) := by
      unfold Rx Sx Tx gsum
      simp only [one_mul]
      ring
    rw [e1]
    refine (norm_add_sq_le _ _).trans (le_of_eq ?_)
    simp only [hfS, hfT, norm_mul, norm_neg, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]
  -- the `T` integral
  have hTint : ∀ q : ℕ+, ((q : ℕ) : ℝ) ≤ Q N →
      (∫ η in (-(1 / (((q : ℕ) : ℝ) * Q N)))..(1 / (((q : ℕ) : ℝ) * Q N)), fT η) ≤ D.card := by
    intro q hqQ
    have hq1 : (1 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast q.pos
    have hδ : 1 / (((q : ℕ) : ℝ) * Q N) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
    have hδ0 : 0 < 1 / (((q : ℕ) : ℝ) * Q N) := by positivity
    have hP := gsum_parseval D (fun _ => (1 : ℂ)) (-(1 / 2))
    simp only [norm_one, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one] at hP
    rw [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num] at hP
    rw [← hP]
    exact intervalIntegral.integral_mono_interval (by linarith) (by linarith) hδ
      (Eventually.of_forall fun x => sq_nonneg _) (cT.intervalIntegrable _ _)
  -- per arc
  have harc : ∀ q ∈ Y N ε ξ M, ∀ r ∈ aWin N ε ξ (q : ℕ),
      (∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), ‖Rx D q r η‖ ^ 2) ≤
        2 * (∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), fS ((r : ℝ) / q + η)) +
          2 * (Decomp1519.muφ q ^ 2 * D.card) := by
    intro q hq r hr
    obtain ⟨hqim, -, -, -⟩ := of_mem_filter hq
    obtain ⟨q0, -, hq0⟩ := Finset.mem_image.mp hqim
    have hqI := Finset.mem_Icc.mp q0.property
    have hqval : (q : ℕ) = q0.val := by rw [← hq0]; rfl
    have hqQ : ((q : ℕ) : ℝ) ≤ Q N :=
      (Nat.cast_le.mpr (by rw [hqval]; exact hqI.2)).trans (Nat.floor_le hQ0.le)
    have hq1 : (1 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast q.pos
    have hδ0 : 0 < 1 / (((q : ℕ) : ℝ) * Q N) := by positivity
    have c1 : Continuous fun η => ‖Rx D q r η‖ ^ 2 := (continuous_Rx D q r).norm.pow 2
    have c2 : Continuous fun η => fS ((r : ℝ) / q + η) := cS.comp (continuous_const.add continuous_id)
    have c3 : Continuous fun η => 2 * fS ((r : ℝ) / q + η) + 2 * (Decomp1519.muφ q ^ 2 * fT η) :=
      (continuous_const.mul c2).add (continuous_const.mul (continuous_const.mul cT))
    calc (∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), ‖Rx D q r η‖ ^ 2)
        ≤ ∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)),
            (2 * fS ((r : ℝ) / q + η) + 2 * (Decomp1519.muφ q ^ 2 * fT η)) :=
          intervalIntegral.integral_mono_on (by linarith) (c1.intervalIntegrable _ _)
            (c3.intervalIntegrable _ _) fun η _ => hpt q r η
      _ = 2 * (∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), fS ((r : ℝ) / q + η)) +
            2 * (Decomp1519.muφ q ^ 2 *
              ∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), fT η) := by
          have i1 : IntervalIntegrable (fun η => 2 * fS ((r : ℝ) / q + η)) volume
              (-(1 / ((q : ℝ) * Q N))) (1 / ((q : ℝ) * Q N)) :=
            (continuous_const.mul c2).intervalIntegrable _ _
          have i2 : IntervalIntegrable (fun η => 2 * (Decomp1519.muφ q ^ 2 * fT η)) volume
              (-(1 / ((q : ℝ) * Q N))) (1 / ((q : ℝ) * Q N)) :=
            (continuous_const.mul (continuous_const.mul cT)).intervalIntegrable _ _
          rw [intervalIntegral.integral_add i1 i2, intervalIntegral.integral_const_mul,
            intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ ≤ _ := by
          have h := hTint q hqQ
          have hm : 0 ≤ Decomp1519.muφ q ^ 2 := sq_nonneg _
          have := mul_le_mul_of_nonneg_left h hm
          linarith
  -- the `S` part by the arc multiplicity
  have hSsum : (∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ),
      ∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), fS ((r : ℝ) / q + η)) ≤
      27 * (D.card * (2 * ℓ) ^ 2) := by
    rw [← Finset.sum_sigma (Y N ε ξ M) (fun q => aWin N ε ξ (q : ℕ))
      (fun i : (Σ _ : ℕ+, ℕ) => ∫ η in (-(1 / (((i.1 : ℕ) : ℝ) * Q N)))..(1 / (((i.1 : ℕ) : ℝ) * Q N)),
        fS ((i.2 : ℝ) / (i.1 : ℕ) + η))]
    have hF : ∀ i ∈ (Y N ε ξ M).sigma (fun q => aWin N ε ξ (q : ℕ)),
        M ≤ (i.1 : ℕ) ∧ (i.1 : ℕ) ≤ 2 * M ∧ Nat.Coprime i.2 i.1 ∧ 1 ≤ i.2 ∧ i.2 ≤ (i.1 : ℕ) := by
      intro i hi
      obtain ⟨hq, hr⟩ := Finset.mem_sigma.mp hi
      obtain ⟨-, hMq, hqM, -⟩ := of_mem_filter hq
      have hrA := (of_mem_filter hr).1
      obtain ⟨hrI, hcop⟩ := Finset.mem_filter.mp hrA
      exact ⟨hMq, hqM, hcop, (Finset.mem_Icc.mp hrI).1, (Finset.mem_Icc.mp hrI).2⟩
    have hper : Function.Periodic fS 1 := fun α => by simp only [hfS, gsum_periodic D _ α]
    have h1 := arc_sum_le _ hM1 hMQ hF fS cS (fun x => sq_nonneg _) hper
    refine h1.trans ?_
    have hP := gsum_parseval D (fun n => (Λ n : ℂ)) 0
    rw [zero_add] at hP
    rw [show (∫ α in (0 : ℝ)..1, fS α) = ∑ n ∈ D, ‖(Λ n : ℂ)‖ ^ 2 from hP]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    rw [← nsmul_eq_mul, ← Finset.sum_const]
    refine Finset.sum_le_sum fun n hn => ?_
    have hn2 := (Finset.mem_Icc.mp (hD hn)).2
    have hn1 := (Finset.mem_Icc.mp (hD hn)).1
    rw [Complex.norm_real, Real.norm_of_nonneg vonMangoldt_nonneg]
    have hl : Λ n ≤ 2 * ℓ := by
      refine vonMangoldt_le_log.trans ?_
      have hnpos : (0 : ℝ) < n := by
        have : (64 : ℕ) ≤ n := hN64.trans hn1
        exact_mod_cast (by omega : 0 < n)
      have : Real.log n ≤ Real.log (2 * N) :=
        Real.log_le_log hnpos (by exact_mod_cast hn2)
      have h2 : Real.log (2 * N) ≤ 2 * ℓ := by
        simp only [hℓdef, L]
        rw [Real.log_mul (by norm_num) (by linarith)]
        have : Real.log 2 ≤ Real.log N := Real.log_le_log (by norm_num) (by linarith)
        linarith
      linarith
    exact pow_le_pow_left₀ vonMangoldt_nonneg hl 2
  -- the `T` part
  have hTsum : (∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ),
      2 * (Decomp1519.muφ q ^ 2 * D.card)) ≤ 128 * D.card * ℓ ^ 2 := by
    have hq : ∀ q ∈ Y N ε ξ M, (∑ r ∈ aWin N ε ξ (q : ℕ),
        2 * (Decomp1519.muφ q ^ 2 * D.card)) ≤ 4 * (4 * (1 + ℓ) ^ 2 / (M : ℝ) ^ 2) * D.card := by
      intro q hq
      obtain ⟨hqim, hMq, -, -⟩ := of_mem_filter hq
      obtain ⟨q0, -, hq0⟩ := Finset.mem_image.mp hqim
      have hqI := Finset.mem_Icc.mp q0.property
      have hqval : (q : ℕ) = q0.val := by rw [← hq0]; rfl
      have hqQ : ((q : ℕ) : ℝ) ≤ Q N :=
        (Nat.cast_le.mpr (by rw [hqval]; exact hqI.2)).trans (Nat.floor_le hQ0.le)
      have hq1 : (1 : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast q.pos
      have hlq : Real.log ((q : ℕ) : ℝ) ≤ ℓ := by
        simp only [hℓdef, L]; exact Real.log_le_log (by linarith) (hqQ.trans hQN)
      have hqM : (M : ℝ) ≤ ((q : ℕ) : ℝ) := by exact_mod_cast hMq
      have hinv := inv_totient_sq_le q.pos hlq hM0 hqM
      have hmu := (Decomp1519.muφ_sq_le (q := (q : ℕ))).trans hinv
      have hc : ((aWin N ε ξ (q : ℕ)).card : ℝ) ≤ 2 := by
        exact_mod_cast card_aWin_le_two hN64 hε ξ q.pos hqQ
      rw [Finset.sum_const, nsmul_eq_mul]
      have hD0 : (0 : ℝ) ≤ D.card := Nat.cast_nonneg _
      have h1 : 2 * (Decomp1519.muφ q ^ 2 * D.card) ≤ 2 * (4 * (1 + ℓ) ^ 2 / (M : ℝ) ^ 2 * D.card) := by
        have := mul_le_mul_of_nonneg_right hmu hD0
        linarith
      have h2 : 0 ≤ 2 * (Decomp1519.muφ q ^ 2 * D.card) := by positivity
      calc ((aWin N ε ξ (q : ℕ)).card : ℝ) * (2 * (Decomp1519.muφ q ^ 2 * D.card))
          ≤ 2 * (2 * (4 * (1 + ℓ) ^ 2 / (M : ℝ) ^ 2 * D.card)) :=
            mul_le_mul hc h1 h2 (by norm_num)
        _ = 4 * (4 * (1 + ℓ) ^ 2 / (M : ℝ) ^ 2) * D.card := by ring
    refine (Finset.sum_le_sum hq).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul]
    have hY := card_Y_le_two_M N ε ξ hM1
    have hD0 : (0 : ℝ) ≤ D.card := Nat.cast_nonneg _
    have h0 : 0 ≤ 4 * (4 * (1 + ℓ) ^ 2 / (M : ℝ) ^ 2) * D.card := by positivity
    calc ((Y N ε ξ M).card : ℝ) * (4 * (4 * (1 + ℓ) ^ 2 / (M : ℝ) ^ 2) * D.card)
        ≤ (2 * M) * (4 * (4 * (1 + ℓ) ^ 2 / (M : ℝ) ^ 2) * D.card) :=
          mul_le_mul_of_nonneg_right hY h0
      _ = 32 * (1 + ℓ) ^ 2 / M * D.card := by field_simp; ring
      _ ≤ 32 * (1 + ℓ) ^ 2 * D.card := by
          have hM1r : (1 : ℝ) ≤ M := by exact_mod_cast hM1
          have : 32 * (1 + ℓ) ^ 2 / M ≤ 32 * (1 + ℓ) ^ 2 :=
            div_le_self (by positivity) hM1r
          exact mul_le_mul_of_nonneg_right this hD0
      _ ≤ 128 * D.card * ℓ ^ 2 := by
          have h4 : (1 + ℓ) ^ 2 ≤ 4 * ℓ ^ 2 := by nlinarith
          have := mul_le_mul_of_nonneg_right h4 (by positivity : (0 : ℝ) ≤ 32 * D.card)
          linarith
  -- assemble
  calc (∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ),
        ∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), ‖Rx D q r η‖ ^ 2)
      ≤ ∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ),
          (2 * (∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), fS ((r : ℝ) / q + η)) +
            2 * (Decomp1519.muφ q ^ 2 * D.card)) :=
        Finset.sum_le_sum fun q hq => Finset.sum_le_sum fun r hr => harc q hq r hr
    _ = 2 * (∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ),
          ∫ η in (-(1 / ((q : ℝ) * Q N)))..(1 / ((q : ℝ) * Q N)), fS ((r : ℝ) / q + η)) +
          ∑ q ∈ Y N ε ξ M, ∑ r ∈ aWin N ε ξ (q : ℕ), 2 * (Decomp1519.muφ q ^ 2 * D.card) := by
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun q _ => ?_
        rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    _ ≤ 2 * (27 * (D.card * (2 * ℓ) ^ 2)) + 128 * D.card * ℓ ^ 2 := by linarith
    _ = 344 * D.card * L N ^ 2 := by rw [hℓdef]; ring

#print axioms gsum_parseval
#print axioms arc_mult_le
#print axioms arc_sum_le
#print axioms card_Y_le_two_M
#print axioms inv_totient_sq_le
#print axioms parseval_cost_proved

end
end LeanLab.PerelliPintz1992.Burst9
