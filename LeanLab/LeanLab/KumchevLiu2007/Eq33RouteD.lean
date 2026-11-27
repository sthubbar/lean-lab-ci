/-
Kumchev and Liu 2007, P0088, arXiv 0801.0130, page 11 Lemma 3.4 with its proof
on pages 11 and 12, and page 15 display 52 with the paragraph after it, which
verifies hypothesis A2.3 of page 7 for the rough weight.

This file proves the statement of Task556a.lemma34_rough_minor_input under the
name lemma34_rough_minor_input_route. The steps are those of page 15:

* `lemma34_first_sum`, Lemma 3.4 with x = Y, y = H, (m, k) = (1, m) and a
  sieve cutoff at most z1 = Y^(1/6 + eps/2). Open leaf.
* `lemma34_second_sum_dyadic`, Lemma 3.4 with x = Y, y = H, (m, k) = (p, m / p)
  and z = z1, for the primes p between z1 and z0 in one dyadic block. Open leaf.
* `dyadic_partition`, `dyadic_mean_square_le` and `lemma34_second_sum`, the
  sum over at most 3 log X dyadic blocks. Proved.
* `buchstab_core` and `display52_identity`, the Buchstab identity of display
  52 on the window I2. Proved.
* `logPower_le_H` and `minor_arc_dirichlet`, the passage from a point off the
  major arcs to display 41 by Dirichlet's theorem. Proved.
* `lemma34_cutoff_le` and `lemma34_cutoff_margin`, the parameter check that
  z1 times the square root of Y is at most H, with a power of X to spare.
  Proved.
* `short_sum_sub_mean_square_le`, the sentence "the hypothesis A2.3 for the
  rough weight then follows from 52". Proved, with the measurability of the
  short sums in t.

QUESTION recorded in the notes: Lemma 3.4 assumes y at most x, that is H at
most Y, while the target statement and the two specialised leaves keep the
written range H at most X^(1 - eps) with Y fixed at X^(7/12 + eps/2).

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp556a

namespace LeanLab.KumchevLiu2007.Eq33RouteD

open Real Complex MeasureTheory LeanLab.KumchevLiu2007 Task556a
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- LEAF: P0088 page 11 Lemma 3.4, as applied on page 15 after display 52 to
the first sum of display 52, with x = Y, y = H, (m, k) = (1, m). The sieve
cutoff z is any real number at most z1 = Y^(1/6 + eps/2); the lemma is uniform
in z. For z at most 2 the weight is identically one, the case z = 2 of the
lemma. The hypothesis on alpha is display 41 with y = H, in the form
P < q ≤ H / P and |q alpha - a| < P / H, where P = (log X)^B. The check
z1 at most H Y^(-1/2) L^(-2B) is inside this leaf. -/
theorem lemma34_first_sum (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ z : ℝ, z ≤ windowY X ε ^ (1 / 6 + ε / 2) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            roughWeight z m *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  sorry

/-- The empty high block in the second sum of display 52. If the dyadic block
starts at or above the sieve cutoff `z0`, no prime in the block is below `z0`,
so its coefficient is zero. -/
theorem lemma34_second_sum_dyadic_empty_high
    (X B ε M : ℝ) (hz0 : windowY X ε ^ (1 / 4 : ℝ) *
        (Real.log X ^ B) ^ (-2 : ℤ) ≤ M) (m : ℕ) :
    (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
        windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
        (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
        p ∣ m)).filter
        (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
      roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨hp1, hpM⟩ := Finset.mem_filter.mp hp
  obtain ⟨-, -, hpz0, -⟩ := Finset.mem_filter.mp hp1
  exact (by linarith : False).elim

/-- The empty low block in the second sum of display 52. If the dyadic block
ends at or below the rough cutoff `z1`, no prime in the block is at least `z1`,
so its coefficient is zero. -/
theorem lemma34_second_sum_dyadic_empty_low
    (X B ε M : ℝ) (hz1 : 2 * M ≤ windowY X ε ^ (1 / 6 + ε / 2)) (m : ℕ) :
    (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
        windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
        (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
        p ∣ m)).filter
        (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
      roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) = 0 := by
  apply Finset.sum_eq_zero
  intro p hp
  obtain ⟨hp1, hpM⟩ := Finset.mem_filter.mp hp
  obtain ⟨-, hpz1, -, -⟩ := Finset.mem_filter.mp hp1
  exact (by linarith : False).elim

/-- LEAF: P0088 page 11 Lemma 3.4, as applied on page 15 after display 52 to
the second sum of display 52, with x = Y, y = H, (m, k) = (p, m / p) and
z = z1 = Y^(1/6 + eps/2), for one dyadic block M at most p below 2M. The
coefficient of p is the indicator of the primes from z1 up to the cutoff
z0 = Y^(1/4) P^(-2) of page 8 display 34. The bound M at most x^(1/4) L^(-2B)
of Lemma 3.4 is enforced by p below z0; for larger M the block is empty. The
bound is uniform in M. The hypothesis on alpha is display 41 with y = H, in
the form P < q ≤ H / P and |q alpha - a| < P / H, where P = (log X)^B. -/
theorem lemma34_second_sum_dyadic (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        ∀ M : ℝ, 1 ≤ M →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
                (fun p : ℕ => M ≤ (p : ℝ) ∧ (p : ℝ) < 2 * M),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  exact lemma34_bilinear_minor_arc_mean_square

/-- P0088 page 15, the display before 52 and display 52 itself, the finite
core of the Buchstab identity. Let z1 be at most z0, let m be a positive
integer below the cube of z1 and at least the square of z0. Then the rough
indicator of m at z0 is the rough indicator at z1 minus the sum over the primes
p dividing m with z1 at most p and p below z0 of the rough indicator of m / p
at z1. The size conditions are those of the sentence between the two displays:
m / p is below the square of z1, so it is a prime, and it exceeds z0. -/
theorem buchstab_core (z0 z1 : ℝ) (m : ℕ) (hz1 : 0 ≤ z1) (hz : z1 ≤ z0)
    (hb : (m : ℝ) < z1 ^ 3) (hc : z0 ^ 2 ≤ (m : ℝ)) (hm : 0 < m) :
    roughWeight z0 m = roughWeight z1 m -
      ∑ p ∈ (Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
          z1 ≤ (p : ℝ) ∧ (p : ℝ) < z0 ∧ p ∣ m), roughWeight z1 (m / p) := by
  by_cases h1 : ∀ p : ℕ, p.Prime → p ∣ m → z1 ≤ (p : ℝ)
  · have hw1 : roughWeight z1 m = 1 := by
      unfold roughWeight
      split_ifs
      rfl
    by_cases h0 : ∀ p : ℕ, p.Prime → p ∣ m → z0 ≤ (p : ℝ)
    · have hw0 : roughWeight z0 m = 1 := by
        unfold roughWeight
        split_ifs
        rfl
      have hempty : (Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
          z1 ≤ (p : ℝ) ∧ (p : ℝ) < z0 ∧ p ∣ m) = ∅ := by
        apply Finset.filter_eq_empty_iff.mpr
        intro p _ hp
        exact absurd (h0 p hp.1 hp.2.2.2) (not_le.mpr hp.2.2.1)
      rw [hw0, hw1, hempty, Finset.sum_empty, sub_zero]
    · push Not at h0
      obtain ⟨q, hq, hqm, hqz⟩ := h0
      have hw0 : roughWeight z0 m = 0 := roughWeight_eq_zero_of_small_prime hq hqm hqz
      have hqz1 : z1 ≤ (q : ℝ) := h1 q hq hqm
      have hsing : (Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
          z1 ≤ (p : ℝ) ∧ (p : ℝ) < z0 ∧ p ∣ m) = {q} := by
        ext p
        simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_singleton]
        constructor
        · rintro ⟨_, hp, hpz1, hpz0, hpm⟩
          by_contra hne
          have hcop : Nat.Coprime p q := (Nat.coprime_primes hp hq).mpr hne
          obtain ⟨r, hr⟩ := hcop.mul_dvd_of_dvd_of_dvd hpm hqm
          have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
          have hq0 : (0 : ℝ) ≤ q := Nat.cast_nonneg q
          have hmr : (m : ℝ) = (p : ℝ) * q * r := by
            rw [hr]
            push_cast
            ring
          have hr0 : r ≠ 0 := by
            intro h
            rw [h, mul_zero] at hr
            omega
          by_cases hr1 : r = 1
          · rw [hr1, Nat.cast_one, mul_one] at hmr
            have h4 : (p : ℝ) * q < z0 * z0 := mul_lt_mul'' hpz0 hqz hp0 hq0
            have hc' : z0 * z0 ≤ (m : ℝ) := by
              rw [← sq]
              exact hc
            linarith
          · obtain ⟨s, hs, hsr⟩ := Nat.exists_prime_and_dvd hr1
            have hsm : s ∣ m := by
              rw [hr]
              exact Dvd.dvd.mul_left hsr _
            have hsz : z1 ≤ (s : ℝ) := h1 s hs hsm
            have hsr' : (s : ℝ) ≤ r := by
              exact_mod_cast Nat.le_of_dvd (Nat.pos_of_ne_zero hr0) hsr
            have h3 : z1 * z1 * z1 ≤ (p : ℝ) * q * r :=
              mul_le_mul (mul_le_mul hpz1 hqz1 hz1 hp0) (hsz.trans hsr') hz1
                (mul_nonneg hp0 hq0)
            have h5 : z1 ^ 3 = z1 * z1 * z1 := by ring
            linarith
        · intro h
          rw [h]
          exact ⟨Nat.lt_succ_of_le (Nat.le_of_dvd hm hqm), hq, hqz1, hqz, hqm⟩
      have hwq : roughWeight z1 (m / q) = 1 := by
        have hr : ∀ p : ℕ, p.Prime → p ∣ m / q → z1 ≤ (p : ℝ) := fun p hp hpd =>
          h1 p hp (hpd.trans (Nat.div_dvd_of_dvd hqm))
        unfold roughWeight
        split_ifs
        rfl
      rw [hw0, hw1, hsing, Finset.sum_singleton, hwq, sub_self]
  · push Not at h1
    obtain ⟨q, hq, hqm, hqz⟩ := h1
    have hw1 : roughWeight z1 m = 0 := roughWeight_eq_zero_of_small_prime hq hqm hqz
    have hw0 : roughWeight z0 m = 0 :=
      roughWeight_eq_zero_of_small_prime hq hqm (hqz.trans_le hz)
    have hsum : (∑ p ∈ (Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
        z1 ≤ (p : ℝ) ∧ (p : ℝ) < z0 ∧ p ∣ m), roughWeight z1 (m / p)) = 0 := by
      apply Finset.sum_eq_zero
      intro p hp
      obtain ⟨_, hpp, hpz1, _, hpm⟩ := Finset.mem_filter.mp hp
      have hne : q ≠ p := by
        intro h
        rw [h] at hqz
        linarith
      have hqd : q ∣ m / p := by
        have hd : q ∣ p * (m / p) := by
          rw [Nat.mul_div_cancel' hpm]
          exact hqm
        exact ((Nat.Prime.dvd_mul hq).mp hd).resolve_left
          (fun h => hne ((Nat.prime_dvd_prime_iff_eq hq hpp).mp h))
      exact roughWeight_eq_zero_of_small_prime hq hqd hqz
    rw [hw0, hw1, hsum, sub_zero]

/-- P0088 page 15 display 52, the Buchstab identity on the window I2.
For m in I2 the rough indicator at z0 = Y^(1/4) P^(-2) is the rough indicator
at z1 = Y^(1/6 + eps/2) minus the sum over the primes p dividing m with
z1 at most p and p below z0 of the rough indicator of m / p at z1. The
boundary convention follows page 4 display 10, where rough means every prime
factor is at least z. The identity needs z1 at most z0. -/
theorem display52_identity (B ε : ℝ) (hB : 0 < B) (hε : 0 < ε) :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X : ℝ, X0 ≤ X →
      windowY X ε ^ (1 / 6 + ε / 2) ≤
        windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) →
      ∀ m ∈ squareWindow (windowY X ε),
        roughWeight (windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ)) m =
          roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) m -
            ∑ p ∈ (Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p) := by
  refine ⟨max 2 (Real.exp (2 ^ (1 / B))), le_max_left _ _, ?_⟩
  intro X hX hz m hm
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hXe : Real.exp (2 ^ (1 / B)) ≤ X := (le_max_right _ _).trans hX
  have hY1 : 1 ≤ windowY X ε := by
    unfold windowY
    exact Real.one_le_rpow (by linarith) (by positivity)
  have hY0 : 0 < windowY X ε := by linarith
  have hlog : (2 : ℝ) ^ (1 / B) ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    exact hXe
  have hP : 2 ≤ Real.log X ^ B := by
    have h := Real.rpow_le_rpow (by positivity) hlog hB.le
    rwa [← Real.rpow_mul (by norm_num), one_div, inv_mul_cancel₀ hB.ne', Real.rpow_one] at h
  have hmw := (Finset.mem_filter.mp hm).2
  have hsq0 : 0 < Real.sqrt (windowY X ε) := Real.sqrt_pos.mpr hY0
  apply buchstab_core _ _ m (Real.rpow_nonneg hY0.le _) hz
  · have hpow : (windowY X ε ^ (1 / 6 + ε / 2)) ^ 3 =
        windowY X ε ^ ((1 / 6 + ε / 2) * 3) := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
      norm_num
    have hs : Real.sqrt (windowY X ε) ≤ windowY X ε ^ ((1 / 6 + ε / 2) * 3) := by
      rw [Real.sqrt_eq_rpow]
      exact Real.rpow_le_rpow_of_exponent_le hY1 (by linarith)
    linarith [hmw.2]
  · have h4 : 4 ≤ (Real.log X ^ B) ^ 2 := by nlinarith
    have hw : (Real.log X ^ B) ^ (-2 : ℤ) ≤ 1 / 4 := by
      rw [zpow_neg, zpow_ofNat, one_div]
      exact inv_anti₀ (by norm_num) h4
    have hw0 : 0 < (Real.log X ^ B) ^ (-2 : ℤ) := zpow_pos (by linarith) _
    have hYq : (windowY X ε ^ (1 / 4 : ℝ)) ^ 2 = Real.sqrt (windowY X ε) := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_mul hY0.le]
      norm_num
    rw [mul_pow, hYq]
    have hw2 : ((Real.log X ^ B) ^ (-2 : ℤ)) ^ 2 ≤ 1 / 2 := by nlinarith
    have hprod := mul_le_mul_of_nonneg_left hw2 hsq0.le
    linarith [hmw.1]
  · have hpos : (0 : ℝ) < m := lt_of_lt_of_le (half_pos hsq0) hmw.1
    exact_mod_cast hpos

/-- P0088 page 15, the note in brackets after display 52: the condition on
theta2 ensures that z1 is at most H Y^(-1/2). Here it is in product form,
z1 times the square root of Y is at most H, in the written range of page 16. -/
theorem lemma34_cutoff_le {X H ε : ℝ} (hX : 1 < X) (hε : 0 < ε)
    (hl : X ^ (7 / 18 + ε) ≤ H) (hu : H ≤ X ^ (1 - ε)) :
    windowY X ε ^ (1 / 6 + ε / 2) * windowY X ε ^ (1 / 2 : ℝ) ≤ H := by
  have hY : 0 < windowY X ε := by
    unfold windowY
    exact Real.rpow_pos_of_pos (by linarith) _
  rw [← Real.rpow_add hY]
  have he : (1 / 6 + ε / 2 + 1 / 2 : ℝ) = 2 / 3 + ε / 2 := by ring
  rw [he]
  exact window_power_le_H hX hε hl hu

/-- P0088 page 15, the note in brackets after display 52, with the room for
the factor L^(-2B) of Lemma 3.4: in the written range of page 16 the product
of z1 and the square root of Y is below H by the power X^(eps/4). -/
theorem lemma34_cutoff_margin {X H ε : ℝ} (hX : 1 < X) (hε : 0 < ε)
    (hl : X ^ (7 / 18 + ε) ≤ H) (hu : H ≤ X ^ (1 - ε)) :
    windowY X ε ^ (1 / 6 + ε / 2) * windowY X ε ^ (1 / 2 : ℝ) * X ^ (ε / 4) ≤ H := by
  have hX0 : 0 < X := by linarith
  have hY : 0 < windowY X ε := by
    unfold windowY
    exact Real.rpow_pos_of_pos hX0 _
  rw [← Real.rpow_add hY, windowY, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
  refine le_trans (Real.rpow_le_rpow_of_exponent_le hX.le ?_) hl
  have hm := short_square_exponent_margin hε.le (written_range_epsilon_le hX hl hu)
  have he : (7 / 12 + ε / 2) * (1 / 6 + ε / 2 + 1 / 2) =
      (7 / 12 + ε / 2) * (2 / 3 + ε / 2) := by ring
  linarith

/-- P0088 page 7 hypothesis A2.3: the square of a short sum over squares in
(t, t + H] is an integrable function of t on every bounded interval. -/
theorem short_sum_sq_intervalIntegrable (S : Finset ℕ) (c : ℕ → ℂ) (H a b : ℝ) :
    IntervalIntegrable (fun t : ℝ =>
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ^ 2)
      volume a b := by
  have hrw : ∀ t : ℝ,
      (∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m) =
        ∑ m ∈ S, if (t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H) then c m else 0 :=
    fun t => Finset.sum_filter _ _
  have hmeas : Measurable (fun t : ℝ =>
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ^ 2) := by
    simp_rw [hrw]
    refine (Measurable.norm ?_).pow_const 2
    refine Finset.measurable_sum _ fun m _ => ?_
    refine Measurable.ite ?_ measurable_const measurable_const
    exact (measurableSet_lt measurable_id measurable_const).inter
      (measurableSet_le measurable_const (measurable_id.add_const H))
  have hbound : ∀ t : ℝ,
      ‖‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ^ 2‖ ≤
        (∑ m ∈ S, ‖c m‖) ^ 2 := by
    intro t
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    have h1 : ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), c m‖ ≤
        ∑ m ∈ S, ‖c m‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.filter_subset _ _) (fun _ _ _ => norm_nonneg _))
    exact pow_le_pow_left₀ (norm_nonneg _) h1 2
  exact (intervalIntegrable_const (c := (∑ m ∈ S, ‖c m‖) ^ 2)).mono_fun'
    hmeas.aestronglyMeasurable (Filter.Eventually.of_forall hbound)

/-- P0088 page 15, the step from display 52 to A2.3: the square of a
difference is at most twice the sum of the squares. -/
theorem norm_sub_sq_le (u v : ℂ) : ‖u - v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
  have h2 := pow_le_pow_left₀ (norm_nonneg _) (norm_sub_le u v) 2
  nlinarith [sq_nonneg (‖u‖ - ‖v‖)]

/-- P0088 page 15, the sentence after display 52: hypothesis A2.3 for a
difference of two weights follows from A2.3 for each of them. The weights
only need to agree with the difference on the support S of the short sums. -/
theorem short_sum_sub_mean_square_le (S : Finset ℕ) (w0 w1 w2 f : ℕ → ℂ)
    (H a b K1 K2 : ℝ) (hab : a ≤ b)
    (hid : ∀ m ∈ S, w0 m = w1 m - w2 m)
    (e1 : (∫ t in a..b,
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        w1 m * f m‖ ^ 2) ≤ K1)
    (e2 : (∫ t in a..b,
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        w2 m * f m‖ ^ 2) ≤ K2) :
    (∫ t in a..b,
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        w0 m * f m‖ ^ 2) ≤ 2 * K1 + 2 * K2 := by
  have hI0 := short_sum_sq_intervalIntegrable S (fun m => w0 m * f m) H a b
  have hI1 := short_sum_sq_intervalIntegrable S (fun m => w1 m * f m) H a b
  have hI2 := short_sum_sq_intervalIntegrable S (fun m => w2 m * f m) H a b
  have hpt : ∀ t : ℝ,
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        w0 m * f m‖ ^ 2 ≤
      2 * ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        w1 m * f m‖ ^ 2 +
      2 * ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        w2 m * f m‖ ^ 2 := by
    intro t
    have hs : (∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
        w0 m * f m) =
        (∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
          w1 m * f m) -
        ∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
          w2 m * f m := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [hid m (Finset.mem_filter.mp hm).1]
      ring
    rw [hs]
    exact norm_sub_sq_le _ _
  calc
    _ ≤ ∫ t in a..b,
        (2 * ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
          w1 m * f m‖ ^ 2 +
        2 * ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
          w2 m * f m‖ ^ 2) :=
      intervalIntegral.integral_mono_on hab hI0 ((hI1.const_mul 2).add (hI2.const_mul 2))
        (fun t _ => hpt t)
    _ = 2 * (∫ t in a..b,
          ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            w1 m * f m‖ ^ 2) +
        2 * ∫ t in a..b,
          ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            w2 m * f m‖ ^ 2 := by
      rw [intervalIntegral.integral_add (hI1.const_mul 2) (hI2.const_mul 2),
        intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
    _ ≤ 2 * K1 + 2 * K2 := by linarith

/-- P0088 page 11, the notation m ∼ M in Lemma 3.4: a finite sum over
positive integers below 2^J splits into the J dyadic blocks 2^j ≤ p < 2^(j+1). -/
theorem dyadic_partition (T : Finset ℕ) (J : ℕ) (g : ℕ → ℂ)
    (hT : ∀ p ∈ T, p ≠ 0 ∧ p < 2 ^ J) :
    ∑ p ∈ T, g p = ∑ j ∈ Finset.range J,
      ∑ p ∈ T.filter (fun p : ℕ => (2 : ℝ) ^ j ≤ (p : ℝ) ∧ (p : ℝ) < 2 * 2 ^ j), g p := by
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun p hp => ?_
  obtain ⟨hp0, hpJ⟩ := hT p hp
  have hiff : ∀ j : ℕ, ((2 : ℝ) ^ j ≤ (p : ℝ) ∧ (p : ℝ) < 2 * 2 ^ j) ↔ Nat.log 2 p = j := by
    intro j
    have hlog := Nat.log_eq_iff (b := 2) (n := p) (m := j) (Or.inr ⟨by norm_num, hp0⟩)
    rw [hlog]
    constructor
    · rintro ⟨h1, h2⟩
      have h3 : (p : ℝ) < 2 ^ (j + 1) := by
        rw [pow_succ]
        linarith
      exact ⟨by exact_mod_cast h1, by exact_mod_cast h3⟩
    · rintro ⟨h1, h2⟩
      have h3 : (p : ℝ) < 2 ^ (j + 1) := by exact_mod_cast h2
      rw [pow_succ] at h3
      exact ⟨by exact_mod_cast h1, by linarith⟩
  simp_rw [hiff]
  simp [Nat.log_lt_of_lt_pow hp0 hpJ]

/-- P0088 page 15, the application of Lemma 3.4 to the second sum of display
52: the mean square of a sum of J dyadic blocks is at most J squared times a
common bound for the blocks, by the Cauchy inequality. -/
theorem dyadic_mean_square_le (S : Finset ℕ) (J : ℕ) (w : ℕ → ℕ → ℂ) (f : ℕ → ℂ)
    (H a b K : ℝ) (hab : a ≤ b)
    (e : ∀ j ∈ Finset.range J, (∫ t in a..b,
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), w j m * f m‖ ^ 2) ≤ K) :
    (∫ t in a..b,
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), (∑ j ∈ Finset.range J, w j m) * f m‖ ^ 2) ≤
        (J : ℝ) ^ 2 * K := by
  have hI := fun j : ℕ => short_sum_sq_intervalIntegrable S (fun m => w j m * f m) H a b
  have hI0 := short_sum_sq_intervalIntegrable S
    (fun m => (∑ j ∈ Finset.range J, w j m) * f m) H a b
  have hIs : IntervalIntegrable (fun t : ℝ => ∑ j ∈ Finset.range J,
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), w j m * f m‖ ^ 2) volume a b := by
    have h := IntervalIntegrable.sum (Finset.range J) (fun j _ => hI j)
    convert h using 1
    ext t
    rw [Finset.sum_apply]
  have hpt : ∀ t : ℝ,
      ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), (∑ j ∈ Finset.range J, w j m) * f m‖ ^ 2 ≤
      (J : ℝ) * ∑ j ∈ Finset.range J, ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), w j m * f m‖ ^ 2 := by
    intro t
    have hs : (∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), (∑ j ∈ Finset.range J, w j m) * f m) =
        ∑ j ∈ Finset.range J, ∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), w j m * f m := by
      simp_rw [Finset.sum_mul]
      exact Finset.sum_comm
    rw [hs]
    calc
      _ ≤ (∑ j ∈ Finset.range J, ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), w j m * f m‖) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2
      _ ≤ ((Finset.range J).card : ℝ) *
          ∑ j ∈ Finset.range J, ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), w j m * f m‖ ^ 2 :=
        sq_sum_le_card_mul_sum_sq
      _ = _ := by rw [Finset.card_range]
  calc
    _ ≤ ∫ t in a..b, (J : ℝ) * ∑ j ∈ Finset.range J,
        ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), w j m * f m‖ ^ 2 :=
      intervalIntegral.integral_mono_on hab hI0 (hIs.const_mul _) (fun t _ => hpt t)
    _ = (J : ℝ) * ∑ j ∈ Finset.range J, ∫ t in a..b,
        ‖∑ m ∈ S.filter (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H), w j m * f m‖ ^ 2 := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finsetSum (fun j _ => hI j)]
    _ ≤ (J : ℝ) * ∑ _j ∈ Finset.range J, K :=
      mul_le_mul_of_nonneg_left (Finset.sum_le_sum e) (Nat.cast_nonneg J)
    _ = (J : ℝ) ^ 2 * K := by
      rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

/-- P0088 page 11 Lemma 3.4, as applied on page 15 after display 52 to the
second sum of display 52, with x = Y, y = H, (m, k) = (p, m / p) and
z = z1 = Y^(1/6 + eps/2). The prime p runs from z1 up to the cutoff
z0 = Y^(1/4) P^(-2) of page 8 display 34. The range of p is split into at most
3 log X dyadic blocks, each bounded by Lemma 3.4 with A + 2 in place of A.
CONDITIONAL ON lemma34_second_sum_dyadic. -/
theorem lemma34_second_sum (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, ∀ q : ℕ, ∀ a : ℤ, IsCoprime a (q : ℤ) →
        Real.log X ^ B < (q : ℝ) → (q : ℝ) ≤ H / Real.log X ^ B →
        |(q : ℝ) * α - a| < (H / Real.log X ^ B)⁻¹ →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖∑ m ∈ (squareWindow (windowY X ε)).filter
              (fun m : ℕ => t < (m : ℝ) ^ 2 ∧ (m : ℝ) ^ 2 ≤ t + H),
            (∑ p ∈ (Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m),
              roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) *
              fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ))‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B2, hB2, h2⟩ := lemma34_second_sum_dyadic (A + 2) (by linarith)
  refine ⟨B2, hB2, fun B hB ε hε => ?_⟩
  have hBpos : 0 < B := hB2.trans_le hB
  obtain ⟨C, X0, hC, hX0, k⟩ := h2 B hB ε hε
  refine ⟨9 * C, max X0 3, by positivity, hX0.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHX α q a hcop hqP hqQ hclose
  have hXa : X0 ≤ X := (le_max_left _ _).trans hX
  have hX3 : 3 ≤ X := (le_max_right _ _).trans hX
  have hX1 : 1 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    linarith [Real.exp_one_lt_d9]
  have hL : 0 < Real.log X := by linarith
  have hε1 := written_range_epsilon_le hX1 hH hHX
  have hY0 : 0 < windowY X ε := by
    unfold windowY
    exact Real.rpow_pos_of_pos (by linarith) _
  have hz0X : windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤ X := by
    have hP1 : 1 ≤ Real.log X ^ B := Real.one_le_rpow hL1 hBpos.le
    have hw : (Real.log X ^ B) ^ (-2 : ℤ) ≤ 1 := by
      rw [zpow_neg]
      exact inv_le_one_of_one_le₀ (one_le_zpow₀ hP1 (by norm_num))
    have hY4 : windowY X ε ^ (1 / 4 : ℝ) ≤ X := by
      rw [windowY, ← Real.rpow_mul (by linarith)]
      calc
        X ^ ((7 / 12 + ε / 2) * (1 / 4)) ≤ X ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hX1.le (by linarith)
        _ = X := Real.rpow_one X
    have hY4' : 0 ≤ windowY X ε ^ (1 / 4 : ℝ) := Real.rpow_nonneg hY0.le _
    calc
      _ ≤ windowY X ε ^ (1 / 4 : ℝ) * 1 := mul_le_mul_of_nonneg_left hw hY4'
      _ ≤ X := by linarith
  obtain ⟨J, hJ1, hJ2⟩ : ∃ J : ℕ, X < (2 : ℝ) ^ J ∧ (J : ℝ) ≤ 3 * Real.log X := by
    refine ⟨⌊Real.logb 2 X⌋₊ + 1, ?_, ?_⟩
    · have h1 : Real.logb 2 X < ((⌊Real.logb 2 X⌋₊ + 1 : ℕ) : ℝ) := by
        push_cast
        exact Nat.lt_floor_add_one _
      have h2 := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) h1
      rwa [Real.rpow_logb (by norm_num) (by norm_num) (by linarith), Real.rpow_natCast] at h2
    · push_cast
      have hlb : 0 ≤ Real.logb 2 X := Real.logb_nonneg (by norm_num) hX1.le
      have h1 : (⌊Real.logb 2 X⌋₊ : ℝ) ≤ Real.logb 2 X := Nat.floor_le hlb
      have h2 : Real.logb 2 X ≤ 2 * Real.log X := by
        rw [Real.logb, div_le_iff₀ (Real.log_pos (by norm_num))]
        nlinarith [Real.log_two_gt_d9]
      linarith
  have hpart : ∀ m : ℕ,
      (∑ p ∈ (Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m),
        roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p)) =
      ∑ j ∈ Finset.range J, ∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
          (fun p : ℕ => (2 : ℝ) ^ j ≤ (p : ℝ) ∧ (p : ℝ) < 2 * 2 ^ j),
        roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p) := by
    intro m
    refine dyadic_partition _ J _ fun p hp => ?_
    obtain ⟨_, hpp, _, hpz, _⟩ := Finset.mem_filter.mp hp
    have hlt : (p : ℝ) < (2 : ℝ) ^ J := by linarith
    exact ⟨hpp.ne_zero, by exact_mod_cast hlt⟩
  simp_rw [hpart]
  refine (dyadic_mean_square_le (squareWindow (windowY X ε)) J
    (fun j m => ∑ p ∈ ((Finset.range (m + 1)).filter (fun p : ℕ => p.Prime ∧
                windowY X ε ^ (1 / 6 + ε / 2) ≤ (p : ℝ) ∧
                (p : ℝ) < windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ∧
                p ∣ m)).filter
        (fun p : ℕ => (2 : ℝ) ^ j ≤ (p : ℝ) ∧ (p : ℝ) < 2 * 2 ^ j),
      roughWeight (windowY X ε ^ (1 / 6 + ε / 2)) (m / p))
    (fun m : ℕ => (fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) : ℂ))
    H _ _ (C * H ^ 2 / Real.log X ^ (A + 2)) (by linarith)
    (fun j _ => k X H hXa hH hHX α q a hcop hqP hqQ hclose ((2 : ℝ) ^ j) (one_le_pow₀ (by norm_num)))).trans ?_
  have hLA : 0 < Real.log X ^ A := Real.rpow_pos_of_pos hL A
  have hpow : Real.log X ^ (A + 2) = Real.log X ^ A * Real.log X ^ 2 := by
    rw [Real.rpow_add hL, Real.rpow_two]
  rw [hpow]
  have hJ0 : (0 : ℝ) ≤ J := Nat.cast_nonneg J
  have hJsq : (J : ℝ) ^ 2 ≤ 9 * Real.log X ^ 2 := by nlinarith
  have hK : 0 ≤ C * H ^ 2 / (Real.log X ^ A * Real.log X ^ 2) :=
    div_nonneg (by positivity) (mul_pos hLA (pow_pos hL 2)).le
  calc
    _ ≤ 9 * Real.log X ^ 2 * (C * H ^ 2 / (Real.log X ^ A * Real.log X ^ 2)) :=
      mul_le_mul_of_nonneg_right hJsq hK
    _ = 9 * C * H ^ 2 / Real.log X ^ A := by
      field_simp

/-- P0088 page 4 display 14 in the written range of page 16: Q = H P^(-1) is
at least one, so that Dirichlet's theorem applies with denominators up to Q. -/
theorem logPower_le_H (B ε : ℝ) (hε : 0 < ε) :
    ∃ X0 : ℝ, 2 ≤ X0 ∧ ∀ X H : ℝ, X0 ≤ X → X ^ (7 / 18 + ε) ≤ H →
      Real.log X ^ B ≤ H := by
  have ht := (isLittleO_log_rpow_rpow_atTop B (by norm_num : (0 : ℝ) < 7 / 18)).bound
    (by norm_num : (0 : ℝ) < 1)
  obtain ⟨X0, h0⟩ := Filter.eventually_atTop.mp ht
  refine ⟨max 2 X0, le_max_left _ _, fun X H hX hH => ?_⟩
  have hX2 : 2 ≤ X := (le_max_left _ _).trans hX
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have h := h0 X ((le_max_right _ _).trans hX)
  rw [one_mul, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_pos (Real.rpow_pos_of_pos hL B),
    abs_of_pos (Real.rpow_pos_of_pos (by linarith) _)] at h
  exact h.trans ((Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)).trans hH)

/-- P0088 page 4 display 15 and page 10 display 41: a point off the major
arcs has, by Dirichlet's theorem, a reduced fraction a / q with P < q ≤ Q and
|q alpha - a| < 1 / Q, where Q = H / P. This gives display 41 with y = H. -/
theorem minor_arc_dirichlet {H P α : ℝ} (hP : 0 < P) (hPH : P ≤ H)
    (hα : α ∉ majorArcs H P) :
    ∃ q : ℕ, ∃ a : ℤ, IsCoprime a (q : ℤ) ∧ P < (q : ℝ) ∧ (q : ℝ) ≤ H / P ∧
      |(q : ℝ) * α - a| < (H / P)⁻¹ := by
  have hQ1 : 1 ≤ H / P := (one_le_div hP).mpr hPH
  have hQ0 : 0 < H / P := lt_of_lt_of_le one_pos hQ1
  have hn : 0 < ⌊H / P⌋₊ := Nat.floor_pos.mpr hQ1
  obtain ⟨r, hr, hden⟩ := Real.exists_rat_abs_sub_le_and_den_le α hn
  have hq0 : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hcop : IsCoprime r.num (r.den : ℤ) := Rat.isCoprime_num_den r
  have hclose : |(r.den : ℝ) * α - r.num| < (H / P)⁻¹ := by
    have hrr : (r : ℝ) = r.num / r.den := Rat.cast_def r
    have he : (r.den : ℝ) * α - r.num = r.den * (α - r) := by
      rw [hrr]
      field_simp
    rw [he, abs_mul, abs_of_pos hq0]
    calc
      (r.den : ℝ) * |α - r| ≤ r.den * (1 / ((⌊H / P⌋₊ + 1 : ℝ) * r.den)) :=
        mul_le_mul_of_nonneg_left hr hq0.le
      _ = (⌊H / P⌋₊ + 1 : ℝ)⁻¹ := by
        field_simp
      _ < (H / P)⁻¹ := inv_strictAnti₀ hQ0 (Nat.lt_floor_add_one _)
  refine ⟨r.den, r.num, hcop, ?_, ?_, hclose⟩
  · by_contra h
    exact hα ⟨r.den, r.den_pos, not_lt.mp h, r.num, hcop, hclose.le⟩
  · exact (Nat.cast_le.mpr hden).trans (Nat.floor_le hQ0.le)

/-- P0088 page 11 Lemma 3.4 applied on page 15 to the two sums of display 52:
hypothesis A2.3 of page 7 for the rough weight, in the written range of page 16.
The statement is that of Task556a.lemma34_rough_minor_input.
CONDITIONAL ON lemma34_first_sum and lemma34_second_sum_dyadic. -/
theorem lemma34_rough_minor_input_route (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C X0 : ℝ, 0 < C ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X ^ (1 - ε) →
        ∀ α : ℝ, α ∉ majorArcs H (Real.log X ^ B) →
        (∫ t in windowY X ε / 4..windowY X ε,
          ‖roughShortSum (windowY X ε) (Real.log X ^ B) H α t‖ ^ 2) ≤
            C * H ^ 2 / Real.log X ^ A := by
  obtain ⟨B1, hB1, h1⟩ := lemma34_first_sum A hA
  obtain ⟨B2, hB2, h2⟩ := lemma34_second_sum A hA
  refine ⟨max B1 B2, lt_max_of_lt_left hB1, fun B hB ε hε => ?_⟩
  have hBpos : 0 < B := (lt_max_of_lt_left hB1).trans_le hB
  obtain ⟨C1, X1, hC1, hX1, k1⟩ := h1 B ((le_max_left _ _).trans hB) ε hε
  obtain ⟨C2, X2, hC2, hX2, k2⟩ := h2 B ((le_max_right _ _).trans hB) ε hε
  obtain ⟨X3, hX3, k3⟩ := display52_identity B ε hBpos hε
  obtain ⟨X4, hX4, k4⟩ := logPower_le_H B ε hε
  refine ⟨2 * C1 + 2 * C2, max X1 (max X2 (max X3 X4)), by positivity,
    hX1.trans (le_max_left _ _), ?_⟩
  intro X H hX hH hHX α hα
  have hXa : X1 ≤ X := (le_max_left _ _).trans hX
  have hXb : X2 ≤ X := ((le_max_left _ _).trans (le_max_right _ _)).trans hX
  have hXc : X3 ≤ X :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hX
  have hXd : X4 ≤ X :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans (le_max_right _ _))).trans hX
  have hX2 : 2 ≤ X := hX1.trans hXa
  have hL : 0 < Real.log X := Real.log_pos (by linarith)
  have hY : 0 < windowY X ε := by
    unfold windowY
    exact Real.rpow_pos_of_pos (by linarith) _
  have hq : 0 ≤ H ^ 2 / Real.log X ^ A := by positivity
  obtain ⟨q, a, hcop, hqP, hqQ, hclose⟩ :=
    minor_arc_dirichlet (Real.rpow_pos_of_pos hL B) (k4 X H hXd hH) hα
  have e1 := k1 X H hXa hH hHX α q a hcop hqP hqQ hclose
  have e2 := k2 X H hXb hH hHX α q a hcop hqP hqQ hclose
  unfold roughShortSum
  by_cases hz : windowY X ε ^ (1 / 4 : ℝ) * (Real.log X ^ B) ^ (-2 : ℤ) ≤
      windowY X ε ^ (1 / 6 + ε / 2)
  · refine (e1 _ hz).trans ?_
    have hr : C1 * H ^ 2 / Real.log X ^ A = C1 * (H ^ 2 / Real.log X ^ A) := by ring
    have hr' : (2 * C1 + 2 * C2) * H ^ 2 / Real.log X ^ A =
        (2 * C1 + 2 * C2) * (H ^ 2 / Real.log X ^ A) := by ring
    rw [hr, hr']
    exact mul_le_mul_of_nonneg_right (by linarith) hq
  · have hid := k3 X hXc (not_le.mp hz).le
    refine (short_sum_sub_mean_square_le (squareWindow (windowY X ε)) _ _ _
      (fun m : ℕ => (fourier ((m ^ 2 : ℕ) : ℤ) (α : AddCircle (1 : ℝ)) : ℂ))
      H _ _ _ _ (by linarith) hid (e1 _ le_rfl) e2).trans ?_
    apply le_of_eq
    ring

end LeanLab.KumchevLiu2007.Eq33RouteD
