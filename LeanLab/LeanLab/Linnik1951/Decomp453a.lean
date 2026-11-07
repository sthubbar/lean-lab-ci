/-
P0093 page 166 equation 9.1. Explicit obstruction for the dead single arc split.
The lower bound audits that split. It is not a claim of a paper error.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Audit1622

namespace LeanLab.Linnik1951

open MeasureTheory Filter
open scoped Topology

/-- Audit of P0093 page 166 equation 9.1 against the fresh single arc leaf.
The arc about one half has mass at least N over 13824 log cubed N under
three explicit size conditions. This uses the existing half phase lower
bound and Mathlib Chebyshev, with no GRH input. -/
theorem half_arc_mass_lower453 (N : ℕ)
    (hl1 : 1 ≤ Real.log N) (hl240 : 240 * Real.log N ≤ (N : ℝ))
    (hlogs : Real.log ((N : ℝ) + 1) ≤ ((N : ℝ) + 1) / 10) :
    (N : ℝ) / (13824 * Real.log N ^ 3) ≤
      ∫ α in Set.Icc ((1 : ℝ) / 2 - 1 / (2 * (N : ℝ) ^ (1 / 7 : ℝ)))
          (1 / 2 + 1 / (2 * (N : ℝ) ^ (1 / 7 : ℝ))),
        ‖primeFourier111 N α‖ ^ 2 := by
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
    have h := Audit1622.half_arc_lower N hN1 L M rfl hLe (α - 1 / 2) hz hMpos
    rw [show (1 / 2 + (α - 1 / 2) : ℝ) = α by ring] at h
    exact pow_le_pow_left₀ hYpos.le (hX.trans h) 2
  -- compare the two windows
  set τ : ℝ := (N : ℝ) ^ (1 / 7 : ℝ) with hτ
  have hτpos : 0 < τ := by positivity
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
  exact hlow.trans ((show 2 * δ * Y ^ 2 ≤ _ from by nlinarith [hconst]).trans hmono)

/-- Audit of P0093 page 166 equation 9.1. For every real coefficient B,
all sufficiently large N violate the dead single arc bound at q two and
a one. The denominator is admissible for those N. No GRH is assumed. -/
theorem eventual_half_arc_violation453 (B : ℝ) :
    ∀ᶠ N : ℕ in atTop,
      (2 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) ∧
      B * (N : ℝ) / (2 * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 <
        ∫ α in Set.Icc ((1 : ℝ) / 2 - 1 / (2 * (N : ℝ) ^ (1 / 7 : ℝ)))
            (1 / 2 + 1 / (2 * (N : ℝ) ^ (1 / 7 : ℝ))),
          ‖primeFourier111 N α‖ ^ 2 := by
  let C := max B 1
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  filter_upwards [Audit1622.eventual_facts C hC] with N hN
  obtain ⟨hl1, hl240, hτ2, hlogs, hfinal⟩ := hN
  refine ⟨hτ2, ?_⟩
  have hNp : (0 : ℝ) < N := by
    have : N ≠ 0 := by intro h; norm_num [h] at hl1
    exact_mod_cast Nat.pos_of_ne_zero this
  have hlp : 0 < Real.log N := lt_of_lt_of_le zero_lt_one hl1
  have hτp : 0 < (N : ℝ) ^ (1 / 7 : ℝ) := by positivity
  have hB : B * (N : ℝ) / (2 * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 ≤
      C * (N : ℝ) / (2 * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 := by
    gcongr
    exact le_max_left _ _
  have hupper : C * (N : ℝ) / (2 * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 <
      (N : ℝ) / (13824 * Real.log N ^ 3) := by
    rw [div_mul_eq_mul_div, div_lt_div_iff₀ (by positivity) (by positivity)]
    have hscaled := mul_lt_mul_of_pos_right hfinal (show 0 < (N : ℝ) * 2 by positivity)
    nlinarith
  exact (hB.trans_lt hupper).trans_le (half_arc_mass_lower453 N hl1 hl240 hlogs)

/-- Audit of P0093 page 166 equation 9.1. The fixed reduced rational
one half violates the proposed single arc error bound beyond every
natural threshold. This records the counterexample with its witness. -/
theorem half_arc_counterexample453 (B : ℝ) (N0 : ℕ) :
    ∃ N : ℕ, N0 < N ∧
      (2 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) ∧
      B * (N : ℝ) / (2 * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13 <
        ∫ α in Set.Icc ((1 : ℝ) / 2 - 1 / (2 * (N : ℝ) ^ (1 / 7 : ℝ)))
            (1 / 2 + 1 / (2 * (N : ℝ) ^ (1 / 7 : ℝ))),
          ‖primeFourier111 N α‖ ^ 2 := by
  obtain ⟨N, hN, hlarge⟩ :=
    ((eventual_half_arc_violation453 B).and (eventually_gt_atTop N0)).exists
  exact ⟨N, hlarge, hN⟩

/-- Audit of P0093 page 166 equation 9.1. Named negation of the
single arc leaf conclusion, from the explicit denominator two witness.
This refutes the fresh split conclusion and does not refute the paper. -/
theorem not_local_prime_mass_conclusion453 : ¬ Audit1622.LeafLocalMass := by
  rintro ⟨B, hB, N0, hmass⟩
  obtain ⟨N, hN, hq, hbad⟩ := half_arc_counterexample453 B N0
  have h := hmass N hN 2 (by norm_num) hq 1 (by norm_num)
  norm_num only [Nat.cast_ofNat, Int.cast_ofNat] at h
  exact (not_lt_of_ge h) hbad

/-- Audit of P0093 page 166 equation 9.1. The original conditional
single arc leaf is equivalent to the negation of its GRH hypothesis.
No truth value of GRH is established. -/
theorem local_mass_iff_not_grh453 :
    (LeanLab.DERZ1997.GRH → Audit1622.LeafLocalMass) ↔ ¬ LeanLab.DERZ1997.GRH := by
  exact ⟨fun h hG => not_local_prime_mass_conclusion453 (h hG),
    fun hn hG => (hn hG).elim⟩

/-- Concrete nonvacuity for the size conditions of half_arc_mass_lower453.
This checks the numerical audit conditions at N equal to 4096. -/
theorem half_arc_size_instance453 :
    1 ≤ Real.log (4096 : ℝ) ∧
      240 * Real.log (4096 : ℝ) ≤ 4096 ∧
      Real.log (4096 + 1 : ℝ) ≤ (4096 + 1 : ℝ) / 10 := by
  have h2lo : (1 / 2 : ℝ) ≤ Real.log 2 := by linarith [Real.log_two_gt_d9]
  have h2hi : Real.log 2 ≤ (1 : ℝ) := by
    linarith [Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)]
  have h12 : Real.log (4096 : ℝ) = 12 * Real.log 2 := by
    rw [show (4096 : ℝ) = 2 ^ 12 by norm_num, Real.log_pow]
    norm_num
  have h13 : Real.log (8192 : ℝ) = 13 * Real.log 2 := by
    rw [show (8192 : ℝ) = 2 ^ 13 by norm_num, Real.log_pow]
    norm_num
  have hmono : Real.log (4096 + 1 : ℝ) ≤ Real.log (8192 : ℝ) :=
    Real.log_le_log (by norm_num) (by norm_num)
  constructor
  · linarith
  constructor
  · linarith
  · calc
      _ ≤ Real.log (8192 : ℝ) := hmono
      _ = 13 * Real.log 2 := h13
      _ ≤ 13 := by linarith
      _ ≤ _ := by norm_num

end LeanLab.Linnik1951
