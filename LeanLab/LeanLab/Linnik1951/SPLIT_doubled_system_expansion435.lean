/-
Split of the explicit local system expansion of page 166 equation 9.1 into four
smaller supplies: the character orthogonality chain, the principal square mass,
the nonprincipal Mellin sum, and the single denominator case. The assembly below
proves the exact statement of doubled_system_expansion435 from those supplies
without using it.

AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Linnik1951.Decomp435b

namespace LeanLab.Linnik1951

open MeasureTheory

/-- LEAF. The character orthogonality chain of page 160 before equation 5.4
applied to the square norm on one doubled system: the square integral over the
system in the unit interval is at most a constant over the totient of q times the
principal square integral over the doubled interval of radius two over q tau, plus
the same constant over the totient of q times the sum of the nonprincipal square
integrals over that interval, plus a constant times two over tau times the sixth
power of log N from the section two error. Unconditional, for any modulus q at
least two and any tau at least four. -/
theorem doubled_system_characters435 :
    ∃ B : ℝ, 0 < B ∧ ∀ (N q : ℕ) [NeZero q] (τ : ℝ), 1 ≤ N → 2 ≤ q → 4 ≤ τ →
      (∫ α in arcSystem111 q τ ∩ Set.Icc 0 1, ‖primeFourier111 N α‖ ^ 2) ≤
        B / (q.totient : ℝ) *
          ((∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
              ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) +
            (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ∫ z in -(2 / ((q : ℝ) * τ))..(2 / ((q : ℝ) * τ)),
                ‖characterPrime280 χ N z‖ ^ 2)) +
        B * (2 / τ) * Real.log N ^ 6 := by
  sorry

/-- LEAF. The principal square mass of page 159 before equation 5.3 with the
logarithmic saving: for the trivial character the square integral over any
interval of radius at most one half is at most a constant times N over log N.
This is the full period square sum, so the saving is the reciprocal of log N and
no power of N is lost. Unconditional, for every modulus. -/
theorem principal_mass435 :
    ∃ P : ℝ, 0 < P ∧ ∀ (N q : ℕ) [NeZero q] (r : ℝ), 3 ≤ N → 0 ≤ r → r ≤ 1 / 2 →
      (∫ z in -r..r, ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) ≤
        P * ((N : ℝ) / Real.log N) := by
  sorry

/-- LEAF. Page 159 equation 5.2 summed over the nonprincipal characters, under
the hypothesis of page 154: the sum of the nonprincipal square integrals over an
interval of radius two over R is at most a constant times the totient of q times
N over R times the thirteenth power of log N, for R between one and N to the two
sevenths. This is the Mellin estimate alone, with no integral over the doubled
system and no prime square mass. -/
theorem nonprincipal_sum435 (hG : LeanLab.DERZ1997.GRH) :
    ∃ X : ℝ, 0 < X ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N → ∀ (q : ℕ) [NeZero q], 2 ≤ q →
      (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) → ∀ R : ℝ, 1 ≤ R → R ≤ (N : ℝ) ^ (2 / 7 : ℝ) →
        (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
            ∫ z in -(2 / R)..(2 / R), ‖characterPrime280 χ N z‖ ^ 2) ≤
          X * (q.totient : ℝ) * ((N : ℝ) / R * Real.log N ^ 13) := by
  sorry

/-- LEAF. Page 166 equation 9.1 at denominator one, the case the character chain
cannot reach because the totient of one has no nonprincipal character. The
square integral over the single doubled system of denominator one is at most a
constant times N over log N. Unconditional. -/
theorem one_denominator_mass435 :
    ∃ Q : ℝ, 0 < Q ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      (∫ α in arcSystem111 1 ((N : ℝ) ^ (1 / 7 : ℝ)) ∩ Set.Icc 0 1,
        ‖primeFourier111 N α‖ ^ 2) ≤ Q * ((N : ℝ) / Real.log N) := by
  sorry

/-- Page 166 equation 9.1 at a modulus at least two. With the radius two over
q tau, the principal and nonprincipal supplies inserted and the constants of the
split, the local expression is at most the printed principal totient term plus
the printed error term. Pure real arithmetic: each of the three pieces is at
most its own term once N exceeds the constant scale of the split. -/
private theorem expansion_absorb435 (B P X Q : ℝ) (N q : ℕ)
    (hB : 0 < B) (hP : 0 < P) (hX : 0 < X) (hQ : 0 < Q)
    (hN3 : 3 ≤ N) (hq : 1 ≤ q) (hlog : 1 ≤ Real.log N)
    (h2B : 2 * B ≤ (B * P + B * X + 2 * B + Q) * (N : ℝ)) :
    B / (q.totient : ℝ) *
        (P * ((N : ℝ) / Real.log N) +
          X * (q.totient : ℝ) *
            ((N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13)) +
      B * (2 / (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 6 ≤
      (B * P + B * X + 2 * B + Q) *
        ((N : ℝ) / q.totient / Real.log N +
          (N : ℝ) * Real.log N ^ 13 *
            (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
              2 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := by
  have hN0 : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hf : (0 : ℝ) < (q.totient : ℝ) := by
    exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
  have hl : (0 : ℝ) < Real.log N := lt_of_lt_of_le zero_lt_one hlog
  have ht : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hN0 _
  have ht1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) :=
    Real.one_le_rpow (by exact_mod_cast (show 1 ≤ N by omega)) (by norm_num)
  have hqr : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hR : (0 : ℝ) < (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by positivity
  have hR1 : (1 : ℝ) ≤ (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by nlinarith
  have hs : (0 : ℝ) < Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) :=
    Real.sqrt_pos.mpr hR
  have hs1 : (1 : ℝ) ≤ Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
    have h := Real.sqrt_le_sqrt hR1
    rwa [Real.sqrt_one] at h
  have hs2 : Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) *
      Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) =
        (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := Real.mul_self_sqrt hR.le
  have hC : (0 : ℝ) < B * P + B * X + 2 * B + Q := by positivity
  have hCP : B * P ≤ B * P + B * X + 2 * B + Q := by
    nlinarith [hB.le, hP.le, hX.le, hQ.le]
  have hCX : B * X ≤ B * P + B * X + 2 * B + Q := by
    nlinarith [hB.le, hP.le, hX.le, hQ.le]
  have hCs : B * X ≤ (B * P + B * X + 2 * B + Q) *
      Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by nlinarith [hCX, hs1, hC]
  have key : B / (q.totient : ℝ) *
        (P * ((N : ℝ) / Real.log N) +
          X * (q.totient : ℝ) *
            ((N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13)) +
      B * (2 / (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 6 =
      (B * P) * ((N : ℝ) / ((q.totient : ℝ) * Real.log N)) +
        (B * X) * ((N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13) +
        (2 * B) * (Real.log N ^ 6 / (N : ℝ) ^ (1 / 7 : ℝ)) := by
    field_simp
  have h1 : (B * P) * ((N : ℝ) / ((q.totient : ℝ) * Real.log N)) ≤
      (B * P + B * X + 2 * B + Q) * ((N : ℝ) / ((q.totient : ℝ) * Real.log N)) :=
    mul_le_mul_of_nonneg_right hCP (by positivity)
  have hx : (B * X) * (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) ≤
      (B * P + B * X + 2 * B + Q) *
        (2 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
    rw [show (B * X) * (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) =
      B * X / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) by ring,
      show (B * P + B * X + 2 * B + Q) *
        (2 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) =
        (2 * (B * P + B * X + 2 * B + Q)) /
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) by ring]
    rw [div_le_div_iff₀ hR hs]
    have hmul : B * X * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ≤
        (B * P + B * X + 2 * B + Q) *
          (Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) *
            Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by
      calc B * X * Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))
          ≤ ((B * P + B * X + 2 * B + Q) *
              Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) *
              Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) :=
            mul_le_mul_of_nonneg_right hCs hs.le
        _ = _ := by ring
    have hpos2 : (0 : ℝ) ≤ (B * P + B * X + 2 * B + Q) *
        (Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) *
          Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by positivity
    nlinarith [hmul, hpos2, hs2, hC]
  have h2 : (B * X) * ((N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13) ≤
      (B * P + B * X + 2 * B + Q) *
        ((N : ℝ) * Real.log N ^ 13 *
          (2 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := by
    have hM : (0 : ℝ) ≤ (N : ℝ) * Real.log N ^ 13 := by positivity
    calc (B * X) * ((N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13) =
          ((N : ℝ) * Real.log N ^ 13) *
            ((B * X) * (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := by ring
      _ ≤ ((N : ℝ) * Real.log N ^ 13) *
            ((B * P + B * X + 2 * B + Q) *
              (2 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) :=
            mul_le_mul_of_nonneg_left hx hM
      _ = _ := by ring
  have h3 : (2 * B) * (Real.log N ^ 6 / (N : ℝ) ^ (1 / 7 : ℝ)) ≤
      (B * P + B * X + 2 * B + Q) *
        ((N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ))) := by
    have h6 : Real.log N ^ 6 ≤ Real.log N ^ 13 :=
      pow_le_pow_right₀ hlog (by norm_num)
    have hnum : (2 * B) * Real.log N ^ 6 ≤
        (B * P + B * X + 2 * B + Q) * ((N : ℝ) * Real.log N ^ 13) := by
      have h1' := mul_le_mul_of_nonneg_right h2B (le_of_lt (pow_pos hl 6))
      have h2' := mul_le_mul_of_nonneg_left h6 (by positivity : (0 : ℝ) ≤
        (B * P + B * X + 2 * B + Q) * (N : ℝ))
      nlinarith [h1', h2']
    calc (2 * B) * (Real.log N ^ 6 / (N : ℝ) ^ (1 / 7 : ℝ)) =
          ((2 * B) * Real.log N ^ 6) / (N : ℝ) ^ (1 / 7 : ℝ) := by ring
      _ ≤ ((B * P + B * X + 2 * B + Q) * ((N : ℝ) * Real.log N ^ 13)) /
            (N : ℝ) ^ (1 / 7 : ℝ) := div_le_div_of_nonneg_right hnum ht.le
      _ = _ := by ring
  calc B / (q.totient : ℝ) *
        (P * ((N : ℝ) / Real.log N) +
          X * (q.totient : ℝ) *
            ((N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13)) +
      B * (2 / (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 6 =
      (B * P) * ((N : ℝ) / ((q.totient : ℝ) * Real.log N)) +
        (B * X) * ((N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13) +
        (2 * B) * (Real.log N ^ 6 / (N : ℝ) ^ (1 / 7 : ℝ)) := key
    _ ≤ (B * P + B * X + 2 * B + Q) * ((N : ℝ) / ((q.totient : ℝ) * Real.log N)) +
          (B * P + B * X + 2 * B + Q) *
            ((N : ℝ) * Real.log N ^ 13 *
              (2 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) +
          (B * P + B * X + 2 * B + Q) *
            ((N : ℝ) * Real.log N ^ 13 * (1 / (N : ℝ) ^ (1 / 7 : ℝ))) := by
        linarith [h1, h2, h3]
    _ = _ := by
        rw [← mul_add, ← mul_add]
        congr 1
        field_simp
        ring

/-- Page 166 equation 9.1. The exact statement of
doubled_system_expansion435, proved from the four supplies above without using
it. -/
theorem doubled_system_expansion435_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        (∫ α in arcSystem111 q ((N : ℝ) ^ (1 / 7 : ℝ)) ∩ Set.Icc 0 1,
          ‖primeFourier111 N α‖ ^ 2) ≤
          C * ((N : ℝ) / q.totient / Real.log N +
            (N : ℝ) * Real.log N ^ 13 *
              (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
                2 / Real.sqrt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) := by
  classical
  obtain ⟨B, hB, hchar⟩ := doubled_system_characters435
  obtain ⟨P, hP, hprin⟩ := principal_mass435
  obtain ⟨X, hX, Nx, hsum⟩ := nonprincipal_sum435 hG
  obtain ⟨Q, hQ, Nq, hone⟩ := one_denominator_mass435
  obtain ⟨L, hL⟩ := exists_nat_gt (Real.exp 1)
  obtain ⟨Nc, hNc⟩ := exists_nat_gt (2 * B / (B * P + B * X + 2 * B + Q))
  refine ⟨B * P + B * X + 2 * B + Q, by positivity, 1 + L + 16384 + Nx + Nq + Nc, ?_⟩
  intro N hN q hq hqt
  have hN1 : 1 ≤ N := by omega
  have hLN : L < N := by omega
  have hbig : 16384 < N := by omega
  have hxN : Nx < N := by omega
  have hqN : Nq < N := by omega
  have hcN : Nc < N := by omega
  have hNr : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hNr1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN1
  have hlog : 1 ≤ Real.log N := by
    have hNR : (L : ℝ) < (N : ℝ) := by exact_mod_cast hLN
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (hL.trans hNR).le
  have hCpos : (0 : ℝ) < B * P + B * X + 2 * B + Q := by positivity
  have h2B : 2 * B ≤ (B * P + B * X + 2 * B + Q) * (N : ℝ) := by
    have hNcR : (Nc : ℝ) < (N : ℝ) := by exact_mod_cast hcN
    have h1 : 2 * B < (B * P + B * X + 2 * B + Q) * (Nc : ℝ) := by
      have h := hNc
      rw [div_lt_iff₀ hCpos] at h
      linarith [h]
    nlinarith [hCpos, hNcR]
  by_cases hq1 : q = 1
  · subst hq1
    have hone' := hone N hqN
    have hQle : Q ≤ B * P + B * X + 2 * B + Q := by
      nlinarith [hB.le, hP.le, hX.le, hQ.le]
    have htot : ((Nat.totient 1 : ℕ) : ℝ) = 1 := by simp
    have hnl : (0 : ℝ) ≤ (N : ℝ) / Real.log N := by positivity
    have hZ : (0 : ℝ) ≤ (N : ℝ) * Real.log N ^ 13 *
        (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
          2 / Real.sqrt ((1 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) := by positivity
    have hstep1 : Q * ((N : ℝ) / Real.log N) ≤
        (B * P + B * X + 2 * B + Q) * ((N : ℝ) / Real.log N) :=
      mul_le_mul_of_nonneg_right hQle hnl
    have hCZ : (0 : ℝ) ≤ (B * P + B * X + 2 * B + Q) *
        ((N : ℝ) * Real.log N ^ 13 *
          (1 / (N : ℝ) ^ (1 / 7 : ℝ) +
            2 / Real.sqrt ((1 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))) :=
      mul_nonneg hCpos.le hZ
    rw [htot, Nat.cast_one, div_one]
    rw [mul_add]
    linarith [hone', hstep1, hCZ]
  · have hq2 : 2 ≤ q := by omega
    haveI : NeZero q := ⟨by omega⟩
    have hf : (0 : ℝ) < (q.totient : ℝ) := by
      exact_mod_cast Nat.totient_pos.mpr (by omega : 0 < q)
    have ht : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNr _
    have ht1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) :=
      Real.one_le_rpow hNr1 (by norm_num)
    have ht4 : 4 ≤ (N : ℝ) ^ (1 / 7 : ℝ) := by
      have h4 : ((4 : ℝ) ^ 7) ^ (1 / 7 : ℝ) = 4 := by
        rw [← Real.rpow_natCast (4 : ℝ) 7, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
        norm_num
      rw [← h4]
      refine Real.rpow_le_rpow (by norm_num) ?_ (by norm_num)
      have h16 : (16384 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hbig.le
      norm_num
      linarith
    have hq8 : (1 : ℝ) ≤ (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by
      have hqr : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
      nlinarith [ht1, hqr]
    have hqt2 : (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (2 / 7 : ℝ) := by
      have he : (N : ℝ) ^ (1 / 7 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) =
          (N : ℝ) ^ (2 / 7 : ℝ) := by
        rw [← Real.rpow_add hNr]
        norm_num
      nlinarith [hqt, ht1]
    have hR8 : 4 ≤ (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := by
      have hqr : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast (show 1 ≤ q by omega)
      nlinarith [ht4, ht, hqr]
    have hchar' := hchar N q ((N : ℝ) ^ (1 / 7 : ℝ)) hN1 hq2 ht4
    have hprin' := hprin N q (2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) (by omega)
      (by positivity) (by
        rw [div_le_iff₀ (by positivity : (0 : ℝ) < (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))]
        linarith [hR8])
    have hsum' := hsum N hxN q hq2 hqt ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) hq8 hqt2
    have hA : (∫ z in -(2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
          ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) +
        (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
          ∫ z in -(2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            ‖characterPrime280 χ N z‖ ^ 2) ≤
        P * ((N : ℝ) / Real.log N) +
          X * (q.totient : ℝ) *
            ((N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13) :=
      add_le_add hprin' hsum'
    refine (hchar'.trans ?_).trans (expansion_absorb435 B P X Q N q hB hP hX hQ
      (by omega) (by omega) hlog h2B)
    have hmul : B / (q.totient : ℝ) *
          ((∫ z in -(2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
              ‖characterPrime280 (1 : DirichletCharacter ℂ q) N z‖ ^ 2) +
            (∑ χ ∈ Finset.univ.filter (fun χ : DirichletCharacter ℂ q => χ ≠ 1),
              ∫ z in -(2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)))..(2 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
                ‖characterPrime280 χ N z‖ ^ 2)) ≤
        B / (q.totient : ℝ) *
          (P * ((N : ℝ) / Real.log N) +
            X * (q.totient : ℝ) *
              ((N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 13)) :=
      mul_le_mul_of_nonneg_left hA (by positivity)
    exact add_le_add hmul (le_refl _)

end LeanLab.Linnik1951
