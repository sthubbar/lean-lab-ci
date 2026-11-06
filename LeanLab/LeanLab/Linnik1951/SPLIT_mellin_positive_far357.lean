/-
Split of the positive outer-interval Mellin square estimate `mellin_positive_far357`
into smaller steps. Nothing here changes a statement: `mellin_positive_far357_split`
repeats the target statement character for character and proves it from the four
OPEN leaves below, which record, in order, (1) the passage from a pointwise bound on
an interval to an integral bound, (2) the pointwise bound on the outer positive
interval, (3) the fact that the outer positive interval is nonempty, and (4) the
interval length. The proof of the assembly does not use `mellin_positive_far357`.
-/
import LeanLab.Linnik1951.Decomp357a

namespace LeanLab.Linnik1951

/-- LEAF. Step 1 of 4: interval arithmetic only. If the square norm of the damped
character prime sum is at most M at every point of the interval from u to v, and u
is at most v, then its integral over that interval is at most M times the length
v minus u. This is the step that turns a pointwise estimate into an integral
estimate; it carries no character information and no arithmetic input. -/
theorem far_integral_le_sup_length357 {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ)
    (M u v : ℝ) (hN : 1 ≤ N) (huv : u ≤ v)
    (hM : ∀ α : ℝ, α ∈ Set.Icc u v → ‖characterPrime280 χ N α‖ ^ 2 ≤ M) :
    (∫ α in u..v, ‖characterPrime280 χ N α‖ ^ 2) ≤ M * (v - u) := by
  have hi : IntervalIntegrable (fun α : ℝ => ‖characterPrime280 χ N α‖ ^ 2)
      MeasureTheory.volume u v :=
    ((continuous_character_prime357 χ N hN).norm.pow 2).intervalIntegrable u v
  calc
    _ ≤ ∫ _α in u..v, M :=
      intervalIntegral.integral_mono_on huv hi intervalIntegrable_const hM
    _ = _ := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring

/-- LEAF. Step 2 of 4: the pointwise bound on the outer positive interval. There
is a fixed positive constant C such that for every large N, every modulus q with
1 at most q at most N to the one seventh, every nonprincipal character mod q, and
every phase α between 4 over N and 1 over q times N to the one seventh, the square
norm of the damped character prime sum is at most C times N times log N to the
tenth. This is the local uniform estimate; the integral over the interval comes
later, from step 1 and the interval length. -/
theorem far_positive_sup357 (hG : LeanLab.DERZ1997.GRH) :
    ∃ C : ℝ, 0 < C ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 → ∀ α : ℝ,
          4 / (N : ℝ) ≤ α → α ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) →
            ‖characterPrime280 χ N α‖ ^ 2 ≤ C * (N : ℝ) * Real.log N ^ 10 := by
  sorry

/-- LEAF. Step 3 of 4: the outer positive interval is nonempty. For N at least
eight and every modulus q with 1 at most q at most N to the one seventh, the left
endpoint 4 over N is at most the right endpoint 1 over q times N to the one
seventh. The content is q times N to the one seventh at most N to the two
sevenths, against 4 at most N to the five sevenths; eight is the small case
threshold. -/
theorem far_left_endpoint_le_right357 (N : ℕ) (hN : 8 ≤ N) :
    ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
      4 / (N : ℝ) ≤ 1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  intro q hq hqt
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast (by omega : 0 < q)
  have hτpos : (0 : ℝ) < (N : ℝ) ^ (1 / 7 : ℝ) := Real.rpow_pos_of_pos hNpos _
  -- 4 at most N to the five sevenths
  have h5 : (4 : ℝ) ≤ (N : ℝ) ^ (5 / 7 : ℝ) := by
    have h8R : (8 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    have hpow : (4 : ℝ) ^ 7 ≤ (N : ℝ) ^ 5 := by
      have h1 : (8 : ℝ) ^ 5 ≤ (N : ℝ) ^ 5 := pow_le_pow_left₀ (by norm_num) h8R 5
      norm_num at h1 ⊢
      linarith
    have hle := Real.rpow_le_rpow (by positivity : (0 : ℝ) ≤ (4 : ℝ) ^ 7) hpow
      (by norm_num : (0 : ℝ) ≤ 1 / 7)
    have h4 : ((4 : ℝ) ^ ((7 : ℕ) : ℝ)) ^ (1 / 7 : ℝ) = 4 := by
      rw [← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 4)]
      rw [show (((7 : ℕ) : ℝ)) * (1 / 7 : ℝ) = 1 by norm_num, Real.rpow_one]
    have hN5 : ((N : ℝ) ^ ((5 : ℕ) : ℝ)) ^ (1 / 7 : ℝ) = (N : ℝ) ^ (5 / 7 : ℝ) := by
      rw [← Real.rpow_mul (le_of_lt hNpos)]
      norm_num
    rwa [← Real.rpow_natCast (4 : ℝ) 7, ← Real.rpow_natCast (N : ℝ) 5, h4, hN5] at hle
  have hstep1 : (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤ (N : ℝ) ^ (2 / 7 : ℝ) := by
    have hqτ : (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) ≤
        (N : ℝ) ^ (1 / 7 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) :=
      mul_le_mul_of_nonneg_right hqt hτpos.le
    have h2 : (N : ℝ) ^ (1 / 7 : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) = (N : ℝ) ^ (2 / 7 : ℝ) := by
      rw [← Real.rpow_add hNpos]
      norm_num
    linarith
  have hstep2 : (4 : ℝ) * (N : ℝ) ^ (2 / 7 : ℝ) ≤ (N : ℝ) := by
    have hm : (4 : ℝ) * (N : ℝ) ^ (2 / 7 : ℝ) ≤
        (N : ℝ) ^ (5 / 7 : ℝ) * (N : ℝ) ^ (2 / 7 : ℝ) :=
      mul_le_mul_of_nonneg_right h5 (Real.rpow_pos_of_pos hNpos _).le
    have he : (N : ℝ) ^ (5 / 7 : ℝ) * (N : ℝ) ^ (2 / 7 : ℝ) = (N : ℝ) := by
      rw [← Real.rpow_add hNpos]
      norm_num
    linarith
  have hmul : (4 : ℝ) * ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ≤ (N : ℝ) := by
    have h4q : (4 : ℝ) * ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) ≤
        4 * (N : ℝ) ^ (2 / 7 : ℝ) :=
      mul_le_mul_of_nonneg_left hstep1 (by norm_num)
    linarith
  have hqτpos : (0 : ℝ) < (q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ) := mul_pos hqpos hτpos
  rw [div_le_iff₀ hNpos, one_div_mul_eq_div, le_div_iff₀ hqτpos]
  exact hmul

/-- LEAF. Step 4 of 4: the length of the outer positive interval. For every N and
every modulus q at least one, the length 1 over q times N to the one seventh minus
4 over N is at most 1 over q times N to the one seventh. This is the elementary
last step, which discards the left endpoint contribution. -/
theorem far_length_le_inverse357 (N q : ℕ) (hq : 1 ≤ q) :
    1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) - 4 / (N : ℝ) ≤
      1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) := by
  have h : (0 : ℝ) ≤ 4 / (N : ℝ) := by positivity
  linarith

/-- Assembly of `mellin_positive_far357` from the four leaves above: the assembly
reads the pointwise constant C as the final constant B, checks that the outer
positive interval is nonempty, bounds the integral by the pointwise bound times
the interval length, and discards the left endpoint contribution. No step uses
`mellin_positive_far357` itself. -/
theorem mellin_positive_far357_split (hG : LeanLab.DERZ1997.GRH) :
    ∃ B : ℝ, 0 < B ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 < N →
      ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ (N : ℝ) ^ (1 / 7 : ℝ) →
        ∀ χ : DirichletCharacter ℂ q, χ ≠ 1 →
          (∫ α in (4 / (N : ℝ))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
            ‖characterPrime280 χ N α‖ ^ 2) ≤
              B * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log N ^ 10 := by
  obtain ⟨C, hC, Nsup, hsup⟩ := far_positive_sup357 hG
  refine ⟨C, hC, max Nsup 8, ?_⟩
  intro N hN q hq hqt χ hχ
  have hNsup : Nsup < N := lt_of_le_of_lt (le_max_left _ _) hN
  have h8 : 8 ≤ N := le_of_lt (lt_of_le_of_lt (le_max_right _ _) hN)
  have h1 : 1 ≤ N := by omega
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hqpos : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hL : (0 : ℝ) ≤ Real.log (N : ℝ) ^ 10 := Even.pow_nonneg (by norm_num) _
  have hMnn : (0 : ℝ) ≤ C * (N : ℝ) * Real.log (N : ℝ) ^ 10 :=
    mul_nonneg (mul_nonneg hC.le hNpos.le) hL
  have huv := far_left_endpoint_le_right357 N h8 q hq hqt
  have hlen := far_length_le_inverse357 N q hq
  have hpt : ∀ α : ℝ,
      α ∈ Set.Icc (4 / (N : ℝ)) (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) →
        ‖characterPrime280 χ N α‖ ^ 2 ≤ C * (N : ℝ) * Real.log (N : ℝ) ^ 10 := by
    intro α hα
    exact hsup N hNsup q hq hqt χ hχ α hα.1 hα.2
  have hInt := far_integral_le_sup_length357 χ N
    (C * (N : ℝ) * Real.log (N : ℝ) ^ 10) (4 / (N : ℝ))
    (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) h1 huv hpt
  calc (∫ α in (4 / (N : ℝ))..(1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))),
        ‖characterPrime280 χ N α‖ ^ 2)
      ≤ (C * (N : ℝ) * Real.log (N : ℝ) ^ 10) *
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) - 4 / (N : ℝ)) := hInt
    _ ≤ (C * (N : ℝ) * Real.log (N : ℝ) ^ 10) *
          (1 / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ))) :=
        mul_le_mul_of_nonneg_left hlen hMnn
    _ = C * (N : ℝ) / ((q : ℝ) * (N : ℝ) ^ (1 / 7 : ℝ)) * Real.log (N : ℝ) ^ 10 := by
        have hτne : ((N : ℝ) ^ (1 / 7 : ℝ)) ≠ 0 :=
          ne_of_gt (Real.rpow_pos_of_pos hNpos _)
        have hqne : (q : ℝ) ≠ 0 := ne_of_gt hqpos
        field_simp

end LeanLab.Linnik1951
