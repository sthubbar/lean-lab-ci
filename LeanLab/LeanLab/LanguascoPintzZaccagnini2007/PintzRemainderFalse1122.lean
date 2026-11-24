import LeanLab.LanguascoPintzZaccagnini2007.Decomp481a

/-!
FALSIFY unit `LanguascoPintzZaccagnini2007/SPLIT_pintz_explicit_formula481`, declaration
`leaf_remainder_bound481`, CLOUD S101 burst-20261122.

The proof of `leaf_remainder_bound481` on main commits the constants `c = ε₀ = B = 1`, `Cε = 1`
and the threshold `X₀ = 1`, then leaves one `sorry`. This file proves that the goal left at that
`sorry` cannot be closed, for any `H₀` and `T₀`.

The reason is that the leaf is uniform in the zero family: the trivial family `K = 0`, with only the
pole of conductor one, satisfies every hypothesis, and the Gamma pair sum does not depend on `P`.
So for two admissible values `P₁ < P₂` at the same `X` and `n` the bound gives
`|binaryMajor131 X n P₁ - binaryMajor131 X n P₂| ≤ 2 B (X exp (-c H) + X / sqrt T)` for every large
`H` and `T`, hence equality. At `X = n = 2` only the arc about `1/1` is major, the prime sum is
`log 2 · e(2α)`, and the major arc integral is `(log 2)^2 sin (2 π P) / (2 π)`. The values at
`P₁ = 2^(2/5)` and `P₂ = 2^(41/100)` differ since `2 π (P - 1) - π/2` lies in `[0, π]` there and
cosine is strictly decreasing on `[0, π]`.

P0045 page 5 states Lemma 4.1 only for the zeros of box (8), the actual family, so the paper does
not claim the uniform leaf. AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real MeasureTheory
open scoped Classical ArithmeticFunction.vonMangoldt

noncomputable section

/-- For `1 ≤ P < 2` the only major arc at `X = 2` is the one about `1/1`, of half width `P/2`. -/
theorem majorArcs131_two_eq {P : ℝ} (hP1 : 1 ≤ P) (hP2 : P < 2) :
    majorArcs131 2 P = Set.Icc (1 - P / 2) (1 + P / 2) := by
  have hP0 : 0 < P := by linarith
  have hw : (1 : ℝ) / arcQ131 2 P = P / 2 := by
    unfold arcQ131
    push_cast
    field_simp
  ext α
  simp only [majorArcs131, Set.mem_setOf_eq]
  constructor
  · rintro ⟨q, a, hq1, hqP, ha, -, hα⟩
    have hq : q = 1 := by
      have : (q : ℝ) < 2 := lt_of_le_of_lt hqP hP2
      have : q < 2 := by exact_mod_cast this
      omega
    subst hq
    have ha1 : a = 1 := by
      rw [Finset.mem_Icc] at ha
      omega
    subst ha1
    simp only [Nat.cast_one, one_mul, div_one, hw] at hα
    exact hα
  · intro hα
    refine ⟨1, 1, le_rfl, by simpa using hP1, by simp, Nat.coprime_one_left 1, ?_⟩
    simp only [Nat.cast_one, one_mul, div_one, hw]
    exact hα

/-- The prime exponential sum at `X = 2` is `log 2 · e(2α)`. -/
theorem primeSum131_two (α : ℝ) :
    primeSum131 2 α = ((Real.log 2 : ℝ) : ℂ) * phase131 (2 * α) := by
  unfold primeSum131
  rw [show (Finset.Icc 1 2 : Finset ℕ) = {1, 2} by decide]
  rw [Finset.sum_pair (by norm_num)]
  rw [ArithmeticFunction.vonMangoldt_apply_one,
    ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]
  push_cast
  ring

/-- The integrand of the major arc integral at `X = n = 2`, `k = 0`. -/
theorem integrand_two_two (α : ℝ) :
    primeSum131 2 α ^ 2 * powerSum131 2 α ^ 0 * phase131 (-((2 : ℕ) : ℝ) * α) =
      ((Real.log 2 : ℝ) : ℂ) ^ 2 * Complex.exp ((4 * π * Complex.I) * α) := by
  rw [primeSum131_two, pow_zero, mul_one]
  unfold phase131
  rw [mul_pow, sq (Complex.exp _), mul_assoc, ← Complex.exp_add, ← Complex.exp_add]
  congr 2
  push_cast
  ring

/-- `exp (4 π i (1 + x)) = cos (4 π x) + i sin (4 π x)`. -/
theorem exp_four_pi_I_one_add (x : ℝ) :
    Complex.exp ((4 * π * Complex.I) * ((1 + x : ℝ) : ℂ)) =
      ((Real.cos (4 * π * x) : ℝ) : ℂ) + ((Real.sin (4 * π * x) : ℝ) : ℂ) * Complex.I := by
  rw [show (4 * π * Complex.I) * ((1 + x : ℝ) : ℂ) =
      ((4 * π * x : ℝ) : ℂ) * Complex.I + ((2 : ℕ) : ℂ) * (2 * π * Complex.I) by
    push_cast; ring]
  rw [Complex.exp_add, Complex.exp_nat_mul_two_pi_mul_I, mul_one, Complex.exp_mul_I]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]

/-- `exp (4 π i (1 - x)) = cos (4 π x) - i sin (4 π x)`. -/
theorem exp_four_pi_I_one_sub (x : ℝ) :
    Complex.exp ((4 * π * Complex.I) * ((1 - x : ℝ) : ℂ)) =
      ((Real.cos (4 * π * x) : ℝ) : ℂ) - ((Real.sin (4 * π * x) : ℝ) : ℂ) * Complex.I := by
  rw [show (1 - x : ℝ) = 1 + -x by ring, exp_four_pi_I_one_add (-x),
    show 4 * π * -x = -(4 * π * x) by ring, Real.cos_neg, Real.sin_neg]
  push_cast
  ring

/-- The real part of the evaluated interval integral. -/
theorem re_aux_two_two (L s c : ℝ) :
    (((L : ℝ) : ℂ) ^ 2 * ((((c : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I -
      (((c : ℝ) : ℂ) - ((s : ℝ) : ℂ) * Complex.I)) / (4 * π * Complex.I))).re =
      L ^ 2 * s / (2 * π) := by
  have hI := Complex.I_ne_zero
  have hpi : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have h : ((L : ℝ) : ℂ) ^ 2 * ((((c : ℝ) : ℂ) + ((s : ℝ) : ℂ) * Complex.I -
      (((c : ℝ) : ℂ) - ((s : ℝ) : ℂ) * Complex.I)) / (4 * π * Complex.I)) =
      ((L ^ 2 * s / (2 * π) : ℝ) : ℂ) := by
    push_cast
    field_simp
    ring
  rw [h, Complex.ofReal_re]

/-- The major arc integral at `X = n = 2` for `1 ≤ P < 2`: `(log 2)^2 sin (2 π P) / (2 π)`. -/
theorem binaryMajor131_two_two {P : ℝ} (hP1 : 1 ≤ P) (hP2 : P < 2) :
    binaryMajor131 2 2 P = Real.log 2 ^ 2 * Real.sin (2 * π * P) / (2 * π) := by
  unfold binaryMajor131 majorContribution131
  rw [majorArcs131_two_eq hP1 hP2]
  simp_rw [integrand_two_two]
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
    intervalIntegral.integral_const_mul]
  have hc : (4 * π * Complex.I : ℂ) ≠ 0 := by
    have : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    simp [this, Complex.I_ne_zero]
  rw [integral_exp_mul_complex hc, exp_four_pi_I_one_add (P / 2), exp_four_pi_I_one_sub (P / 2),
    show 4 * π * (P / 2) = 2 * π * P by ring]
  exact re_aux_two_two _ _ _

/-- `(2^(2/5))^5 = 4`. -/
theorem two_rpow_two_fifths_pow_five : ((2 : ℝ) ^ ((2 : ℝ) / 5)) ^ (5 : ℕ) = 4 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    show (2 : ℝ) / 5 * ((5 : ℕ) : ℝ) = 2 by norm_num, Real.rpow_two]
  norm_num

/-- `(2^(1/2))^2 = 2`. -/
theorem two_rpow_half_sq : ((2 : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) = 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num : (0 : ℝ) ≤ 2),
    show (1 : ℝ) / 2 * ((2 : ℕ) : ℝ) = 1 by norm_num, Real.rpow_one]

/-- `1.25 ≤ 2^(2/5)`, since `1.25^5 < 4`. -/
theorem five_fourths_le_two_rpow : (5 / 4 : ℝ) ≤ (2 : ℝ) ^ ((2 : ℝ) / 5) := by
  by_contra h
  push_neg at h
  have h0 : 0 ≤ (2 : ℝ) ^ ((2 : ℝ) / 5) := Real.rpow_nonneg (by norm_num) _
  have h5 : ((2 : ℝ) ^ ((2 : ℝ) / 5)) ^ (5 : ℕ) < (5 / 4 : ℝ) ^ (5 : ℕ) :=
    pow_lt_pow_left₀ h h0 (by norm_num)
  rw [two_rpow_two_fifths_pow_five] at h5
  norm_num at h5

/-- `2^(41/100) ≤ 7/4`, since `2^(41/100) ≤ 2^(1/2)` and `2 < (7/4)^2`. -/
theorem two_rpow_le_seven_fourths : (2 : ℝ) ^ ((41 : ℝ) / 100) ≤ 7 / 4 := by
  have hle : (2 : ℝ) ^ ((41 : ℝ) / 100) ≤ (2 : ℝ) ^ ((1 : ℝ) / 2) :=
    Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  refine le_trans hle ?_
  by_contra h
  push_neg at h
  have h2 : ((7 / 4 : ℝ)) ^ (2 : ℕ) < ((2 : ℝ) ^ ((1 : ℝ) / 2)) ^ (2 : ℕ) :=
    pow_lt_pow_left₀ h (by norm_num) (by norm_num)
  rw [two_rpow_half_sq] at h2
  norm_num at h2

/-- The two endpoints `2^(2/5) < 2^(41/100)` of the admissible range at `X = 2` give different
major arc integrals at `n = 2`. -/
theorem binaryMajor131_two_two_ne :
    binaryMajor131 2 2 ((2 : ℝ) ^ ((2 : ℝ) / 5)) ≠
      binaryMajor131 2 2 ((2 : ℝ) ^ ((41 : ℝ) / 100)) := by
  set P₁ : ℝ := (2 : ℝ) ^ ((2 : ℝ) / 5) with hP₁
  set P₂ : ℝ := (2 : ℝ) ^ ((41 : ℝ) / 100) with hP₂
  have h12 : P₁ < P₂ := Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by norm_num)
  have hl : (5 / 4 : ℝ) ≤ P₁ := five_fourths_le_two_rpow
  have hu : P₂ ≤ 7 / 4 := two_rpow_le_seven_fourths
  rw [binaryMajor131_two_two (by linarith) (by linarith),
    binaryMajor131_two_two (by linarith) (by linarith)]
  have hsin : ∀ P : ℝ, Real.sin (2 * π * P) = Real.cos (2 * π * (P - 1) - π / 2) := by
    intro P
    rw [Real.cos_sub_pi_div_two, show 2 * π * P = 2 * π * (P - 1) + 2 * π by ring,
      Real.sin_add_two_pi]
  have hpi := Real.pi_pos
  have a1 : π * (5 / 4) ≤ π * P₁ := mul_le_mul_of_nonneg_left hl hpi.le
  have a2 : π * P₂ ≤ π * (7 / 4) := mul_le_mul_of_nonneg_left hu hpi.le
  have a3 : π * P₁ < π * P₂ := mul_lt_mul_of_pos_left h12 hpi
  have hlt : Real.cos (2 * π * (P₂ - 1) - π / 2) < Real.cos (2 * π * (P₁ - 1) - π / 2) := by
    apply Real.strictAntiOn_cos
    · rw [Set.mem_Icc]; constructor <;> linarith
    · rw [Set.mem_Icc]; constructor <;> linarith
    · linarith
  intro heq
  have hlog : 0 < Real.log 2 ^ 2 := by
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
    positivity
  rw [hsin, hsin] at heq
  have h2pi : 0 < 2 * π := by positivity
  rw [div_left_inj' h2pi.ne'] at heq
  have := mul_left_cancel₀ hlog.ne' heq
  linarith

/-- The goal left at the `sorry` of `leaf_remainder_bound481`, after its committed constants
`c = ε₀ = B = 1`, `Cε = 1`, `X₀ = 1`, quantified over the `H` and `T` above the given `H₀` and
`T₀`, is false. Witness: `X = n = 2`, the trivial family `K = 0` with the pole of conductor one,
`Sg = 𝔖(n)`, and the two endpoints of the admissible range of `P`. -/
theorem leaf_remainder_bound481_skeleton_false (H₀ T₀ : ℝ) :
    ¬ (∀ H T : ℝ, H₀ ≤ H → T₀ ≤ T →
        ∀ X : ℕ, 1 ≤ X →
          ∀ P : ℝ, AdmissibleP131 X P →
          ∀ (K : ℕ) (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
            (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ),
            (z 0).1 = 1 → (z 0).2.2 = 1 →
            (∀ i, i ≠ 0 → z i ∈ zeroBox481 X H T P) →
            (∀ w, ((univ.filter (fun i => i ≠ 0 ∧ z i = w)).card : ℕ) ≤
              analyticOrderNatAt (Lfun481 w.2.1) w.2.2) →
            (∀ n ∈ evenJ131 X, Sg 0 0 n = (Sing n : ℂ)) →
            (∀ i j n, n ∈ evenJ131 X → ‖Sg i j n‖ ≤ Sing n) →
            (∀ ε : ℝ, 0 < ε → ε < 1 → ∀ i j n, n ∈ evenJ131 X →
              (¬ (z i).1 ∣ 1 * n ∨ ¬ (z j).1 ∣ 1 * n) → ‖Sg i j n‖ ≤ ε) →
            ∀ n ∈ evenJ131 X,
              |binaryMajor131 X n P -
                (∑ i, ∑ j, Sg i j n * zeroSign481 i * zeroSign481 j *
                  gammaPair481 (z i).2.2 (z j).2.2 n).re| ≤
                1 * ((X : ℝ) * Real.exp (-1 * H) + X / Real.sqrt T)) := by
  intro h
  set P₁ : ℝ := (2 : ℝ) ^ ((2 : ℝ) / 5) with hP₁
  set P₂ : ℝ := (2 : ℝ) ^ ((41 : ℝ) / 100) with hP₂
  have hadm1 : AdmissibleP131 2 P₁ := by
    refine ⟨by rw [hP₁]; norm_num, ?_⟩
    push_cast
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hadm2 : AdmissibleP131 2 P₂ := by
    refine ⟨?_, by rw [hP₂]; norm_num⟩
    push_cast
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
  have hn : (2 : ℕ) ∈ evenJ131 2 := by
    unfold evenJ131
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by norm_num, le_refl 2⟩, by decide, by norm_num⟩
  let z : Fin (0 + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ :=
    fun _ => ⟨1, ((1 : DirichletCharacter ℂ 1), (1 : ℂ))⟩
  let Sg : Fin (0 + 1) → Fin (0 + 1) → ℕ → ℂ := fun _ _ n => (Sing n : ℂ)
  have hbox : ∀ (H T P : ℝ) (i : Fin (0 + 1)), i ≠ 0 → z i ∈ zeroBox481 2 H T P := by
    intro H T P i hi
    exact absurd (Fin.ext (by have := i.isLt; simp only [Fin.val_zero]; omega)) hi
  have hmult : ∀ w, ((univ.filter (fun i : Fin (0 + 1) => i ≠ 0 ∧ z i = w)).card : ℕ) ≤
      analyticOrderNatAt (Lfun481 w.2.1) w.2.2 := by
    intro w
    have hcard : (univ.filter (fun i : Fin (0 + 1) => i ≠ 0 ∧ z i = w)).card = 0 := by
      rw [Finset.card_eq_zero]
      refine Finset.eq_empty_iff_forall_notMem.2 ?_
      intro i hi
      simp only [mem_filter, mem_univ, true_and] at hi
      exact hi.1 (Fin.ext (by have := i.isLt; simp only [Fin.val_zero]; omega))
    rw [hcard]
    exact Nat.zero_le _
  have hSgb : ∀ i j n, n ∈ evenJ131 2 → ‖Sg i j n‖ ≤ Sing n := by
    intro i j n _
    simp only [Sg, Complex.norm_real, Real.norm_eq_abs]
    exact le_of_eq (abs_of_nonneg (Sing_nonneg131 n))
  have hSge : ∀ ε : ℝ, 0 < ε → ε < 1 → ∀ i j n, n ∈ evenJ131 2 →
      (¬ (z i).1 ∣ 1 * n ∨ ¬ (z j).1 ∣ 1 * n) → ‖Sg i j n‖ ≤ ε := by
    intro ε _ _ i j n _ hd
    rcases hd with hd | hd <;> exact absurd (one_dvd _) hd
  have key : ∀ a b c e : ℝ, |a - c| ≤ e → |b - c| ≤ e → |a - b| ≤ 2 * e := by
    intro a b c e h1 h2
    have := abs_sub_le a c b
    rw [abs_sub_comm c b] at this
    linarith
  have hbound : ∀ H T : ℝ, H₀ ≤ H → T₀ ≤ T →
      |binaryMajor131 2 2 P₁ - binaryMajor131 2 2 P₂| ≤
        2 * (2 * Real.exp (-1 * H) + 2 / Real.sqrt T) := by
    intro H T hH hT
    have e1 := h H T hH hT 2 (by norm_num) P₁ hadm1 0 z Sg rfl rfl (hbox H T P₁) hmult
      (fun n _ => rfl) hSgb hSge 2 hn
    have e2 := h H T hH hT 2 (by norm_num) P₂ hadm2 0 z Sg rfl rfl (hbox H T P₂) hmult
      (fun n _ => rfl) hSgb hSge 2 hn
    have e3 := key _ _ _ _ e1 e2
    simp only [Nat.cast_ofNat, one_mul] at e3
    exact e3
  have hne := binaryMajor131_two_two_ne
  set δ : ℝ := |binaryMajor131 2 2 P₁ - binaryMajor131 2 2 P₂| with hδ
  have hδpos : 0 < δ := abs_pos.2 (sub_ne_zero.2 hne)
  -- choose `H` with `exp (-H) ≤ δ / 8` and `T` with `2 / sqrt T < δ / 4`
  set H : ℝ := max H₀ (Real.log (8 / δ)) with hHdef
  set T : ℝ := max T₀ ((8 / δ + 1) ^ 2) with hTdef
  have hb := hbound H T (le_max_left _ _) (le_max_left _ _)
  have hδne := hδpos.ne'
  have hexp : Real.exp (-1 * H) ≤ δ / 8 := by
    have hH : Real.log (8 / δ) ≤ H := le_max_right _ _
    have : Real.exp (-1 * H) ≤ Real.exp (-Real.log (8 / δ)) :=
      Real.exp_le_exp.2 (by linarith)
    refine le_trans this (le_of_eq ?_)
    rw [Real.exp_neg, Real.exp_log (by positivity), inv_div]
  have hsqrt : 2 / Real.sqrt T < δ / 4 := by
    have hT : (8 / δ + 1) ^ 2 ≤ T := le_max_right _ _
    have hs : 8 / δ + 1 ≤ Real.sqrt T :=
      calc 8 / δ + 1 = Real.sqrt ((8 / δ + 1) ^ 2) := (Real.sqrt_sq (by positivity)).symm
        _ ≤ Real.sqrt T := Real.sqrt_le_sqrt hT
    have hs0 : 0 < Real.sqrt T := lt_of_lt_of_le (by positivity) hs
    rw [div_lt_iff₀ hs0]
    have : δ / 4 * (8 / δ + 1) ≤ δ / 4 * Real.sqrt T :=
      mul_le_mul_of_nonneg_left hs (by positivity)
    have h2 : δ / 4 * (8 / δ + 1) = 2 + δ / 4 := by field_simp; ring
    linarith
  linarith

end

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.majorArcs131_two_eq
#print axioms LeanLab.LPZ2007.binaryMajor131_two_two
#print axioms LeanLab.LPZ2007.binaryMajor131_two_two_ne
#print axioms LeanLab.LPZ2007.leaf_remainder_bound481_skeleton_false
#print axioms LeanLab.LPZ2007.primeSum131_two
#print axioms LeanLab.LPZ2007.integrand_two_two
#print axioms LeanLab.LPZ2007.exp_four_pi_I_one_add
#print axioms LeanLab.LPZ2007.exp_four_pi_I_one_sub
#print axioms LeanLab.LPZ2007.re_aux_two_two
#print axioms LeanLab.LPZ2007.two_rpow_two_fifths_pow_five
#print axioms LeanLab.LPZ2007.two_rpow_half_sq
#print axioms LeanLab.LPZ2007.five_fourths_le_two_rpow
#print axioms LeanLab.LPZ2007.two_rpow_le_seven_fourths
