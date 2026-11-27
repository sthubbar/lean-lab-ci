/-
P0069 Baker Harman Pintz 1997, page 43 display 5.2 and page 52, "We have proved (5.1) and
(5.2) for b0(m)", read with the decomposition 5.15 on pages 50 and 51.
Burst burst-20261124 session S1, route unit LowerShortC165.lower_exceptional_mean_square,
frontier leaf DQLeaf518Split.leaf_518_M1.

The paper proves 5.2 for b0 term by term: b0 is rho minus the discarded E2 and E4 parts of
5.15, that is the sum of the kept Buchstab terms, and each kept term satisfies 5.2 by
Lemmas 30 to 35. The lab has no definitions of the kept terms yet, so a faithful per term
LEAF split of leaf_518_M1 cannot be stated today. Splitting instead into rho, the E2 part and
the E4 part would be unfaithful: 5.2 for rho alone is not proved in the paper. This file
proves the linear glue such a split needs, in exactly the form of leaf_518_M1 with a general
coefficient family: display 5.2 for the principal character is closed under sums and
negation of coefficient families. No LEAF, no sorry, no new definition.

AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DQLeaf518Split

namespace LeanLab.BHP1997.Lower52Add1124
open Classical Complex DecompC165b LowerShortC165 DQLeaf518Split
open MeasureTheory

/-- Page 43, display 5.2: the integrand `|G(1/2+it)|^2 / (T2^2 + t^2)` is continuous in `t`
when `T2 > 0`. -/
theorem integrand52_continuous (J : Finset ℕ) (c : ℕ → ℂ) {T : ℝ} (hT : 0 < T) :
    Continuous (fun t : ℝ => ‖∑ m ∈ J, c m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
      (T ^ 2 + t ^ 2)) :=
  ((dirichlet_poly_continuous J c).norm.pow 2).div (by fun_prop) fun t => by positivity

/-- Page 43, display 5.2 for a sum of two coefficient families on one range of `t`:
`|G1 + G2|^2 <= 2 |G1|^2 + 2 |G2|^2` pointwise, integrated against the kernel. -/
theorem integral52_add (J : Finset ℕ) (c1 c2 : ℕ → ℂ) {T : ℝ} (hT : 0 < T) {a d : ℝ}
    (had : a ≤ d) :
    (∫ t in a..d, ‖∑ m ∈ J, (c1 m + c2 m) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
      (T ^ 2 + t ^ 2)) ≤
      2 * (∫ t in a..d, ‖∑ m ∈ J, c1 m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        (T ^ 2 + t ^ 2)) +
      2 * (∫ t in a..d, ‖∑ m ∈ J, c2 m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
        (T ^ 2 + t ^ 2)) := by
  have i12 := (integrand52_continuous J (fun m => c1 m + c2 m) hT).intervalIntegrable
    (μ := volume) a d
  have i1 := (integrand52_continuous J c1 hT).intervalIntegrable (μ := volume) a d
  have i2 := (integrand52_continuous J c2 hT).intervalIntegrable (μ := volume) a d
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul,
    ← intervalIntegral.integral_add (i1.const_mul 2) (i2.const_mul 2)]
  refine intervalIntegral.integral_mono_on had i12 ((i1.const_mul 2).add (i2.const_mul 2))
    fun t _ => ?_
  have hD : 0 < T ^ 2 + t ^ 2 := by positivity
  set u := ∑ m ∈ J, c1 m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)
  set v := ∑ m ∈ J, c2 m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)
  have hsum : ∑ m ∈ J, (c1 m + c2 m) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) = u + v := by
    simp only [u, v, ← Finset.sum_add_distrib, add_div]
  rw [hsum]
  have h := norm_add_le u v
  have hsq : ‖u + v‖ ^ 2 ≤ 2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2 := by
    nlinarith [norm_nonneg u, norm_nonneg v, norm_nonneg (u + v), sq_nonneg (‖u‖ - ‖v‖)]
  calc ‖u + v‖ ^ 2 / (T ^ 2 + t ^ 2) ≤ (2 * ‖u‖ ^ 2 + 2 * ‖v‖ ^ 2) / (T ^ 2 + t ^ 2) :=
        div_le_div_of_nonneg_right hsq hD.le
    _ = 2 * (‖u‖ ^ 2 / (T ^ 2 + t ^ 2)) + 2 * (‖v‖ ^ 2 / (T ^ 2 + t ^ 2)) := by ring

/-- Pages 43 and 52, display 5.2 for the principal character in the form of
`DQLeaf518Split.leaf_518_M1`, for a sum of two coefficient families: if 5.2 holds for `b1` and
for `b2` then it holds for `b1 + b2`. This is how page 52 passes 5.2 from the kept terms of
5.15 to b0. PROVED. -/
theorem lower52_add {ε : ℝ} (b1 b2 : ℝ → ℕ → ℝ)
    (h1 : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (b1 x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (b1 x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A))
    (h2 : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (b2 x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (b2 x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (((b1 x m + b2 x m : ℝ) : ℂ) : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (((b1 x m + b2 x m : ℝ) : ℂ) : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C1, hC1⟩ := h1 A hA
  obtain ⟨C2, hC2⟩ := h2 A hA
  refine ⟨max (max C1 C2) (max 1 (2 * |C1| + 2 * |C2|)), fun x hx q hq hqs => ?_⟩
  have hx1 : C1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx2 : C2 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hxo : 1 ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx
  have hCc : 2 * |C1| + 2 * |C2| ≤ max (max C1 C2) (max 1 (2 * |C1| + 2 * |C2|)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  have hY : 0 < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos (by linarith) _
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hs : (0 : ℝ) < sieveQ ε x := by exact_mod_cast lt_of_lt_of_le hq hqs
  have hT : 0 < x ^ (11 / 20 + ε) / (q * sieveQ ε x) := div_pos hY (by positivity)
  set T := x ^ (11 / 20 + ε) / (q * sieveQ ε x) with hTdef
  set K := x ^ (11 / 20 + ε) / T ^ 2 * Real.log x ^ (-A) with hK
  have hK0 : 0 ≤ K := by
    have := Real.rpow_nonneg (Real.log_nonneg hxo) (-A)
    positivity
  have e1 := hC1 x hx1 q hq hqs
  have e2 := hC2 x hx2 q hq hqs
  set χ := (1 : DirichletCharacter ℂ q)
  have e : ∀ t : ℝ, (∑ m ∈ rightInterval ε x, ((b1 x m + b2 x m : ℝ) : ℂ) * χ (m : ZMod q) /
      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)) =
      ∑ m ∈ rightInterval ε x, ((b1 x m : ℂ) * χ (m : ZMod q) + (b2 x m : ℂ) * χ (m : ZMod q)) /
      (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I) := fun t =>
    Finset.sum_congr rfl fun m _ => by push_cast; ring
  simp_rw [e]
  have hRHS : 2 * C1 * K + 2 * C2 * K ≤ max (max C1 C2) (max 1 (2 * |C1| + 2 * |C2|)) * K := by
    have h3 : 2 * C1 + 2 * C2 ≤ max (max C1 C2) (max 1 (2 * |C1| + 2 * |C2|)) := by
      have := le_abs_self C1; have := le_abs_self C2; linarith
    nlinarith [mul_le_mul_of_nonneg_right h3 hK0]
  have hmulK : ∀ C : ℝ, C * (x ^ (11 / 20 + ε) / T ^ 2) * Real.log x ^ (-A) = C * K := by
    intro C; rw [hK]; ring
  rw [hmulK] at e1 e2 ⊢
  by_cases hTY : Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ x ^ (11 / 20 + ε)
  · have ia := integral52_add (rightInterval ε x) (fun m => (b1 x m : ℂ) * χ (m : ZMod q))
      (fun m => (b2 x m : ℂ) * χ (m : ZMod q)) hT (a := -x ^ (11 / 20 + ε))
      (d := -Real.exp (Real.log x ^ (1 / 3 : ℝ))) (by linarith)
    have ib := integral52_add (rightInterval ε x) (fun m => (b1 x m : ℂ) * χ (m : ZMod q))
      (fun m => (b2 x m : ℂ) * χ (m : ZMod q)) hT hTY
    try simp only at ia ib
    linarith
  · push_neg at hTY
    have hneg : ∀ (c : ℕ → ℂ) (a d : ℝ), d ≤ a →
        (∫ t in a..d, ‖∑ m ∈ rightInterval ε x, c m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
          (T ^ 2 + t ^ 2)) ≤ 0 := by
      intro c a d hda
      rw [intervalIntegral.integral_symm]
      have : 0 ≤ ∫ t in d..a, ‖∑ m ∈ rightInterval ε x,
          c m / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 / (T ^ 2 + t ^ 2) :=
        intervalIntegral.integral_nonneg hda fun t _ => by positivity
      linarith
    have ha := hneg (fun m => (b1 x m : ℂ) * χ (m : ZMod q) + (b2 x m : ℂ) * χ (m : ZMod q))
      (-x ^ (11 / 20 + ε)) (-Real.exp (Real.log x ^ (1 / 3 : ℝ))) (by linarith)
    have hb := hneg (fun m => (b1 x m : ℂ) * χ (m : ZMod q) + (b2 x m : ℂ) * χ (m : ZMod q))
      (Real.exp (Real.log x ^ (1 / 3 : ℝ))) (x ^ (11 / 20 + ε)) hTY.le
    try simp only at ha hb
    have : 0 ≤ max (max C1 C2) (max 1 (2 * |C1| + 2 * |C2|)) * K :=
      mul_nonneg (le_trans zero_le_one (le_trans (le_max_left _ _) (le_max_right _ _))) hK0
    linarith

/-- Pages 43 and 52, display 5.2 for the principal character in the form of
`DQLeaf518Split.leaf_518_M1` is unchanged when the coefficients change sign. With
`lower52_add` this moves 5.2 through the signed Buchstab sums of 5.15. PROVED. -/
theorem lower52_neg {ε : ℝ} (b : ℝ → ℕ → ℝ)
    (h : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (((-b x m : ℝ) : ℂ) : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (((-b x m : ℝ) : ℂ) : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C, hC⟩ := h A hA
  refine ⟨C, fun x hx q hq hqs => ?_⟩
  have e : ∀ t : ℝ, ‖∑ m ∈ rightInterval ε x, ((-b x m : ℝ) : ℂ) *
      (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ =
      ‖∑ m ∈ rightInterval ε x, (b x m : ℂ) *
      (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ := by
    intro t
    rw [← norm_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun m _ => ?_
    push_cast
    ring
  simp_rw [e]
  exact hC x hx q hq hqs

end LeanLab.BHP1997.Lower52Add1124
