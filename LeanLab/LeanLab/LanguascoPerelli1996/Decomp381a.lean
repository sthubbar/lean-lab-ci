import LeanLab.LanguascoPerelli1996.Statements
import LeanLab.LanguascoPerelli1996.Partial381
import LeanLab.LanguascoPerelli1996.Point381

/-!
P0071 pages 358 and 359, displays 20, 21 and 24.
Keep the truncated endpoint in display 21 rather than treating the
without loss of generality passage to display 22 as an exact inequality.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.LanguascoPerelli1996.Decomp381a
open scoped ContDiff
open Real MeasureTheory intervalIntegral

/-- Page 358 display 21. The remainder polynomial stopped at Y. -/
noncomputable def partialR (X Y η : ℝ) (q a : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc ⌈X / 4⌉₊ ⌊Y⌋₊,
    ((ArithmeticFunction.vonMangoldt n : ℂ) * e ((n : ℝ) * ((a : ℝ) / q)) -
      (muPhi q : ℂ)) * e ((n : ℝ) * η)

/-- Page 358 display 21 at its full endpoint. The stopped polynomial is R. -/
theorem partialR_full (X η : ℝ) (q a : ℕ) : partialR X (2 * X) η q a = R X η q a := by
  unfold partialR R S Tsum
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  have he : e ((n : ℝ) * ((a : ℝ) / q + η)) =
      e ((n : ℝ) * ((a : ℝ) / q)) * e ((n : ℝ) * η) := by
    unfold e
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  rw [he]
  ring

/-- Page 358 display 21, a finite mass witness for its hypothesis.
There are only finitely many integer upper cutoffs below 2X, so a
nonnegative common mass bound exists without GRH or GMCxi. -/
theorem partial_mass_bound_exists (X : ℝ) {ξ : ℝ} (hξ : 0 < ξ) (q a : ℕ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X →
      (∫ t in (-ξ)..ξ, ‖partialR X Y t q a‖ ^ 2) ≤ M := by
  let N := ⌊2 * X⌋₊
  let mass := fun k : ℕ => ∫ t in (-ξ)..ξ, ‖partialR X (k : ℝ) t q a‖ ^ 2
  have hmass (k : ℕ) : 0 ≤ mass k :=
    integral_nonneg_of_forall (by linarith) (fun _ => sq_nonneg _)
  refine ⟨∑ k ∈ Finset.range (N + 1), mass k,
    Finset.sum_nonneg (fun k _ => hmass k), ?_⟩
  intro Y hY hY2
  have hk : ⌊Y⌋₊ ∈ Finset.range (N + 1) := by
    apply Finset.mem_range.mpr
    exact Nat.lt_succ_of_le (Nat.floor_le_floor hY2)
  have heq (t : ℝ) : partialR X Y t q a = partialR X (⌊Y⌋₊ : ℝ) t q a := by
    simp only [partialR, Nat.floor_natCast]
  simp_rw [heq]
  exact Finset.single_le_sum (fun k _ => hmass k) hk

/-- LEAF. Page 358 display 20. Sobolev Gallagher and Cauchy Schwarz
for the actual finite remainder polynomial. The explicit constant two
allows the two terms printed with an implied absolute constant. -/
theorem remainder_point_control {X ξ η : ℝ} (hξ : 0 < ξ) (hη : |η| ≤ ξ)
    (q a : ℕ) :
    ‖R X η q a‖ ^ 2 ≤ 2 *
      ((∫ t in (-ξ)..ξ, ‖R X t q a‖ ^ 2) / ξ +
        Real.sqrt ((∫ t in (-ξ)..ξ, ‖R X t q a‖ ^ 2) *
          (∫ t in (-ξ)..ξ, ‖deriv (fun v : ℝ => R X v q a) t‖ ^ 2))) := by
  have hc : ContDiff ℝ ∞ (fun t : ℝ => R X t q a) := by
    unfold R S Tsum e
    have hcast : ContDiff ℝ ∞ (fun t : ℝ => (t : ℂ)) := Complex.ofRealCLM.contDiff
    fun_prop
  exact Point381.point_control hc hξ hη

/-- LEAF. Page 358 display 21, partial summation in L2.
An upper bound M for every stopped polynomial controls the derivative
mass by an absolute constant times X squared M. This retains the maximum
in display 21 and does not assert display 22 for the fixed polynomial. -/
theorem remainder_derivative_of_partial_mass :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ X : ℝ, 1 ≤ X → ∀ ξ : ℝ, 0 < ξ →
      ∀ q a : ℕ, ∀ M : ℝ, 0 ≤ M →
        (∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X →
          (∫ t in (-ξ)..ξ, ‖partialR X Y t q a‖ ^ 2) ≤ M) →
        (∫ t in (-ξ)..ξ, ‖deriv (fun v : ℝ => R X v q a) t‖ ^ 2) ≤
          A * X ^ 2 * M := by
  refine ⟨64 * Real.pi ^ 2, by positivity, ?_⟩
  intro X hX ξ hξ q a M hM hm
  let m := ⌈X / 4⌉₊
  let N := ⌊2 * X⌋₊
  let c : ℕ → ℂ := fun n => (ArithmeticFunction.vonMangoldt n : ℂ) *
    e ((n : ℝ) * ((a : ℝ) / q)) - (muPhi q : ℂ)
  have hN0 : (0 : ℝ) ≤ 2 * X := by linarith
  have hNle : (N : ℝ) ≤ 2 * X := Nat.floor_le hN0
  have hmN : m ≤ N := by
    apply Nat.ceil_le.mpr
    have hfloor := Nat.lt_floor_add_one (2 * X)
    dsimp [N]
    linarith
  have hm0 : X / 4 ≤ (m : ℝ) := Nat.le_ceil _
  have hprefix : ∀ k, m ≤ k → k ≤ N →
      (∫ t in (-ξ)..ξ, ‖∑ n ∈ Finset.Icc m k, c n * e ((n : ℝ) * t)‖ ^ 2) ≤ M := by
    intro k hmk hkN
    have hkr : (k : ℝ) ≤ 2 * X := (Nat.cast_le.mpr hkN).trans hNle
    have hkl : X / 4 ≤ (k : ℝ) := hm0.trans (Nat.cast_le.mpr hmk)
    have hh := hm (k : ℝ) hkl hkr
    simpa only [partialR, Nat.floor_natCast, m, c] using hh
  have hh := Partial381.polynomial_derivative_mass hmN c (show -ξ ≤ ξ by linarith) hM hprefix
  have heq : (fun v : ℝ => R X v q a) =
      (fun v : ℝ => ∑ n ∈ Finset.Icc m N, c n * e ((n : ℝ) * v)) := by
    funext v
    exact (partialR_full X v q a).symm
  rw [heq]
  calc
    _ ≤ 16 * Real.pi ^ 2 * (N : ℝ) ^ 2 * M := hh
    _ ≤ 64 * Real.pi ^ 2 * X ^ 2 * M := by
      have hs := pow_le_pow_left₀ (Nat.cast_nonneg N) hNle 2
      nlinarith [mul_le_mul_of_nonneg_right hs (show 0 ≤ 16 * Real.pi ^ 2 * M by positivity)]

/-- LEAF. Pages 358 and 359, the uniform endpoint treatment after
21 and the proof of 24 via 23 and displays 15 through 19.
GMCxi bounds the mean square for every stopped polynomial in 21.
This is the uniform endpoint assertion needed by the paper's reduction
before 22, not a claim that the maximum occurs literally at Y equal to 2X. -/
theorem partial_remainder_mean_square :
    ∀ θ : ℝ, 0 < θ → θ ≤ 1 / 2 → ∀ ξ : ℝ → ℕ → ℝ, GMCxi θ ξ →
      ∀ ε : ℝ, 0 < ε → ∃ B X0 : ℝ, 0 ≤ B ∧ ∀ X : ℝ, X0 ≤ X → 1 ≤ X →
        ∀ (q : ℕ) [NeZero q], (q : ℝ) ≤ X ^ θ → ∀ a : ℕ, Nat.Coprime a q →
          ∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X →
            (∫ t in (-(ξ X q))..(ξ X q), ‖partialR X Y t q a‖ ^ 2) ≤
              B * ξ X q * X ^ (1 + ε) := by
  sorry

/-- Pages 358 and 359, Theorem 4 assembled with the actual integrals.
Exactly the existing Theorem4. CONDITIONAL ON partial_remainder_mean_square alone. -/
theorem theorem4_decomposed : Theorem4 := by
  intro θ hθ hθ2 ξ hG ε hε
  obtain ⟨A, hA, hderiv⟩ := remainder_derivative_of_partial_mass
  obtain ⟨B, X0, hB, hmass⟩ := partial_remainder_mean_square θ hθ hθ2 ξ hG
    (2 * ε) (by positivity)
  let C := 2 * B * (1 + Real.sqrt A)
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨Real.sqrt (2 * C), max X0 1, ?_⟩
  intro X hX q inst hq a ha η hη
  have hX1 : 1 ≤ X := (le_max_right _ _).trans hX
  have hX0 : 0 < X := by linarith
  have hx : 0 < ξ X q := (hG.2.1 X q).1
  let M := B * ξ X q * X ^ (1 + 2 * ε)
  let J := ∫ t in (-(ξ X q))..(ξ X q), ‖R X t q a‖ ^ 2
  let D := ∫ t in (-(ξ X q))..(ξ X q), ‖deriv (fun v : ℝ => R X v q a) t‖ ^ 2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hpartials : ∀ Y : ℝ, X / 4 ≤ Y → Y ≤ 2 * X →
      (∫ t in (-(ξ X q))..(ξ X q), ‖partialR X Y t q a‖ ^ 2) ≤ M :=
    hmass X ((le_max_left _ _).trans hX) hX1 q hq a ha
  have hJ : J ≤ M := by
    have hb := hpartials (2 * X) (by linarith) le_rfl
    simpa only [partialR_full] using hb
  have hJ0 : 0 ≤ J := integral_nonneg_of_forall (by linarith) (fun _ => sq_nonneg _)
  have hD : D ≤ A * X ^ 2 * M := hderiv X hX1 (ξ X q) hx q a M hM hpartials
  have hpoint : ‖R X η q a‖ ^ 2 ≤ 2 * (J / ξ X q + Real.sqrt (J * D)) :=
    remainder_point_control hx hη q a
  have hsqrt : Real.sqrt (J * D) ≤ Real.sqrt A * X * M := by
    apply (Real.sqrt_le_left (by positivity)).2
    have hprod : J * D ≤ A * X ^ 2 * M ^ 2 := by
      calc
        J * D ≤ J * (A * X ^ 2 * M) := mul_le_mul_of_nonneg_left hD hJ0
        _ ≤ M * (A * X ^ 2 * M) := mul_le_mul_of_nonneg_right hJ (by positivity)
        _ = _ := by ring
    calc
      J * D ≤ A * X ^ 2 * M ^ 2 := hprod
      _ = (Real.sqrt A * X * M) ^ 2 := by simp only [mul_pow, Real.sq_sqrt hA]
  have hjdiv : J / ξ X q ≤ B * X ^ (1 + 2 * ε) := by
    apply (div_le_iff₀ hx).2
    simpa only [M, mul_assoc, mul_comm, mul_left_comm] using hJ
  have hsquare : ‖R X η q a‖ ^ 2 ≤ C * X ^ (1 + 2 * ε) * (1 + ξ X q * X) := by
    have hraw : ‖R X η q a‖ ^ 2 ≤
        2 * (B * X ^ (1 + 2 * ε) + Real.sqrt A * X * M) := by linarith
    calc
      _ ≤ 2 * (B * X ^ (1 + 2 * ε) + Real.sqrt A * X * M) := hraw
      _ ≤ C * X ^ (1 + 2 * ε) * (1 + ξ X q * X) := by
        dsimp [C, M]
        nlinarith [mul_nonneg (Real.sqrt_nonneg A) (mul_nonneg hB
          (Real.rpow_nonneg hX0.le (1 + 2 * ε))),
          mul_nonneg (mul_nonneg hB (Real.rpow_nonneg hX0.le (1 + 2 * ε)))
            (mul_nonneg hx.le hX0.le)]
  have hfinal : ‖R X η q a‖ ≤ Real.sqrt (2 * C) * X ^ ((1 + 2 * ε) / 2) *
      (1 + (ξ X q * X) ^ (1 / 2 : ℝ)) := by
    let u := (ξ X q * X) ^ (1 / 2 : ℝ)
    let w := X ^ ((1 + 2 * ε) / 2)
    have hu : u ^ 2 = ξ X q * X := by
      dsimp [u]
      rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      norm_num
    have hw : w ^ 2 = X ^ (1 + 2 * ε) := by
      dsimp [w]
      rw [← Real.rpow_natCast, ← Real.rpow_mul hX0.le]
      congr 1
      norm_num
    have hBsq := Real.sq_sqrt (show 0 ≤ 2 * C by positivity)
    have hbound : ‖R X η q a‖ ^ 2 ≤ (Real.sqrt (2 * C) * w * (1 + u)) ^ 2 := by
      have hu0 : 0 ≤ u := by dsimp [u]; positivity
      have hw0 : 0 ≤ w := by dsimp [w]; positivity
      rw [mul_pow, mul_pow, hBsq, hw]
      nlinarith [mul_nonneg hC (Real.rpow_nonneg hX0.le (1 + 2 * ε)),
        mul_nonneg (mul_nonneg hC (Real.rpow_nonneg hX0.le (1 + 2 * ε))) hu0]
    have hout0 : 0 ≤ Real.sqrt (2 * C) * w * (1 + u) := by dsimp [w, u]; positivity
    nlinarith [norm_nonneg (R X η q a)]
  simpa only [show (1 + 2 * ε) / 2 = 1 / 2 + ε by ring, mul_comm (ξ X q) X] using hfinal

end LeanLab.LanguascoPerelli1996.Decomp381a

#print axioms LeanLab.LanguascoPerelli1996.Decomp381a.partialR_full
#print axioms LeanLab.LanguascoPerelli1996.Decomp381a.remainder_point_control
#print axioms LeanLab.LanguascoPerelli1996.Decomp381a.remainder_derivative_of_partial_mass
#print axioms LeanLab.LanguascoPerelli1996.Decomp381a.partial_remainder_mean_square
#print axioms LeanLab.LanguascoPerelli1996.Decomp381a.theorem4_decomposed

#print axioms LeanLab.LanguascoPerelli1996.Decomp381a.partial_mass_bound_exists
