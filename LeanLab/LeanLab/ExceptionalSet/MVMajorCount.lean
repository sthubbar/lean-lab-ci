import LeanLab.ExceptionalSet.MVMajorExplicit

/-!
# Estermann's major arc count off the exceptional set, explicit form

Lab proof, unit U-6250, CLOUD 20261020T0917Z-cloud39. AI wrote the Lean code. Known
mathematics, Estermann 1938, Vaughan's book Chapter 3. Binary Goldbach is OPEN.

* `errMV x Q E`: the error of `majorPart_explicit`.
* `majorPart_gt`: if that error is at most `M x/16`, `M = Mx x`, `x ≥ 7` and
  `e⁸ G(n)/√⌊Q⌋ ≤ 1/4`, then every even `n` in `(x/2, x]` has major arc part of modulus above
  `M x/4`; the proof uses only `𝔖_Q(n) ≥ 3/4`, not the full `2C₂`.
* `card_major_small_le`: then at most `e⁸ x / T` even `n` in `(x/2, x]` have major arc part at
  most `M x/4`, whenever `e⁸ T/√⌊Q⌋ ≤ 1/4`.
-/

namespace LeanLab.ExceptionalSet.MVMajor

open Complex Finset Real ZMod
open scoped ArithmeticFunction.Moebius
open LeanLab.PNTPort.Vinogradov LeanLab.PNTPort.LargeSieve LeanLab.ExceptionalSet.MV

attribute [local instance] Classical.propDecidable

/-- The error term of `majorPart_explicit`. -/
noncomputable def errMV (x : ℕ) (Q E : ℝ) : ℝ :=
  Q ^ 2 * ((2 * Q + 1) * (((Chebyshev.psi x - Chebyshev.theta x) +
      E * (1 + 2 * π * x * Q / (Mx x))) * (x * Real.log x + x))) +
    (∑ q ∈ Icc 1 ⌊Q⌋₊, 1 / (q.totient : ℝ)) *
      (2 * (Mx x) / (Q / (Mx x)) + 1 / (2 * (Q / (Mx x)) ^ 2))

/-- **The major arc part is large off the exceptional set.** -/
theorem majorPart_gt {x n : ℕ} {Q : ℝ} (hQ : 1 ≤ Q) (hQM : 2 * Q ^ 3 < Mx x) (hx : 7 ≤ x)
    (hn2 : x / 2 + 1 ≤ n) (hnx : n ≤ x) (heven : Even n) {E : ℝ}
    (hmaj : ∀ q ∈ Icc 1 ⌊Q⌋₊, ∀ a' : ℤ, IsCoprime a' (q : ℤ) → ∀ β : ℝ,
      ‖S x (a' / q + β) - (μ q : ℂ) / q.totient * V x β‖ ≤ E * (1 + 2 * π * |β| * x))
    (hErr : errMV x Q E ≤ (Mx x : ℝ) * x / 16) (hP2 : 2 ≤ ⌊Q⌋₊)
    (hsing : Real.exp 8 * G n / Real.sqrt ⌊Q⌋₊ ≤ 1 / 4) :
    (Mx x : ℝ) * x / 4 < ‖majorPart (logPrimes x) (minorArcs x Q) (n : ZMod (Mx x))‖ := by
  have hnM : n < Mx x := by unfold Mx; omega
  have hexp := majorPart_explicit hQ hQM hnM hmaj
  have hJ := J2_eq (N := x) (n := n) (by omega) (by omega)
  have hs := sing2_ge heven (by omega) hP2
  set s := ∑ q ∈ Icc 1 ⌊Q⌋₊, f2 n q with hsdef
  have hs34 : 3 / 4 ≤ s := by linarith
  have hM : (0 : ℝ) < Mx x := by unfold Mx; positivity
  have hn1 : ((x : ℝ) - 1) / 2 ≤ (n : ℝ) - 1 := by
    have h1 : (x : ℝ) ≤ 2 * (n : ℝ) - 1 := by
      have : x ≤ 2 * n - 1 := by omega
      have h2 : ((2 * n - 1 : ℕ) : ℝ) = 2 * (n : ℝ) - 1 := by
        rw [Nat.cast_sub (by omega)]; push_cast; ring
      rw [← h2]; exact_mod_cast this
    linarith
  have hmain : ‖(Mx x : ℂ) * (J2 x n : ℂ) * ((s : ℝ) : ℂ)‖ = (Mx x : ℝ) * ((n : ℝ) - 1) * s := by
    rw [hJ]
    have h0 : (0 : ℝ) ≤ (n : ℝ) - 1 := by
      have : (1 : ℝ) ≤ n := by exact_mod_cast (show 1 ≤ n by omega)
      linarith
    have : (Mx x : ℂ) * ((((n : ℝ) - 1 : ℝ)) : ℂ) * ((s : ℝ) : ℂ) =
        (((Mx x : ℝ) * ((n : ℝ) - 1) * s : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.norm_real, Real.norm_of_nonneg (by positivity)]
  have htri := norm_sub_norm_le ((Mx x : ℂ) * (J2 x n : ℂ) * ((s : ℝ) : ℂ))
    (majorPart (logPrimes x) (minorArcs x Q) (n : ZMod (Mx x)))
  rw [norm_sub_rev, hmain] at htri
  have hE := hexp.trans hErr
  have hlow : (Mx x : ℝ) * (((x : ℝ) - 1) / 2) * (3 / 4) ≤ (Mx x : ℝ) * ((n : ℝ) - 1) * s := by
    have h0 : (0 : ℝ) ≤ ((x : ℝ) - 1) / 2 := by
      have : (7 : ℝ) ≤ x := by exact_mod_cast hx
      linarith
    apply mul_le_mul (mul_le_mul_of_nonneg_left hn1 hM.le) hs34 (by norm_num)
    exact mul_nonneg hM.le (le_trans h0 hn1)
  have hx7 : (7 : ℝ) ≤ x := by exact_mod_cast hx
  have : (Mx x : ℝ) * x / 4 + (Mx x : ℝ) * x / 16 < (Mx x : ℝ) * (((x : ℝ) - 1) / 2) * (3 / 4) := by
    nlinarith
  linarith

/-- **The major arc count, explicit form.** -/
theorem card_major_small_le {x : ℕ} {Q : ℝ} (hQ : 1 ≤ Q) (hQM : 2 * Q ^ 3 < Mx x) (hx : 7 ≤ x)
    {E : ℝ}
    (hmaj : ∀ q ∈ Icc 1 ⌊Q⌋₊, ∀ a' : ℤ, IsCoprime a' (q : ℤ) → ∀ β : ℝ,
      ‖S x (a' / q + β) - (μ q : ℂ) / q.totient * V x β‖ ≤ E * (1 + 2 * π * |β| * x))
    (hErr : errMV x Q E ≤ (Mx x : ℝ) * x / 16) (hP2 : 2 ≤ ⌊Q⌋₊) {T : ℝ} (hT : 0 < T)
    (hsing : Real.exp 8 * T / Real.sqrt ⌊Q⌋₊ ≤ 1 / 4) :
    ((((Finset.Icc (x / 2 + 1) x).filter (fun n : ℕ => Even n ∧
        ‖majorPart (logPrimes x) (minorArcs x Q) (n : ZMod (Mx x))‖
          ≤ (Mx x : ℝ) * x / 4)).card : ℕ) : ℝ) ≤ Real.exp 8 * x / T := by
  refine le_trans ?_ (card_G_gt x hT)
  exact_mod_cast card_le_card (fun n hn => by
    rw [mem_filter, mem_Icc] at hn ⊢
    refine ⟨⟨by omega, hn.1.2⟩, ?_⟩
    by_contra hG
    push_neg at hG
    have hsq : 0 < Real.sqrt ⌊Q⌋₊ := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < ⌊Q⌋₊))
    have h1 : Real.exp 8 * G n / Real.sqrt ⌊Q⌋₊ ≤ 1 / 4 := by
      refine le_trans ?_ hsing
      apply div_le_div_of_nonneg_right _ hsq.le
      exact mul_le_mul_of_nonneg_left hG (Real.exp_pos 8).le
    have := majorPart_gt hQ hQM hx hn.1.1 hn.1.2 hn.2.1 hmaj hErr hP2 h1
    have h2 := hn.2.2
    push_cast at h2
    linarith)

end LeanLab.ExceptionalSet.MVMajor
