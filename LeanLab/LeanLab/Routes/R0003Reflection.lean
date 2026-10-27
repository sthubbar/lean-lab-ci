/-
R-0003, T3 MOONSHOT, run 20261019T0202Z-9877, unit U-1015: pseudorandomness alone cannot give a
single binary representation, the reflection obstruction.

The route tested: transference, Green-Tao style, models the primes by a dense pseudorandom set and
counts patterns through Gowers or Fourier uniformity. For the binary count at one `n` this fails
exactly: for any `0/1` function `f` on `ZMod M` and any `n`, the reflected complement
`g x = 1 - f (n - x)` has `Σ_j f j * g (n - j) = 0`, `reflection_conv_zero`, while `g` has the
complementary mean and the same Fourier magnitudes as `f` at every nonzero frequency,
`dft_reflect_norm`. So any hypothesis on `f` and `g` made only of densities and Fourier sizes is
met by a pair with no representation of `n`; for the primes the obstruction is ruled out only by
binary Goldbach itself.

KNOWN mathematics, folklore. AI-written Lean code, Claude. Checked only by the Lean kernel.
Binary Goldbach is OPEN, and nothing here is progress on it.
-/
import LeanLab.Routes.R0001Parseval

open ZMod Finset

namespace LeanLab.Routes.R0003
open LeanLab.Routes.R0001

variable {M : ℕ} [NeZero M]

/-- The reflected complement of `f` about `n`. -/
def reflect (f : ZMod M → ℂ) (n : ZMod M) (x : ZMod M) : ℂ := 1 - f (n - x)

/-- **No representation**: for `f` with values in `{0, 1}`, `Σ_j f j * reflect f n (n - j) = 0`. -/
theorem reflection_conv_zero (f : ZMod M → ℂ) (hf : ∀ x, f x = 0 ∨ f x = 1) (n : ZMod M) :
    ∑ j, f j * reflect f n (n - j) = 0 := by
  refine Finset.sum_eq_zero fun j _ => ?_
  unfold reflect
  rw [sub_sub_cancel]
  rcases hf j with h | h <;> rw [h] <;> ring

/-- The means are complementary: `Σ reflect f n = M - Σ f`. -/
theorem sum_reflect (f : ZMod M → ℂ) (n : ZMod M) :
    ∑ x, reflect f n x = (M : ℂ) - ∑ x, f x := by
  unfold reflect
  rw [Finset.sum_sub_distrib]
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one]
  congr 1
  exact Fintype.sum_equiv (Equiv.subLeft n) _ _ (fun x => rfl)

/-- **Same Fourier magnitudes away from 0**: for real `f` and `k ≠ 0`,
`‖𝓕 (reflect f n) k‖ = ‖𝓕 f k‖`. -/
theorem dft_reflect_norm (f : ZMod M → ℂ) (hreal : ∀ x, (starRingEnd ℂ) (f x) = f x)
    (n k : ZMod M) (hk : k ≠ 0) :
    ‖𝓕 (reflect f n) k‖ = ‖𝓕 f k‖ := by
  -- 𝓕 (reflect f n) k = Σ_x e(-xk) - Σ_x e(-xk) f(n - x); the first sum is 0 for k ≠ 0
  have h1 : 𝓕 (reflect f n) k = 𝓕 (fun _ => (1 : ℂ)) k - 𝓕 (fun x => f (n - x)) k := by
    rw [dft_apply, dft_apply, dft_apply, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun x _ => ?_
    unfold reflect
    simp only [smul_eq_mul, mul_sub]
  have h0 : 𝓕 (fun _ => (1 : ℂ)) k = 0 := by
    rw [dft_apply]
    simp only [smul_eq_mul, mul_one]
    have := sum_stdAddChar_mul (N := M) (-k)
    have e : ∀ x : ZMod M, (stdAddChar (x * (-k)) : ℂ) = stdAddChar (-(x * k)) := by
      intro x; ring_nf
    simp only [e] at this
    rw [this, ite_eq_right_iff.mpr (fun h => absurd h (neg_ne_zero.mpr hk))]
  -- the reindexed term is e(-nk) times the conjugate of 𝓕 f k
  have h2 : 𝓕 (fun x => f (n - x)) k = (stdAddChar (-(n * k)) : ℂ) * (starRingEnd ℂ) (𝓕 f k) := by
    rw [dft_apply, dft_apply, map_sum, Finset.mul_sum]
    refine Fintype.sum_equiv (Equiv.subLeft n) _ _ (fun x => ?_)
    simp only [Equiv.subLeft_apply, smul_eq_mul, map_mul, hreal]
    rw [conj_stdAddChar, neg_neg, ← mul_assoc, ← AddChar.map_add_eq_mul]
    congr 2
    ring
  rw [h1, h0, h2, zero_sub, norm_neg, norm_mul, RCLike.norm_conj]
  have hu : ‖(stdAddChar (-(n * k)) : ℂ)‖ = 1 := by
    simp [AddChar.norm_apply]
  rw [hu, one_mul]

#print axioms reflection_conv_zero
#print axioms sum_reflect
#print axioms dft_reflect_norm

end LeanLab.Routes.R0003
