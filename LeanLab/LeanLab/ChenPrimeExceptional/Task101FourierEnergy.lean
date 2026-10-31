/-
AI wrote this Lean code for CODEX task101.
P0039 Lemma 4.2, page 19. Finite cyclic Fourier energy and large values.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task101CharacterTwist

open Finset ComplexConjugate

namespace LeanLab.ChenPrimeExceptional.Task101

noncomputable section

/-- The unnormalized cyclic convolution. -/
def cyclicConv {r : ℕ} [NeZero r] (f g : ZMod r → ℂ) (m : ZMod r) : ℂ :=
  ∑ n : ZMod r, f n * g (m - n)

/-- The energy is the sum of squared absolute values. -/
def energy {ι : Type*} [Fintype ι] (f : ι → ℂ) : ℝ :=
  ∑ n, ‖f n‖ ^ 2

/-- The discrete Fourier transform scales the complex inner product by the modulus. -/
theorem dft_pairing {r : ℕ} [NeZero r] (f g : ZMod r → ℂ) :
    ∑ k : ZMod r, ZMod.dft f k * conj (ZMod.dft g k) =
      (r : ℂ) * ∑ n : ZMod r, f n * conj (g n) := by
  calc
    _ = ∑ k : ZMod r, (∑ n : ZMod r,
        ZMod.stdAddChar (-(n * k)) * f n) * conj (ZMod.dft g k) := by
      congr 1
    _ = ∑ n : ZMod r, f n * ZMod.dft (fun k => conj (ZMod.dft g k)) n := by
      simp only [sum_mul]
      rw [sum_comm]
      apply sum_congr rfl
      intro n _
      rw [ZMod.dft_apply, mul_sum]
      apply sum_congr rfl
      intro k _
      simp only [smul_eq_mul, mul_comm k n]
      ring
    _ = _ := by
      simp_rw [dft_conj, ZMod.dft_dft, neg_neg, smul_eq_mul, map_mul, Complex.conj_natCast]
      rw [mul_sum]
      apply sum_congr rfl
      intro n _
      ring

/-- Parseval's identity for the unnormalized discrete Fourier transform. -/
theorem dft_energy {r : ℕ} [NeZero r] (f : ZMod r → ℂ) :
    energy (ZMod.dft f) = (r : ℝ) * energy f := by
  have h := dft_pairing f f
  simp only [Complex.mul_conj'] at h
  exact_mod_cast h

/-- Cyclic convolution becomes multiplication under the discrete Fourier transform. -/
theorem dft_cyclicConv {r : ℕ} [NeZero r] (f g : ZMod r → ℂ) (k : ZMod r) :
    ZMod.dft (cyclicConv f g) k = ZMod.dft f k * ZMod.dft g k := by
  rw [ZMod.dft_apply]
  simp only [cyclicConv, smul_eq_mul, mul_sum]
  rw [sum_comm]
  rw [ZMod.dft_apply, ZMod.dft_apply, sum_mul]
  apply sum_congr rfl
  intro n _
  rw [mul_sum]
  calc
    _ = ∑ m : ZMod r, ZMod.stdAddChar (-((m + n) * k)) * (f n * g m) := by
      exact Fintype.sum_equiv (Equiv.addRight (-n)) _ _ (fun m => by simp [sub_eq_add_neg])
    _ = _ := by
      apply sum_congr rfl
      intro m _
      rw [add_mul, neg_add, AddChar.map_add_eq_mul]
      simp only [smul_eq_mul]
      ring

/-- A uniform Fourier bound controls the convolution energy without a factor of the modulus. -/
theorem cyclicConv_energy_bound {r : ℕ} [NeZero r] (f g : ZMod r → ℂ) {B : ℝ}
    (hB : 0 ≤ B) (hf : ∀ k, ‖ZMod.dft f k‖ ≤ B) :
    energy (cyclicConv f g) ≤ B ^ 2 * energy g := by
  have hE : energy (ZMod.dft (cyclicConv f g)) ≤ B ^ 2 * energy (ZMod.dft g) := by
    unfold energy
    rw [mul_sum]
    apply sum_le_sum
    intro k _
    rw [dft_cyclicConv, norm_mul, mul_pow]
    exact mul_le_mul_of_nonneg_right (sq_le_sq₀ (norm_nonneg _) hB |>.mpr (hf k)) (sq_nonneg _)
  rw [dft_energy, dft_energy] at hE
  have hr : (0 : ℝ) < r := Nat.cast_pos.mpr (NeZero.pos r)
  nlinarith

/-- The energy bounds the number of values above any nonnegative threshold. -/
theorem energy_large_values {ι : Type*} [Fintype ι] (f : ι → ℂ) {T : ℝ} (hT : 0 ≤ T) :
    ((Finset.univ.filter fun m => T < ‖f m‖).card : ℝ) * T ^ 2 ≤ energy f := by
  classical
  calc
    _ = ∑ m ∈ Finset.univ.filter (fun m => T < ‖f m‖), T ^ 2 := by
      simp [nsmul_eq_mul]
    _ ≤ ∑ m ∈ Finset.univ.filter (fun m => T < ‖f m‖), ‖f m‖ ^ 2 := by
      apply sum_le_sum
      intro m hm
      exact (sq_le_sq₀ hT (norm_nonneg _) |>.mpr (mem_filter.mp hm).2.le)
    _ ≤ energy f := sum_le_sum_of_subset_of_nonneg (filter_subset _ _) (fun _ _ _ => sq_nonneg _)

/-- Finite cyclic version of the large-value estimate in Lemma 4.2 on page 19. -/
theorem cyclicConv_large_values {r : ℕ} [NeZero r] (f g : ZMod r → ℂ) {B T : ℝ}
    (hB : 0 ≤ B) (hT : 0 < T) (hf : ∀ k, ‖ZMod.dft f k‖ ≤ B) :
    ((Finset.univ.filter fun m => T < ‖cyclicConv f g m‖).card : ℝ) ≤
      B ^ 2 * energy g / T ^ 2 := by
  exact (le_div_iff₀ (sq_pos_of_pos hT)).mpr
    ((energy_large_values (cyclicConv f g) hT.le).trans (cyclicConv_energy_bound f g hB hf))

/-- The exponent two thirds in Lemma 4.2 comes from cubing the threshold coefficient. -/
theorem two_thirds_cube {η : ℝ} (hη : 0 ≤ η) :
    (η ^ ((2 : ℝ) / 3)) ^ 3 = η ^ 2 := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hη]
  norm_num

/-- The quantitative large-value estimate with the exact two-thirds exponent of page 19. -/
theorem cyclicConv_two_thirds {r : ℕ} [NeZero r] (f g : ZMod r → ℂ)
    {η N G : ℝ} (hη : 0 < η) (hN : 0 < N) (hG : 0 < G)
    (hg : energy g ≤ G ^ 2) (hf : ∀ k, ‖ZMod.dft f k‖ ≤ η * N) :
    ((Finset.univ.filter fun m =>
      η ^ ((2 : ℝ) / 3) * Real.sqrt N * G < ‖cyclicConv f g m‖).card : ℝ) ≤
        η ^ ((2 : ℝ) / 3) * N := by
  let a := η ^ ((2 : ℝ) / 3)
  have ha : 0 < a := Real.rpow_pos_of_pos hη _
  have ha3 : a ^ 3 = η ^ 2 := two_thirds_cube hη.le
  have h := (energy_large_values (cyclicConv f g) (show 0 ≤ a * Real.sqrt N * G by positivity)).trans
    ((cyclicConv_energy_bound f g (mul_pos hη hN).le hf).trans
      (mul_le_mul_of_nonneg_left hg (sq_nonneg _)))
  have hP : 0 < a ^ 2 * N * G ^ 2 := by positivity
  apply (mul_le_mul_iff_right₀ hP).mp
  convert h using 1
  · rw [mul_pow, mul_pow, Real.sq_sqrt hN.le]
    ring
  · rw [mul_pow, ← ha3]
    ring

end
end LeanLab.ChenPrimeExceptional.Task101

#print axioms LeanLab.ChenPrimeExceptional.Task101.dft_pairing
#print axioms LeanLab.ChenPrimeExceptional.Task101.dft_energy
#print axioms LeanLab.ChenPrimeExceptional.Task101.dft_cyclicConv
#print axioms LeanLab.ChenPrimeExceptional.Task101.cyclicConv_energy_bound
#print axioms LeanLab.ChenPrimeExceptional.Task101.energy_large_values
#print axioms LeanLab.ChenPrimeExceptional.Task101.cyclicConv_large_values
#print axioms LeanLab.ChenPrimeExceptional.Task101.two_thirds_cube
#print axioms LeanLab.ChenPrimeExceptional.Task101.cyclicConv_two_thirds
