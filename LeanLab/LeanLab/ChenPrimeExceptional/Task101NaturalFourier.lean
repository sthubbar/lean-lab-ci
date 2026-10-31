/-
AI wrote this Lean code for CODEX task101.
Natural-number realization of the large-value estimate in P0039 Lemma 4.2, page 19.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task101FourierEnergy

open Finset

namespace LeanLab.ChenPrimeExceptional.Task101

noncomputable section

/-- Extend the values from zero through N to a cyclic group with no convolution wraparound. -/
def cyclicLift (N : ℕ) (f : ℕ → ℂ) (x : ZMod (2 * N + 1)) : ℂ :=
  if x.val ≤ N then f x.val else 0

/-- The natural-number convolution of the two functions truncated at N. -/
def natConv (N : ℕ) (f g : ℕ → ℂ) (m : ℕ) : ℂ :=
  ∑ n ∈ range (N + 1), if n ≤ m ∧ m - n ≤ N then f n * g (m - n) else 0

/-- Sum over cyclic residues by their natural representatives. -/
theorem sum_zmod_val {M : Type*} [AddCommMonoid M] {r : ℕ} [NeZero r] (f : ℕ → M) :
    ∑ x : ZMod r, f x.val = ∑ n ∈ range r, f n := by
  cases r with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ r => exact Fin.sum_univ_eq_sum_range f (r + 1)

/-- A truncated sum in the larger cyclic range is the original natural sum. -/
theorem sum_truncated_range {M : Type*} [AddCommMonoid M] (N : ℕ) (f : ℕ → M) :
    (∑ n ∈ range (2 * N + 1), if n ≤ N then f n else 0) = ∑ n ∈ range (N + 1), f n := by
  rw [← sum_filter]
  congr 1
  ext n
  simp only [mem_filter, mem_range]
  omega

/-- The discrete transform of the lift is a sample of the real Fourier sum. -/
theorem dft_cyclicLift (N : ℕ) (f : ℕ → ℂ) (k : ZMod (2 * N + 1)) :
    ZMod.dft (cyclicLift N f) k =
      fourierSum (range (N + 1)) f (((-k).val : ℝ) / (2 * N + 1)) := by
  have hterm (x : ZMod (2 * N + 1)) :
      ZMod.stdAddChar (-(x * k)) * cyclicLift N f x =
        if x.val ≤ N then f x.val * phase (((-k).val : ℝ) / (2 * N + 1) * x.val) else 0 := by
    rw [show -(x * k) = (-k) * (x.val : ZMod (2 * N + 1)) by simp; ring,
      residue_phase]
    push_cast
    unfold cyclicLift
    split_ifs <;> ring
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, hterm]
  rw [sum_zmod_val (r := 2 * N + 1) (fun n => if n ≤ N then
    f n * phase (((-k).val : ℝ) / (2 * N + 1) * n) else 0), sum_truncated_range]
  rfl

/-- Lifting preserves the energy on the truncated natural support. -/
theorem energy_cyclicLift (N : ℕ) (f : ℕ → ℂ) :
    energy (cyclicLift N f) = ∑ n ∈ range (N + 1), ‖f n‖ ^ 2 := by
  unfold energy cyclicLift
  simp_rw [apply_ite (fun z : ℂ => ‖z‖ ^ 2), norm_zero, zero_pow (by decide : 2 ≠ 0)]
  rw [sum_zmod_val (r := 2 * N + 1) (fun n => if n ≤ N then ‖f n‖ ^ 2 else 0),
    sum_truncated_range]

/-- A lifted subtraction agrees with natural subtraction on all possible contributing terms. -/
theorem cyclicLift_sub (N : ℕ) (g : ℕ → ℂ) {m n : ℕ} (hm : m ≤ 2 * N) (hn : n ≤ N) :
    cyclicLift N g ((m : ZMod (2 * N + 1)) - n) =
      if n ≤ m ∧ m - n ≤ N then g (m - n) else 0 := by
  have hmval : (m : ZMod (2 * N + 1)).val = m := ZMod.val_natCast_of_lt (by omega)
  have hnval : (n : ZMod (2 * N + 1)).val = n := ZMod.val_natCast_of_lt (by omega)
  by_cases hnm : n ≤ m
  · have hv := ZMod.val_sub (a := (m : ZMod (2 * N + 1))) (b := n)
      (by rw [hmval, hnval]; exact hnm)
    rw [hmval, hnval] at hv
    simp only [cyclicLift, hv, hnm, true_and]
  · have hlarge : N < ((m : ZMod (2 * N + 1)) - n).val := by
      by_contra h
      have hsmall : ((m : ZMod (2 * N + 1)) - n).val ≤ N := by omega
      have he := congrArg ZMod.val (sub_add_cancel (m : ZMod (2 * N + 1)) n)
      rw [ZMod.val_add_of_lt (by rw [hnval]; omega), hmval, hnval] at he
      omega
    simp [cyclicLift, hnm, not_le.mpr hlarge]

/-- The cyclic convolution has no wraparound on the full natural convolution range. -/
theorem cyclicConv_cyclicLift (N : ℕ) (f g : ℕ → ℂ) {m : ℕ} (hm : m ≤ 2 * N) :
    cyclicConv (cyclicLift N f) (cyclicLift N g) (m : ZMod (2 * N + 1)) =
      natConv N f g m := by
  unfold cyclicConv
  have hterm (x : ZMod (2 * N + 1)) :
      cyclicLift N f x * cyclicLift N g ((m : ZMod (2 * N + 1)) - x) =
        if x.val ≤ N then f x.val *
          cyclicLift N g ((m : ZMod (2 * N + 1)) - (x.val : ZMod (2 * N + 1))) else 0 := by
    rw [ZMod.natCast_zmod_val]
    unfold cyclicLift
    split_ifs <;> ring
  simp only [hterm]
  rw [sum_zmod_val (r := 2 * N + 1) (fun n => if n ≤ N then
    f n * cyclicLift N g ((m : ZMod (2 * N + 1)) - n) else 0), sum_truncated_range]
  unfold natConv
  apply sum_congr rfl
  intro n hn
  rw [cyclicLift_sub N g hm (by simp only [mem_range] at hn; omega)]
  split_ifs <;> ring

/-- The lift preserves the entire natural convolution energy. -/
theorem energy_natConv (N : ℕ) (f g : ℕ → ℂ) :
    energy (cyclicConv (cyclicLift N f) (cyclicLift N g)) =
      ∑ m ∈ range (2 * N + 1), ‖natConv N f g m‖ ^ 2 := by
  unfold energy
  calc
    _ = ∑ x : ZMod (2 * N + 1), ‖natConv N f g x.val‖ ^ 2 := by
      apply sum_congr rfl
      intro x _
      have h := cyclicConv_cyclicLift N f g (m := x.val) (by have := x.val_lt; omega)
      rw [ZMod.natCast_zmod_val] at h
      rw [h]
    _ = _ := sum_zmod_val (r := 2 * N + 1) (fun m => ‖natConv N f g m‖ ^ 2)

/-- The real Fourier supremum controls natural convolution energy. -/
theorem natConv_energy_bound (N : ℕ) (f g : ℕ → ℂ) {B : ℝ}
    (hB : 0 ≤ B) (hf : fourierNorm (range (N + 1)) f ≤ B) :
    (∑ m ∈ range (2 * N + 1), ‖natConv N f g m‖ ^ 2) ≤
      B ^ 2 * ∑ n ∈ range (N + 1), ‖g n‖ ^ 2 := by
  have h := cyclicConv_energy_bound (cyclicLift N f) (cyclicLift N g) hB (fun k => by
    rw [dft_cyclicLift]
    exact (fourierSum_le_norm _ _ _).trans hf)
  rwa [energy_natConv, energy_cyclicLift] at h

/-- Natural and cyclic exceptional sets have equal cardinality under the lift. -/
theorem natConv_large_card_eq (N : ℕ) (f g : ℕ → ℂ) (T : ℝ) :
    (range (2 * N + 1) |>.filter fun m => T < ‖natConv N f g m‖).card =
      (univ.filter fun m : ZMod (2 * N + 1) =>
        T < ‖cyclicConv (cyclicLift N f) (cyclicLift N g) m‖).card := by
  classical
  apply card_nbij' (fun m : ℕ => (m : ZMod (2 * N + 1))) ZMod.val
  · intro m hm
    simp only [Finset.mem_coe, mem_filter, mem_range] at hm
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and]
    rw [cyclicConv_cyclicLift N f g (by omega)]
    exact hm.2
  · intro x hx
    simp only [Finset.mem_coe, mem_filter, mem_univ, true_and] at hx
    simp only [Finset.mem_coe, mem_filter, mem_range]
    refine ⟨x.val_lt, ?_⟩
    have h := cyclicConv_cyclicLift N f g (m := x.val) (by have := x.val_lt; omega)
    rw [ZMod.natCast_zmod_val] at h
    rwa [← h]
  · intro m hm
    exact ZMod.val_natCast_of_lt (by simp only [Finset.mem_coe, mem_filter, mem_range] at hm; exact hm.1)
  · intro x _
    exact ZMod.natCast_zmod_val x

/-- The exact two-thirds large-value estimate on natural numbers for an arbitrary energy bound. -/
theorem natConv_two_thirds (N : ℕ) (f g : ℕ → ℂ) {η G : ℝ}
    (hη : 0 < η) (hN : 0 < N) (hG : 0 < G)
    (hg : (∑ n ∈ range (N + 1), ‖g n‖ ^ 2) ≤ G ^ 2)
    (hf : fourierNorm (range (N + 1)) f ≤ η * N) :
    (((range (2 * N + 1)).filter fun m =>
      η ^ ((2 : ℝ) / 3) * Real.sqrt N * G < ‖natConv N f g m‖).card : ℝ) ≤
        η ^ ((2 : ℝ) / 3) * N := by
  rw [natConv_large_card_eq]
  apply cyclicConv_two_thirds (cyclicLift N f) (cyclicLift N g) hη (by exact_mod_cast hN) hG
  · rwa [energy_cyclicLift]
  · intro k
    rw [dft_cyclicLift]
    exact (fourierSum_le_norm _ _ _).trans hf

/-- Zero energy of the second function makes the truncated natural convolution vanish. -/
theorem natConv_zero_of_energy_zero (N : ℕ) (f g : ℕ → ℂ)
    (hg : (∑ n ∈ range (N + 1), ‖g n‖ ^ 2) = 0) (m : ℕ) : natConv N f g m = 0 := by
  have hzero : ∀ n ∈ range (N + 1), g n = 0 := by
    intro n hn
    have hs : ‖g n‖ ^ 2 ≤ ∑ n ∈ range (N + 1), ‖g n‖ ^ 2 :=
      single_le_sum (f := fun n => ‖g n‖ ^ 2) (fun _ _ => sq_nonneg _) hn
    rw [hg] at hs
    have : ‖g n‖ = 0 := by nlinarith [norm_nonneg (g n)]
    exact norm_eq_zero.mp this
  unfold natConv
  apply sum_eq_zero
  intro n hn
  split_ifs with h
  · rw [hzero (m - n) (by simp only [mem_range]; omega), mul_zero]
  · rfl

/-- The core estimate of P0039 Lemma 4.2 on page 19, including the zero-energy case. -/
theorem natConv_paper_large_values (N : ℕ) (f g : ℕ → ℂ) {η : ℝ}
    (hη : 0 < η) (hN : 0 < N)
    (hf : fourierNorm (range (N + 1)) f ≤ η * N) :
    (((range (2 * N + 1)).filter fun m =>
      η ^ ((2 : ℝ) / 3) * Real.sqrt N *
        Real.sqrt (∑ n ∈ range (N + 1), ‖g n‖ ^ 2) < ‖natConv N f g m‖).card : ℝ) ≤
          η ^ ((2 : ℝ) / 3) * N := by
  have hg : 0 ≤ ∑ n ∈ range (N + 1), ‖g n‖ ^ 2 := sum_nonneg (fun _ _ => sq_nonneg _)
  by_cases hzero : (∑ n ∈ range (N + 1), ‖g n‖ ^ 2) = 0
  · simp only [hzero, Real.sqrt_zero, mul_zero, natConv_zero_of_energy_zero N f g hzero,
      norm_zero, lt_self_iff_false, filter_false, card_empty, Nat.cast_zero]
    positivity
  · exact natConv_two_thirds N f g hη hN (Real.sqrt_pos.mpr (lt_of_le_of_ne hg (Ne.symm hzero)))
      (by rw [Real.sq_sqrt hg]) hf

end
end LeanLab.ChenPrimeExceptional.Task101

#print axioms LeanLab.ChenPrimeExceptional.Task101.sum_zmod_val
#print axioms LeanLab.ChenPrimeExceptional.Task101.sum_truncated_range
#print axioms LeanLab.ChenPrimeExceptional.Task101.dft_cyclicLift
#print axioms LeanLab.ChenPrimeExceptional.Task101.energy_cyclicLift
#print axioms LeanLab.ChenPrimeExceptional.Task101.cyclicLift_sub
#print axioms LeanLab.ChenPrimeExceptional.Task101.cyclicConv_cyclicLift
#print axioms LeanLab.ChenPrimeExceptional.Task101.energy_natConv
#print axioms LeanLab.ChenPrimeExceptional.Task101.natConv_energy_bound
#print axioms LeanLab.ChenPrimeExceptional.Task101.natConv_large_card_eq
#print axioms LeanLab.ChenPrimeExceptional.Task101.natConv_two_thirds
#print axioms LeanLab.ChenPrimeExceptional.Task101.natConv_zero_of_energy_zero
#print axioms LeanLab.ChenPrimeExceptional.Task101.natConv_paper_large_values
