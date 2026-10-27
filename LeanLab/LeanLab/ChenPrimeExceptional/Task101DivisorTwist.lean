/-
AI wrote this Lean code for CODEX task101.
The literal divisor-sum form of P0039 Lemma 4.3, page 20.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task101CharacterTwist

open Finset

namespace LeanLab.ChenPrimeExceptional.Task101

noncomputable section

/-- Fourier norms depend only on the values on the chosen finite support. -/
theorem fourierNorm_congr (s : Finset ℕ) {g h : ℕ → ℂ} (hgh : ∀ n ∈ s, g n = h n) :
    fourierNorm s g = fourierNorm s h := by
  have heq : ∀ α, fourierSum s g α = fourierSum s h α := by
    intro α
    unfold fourierSum
    apply sum_congr rfl
    intro n hn
    rw [hgh n hn]
  simp only [fourierNorm, heq]

/-- A finite divisor sum is the residue-projection expansion used in Lemma 4.3. -/
theorem divisor_sum_truncation (weights : ℕ → ℂ) {n M : ℕ} (hn : 0 < n) (hM : n ≤ M) :
    (∑ d ∈ n.divisors, weights d) = ∑ d ∈ Icc 1 M, if d ∣ n then weights d else 0 := by
  rw [← sum_filter]
  congr 1
  ext d
  simp only [Nat.mem_divisors, mem_filter, mem_Icc]
  constructor
  · rintro ⟨hd, _⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hd hn, (Nat.le_of_dvd hn hd).trans hM⟩, hd⟩
  · rintro ⟨_, hd⟩
    exact ⟨hd, hn.ne'⟩

/-- Lemma 4.3 for the paper's literal sum over divisors on any positive finite support. -/
theorem fourierNorm_divisor_sum (s : Finset ℕ) (g weights : ℕ → ℂ) (M : ℕ)
    (hs : ∀ n ∈ s, 0 < n ∧ n ≤ M) :
    fourierNorm s (fun n => (∑ d ∈ n.divisors, weights d) * g n) ≤
      (∑ d ∈ Icc 1 M, ‖weights d‖) * fourierNorm s g := by
  have heq : fourierNorm s (fun n => (∑ d ∈ n.divisors, weights d) * g n) =
      fourierNorm s (fun n => (∑ d ∈ Icc 1 M, if d ∣ n then weights d else 0) * g n) := by
    apply fourierNorm_congr
    intro n hn
    rw [divisor_sum_truncation weights (hs n hn).1 (hs n hn).2]
  rw [heq]
  exact fourierNorm_sieve s (Icc 1 M) g weights (fun d hd => by simp only [mem_Icc] at hd; omega)

/-- Multiplying by an additive phase preserves the real Fourier supremum exactly. -/
theorem fourierNorm_phase (s : Finset ℕ) (g : ℕ → ℂ) (β : ℝ) :
    fourierNorm s (fun n => g n * phase (β * n)) = fourierNorm s g := by
  apply le_antisymm
  · apply fourierNorm_le
    intro α
    rw [fourierSum_phase]
    exact fourierSum_le_norm s g _
  · apply fourierNorm_le
    intro α
    have h := fourierSum_le_norm s (fun n => g n * phase (β * n)) (α - β)
    rwa [fourierSum_phase, sub_add_cancel] at h

/-- The transform of a single residue indicator has absolute value one at every frequency. -/
theorem residue_indicator_dft_norm {r : ℕ} [NeZero r] (a k : ZMod r) :
    ‖ZMod.dft (fun x : ZMod r => if x = a then (1 : ℂ) else 0) k‖ = 1 := by
  classical
  rw [ZMod.dft_apply]
  simp only [smul_eq_mul, mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]
  change ‖(ZMod.toCircle (-(a * k)) : ℂ)‖ = 1
  simp

/-- Restricting to any residue class cannot increase the Fourier norm. -/
theorem fourierNorm_residue (s : Finset ℕ) (g : ℕ → ℂ)
    {r : ℕ} [NeZero r] (a : ZMod r) :
    fourierNorm s (fun n => if (n : ZMod r) = a then g n else 0) ≤ fourierNorm s g := by
  have heq : (fun n : ℕ => if (n : ZMod r) = a then g n else 0) =
      (fun n : ℕ => (if (n : ZMod r) = a then (1 : ℂ) else 0) * g n) := by
    funext n
    split_ifs <;> simp
  rw [heq]
  have h := fourierNorm_periodic s g (fun x : ZMod r => if x = a then (1 : ℂ) else 0)
  simpa only [residue_indicator_dft_norm, sum_const, card_univ, ZMod.card,
    nsmul_eq_mul, mul_one, inv_mul_cancel₀ (NeZero.ne (r : ℝ)), one_mul] using h

end
end LeanLab.ChenPrimeExceptional.Task101

#print axioms LeanLab.ChenPrimeExceptional.Task101.fourierNorm_congr
#print axioms LeanLab.ChenPrimeExceptional.Task101.divisor_sum_truncation
#print axioms LeanLab.ChenPrimeExceptional.Task101.fourierNorm_divisor_sum
#print axioms LeanLab.ChenPrimeExceptional.Task101.fourierNorm_phase
#print axioms LeanLab.ChenPrimeExceptional.Task101.residue_indicator_dft_norm
#print axioms LeanLab.ChenPrimeExceptional.Task101.fourierNorm_residue
