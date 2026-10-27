/-
AI wrote this Lean code for CODEX task101.
P0039 Lemma 4.3, page 20. Finite Fourier sums and sieve twists.
Binary Goldbach is open.
-/
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.Normed.Group.FunctionSeries
import Mathlib.Tactic

open Finset

namespace LeanLab.ChenPrimeExceptional.Task101

noncomputable section

/-- The standard positive additive phase as a complex valued character. -/
def phase : AddChar ℝ ℂ := Circle.coeHom.compAddChar Real.fourierChar

/-- The finite Fourier sum with the positive sign convention of Definition 4.1. -/
def fourierSum (s : Finset ℕ) (g : ℕ → ℂ) (α : ℝ) : ℂ :=
  ∑ n ∈ s, g n * phase (α * n)

/-- The Fourier supremum for a fixed finite support. -/
def fourierNorm (s : Finset ℕ) (g : ℕ → ℂ) : ℝ :=
  ⨆ α : ℝ, ‖fourierSum s g α‖

/-- Finite support bounds every Fourier sum by the sum of absolute values. -/
theorem fourierSum_le_l1 (s : Finset ℕ) (g : ℕ → ℂ) (α : ℝ) :
    ‖fourierSum s g α‖ ≤ ∑ n ∈ s, ‖g n‖ := by
  exact (norm_sum_le _ _).trans_eq (sum_congr rfl fun n _ => by
    rw [norm_mul]
    change ‖g n‖ * ‖(Real.fourierChar (α * n) : ℂ)‖ = ‖g n‖
    simp)

/-- The set defining the supremum is bounded above. -/
theorem fourierSum_bddAbove (s : Finset ℕ) (g : ℕ → ℂ) :
    BddAbove (Set.range fun α : ℝ => ‖fourierSum s g α‖) := by
  exact ⟨∑ n ∈ s, ‖g n‖, by rintro _ ⟨α, rfl⟩; exact fourierSum_le_l1 s g α⟩

/-- Every Fourier sum is bounded by the Fourier norm. -/
theorem fourierSum_le_norm (s : Finset ℕ) (g : ℕ → ℂ) (α : ℝ) :
    ‖fourierSum s g α‖ ≤ fourierNorm s g := by
  exact le_ciSup (fourierSum_bddAbove s g) α

/-- The Fourier norm is nonnegative. -/
theorem fourierNorm_nonneg (s : Finset ℕ) (g : ℕ → ℂ) :
    0 ≤ fourierNorm s g :=
  (norm_nonneg _).trans (fourierSum_le_norm s g 0)

/-- A uniform bound on Fourier sums bounds the Fourier norm. -/
theorem fourierNorm_le {s : Finset ℕ} {g : ℕ → ℂ} {B : ℝ}
    (h : ∀ α : ℝ, ‖fourierSum s g α‖ ≤ B) : fourierNorm s g ≤ B := by
  exact ciSup_le h

/-- The residue character is a real Fourier phase of rational frequency. -/
theorem residue_phase {d : ℕ} [NeZero d] (b : ZMod d) (n : ℕ) :
    ZMod.stdAddChar (b * (n : ZMod d)) =
      phase (((b.val : ℝ) / d) * n) := by
  calc
    _ = ZMod.stdAddChar ((b.val * n : ℕ) : ZMod d) := by
      rw [Nat.cast_mul, ZMod.natCast_zmod_val]
    _ = Complex.exp (2 * Real.pi * Complex.I * (b.val * n : ℕ) / d) := by
      simpa only [Int.cast_natCast] using
        (ZMod.stdAddChar_coe (N := d) ((b.val * n : ℕ) : ℤ))
    _ = _ := by
      change _ = (Real.fourierChar _ : ℂ)
      rw [Real.fourierChar_apply]
      push_cast
      congr 1
      ring

/-- Character orthogonality detects divisibility by the modulus. -/
theorem divisor_indicator {d : ℕ} [NeZero d] (n : ℕ) :
    (if d ∣ n then (1 : ℂ) else 0) =
      (d : ℂ)⁻¹ * ∑ b : ZMod d, ZMod.stdAddChar (b * (n : ZMod d)) := by
  rw [AddChar.sum_mulShift _ (ZMod.isPrimitive_stdAddChar d)]
  simp only [ZMod.card, ZMod.natCast_eq_zero_iff]
  split_ifs <;> simp [NeZero.ne (d : ℂ)]

/-- Multiplying by a rational phase translates the Fourier frequency. -/
theorem fourierSum_phase (s : Finset ℕ) (g : ℕ → ℂ) (α β : ℝ) :
    fourierSum s (fun n => g n * phase (β * n)) α =
      fourierSum s g (α + β) := by
  unfold fourierSum
  apply sum_congr rfl
  intro n _
  rw [add_mul, AddChar.map_add_eq_mul]
  ring

/-- Projecting to multiples of d is the average of d shifted Fourier sums. -/
theorem fourierSum_divisor (s : Finset ℕ) (g : ℕ → ℂ) {d : ℕ} [NeZero d] (α : ℝ) :
    fourierSum s (fun n => if d ∣ n then g n else 0) α =
      (d : ℂ)⁻¹ * ∑ b : ZMod d, fourierSum s g (α + (b.val : ℝ) / d) := by
  have hterm (n : ℕ) :
      (if d ∣ n then g n else 0) * phase (α * n) =
        (d : ℂ)⁻¹ * ∑ b : ZMod d,
          g n * phase ((α + (b.val : ℝ) / d) * n) := by
    simp_rw [add_mul, AddChar.map_add_eq_mul, ← residue_phase]
    rw [show (∑ b : ZMod d, g n * (phase (α * n) *
        ZMod.stdAddChar (b * (n : ZMod d)))) =
      g n * phase (α * n) * ∑ b : ZMod d,
        ZMod.stdAddChar (b * (n : ZMod d)) by
      simp_rw [← mul_assoc]; rw [mul_sum]]
    have h := divisor_indicator (d := d) n
    rw [show (d : ℂ)⁻¹ * (g n * phase (α * n) *
        ∑ b : ZMod d, ZMod.stdAddChar (b * (n : ZMod d))) =
      g n * phase (α * n) * ((d : ℂ)⁻¹ *
        ∑ b : ZMod d, ZMod.stdAddChar (b * (n : ZMod d))) by ring, ← h]
    split_ifs <;> simp
  change (∑ n ∈ s, (if d ∣ n then g n else 0) * phase (α * n)) =
    (d : ℂ)⁻¹ * ∑ b : ZMod d, ∑ n ∈ s,
      g n * phase ((α + (b.val : ℝ) / d) * n)
  simp_rw [hterm]
  rw [← mul_sum, sum_comm]

/-- The Fourier norm cannot increase under projection to multiples of a positive integer. -/
theorem fourierNorm_divisor (s : Finset ℕ) (g : ℕ → ℂ) {d : ℕ} [NeZero d] :
    fourierNorm s (fun n => if d ∣ n then g n else 0) ≤ fourierNorm s g := by
  apply fourierNorm_le
  intro α
  rw [fourierSum_divisor, norm_mul, norm_inv, Complex.norm_natCast]
  calc
    _ ≤ (d : ℝ)⁻¹ * ∑ b : ZMod d, fourierNorm s g := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (Nat.cast_nonneg _))
      exact (norm_sum_le _ _).trans (sum_le_sum fun b _ => fourierSum_le_norm s g _)
    _ = fourierNorm s g := by
      simp [ZMod.card, nsmul_eq_mul, NeZero.ne (d : ℝ)]

/-- Opening a finite divisor-sum sieve gives a weighted sum of residue projections. -/
theorem fourierSum_sieve (s D : Finset ℕ) (g weights : ℕ → ℂ) (α : ℝ) :
    fourierSum s (fun n => (∑ d ∈ D, if d ∣ n then weights d else 0) * g n) α =
      ∑ d ∈ D, weights d * fourierSum s (fun n => if d ∣ n then g n else 0) α := by
  unfold fourierSum
  simp_rw [sum_mul, mul_sum]
  rw [sum_comm]
  apply sum_congr rfl
  intro d _
  apply sum_congr rfl
  intro n _
  split_ifs <;> ring

/-- Lemma 4.3, page 20, first inequality for a finitely supported sieve weight. -/
theorem fourierNorm_sieve (s D : Finset ℕ) (g weights : ℕ → ℂ)
    (hD : ∀ d ∈ D, d ≠ 0) :
    fourierNorm s (fun n => (∑ d ∈ D, if d ∣ n then weights d else 0) * g n) ≤
      (∑ d ∈ D, ‖weights d‖) * fourierNorm s g := by
  apply fourierNorm_le
  intro α
  rw [fourierSum_sieve]
  calc
    _ ≤ ∑ d ∈ D, ‖weights d * fourierSum s (fun n => if d ∣ n then g n else 0) α‖ :=
      norm_sum_le _ _
    _ ≤ ∑ d ∈ D, ‖weights d‖ * fourierNorm s g := by
      apply sum_le_sum
      intro d hd
      let : NeZero d := ⟨hD d hd⟩
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left
        ((fourierSum_le_norm s _ α).trans (fourierNorm_divisor s g)) (norm_nonneg _)
    _ = _ := (sum_mul ..).symm

end
end LeanLab.ChenPrimeExceptional.Task101
#print axioms LeanLab.ChenPrimeExceptional.Task101.fourierSum_le_l1
#print axioms LeanLab.ChenPrimeExceptional.Task101.fourierSum_bddAbove
#print axioms LeanLab.ChenPrimeExceptional.Task101.fourierSum_le_norm
#print axioms LeanLab.ChenPrimeExceptional.Task101.fourierNorm_nonneg
#print axioms LeanLab.ChenPrimeExceptional.Task101.fourierNorm_le

#print axioms LeanLab.ChenPrimeExceptional.Task101.residue_phase
#print axioms LeanLab.ChenPrimeExceptional.Task101.divisor_indicator
#print axioms LeanLab.ChenPrimeExceptional.Task101.fourierSum_phase
#print axioms LeanLab.ChenPrimeExceptional.Task101.fourierSum_divisor
#print axioms LeanLab.ChenPrimeExceptional.Task101.fourierNorm_divisor
#print axioms LeanLab.ChenPrimeExceptional.Task101.fourierSum_sieve
#print axioms LeanLab.ChenPrimeExceptional.Task101.fourierNorm_sieve
