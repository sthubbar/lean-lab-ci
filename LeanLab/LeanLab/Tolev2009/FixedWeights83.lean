/-
AI wrote this Lean code. Codex task83.
Binary Goldbach is open.
Source: https://arxiv.org/abs/0902.2669 page 2, the formula before the main theorem.
The fixed residues here are positive natural numbers.
-/
import LeanLab.Tolev2009.Faithful

open Finset Real

namespace LeanLab.Tolev2009.FixedWeights83

open LeanLab.Tolev2009 LeanLab.Tolev2009.Faithful

/-- LEAF. Page 1 display 2. Reducing each residue preserves the weighted error. -/
theorem delta_mod (k l : Fin 3 → ℕ) (N : ℕ) :
    Δ singSeries k (fun i => l i % k i) N = Δ singSeries k l N := by
  simp only [Δ, M, singSeries_mod, R, Nat.mod_mod]

/-- LEAF. Page 2, the weighted average for three fixed natural residues. -/
noncomputable def fixedError (lam₁ lam₂ lam₃ : ℕ → ℝ) (l₁ l₂ l₃ : ℕ)
    (B : ℝ) (N : ℕ) : ℝ :=
  let L := Real.log N
  let K := ⌊Real.sqrt N * L ^ (-B)⌋₊
  let K₃ := ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * L ^ (-B)⌋₊
  ∑ k₁ ∈ Icc 1 K, ∑ k₂ ∈ Icc 1 K,
    if Nat.Coprime l₁ k₁ ∧ Nat.Coprime l₂ k₂ then
      lam₁ k₁ * lam₂ k₂ *
        ∑ k₃ ∈ (Icc 1 K₃).filter (fun k => Nat.Coprime k l₃),
          lam₃ k₃ * Δ singSeries ![k₁, k₂, k₃] ![l₁, l₂, l₃] N
    else 0

/-- LEAF. Page 2 displays 4 and 5. Taking fixed residues and bounded outer weights
is dominated by the maximum over residues. No analytic input is used. -/
theorem fixedError_le (lam₁ lam₂ lam₃ : ℕ → ℝ) (l₁ l₂ l₃ : ℕ) (B : ℝ) (N : ℕ)
    (h₁ : ∀ k, |lam₁ k| ≤ 1) (h₂ : ∀ k, |lam₂ k| ≤ 1) :
    |fixedError lam₁ lam₂ lam₃ l₁ l₂ l₃ B N| ≤ Estar singSeries lam₃ l₃ B N := by
  unfold fixedError Estar
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k₁ hk₁ => ?_)
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun k₂ hk₂ => ?_)
  split_ifs with hc
  · have hk1 : 0 < k₁ := (mem_Icc.mp hk₁).1
    have hk2 : 0 < k₂ := (mem_Icc.mp hk₂).1
    have hr1 : l₁ % k₁ ∈ residues k₁ := by
      simp only [residues, mem_filter, mem_range]
      exact ⟨Nat.mod_lt _ hk1, by simpa using hc.1⟩
    have hr2 : l₂ % k₂ ∈ residues k₂ := by
      simp only [residues, mem_filter, mem_range]
      exact ⟨Nat.mod_lt _ hk2, by simpa using hc.2⟩
    have he : ∀ k₃, Δ singSeries ![k₁, k₂, k₃] ![l₁, l₂, l₃] N =
        Δ singSeries ![k₁, k₂, k₃] ![l₁ % k₁, l₂ % k₂, l₃] N := by
      intro k₃
      rw [← delta_mod ![k₁, k₂, k₃] ![l₁, l₂, l₃],
        ← delta_mod ![k₁, k₂, k₃] ![l₁ % k₁, l₂ % k₂, l₃]]
      congr 1
      funext i
      fin_cases i <;> simp
    rw [abs_mul, abs_mul]
    have hb : |lam₁ k₁| * |lam₂ k₂| ≤ 1 := by
      simpa using mul_le_mul (h₁ k₁) (h₂ k₂) (abs_nonneg _) (by norm_num : (0 : ℝ) ≤ 1)
    refine (mul_le_of_le_one_left (abs_nonneg _) hb).trans ?_
    have hsum : (∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter
        (fun k => Nat.Coprime k l₃),
        lam₃ k₃ * Δ singSeries ![k₁, k₂, k₃] ![l₁, l₂, l₃] N) =
        ∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter
        (fun k => Nat.Coprime k l₃),
        lam₃ k₃ * Δ singSeries ![k₁, k₂, k₃] ![l₁ % k₁, l₂ % k₂, l₃] N := by
      refine sum_congr rfl fun k₃ _ => ?_
      rw [he k₃]
    rw [hsum]
    exact le_iSup2 (residues k₁) (residues k₂)
      (fun a b => |∑ k₃ ∈ (Icc 1 ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊).filter
        (fun k => Nat.Coprime k l₃),
        lam₃ k₃ * Δ singSeries ![k₁, k₂, k₃] ![a, b, l₃] N|)
      (fun _ _ => abs_nonneg _) hr1 hr2
  · simpa only [abs_zero, innerF, inner] using
      innerF_nonneg (fun k l => Δ singSeries k l N) lam₃ l₃
        ⌊(N : ℝ) ^ ((1 : ℝ) / 3) * Real.log N ^ (-B)⌋₊ k₁ k₂

/-- LEAF. Page 2, the formula before the theorem follows from display 5.
CONDITIONAL ON the faithful MainTheorem. B depends only on A. -/
theorem fixed_weights_of_main (h : MainTheorem) :
    ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧
      ∀ l₁ l₂ l₃ : ℕ, 1 ≤ l₁ → 1 ≤ l₂ → 1 ≤ l₃ →
      ∃ C N₀ : ℝ, ∀ lam₁ lam₂ lam₃ : ℕ → ℝ,
        (∀ k, |lam₁ k| ≤ 1) → (∀ k, |lam₂ k| ≤ 1) → (∀ k, |lam₃ k| ≤ 1) →
        ∀ N : ℕ, Odd N → N₀ ≤ N →
          |fixedError lam₁ lam₂ lam₃ l₁ l₂ l₃ B N| ≤
            C * (N : ℝ) ^ 2 * Real.log N ^ (-A) := by
  intro A hA
  obtain ⟨B, hB, hb⟩ := h A hA
  refine ⟨B, hB, fun l₁ l₂ l₃ _ _ hl₃ => ?_⟩
  obtain ⟨C, N₀, hc⟩ := hb l₃ hl₃
  refine ⟨C, N₀, fun lam₁ lam₂ lam₃ h₁ h₂ h₃ N hodd hN => ?_⟩
  exact (fixedError_le lam₁ lam₂ lam₃ l₁ l₂ l₃ B N h₁ h₂).trans (hc lam₃ h₃ N hodd hN)

end LeanLab.Tolev2009.FixedWeights83
