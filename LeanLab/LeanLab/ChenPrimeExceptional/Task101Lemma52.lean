/-
AI wrote this Lean code for CODEX task101.
P0039 Lemma 5.2, page 29, with the literal natural interval and explicit constants.
Binary Goldbach is open.
-/
import LeanLab.ChenPrimeExceptional.Task101SmoothVariation

open Finset Real

namespace LeanLab.ChenPrimeExceptional.Task101

noncomputable section

/-- Reindex a natural interval by its distance from the lower endpoint. -/
theorem sum_shift_Ioc {A : Type*} [AddCommMonoid A] (a : ℕ → A) (q k : ℕ) :
    (∑ i ∈ range k, a (q + 1 + i)) = ∑ j ∈ Ioc q (q + k), a j := by
  have hi : Ioc q (q + k) = Ico (q + 1) (q + 1 + k) := by
    ext j
    simp only [mem_Ioc, mem_Ico]
    omega
  rw [hi, sum_Ico_eq_sum_range]
  simp

/-- The integer immediately below square root of N is below N for N at least two. -/
theorem floor_sqrt_lt {N : ℕ} (hN : 2 ≤ N) : ⌊sqrt (N : ℝ)⌋₊ < N := by
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hs := Real.sqrt_lt_self_iff.mpr hNr
  have hf := Nat.floor_le (sqrt_nonneg (N : ℝ))
  exact_mod_cast hf.trans_lt hs

/-- Lemma 5.2 with explicit constants and its natural interval square root of N below n at most N. -/
theorem lemma52_interval (N : ℕ) (hN : 2 ≤ N) (a : ℕ → ℂ) {f f' : ℝ → ℂ}
    {c W C M U : ℝ} (hc : 0 < c) (hC : 0 ≤ C)
    (hf : ∀ t ∈ Set.Icc (sqrt (N : ℝ)) N, HasDerivAt f (f' t) t)
    (hbound : ∀ t ∈ Set.Icc (sqrt (N : ℝ)) N, ‖f' t‖ ≤ C / t)
    (hlo : ∀ t ∈ Set.Icc (sqrt (N : ℝ)) N, c * log N ≤ ‖f t‖)
    (hhi : ∀ t ∈ Set.Icc (sqrt (N : ℝ)) N, ‖f t‖ ≤ W * log N)
    (hM : ∀ ξ : ℕ, ξ ≤ N → ‖∑ j ∈ Ioc ⌊sqrt (N : ℝ)⌋₊ ξ, a j‖ ≤ M)
    (hU : ∀ ξ : ℕ, ξ ≤ N → ‖∑ j ∈ Ioc ⌊sqrt (N : ℝ)⌋₊ ξ, f j * a j‖ ≤ U) :
    ‖∑ j ∈ Ioc ⌊sqrt (N : ℝ)⌋₊ N, f j * a j‖ ≤ (W + C) * log N * M ∧
      ‖∑ j ∈ Ioc ⌊sqrt (N : ℝ)⌋₊ N, a j‖ ≤ ((1 / c + C / c ^ 2) / log N) * U := by
  let q := ⌊sqrt (N : ℝ)⌋₊
  have hqN : q < N := floor_sqrt_lt hN
  have hNr : (1 : ℝ) < N := by exact_mod_cast (show 1 < N by omega)
  have hend : ((q + 1 : ℕ) : ℝ) + (N - q - 1 : ℕ) = N := by
    exact_mod_cast (show q + 1 + (N - q - 1) = N by omega)
  have hstart : sqrt (N : ℝ) ≤ ((q + 1 : ℕ) : ℝ) := by
    have h := Nat.lt_floor_add_one (sqrt (N : ℝ))
    exact_mod_cast h.le
  have hsubset : Set.Icc ((q + 1 : ℕ) : ℝ) (((q + 1 : ℕ) : ℝ) + (N - q - 1 : ℕ)) ⊆
      Set.Icc (sqrt (N : ℝ)) N := by
    intro t ht
    exact ⟨hstart.trans ht.1, ht.2.trans_eq hend⟩
  have hshift (k : ℕ) :
      (∑ i ∈ range k, f (((q + 1 : ℕ) : ℝ) + i) * a (q + 1 + i)) =
        ∑ j ∈ Ioc q (q + k), f j * a j := by
    convert sum_shift_Ioc (fun j => f j * a j) q k using 1
    apply sum_congr rfl
    intro i _
    push_cast
    rfl
  have hms : ∀ k ≤ N - q, ‖∑ i ∈ range k, a (q + 1 + i)‖ ≤ M := by
    intro k hk
    rw [sum_shift_Ioc]
    exact hM (q + k) (by omega)
  have hus : ∀ k ≤ N - q,
      ‖∑ i ∈ range k, f (((q + 1 : ℕ) : ℝ) + i) * a (q + 1 + i)‖ ≤ U := by
    intro k hk
    rw [hshift]
    exact hU (q + k) (by omega)
  have h := lemma52_logarithmic (fun i => a (q + 1 + i)) (N - q)
    (show (1 : ℝ) ≤ ((q + 1 : ℕ) : ℝ) by exact_mod_cast (show 1 ≤ q + 1 by omega))
    hNr hend.le hc hC (fun t ht => hf t (hsubset ht)) (fun t ht => hbound t (hsubset ht))
    (fun t ht => hlo t (hsubset ht)) (fun t ht => hhi t (hsubset ht)) hms hus
  rw [hshift, sum_shift_Ioc] at h
  have hqend : q + (N - q) = N := by omega
  simpa only [hqend] using h

end
end LeanLab.ChenPrimeExceptional.Task101

#print axioms LeanLab.ChenPrimeExceptional.Task101.sum_shift_Ioc
#print axioms LeanLab.ChenPrimeExceptional.Task101.floor_sqrt_lt
#print axioms LeanLab.ChenPrimeExceptional.Task101.lemma52_interval
