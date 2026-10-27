/-
P0095 Lu 2010, page 2379 equation 63 and page 2392 equation 86.
CODEX task47, unit U-8105. AI wrote this Lean code. Binary Goldbach is open.
Exact identification of the finite rational expansion with the printed Gauss sum form.
The mean-square conclusion is conditional on the cited zero mass estimate 39.
-/
import LeanLab.ExceptionalSet.Lu2010Formula63
import LeanLab.ExceptionalSet.Lu2010GaussFourier

namespace LeanLab.ExceptionalSet.Lu2010Eq63
open Finset ZMod
open LeanLab.PNTPort.LargeSieve
open LeanLab.ExceptionalSet.Lu2010Assembly
open LeanLab.ExceptionalSet.Lu2010ZeroIntegral
open LeanLab.ExceptionalSet.Lu2010Formula63
open LeanLab.ExceptionalSet.Lu2010Eq86
open LeanLab.ExceptionalSet.Lu2010GaussFourier

/-- A coefficient of one exponent pair in the expanded Gauss sum. -/
noncomputable def pairCoefficient (N : ℕ) (z : Exponent × Exponent) (p : ℕ × ℕ) : ℂ :=
  if pairMod z ∣ p.1 then J N z.1.rho z.2.rho * (tau z.1 p.1 * tau z.2 p.1) *
    pairChar z p.1 p.2 / (p.1.totient : ℂ) ^ 2 else 0

/-- One modulus in the literal Gauss sum expression 63. -/
noncomputable def gaussTerm (N : ℕ) (z : Exponent × Exponent) (q k : ℕ) : ℂ :=
  if hq : 0 < q then
    haveI : NeZero q := ⟨hq.ne'⟩
    if pairMod z ∣ q then
      (J N z.1.rho z.2.rho * (tau z.1 q * tau z.2 q) / (q.totient : ℂ) ^ 2) *
        gaussSum (pairChar z q) (stdAddChar.mulShift (-(k : ZMod q)))
    else 0
  else 0

/-- The finite counterpart of equation 63 with its conductor and ordinate restrictions. -/
noncomputable def printed63 (N : ℕ) (s : Finset Exponent) (M : ℝ) (k : ℕ) : ℂ :=
  ∑ z ∈ pairs N s M, ∑ q ∈ Icc 1 ⌊PP N⌋₊, gaussTerm N z q k

/-- Expanding G in one modulus gives the rational coefficients exactly. -/
theorem pair_eq_gauss (N : ℕ) (z : Exponent × Exponent) (Q k : ℕ) :
    rationalSum Q (pairCoefficient N z) (k : ℤ) = ∑ q ∈ Icc 1 Q, gaussTerm N z q k := by
  classical
  rw [rationalSum_double]
  apply sum_congr rfl
  intro q hq
  have hq0 : 0 < q := by have := (mem_Icc.mp hq).1; omega
  have : NeZero q := ⟨hq0.ne'⟩
  unfold gaussTerm
  rw [dite_eq_left hq0]
  by_cases hd : pairMod z ∣ q
  · simp only [pairCoefficient, hd, ite_true]
    rw [gauss_reduced, mul_sum]
    apply sum_congr rfl
    intro a _
    ring
  · simp [pairCoefficient, hd]

/-- The normalized packet expansion and the literal finite Gauss formula are equal. -/
theorem D6_eq_printed63 {N : ℕ} (hN : 1 ≤ N) (s : Finset Exponent) (M : ℝ) (k : ℕ) :
    D6 N s M k = printed63 N s M k := by
  classical
  have he : D6 N s M k = ∑ z ∈ pairs N s M, rationalSum ⌊PP N⌋₊ (pairCoefficient N z) (k : ℤ) := by
    unfold D6 rationalSum
    simp_rw [B_explicit hN, sum_mul]
    rw [sum_comm]
    rfl
  rw [he]
  unfold printed63
  apply sum_congr rfl
  intro z _
  exact pair_eq_gauss N z _ k

/-- The existing equation 86 window bound follows from equation 63 and the cited mass of 39. -/
theorem eq86_of_eq63_and_mass39 (family : ℕ → Finset Exponent) (M : ℕ → ℝ)
    (h39 : Mass39 family) :
    ∃ C86 : ℝ, 0 ≤ C86 ∧ ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N →
      ∑ k ∈ Win N, ‖printed63 N (family N) (M N) k‖ ^ 2 ≤
        C86 * PP N ^ (-1 : ℝ) * dd N * (N : ℝ) ^ (2.0003 : ℝ) := by
  obtain ⟨C86, hC86, N0, h86⟩ := eq86_of_mass39 family M h39
  refine ⟨C86, hC86, max N0 1, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := le_trans (le_max_right _ _) hN
  simp_rw [← D6_eq_printed63 hN1]
  exact h86 N (le_trans (le_max_left _ _) hN)

end LeanLab.ExceptionalSet.Lu2010Eq63

#print axioms LeanLab.ExceptionalSet.Lu2010Eq63.pair_eq_gauss
#print axioms LeanLab.ExceptionalSet.Lu2010Eq63.D6_eq_printed63
#print axioms LeanLab.ExceptionalSet.Lu2010Eq63.eq86_of_eq63_and_mass39
