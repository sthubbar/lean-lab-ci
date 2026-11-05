import LeanLab.LiuWang2002.GapCert352

/-! Square interval transfer for Schoenfeld page 356. AI wrote the Lean code. Binary Goldbach is open. -/
namespace LeanLab.LiuWang2002.Task352
open Real

/-- One checked square interval transfers to the real correction.
Derived certificate step for page 356, proof of display 5.1 star. -/
theorem gap_square_interval (X : ℝ) (l h m : ℕ) (hl : 1 ≤ l)
    (hlo : (l : ℝ) ^ 2 ≤ X) (hhi : X ≤ (h : ℝ) ^ 2)
    (hc : 2718282 ^ m < gapProduct (l*l) * 1000000 ^ m)
    (hm : (98 : ℕ) * h + 61600 ≤ 100 * m) :
    0.98 * sqrt X + 616 < Chebyshev.psi X - Chebyshev.theta X := by
  have hg := gap_of_certificate (l*l) m 1 (by nlinarith) (by norm_num) (by simpa using hc)
  have hmono := gap_mono (show ((l*l : ℕ) : ℝ) ≤ X by simpa only [Nat.cast_mul, pow_two] using hlo)
  have hX : 0 ≤ X := (sq_nonneg (l : ℝ)).trans hlo
  have hs : sqrt X ≤ h := (sqrt_le_iff).mpr ⟨Nat.cast_nonneg _, hhi⟩
  have hmR : (98 : ℝ) * h + 61600 ≤ 100 * m := by exact_mod_cast hm
  norm_num at hg hmono
  linarith

/-- An explicit endpoint parameter keeps closed product certificates
opaque during interval assembly. Its equality to l squared is checked
separately. Derived transfer for page 356, display 5.1 star. -/
theorem gap_square_interval_at (X : ℝ) (N l h m : ℕ) (hN : N = l*l) (hl : 1 ≤ l)
    (hlo : (l : ℝ) ^ 2 ≤ X) (hhi : X ≤ (h : ℝ) ^ 2)
    (hc : 2718282 ^ m < gapProduct N * 1000000 ^ m)
    (hm : (98 : ℕ) * h + 61600 ≤ 100 * m) :
    0.98 * sqrt X + 616 < Chebyshev.psi X - Chebyshev.theta X := by
  subst N
  exact gap_square_interval X l h m hl hlo hhi hc hm


end LeanLab.LiuWang2002.Task352
#print axioms LeanLab.LiuWang2002.Task352.gap_square_interval
#print axioms LeanLab.LiuWang2002.Task352.gap_square_interval_at
