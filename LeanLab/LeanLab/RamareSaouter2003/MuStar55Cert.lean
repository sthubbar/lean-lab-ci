/-
P0099, O. Ramaré and Y. Saouter, Short effective intervals containing primes,
J. Number Theory 98 (2003) 10-33. Copy: papers/P0099.pdf.

Unit U-6744, session 20261020T2217Z-cloud52. AI-written Lean code, Claude. Checked only by
the Lean kernel. Binary Goldbach is OPEN.

* `cert55a`, `cert55b`: the two rational inequalities of `holderCert_of` for m = 55, by
  `decide +kernel`. PROVED.
* `holderCert55`: `HolderCert 55`. PROVED.
* `muStar55Bounds`: `MuStar55Bounds`, μ_55/2 ≤ μ*_55 ≤ μ_55, outright. PROVED.
* `theorem2At1e20_of_thm4`: Table 1 row one, CONDITIONAL ON `Theorem4Fm` with T0 = 3.3e9 and
  `Lemma1Upper` only; the MuStar48Bounds hypothesis is discharged by `muStar48Bounds`.
* `theorem2_row59_of_thm4`: Table 1 row 59, CONDITIONAL ON `Theorem4Fm` and `Lemma1Upper` only.
* `theorem3_of_thm4`: Theorem 3, CONDITIONAL ON `Theorem4Fm`, `Lemma1Upper` and `ChainCert`.
-/
import Mathlib
import LeanLab.RamareSaouter2003.MuStarLower

namespace LeanLab.RamareSaouter2003.MuStar55Cert
open Real LeanLab.RamareSaouter2003.Smooth LeanLab.RamareSaouter2003.MuStarLower

theorem cert55a : 0 < intL 0 (mulL (powL (gL 55) 4) (powL wL 3)) := by decide +kernel
theorem cert55b : intL 0 (powL (gL 55) 2) * intL 0 (mulL (powL (gL 55) 4) (powL wL 3)) ≤
      4 * intL 0 (mulL (powL (gL 55) 2) wL) ^ 3 := by decide +kernel

/-- `HolderCert 55`. PROVED by exact rational arithmetic. -/
theorem holderCert55 : HolderCert 55 := holderCert_of 55 cert55a cert55b

/-- `MuStar55Bounds`, μ_55/2 ≤ μ*_55 ≤ μ_55. PROVED outright. -/
theorem muStar55Bounds : LeanLab.RamareSaouter2003.Row59.MuStar55Bounds :=
  muStar55Bounds_of_cert holderCert55

/-- Table 1 row one, CONDITIONAL ON `Theorem4Fm` with T0 = 3.3e9 and `Lemma1Upper`. -/
theorem theorem2At1e20_of_thm4 {NT : ℝ → ℝ} (h4 : Theorem4Fm NT 3300000000)
    (hN : LeanLab.RamareSaouter2003.Row1.Lemma1Upper NT) : Theorem2At1e20 :=
  LeanLab.RamareSaouter2003.Row1.theorem2At1e20_of h4 hN muStar48Bounds

/-- Table 1 row 59, CONDITIONAL ON `Theorem4Fm` with T0 = 3.3e9 and `Lemma1Upper`. -/
theorem theorem2_row59_of_thm4 {NT : ℝ → ℝ} (h4 : Theorem4Fm NT 3300000000)
    (hN : LeanLab.RamareSaouter2003.Row1.Lemma1Upper NT) : ∀ x : ℝ, Real.exp 59 ≤ x →
      ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 209257759) < p ∧ (p : ℝ) ≤ x :=
  LeanLab.RamareSaouter2003.Row59.theorem2_row59_of h4 hN muStar55Bounds

/-- Theorem 3, CONDITIONAL ON `Theorem4Fm`, `Lemma1Upper` and the Section 7 `ChainCert`. -/
theorem theorem3_of_thm4 {NT : ℝ → ℝ} (h4 : Theorem4Fm NT 3300000000)
    (hN : LeanLab.RamareSaouter2003.Row1.Lemma1Upper NT)
    (hc : ChainCert 10726905041 ((10 : ℝ) ^ 20) 28314000) :
    ∀ x : ℝ, 10726905041 < x →
      ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 28314000) < p ∧ (p : ℝ) ≤ x :=
  theorem3_of_chain (theorem2At1e20_of_thm4 h4 hN) hc

end LeanLab.RamareSaouter2003.MuStar55Cert

#print axioms LeanLab.RamareSaouter2003.MuStar55Cert.holderCert55
#print axioms LeanLab.RamareSaouter2003.MuStar55Cert.muStar55Bounds
#print axioms LeanLab.RamareSaouter2003.MuStar55Cert.theorem2At1e20_of_thm4
#print axioms LeanLab.RamareSaouter2003.MuStar55Cert.theorem2_row59_of_thm4
#print axioms LeanLab.RamareSaouter2003.MuStar55Cert.theorem3_of_thm4
