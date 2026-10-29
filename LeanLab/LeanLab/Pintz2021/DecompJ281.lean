/-
P0054 J. Pintz, "An approximate formula for Goldbach's problem with applications",
Riv. Mat. Univ. Parma 12 (2021), 181-199. Unit U-1581 decomposed, GEMINI task281.

AI-written Lean code, Gemini, 2026-10-28. Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Pintz2021.Audit168
import LeanLab.Pintz2021.Statements
import LeanLab.Pintz2021.Reduction3
import LeanLab.Pintz2021.Lemma1U1369
import LeanLab.Pintz2021.WeightedKernelsTask08
import LeanLab.Pintz2021.DifferenceTask53
import LeanLab.Pintz2021.State1581

namespace LeanLab.Pintz2021.DecompJ281

open Complex Finset Filter Topology
open LeanLab.Pintz2021.MinorArcs LeanLab.Pintz2021.Reduction3
open LeanLab.Pintz2021.State1581 LeanLab.Pintz2021.DifferenceTask53

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ### Modified singular series and U cutoff, (2.11) and (2.12) -/

/-- `c'(χ₁,χ₂,q,m) = φ(q)^{-2} c_{χ₁\overline{χ₂}χ₀,q}(-m) τ(\overline{χ₁}χ₀,q) \overline{τ(\overline{χ₂}χ₀,q)}`. -/
def cCoefPrime (z w : ExcPair) (q : ℕ) (m : ℕ) : ℂ :=
  ((Nat.totient q : ℂ) ^ 2)⁻¹ * cRam q (lift z q * (lift w q)⁻¹) (-(m : ℤ)) *
    tau q (lift z q)⁻¹ * starRingEnd ℂ (tau q (lift w q)⁻¹)

/-- The partial sums of `𝔖'`: `∑_{q ≤ Q, [r₁, r₂] ∣ q} c'(χ₁,χ₂,q,m)`. -/
def singPartialPrime (z w : ExcPair) (m Q : ℕ) : ℂ :=
  ∑ q ∈ (Icc 1 Q).filter (fun q => Nat.lcm z.r w.r ∣ q), cCoefPrime z w q m

/-- `R₁'(m) = ∫_{𝔐} |S(α)|² e(-mα) dα`, using `differenceR1`. -/
def R1majPrime (ε X P : ℝ) (m : ℕ) : ℂ :=
  differenceR1 (S (X1 ε X) X) (Lemma1U1369.majorArcs P (X / P))ᶜ m

/-- The main term of (2.11), with the discrete difference kernel `I'(ϱᵢ,ϱⱼ,m)`:
`∑_{i,j ∈ E} A(ϱᵢ)A(ϱⱼ) 𝔖'(χᵢ,χⱼ,m) I'(ϱᵢ,ϱⱼ,m)`. -/
def mainTermPrime (E : Set ExcPair) (Sg' : ExcPair → ExcPair → ℕ → ℂ) (ε X : ℝ) (m : ℕ) : ℂ :=
  ∑ᶠ (z) (_ : z ∈ E), ∑ᶠ (w) (_ : w ∈ E),
    ((mult z * mult w : ℕ) : ℂ) * (Asign z : ℂ) * (Asign w : ℂ) * Sg' z w m *
      WeightedKernelsTask08.weightedKernel (X1 ε X) X z.ρ w.ρ m true

/-- The cutoff function `U(χ₁, χ₂, m) = \max(r₁²/(r₁,r₂)², r₂²/(r₁,r₂)², r₁/(m,r₁), r₂/(m,r₂), \mathrm{cond}(χ₁\overline{χ₂}))`.
We evaluate the gcd for `m : ℕ`. -/
def UCutoff (z w : ExcPair) (m : ℕ) : ℝ :=
  max (max ((z.r : ℝ)^2 / (Nat.gcd z.r w.r : ℝ)^2) ((w.r : ℝ)^2 / (Nat.gcd z.r w.r : ℝ)^2))
    (max (max ((z.r : ℝ) / (Nat.gcd m z.r : ℝ)) ((w.r : ℝ) / (Nat.gcd m w.r : ℝ)))
      ((lift z (Nat.lcm z.r w.r) * (lift w (Nat.lcm z.r w.r))⁻¹).conductor : ℝ))


/-- The truncated main term of (2.12). -/
def mainTermTruncatedPrime (E : Set ExcPair) (Sg' : ExcPair → ExcPair → ℕ → ℂ) (ε X U : ℝ) (m : ℕ) : ℂ :=
  ∑ᶠ (z) (_ : z ∈ E ∧ |z.ρ.im| ≤ U), ∑ᶠ (w) (_ : w ∈ E ∧ |w.ρ.im| ≤ U),
    if UCutoff z w m ≤ U then
      ((mult z * mult w : ℕ) : ℂ) * (Asign z : ℂ) * (Asign w : ℂ) * Sg' z w m *
        WeightedKernelsTask08.weightedKernel (X1 ε X) X z.ρ w.ρ m true
    else 0

/-- LEAF P0054 page 8: The pole lies in the truncated subset if U is at least 0. -/
theorem pole_mem_truncated {H P X U : ℝ} (hU : 0 ≤ U) :
    pole ∈ excSet H (Real.sqrt X) P X ∧ |pole.ρ.im| ≤ U := by
  refine ⟨pole_mem_excSet H (Real.sqrt X) P X, ?_⟩
  simp [pole, hU]

/-- LEAF P0054 page 8: The pole is not truncated by any U at least 1. -/
theorem pole_not_truncated {m : ℕ} {U : ℝ} (hU : 1 ≤ U) :
    UCutoff pole pole m ≤ U := by
  have hc : (lift pole (Nat.lcm pole.r pole.r) *
      (lift pole (Nat.lcm pole.r pole.r))⁻¹).conductor = 1 := by
    rw [Audit168.lift_pole, inv_one, mul_one]
    change (1 : DirichletCharacter ℂ 1).conductor = 1
    exact DirichletCharacter.conductor_one
  simp only [UCutoff, hc]
  simpa [pole] using hU

/-- LEAF P0054 page 8: `cCoefPrime` for the pole is exactly `cCoef` for the pole, as the trivial character is real. -/
theorem cCoefPrime_pole (q m : ℕ) :
    cCoefPrime pole pole q m = cCoef pole pole q m := by
  have ht : tau q 1 = ((ArithmeticFunction.moebius q : ℤ) : ℂ) :=
    (Audit168.cRam_one q 1).trans (PrincipalSeriesTask99.gauss_principal q)
  simp only [cCoefPrime, cCoef, Audit168.lift_pole, inv_one, mul_one, ht, map_intCast]


/-- LEAF P0054 page 8 display 2.21: Theorem 1 display 2.21 is cited as a leaf. -/
theorem leaf_221 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c H0 C X0 : ℝ, 0 < c ∧ ∀ H X P0 : ℝ, Thm1Hyp ε H0 X0 H X P0 →
      ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
        (excSet H (Real.sqrt X) P X).Finite ∧
        ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
          (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ,
            Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) ∧
          ∀ m : ℕ, (m : ℝ) ≤ X →
            ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
              C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0)) := by sorry


/-- LEAF P0054 page 8 display 2.22: The difference between the full and truncated main terms is bounded by the additional error. -/
theorem leaf_truncation_error :
  ∃ C' : ℝ, 0 < C' ∧ ∀ H X P U ε : ℝ, ∀ Sg' : ExcPair → ExcPair → ℕ → ℂ, ∀ m : ℕ,
    ‖mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m -
     mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X U m‖ ≤
      C' * (Sing m * X * Real.log U / Real.sqrt U) := by sorry

/-- LEAF P0054 page 8 display 2.22: The combined error bound is derived from the main term bound and the truncation bound via triangle inequality. -/
theorem leaf_triangle_inequality {H X P U ε ε0 c C C' : ℝ} {m : ℕ} {Sg' : ExcPair → ExcPair → ℕ → ℂ}
    (h_bound1 : ‖R1majPrime ε X P m - mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m‖ ≤
      C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0)))
    (h_bound2 : ‖mainTermPrime (excSet H (Real.sqrt X) P X) Sg' ε X m - mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X U m‖ ≤
      C' * (Sing m * X * Real.log U / Real.sqrt U))
    (hU : U = Real.sqrt X) :
    ‖R1majPrime ε X P m - mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X U m‖ ≤
      max C C' * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0) + Sing m * X * Real.log U / (X ^ (1/4 : ℝ))) := by sorry

/-- Assembly theorem for 2.22, proved directly from the leaf. -/
theorem assembly_222 :
  ∃ ε0 : ℝ, 0 < ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε0 →
    ∃ c H0 C X0 : ℝ, 0 < c ∧ ∀ H X P0 : ℝ, Thm1Hyp ε H0 X0 H X P0 →
      ∃ P : ℝ, P0 * X ^ (-ε) ≤ P ∧ P ≤ P0 ∧
        (excSet H (Real.sqrt X) P X).Finite ∧
        ∃ Sg' : ExcPair → ExcPair → ℕ → ℂ,
          (∀ z ∈ excSet H (Real.sqrt X) P X, ∀ w ∈ excSet H (Real.sqrt X) P X, ∀ m : ℕ,
            Tendsto (singPartialPrime z w m) atTop (𝓝 (Sg' z w m))) ∧
          ∀ m : ℕ, X / 4 ≤ m ∧ (m : ℝ) ≤ X / 2 →
            ‖R1majPrime ε X P m - mainTermTruncatedPrime (excSet H (Real.sqrt X) P X) Sg' ε X (Real.sqrt X) m‖ ≤
              C * (Sing m * X * Real.exp (-(c * H)) + X ^ (1 - ε0) + Sing m * X * Real.log (Real.sqrt X) / (X ^ (1/4 : ℝ))) := by
  obtain ⟨ε0, hε0, h1⟩ := leaf_221
  obtain ⟨C', hC'pos, hC'⟩ := leaf_truncation_error
  refine ⟨ε0, hε0, ?_⟩
  intro ε hε hε0'
  obtain ⟨c, H0, C, X0, hc, h2⟩ := h1 ε hε hε0'
  refine ⟨c, H0, max C C', X0, hc, ?_⟩
  intro H X P0 hHyp
  obtain ⟨P, hP1, hP2, hFin, Sg', hSg1, hSg2⟩ := h2 H X P0 hHyp
  refine ⟨P, hP1, hP2, hFin, Sg', hSg1, ?_⟩
  intro m hm1
  have hm2 := hm1.2
  have h_bound1 := hSg2 m (by linarith)
  have h_bound2 := hC' H X P (Real.sqrt X) ε Sg' m
  exact leaf_triangle_inequality h_bound1 h_bound2 rfl

end
end LeanLab.Pintz2021.DecompJ281

#print axioms LeanLab.Pintz2021.DecompJ281.pole_not_truncated

#print axioms LeanLab.Pintz2021.DecompJ281.cCoefPrime_pole
