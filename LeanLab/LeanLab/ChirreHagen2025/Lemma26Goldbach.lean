/-
P0075 line, T2, unit U-6502, I-0010, CLOUD 20261020T1415Z-cloud44, 2026-10-20.
The 5.78 log² x chain of SmoothGoldbach.lean with the cited `Lemma26`, Chirre-Hagen's Lemma 2.6,
replaced by `TrudgianN`, Trudgian's published `N(T)` bound, through `lemma26_of_trudgian`.
Still CONDITIONAL ON RH, `ExplicitA`, `HadamardK`, `Ordinates14`, Schoenfeld's θ bound and the
4·10^18 even Goldbach check, as before. AI-written Lean code, Claude. Binary Goldbach is open.
-/
import LeanLab.ChirreHagen2025.SmoothGoldbach
import LeanLab.ChirreHagen2025.AlmostAll
import LeanLab.ChirreHagen2025.Lemma26Proof

namespace LeanLab.ChirreHagen2025
open SmoothT2

theorem goldbach_578_of_trudgian {ι : Type*} {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → ExplicitA γ Z δ)
    (hH : RiemannHypothesis → HadamardK γ) (h14 : Ordinates14 γ) (hN : Lemma26P.TrudgianN γ)
    (hEv : EvenGoldbachUpTo (4 * 10 ^ 18)) (hS : RiemannHypothesis → SchoenfeldTheta) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 5.78 * Real.log x ^ 2 :=
  goldbach_578_of_zeros hE hH h14 (Lemma26P.lemma26_of_trudgian hN) hEv hS

/-- `almost_all_smooth` of AlmostAll.lean with `Lemma26` replaced by `TrudgianN`. -/
theorem almost_all_of_trudgian {ι : Type*} {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → ExplicitA γ Z δ)
    (hH : HadamardK γ) (h14 : Ordinates14 γ) (hN : Lemma26P.TrudgianN γ)
    {X δ : ℝ} (hX : 5 * 10 ^ 17 ≤ X) (hδ : 0 < δ) (hδ13 : δ ≤ 1 / 10 ^ 13)
    (hs : δ * √X < 1) :
    MeasureTheory.volume.real {y | y ∈ Set.Ioc (X / 2) X ∧ NoPrimeIn δ y}
      ≤ 5.178 * Real.log (2.0001 / δ) ^ 2 / δ :=
  almost_all_smooth hE hH h14 (Lemma26P.lemma26_of_trudgian hN) hX hδ hδ13 hs

end LeanLab.ChirreHagen2025
