/-
P0075 line, T2, OPEN AUDIT U-1248, I-0010, PC 20261020T1503Z-30533, 2026-10-20, from U-6502 of CLOUD 20261020T1415Z-cloud44.
The 5.78 log² x chain of SmoothGoldbach.lean with the cited `Lemma26`, Chirre-Hagen's Lemma 2.6,
replaced by `HSWN`, the corrected N(T) bound of Hasanalizade-Shen-Wong arXiv 2107.06506, through `lemma26_of_hsw`, in place of Trudgian 2014, reported erroneous.
Still CONDITIONAL ON RH, `ExplicitA`, `HadamardK`, `Ordinates14`, Schoenfeld's θ bound and the
4·10^18 even Goldbach check, as before. AI-written Lean code, Claude. Binary Goldbach is open.
-/
import LeanLab.ChirreHagen2025.SmoothGoldbach
import LeanLab.ChirreHagen2025.AlmostAll
import LeanLab.ChirreHagen2025.Lemma26HSW

namespace LeanLab.ChirreHagen2025
open SmoothT2

theorem goldbach_578_of_hsw {ι : Type*} {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : RiemannHypothesis → ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → ExplicitA γ Z δ)
    (hH : RiemannHypothesis → HadamardK γ) (h14 : Ordinates14 γ) (hN : Lemma26H.HSWN γ)
    (hEv : EvenGoldbachUpTo (4 * 10 ^ 18)) (hS : RiemannHypothesis → SchoenfeldTheta) :
    RiemannHypothesis → ∀ x : ℝ, 3 ≤ x →
      ∃ n : ℕ, IsGoldbachNumber n ∧ x < n ∧ (n : ℝ) < x + 5.78 * Real.log x ^ 2 :=
  goldbach_578_of_zeros hE hH h14 (Lemma26H.lemma26_of_hsw hN) hEv hS

/-- `almost_all_smooth` of AlmostAll.lean with `Lemma26` replaced by `HSWN`. -/
theorem almost_all_of_hsw {ι : Type*} {γ : ι → ℝ} {Z : ℕ → Finset ι}
    (hE : ∀ δ, 0 < δ → δ ≤ 1 / 10 ^ 13 → ExplicitA γ Z δ)
    (hH : HadamardK γ) (h14 : Ordinates14 γ) (hN : Lemma26H.HSWN γ)
    {X δ : ℝ} (hX : 5 * 10 ^ 17 ≤ X) (hδ : 0 < δ) (hδ13 : δ ≤ 1 / 10 ^ 13)
    (hs : δ * √X < 1) :
    MeasureTheory.volume.real {y | y ∈ Set.Ioc (X / 2) X ∧ NoPrimeIn δ y}
      ≤ 5.178 * Real.log (2.0001 / δ) ^ 2 / δ :=
  almost_all_smooth hE hH h14 (Lemma26H.lemma26_of_hsw hN) hX hδ hδ13 hs

end LeanLab.ChirreHagen2025

