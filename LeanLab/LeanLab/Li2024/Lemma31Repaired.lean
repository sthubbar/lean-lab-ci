/-
T1, unit U-1135, PC run 20261020T0003Z-10609. P0027 R. Li, On Chen's theorem, Goldbach's conjecture
and almost prime twins II, arXiv 2405.05727 v4 and Mathematical Reports 2026, Lemma 3.1, which is Wu
2008 Lemma 2.2 at κ₁ = 1/11.49, κ₂ = 1/6.18, read 2026-10-19, see FINDINGS F-0051.
Li's parameters satisfy Wu's hypotheses, `li_admissible`, so the lab's Wu08Sum.lemma22_wuA gives Li's
Lemma 3.1 with S₁₅'s range repaired to p₄ < N^{1/2−3/11.49}, for Wu's A = {N − p}, with the
explicit error 4N/(N^κ₁ − 1): `lemma31_repaired`. This is the repaired Lemma 3.1 that F-0051's
estimate D₁,₂(N) ≥ about 1.8935 Θ(N) starts from; the integral evaluation is not in Lean.
Plain math twin: as Wu2008Lemma22Err.lean lemma22_wuA with κ₁ = 100/1149, κ₂ = 100/618.
KNOWN mathematics. Binary Goldbach is OPEN.
AI-written Lean code, Claude, 2026-10-20. Checked only by the Lean kernel.
-/
import LeanLab.ChenDoubleSieve.Wu2008Lemma22Err

namespace LeanLab.Li2024.Lemma31
open LeanLab.ChenDoubleSieve.Wu08Sum LeanLab.ChenDoubleSieve.Wu08Real

noncomputable section

def lk1 : ℝ := 100 / 1149
def lk2 : ℝ := 100 / 618

theorem li_admissible : Admissible lk1 lk2 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp only [lk1, lk2] <;> norm_num

/-- **Li 2024 Lemma 3.1, S₁₅'s range repaired, Wu's `A = {N − p}`, explicit error.** -/
theorem lemma31_repaired (N : ℕ) (hN : 1 < N) (hNk : 1 < (N : ℝ) ^ lk1) :
    (3 * Y1 (wuA N) N lk1 + Y2 (wuA N) N lk2 + Y5 (wuA N) N lk1 lk2 + Y6 (wuA N) N lk1 lk2 : ℝ)
      - Y3 (wuA N) N lk1 - Y4 (wuA N) N lk1 - 2 * Y7 (wuA N) N lk1 - Y8 (wuA N) N lk1
      - Y9 (wuA N) N lk1 lk2 - Y10 (wuA N) N lk1 lk2 - Y11 (wuA N) N lk1 lk2
      ≤ 4 * D12 (wuA N) + 4 * (N / ((N : ℝ) ^ lk1 - 1)) :=
  lemma22_wuA N lk1 lk2 li_admissible hN hNk

end

end LeanLab.Li2024.Lemma31

#print axioms LeanLab.Li2024.Lemma31.li_admissible
#print axioms LeanLab.Li2024.Lemma31.lemma31_repaired
