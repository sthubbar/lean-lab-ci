/-
P0069, page 23. The reciprocal kernel sum in each character fiber.
AI wrote the Lean code. CODEX task165. Goldbach is open.
-/
import LeanLab.BHP1997.Spacing132

namespace LeanLab.BHP1997.KernelC165
open Classical Complex

/-- Page 23, fourth display. In a fixed character fiber the reciprocal
kernel sum is at most 10 log x. Reuse the proved real spacing estimate. -/
theorem character_kernel_le {q : ℕ}
    (S : Finset (ℝ × DirichletCharacter ℂ q)) (χ : DirichletCharacter ℂ q)
    {x T u : ℝ} (hx : 2 ≤ x) (hT : 0 ≤ T) (hTx : T ≤ x)
    (hspace : Thm4.WellSpaced S) (htimes : ∀ p ∈ S, |p.1| ≤ T)
    (hu : |u| ≤ 2 * T) :
    ∑ p ∈ S.filter (fun p => p.2 = χ), 1 / (1 + |p.1 - u|) ≤ 10 * Real.log x := by
  let P := S.filter (fun p => p.2 = χ)
  let X := P.image Prod.fst
  have hinj : Set.InjOn Prod.fst (P : Set (ℝ × DirichletCharacter ℂ q)) := by
    intro p hp r hr heq
    apply Prod.ext heq
    exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hr).2.symm
  have hXspace : ∀ t ∈ X, ∀ v ∈ X, t ≠ v → 1 ≤ |t - v| := by
    intro t ht v hv hne
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hv
    apply hspace p (Finset.mem_filter.mp hp).1 r (Finset.mem_filter.mp hr).1
    · intro heq
      exact hne (congrArg Prod.fst heq)
    · exact (Finset.mem_filter.mp hp).2.trans (Finset.mem_filter.mp hr).2.symm
  have hXtimes : ∀ t ∈ X, |t| ≤ T := by
    intro t ht
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp ht
    exact htimes p (Finset.mem_filter.mp hp).1
  have hh := Spacing132.kernel_le_ten_log X hx hT hTx hXspace hXtimes hu
  simpa only [X, Finset.sum_image hinj] using hh

/-- Page 23, fourth and fifth displays. The weighted integrals of any
continuous nonnegative family are at most 10 log x times its unweighted
integrals over all characters. This is the finite sum and integral step. -/
theorem weighted_kernel_integral {q : ℕ}
    (S : Finset (ℝ × DirichletCharacter ℂ q))
    (f : DirichletCharacter ℂ q → ℝ → ℝ)
    (hf : ∀ χ, Continuous (f χ)) (hf0 : ∀ χ u, 0 ≤ f χ u)
    {x T : ℝ} (hx : 2 ≤ x) (hT : 0 ≤ T) (hTx : T ≤ x)
    (hspace : Thm4.WellSpaced S) (htimes : ∀ p ∈ S, |p.1| ≤ T) :
    (∑ p ∈ S, ∫ u in (-2 * T)..(2 * T), f p.2 u / (1 + |p.1 - u|)) ≤
      10 * Real.log x * ∑ χ : DirichletCharacter ℂ q,
        ∫ u in (-2 * T)..(2 * T), f χ u := by
  have hc (p : ℝ × DirichletCharacter ℂ q) :
      Continuous (fun u : ℝ => f p.2 u / (1 + |p.1 - u|)) := by
    apply (hf p.2).div
      (continuous_const.add (continuous_const.sub continuous_id).abs)
    intro u
    change (1 : ℝ) + |p.1 - u| ≠ 0
    positivity
  have hsum : Continuous (fun u : ℝ => ∑ p ∈ S, f p.2 u / (1 + |p.1 - u|)) :=
    continuous_finsetSum S (fun p _ => hc p)
  have hsumf : Continuous (fun u : ℝ => 10 * Real.log x *
      ∑ χ : DirichletCharacter ℂ q, f χ u) :=
    continuous_const.mul (continuous_finsetSum _ (fun χ _ => hf χ))
  rw [← intervalIntegral.integral_finsetSum (fun p _ => (hc p).intervalIntegrable _ _)]
  calc
    (∫ u in (-2 * T)..(2 * T), ∑ p ∈ S, f p.2 u / (1 + |p.1 - u|)) ≤
        ∫ u in (-2 * T)..(2 * T),
          10 * Real.log x * ∑ χ : DirichletCharacter ℂ q, f χ u := by
      apply intervalIntegral.integral_mono_on (by linarith)
        (hsum.intervalIntegrable _ _) (hsumf.intervalIntegrable _ _)
      intro u hu
      have hu' : |u| ≤ 2 * T := abs_le.mpr ⟨by linarith [hu.1], hu.2⟩
      calc
        (∑ p ∈ S, f p.2 u / (1 + |p.1 - u|)) =
            ∑ χ : DirichletCharacter ℂ q,
              ∑ p ∈ S.filter (fun p => p.2 = χ),
                f p.2 u / (1 + |p.1 - u|) :=
          (Finset.sum_fiberwise S Prod.snd _).symm
        _ = ∑ χ : DirichletCharacter ℂ q,
            f χ u * ∑ p ∈ S.filter (fun p => p.2 = χ), 1 / (1 + |p.1 - u|) := by
          apply Finset.sum_congr rfl
          intro χ hχ
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro p hp
          rw [(Finset.mem_filter.mp hp).2]
          ring
        _ ≤ ∑ χ : DirichletCharacter ℂ q, f χ u * (10 * Real.log x) := by
          apply Finset.sum_le_sum
          intro χ hχ
          exact mul_le_mul_of_nonneg_left
            (character_kernel_le S χ hx hT hTx hspace htimes hu') (hf0 χ u)
        _ = 10 * Real.log x * ∑ χ : DirichletCharacter ℂ q, f χ u := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro χ hχ
          ring
    _ = _ := by
      rw [intervalIntegral.integral_const_mul,
        intervalIntegral.integral_finsetSum (fun χ _ => (hf χ).intervalIntegrable _ _)]

end LeanLab.BHP1997.KernelC165
