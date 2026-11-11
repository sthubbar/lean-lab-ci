import LeanLab.ExceptionalSet.Decomp483e
import LeanLab.ExceptionalSet.Decomp483c
import LeanLab.ExceptionalSet.Decomp483d

/-!
P0082 page369 displays37 to39, finite strip cover bookkeeping.
The geometric implication is separate from the analytic localization theorem.
The final shifted moment reduction is CONDITIONAL ON its displayed phase and prime inputs.
AI wrote the Lean code. Binary Goldbach is open.
-/
namespace LeanLab.ExceptionalSet.Decomp483f
open Real MeasureTheory Set Finset

/-- P0082 page369 display39. A nonnegative weight bounded by B has
mass at most twice r times B on any translated strip section of radius r. -/
theorem strip_mass_le (A : Set ℝ) (g : ℝ → ℝ) (hg0 : ∀ y, 0 ≤ g y)
    (x d r B : ℝ) (hr : 0 ≤ r) (hB : 0 ≤ B) (hgb : ∀ y ∈ A, g y ≤ B) :
    (∫ y in A ∩ {y : ℝ | |y - x - d| ≤ r}, g y) ≤ 2 * r * B := by
  have hsub : A ∩ {y : ℝ | |y - x - d| ≤ r} ⊆ Icc (x + d - r) (x + d + r) := by
    intro y hy
    have hh := abs_le.mp (show |y - x - d| ≤ r from hy.2)
    constructor <;> linarith
  have hi : IntegrableOn (fun _ : ℝ => B) (Icc (x + d - r) (x + d + r)) :=
    integrableOn_const (by simp)
  calc
    _ ≤ ∫ y in A ∩ {y : ℝ | |y - x - d| ≤ r}, B :=
      setIntegral_mono_of_nonneg (fun y _ => hg0 y) (fun y hy => hgb y hy.1) (hi.mono_set hsub)
    _ ≤ ∫ y in Icc (x + d - r) (x + d + r), B :=
      setIntegral_mono_set hi (Filter.Eventually.of_forall (fun _ => hB)) hsub.eventuallySubset
    _ = _ := by
      rw [setIntegral_const]
      simp only [Measure.real, Real.volume_Icc, smul_eq_mul]
      rw [ENNReal.toReal_ofReal (by linarith : 0 ≤ x + d + r - (x + d - r))]
      ring

/-- P0082 page369 displays37 to39, elementary finite cover step.
Outside finitely many translated strips H is at most Q. Inside them the
uniform bound T and the strip length give the second contribution. -/
theorem finite_strip_cover_integral_le (A : Set ℝ) (g : ℝ → ℝ) (H : ℝ → ℝ → ℝ)
    (hg : IntegrableOn g A) (hg0 : ∀ x, 0 ≤ g x) (hH0 : ∀ x y, 0 ≤ H x y)
    (S : Finset ℤ) (c : ℤ → ℝ) (r B T Q : ℝ)
    (hr : 0 ≤ r) (hB : 0 ≤ B) (hT : 0 ≤ T) (hQ : 0 ≤ Q)
    (hgb : ∀ x ∈ A, g x ≤ B) (hH : ∀ x ∈ A, ∀ y ∈ A, H x y ≤ T)
    (hcover : ∀ x ∈ A, ∀ y ∈ A, Q < H x y → ∃ h ∈ S, |y - x - c h| ≤ r) :
    (∫ x in A, ∫ y in A, g x * g y * H x y) ≤
      Q * (∫ x in A, g x) ^ 2 +
        2 * r * B * T * (S.card : ℝ) * (∫ x in A, g x) := by
  classical
  let M := ∫ x in A, g x
  have hi (x : ℝ) (hx : x ∈ A) :
      (∫ y in A, g x * g y * H x y) ≤
        (Q * M + 2 * r * B * T * (S.card : ℝ)) * g x := by
    let strip := fun h : ℤ => {y : ℝ | |y - x - c h| ≤ r}
    let R := fun y : ℝ => g x * Q * g y +
      ∑ h ∈ S, (strip h).indicator (fun y => g x * T * g y) y
    have hstrip (h : ℤ) : MeasurableSet (strip h) :=
      measurableSet_le ((measurable_id.sub measurable_const).sub measurable_const).abs measurable_const
    have ht (h : ℤ) : IntegrableOn ((strip h).indicator (fun y => g x * T * g y)) A :=
      (hg.const_mul (g x * T)).indicator (hstrip h)
    have hR : IntegrableOn R A :=
      (hg.const_mul (g x * Q)).add (integrable_finsetSum S (fun h _ => ht h))
    have ht0 (h : ℤ) (y : ℝ) :
        0 ≤ (strip h).indicator (fun y => g x * T * g y) y := by
      by_cases hm : y ∈ strip h
      · rw [Set.indicator_of_mem hm]
        exact mul_nonneg (mul_nonneg (hg0 x) hT) (hg0 y)
      · simp [hm]
    have hpoint (y : ℝ) (hy : y ∈ A) : g x * g y * H x y ≤ R y := by
      dsimp only [R]
      have hbase : 0 ≤ g x * Q * g y := mul_nonneg (mul_nonneg (hg0 x) hQ) (hg0 y)
      have hsum0 : 0 ≤ ∑ h ∈ S, (strip h).indicator (fun y => g x * T * g y) y :=
        sum_nonneg (fun h _ => ht0 h y)
      by_cases hsmall : H x y ≤ Q
      · have hb : g x * g y * H x y ≤ g x * Q * g y := by
          nlinarith only [mul_le_mul_of_nonneg_left hsmall (mul_nonneg (hg0 x) (hg0 y))]
        exact hb.trans (le_add_of_nonneg_right hsum0)
      · obtain ⟨h, hh, hnear⟩ := hcover x hx y hy (lt_of_not_ge hsmall)
        have hm : y ∈ strip h := hnear
        have hs := Finset.single_le_sum (fun k _ => ht0 k y) hh
        rw [Set.indicator_of_mem hm] at hs
        have hb : g x * g y * H x y ≤ g x * T * g y := by
          nlinarith only [mul_le_mul_of_nonneg_left (hH x hx y hy)
            (mul_nonneg (hg0 x) (hg0 y))]
        linarith only [hb, hs, hbase]
    have hterm (h : ℤ) :
        (∫ y in A, (strip h).indicator (fun y => g x * T * g y) y) ≤
          g x * T * (2 * r * B) := by
      rw [setIntegral_indicator (hstrip h), integral_const_mul]
      exact mul_le_mul_of_nonneg_left
        (strip_mass_le A g hg0 x (c h) r B hr hB hgb) (mul_nonneg (hg0 x) hT)
    have hsum : (∑ h ∈ S, ∫ y in A,
        (strip h).indicator (fun y => g x * T * g y) y) ≤
          (S.card : ℝ) * (g x * T * (2 * r * B)) := by
      simpa only [sum_const, nsmul_eq_mul] using sum_le_sum (fun h _ => hterm h)
    calc
      _ ≤ ∫ y in A, R y :=
        setIntegral_mono_of_nonneg
          (fun y _ => mul_nonneg (mul_nonneg (hg0 x) (hg0 y)) (hH0 x y)) hpoint hR
      _ = g x * Q * M + ∑ h ∈ S, ∫ y in A,
          (strip h).indicator (fun y => g x * T * g y) y := by
        dsimp only [R, M]
        rw [integral_add (hg.const_mul (g x * Q)) (integrable_finsetSum S (fun h _ => ht h)),
          integral_const_mul, integral_finsetSum S (fun h _ => ht h)]
      _ ≤ g x * Q * M + (S.card : ℝ) * (g x * T * (2 * r * B)) := add_le_add le_rfl hsum
      _ = _ := by ring
  calc
    _ ≤ ∫ x in A, (Q * M + 2 * r * B * T * (S.card : ℝ)) * g x := by
      apply setIntegral_mono_of_nonneg
      · intro x hx
        apply integral_nonneg
        intro y
        exact mul_nonneg (mul_nonneg (hg0 x) (hg0 y)) (hH0 x y)
      · exact hi
      · exact hg.const_mul _
    _ = _ := by rw [integral_const_mul]; dsimp only [M]; ring

/-- P0082 page369 displays37 to39. The shifted moment follows from
an explicit phase cover and a pointwise prime bound. CONDITIONAL ON those inputs. -/
theorem shifted_moment_from_cover (P X Δ : ℝ) (hX : 2 ≤ X) (hΔ : 0 < Δ) (hΔ1 : Δ < 1)
    (s : Finset ℕ) (v : ℕ → ℝ) (A : Set ℝ) (S : Finset ℤ) (r V Q : ℝ)
    (hr : 0 ≤ r) (hV : 0 ≤ V) (hQ : 0 ≤ Q)
    (hprime : ∀ α ∈ A, ‖LeanLab.ExceptionalSet.U1539.Sp P X α‖ ^ 2 ≤ V)
    (hcover : ∀ α ∈ A, ∀ β ∈ A,
      Q < ‖∑ n ∈ s, LeanLab.ExceptionalSet.U1539.eC ((β - α) * v n)‖ →
        ∃ h ∈ S, |β - α - (h : ℝ) / 2| ≤ r) :
    (∑ n ∈ s, ‖∫ α in A, OddTail467.integrand P X Δ (v n) α‖ ^ 2) ≤
      Q * (7 * (Real.log 4 * X * Real.log X) / Real.sqrt Δ) ^ 2 +
      2 * r * V * (s.card : ℝ) * (S.card : ℝ) *
        (7 * (Real.log 4 * X * Real.log X) / Real.sqrt Δ) := by
  let g := fun α : ℝ => ‖U1539.Sp P X α ^ 2 * OddKernel467.evenKernel Δ α‖
  let H := fun α β => ‖∑ n ∈ s, U1539.eC ((β - α) * v n)‖
  let M := ∫ α in A, g α
  have hg : Integrable g := by
    simpa only [g, OddTail467.integrand, norm_mul, U1539.norm_eC, mul_one] using
      (OddTail467.total_integrable P X Δ 0 hΔ hΔ1).norm
  have hg0 (α : ℝ) : 0 ≤ g α := norm_nonneg _
  have hH0 (α β : ℝ) : 0 ≤ H α β := norm_nonneg _
  have hk (α : ℝ) : ‖OddKernel467.evenKernel Δ α‖ ≤ 1 := by
    rw [OddTail467.norm_evenKernel]
    have h := KernelTail385.kernel_abs_le_two_sub Δ ((1 / 2) * α) hΔ hΔ1
    linarith
  have hgb (α : ℝ) (hα : α ∈ A) : g α ≤ V := by
    calc
      _ = ‖U1539.Sp P X α‖ ^ 2 * ‖OddKernel467.evenKernel Δ α‖ := by
        simp only [g, norm_mul, norm_pow]
      _ ≤ ‖U1539.Sp P X α‖ ^ 2 := mul_le_of_le_one_right (sq_nonneg _) (hk α)
      _ ≤ _ := hprime α hα
  have hHb (α : ℝ) (_ : α ∈ A) (β : ℝ) (_ : β ∈ A) : H α β ≤ (s.card : ℝ) :=
    Fejer467.phase_sum_norm_le_card s v (β - α)
  have hgeo := finite_strip_cover_integral_le A g H hg.integrableOn hg0 hH0 S
    (fun h : ℤ => (h : ℝ) / 2) r V (s.card : ℝ) Q hr hV (Nat.cast_nonneg _) hQ
    hgb hHb hcover
  have hmass : M ≤ 7 * (Real.log 4 * X * Real.log X) / Real.sqrt Δ :=
    (setIntegral_le_integral hg (Filter.Eventually.of_forall hg0)).trans
      (Decomp483d.shifted_weighted_mass_sqrt P X Δ hX hΔ hΔ1)
  have hM0 : 0 ≤ M := integral_nonneg hg0
  obtain ⟨hgi, hgram⟩ := Decomp483c.shifted_moment_gram_bound P X Δ hΔ hΔ1 s v A
  calc
    _ ≤ ∫ z : ℝ × ℝ, g z.1 * g z.2 * H z.1 z.2
        ∂(volume.restrict A).prod (volume.restrict A) := hgram
    _ = ∫ α in A, ∫ β in A, g α * g β * H α β := integral_prod _ hgi
    _ ≤ Q * M ^ 2 + 2 * r * V * (s.card : ℝ) * (S.card : ℝ) * M := hgeo
    _ ≤ _ := by gcongr

end LeanLab.ExceptionalSet.Decomp483f
