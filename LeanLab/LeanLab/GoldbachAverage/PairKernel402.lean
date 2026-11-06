import LeanLab.GoldbachAverage.Kernel402
import LeanLab.GoldbachAverage.ZeroSumsCore

/-!
BHMS, arXiv 1704.06103v2 page 18 final low zero displays.
Compact zero finiteness identifies the cutoff pair tsum with a finite double sum.
The proved reciprocal kernel and head count then give the low pair estimate.
AI wrote this Lean code. Goldbach is open.
-/

noncomputable section
namespace LeanLab.GoldbachAverage.PairKernel402
open Finset
open LeanLab.PNTPort.Selberg LeanLab.PNTPort.ExplicitPsi1

/-- Bounded ordinate sets of nontrivial zeros are finite, as used on BHMS page 18. -/
theorem low_zeros_finite (T : ℝ) (hT : 0 ≤ T) :
    Set.Finite {ρ : NontrivialZero | |ρ.1.im| ≤ T} := by
  have hf := (zeros_rect_finite 2 T).preimage
    (f := fun ρ : NontrivialZero => ρ.1) Subtype.val_injective.injOn
  apply hf.subset
  intro ρ hρ
  refine ⟨(mem_rect (by norm_num : (-1 : ℝ) / 2 ≤ 2) hT).mpr ?_, ρ.2.1⟩
  exact ⟨⟨by linarith [ρ.2.2.1], by linarith [ρ.2.2.2]⟩, abs_le.mp hρ⟩

/-- The finite cutoff expansion of the reciprocal pair kernel on BHMS page 18. -/
theorem low_pair_sum_eq_finite (T : ℝ) (S : Finset NontrivialZero)
    (hS : ∀ ρ : NontrivialZero, ρ ∈ S ↔ |ρ.1.im| ≤ T) :
    (∑' ρ : NontrivialZero, ∑' σ : NontrivialZero,
      if |ρ.1.im| ≤ T ∧ |σ.1.im| ≤ T then
        (analyticOrderNatAt riemannZeta ρ.1 : ℝ) *
          (analyticOrderNatAt riemannZeta σ.1 : ℝ) / (1 + |ρ.1.im - σ.1.im|)
      else 0) =
    ∑ ρ ∈ S, ∑ σ ∈ S, mz ρ.1 * mz σ.1 / (1 + |ρ.1.im - σ.1.im|) := by
  rw [tsum_eq_sum (s := S) (fun ρ hρ => by
    have hn : ¬ |ρ.1.im| ≤ T := fun hh => hρ ((hS ρ).mpr hh)
    simp only [hn, false_and, ite_false, tsum_zero])]
  apply sum_congr rfl
  intro ρ hρ
  rw [tsum_eq_sum (s := S) (fun σ hσ => by
    have hn : ¬ |σ.1.im| ≤ T := fun hh => hσ ((hS σ).mpr hh)
    simp only [hn, and_false, ite_false])]
  apply sum_congr rfl
  intro σ hσ
  rw [if_pos ⟨(hS ρ).mp hρ, (hS σ).mp hσ⟩]
  rfl

/-- The low zero pair count of BHMS page 18, with log to the fourth replacing log cubed.
The sums are over the actual nontrivial zeros and their actual multiplicities. -/
theorem low_pair_count_ts : ∃ C : ℝ, 0 ≤ C ∧
    ∀ x h : ℝ, 2 ≤ x → 2 ≤ h → h ≤ x →
      (∑' ρ : NontrivialZero, ∑' σ : NontrivialZero,
        if |ρ.1.im| ≤ x / h ∧ |σ.1.im| ≤ x / h then
          (analyticOrderNatAt riemannZeta ρ.1 : ℝ) *
            (analyticOrderNatAt riemannZeta σ.1 : ℝ) / (1 + |ρ.1.im - σ.1.im|)
        else 0) ≤ C * (x / h) * Real.log x ^ 4 := by
  classical
  obtain ⟨C, hC, hc⟩ := Kernel402.finite_low_pair_count
  refine ⟨C, hC, ?_⟩
  intro x h hx hh hhx
  have hT : 0 ≤ x / h := by positivity
  let S := (low_zeros_finite (x / h) hT).toFinset
  have hS (ρ : NontrivialZero) : ρ ∈ S ↔ |ρ.1.im| ≤ x / h :=
    Set.Finite.mem_toFinset _
  rw [low_pair_sum_eq_finite (x / h) S hS]
  have hb := hc x h hx hh hhx (S.image (fun ρ => ρ.1)) (by
    intro ρ hρ
    obtain ⟨σ, hσ, rfl⟩ := mem_image.mp hρ
    exact ⟨σ.2, (hS σ).mp hσ⟩)
  unfold NontrivialZero at *
  have he : (∑ ρ ∈ S.image (fun ρ => ρ.1), ∑ σ ∈ S.image (fun σ => σ.1),
      mz ρ * mz σ / (1 + |ρ.im - σ.im|)) =
      ∑ ρ ∈ S, ∑ σ ∈ S, mz ρ.1 * mz σ.1 / (1 + |ρ.1.im - σ.1.im|) := by
    rw [sum_image Subtype.val_injective.injOn]
    apply sum_congr rfl
    intro ρ _
    exact sum_image Subtype.val_injective.injOn
  rw [he] at hb
  exact hb

end LeanLab.GoldbachAverage.PairKernel402
