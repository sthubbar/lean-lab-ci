/-
P0028, https://arxiv.org/abs/1610.02017, Lemma 4.3, pages 8 to 10.
Assemble the four local conclusions from explicit averaging set hypotheses.
MMSLargeSpectrum supplies existence and size for a small density margin.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSBohrDensity
import LeanLab.Ternary.MMSBohrPhases
import LeanLab.Ternary.MMSSmallModel

namespace LeanLab.Ternary.MMS

/-- A fixed upper bound on N gives a fixed constant in the trivial decomposition. -/
theorem lemma43_bounded_model {N M : ℕ} {η ε K q δ : ℝ} {f : ℕ → ℝ}
    (hf : Prop31Hyp N η ε K q f) (hη : 0 ≤ η) (hε : 0 < ε)
    (hq : 0 < q) (hK : 0 ≤ K) (hδ : 0 ≤ δ) (hNM : N ≤ M) :
    Lemma43Data N η ε K q δ M f (intervalLift N f) 0 := by
  obtain ⟨he, hb, hu, hd, hgq, hhq⟩ := lemma43_trivial_model hf hη hε hq hK hδ
  refine ⟨he, ?_, hu, hd, hgq, hhq⟩
  intro n
  refine ⟨(hb n).1, (hb n).2.trans ?_⟩
  have hNM' : (N : ℝ) ≤ M := by exact_mod_cast hNM
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_right hNM' hη)

/-- The four conclusions of Lemma 4.3 follow from a large, short, phase controlled set. -/
theorem lemma43Data_of_bohr {N : ℕ} {η ε K q δ κ : ℝ} {f : ℕ → ℝ}
    (hf : Prop31Hyp N η ε K q f) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 6) (hq : 0 ≤ q) (hδ : 0 ≤ δ)
    (B : Finset ℤ) (hB : B.Nonempty) (hκ : 0 < κ)
    (hsize : κ * N ≤ B.card)
    (hshort : ∀ a ∈ B, ∀ b ∈ B, |((a - b : ℤ) : ℝ)| ≤ δ * N)
    (hphase : ∀ γ : ℝ, δ * N ≤ ‖fhat N f γ‖ →
      ∀ b ∈ B, ∃ k : ℤ, |(b : ℝ) * γ - k| ≤ δ / 30) :
    Lemma43Data N η ε K q δ (1 / κ) f
      (intSmooth B (intervalLift N f)) (intervalLift N f - intSmooth B (intervalLift N f)) := by
  refine ⟨by abel, prop31Hyp_smooth_bounds hf hη B hB κ hκ hsize,
    prop31Hyp_uniform_bound hf hη1 hδ B hB hphase,
    intSmooth_denseOnAPs hf.2.1 hη hε hε1 hδ B hB hshort, ?_, ?_⟩
  · exact (intSmooth_restriction_bounds B hB _ hq).1.trans
      (by simpa only [intLq_intervalLift] using hf.2.2.2)
  · exact (intSmooth_restriction_bounds B hB _ hq).2.trans
      (by simpa only [intLq_intervalLift] using hf.2.2.2)

end LeanLab.Ternary.MMS
