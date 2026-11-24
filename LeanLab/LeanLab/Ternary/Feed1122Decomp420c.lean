/-
MMS https://arxiv.org/abs/1610.02017v2, pages 11 and 12.
Feed 1122 split of harman_reference_mean_enveloped in Decomp420c.
The sealed enveloped mean is reduced to the two weighted limit leaves of
Decomp571b, roughReferenceMean_limit and correctionReferenceMean_limit.
The Buchstab comparison with the notebook envelope is already proved in Decomp571a.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.Decomp420c
import LeanLab.Ternary.Decomp571b

namespace LeanLab.Ternary.MMS.Task420

/-- The sealed notebook envelope of Decomp420c is the local copy of Decomp571a.
MMS page 12 footnote 3. Both are the same three branch formula. -/
theorem buchstabEnvelope_eq_referenceEnvelope :
    buchstabEnvelope = Task571.referenceEnvelope := rfl

/-- The sealed triple integral is the ordered profile integral of the envelope.
MMS page 11 bottom display, with omega replaced by its upper envelope. -/
theorem buchstabEnvelopeIntegral_eq_profileIntegral :
    buchstabEnvelopeIntegral = Task571.profileIntegral Task571.referenceEnvelope := rfl

/-- The exact statement of harman_reference_mean_enveloped from the Decomp571b leaves.
MMS page 11 bottom Buchstab display, page 12 first paragraph and footnote 3.
CONDITIONAL ON Task571.roughReferenceMean_limit and
Task571.correctionReferenceMean_limit, through harman_reference_mean_enveloped_supply. -/
theorem harman_reference_mean_enveloped_of_leaves :
    ∃ αp : ℝ, 0 < αp ∧ αp ≤ 4 * buchstabEnvelope 4 + buchstabEnvelopeIntegral ∧
      ∀ δ : ℝ, 0 < δ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
        |Task379.referenceMean x - αp| ≤ δ := by
  rw [buchstabEnvelope_eq_referenceEnvelope, buchstabEnvelopeIntegral_eq_profileIntegral]
  exact Task571.harman_reference_mean_enveloped_supply

end LeanLab.Ternary.MMS.Task420
