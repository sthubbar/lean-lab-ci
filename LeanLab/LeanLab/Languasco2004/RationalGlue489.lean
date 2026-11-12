/-
Integral glue for PP1993 page 46 display 14 and page 47 display 15.
Source https://doi.org/10.1112/jlms/s2-47.1.41.
Only the finite Farey cover remains OPEN in this module.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.Languasco2004.LocalData489

namespace LeanLab.Languasco2004.RationalGlue489
open Finset Real MeasureTheory Decomp279b Decomp413a Decomp413b Decomp489b
noncomputable section

/-- Page 46 display 14: integration over two covering pieces costs at most
 twice a uniform mass bound. No disjointness hypothesis is needed. -/
theorem two_piece_mass_bound {α : Type*} [MeasurableSpace α] (μ : Measure α)
    {f : α → ℝ} {D A B : Set α} {V : ℝ}
    (hA : MeasurableSet A) (hfA : IntegrableOn f A μ) (hfB : IntegrableOn f B μ)
    (hf0 : ∀ x, 0 ≤ f x) (hcover : D ⊆ A ∪ B)
    (hVA : (∫ x in A, f x ∂μ) ≤ V) (hVB : (∫ x in B, f x ∂μ) ≤ V) :
    (∫ x in D, f x ∂μ) ≤ 2 * V := by
  have hfD := (hfA.union hfB).mono_set hcover
  have hDA : D ∩ A ⊆ A := Set.inter_subset_right
  have hDB : D \ A ⊆ B := by
    intro x hx
    exact (hcover hx.1).resolve_left hx.2
  have hleft := setIntegral_mono_set hfA (Filter.Eventually.of_forall hf0)
    (Filter.Eventually.of_forall hDA)
  have hright := setIntegral_mono_set hfB (Filter.Eventually.of_forall hf0)
    (Filter.Eventually.of_forall hDB)
  rw [← integral_inter_add_sdiff hA hfD]
  linarith

/-- Page 47 display 15: integrate the principal plus remainder square bound.
The integral is on the symmetric punctured envelope of the source Farey arc. -/
theorem arc_mass_from_parts (N Y H B : ℝ) (q a : ℕ) :
    (∫ t in puncturedEnvelope N Y H B q, ‖secondSum Y ((a : ℝ) / q + t)‖ ^ 2) ≤
      2 * (principalArcMass N Y H B q + remainderArcMass N Y H B q a) := by
  have hsub : puncturedEnvelope N Y H B q ⊆
      Set.Icc (-(1 / ((q : ℝ) * fareyOrder H))) (1 / ((q : ℝ) * fareyOrder H)) := Set.sdiff_subset
  have hS : IntegrableOn (fun t : ℝ => ‖secondSum Y ((a : ℝ) / q + t)‖ ^ 2)
      (puncturedEnvelope N Y H B q) volume := by
    refine (Continuous.integrableOn_Icc ?_).mono_set hsub
    unfold secondSum phase
    fun_prop
  have hP : IntegrableOn (fun t : ℝ => ‖rationalWeight q * secondModel Y t‖ ^ 2)
      (puncturedEnvelope N Y H B q) volume := by
    refine (Continuous.integrableOn_Icc ?_).mono_set hsub
    unfold secondModel phase
    fun_prop
  have hR : IntegrableOn (fun t : ℝ => ‖secondRemainder Y q a t‖ ^ 2)
      (puncturedEnvelope N Y H B q) volume := by
    refine (Continuous.integrableOn_Icc ?_).mono_set hsub
    unfold secondRemainder secondSum secondModel phase
    fun_prop
  have hpoint (t : ℝ) : ‖secondSum Y ((a : ℝ) / q + t)‖ ^ 2 ≤
      2 * (‖rationalWeight q * secondModel Y t‖ ^ 2 + ‖secondRemainder Y q a t‖ ^ 2) := by
    convert Decomp279b.norm_add_sq (rationalWeight q * secondModel Y t) (secondRemainder Y q a t) using 1
    congr 2
    unfold secondRemainder
    ring
  calc (∫ t in puncturedEnvelope N Y H B q, ‖secondSum Y ((a : ℝ) / q + t)‖ ^ 2) ≤
      ∫ t in puncturedEnvelope N Y H B q,
        2 * (‖rationalWeight q * secondModel Y t‖ ^ 2 + ‖secondRemainder Y q a t‖ ^ 2) :=
      integral_mono hS ((hP.add hR).const_mul 2) hpoint
    _ = _ := by rw [integral_const_mul, integral_add hP hR]; rfl

/-- LEAF. Page 46 before display 14: the local minor set has a cover by
at most two punctured rational envelopes. This is the finite Farey geometry
only, with no integral, character, zero count or prime estimate. -/
theorem farey_two_envelope_cover :
    ∃ N₀ : ℝ, ∀ N Y H B : ℝ, N₀ ≤ N → 0 < Y → 16 ≤ H → 0 ≤ B →
    ∀ ξ : ℝ, ∃ q₁ a₁ q₂ a₂ : ℕ,
      (1 ≤ q₁ ∧ (q₁ : ℝ) ≤ fareyOrder H ∧ 1 ≤ a₁ ∧ a₁ ≤ q₁ ∧ Nat.Coprime a₁ q₁) ∧
      (1 ≤ q₂ ∧ (q₂ : ℝ) ≤ fareyOrder H ∧ 1 ≤ a₂ ∧ a₂ ≤ q₂ ∧ Nat.Coprime a₂ q₂) ∧
      minorDomain N Y H B ∩ Set.Ioo (ξ - 1 / H) (ξ + 1 / H) ⊆
        {α : ℝ | α - (a₁ : ℝ) / q₁ ∈ puncturedEnvelope N Y H B q₁} ∪
        {α : ℝ | α - (a₂ : ℝ) / q₂ ∈ puncturedEnvelope N Y H B q₂} := by sorry

/-- Translation invariance for any measurable local rational envelope. -/
theorem envelope_translation (f : ℝ → ℝ) (c : ℝ) (S : Set ℝ) (hS : MeasurableSet S) :
    (∫ x in {x : ℝ | x - c ∈ S}, f x) = ∫ t in S, f (c + t) := by
  classical
  have hpre : MeasurableSet {x : ℝ | x - c ∈ S} := hS.preimage (by fun_prop)
  rw [← integral_indicator hpre, ← integral_indicator hS]
  have heq : (fun t : ℝ => ({x : ℝ | x - c ∈ S}.indicator f) (c + t)) =
      S.indicator (fun t => f (c + t)) := by
    funext t
    change (if c + t - c ∈ S then f (c + t) else 0) =
      (if t ∈ S then f (c + t) else 0)
    rw [add_sub_cancel_left]
  rw [← heq, integral_add_left_eq_self]

/-- The exact local integral reduction follows from the two envelope cover.
CONDITIONAL ON farey_two_envelope_cover. -/
theorem local_reduction_from_cover :
    ∃ N₀ : ℝ, ∀ N Y H B P R : ℝ, N₀ ≤ N → 0 < Y → 16 ≤ H → 0 ≤ B →
      0 ≤ P → 0 ≤ R →
      (∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ fareyOrder H → principalArcMass N Y H B q ≤ P) →
      (∀ q a : ℕ, 1 ≤ q → (q : ℝ) ≤ fareyOrder H →
        1 ≤ a → a ≤ q → Nat.Coprime a q → remainderArcMass N Y H B q a ≤ R) →
      ∀ ξ : ℝ, localMass N Y H B ξ ≤ 4 * (P + R) := by
  obtain ⟨N₀, hcover⟩ := farey_two_envelope_cover
  refine ⟨N₀, ?_⟩
  intro N Y H B P R hN hY hH hB hP0 hR0 hP hR ξ
  obtain ⟨q₁, a₁, q₂, a₂, h₁, h₂, hc⟩ := hcover N Y H B hN hY hH hB ξ
  have hmeas (q : ℕ) : MeasurableSet (puncturedEnvelope N Y H B q) := by
    unfold puncturedEnvelope
    apply MeasurableSet.diff measurableSet_Icc
    split_ifs <;> measurability
  have hbound (q a : ℕ) (hq : 1 ≤ q) (hqQ : (q : ℝ) ≤ fareyOrder H)
      (ha : 1 ≤ a) (haq : a ≤ q) (hcop : Nat.Coprime a q) :
      (∫ x in {x : ℝ | x - (a : ℝ) / q ∈ puncturedEnvelope N Y H B q}, ‖secondSum Y x‖ ^ 2)
        ≤ 2 * (P + R) := by
    rw [envelope_translation _ _ _ (hmeas q)]
    have ht := arc_mass_from_parts N Y H B q a
    have hp := hP q hq hqQ
    have hr := hR q a hq hqQ ha haq hcop
    linarith
  have hint (q a : ℕ) : IntegrableOn (fun x : ℝ => ‖secondSum Y x‖ ^ 2)
      {x : ℝ | x - (a : ℝ) / q ∈ puncturedEnvelope N Y H B q} volume := by
    have hsub : {x : ℝ | x - (a : ℝ) / q ∈ puncturedEnvelope N Y H B q} ⊆
        Set.Icc ((a : ℝ) / q - 1 / ((q : ℝ) * fareyOrder H))
          ((a : ℝ) / q + 1 / ((q : ℝ) * fareyOrder H)) := by
      intro x hx
      have hb := hx.1
      constructor <;> linarith [hb.1, hb.2]
    refine (Continuous.integrableOn_Icc ?_).mono_set hsub
    unfold secondSum phase
    fun_prop
  have hresult := two_piece_mass_bound volume
    ((hmeas q₁).preimage (by fun_prop : Measurable (fun x : ℝ => x - (a₁ : ℝ) / q₁)))
    (hint q₁ a₁) (hint q₂ a₂) (fun _ => sq_nonneg _) hc
    (hbound q₁ a₁ h₁.1 h₁.2.1 h₁.2.2.1 h₁.2.2.2.1 h₁.2.2.2.2)
    (hbound q₂ a₂ h₂.1 h₂.2.1 h₂.2.2.1 h₂.2.2.2.1 h₂.2.2.2.2)
  calc localMass N Y H B ξ ≤ 2 * (2 * (P + R)) := hresult
    _ = 4 * (P + R) := by ring

#print axioms two_piece_mass_bound
#print axioms arc_mass_from_parts
#print axioms farey_two_envelope_cover
#print axioms envelope_translation
#print axioms local_reduction_from_cover
end
end LeanLab.Languasco2004.RationalGlue489
