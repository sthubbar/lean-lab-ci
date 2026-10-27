/-
P0028, https://arxiv.org/abs/1610.02017, Lemma 4.3, pages 9 and 10.
A finite frequency net supplies the averaging set and all four local conclusions.
The uniform covering input is explicit here and proved in MMSLargeSpectrum.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSRealBohr
import LeanLab.Ternary.MMSLemma43Model
open Finset
namespace LeanLab.Ternary.MMS

theorem phase_control_of_frequency_net {N : ℕ} {δ : ℝ} (hN : 0 < N) (hδ : 0 ≤ δ)
    (R : Finset ℝ) (T : Set ℝ) (B : Finset ℤ)
    (hb : ∀ b ∈ B, 0 ≤ (b : ℝ) ∧ (b : ℝ) ≤ δ / 2 * N)
    (hphase : ∀ r ∈ R, ∀ b ∈ B, ∃ t : ℤ, |(b : ℝ) * r - t| ≤ δ / 60)
    (hnet : ∀ γ ∈ T, ∃ r ∈ R, ∃ k : ℤ, |γ - r - k| ≤ 1 / (30 * N)) :
    ∀ γ ∈ T, ∀ b ∈ B, ∃ t : ℤ, |(b : ℝ) * γ - t| ≤ δ / 30 := by
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  intro γ hγ b hbB
  obtain ⟨r, hr, k, hk⟩ := hnet γ hγ
  obtain ⟨t, ht⟩ := hphase r hr b hbB
  refine ⟨t + b * k, ?_⟩
  have he : (b : ℝ) * γ - ((t + b * k : ℤ) : ℝ) =
      ((b : ℝ) * r - t) + (b : ℝ) * (γ - r - k) := by
    push_cast
    ring
  have herr : |(b : ℝ) * (γ - r - k)| ≤ δ / 60 := by
    rw [abs_mul, abs_of_nonneg (hb b hbB).1]
    calc (b : ℝ) * |γ - r - k| ≤ (δ / 2 * N) * (1 / (30 * N)) :=
        mul_le_mul (hb b hbB).2 hk (abs_nonneg _) (by positivity)
      _ = δ / 60 := by field_simp; ring
  rw [he]
  exact (abs_add_le _ _).trans (by linarith)

theorem exists_bohr_set_of_frequency_net (δ : ℝ) (hδ : 0 < δ) (k : ℕ) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ (N : ℕ), 0 < N → ∀ (R : Finset ℝ) (T : Set ℝ), R.card ≤ k →
      (∀ γ ∈ T, ∃ r ∈ R, ∃ t : ℤ, |γ - r - t| ≤ 1 / (30 * N)) →
      ∃ B : Finset ℤ, B.Nonempty ∧ κ * N ≤ B.card ∧
        (∀ a ∈ B, ∀ b ∈ B, |((a - b : ℤ) : ℝ)| ≤ δ * N) ∧
        ∀ γ ∈ T, ∀ b ∈ B, ∃ t : ℤ, |(b : ℝ) * γ - t| ≤ δ / 30 := by
  obtain ⟨κ, hκ, h⟩ := exists_bohr_set_of_finite_spectrum (δ / 2) (by positivity) k
  refine ⟨κ, hκ, ?_⟩
  intro N hN R T hR hnet
  obtain ⟨B, hB, hs, hb, hshort, hp⟩ := h N R hR
  refine ⟨B, hB, hs, ?_, ?_⟩
  · intro a ha b hbB
    have := hshort a ha b hbB
    have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
    nlinarith
  · apply phase_control_of_frequency_net hN hδ.le R T B
    · intro b hbB
      exact ⟨by exact_mod_cast (hb b hbB).1, (hb b hbB).2⟩
    · intro r hr b hbB
      obtain ⟨t, ht⟩ := hp r hr b hbB
      exact ⟨t, by convert ht using 1 <;> ring⟩
    · exact hnet

/-- CONDITIONAL ON a uniform finite covering of each large spectrum. -/
theorem lemma43_of_frequency_nets {ε K q δ : ℝ}
    (hε : 0 < ε) (hε1 : ε ≤ 1 / 6) (hq : 0 ≤ q) (hδ : 0 < δ)
    (hnet : ∃ k : ℕ, ∀ η : ℝ, 0 < η → η < 1 → ∀ N : ℕ, 1 ≤ N → ∀ f : ℕ → ℝ,
      Prop31Hyp N η ε K q f → ∃ R : Finset ℝ, R.card ≤ k ∧
        ∀ γ : ℝ, δ * N ≤ ‖fhat N f γ‖ →
          ∃ r ∈ R, ∃ t : ℤ, |γ - r - t| ≤ 1 / (30 * N)) :
    ∃ C ≥ (0 : ℝ), ∀ η : ℝ, 0 < η → η < 1 → ∀ N : ℕ, 1 ≤ N → ∀ f : ℕ → ℝ,
      Prop31Hyp N η ε K q f → ∃ g h : ℤ →₀ ℝ, Lemma43Data N η ε K q δ C f g h := by
  obtain ⟨k, hk⟩ := hnet
  obtain ⟨κ, hκ, hB⟩ := exists_bohr_set_of_frequency_net δ hδ k
  refine ⟨1 / κ, by positivity, ?_⟩
  intro η hη hη1 N hN f hf
  obtain ⟨R, hR, hcover⟩ := hk η hη hη1 N hN f hf
  obtain ⟨B, hBne, hsize, hshort, hphase⟩ :=
    hB N (by omega) R {γ | δ * N ≤ ‖fhat N f γ‖} hR hcover
  exact ⟨intSmooth B (intervalLift N f), intervalLift N f - intSmooth B (intervalLift N f),
    lemma43Data_of_bohr hf hη.le hη1.le hε hε1 hq hδ.le B hBne hκ hsize hshort hphase⟩
end LeanLab.Ternary.MMS
