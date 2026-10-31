/-
P0038 Shao 2012, Proposition 3.2: f₁, f₂, f₃ from the units mod 15 to [0, 1] with sums F₁, F₂,
F₃ and F₁F₂ + F₂F₃ + F₃F₁ > 5(F₁ + F₂ + F₃); every x mod 15 is a₁ + a₂ + a₃ with units aᵢ,
f₁ a₁ f₂ a₂ f₃ a₃ > 0 and f₁ a₁ + f₂ a₂ + f₃ a₃ > 3/2. Sort the values; either some admissible
index triple gives Lemma 2.3 on the top-level sets, or the real part Prop32Real gives T ≤ 0.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0102Z-30056, unit U-0125.
-/
import LeanLab.DensityGoldbach.Prop32Real
import LeanLab.DensityGoldbach.Lemma23
import LeanLab.DensityGoldbach.Prop31Prime

open Finset

namespace LeanLab.DensityGoldbach.P32

lemma Bad_swap12 {x y z : ℕ → ℝ} (h : Bad x y z) : Bad y x z := by
  intro j₁ j₂ j₃ h₁ h₂ h₃ hc p₁ p₂ p₃
  have := h j₂ j₁ j₃ h₂ h₁ h₃ (by linarith) p₂ p₁ p₃
  linarith

lemma Bad_swap23 {x y z : ℕ → ℝ} (h : Bad x y z) : Bad x z y := by
  intro j₁ j₂ j₃ h₁ h₂ h₃ hc p₁ p₂ p₃
  have := h j₁ j₃ j₂ h₁ h₃ h₂ (by linarith) p₁ p₃ p₂
  linarith

/-- The real part without sorting the supports. -/
theorem real_any (x y z : ℕ → ℝ) (hgx : Good x) (hgy : Good y) (hgz : Good z)
    (hB : Bad x y z) (n₁ n₂ n₃ : ℕ) (hsx : Supp x n₁) (hsy : Supp y n₂) (hsz : Supp z n₃)
    (h₁ : n₁ ≤ 8) (h₂ : n₂ ≤ 8) (h₃ : n₃ ≤ 8)
    (hT : 0 < Tf (sum8 x) (sum8 y) (sum8 z)) : False := by
  by_cases g1 : n₁ ≤ n₂ ∧ n₂ ≤ n₃
  · exact real_main x y z hgx hgy hgz hB n₁ n₂ n₃ hsx hsy hsz g1.1 g1.2 h₃ hT
  by_cases g2 : n₁ ≤ n₃ ∧ n₃ ≤ n₂
  · exact real_main x z y hgx hgz hgy (Bad_swap23 hB) n₁ n₃ n₂ hsx hsz hsy g2.1 g2.2 h₂
      (by unfold Tf at hT ⊢; linarith)
  by_cases g3 : n₂ ≤ n₁ ∧ n₁ ≤ n₃
  · exact real_main y x z hgy hgx hgz (Bad_swap12 hB) n₂ n₁ n₃ hsy hsx hsz g3.1 g3.2 h₃
      (by unfold Tf at hT ⊢; linarith)
  by_cases g4 : n₂ ≤ n₃ ∧ n₃ ≤ n₁
  · exact real_main y z x hgy hgz hgx (Bad_swap23 (Bad_swap12 hB)) n₂ n₃ n₁ hsy hsz hsx
      g4.1 g4.2 h₁ (by unfold Tf at hT ⊢; linarith)
  by_cases g5 : n₃ ≤ n₁ ∧ n₁ ≤ n₂
  · exact real_main z x y hgz hgx hgy (Bad_swap12 (Bad_swap23 hB)) n₃ n₁ n₂ hsz hsx hsy
      g5.1 g5.2 h₂ (by unfold Tf at hT ⊢; linarith)
  have g6 : n₃ ≤ n₂ ∧ n₂ ≤ n₁ := by omega
  exact real_main z y x hgz hgy hgx (Bad_swap12 (Bad_swap23 (Bad_swap12 hB))) n₃ n₂ n₁
    hsz hsy hsx g6.1 g6.2 h₁ (by unfold Tf at hT ⊢; linarith)

lemma exists_supp {x : ℕ → ℝ} (hg : Good x) : ∃ n ≤ 8, Supp x n := by
  classical
  by_cases h : ∃ j, j < 8 ∧ x j ≤ 0
  · refine ⟨Nat.find h, (Nat.find_spec h).1.le, fun j hj => ⟨fun hp => ?_, fun hjn => ?_⟩⟩
    · by_contra hn
      push Not at hn
      have := hg.2 _ _ hn hj
      linarith [(Nat.find_spec h).2]
    · by_contra hn
      push Not at hn
      exact absurd (Nat.find_min' h ⟨hj, hn⟩) (by omega)
  · push Not at h
    exact ⟨8, le_rfl, fun j hj => ⟨fun _ => hj, fun _ => h j hj⟩⟩

lemma card_units15 : #(unitsMod 15) = 8 := by
  rw [unitsMod, card_filter]; rfl

/-- Sorting one function on the units mod 15. -/
lemma sorted15 (f : ZMod 15 → ℝ) (hf : ∀ a, 0 ≤ f a ∧ f a ≤ 1) :
    ∃ a : ℕ → ℝ, Good a ∧ sum8 a = ∑ u ∈ unitsMod 15, f u ∧
      ∀ j, j < 8 → j + 1 ≤ #((unitsMod 15).filter (fun u => a j ≤ f u)) := by
  obtain ⟨a, hb, hm, hs, hl⟩ := sort_seq (unitsMod 15) f hf
  rw [card_units15] at hb hm hs hl
  exact ⟨a, ⟨hb, hm⟩, by rw [sum8_eq, hs], hl⟩

end LeanLab.DensityGoldbach.P32

namespace LeanLab.DensityGoldbach

open P32 in
/-- **Shao Proposition 3.2.** -/
theorem shao_prop32 (f₁ f₂ f₃ : ZMod 15 → ℝ) (hf₁ : ∀ a, 0 ≤ f₁ a ∧ f₁ a ≤ 1)
    (hf₂ : ∀ a, 0 ≤ f₂ a ∧ f₂ a ≤ 1) (hf₃ : ∀ a, 0 ≤ f₃ a ∧ f₃ a ≤ 1)
    (h : 5 * ((∑ u ∈ unitsMod 15, f₁ u) + (∑ u ∈ unitsMod 15, f₂ u)
        + (∑ u ∈ unitsMod 15, f₃ u)) <
      (∑ u ∈ unitsMod 15, f₁ u) * (∑ u ∈ unitsMod 15, f₂ u)
        + (∑ u ∈ unitsMod 15, f₂ u) * (∑ u ∈ unitsMod 15, f₃ u)
        + (∑ u ∈ unitsMod 15, f₃ u) * (∑ u ∈ unitsMod 15, f₁ u))
    (x : ZMod 15) : ∃ a₁ ∈ unitsMod 15, ∃ a₂ ∈ unitsMod 15, ∃ a₃ ∈ unitsMod 15,
      x = a₁ + a₂ + a₃ ∧ 0 < f₁ a₁ * f₂ a₂ * f₃ a₃ ∧ 3 / 2 < f₁ a₁ + f₂ a₂ + f₃ a₃ := by
  obtain ⟨a, hga, hsa, hla⟩ := sorted15 f₁ hf₁
  obtain ⟨b, hgb, hsb, hlb⟩ := sorted15 f₂ hf₂
  obtain ⟨c, hgc, hsc, hlc⟩ := sorted15 f₃ hf₃
  by_cases hgood : ∃ j₁ j₂ j₃ : ℕ, j₁ < 8 ∧ j₂ < 8 ∧ j₃ < 8 ∧
      5 * ((j₁ + 1) + (j₂ + 1) + (j₃ + 1)) < (j₁ + 1) * (j₂ + 1) + (j₂ + 1) * (j₃ + 1)
        + (j₃ + 1) * (j₁ + 1) ∧
      0 < a j₁ ∧ 0 < b j₂ ∧ 0 < c j₃ ∧ 3 / 2 < a j₁ + b j₂ + c j₃
  · obtain ⟨j₁, j₂, j₃, h₁, h₂, h₃, hc, p₁, p₂, p₃, hsum⟩ := hgood
    obtain ⟨I, hI, hIc⟩ := exists_subset_card_eq (hla j₁ h₁)
    obtain ⟨J, hJ, hJc⟩ := exists_subset_card_eq (hlb j₂ h₂)
    obtain ⟨K, hK, hKc⟩ := exists_subset_card_eq (hlc j₃ h₃)
    have hIU : I ⊆ unitsMod 15 := hI.trans (filter_subset _ _)
    have hJU : J ⊆ unitsMod 15 := hJ.trans (filter_subset _ _)
    have hKU : K ⊆ unitsMod 15 := hK.trans (filter_subset _ _)
    obtain ⟨s, hs, t, ht, r, hr, e⟩ := shao_lemma23 I J K hIU hJU hKU
      (by rw [hIc, hJc, hKc]; exact hc) x
    have es := (mem_filter.1 (hI hs)).2
    have et := (mem_filter.1 (hJ ht)).2
    have er := (mem_filter.1 (hK hr)).2
    refine ⟨s, hIU hs, t, hJU ht, r, hKU hr, e.symm, ?_, by linarith⟩
    have : 0 < f₁ s := by linarith
    have : 0 < f₂ t := by linarith
    have : 0 < f₃ r := by linarith
    positivity
  · exfalso
    have hB : Bad a b c := by
      intro j₁ j₂ j₃ h₁ h₂ h₃ hc p₁ p₂ p₃
      by_contra hlt
      push Not at hlt
      exact hgood ⟨j₁, j₂, j₃, h₁, h₂, h₃, hc, p₁, p₂, p₃, hlt⟩
    obtain ⟨n₁, hn₁, hs₁⟩ := exists_supp hga
    obtain ⟨n₂, hn₂, hs₂⟩ := exists_supp hgb
    obtain ⟨n₃, hn₃, hs₃⟩ := exists_supp hgc
    exact real_any a b c hga hgb hgc hB n₁ n₂ n₃ hs₁ hs₂ hs₃ hn₁ hn₂ hn₃
      (by unfold Tf; rw [hsa, hsb, hsc]; linarith)

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.shao_prop32
