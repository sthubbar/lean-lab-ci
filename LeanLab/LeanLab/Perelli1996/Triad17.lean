import Mathlib
import LeanLab.Perelli1996.Statements
import LeanLab.Perelli1996.B.Sing
import LeanLab.ChenExplicit.Statements
import LeanLab.ChenExplicit.Reductions

namespace LeanLab.Perelli1996.Triad17
open Finset Real Filter Topology
open LeanLab.ChenExplicit LeanLab.Perelli1996 LeanLab.Perelli1996.B

lemma le_singF (m : ℕ) (p : {p : ℕ // p.Prime}) (hp2 : 2 < p.1) :
    1 - 1 / ((p.1 : ℝ) - 1) ^ 2 ≤ singF (2 * m) p := by
  unfold singF
  split_ifs with h
  · have hp_le : (3:ℝ) ≤ p.1 := by exact_mod_cast hp2
    have hp_sub : 0 < (p.1:ℝ) - 1 := by linarith
    have : 1 / ((p.1 : ℝ) - 1) ^ 2 ≥ 0 := by positivity
    have : 1 / ((p.1 : ℝ) - 1) ≥ 0 := by positivity
    linarith
  · exact le_rfl

lemma nonneg_singF (p : {p : ℕ // p.Prime}) (hp2 : 2 < p.1) :
    0 ≤ 1 - 1 / ((p.1 : ℝ) - 1) ^ 2 := by
  have hp_le : (3:ℝ) ≤ p.1 := by exact_mod_cast hp2
  have hp_sub : (2:ℝ) ≤ (p.1:ℝ) - 1 := by linarith
  have : 1 / ((p.1 : ℝ) - 1) ^ 2 ≤ 1 / 4 := by
    rw [div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  linarith

-- triad17_pos : 0 < Sing (2 * m) for m >= 1 from twinC_pos.
theorem triad17_pos (m : ℕ) (hm : 1 ≤ m) :
  0 < Sing (2 * m) := by
  have h1 : Even (2 * m) := even_two_mul m
  have h2 : 2 * m ≠ 0 := by omega
  have h3 : 1 ≤ Sing (2 * m) := one_le_sing h1 h2
  linarith

-- triad17_main : for every natural m >= 1, 2 * LeanLab.ChenExplicit.twinC <= LeanLab.Perelli1996.Sing (2 * m)
theorem triad17_main (m : ℕ) (hm : 1 ≤ m) :
  2 * twinC <= Sing (2 * m) := by
  have h_multi : Multipliable (singF (2 * m)) := sing_multipliable (by omega)
  have h_sing_eq : Sing (2 * m) = ∏' p, singF (2 * m) p := sing_eq (2 * m)

  have h_twinC_multi := twinC_multipliable

  have h_prod_sing := h_multi.hasProd
  have h_prod_twinC := h_twinC_multi.hasProd

  set two : {p : ℕ // p.Prime} := ⟨2, Nat.prime_two⟩

  have hdvd : two.1 ∣ 2 * m := dvd_mul_right 2 m
  have hf2 : singF (2 * m) two = 2 := by
    unfold singF
    have : (two.1 : ℝ) = 2 := rfl
    rw [if_pos hdvd, this]
    norm_num

  let f : {p : ℕ // p.Prime ∧ 2 < p} → ℝ := fun p => 1 - 1 / ((p : ℝ) - 1) ^ 2
  let g : {p : ℕ // p.Prime} → ℝ := singF (2 * m)

  let embed : {p : ℕ // p.Prime ∧ 2 < p} ↪ {p : ℕ // p.Prime} := ⟨fun p => ⟨p.1, p.2.1⟩, by
    intro a b hab
    apply Subtype.ext
    have h1 : (a.val : ℕ) = (b.val : ℕ) := by injection hab
    exact h1⟩

  have h_ge : ∀ T : Finset {p : ℕ // p.Prime ∧ 2 < p},
      2 * ∏ p ∈ T, f p ≤ ∏ p ∈ insert two (T.map embed), g p := by
    intro T
    have h_prod_eq : ∏ p ∈ insert two (T.map embed), g p = g two * ∏ p ∈ T.map embed, g p := by
      apply Finset.prod_insert
      intro h
      rw [Finset.mem_map] at h
      rcases h with ⟨p, _, hp⟩
      have : p.1 = 2 := by
        have h_eq : p.1 = two.1 := by
          have : embed p = two := hp
          injection this
        exact h_eq
      have hp2 := p.2.2
      omega
    rw [h_prod_eq]
    have hf2' : g two = 2 := hf2
    rw [hf2']
    apply mul_le_mul_of_nonneg_left
    · rw [Finset.prod_map]
      apply Finset.prod_le_prod₀
      · intro p _
        have hp2 := p.2.2
        exact nonneg_singF (embed p) hp2
      · intro p _
        have hp2 := p.2.2
        exact le_singF m (embed p) hp2
    · norm_num

  have h_map : Tendsto (fun T : Finset {p : ℕ // p.Prime ∧ 2 < p} => 2 * ∏ p ∈ T, f p) atTop (𝓝 (2 * twinC)) := by
    exact Tendsto.const_mul 2 h_prod_twinC

  have h_prod_sing' : Tendsto (fun S' : Finset {p : ℕ // p.Prime} => ∏ p ∈ S', g p) atTop (𝓝 (Sing (2 * m))) := by
    have h : Sing (2 * m) = ∏' (b : { p : ℕ // p.Prime }), g b := h_sing_eq
    rw [h]
    exact h_prod_sing

  have h_comp : Tendsto (fun T : Finset {p : ℕ // p.Prime ∧ 2 < p} => ∏ p ∈ insert two (T.map embed), g p) atTop (𝓝 (Sing (2 * m))) := by
    apply Tendsto.comp h_prod_sing'
    rw [tendsto_atTop_atTop]
    intro S'
    let S'_gt2 := S'.filter (fun p => 2 < p.1)
    let T : Finset {p : ℕ // p.Prime ∧ 2 < p} := S'_gt2.attach.map ⟨fun p => ⟨p.1.1, p.1.2, by
      have := p.2
      rw [Finset.mem_filter] at this
      exact this.2⟩, by
        intro a b hab
        apply Subtype.ext
        apply Subtype.ext
        have h1 : (a.val.val : ℕ) = (b.val.val : ℕ) := by injection hab
        exact h1⟩
    use T
    intro S_big hsub
    intro p hp
    have hp_cases : p.1 = 2 ∨ 2 < p.1 := by
      have : 2 ≤ p.1 := p.2.two_le
      omega
    cases hp_cases with
    | inl h_eq =>
      have : p = two := by
        apply Subtype.ext
        exact h_eq
      rw [this]
      apply Finset.mem_insert_self
    | inr h_gt =>
      apply Finset.mem_insert_of_mem
      rw [Finset.mem_map]
      use ⟨p.1, p.2, h_gt⟩
      refine ⟨?_, rfl⟩
      apply hsub
      rw [Finset.mem_map]
      use ⟨p, by
        rw [Finset.mem_filter]
        exact ⟨hp, h_gt⟩⟩
      refine ⟨Finset.mem_attach _ _, rfl⟩

  have h_le_lim : 0 ≤ Sing (2 * m) - 2 * twinC := by
    apply ge_of_tendsto (Tendsto.sub h_comp h_map)
    filter_upwards [Filter.univ_mem] with T _
    have h_le := h_ge T
    linarith

  linarith

end LeanLab.Perelli1996.Triad17
