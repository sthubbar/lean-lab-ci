/-
The dense part of Shao Proposition 4.1.
Source: https://arxiv.org/abs/1206.6139v2 pages 14 to 15.
AI wrote the Lean code. Binary Goldbach is open.
-/
import Mathlib

open Finset
open scoped Classical

namespace LeanLab.DensityGoldbach.Counting408

/-- Shao page 14, the display bounding mass by the size of a superlevel set.
Mathlib sum_le_sum and sum_filter provide the finite sum steps. -/
theorem superlevel_mass {N : ℕ} [NeZero N] (g : ZMod N → ℝ) (B τ : ℝ)
    (hB : 0 ≤ B) (hτ : 0 ≤ τ) (hg : ∀ x, g x ≤ B / N) :
    (∑ x, g x) ≤ B *
      (((univ.filter (fun x : ZMod N => τ / N ≤ g x)).card : ℝ) / N) + τ := by
  have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
  have hpoint : ∀ x, g x ≤ (if τ / N ≤ g x then B / N else 0) + τ / N := by
    intro x
    split_ifs with h
    · exact (hg x).trans (le_add_of_nonneg_right (by positivity))
    · have : g x < τ / N := lt_of_not_ge h
      simpa using this.le
  calc
    (∑ x, g x) ≤ ∑ x : ZMod N, ((if τ / N ≤ g x then B / N else 0) + τ / N) :=
      sum_le_sum fun x _ => hpoint x
    _ = B * (((univ.filter (fun x : ZMod N => τ / N ≤ g x)).card : ℝ) / N) + τ := by
      rw [sum_add_distrib, ← sum_filter]
      simp only [sum_const, nsmul_eq_mul, card_univ, ZMod.card]
      field_simp
      <;> ring

/-- Shao page 15, the first display. With delta at most 1/8 and cap
1 + delta/10, the threshold delta squared leaves each density at least delta/2
and their sum at least 1 + delta/2. -/
theorem superlevel_densities (δ : ℝ) (hδ : 0 < δ) (hδsmall : δ ≤ 1 / 8)
    (mass density : Fin 3 → ℝ)
    (hmass : ∀ i, δ ≤ mass i)
    (htotal : 1 + δ ≤ mass 0 + mass 1 + mass 2)
    (hbound : ∀ i, mass i ≤ (1 + δ / 10) * density i + δ ^ 2) :
    (∀ i, δ / 2 ≤ density i) ∧ 1 + δ / 2 ≤ density 0 + density 1 + density 2 := by
  have hcap : 0 < 1 + δ / 10 := by positivity
  have hind : ∀ i, δ / 2 ≤ density i := by
    intro i
    have hsmall : δ ^ 2 ≤ δ / 8 := by nlinarith
    have hm := hmass i
    have hb := hbound i
    nlinarith
  refine ⟨hind, ?_⟩
  have hb0 := hbound 0
  have hb1 := hbound 1
  have hb2 := hbound 2
  have hsmall : δ ^ 2 ≤ δ / 8 := by nlinarith
  nlinarith

section

variable {N : ℕ} [NeZero N]

private theorem card_inter_ge (S Y : Finset (ZMod N)) :
    S.card + Y.card ≤ N + (S ∩ Y).card := by
  have h1 : (S ∪ Y).card + (S ∩ Y).card = S.card + Y.card := Finset.card_union_add_card_inter S Y
  have h2 : (S ∪ Y).card ≤ N := by
    have := Finset.card_le_univ (S ∪ Y)
    rwa [ZMod.card] at this
  omega

private theorem card_image_sub (x : ZMod N) (S : Finset (ZMod N)) :
    (S.image (fun u => x - u)).card = S.card := by
  apply Finset.card_image_of_injective
  intro a b h
  simpa using h

private theorem min_eq_card_filter (m k : ℕ) :
    min m k = ((Finset.Ico 1 (k + 1)).filter (fun t => t ≤ m)).card := by
  have he : (Finset.Ico 1 (k + 1)).filter (fun t => t ≤ m) = Finset.Icc 1 (min m k) := by
    ext t
    simp only [Finset.mem_filter, Finset.mem_Ico, Finset.mem_Icc]
    omega
  rw [he, Nat.card_Icc]
  omega

private theorem filter_reflect_eq (A B C : Finset (ZMod N)) (x : ZMod N) (t : ℕ) :
    (C.filter (fun w => t ≤ (A.filter (fun a => x - w - a ∈ B)).card))
      = C ∩ (univ.filter (fun u => t ≤ (A.filter (fun a => u - a ∈ B)).card)).image
          (fun u => x - u) := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_inter, Finset.mem_image, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hwC, hw⟩
    exact ⟨hwC, x - w, hw, by ring⟩
  · rintro ⟨hwC, u, hu, rfl⟩
    exact ⟨hwC, by simpa using hu⟩

private theorem triple_ge_levels (A B C : Finset (ZMod N)) (x : ZMod N) (k : ℕ) :
    (∑ w ∈ C, (A.filter (fun a => x - w - a ∈ B)).card)
      ≥ ∑ t ∈ Finset.Ico 1 (k + 1),
          ((univ.filter (fun u => t ≤ (A.filter (fun a => u - a ∈ B)).card)).card + C.card - N) := by
  have h1 : (∑ t ∈ Finset.Ico 1 (k + 1),
        (C.filter (fun w => t ≤ (A.filter (fun a => x - w - a ∈ B)).card)).card)
      ≤ (∑ w ∈ C, (A.filter (fun a => x - w - a ∈ B)).card) := by
    have hm : (∑ w ∈ C, min ((A.filter (fun a => x - w - a ∈ B)).card) k)
        ≤ (∑ w ∈ C, (A.filter (fun a => x - w - a ∈ B)).card) := by
      apply Finset.sum_le_sum
      intro w _
      exact Nat.min_le_left _ _
    have heq : (∑ w ∈ C, min ((A.filter (fun a => x - w - a ∈ B)).card) k)
        = ∑ t ∈ Finset.Ico 1 (k + 1),
            (C.filter (fun w => t ≤ (A.filter (fun a => x - w - a ∈ B)).card)).card := by
      have hpt : ∀ w : ZMod N, min ((A.filter (fun a => x - w - a ∈ B)).card) k
          = ∑ t ∈ Finset.Ico 1 (k + 1),
              (if t ≤ (A.filter (fun a => x - w - a ∈ B)).card then (1 : ℕ) else 0) := by
        intro w
        rw [min_eq_card_filter, Finset.card_filter]
      rw [Finset.sum_congr rfl (fun w _ => hpt w)]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro t _
      rw [Finset.card_filter]
    rw [← heq]
    exact hm
  have h2 : ∀ t ∈ Finset.Ico 1 (k + 1),
      ((univ.filter (fun u => t ≤ (A.filter (fun a => u - a ∈ B)).card)).card + C.card - N)
        ≤ (C.filter (fun w => t ≤ (A.filter (fun a => x - w - a ∈ B)).card)).card := by
    intro t _
    rw [filter_reflect_eq]
    have hcov := card_inter_ge C
      ((univ.filter (fun u => t ≤ (A.filter (fun a => u - a ∈ B)).card)).image (fun u => x - u))
    have hcard := card_image_sub x (univ.filter (fun u => t ≤ (A.filter (fun a => u - a ∈ B)).card))
    omega
  calc (∑ t ∈ Finset.Ico 1 (k + 1),
          ((univ.filter (fun u => t ≤ (A.filter (fun a => u - a ∈ B)).card)).card + C.card - N))
      ≤ (∑ t ∈ Finset.Ico 1 (k + 1),
          (C.filter (fun w => t ≤ (A.filter (fun a => x - w - a ∈ B)).card)).card) :=
        Finset.sum_le_sum h2
    _ ≤ (∑ w ∈ C, (A.filter (fun a => x - w - a ∈ B)).card) := h1

private theorem triple_filter_eq (A B C : Finset (ZMod N)) (x : ZMod N) :
    (univ.filter (fun yz : ZMod N × ZMod N =>
        yz.1 ∈ A ∧ yz.2 ∈ B ∧ x - yz.1 - yz.2 ∈ C))
      = (A.product B).filter (fun yz => x - yz.1 - yz.2 ∈ C) := by
  ext yz
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨hA, hB, hC⟩
    exact ⟨Finset.mem_product.mpr ⟨hA, hB⟩, hC⟩
  · rintro ⟨hAB, hC⟩
    obtain ⟨hA, hB⟩ := Finset.mem_product.mp hAB
    exact ⟨hA, hB, hC⟩

private theorem triple_card_swap (A B C : Finset (ZMod N)) (x : ZMod N) :
    ((A.product B).filter (fun yz => x - yz.1 - yz.2 ∈ C)).card
      = ((C.product A).filter (fun q => x - q.1 - q.2 ∈ B)).card := by
  refine Finset.card_bij (fun p _ => (x - p.1 - p.2, p.1)) ?_ ?_ ?_
  · intro p hp
    obtain ⟨hpAB, hpc⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpA, hpB⟩ := Finset.mem_product.mp hpAB
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hpc, hpA⟩, ?_⟩
    show x - (x - p.1 - p.2) - p.1 ∈ B
    rw [show x - (x - p.1 - p.2) - p.1 = p.2 by ring]
    exact hpB
  · intro p1 _ p2 _ h
    have h1 : p1.1 = p2.1 := congrArg Prod.snd h
    have h2 : x - p1.1 - p1.2 = x - p2.1 - p2.2 := congrArg Prod.fst h
    rw [h1] at h2
    have h3 : p1.2 = p2.2 := sub_right_inj.mp h2
    exact Prod.ext h1 h3
  · intro q hq
    obtain ⟨hqCA, hqb⟩ := Finset.mem_filter.mp hq
    obtain ⟨hqC, hqA⟩ := Finset.mem_product.mp hqCA
    refine ⟨(q.2, x - q.1 - q.2), ?_, ?_⟩
    · refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨hqA, hqb⟩, ?_⟩
      show x - q.2 - (x - q.1 - q.2) ∈ C
      rw [show x - q.2 - (x - q.1 - q.2) = q.1 by ring]
      exact hqC
    · show (x - q.2 - (x - q.1 - q.2), q.2) = q
      rw [show x - q.2 - (x - q.1 - q.2) = q.1 by ring]

private theorem triple_card_sum (A B C : Finset (ZMod N)) (x : ZMod N) :
    ((C.product A).filter (fun q => x - q.1 - q.2 ∈ B)).card
      = ∑ w ∈ C, (A.filter (fun a => x - w - a ∈ B)).card := by
  rw [Finset.card_filter]
  simp only [Finset.product_eq_sprod]
  rw [Finset.sum_product]
  apply Finset.sum_congr rfl
  intro w _
  rw [Finset.card_filter]

private theorem triple_eq_sum (A B C : Finset (ZMod N)) (x : ZMod N) :
    (univ.filter (fun yz : ZMod N × ZMod N =>
        yz.1 ∈ A ∧ yz.2 ∈ B ∧ x - yz.1 - yz.2 ∈ C)).card
      = ∑ w ∈ C, (A.filter (fun a => x - w - a ∈ B)).card := by
  rw [triple_filter_eq, triple_card_swap, triple_card_sum]

/-- Reflection gives the same representation count with the summands exchanged. -/
private theorem rep_card_swap {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B : Finset G) (x : G) :
    (A.filter (fun a => x - a ∈ B)).card =
      (B.filter (fun b => x - b ∈ A)).card := by
  classical
  refine Finset.card_bij (fun a _ => x - a) ?_ ?_ ?_
  · intro a ha
    rw [Finset.mem_filter] at ha ⊢
    exact ⟨ha.2, by simpa using ha.1⟩
  · intro a _ b _ hab
    have h := congrArg (fun y : G => x - y) hab
    simpa using h
  · intro b hb
    rw [Finset.mem_filter] at hb
    refine ⟨x - b, ?_, ?_⟩
    · rw [Finset.mem_filter]
      exact ⟨hb.2, by simpa using hb.1⟩
    · simp

/-- Filtering a disjoint union in the first summand adds representation counts. -/
private theorem rep_card_union_left {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A₁ A₂ B : Finset G) (x : G) (h : Disjoint A₁ A₂) :
    ((A₁ ∪ A₂).filter (fun a => x - a ∈ B)).card =
      (A₁.filter (fun a => x - a ∈ B)).card +
        (A₂.filter (fun a => x - a ∈ B)).card := by
  classical
  rw [Finset.filter_union, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter_filter h

/-- Filtering a disjoint union in the second summand adds representation counts. -/
private theorem rep_card_union_right {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B₁ B₂ : Finset G) (x : G) (h : Disjoint B₁ B₂) :
    (A.filter (fun a => x - a ∈ B₁ ∪ B₂)).card =
      (A.filter (fun a => x - a ∈ B₁)).card +
        (A.filter (fun a => x - a ∈ B₂)).card := by
  classical
  have hset : (A.filter (fun a => x - a ∈ B₁ ∪ B₂)) =
      (A.filter (fun a => x - a ∈ B₁)) ∪
        (A.filter (fun a => x - a ∈ B₂)) := by
    ext a
    simp only [Finset.mem_filter, Finset.mem_union]
    tauto
  rw [hset, Finset.card_union_of_disjoint]
  exact Finset.disjoint_filter.2 fun a _ h₁ h₂ => Finset.disjoint_left.mp h h₁ h₂

/-- Pollard's basic decomposition of the representation function. -/
private theorem rep_card_decompose {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B : Finset G) (x : G) :
    (A.filter (fun a => x - a ∈ B)).card =
      ((A \ B).filter (fun a => x - a ∈ B \ A)).card +
        ((A ∩ B).filter (fun a => x - a ∈ A ∪ B)).card := by
  classical
  have hA : A \ B ∪ A ∩ B = A := Finset.sdiff_union_inter _ _
  have hB : B \ A ∪ A ∩ B = B := by
    rw [Finset.inter_comm]
    exact Finset.sdiff_union_inter _ _
  have hAB : Disjoint (A \ B) (A ∩ B) := disjoint_sdiff_inter _ _
  have hBA : Disjoint (B \ A) (A ∩ B) := by
    rw [Finset.inter_comm]
    exact disjoint_sdiff_inter _ _
  have hBsplit (D : Finset G) :
      (D.filter (fun a => x - a ∈ B)).card =
        (D.filter (fun a => x - a ∈ B \ A)).card +
          (D.filter (fun a => x - a ∈ A ∩ B)).card := by
    calc
      (D.filter (fun a => x - a ∈ B)).card =
          (D.filter (fun a => x - a ∈ B \ A ∪ A ∩ B)).card := by rw [hB]
      _ = _ := rep_card_union_right D (B \ A) (A ∩ B) x hBA
  have hAsplit (D : Finset G) :
      (D.filter (fun a => x - a ∈ A)).card =
        (D.filter (fun a => x - a ∈ A \ B)).card +
          (D.filter (fun a => x - a ∈ A ∩ B)).card := by
    calc
      (D.filter (fun a => x - a ∈ A)).card =
          (D.filter (fun a => x - a ∈ A \ B ∪ A ∩ B)).card := by rw [hA]
      _ = _ := rep_card_union_right D (A \ B) (A ∩ B) x hAB
  have hU : B \ A ∪ A = A ∪ B := by
    ext y
    simp only [Finset.mem_union, Finset.mem_sdiff]
    tauto
  calc
    (A.filter (fun a => x - a ∈ B)).card =
        ((A \ B ∪ A ∩ B).filter (fun a => x - a ∈ B)).card := by rw [hA]
    _ = ((A \ B).filter (fun a => x - a ∈ B)).card +
        ((A ∩ B).filter (fun a => x - a ∈ B)).card :=
      rep_card_union_left (A \ B) (A ∩ B) B x hAB
    _ = (((A \ B).filter (fun a => x - a ∈ B \ A)).card +
        ((A \ B).filter (fun a => x - a ∈ A ∩ B)).card) +
        (((A ∩ B).filter (fun a => x - a ∈ B \ A)).card +
          ((A ∩ B).filter (fun a => x - a ∈ A ∩ B)).card) := by
      rw [hBsplit (A \ B), hBsplit (A ∩ B)]
    _ = ((A \ B).filter (fun a => x - a ∈ B \ A)).card +
        (((A ∩ B).filter (fun a => x - a ∈ B \ A)).card +
          (((A ∩ B).filter (fun a => x - a ∈ A \ B)).card +
            ((A ∩ B).filter (fun a => x - a ∈ A ∩ B)).card)) := by
      rw [rep_card_swap (A \ B) (A ∩ B) x]
      omega
    _ = ((A \ B).filter (fun a => x - a ∈ B \ A)).card +
        (((A ∩ B).filter (fun a => x - a ∈ B \ A)).card +
          ((A ∩ B).filter (fun a => x - a ∈ A)).card) := by
      rw [← hAsplit (A ∩ B)]
    _ = ((A \ B).filter (fun a => x - a ∈ B \ A)).card +
        ((A ∩ B).filter (fun a => x - a ∈ B \ A ∪ A)).card := by
      rw [rep_card_union_right (A ∩ B) (B \ A) A x sdiff_disjoint]
    _ = _ := by rw [hU]

/-- Layer cake for a truncated representation function. -/
private theorem rep_layer_cake {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (A B : Finset G) (t : ℕ) :
    (∑ u : G, min ((A.filter (fun a => u - a ∈ B)).card) t) =
      ∑ i ∈ Finset.Ico 1 (t + 1),
        (univ.filter (fun u : G => i ≤ (A.filter (fun a => u - a ∈ B)).card)).card := by
  classical
  have hpt : ∀ u : G, min ((A.filter (fun a => u - a ∈ B)).card) t =
      ∑ i ∈ Finset.Ico 1 (t + 1),
        (if i ≤ (A.filter (fun a => u - a ∈ B)).card then (1 : ℕ) else 0) := by
    intro u
    rw [min_eq_card_filter, Finset.card_filter]
  rw [Finset.sum_congr rfl (fun u _ => hpt u), Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.card_filter]

/-- All representations, without truncation, form the product set. -/
private theorem rep_total {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (A B : Finset G) :
    (∑ u : G, (A.filter (fun a => u - a ∈ B)).card) = A.card * B.card := by
  classical
  simp_rw [Finset.card_filter]
  rw [Finset.sum_comm]
  calc
    (∑ a ∈ A, ∑ u : G, if u - a ∈ B then (1 : ℕ) else 0) =
        ∑ _a ∈ A, B.card := by
      apply Finset.sum_congr rfl
      intro a _
      have hbij : Function.Bijective (fun u : G => u - a) := by
        constructor
        · intro u v huv
          have h := congrArg (fun y : G => y + a) huv
          simpa using h
        · intro v
          exact ⟨v + a, by simp⟩
      calc
        (∑ u : G, if u - a ∈ B then (1 : ℕ) else 0) =
            ∑ u : G, if u ∈ B then (1 : ℕ) else 0 :=
          Function.Bijective.sum_comp hbij (fun u : G => if u ∈ B then (1 : ℕ) else 0)
        _ = B.card := by
          rw [← Finset.card_filter]
          simp
    _ = A.card * B.card := by simp [Finset.sum_const, nsmul_eq_mul]

/-- The layer-cake mass does not depend on the order of the summands. -/
private theorem rep_mass_swap {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (A B : Finset G) (t : ℕ) :
    (∑ i ∈ Finset.Ico 1 (t + 1),
      (univ.filter (fun u : G => i ≤ (A.filter (fun a => u - a ∈ B)).card)).card) =
    ∑ i ∈ Finset.Ico 1 (t + 1),
      (univ.filter (fun u : G => i ≤ (B.filter (fun b => u - b ∈ A)).card)).card := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  congr 1
  ext u
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [rep_card_swap]

/-- Translating the first summand shifts its representation function. -/
private theorem rep_card_translate {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B : Finset G) (d u : G) :
    ((A.image (fun a => a + d)).filter (fun a => u - a ∈ B)).card =
      (A.filter (fun a => (u - d) - a ∈ B)).card := by
  classical
  have hinj : Function.Injective (fun a : G => a + d) := by
    intro a b hab
    have h := congrArg (fun y : G => y - d) hab
    simpa using h
  rw [Finset.filter_image, Finset.card_image_of_injective _ hinj]
  congr 1
  ext a
  simp only [Finset.mem_filter]
  rw [show u - (a + d) = (u - d) - a by abel]

/-- Layer-cake mass is invariant under translation of the first summand. -/
private theorem rep_mass_translate {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (A B : Finset G) (d : G) (t : ℕ) :
    (∑ i ∈ Finset.Ico 1 (t + 1),
      (univ.filter (fun u : G =>
        i ≤ ((A.image (fun a => a + d)).filter (fun a => u - a ∈ B)).card)).card) =
    ∑ i ∈ Finset.Ico 1 (t + 1),
      (univ.filter (fun u : G => i ≤ (A.filter (fun a => u - a ∈ B)).card)).card := by
  classical
  apply Finset.sum_congr rfl
  intro i _
  refine Finset.card_bij (fun u _ => u - d) ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_filter] at hu ⊢
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [rep_card_translate] at hu
    exact hu.2
  · intro u _ v _ huv
    have h := congrArg (fun y : G => y + d) huv
    simpa using h
  · intro v hv
    rw [Finset.mem_filter] at hv
    refine ⟨v + d, ?_, by simp⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rw [rep_card_translate]
    simpa using hv.2

/-- The minimum of a sum dominates the sum of two truncated minima. -/
private theorem min_add_min_le_min (t v a b : ℕ) (h : v ≤ t) :
    min v a + min (t - v) b ≤ min t (a + b) := by
  rcases le_total v a with ha | ha
  · rw [min_eq_left ha]
    rcases le_total (t - v) b with hb | hb
    · rw [min_eq_left hb]
      have ht : t ≤ a + b := by omega
      rw [min_eq_left ht]
      omega
    · rw [min_eq_right hb]
      rcases le_total t (a + b) with ht | ht
      · rw [min_eq_left ht]
        omega
      · rw [min_eq_right ht]
        omega
  · rw [min_eq_right ha]
    rcases le_total (t - v) b with hb | hb
    · rw [min_eq_left hb]
      rcases le_total t (a + b) with ht | ht
      · rw [min_eq_left ht]
        omega
      · rw [min_eq_right ht]
        omega
    · rw [min_eq_right hb]
      rcases le_total t (a + b) with ht | ht
      · rw [min_eq_left ht]
        omega
      · rw [min_eq_right ht]

/-- The decomposition of representation functions bounds their truncated masses. -/
private theorem rep_mass_decompose {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (A B : Finset G) (t v : ℕ) (h : v ≤ t) :
    (∑ i ∈ Finset.Ico 1 (v + 1),
      (univ.filter (fun u : G => i ≤ ((A ∩ B).filter (fun a => u - a ∈ A ∪ B)).card)).card) +
    (∑ i ∈ Finset.Ico 1 (t - v + 1),
      (univ.filter (fun u : G => i ≤ ((A \ B).filter (fun a => u - a ∈ B \ A)).card)).card) ≤
    ∑ i ∈ Finset.Ico 1 (t + 1),
      (univ.filter (fun u : G => i ≤ (A.filter (fun a => u - a ∈ B)).card)).card := by
  classical
  rw [← rep_layer_cake (A ∩ B) (A ∪ B) v,
    ← rep_layer_cake (A \ B) (B \ A) (t - v), ← rep_layer_cake A B t,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro u _
  rw [rep_card_decompose A B u]
  have hm := min_add_min_le_min t v
    ((A ∩ B).filter (fun a => u - a ∈ A ∪ B)).card
    ((A \ B).filter (fun a => u - a ∈ B \ A)).card h
  simpa [min_comm, add_comm] using hm

/-- A sum has at most `|B|` representations. -/
private theorem rep_card_le {G : Type*} [AddCommGroup G] [DecidableEq G]
    (A B : Finset G) (u : G) :
    (A.filter (fun a => u - a ∈ B)).card ≤ B.card := by
  classical
  rw [rep_card_swap]
  exact Finset.card_filter_le _ _

/-- Without truncation, layer-cake mass is the full product cardinality. -/
private theorem rep_mass_full {G : Type*} [AddCommGroup G] [DecidableEq G] [Fintype G]
    (A B : Finset G) :
    (∑ i ∈ Finset.Ico 1 (B.card + 1),
      (univ.filter (fun u : G => i ≤ (A.filter (fun a => u - a ∈ B)).card)).card) =
      A.card * B.card := by
  classical
  rw [← rep_layer_cake A B B.card]
  calc
    (∑ u : G, min ((A.filter (fun a => u - a ∈ B)).card) B.card) =
        ∑ u : G, (A.filter (fun a => u - a ∈ B)).card := by
      apply Finset.sum_congr rfl
      intro u _
      exact min_eq_left (rep_card_le A B u)
    _ = A.card * B.card := rep_total A B

/-- In prime characteristic, full intersection at every extremal translate is periodicity. -/
private theorem eq_univ_of_translate_inter {p : ℕ} (hp : p.Prime) [NeZero p]
    (A B : Finset (ZMod p)) (hA : A.Nonempty) (hB : 1 < B.card)
    (hfull : ∀ a ∈ A, ∀ b ∈ B,
      ((A.image (fun a' => a' + (b - a))) ∩ B).card = B.card) :
    A = Finset.univ := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b₀, hb₀, b₁, hb₁, hbne⟩ := Finset.one_lt_card.mp hB
  have hd : b₁ - b₀ ≠ 0 := sub_ne_zero.mpr (Ne.symm hbne)
  have hshift : ∀ a ∈ A, a + (b₁ - b₀) ∈ A := by
    intro a ha
    have hf := hfull a ha b₀ hb₀
    have heq : (A.image (fun a' => a' + (b₀ - a)) ∩ B) = B :=
      Finset.eq_of_subset_of_card_le Finset.inter_subset_right (by omega)
    have hb₁' : b₁ ∈ A.image (fun a' => a' + (b₀ - a)) := by
      have hm : b₁ ∈ A.image (fun a' => a' + (b₀ - a)) ∩ B := by
        rw [heq]
        exact hb₁
      exact (Finset.mem_inter.mp hm).1
    obtain ⟨a', ha', heq'⟩ := Finset.mem_image.mp hb₁'
    have heq'' : a + (b₁ - b₀) = a' := by
      rw [← heq']
      ring
    rw [heq'']
    exact ha'
  have hiter : ∀ n : ℕ, ∀ a ∈ A, a + n • (b₁ - b₀) ∈ A := by
    intro n
    induction n with
    | zero =>
        intro a ha
        simpa using ha
    | succ n ih =>
        intro a ha
        rw [succ_nsmul]
        have ha' : a + n • (b₁ - b₀) ∈ A := ih a ha
        have hs := hshift (a + n • (b₁ - b₀)) ha'
        simpa [add_assoc] using hs
  ext z
  simp only [Finset.mem_univ, iff_true]
  obtain ⟨a, ha⟩ := hA
  have hz : z - a = (((z - a) / (b₁ - b₀)).val : ℕ) • (b₁ - b₀) := by
    rw [nsmul_eq_mul, ZMod.natCast_zmod_val]
    exact (div_mul_cancel₀ (z - a) hd).symm
  have hm := hiter (((z - a) / (b₁ - b₀)).val) a ha
  rw [← hz] at hm
  simpa using hm

/-- Pollard's inequality is equality at the smallest possible level. -/
private theorem pollard_base {p : ℕ} [NeZero p]
    (A B : Finset (ZMod p)) (t : ℕ) (ht : t = B.card) :
    t * min p (A.card + B.card - t) ≤
      ∑ i ∈ Finset.Ico 1 (t + 1),
        (univ.filter (fun u : ZMod p => i ≤ (A.filter (fun a => u - a ∈ B)).card)).card := by
  classical
  have ha : A.card ≤ p := by
    have h := Finset.card_le_univ A
    rw [ZMod.card] at h
    exact h
  have hmin : min p (A.card + B.card - t) = A.card := by
    rw [ht, Nat.add_sub_cancel_right]
    exact min_eq_right ha
  rw [hmin, ht]
  exact Nat.le_of_eq ((Nat.mul_comm _ _).trans (rep_mass_full A B).symm)

/-- Pollard's inequality for the whole group in the first summand. -/
private theorem pollard_univ {p : ℕ} [NeZero p]
    (B : Finset (ZMod p)) (t : ℕ) (ht : t ≤ B.card) :
    t * min p ((Finset.univ : Finset (ZMod p)).card + B.card - t) ≤
      ∑ i ∈ Finset.Ico 1 (t + 1),
        (univ.filter (fun u : ZMod p =>
          i ≤ ((Finset.univ : Finset (ZMod p)).filter (fun a => u - a ∈ B)).card)).card := by
  classical
  have hr : ∀ u : ZMod p,
      ((Finset.univ : Finset (ZMod p)).filter (fun a => u - a ∈ B)).card = B.card := by
    intro u
    rw [rep_card_swap]
    simp
  have hcard : ∀ i ∈ Finset.Ico 1 (t + 1),
      (univ.filter (fun u : ZMod p =>
        i ≤ ((Finset.univ : Finset (ZMod p)).filter (fun a => u - a ∈ B)).card)).card = p := by
    intro i hi
    have hit : i ≤ t := by
      rw [Finset.mem_Ico] at hi
      omega
    have hib : i ≤ B.card := hit.trans ht
    have heq : (univ.filter (fun u : ZMod p =>
        i ≤ ((Finset.univ : Finset (ZMod p)).filter (fun a => u - a ∈ B)).card)) = univ := by
      ext u
      simp [hr, hib]
    rw [heq]
    simp [ZMod.card]
  have hF : (∑ i ∈ Finset.Ico 1 (t + 1),
        (univ.filter (fun u : ZMod p =>
          i ≤ ((Finset.univ : Finset (ZMod p)).filter (fun a => u - a ∈ B)).card)).card) = t * p := by
    calc
      _ = ∑ _i ∈ Finset.Ico 1 (t + 1), p := Finset.sum_congr rfl hcard
      _ = t * p := by simp [Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
  rw [hF]
  exact Nat.mul_le_mul_left t (min_le_left _ _)

/-- The numerical comparison in Pollard's induction. -/
private theorem pollard_arith (a b p t v : ℕ) (hta : t ≤ a) (htb : t ≤ b)
    (hv : v < t) (hvp : 0 < v) :
    t * min p (a + b - t) ≤
      v * (a + b - v) + (t - v) * min p (a + b - t - v) := by
  have hle : v ≤ t := le_of_lt hv
  have htv : t - v + v = t := Nat.sub_add_cancel hle
  have hQ : a + b - t - v + v = a + b - t := by omega
  have hR : a + b - v = (a + b - t - v) + t := by omega
  by_cases hc : p ≤ a + b - t - v
  · have hc' : p ≤ a + b - t := by omega
    rw [min_eq_left hc, min_eq_left hc']
    have hn : 0 ≤ v * ((a + b - t - v) + t - p) := by positivity
    nlinarith
  · have hc' : a + b - t - v ≤ p := by omega
    rw [min_eq_right hc']
    calc
      t * min p (a + b - t) ≤ t * (a + b - t) :=
        Nat.mul_le_mul_left t (min_le_right _ _)
      _ = v * (a + b - v) + (t - v) * (a + b - t - v) := by nlinarith

/-- Pollard's theorem, with the smaller set second. -/
private theorem pollard_prime_aux {p : ℕ} (hp : p.Prime) [NeZero p] :
    ∀ b : ℕ, ∀ A B : Finset (ZMod p), B.card = b → B.card ≤ A.card →
      ∀ t : ℕ, 0 < t → t ≤ B.card →
      t * min p (A.card + B.card - t) ≤
        ∑ i ∈ Finset.Ico 1 (t + 1),
          (univ.filter (fun u : ZMod p => i ≤ (A.filter (fun a => u - a ∈ B)).card)).card := by
  intro b
  induction b using Nat.strong_induction_on with
  | h b ih =>
    intro A B hbc hBA t ht htB
    by_cases hbase : t = B.card
    · exact pollard_base A B t hbase
    have htlt : t < B.card := by omega
    have hBgt : 1 < B.card := by omega
    have hBA' : B.card ≤ A.card := hBA
    have hA : A.Nonempty := Finset.card_pos.mp (by omega)
    by_cases hfull : ∀ a ∈ A, ∀ b ∈ B,
        ((A.image (fun a' => a' + (b - a))) ∩ B).card = B.card
    · have hAu := eq_univ_of_translate_inter hp A B hA hBgt hfull
      have hu := pollard_univ B t htB
      simpa [hAu] using hu
    · push_neg at hfull
      obtain ⟨a₀, ha₀, b₀, hb₀, hne⟩ := hfull
      set A' : Finset (ZMod p) := A.image (fun a' => a' + (b₀ - a₀)) with hA'def
      have hmass := rep_mass_translate A B (b₀ - a₀) t
      rw [← hmass]
      have hinj : Function.Injective (fun a : ZMod p => a + (b₀ - a₀)) := by
        intro a₁ a₂ haa
        have h := congrArg (fun y : ZMod p => y - (b₀ - a₀)) haa
        simpa using h
      have hAc : A'.card = A.card := by
        rw [hA'def]
        exact Finset.card_image_of_injective _ hinj
      rw [← hAc]
      have hBA'' : B.card ≤ A'.card := by simpa [hAc] using hBA'
      have hbimg : b₀ ∈ A' := by
        rw [hA'def]
        exact Finset.mem_image.mpr ⟨a₀, ha₀, by ring⟩
      have hbinter : b₀ ∈ A' ∩ B := Finset.mem_inter.mpr ⟨hbimg, hb₀⟩
      have hvpos : 0 < (A' ∩ B).card := Finset.card_pos.mpr ⟨b₀, hbinter⟩
      have hvle : (A' ∩ B).card ≤ B.card := Finset.card_le_card Finset.inter_subset_right
      have hvlt : (A' ∩ B).card < B.card := by omega
      have hIU : (A' ∩ B).card ≤ (A' ∪ B).card := by
        apply Finset.card_le_card
        exact Finset.inter_subset_left.trans Finset.subset_union_left
      have hScard : (A' \ B).card = A'.card - (A' ∩ B).card := by
        simp [Finset.card_sdiff, Finset.inter_comm]
      have hTcard : (B \ A').card = B.card - (A' ∩ B).card := by
        simp [Finset.card_sdiff, Finset.inter_comm]
      have hUcard0 := Finset.card_union_add_card_inter A' B
      have hUcard : (A' ∪ B).card = A'.card + B.card - (A' ∩ B).card := by omega
      by_cases htv : t ≤ (A' ∩ B).card
      · have hvltb : (A' ∩ B).card < b := by omega
        have hIH := ih ((A' ∩ B).card) hvltb (A' ∪ B) (A' ∩ B) rfl hIU t ht htv
        rw [Finset.card_union_add_card_inter, rep_mass_swap (A' ∪ B) (A' ∩ B) t] at hIH
        have hdec := rep_mass_decompose A' B t t (le_refl t)
        exact hIH.trans ((Nat.le_add_right _ _).trans hdec)
      · have hvlt' : (A' ∩ B).card < t := by omega
        have hTleS : (B \ A').card ≤ (A' \ B).card := by
          rw [hScard, hTcard]
          exact Nat.sub_le_sub_right hBA'' _
        have hTlt : (B \ A').card < b := by
          rw [hTcard, hbc]
          omega
        have hTaux : t - (A' ∩ B).card ≤ (B \ A').card := by
          rw [hTcard]
          omega
        have hIH := ih ((B \ A').card) hTlt (A' \ B) (B \ A') rfl hTleS
          (t - (A' ∩ B).card) (by omega) hTaux
        have hSTlevel : (A' \ B).card + (B \ A').card - (t - (A' ∩ B).card) =
            A'.card + B.card - t - (A' ∩ B).card := by
          rw [hScard, hTcard]
          omega
        rw [hSTlevel] at hIH
        have hfirst :
            (∑ i ∈ Finset.Ico 1 ((A' ∩ B).card + 1),
              (univ.filter (fun u : ZMod p =>
                i ≤ ((A' ∩ B).filter (fun a => u - a ∈ A' ∪ B)).card)).card) =
            (A' ∩ B).card * (A'.card + B.card - (A' ∩ B).card) := by
          calc
            _ = ∑ i ∈ Finset.Ico 1 ((A' ∩ B).card + 1),
                (univ.filter (fun u : ZMod p =>
                  i ≤ ((A' ∪ B).filter (fun a => u - a ∈ A' ∩ B)).card)).card :=
              (rep_mass_swap (A' ∪ B) (A' ∩ B) (A' ∩ B).card).symm
            _ = (A' ∪ B).card * (A' ∩ B).card := rep_mass_full (A' ∪ B) (A' ∩ B)
            _ = _ := by rw [hUcard, Nat.mul_comm]
        have hb2 : (A' ∩ B).card * (A'.card + B.card - (A' ∩ B).card) +
            (t - (A' ∩ B).card) * min p (A'.card + B.card - t - (A' ∩ B).card) ≤
            (∑ i ∈ Finset.Ico 1 ((A' ∩ B).card + 1),
              (univ.filter (fun u : ZMod p =>
                i ≤ ((A' ∩ B).filter (fun a => u - a ∈ A' ∪ B)).card)).card) +
            ∑ i ∈ Finset.Ico 1 (t - (A' ∩ B).card + 1),
              (univ.filter (fun u : ZMod p =>
                i ≤ ((A' \ B).filter (fun a => u - a ∈ B \ A')).card)).card := by
          calc
            _ = _ := congrArg (fun x => x +
              ((t - (A' ∩ B).card) * min p (A'.card + B.card - t - (A' ∩ B).card))) hfirst.symm
            _ ≤ _ := add_le_add (le_refl _) hIH
        have hdec := rep_mass_decompose A' B t (A' ∩ B).card (le_of_lt hvlt')
        exact (pollard_arith A'.card B.card p t (A' ∩ B).card
          (htB.trans hBA'') htB hvlt' hvpos).trans (hb2.trans hdec)

/-- Pollard's theorem in either order of the two sets. -/
private theorem pollard_prime {p : ℕ} (hp : p.Prime) [NeZero p]
    (A B : Finset (ZMod p)) (t : ℕ) (ht : 0 < t) (htm : t ≤ min A.card B.card) :
    t * min p (A.card + B.card - t) ≤
      ∑ i ∈ Finset.Ico 1 (t + 1),
        (univ.filter (fun u : ZMod p => i ≤ (A.filter (fun a => u - a ∈ B)).card)).card := by
  classical
  by_cases hAB : B.card ≤ A.card
  · exact pollard_prime_aux hp B.card A B rfl hAB t ht (htm.trans (Nat.min_le_right _ _))
  · have hBA : A.card ≤ B.card := by omega
    have h := pollard_prime_aux hp A.card B A rfl hBA t ht (htm.trans (Nat.min_le_left _ _))
    rw [rep_mass_swap A B t, add_comm]
    exact h

/-- Cast of a truncated subtraction, one-sided. -/
private theorem cast_sub_ge (m n : ℕ) : (m : ℝ) - (n : ℝ) ≤ ((m - n : ℕ) : ℝ) := by
  rcases le_total n m with h | h
  · rw [Nat.cast_sub h]
  · have h0 : m - n = 0 := Nat.sub_eq_zero_of_le h
    rw [h0]
    have : (m : ℝ) ≤ n := by exact_mod_cast h
    push_cast
    linarith

end

/-- LEAF. Shao page 15 Lemma 4.4, from Li and Pan math/0701240v3
pages 10 to 11 Lemma 3.3 at k = 3. Their parameter is at least theta/4,
so the lower bound is the cube of theta/4 times N squared.
This concerns finite sets only. No weights or Fourier assumptions occur. -/
theorem popular_triples (θ : ℝ) (hθ : 0 < θ) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N.Prime → N₀ ≤ N → ∀ [NeZero N],
      ∀ X : Fin 3 → Finset (ZMod N),
      (∀ i, θ * N ≤ ((X i).card : ℝ)) →
      (1 + θ) * N ≤ ((X 0).card : ℝ) + (X 1).card + (X 2).card →
      ∀ x : ZMod N, (θ / 4) ^ 3 * (N : ℝ) ^ 2 ≤
        (((univ : Finset (ZMod N × ZMod N)).filter
          (fun yz => yz.1 ∈ X 0 ∧ yz.2 ∈ X 1 ∧ x - yz.1 - yz.2 ∈ X 2)).card : ℝ) := by
  refine ⟨⌈4 / θ⌉₊ + 5, ?_⟩
  intro N hNp hN₀ inst X hX htot x
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hNp.pos
  have hceil4 : (4 / θ : ℝ) ≤ (⌈4 / θ⌉₊ : ℝ) := Nat.le_ceil _
  have hNge : ((⌈4 / θ⌉₊ : ℕ) : ℝ) ≤ (N : ℝ) := by
    have h : ((⌈4 / θ⌉₊ + 5 : ℕ) : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN₀
    push_cast at h
    linarith
  have hθN4 : (1 : ℝ) ≤ θ * N / 4 := by
    have h4θ : 4 / θ ≤ (N : ℝ) := le_trans hceil4 hNge
    have h4 : 4 ≤ θ * N := by
      have h5 := (div_le_iff₀ hθ).mp h4θ
      linarith
    linarith
  have hA : θ * N ≤ ((X 0).card : ℝ) := hX 0
  have hB : θ * N ≤ ((X 1).card : ℝ) := hX 1
  have hC : θ * N ≤ ((X 2).card : ℝ) := hX 2
  have hcardN : ((X 0).card : ℝ) ≤ (N : ℝ) := by
    have h := Finset.card_le_univ (X 0)
    rw [ZMod.card] at h
    exact_mod_cast h
  have hquarter : (0:ℝ) < θ * N / 4 := by positivity
  by_cases hθ1 : θ ≤ 1
  · set k : ℕ := ⌈θ * N / 4⌉₊ with hkdef
    have hk_ge : θ * N / 4 ≤ (k : ℝ) := Nat.le_ceil _
    have hk_lt : (k : ℝ) < θ * N / 4 + 1 := Nat.ceil_lt_add_one (le_of_lt hquarter)
    have hk_le : (k : ℝ) ≤ θ * N / 2 := by linarith
    have hk_ge1 : (1 : ℝ) ≤ (k : ℝ) := le_trans hθN4 hk_ge
    have hkpos : 0 < k := by exact_mod_cast hk_ge1
    have hkmin : k ≤ min (X 0).card (X 1).card := by
      rw [Nat.le_min]
      exact ⟨by exact_mod_cast (by linarith : (k:ℝ) ≤ ((X 0).card : ℝ)),
             by exact_mod_cast (by linarith : (k:ℝ) ≤ ((X 1).card : ℝ))⟩
    have hksum : k ≤ (X 0).card + (X 1).card :=
      le_trans hkmin (le_trans (Nat.min_le_left _ _) (Nat.le_add_right _ _))
    have hpoll := pollard_prime hNp (X 0) (X 1) k hkpos hkmin
    -- Pollard cast to the reals
    have hpollR : (k : ℝ) * min (N : ℝ) (((X 0).card : ℝ) + ((X 1).card : ℝ) - (k : ℝ)) ≤
        ∑ t ∈ Finset.Ico 1 (k + 1),
          ((univ.filter (fun u : ZMod N => t ≤ ((X 0).filter (fun a => u - a ∈ X 1)).card)).card : ℝ) := by
      have hcast : ((k * min N ((X 0).card + (X 1).card - k) : ℕ) : ℝ) ≤
          (((∑ t ∈ Finset.Ico 1 (k + 1),
            (univ.filter (fun u : ZMod N => t ≤ ((X 0).filter (fun a => u - a ∈ X 1)).card)).card) : ℕ) : ℝ) := by
        exact_mod_cast hpoll
      have h1 : ((k * min N ((X 0).card + (X 1).card - k) : ℕ) : ℝ)
          = (k : ℝ) * min (N : ℝ) (((X 0).card : ℝ) + ((X 1).card : ℝ) - (k : ℝ)) := by
        push_cast [Nat.cast_sub hksum, Nat.cast_min]
        ring
      have h2 : (((∑ t ∈ Finset.Ico 1 (k + 1),
            (univ.filter (fun u : ZMod N => t ≤ ((X 0).filter (fun a => u - a ∈ X 1)).card)).card) : ℕ) : ℝ)
          = ∑ t ∈ Finset.Ico 1 (k + 1),
            ((univ.filter (fun u : ZMod N => t ≤ ((X 0).filter (fun a => u - a ∈ X 1)).card)).card : ℝ) := by
        push_cast
        ring
      rw [h1, h2] at hcast
      exact hcast
    -- the level inequality, cast to the reals
    have hlev := triple_ge_levels (X 0) (X 1) (X 2) x k
    have hsum_eq := triple_eq_sum (X 0) (X 1) (X 2) x
    have hlevR : (∑ t ∈ Finset.Ico 1 (k + 1),
          (((univ.filter (fun u : ZMod N => t ≤ ((X 0).filter (fun a => u - a ∈ X 1)).card)).card : ℝ)
            + ((X 2).card : ℝ) - (N : ℝ)))
        ≤ (((univ.filter (fun yz : ZMod N × ZMod N =>
            yz.1 ∈ X 0 ∧ yz.2 ∈ X 1 ∧ x - yz.1 - yz.2 ∈ X 2)).card : ℝ)) := by
      rw [hsum_eq]
      calc (∑ t ∈ Finset.Ico 1 (k + 1),
            (((univ.filter (fun u : ZMod N => t ≤ ((X 0).filter (fun a => u - a ∈ X 1)).card)).card : ℝ)
              + ((X 2).card : ℝ) - (N : ℝ)))
          ≤ (∑ t ∈ Finset.Ico 1 (k + 1),
              (((univ.filter (fun u : ZMod N => t ≤ ((X 0).filter (fun a => u - a ∈ X 1)).card)).card
                + (X 2).card - N : ℕ) : ℝ)) := by
            apply Finset.sum_le_sum
            intro t _
            have := cast_sub_ge ((univ.filter (fun u : ZMod N =>
              t ≤ ((X 0).filter (fun a => u - a ∈ X 1)).card)).card + (X 2).card) N
            push_cast at this ⊢
            linarith
        _ = ((∑ t ∈ Finset.Ico 1 (k + 1),
              ((univ.filter (fun u : ZMod N => t ≤ ((X 0).filter (fun a => u - a ∈ X 1)).card)).card
                + (X 2).card - N)) : ℕ) := by push_cast; rfl
        _ ≤ ((∑ w ∈ X 2, ((X 0).filter (fun a => x - w - a ∈ X 1)).card : ℕ) : ℝ) := by
            exact_mod_cast hlev
    have hsplit : (∑ t ∈ Finset.Ico 1 (k + 1),
          (((univ.filter (fun u : ZMod N => t ≤ ((X 0).filter (fun a => u - a ∈ X 1)).card)).card : ℝ)
            + ((X 2).card : ℝ) - (N : ℝ)))
        = (∑ t ∈ Finset.Ico 1 (k + 1),
            ((univ.filter (fun u : ZMod N => t ≤ ((X 0).filter (fun a => u - a ∈ X 1)).card)).card : ℝ))
          + (k : ℝ) * (((X 2).card : ℝ) - (N : ℝ)) := by
      have hp : ∀ t : ℕ,
          (((univ.filter (fun u : ZMod N => t ≤ ((X 0).filter (fun a => u - a ∈ X 1)).card)).card : ℝ)
            + ((X 2).card : ℝ) - (N : ℝ))
          = (((univ.filter (fun u : ZMod N => t ≤ ((X 0).filter (fun a => u - a ∈ X 1)).card)).card : ℝ))
            + (((X 2).card : ℝ) - (N : ℝ)) := fun t => by ring
      rw [Finset.sum_congr rfl (fun t _ => hp t), Finset.sum_add_distrib, Finset.sum_const,
        Nat.card_Ico, nsmul_eq_mul]
      norm_num
    have hτ : (θ / 4) ^ 3 * (N : ℝ) ^ 2 ≤ (k : ℝ) * (θ * N - (k : ℝ)) := by
      have hprod : (θ * N / 4) * (θ * N / 2) ≤ (k : ℝ) * (θ * N - (k : ℝ)) :=
        mul_le_mul hk_ge (by linarith) (by linarith) (by positivity)
      have heq : (θ * N / 4) * (θ * N / 2) = θ ^ 2 * (N : ℝ) ^ 2 / 8 := by ring
      have hsq : (0:ℝ) < θ ^ 2 * (N : ℝ) ^ 2 := by positivity
      rw [heq] at hprod
      nlinarith [hprod, hθ1, hθ, hsq]
    have hmain : (k : ℝ) * (θ * N - (k : ℝ))
        ≤ (((univ.filter (fun yz : ZMod N × ZMod N =>
            yz.1 ∈ X 0 ∧ yz.2 ∈ X 1 ∧ x - yz.1 - yz.2 ∈ X 2)).card : ℝ)) := by
      have hbase := hlevR
      rw [hsplit] at hbase
      by_cases hcase : (N : ℝ) ≤ ((X 0).card : ℝ) + ((X 1).card : ℝ) - (k : ℝ)
      · rw [min_eq_left hcase] at hpollR
        have hstep : (k : ℝ) * (θ * N - (k : ℝ))
            ≤ (k : ℝ) * (N : ℝ) + (k : ℝ) * (((X 2).card : ℝ) - (N : ℝ)) := by
          have h1 : θ * N - (k : ℝ) ≤ (N : ℝ) + (((X 2).card : ℝ) - (N : ℝ)) := by
            linarith
          nlinarith [hk_ge1, h1]
        linarith
      · have hlt : ((X 0).card : ℝ) + ((X 1).card : ℝ) - (k : ℝ) ≤ (N : ℝ) :=
          le_of_lt (lt_of_not_ge hcase)
        rw [min_eq_right hlt] at hpollR
        have hstep : (k : ℝ) * (θ * N - (k : ℝ))
            ≤ (k : ℝ) * (((X 0).card : ℝ) + ((X 1).card : ℝ) - (k : ℝ))
              + (k : ℝ) * (((X 2).card : ℝ) - (N : ℝ)) := by
          have h1 : θ * N - (k : ℝ)
              ≤ (((X 0).card : ℝ) + ((X 1).card : ℝ) - (k : ℝ)) + (((X 2).card : ℝ) - (N : ℝ)) := by
            linarith
          nlinarith [hk_ge1, h1]
        linarith
    linarith
  · exfalso
    have h1 : θ * N ≤ (N : ℝ) := le_trans hA hcardN
    have h2 : (1:ℝ) < θ := lt_of_not_ge hθ1
    nlinarith [hNpos, h1, h2]


/-- Shao page 15, the display after Lemma 4.4. Every counted pair contributes
at least the cube of the superlevel threshold to the weighted sum. -/
theorem weighted_count {N : ℕ} [NeZero N] (g : Fin 3 → ZMod N → ℝ)
    (t : ℝ) (ht : 0 ≤ t) (hg : ∀ i x, 0 ≤ g i x) (x : ZMod N) :
    t ^ 3 * (((univ : Finset (ZMod N × ZMod N)).filter
      (fun yz => t ≤ g 0 yz.1 ∧ t ≤ g 1 yz.2 ∧ t ≤ g 2 (x - yz.1 - yz.2))).card : ℝ) ≤
      ∑ y : ZMod N, ∑ z : ZMod N, g 0 y * g 1 z * g 2 (x - y - z) := by
  let S : Finset (ZMod N × ZMod N) := univ.filter
    (fun yz => t ≤ g 0 yz.1 ∧ t ≤ g 1 yz.2 ∧ t ≤ g 2 (x - yz.1 - yz.2))
  calc
    t ^ 3 * (S.card : ℝ) = ∑ _yz ∈ S, t ^ 3 := by
      rw [sum_const, nsmul_eq_mul, mul_comm]
    _ ≤ ∑ yz ∈ S, g 0 yz.1 * g 1 yz.2 * g 2 (x - yz.1 - yz.2) := by
      apply sum_le_sum
      intro yz hyz
      have h := (mem_filter.mp hyz).2
      calc
        t ^ 3 = t * t * t := by ring
        _ ≤ g 0 yz.1 * g 1 yz.2 * g 2 (x - yz.1 - yz.2) :=
          mul_le_mul (mul_le_mul h.1 h.2.1 ht (hg _ _)) h.2.2 ht
            (mul_nonneg (hg _ _) (hg _ _))
    _ ≤ ∑ yz : ZMod N × ZMod N, g 0 yz.1 * g 1 yz.2 * g 2 (x - yz.1 - yz.2) :=
      sum_le_sum_of_subset_of_nonneg (filter_subset _ _) fun yz _ _ =>
        mul_nonneg (mul_nonneg (hg _ _) (hg _ _)) (hg _ _)
    _ = ∑ y : ZMod N, ∑ z : ZMod N, g 0 y * g 1 z * g 2 (x - y - z) := by
      rw [Fintype.sum_prod_type]

end LeanLab.DensityGoldbach.Counting408

#print axioms LeanLab.DensityGoldbach.Counting408.superlevel_mass
#print axioms LeanLab.DensityGoldbach.Counting408.superlevel_densities
#print axioms LeanLab.DensityGoldbach.Counting408.weighted_count
#print axioms LeanLab.DensityGoldbach.Counting408.popular_triples
