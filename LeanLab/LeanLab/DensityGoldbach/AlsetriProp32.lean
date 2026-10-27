/-
P0085 Alsetri 2025, arXiv 2505.09648, Proposition 3.2: f₁, f₂, f₃ : Z_15 → [0, 1] vanishing on
the classes not ≡ 1 mod 3, Fᵢ = Σ_{a ∈ Z_15^*} fᵢ(a), F₁F₂ + F₂F₃ + F₃F₁ > 2(F₁ + F₂ + F₃);
then every x ≡ 0 mod 3 is a₁ + a₂ + a₃ with reduced aᵢ, fᵢ(aᵢ) > 0 and Σ fᵢ(aᵢ) > 3/2.
Proof as in the paper: sort each fᵢ on the four units {1, 4, 7, 13} ≡ 1 mod 3, the real core
`p32_core` contrapositively, superlevel sets mapped to Z_5 (injective there), Cauchy-Davenport
in Z_5, and back to Z_15 since the sum of three classes ≡ 1 mod 3 is ≡ 0 mod 3.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
-/
import LeanLab.DensityGoldbach.AlsetriProp32Real
import LeanLab.DensityGoldbach.AlsetriProp31
import LeanLab.DensityGoldbach.Alsetri2025

open Finset
open scoped Pointwise

namespace LeanLab.DensityGoldbach

/-- Prop 3.2's real core for sequences indexed by `ℕ`. -/
lemma p32_fun (a b c : ℕ → ℝ) (ha : ∀ i, i < 4 → 0 ≤ a i ∧ a i ≤ 1)
    (hb : ∀ i, i < 4 → 0 ≤ b i ∧ b i ≤ 1) (hc : ∀ i, i < 4 → 0 ≤ c i ∧ c i ≤ 1)
    (hma : ∀ i j, i ≤ j → j < 4 → a j ≤ a i) (hmb : ∀ i j, i ≤ j → j < 4 → b j ≤ b i)
    (hmc : ∀ i j, i ≤ j → j < 4 → c j ≤ c i)
    (hcond : ∀ i j k, i < 4 → j < 4 → k < 4 → 4 ≤ i + j + k → 0 < a i → 0 < b j → 0 < c k →
      a i + b j + c k ≤ 3 / 2) :
    (∑ i ∈ Finset.range 4, a i) * (∑ i ∈ Finset.range 4, b i)
      + (∑ i ∈ Finset.range 4, b i) * (∑ i ∈ Finset.range 4, c i)
      + (∑ i ∈ Finset.range 4, c i) * (∑ i ∈ Finset.range 4, a i)
      ≤ 2 * ((∑ i ∈ Finset.range 4, a i) + (∑ i ∈ Finset.range 4, b i)
        + (∑ i ∈ Finset.range 4, c i)) := by
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
  exact p32_core (a 0) (a 1) (a 2) (a 3) (b 0) (b 1) (b 2) (b 3) (c 0) (c 1) (c 2) (c 3)
    (ha 3 (by norm_num)).1 (ha 0 (by norm_num)).2 (hma 0 1 (by norm_num) (by norm_num))
    (hma 1 2 (by norm_num) (by norm_num)) (hma 2 3 (by norm_num) (by norm_num))
    (hb 3 (by norm_num)).1 (hb 0 (by norm_num)).2 (hmb 0 1 (by norm_num) (by norm_num))
    (hmb 1 2 (by norm_num) (by norm_num)) (hmb 2 3 (by norm_num) (by norm_num))
    (hc 3 (by norm_num)).1 (hc 0 (by norm_num)).2 (hmc 0 1 (by norm_num) (by norm_num))
    (hmc 1 2 (by norm_num) (by norm_num)) (hmc 2 3 (by norm_num) (by norm_num))
    (fun h1 h2 h3 => hcond 0 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 0 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 0 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 0 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 0 3 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 0 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 1 0 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 1 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 1 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 1 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 1 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 1 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 1 3 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 1 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 1 3 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 1 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 2 0 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 2 0 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 2 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 2 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 2 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 2 2 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 2 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 2 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 2 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 2 3 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 2 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 2 3 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 2 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 3 0 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 3 0 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 3 0 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 3 1 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 3 1 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 3 1 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 3 1 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 3 2 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 3 2 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 3 2 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 3 2 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 3 3 0 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 3 3 1 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 3 3 2 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)
    (fun h1 h2 h3 => hcond 3 3 3 (by norm_num) (by norm_num) (by norm_num) (by norm_num) h1 h2 h3)

/-- The units `≡ 1 mod 3` of `Z_15`. -/
def U15one : Finset (ZMod 15) := {1, 4, 7, 13}

lemma S15_card : #U15one = 4 := by decide

lemma S15_sub : U15one ⊆ unitsMod 15 := by rw [units15_eq]; decide

/-- Reduction mod 5. -/
noncomputable def red5 : ZMod 15 →+* ZMod 5 := ZMod.castHom (by norm_num : 5 ∣ 15) (ZMod 5)

lemma red5_apply (u : ZMod 15) : red5 u = ((u.val : ℕ) : ZMod 5) := by
  rw [red5, ZMod.castHom_apply, ZMod.cast_eq_val]

lemma red5_inj : Set.InjOn red5 U15one := by
  intro u hu v hv h
  rw [red5_apply, red5_apply] at h
  revert h
  simp only [U15one, coe_insert, coe_singleton, Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
  rcases hu with rfl | rfl | rfl | rfl <;> rcases hv with rfl | rfl | rfl | rfl <;> decide

lemma eq15 : ∀ u v : ZMod 15, ((u.val : ℕ) : ZMod 5) = ((v.val : ℕ) : ZMod 5) →
    u.val % 3 = v.val % 3 → u = v := by decide

lemma S15_sum3 : ∀ u ∈ U15one, ∀ v ∈ U15one, ∀ w ∈ U15one, (u + v + w).val % 3 = 0 := by decide

/-- A function vanishing off the classes `≡ 1 mod 3` has the same sum over `Z_15^*` and `U15one`. -/
lemma sum_units15 (f : ZMod 15 → ℝ) (hs : ∀ a : ZMod 15, a.val % 3 ≠ 1 → f a = 0) :
    ∑ a ∈ unitsMod 15, f a = ∑ a ∈ U15one, f a := by
  have z2 : f 2 = 0 := hs 2 (by decide)
  have z8 : f 8 = 0 := hs 8 (by decide)
  have z11 : f 11 = 0 := hs 11 (by decide)
  have z14 : f 14 = 0 := hs 14 (by decide)
  rw [units15_eq, U15one]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton,
    z2, z8, z11, z14]
  ring

lemma card_red5 (I : Finset (ZMod 15)) (hI : I ⊆ U15one) : #(I.image red5) = #I :=
  card_image_of_injOn (red5_inj.mono (by exact_mod_cast hI))

/-- **Alsetri Proposition 3.2.** -/
def AlsetriProp32 : Prop := ∀ f₁ f₂ f₃ : ZMod 15 → ℝ,
  (∀ a, 0 ≤ f₁ a ∧ f₁ a ≤ 1) → (∀ a, 0 ≤ f₂ a ∧ f₂ a ≤ 1) → (∀ a, 0 ≤ f₃ a ∧ f₃ a ≤ 1) →
  (∀ a : ZMod 15, a.val % 3 ≠ 1 → f₁ a = 0) → (∀ a : ZMod 15, a.val % 3 ≠ 1 → f₂ a = 0) →
  (∀ a : ZMod 15, a.val % 3 ≠ 1 → f₃ a = 0) →
  2 * ((∑ a ∈ unitsMod 15, f₁ a) + (∑ a ∈ unitsMod 15, f₂ a) + (∑ a ∈ unitsMod 15, f₃ a)) <
    (∑ a ∈ unitsMod 15, f₁ a) * (∑ a ∈ unitsMod 15, f₂ a)
      + (∑ a ∈ unitsMod 15, f₂ a) * (∑ a ∈ unitsMod 15, f₃ a)
      + (∑ a ∈ unitsMod 15, f₃ a) * (∑ a ∈ unitsMod 15, f₁ a) →
  ∀ x : ZMod 15, x.val % 3 = 0 → ∃ a₁ ∈ unitsMod 15, ∃ a₂ ∈ unitsMod 15, ∃ a₃ ∈ unitsMod 15,
    x = a₁ + a₂ + a₃ ∧ 0 < f₁ a₁ ∧ 0 < f₂ a₂ ∧ 0 < f₃ a₃ ∧ 3 / 2 < f₁ a₁ + f₂ a₂ + f₃ a₃

theorem alsetri_prop32 : AlsetriProp32 := by
  intro f₁ f₂ f₃ h1 h2 h3 s1 s2 s3 hT x hx
  rw [sum_units15 f₁ s1, sum_units15 f₂ s2, sum_units15 f₃ s3] at hT
  obtain ⟨a, hbda, hmoa, hsa, hleva⟩ := sort_seq U15one f₁ h1
  obtain ⟨b, hbdb, hmob, hsb, hlevb⟩ := sort_seq U15one f₂ h2
  obtain ⟨c, hbdc, hmoc, hsc, hlevc⟩ := sort_seq U15one f₃ h3
  rw [S15_card] at hbda hmoa hsa hleva hbdb hmob hsb hlevb hbdc hmoc hsc hlevc
  obtain ⟨i, j, k, hi, hj, hk, hs, pa, pb, pc, hlt⟩ : ∃ i j k, i < 4 ∧ j < 4 ∧ k < 4 ∧
      4 ≤ i + j + k ∧ 0 < a i ∧ 0 < b j ∧ 0 < c k ∧ 3 / 2 < a i + b j + c k := by
    by_contra hne
    push Not at hne
    have := p32_fun a b c hbda hbdb hbdc hmoa hmob hmoc
      (fun i j k hi hj hk hs h1 h2 h3 => hne i j k hi hj hk hs h1 h2 h3)
    rw [hsa, hsb, hsc] at this
    linarith
  have hfp : ∀ (g : ZMod 15 → ℝ) (t : ℝ), (U15one.filter (fun u => t ≤ g u)) ⊆ U15one :=
    fun g t => filter_subset _ _
  have hp5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have huniv := three_levels 5 ((U15one.filter (fun u => a i ≤ f₁ u)).image red5)
    ((U15one.filter (fun u => b j ≤ f₂ u)).image red5) ((U15one.filter (fun u => c k ≤ f₃ u)).image red5)
    i j k (by rw [card_red5 _ (hfp _ _)]; exact hleva i hi)
    (by rw [card_red5 _ (hfp _ _)]; exact hlevb j hj)
    (by rw [card_red5 _ (hfp _ _)]; exact hlevc k hk) (by omega)
  have hx5 : red5 x ∈ ((U15one.filter (fun u => a i ≤ f₁ u)).image red5) +
      ((U15one.filter (fun u => b j ≤ f₂ u)).image red5) +
      ((U15one.filter (fun u => c k ≤ f₃ u)).image red5) := by rw [huniv]; exact mem_univ _
  obtain ⟨y, hy, z3, hz3, hyz⟩ := mem_add.1 hx5
  obtain ⟨z1, hz1, z2, hz2, rfl⟩ := mem_add.1 hy
  obtain ⟨u1, hu1, rfl⟩ := mem_image.1 hz1
  obtain ⟨u2, hu2, rfl⟩ := mem_image.1 hz2
  obtain ⟨u3, hu3, rfl⟩ := mem_image.1 hz3
  obtain ⟨hu1S, hu1f⟩ := mem_filter.1 hu1
  obtain ⟨hu2S, hu2f⟩ := mem_filter.1 hu2
  obtain ⟨hu3S, hu3f⟩ := mem_filter.1 hu3
  have hxe : x = u1 + u2 + u3 := by
    apply eq15
    · rw [← red5_apply, ← red5_apply, map_add, map_add]; exact hyz.symm
    · rw [hx, S15_sum3 u1 hu1S u2 hu2S u3 hu3S]
  exact ⟨u1, S15_sub hu1S, u2, S15_sub hu2S, u3, S15_sub hu3S, hxe, by linarith, by linarith,
    by linarith, by linarith⟩

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.alsetri_prop32
