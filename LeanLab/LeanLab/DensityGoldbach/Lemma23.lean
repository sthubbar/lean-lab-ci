/-
P0038 Shao 2012, Lemma 2.3: A, B, C subsets of the units mod 15 with
|A||B| + |B||C| + |C||A| > 5(|A| + |B| + |C|) have A + B + C = Z mod 15.
The paper uses Li-Pan Cor 2.1 when the sizes sum past 16 and a computer for the rest; here
all cases go through one kernel-checked bitmask computation, Lemma23Check.lean, by
monotonicity over the five minimal sorted size types and the pigeonhole step
|(x - (A + B)) ∩ U| + |C| > 8.
AI-written Lean code, Claude, 2026-10-17, run 20261017T0102Z-30056, unit U-0123.
-/
import LeanLab.DensityGoldbach.Statements
import LeanLab.DensityGoldbach.Lemma23C278
import LeanLab.DensityGoldbach.Lemma23C367
import LeanLab.DensityGoldbach.Lemma23C457
import LeanLab.DensityGoldbach.Lemma23C466
import LeanLab.DensityGoldbach.Lemma23C556

open Finset

namespace LeanLab.DensityGoldbach.L23

/-- The `k`-th unit mod 15. -/
def ι (k : ℕ) : ZMod 15 := (u k : ZMod 15)

lemma u_le (k : ℕ) (hk : k < 8) : u k ≤ 14 := by
  interval_cases k <;> decide

lemma isUnit_iff_exists (z : ZMod 15) : IsUnit z ↔ ∃ k < 8, ι k = z := by
  rw [← ZMod.natCast_zmod_val z, ZMod.isUnit_iff_coprime]
  have : ∀ v : ℕ, v < 15 → (v.Coprime 15 ↔ ∃ k < 8, ι k = (v : ZMod 15)) := by decide
  exact this z.val (ZMod.val_lt z)

lemma ι_inj (k₁ k₂ : ℕ) (h₁ : k₁ < 8) (h₂ : k₂ < 8) (h : ι k₁ = ι k₂) : k₁ = k₂ := by
  have : ∀ k₁ < 8, ∀ k₂ < 8, ι k₁ = ι k₂ → k₁ = k₂ := by decide
  exact this k₁ h₁ k₂ h₂ h

/-- The index set of `A`. -/
noncomputable def idx (A : Finset (ZMod 15)) : Finset ℕ := (range 8).filter fun k => ι k ∈ A

lemma card_idx (A : Finset (ZMod 15)) (hA : A ⊆ unitsMod 15) : #(idx A) = #A := by
  have himg : (idx A).image ι = A := by
    ext z; constructor
    · intro hz; obtain ⟨k, hk, rfl⟩ := mem_image.1 hz; exact (mem_filter.1 hk).2
    · intro hz
      have hu : IsUnit z := (mem_filter.1 (hA hz)).2
      obtain ⟨k, hk, rfl⟩ := (isUnit_iff_exists z).1 hu
      exact mem_image.2 ⟨k, mem_filter.2 ⟨mem_range.2 hk, hz⟩, rfl⟩
  have hinj : Set.InjOn ι (idx A) := by
    intro k₁ h₁ k₂ h₂ h
    exact ι_inj k₁ k₂ (mem_range.1 (mem_filter.1 h₁).1) (mem_range.1 (mem_filter.1 h₂).1) h
  calc #(idx A) = #((idx A).image ι) := (card_image_of_injOn hinj).symm
    _ = #A := by rw [himg]

/-- The bitmask of `A`. -/
noncomputable def code (A : Finset (ZMod 15)) : ℕ := ∑ k ∈ idx A, 2 ^ k

lemma testBit_code (A : Finset (ZMod 15)) (k : ℕ) : (code A).testBit k = true ↔ k ∈ idx A := by
  rw [← Nat.mem_bitIndices, ← List.mem_toFinset, code, Finset.toFinset_bitIndices_sum_two_pow]

lemma code_lt (A : Finset (ZMod 15)) : code A < 256 := by
  have h : code A ≤ ∑ k ∈ range 8, 2 ^ k :=
    sum_le_sum_of_subset (filter_subset _ _)
  have h2 : ∑ k ∈ range 8, 2 ^ k = 255 := by decide
  omega

lemma pop_code (A : Finset (ZMod 15)) : pop (code A) = #(idx A) := by
  rw [pop, sumLt_eq]
  have : ∀ k ∈ range 8, (if (code A).testBit k then 1 else 0) = if k ∈ idx A then 1 else 0 := by
    intro k _
    by_cases h : k ∈ idx A
    · rw [if_pos ((testBit_code A k).2 h), if_pos h]
    · rw [if_neg (fun h' => h ((testBit_code A k).1 h')), if_neg h]
  rw [sum_congr rfl this, sum_boole, Nat.cast_id]
  congr 1
  ext k; simp only [mem_filter, idx, mem_range]; tauto

lemma testBit_sumMask (i j d : ℕ) (h : (sumMask i j).testBit d = true) :
    ∃ k₁ < 8, ∃ k₂ < 8, i.testBit k₁ = true ∧ j.testBit k₂ = true ∧ d = (u k₁ + u k₂) % 15 := by
  obtain ⟨k₁, h₁, h⟩ := (testBit_orLt _ _ _).1 h
  obtain ⟨k₂, h₂, h⟩ := (testBit_orLt _ _ _).1 h
  by_cases hb : (i.testBit k₁ && j.testBit k₂) = true
  · rw [if_pos hb, Nat.testBit_two_pow] at h
    rw [Bool.and_eq_true] at hb
    exact ⟨k₁, h₁, k₂, h₂, hb.1, hb.2, (of_decide_eq_true h).symm⟩
  · rw [if_neg hb, Nat.zero_testBit] at h
    exact absurd h (by simp)

/-- **The core**: one size type `(a, b, c)` whose check passed covers `Z/15`. -/
theorem cover_of_check (a b c : ℕ) (hc : check a b c = true) (A B C : Finset (ZMod 15))
    (hA : A ⊆ unitsMod 15) (hB : B ⊆ unitsMod 15) (hC : C ⊆ unitsMod 15)
    (ha : #A = a) (hb : #B = b) (hcC : #C = c) (z : ZMod 15) :
    ∃ x ∈ A, ∃ y ∈ B, ∃ w ∈ C, x + y + w = z := by
  rw [check, allLt_spec] at hc
  have h1 := hc (code A) (code_lt A)
  rw [checkI, pop_code, card_idx A hA, ha, beq_self_eq_true, Bool.not_true, Bool.false_or,
    allLt_spec] at h1
  have h2 := h1 (code B) (code_lt B)
  rw [pop_code, card_idx B hB, hb, beq_self_eq_true, Bool.not_true, Bool.false_or,
    allLt_spec] at h2
  have h3 := h2 z.val (ZMod.val_lt z)
  rw [decide_eq_true_iff, cnt, sumLt_eq, sum_boole, Nat.cast_id] at h3
  set T := (range 8).filter fun k => (sumMask (code A) (code B)).testBit
    ((z.val + 15 - u k) % 15) = true with hT
  have hcC' : #(idx C) = c := by rw [card_idx C hC, hcC]
  have hlt : #(range 8) < #T + #(idx C) := by rw [card_range]; omega
  obtain ⟨k₃, hk₃⟩ := inter_nonempty_of_card_lt_card_add_card (filter_subset _ _)
    (filter_subset _ _) hlt
  obtain ⟨hk₃T, hk₃C⟩ := mem_inter.1 hk₃
  obtain ⟨hk₃r, hbit⟩ := mem_filter.1 hk₃T
  obtain ⟨k₁, hk₁, k₂, hk₂, hb₁, hb₂, hd⟩ := testBit_sumMask _ _ _ hbit
  have hm₁ := mem_filter.1 ((testBit_code A k₁).1 hb₁)
  have hm₂ := mem_filter.1 ((testBit_code B k₂).1 hb₂)
  have hm₃ := (mem_filter.1 hk₃C).2
  refine ⟨ι k₁, hm₁.2, ι k₂, hm₂.2, ι k₃, hm₃, ?_⟩
  have hu3 := u_le k₃ (mem_range.1 hk₃r)
  have hcast : ((u k₁ + u k₂ : ℕ) : ZMod 15) = ((z.val + 15 - u k₃ : ℕ) : ZMod 15) :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).2 hd.symm
  rw [Nat.cast_sub (by omega)] at hcast
  push_cast at hcast
  rw [ZMod.natCast_zmod_val] at hcast
  have h15 : (15 : ZMod 15) = 0 := by decide
  unfold ι
  linear_combination hcast + h15

lemma card_le_eight (A : Finset (ZMod 15)) (hA : A ⊆ unitsMod 15) : #A ≤ 8 := by
  rw [← card_idx A hA]
  exact (card_le_card (filter_subset _ _)).trans (card_range 8).le

/-- Monotonicity: a passed check for sizes at most the actual sizes covers. -/
theorem cover_of_type (a b c : ℕ) (hc : check a b c = true) (A B C : Finset (ZMod 15))
    (hA : A ⊆ unitsMod 15) (hB : B ⊆ unitsMod 15) (hC : C ⊆ unitsMod 15)
    (ha : a ≤ #A) (hb : b ≤ #B) (hcC : c ≤ #C) (z : ZMod 15) :
    ∃ x ∈ A, ∃ y ∈ B, ∃ w ∈ C, x + y + w = z := by
  obtain ⟨A', hA', hA'c⟩ := exists_subset_card_eq ha
  obtain ⟨B', hB', hB'c⟩ := exists_subset_card_eq hb
  obtain ⟨C', hC', hC'c⟩ := exists_subset_card_eq hcC
  obtain ⟨x, hx, y, hy, w, hw, h⟩ := cover_of_check a b c hc A' B' C' (hA'.trans hA)
    (hB'.trans hB) (hC'.trans hC) hA'c hB'c hC'c z
  exact ⟨x, hA' hx, y, hB' hy, w, hC' hw, h⟩

/-- The minimal sorted size types. -/
lemma size_types : ∀ p : ℕ, p < 9 → ∀ q : ℕ, q < 9 → ∀ r : ℕ, r < 9 → p ≤ q → q ≤ r →
    5 * (p + q + r) < p * q + q * r + r * p →
    (2 ≤ p ∧ 7 ≤ q ∧ 8 ≤ r) ∨ (3 ≤ p ∧ 6 ≤ q ∧ 7 ≤ r) ∨ (4 ≤ p ∧ 5 ≤ q ∧ 7 ≤ r) ∨
      (4 ≤ p ∧ 6 ≤ q ∧ 6 ≤ r) ∨ (5 ≤ p ∧ 5 ≤ q ∧ 6 ≤ r) := by
  intro p hp q hq r hr h1 h2 h3
  interval_cases p <;> interval_cases q <;> omega

theorem lemma23_sorted (A B C : Finset (ZMod 15))
    (hA : A ⊆ unitsMod 15) (hB : B ⊆ unitsMod 15) (hC : C ⊆ unitsMod 15)
    (hab : #A ≤ #B) (hbc : #B ≤ #C)
    (h : 5 * (#A + #B + #C) < #A * #B + #B * #C + #C * #A) (z : ZMod 15) :
    ∃ x ∈ A, ∃ y ∈ B, ∃ w ∈ C, x + y + w = z := by
  rcases size_types #A (by have := card_le_eight A hA; omega) #B
    (by have := card_le_eight B hB; omega) #C (by have := card_le_eight C hC; omega)
    hab hbc h with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · exact cover_of_type 2 7 8 check_278 A B C hA hB hC h1 h2 h3 z
  · exact cover_of_type 3 6 7 check_367 A B C hA hB hC h1 h2 h3 z
  · exact cover_of_type 4 5 7 check_457 A B C hA hB hC h1 h2 h3 z
  · exact cover_of_type 4 6 6 check_466 A B C hA hB hC h1 h2 h3 z
  · exact cover_of_type 5 5 6 check_556 A B C hA hB hC h1 h2 h3 z

end LeanLab.DensityGoldbach.L23

namespace LeanLab.DensityGoldbach

open L23 in
/-- **Shao Lemma 2.3**: `A, B, C ⊆ Z₁₅*` with `|A||B| + |B||C| + |C||A| > 5(|A| + |B| + |C|)`
have `A + B + C = Z₁₅`. -/
theorem shao_lemma23 (A B C : Finset (ZMod 15))
    (hA : A ⊆ unitsMod 15) (hB : B ⊆ unitsMod 15) (hC : C ⊆ unitsMod 15)
    (h : 5 * (#A + #B + #C) < #A * #B + #B * #C + #C * #A) (z : ZMod 15) :
    ∃ x ∈ A, ∃ y ∈ B, ∃ w ∈ C, x + y + w = z := by
  by_cases g1 : #A ≤ #B ∧ #B ≤ #C
  · exact lemma23_sorted A B C hA hB hC g1.1 g1.2 h z
  by_cases g2 : #A ≤ #C ∧ #C ≤ #B
  · obtain ⟨x, hx, w, hw, y, hy, e⟩ := lemma23_sorted A C B hA hC hB g2.1 g2.2 (by linarith) z
    exact ⟨x, hx, y, hy, w, hw, by rw [← e]; abel⟩
  by_cases g3 : #B ≤ #A ∧ #A ≤ #C
  · obtain ⟨y, hy, x, hx, w, hw, e⟩ := lemma23_sorted B A C hB hA hC g3.1 g3.2 (by linarith) z
    exact ⟨x, hx, y, hy, w, hw, by rw [← e]; abel⟩
  by_cases g4 : #B ≤ #C ∧ #C ≤ #A
  · obtain ⟨y, hy, w, hw, x, hx, e⟩ := lemma23_sorted B C A hB hC hA g4.1 g4.2 (by linarith) z
    exact ⟨x, hx, y, hy, w, hw, by rw [← e]; abel⟩
  by_cases g5 : #C ≤ #A ∧ #A ≤ #B
  · obtain ⟨w, hw, x, hx, y, hy, e⟩ := lemma23_sorted C A B hC hA hB g5.1 g5.2 (by linarith) z
    exact ⟨x, hx, y, hy, w, hw, by rw [← e]; abel⟩
  have g6 : #C ≤ #B ∧ #B ≤ #A := by omega
  obtain ⟨w, hw, y, hy, x, hx, e⟩ := lemma23_sorted C B A hC hB hA g6.1 g6.2 (by linarith) z
  exact ⟨x, hx, y, hy, w, hw, by rw [← e]; abel⟩

end LeanLab.DensityGoldbach

#print axioms LeanLab.DensityGoldbach.shao_lemma23
