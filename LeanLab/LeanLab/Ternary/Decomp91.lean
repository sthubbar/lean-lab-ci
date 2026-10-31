/-
CODEX task91. P0028, https://arxiv.org/abs/1610.02017v2.
Decomposition of corrected Proposition 3.2 through section 4.2, page 8.
The existing section 4.1 reduction supplies the popular sumset bound.
The external asymmetric Eberhard, Green and Manners input stays a named leaf.
The final assembly has no sorry of its own and remains CONDITIONAL ON that leaf.
AI wrote this Lean code. Binary Goldbach is open.
-/
import LeanLab.Ternary.MMSProp33
import LeanLab.Ternary.MMSZeroAudit

namespace LeanLab.Ternary.MMS.Task91
open Finset LeanLab.Ternary.MMS

/-- LEAF. Essential supports retain density after thresholding at ε/2. P0028 page 8, section 4.2, first density display. -/
theorem essential_support {f : ℕ → ℝ} {P : Finset ℕ} {ε : ℝ} (hε : 0 ≤ ε) (hP : 0 < P.card)
    (hf1 : ∀ n ∈ P, f n ≤ 1) (havg : 1 / 3 + ε ≤ avg f P) :
    (1 / 3 + ε / 2) * P.card ≤ (P.filter (fun n => ε / 2 ≤ f n)).card := by
  exact card_filter_ge hε hP hf1 havg

/-- LEAF. The reflected popular sumset meets the third support in at least the sum of their sizes minus n+1. P0028 page 8, section 4.2, good pair display. The extra endpoint is retained. -/
theorem good_count {n : ℕ} {S A₃ : Finset ℕ} (hS : S ⊆ range (n + 1)) (hA : A₃ ⊆ Icc 1 n) :
    A₃.card + S.card ≤ (A₃.filter (fun a => n - a ∈ S)).card + n + 1 := by
  exact count_good hS hA

/-- LEAF. Triples in the essential supports contribute at least the cube of their common weight. P0028 page 8, section 4.2, final convolution display. -/
theorem weighted_count {N n : ℕ} {f₁ f₂ f₃ : ℕ → ℝ}
    (h₁ : ∀ x ∈ Icc 1 N, 0 ≤ f₁ x) (h₂ : ∀ x ∈ Icc 1 N, 0 ≤ f₂ x)
    (h₃ : ∀ x ∈ Icc 1 N, 0 ≤ f₃ x)
    {A₁ A₂ G : Finset ℕ} (hA₁ : A₁ ⊆ Icc 1 N) (hA₂ : A₂ ⊆ Icc 1 N) (hG : G ⊆ Icc 1 N)
    (hGn : ∀ a ∈ G, a ≤ n) {m : ℝ} (hm : 0 ≤ m)
    (m₁ : ∀ x ∈ A₁, m ≤ f₁ x) (m₂ : ∀ x ∈ A₂, m ≤ f₂ x) (m₃ : ∀ x ∈ G, m ≤ f₃ x) :
    m ^ 3 * ∑ a ∈ G, (rep A₁ A₂ (n - a) : ℝ) ≤ conv3 N f₁ f₂ f₃ n := by
  exact conv3_ge h₁ h₂ h₃ hA₁ hA₂ hG hGn hm m₁ m₂ m₃

/-- LEAF. P0028 page 7, Theorem 4.1, for positive N and the used range of ε.
External source: Eberhard, Green and Manners, Sets of integers with no large sum-free
subset, Theorem 4.1 and remarks after Theorem 6.2, as cited by P0028.
This published additive combinatorial input remains CONDITIONAL. -/
theorem asymmetric_popular_input :
    ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ > (0 : ℝ),
      ∀ (N : ℕ) (A B : Finset ℕ), 0 < N → A ⊆ Icc 1 N → B ⊆ Icc 1 N →
      ((popular N δ A B).card : ℝ) ≤ 4 * (min A.card B.card : ℕ) - ε * N →
      ∃ P : Finset ℕ, IsAPIn N P ∧ δ * N ≤ P.card ∧
        (1 / 2 + ε / 5) * P.card ≤ (A ∩ P).card := by sorry

set_option maxHeartbeats 1000000 in
/-- The exact corrected Prop32 assembled from the leaves. CONDITIONAL ON the leaves. -/
theorem prop32_decomposed : Prop32 := by
  have H : Prop33 := prop33_of_thm41 (thm41_of_positive asymmetric_popular_input)
  intro ε hε
  set e := min ε (1 / 3) with he_def
  have he : 0 < e := lt_min hε (by norm_num)
  have heε : e ≤ ε := min_le_left _ _
  have he3 : e ≤ 1 / 3 := min_le_right _ _
  obtain ⟨η₃, hη₃, N₃, h33⟩ := H e he
  set η := min η₃ 1 / 8 with hη_def
  have hη : 0 < η := by positivity
  have hηη₃ : η ≤ η₃ / 8 := by
    rw [hη_def]; exact div_le_div_of_nonneg_right (min_le_left _ _) (by norm_num)
  have hη1 : η ≤ 1 / 8 := by
    rw [hη_def]; exact div_le_div_of_nonneg_right (min_le_right _ _) (by norm_num)
  refine ⟨η, hη, e ^ 4 * η₃ / 768, by positivity, 8 * N₃ + ⌈16 / e⌉₊ + 8, ?_⟩
  intro N f₁ f₂ f₃ hN u₁ u₂ u₃ d₁ d₂ d₃ n hn2 hnN
  have d₁' := dense_mono heε d₁
  have d₂' := dense_mono heε d₂
  have d₃' := dense_mono heε d₃
  -- sizes
  have hNr : (8 * N₃ + ⌈16 / e⌉₊ + 8 : ℝ) ≤ N := by exact_mod_cast hN
  have hceil := Nat.le_ceil (16 / e)
  have hN₃0 : (0 : ℝ) ≤ N₃ := by positivity
  have hN8 : (8 : ℝ) ≤ N := by linarith [show (0 : ℝ) ≤ 16 / e by positivity]
  have hNe : 16 / e ≤ N := by linarith
  have heN : 16 ≤ e * N := by rwa [div_le_iff₀ he, mul_comm] at hNe
  set M := n / 2 with hM
  have hM2 : 2 * M ≤ n := by omega
  have hM2' : n ≤ 2 * M + 1 := by omega
  have hM2r : (n : ℝ) ≤ 2 * M + 1 := by exact_mod_cast hM2'
  have hMN8 : (N : ℝ) / 8 ≤ M := by linarith
  have hMN₃ : N₃ ≤ M := by
    have : (N₃ : ℝ) ≤ M := by linarith
    exact_mod_cast this
  have hM1 : 1 ≤ M := by
    have : (1 : ℝ) ≤ M := by linarith
    exact_mod_cast this
  have hMn : M ≤ n := by omega
  have hMN : M ≤ N := hMn.trans hnN
  have hn1 : 1 ≤ n := hM1.trans hMn
  have hIccM : Icc 1 M ⊆ Icc 1 N := Finset.Icc_subset_Icc le_rfl hMN
  have hIccn : Icc 1 n ⊆ Icc 1 N := Finset.Icc_subset_Icc le_rfl hnN
  -- essential supports
  set A₁ := (Icc 1 M).filter (fun x => e / 2 ≤ f₁ x) with hA₁
  set A₂ := (Icc 1 M).filter (fun x => e / 2 ≤ f₂ x) with hA₂
  set A₃ := (Icc 1 n).filter (fun x => e / 2 ≤ f₃ x) with hA₃
  have key : ∀ (f : ℕ → ℝ), UnitValued N f → DenseOnAPs N η e f →
      ∀ P : Finset ℕ, IsAPIn N P → η * N ≤ P.card →
        (1 / 3 + e / 2) * P.card ≤ (P.filter (fun x => e / 2 ≤ f x)).card := by
    intro f u d P hP hl
    exact essential_support he.le hP.card_pos
      (fun x hx => (u x (hP.subset_Icc hx)).2) (d P hP hl)
  have dset : ∀ (f : ℕ → ℝ), UnitValued N f → DenseOnAPs N η e f →
      DenseSetOnAPs M η₃ (1 / 3 + e / 2) ((Icc 1 M).filter (fun x => e / 2 ≤ f x)) := by
    intro f u d P hP hl
    have hPN : IsAPIn N P := hP.mono hMN
    have hl' : η * N ≤ P.card := by
      have : η * N ≤ η₃ * M :=
        calc η * N ≤ η₃ / 8 * N := mul_le_mul_of_nonneg_right hηη₃ (Nat.cast_nonneg _)
          _ = η₃ * (N / 8) := by ring
          _ ≤ η₃ * M := mul_le_mul_of_nonneg_left hMN8 hη₃.le
      linarith
    have := key f u d P hPN hl'
    have hsub : P.filter (fun x => e / 2 ≤ f x) ⊆
        (Icc 1 M).filter (fun x => e / 2 ≤ f x) ∩ P := by
      intro x hx
      rw [Finset.mem_filter] at hx
      rw [Finset.mem_inter, Finset.mem_filter]
      exact ⟨⟨hP.subset_Icc hx.1, hx.2⟩, hx.1⟩
    have := Finset.card_le_card hsub
    have : ((P.filter (fun x => e / 2 ≤ f x)).card : ℝ) ≤
        (((Icc 1 M).filter (fun x => e / 2 ≤ f x)) ∩ P).card := by exact_mod_cast this
    linarith
  have hS := h33 M (1 / 3 + e / 2) hMN₃ (by positivity) (by linarith) A₁ A₂
    (Finset.filter_subset _ _) (Finset.filter_subset _ _) (dset f₁ u₁ d₁') (dset f₂ u₂ d₂')
  set S := popular M η₃ A₁ A₂ with hS_def
  -- |A₁| ≥ M/3 and |A₃| ≥ (1/3 + e/2) n
  have hA₁card : (1 / 3 + e / 2) * M ≤ A₁.card := by
    have hηN : η * N ≤ N / 8 := by
      have := mul_le_mul_of_nonneg_right hη1 (Nat.cast_nonneg (α := ℝ) N); linarith
    have := key f₁ u₁ d₁' (Icc 1 M) (isAPIn_Icc hM1 hMN) (by simp; linarith)
    simpa using this
  have hA₃card : (1 / 3 + e / 2) * n ≤ A₃.card := by
    have hnr : (N : ℝ) / 2 ≤ n := hn2
    have hηN : η * N ≤ N / 8 := by
      have := mul_le_mul_of_nonneg_right hη1 (Nat.cast_nonneg (α := ℝ) N); linarith
    have := key f₃ u₃ d₃' (Icc 1 n) (isAPIn_Icc hn1 hnN) (by simp; linarith)
    simpa using this
  -- the good set
  have hSsub : S ⊆ range (n + 1) := by
    intro b hb
    rw [hS_def, popular, Finset.mem_filter, Finset.mem_range] at hb
    rw [Finset.mem_range]; omega
  set G := A₃.filter (fun a => n - a ∈ S) with hG
  have hcount := good_count hSsub (Finset.filter_subset _ _ : A₃ ⊆ Icc 1 n)
  have hcount' : (A₃.card : ℝ) + S.card ≤ G.card + n + 1 := by exact_mod_cast hcount
  have hGcard : e * N / 4 ≤ G.card := by
    have hnr : (N : ℝ) / 2 ≤ n := hn2
    have : (4 * (1 / 3 + e / 2) - e) * M ≤ S.card := hS
    have h1 := mul_le_mul_of_nonneg_left hM2r he.le
    have h2 := mul_le_mul_of_nonneg_left hnr he.le
    clear_value A₁ A₂ A₃ S G M
    linarith
  -- each good a gives many representations
  have hrep : ∀ a ∈ G, η₃ * A₁.card ≤ (rep A₁ A₂ (n - a) : ℝ) := by
    intro a ha
    have h := (Finset.mem_filter.mp ha).2
    rw [hS_def, popular, Finset.mem_filter] at h
    have hmax : (A₁.card : ℝ) ≤ ((max A₁.card A₂.card : ℕ) : ℝ) := by
      exact_mod_cast le_max_left _ _
    exact (mul_le_mul_of_nonneg_left hmax hη₃.le).trans h.2
  have hsum : (G.card : ℝ) * (η₃ * A₁.card) ≤ ∑ a ∈ G, (rep A₁ A₂ (n - a) : ℝ) := by
    have := Finset.card_nsmul_le_sum G (fun a => (rep A₁ A₂ (n - a) : ℝ)) _ hrep
    simpa [nsmul_eq_mul] using this
  have sA₁ : A₁ ⊆ Icc 1 N := (Finset.filter_subset _ _).trans hIccM
  have sA₂ : A₂ ⊆ Icc 1 N := (Finset.filter_subset _ _).trans hIccM
  have sGA₃ : G ⊆ A₃ := Finset.filter_subset _ _
  have sA₃ : A₃ ⊆ Icc 1 n := Finset.filter_subset _ _
  have sG : G ⊆ Icc 1 N := (sGA₃.trans sA₃).trans hIccn
  have hGn : ∀ a ∈ G, a ≤ n := fun a ha => (Finset.mem_Icc.mp (sA₃ (sGA₃ ha))).2
  have m₁ : ∀ x ∈ A₁, e / 2 ≤ f₁ x := fun x hx => (Finset.mem_filter.mp hx).2
  have m₂ : ∀ x ∈ A₂, e / 2 ≤ f₂ x := fun x hx => (Finset.mem_filter.mp hx).2
  have m₃ : ∀ x ∈ G, e / 2 ≤ f₃ x := fun x hx => (Finset.mem_filter.mp (sGA₃ hx)).2
  have hconv := weighted_count (fun x hx => (u₁ x hx).1) (fun x hx => (u₂ x hx).1)
    (fun x hx => (u₃ x hx).1) sA₁ sA₂ sG hGn (by positivity : (0 : ℝ) ≤ e / 2) m₁ m₂ m₃
  -- assemble: (e/2)^3 · (eN/4) · η₃ · (N/24) ≤ conv
  have hA₁N : (N : ℝ) / 24 ≤ A₁.card := by
    linarith [mul_nonneg he.le (Nat.cast_nonneg (α := ℝ) M)]
  have hN0 : (0 : ℝ) ≤ N := by positivity
  have step : e * N / 4 * (η₃ * (N / 24)) ≤ (G.card : ℝ) * (η₃ * A₁.card) := by
    apply mul_le_mul hGcard _ (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_left hA₁N hη₃.le
  have he3' : (0 : ℝ) ≤ (e / 2) ^ 3 := by positivity
  calc e ^ 4 * η₃ / 768 * (N : ℝ) ^ 2 = (e / 2) ^ 3 * (e * N / 4 * (η₃ * (N / 24))) := by ring
    _ ≤ (e / 2) ^ 3 * ∑ a ∈ G, (rep A₁ A₂ (n - a) : ℝ) :=
        mul_le_mul_of_nonneg_left (step.trans hsum) he3'
    _ ≤ conv3 N f₁ f₂ f₃ n := hconv


end LeanLab.Ternary.MMS.Task91
