/-
Matomaki-Maynard-Shao 2016, section 4.2: Proposition 3.3 implies Proposition 3.2.
P0028, arXiv 1610.02017 v2. Both in the corrected form with N ≥ N₀(ε), see F-0006.
The proof follows section 4.2: essential supports A₁, A₂ of f₁, f₂ on [⌊n₀/2⌋], their
popular sums S, the essential support A₃ of f₃ on [n₀], and the count of a ∈ A₃ with
n₀ − a ∈ S. We make the paper's progression lengths explicit: its η for [N] becomes
min(η, 1)/8, so that a progression of length η⌊n₀/2⌋ is long in [N].
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Ternary.MMSTransference

namespace LeanLab.Ternary.MMS

open Finset

/-! ### Progressions -/

theorem isAPIn_Icc {N M : ℕ} (hM : 1 ≤ M) (hMN : M ≤ N) : IsAPIn N (Icc 1 M) := by
  refine ⟨1, 1, M, le_rfl, hM, ?_, fun n hn => ?_⟩
  · ext n
    simp only [Finset.mem_Icc, Finset.mem_image, Finset.mem_range]
    constructor
    · rintro ⟨h1, h2⟩; exact ⟨n - 1, by omega, by omega⟩
    · rintro ⟨k, hk, rfl⟩; omega
  · rw [Finset.mem_Icc] at hn; omega

theorem IsAPIn.mono {N N' : ℕ} {P : Finset ℕ} (h : IsAPIn N' P) (hN : N' ≤ N) : IsAPIn N P := by
  obtain ⟨a, d, L, hd, hL, hP, hmem⟩ := h
  exact ⟨a, d, L, hd, hL, hP, fun n hn => ⟨(hmem n hn).1, (hmem n hn).2.trans hN⟩⟩

theorem IsAPIn.subset_Icc {N : ℕ} {P : Finset ℕ} (h : IsAPIn N P) : P ⊆ Icc 1 N := by
  obtain ⟨-, -, -, -, -, -, hmem⟩ := h
  intro n hn; rw [Finset.mem_Icc]; exact hmem n hn

/-! ### Essential supports are dense -/

/-- If `f ≤ 1` on `P` and the average of `f` on `P` is at least `1/3 + ε`, then at least
`(1/3 + ε/2)|P|` points of `P` have `f ≥ ε/2`. -/
theorem card_filter_ge {f : ℕ → ℝ} {P : Finset ℕ} {ε : ℝ} (hε : 0 ≤ ε) (hP : 0 < P.card)
    (hf1 : ∀ n ∈ P, f n ≤ 1) (havg : 1 / 3 + ε ≤ avg f P) :
    (1 / 3 + ε / 2) * P.card ≤ (P.filter (fun n => ε / 2 ≤ f n)).card := by
  have hc : (0 : ℝ) < P.card := by exact_mod_cast hP
  have hsum : (1 / 3 + ε) * P.card ≤ ∑ n ∈ P, f n := by
    unfold avg at havg; rwa [le_div_iff₀ hc] at havg
  rw [← Finset.sum_filter_add_sum_filter_not P (fun n => ε / 2 ≤ f n)] at hsum
  have h1 : ∑ n ∈ P.filter (fun n => ε / 2 ≤ f n), f n ≤
      (P.filter (fun n => ε / 2 ≤ f n)).card := by
    have := Finset.sum_le_sum (s := P.filter (fun n => ε / 2 ≤ f n)) (g := fun _ => (1 : ℝ))
      (fun n hn => hf1 n (Finset.mem_filter.mp hn).1)
    simpa using this
  have h2 : ∑ n ∈ P.filter (fun n => ¬ ε / 2 ≤ f n), f n ≤
      (P.filter (fun n => ¬ ε / 2 ≤ f n)).card * (ε / 2) := by
    have := Finset.sum_le_sum (s := P.filter (fun n => ¬ ε / 2 ≤ f n)) (g := fun _ => ε / 2)
      (fun n hn => le_of_lt (not_le.mp (Finset.mem_filter.mp hn).2))
    simpa using this
  have h3 : ((P.filter (fun n => ¬ ε / 2 ≤ f n)).card : ℝ) ≤ P.card := by
    exact_mod_cast Finset.card_filter_le _ _
  nlinarith

/-! ### The convolution counts the triples -/

theorem conv3_ge {N n : ℕ} {f₁ f₂ f₃ : ℕ → ℝ}
    (h₁ : ∀ x ∈ Icc 1 N, 0 ≤ f₁ x) (h₂ : ∀ x ∈ Icc 1 N, 0 ≤ f₂ x)
    (h₃ : ∀ x ∈ Icc 1 N, 0 ≤ f₃ x)
    {A₁ A₂ G : Finset ℕ} (hA₁ : A₁ ⊆ Icc 1 N) (hA₂ : A₂ ⊆ Icc 1 N) (hG : G ⊆ Icc 1 N)
    (hGn : ∀ a ∈ G, a ≤ n) {m : ℝ} (hm : 0 ≤ m)
    (m₁ : ∀ x ∈ A₁, m ≤ f₁ x) (m₂ : ∀ x ∈ A₂, m ≤ f₂ x) (m₃ : ∀ x ∈ G, m ≤ f₃ x) :
    m ^ 3 * ∑ a ∈ G, (rep A₁ A₂ (n - a) : ℝ) ≤ conv3 N f₁ f₂ f₃ n := by
  set T := (A₁ ×ˢ A₂).filter (fun p => p.1 + p.2 < n ∧ n - (p.1 + p.2) ∈ G) with hT
  -- step 1: the sum of representation counts is at most |T|
  have step1 : ∑ a ∈ G, rep A₁ A₂ (n - a) ≤ T.card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := fun p => n - (p.1 + p.2)) (t := G)
      (fun p hp => (Finset.mem_filter.mp hp).2.2)]
    apply Finset.sum_le_sum
    intro a ha
    apply Finset.card_le_card
    intro p hp
    simp only [Finset.mem_filter] at hp
    obtain ⟨hpA, hps⟩ := hp
    have ha1 := (Finset.mem_Icc.mp (hG ha)).1
    have han := hGn a ha
    have hlt : p.1 + p.2 < n := by omega
    have hsub : n - (p.1 + p.2) = a := by omega
    simp only [hT, Finset.mem_filter]
    exact ⟨⟨hpA, hlt, hsub ▸ ha⟩, hsub⟩
  have step1' : (∑ a ∈ G, (rep A₁ A₂ (n - a) : ℝ)) ≤ T.card := by exact_mod_cast step1
  -- the summand of conv3 as a function on pairs
  set g : ℕ × ℕ → ℝ := fun p =>
    if p.1 + p.2 < n ∧ n - (p.1 + p.2) ≤ N then f₁ p.1 * f₂ p.2 * f₃ (n - (p.1 + p.2)) else 0
    with hg
  have hconv : conv3 N f₁ f₂ f₃ n = ∑ p ∈ Icc 1 N ×ˢ Icc 1 N, g p := by
    rw [Finset.sum_product]; rfl
  -- step 2: each term over T is at least m^3
  have step2 : (T.card : ℝ) * m ^ 3 ≤ ∑ p ∈ T, g p := by
    have : ∀ p ∈ T, m ^ 3 ≤ g p := by
      intro p hp
      simp only [hT, Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨⟨hp1, hp2⟩, hlt, hpG⟩ := hp
      have hle : n - (p.1 + p.2) ≤ N := (Finset.mem_Icc.mp (hG hpG)).2
      simp only [hg]
      rw [if_pos (And.intro hlt hle)]
      have a1 := m₁ _ hp1
      have a2 := m₂ _ hp2
      have a3 := m₃ _ hpG
      have : m * m ≤ f₁ p.1 * f₂ p.2 := mul_le_mul a1 a2 hm (hm.trans a1)
      calc m ^ 3 = m * m * m := by ring
        _ ≤ f₁ p.1 * f₂ p.2 * f₃ (n - (p.1 + p.2)) :=
          mul_le_mul this a3 hm (mul_nonneg (hm.trans a1) (hm.trans a2))
    have := Finset.card_nsmul_le_sum T g (m ^ 3) this
    simpa [nsmul_eq_mul] using this
  -- step 3: T sits inside the full range and the other terms are nonnegative
  have step3 : ∑ p ∈ T, g p ≤ ∑ p ∈ Icc 1 N ×ˢ Icc 1 N, g p := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      simp only [hT, Finset.mem_filter, Finset.mem_product] at hp
      exact Finset.mem_product.mpr ⟨hA₁ hp.1.1, hA₂ hp.1.2⟩
    · intro p hp _
      rw [Finset.mem_product] at hp
      simp only [hg]
      split_ifs with hc
      · have hp1 := Finset.mem_Icc.mp hp.1
        have hp2 := Finset.mem_Icc.mp hp.2
        have h3' : n - (p.1 + p.2) ∈ Icc 1 N := Finset.mem_Icc.mpr ⟨by omega, hc.2⟩
        exact mul_nonneg (mul_nonneg (h₁ _ hp.1) (h₂ _ hp.2)) (h₃ _ h3')
      · exact le_rfl
  rw [hconv]
  have hm3 : 0 ≤ m ^ 3 := pow_nonneg hm 3
  nlinarith [mul_le_mul_of_nonneg_left step1' hm3]

/-! ### The count of section 4.2 -/

/-- If `S ⊆ [0, n]` and `A₃ ⊆ [1, n]`, the number of `a ∈ A₃` with `n − a ∈ S` is at least
`|A₃| + |S| − n − 1`. -/
theorem count_good {n : ℕ} {S A₃ : Finset ℕ} (hS : S ⊆ range (n + 1)) (hA : A₃ ⊆ Icc 1 n) :
    A₃.card + S.card ≤ (A₃.filter (fun a => n - a ∈ S)).card + n + 1 := by
  set T := (Icc 1 n).filter (fun a => n - a ∈ S) with hT
  have h1 : S.erase n ⊆ T.image (fun a => n - a) := by
    intro b hb
    rw [Finset.mem_erase] at hb
    have hb' := Finset.mem_range.mp (hS hb.2)
    rw [Finset.mem_image]
    refine ⟨n - b, ?_, by omega⟩
    rw [hT, Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [show n - (n - b) = b by omega]; exact hb.2
  have h2 : S.card - 1 ≤ T.card :=
    (Finset.pred_card_le_card_erase).trans ((Finset.card_le_card h1).trans Finset.card_image_le)
  have h3 : (A₃ ∪ T).card ≤ n := by
    have : A₃ ∪ T ⊆ Icc 1 n := Finset.union_subset hA (Finset.filter_subset _ _)
    simpa using Finset.card_le_card this
  have h4 : A₃ ∩ T ⊆ A₃.filter (fun a => n - a ∈ S) := by
    intro a ha
    rw [Finset.mem_inter] at ha
    rw [Finset.mem_filter]
    exact ⟨ha.1, (Finset.mem_filter.mp ha.2).2⟩
  have h5 := Finset.card_union_add_card_inter A₃ T
  have h6 := Finset.card_le_card h4
  omega

/-! ### Proposition 3.3 implies Proposition 3.2 -/

theorem dense_mono {N : ℕ} {η ε ε' : ℝ} {f : ℕ → ℝ} (h : ε' ≤ ε) (H : DenseOnAPs N η ε f) :
    DenseOnAPs N η ε' f := fun P hP hl => le_trans (by linarith) (H P hP hl)

set_option maxHeartbeats 1000000 in
/-- **Section 4.2 of P0028, formalized**: the corrected Proposition 3.3 implies the corrected
Proposition 3.2, with `η = min(η₃, 1)/8` and `c = e⁴ η₃ / 768`, `e = min(ε, 1/3)`. -/
theorem prop32_of_prop33 (H : Prop33) : Prop32 := by
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
    exact card_filter_ge he.le hP.card_pos
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
  have hcount := count_good hSsub (Finset.filter_subset _ _ : A₃ ⊆ Icc 1 n)
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
  have hconv := conv3_ge (fun x hx => (u₁ x hx).1) (fun x hx => (u₂ x hx).1)
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

/-- With the cited corrected Proposition 3.3, the corrected Proposition 3.2. -/
theorem mms_prop32_of_cited : Prop32 := prop32_of_prop33 mms_prop33

end LeanLab.Ternary.MMS
