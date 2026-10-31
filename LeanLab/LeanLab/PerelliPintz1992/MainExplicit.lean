/-
P0070 Perelli-Pintz 1992, Section 3, p. 359: the Theorem from (6) and (7), in explicit form.

* `measurableSet_majorArcs`: the major arcs `𝔐` are a measurable set.
* `setIntegral_union_le'` and `setIntegral_biUnion_le'`: for `g ≥ 0`, the integral over a finite
  union of measurable sets is at most the sum of the integrals.
* `Ioo_subset_windows`: an interval of half-width `δ` is covered by `⌈2δ/w⌉ + 1` open windows of
  half-width `w`.
* `near_inter_subset`: inside an interval of length at most 1, with `δ ≤ 1/2`, only the five
  half-integer shifts `j = -2, …, 2` of `near(ξ, δ)` meet it. The paper writes `j = -1, 0, 1`;
  `j = ±2` is needed when `ξ` and `α` sit at opposite ends of `(1/Q, 1 + 1/Q]`.
* `parseval_T`: `∫_{(c, c+1]} |S|² = Ψ(N, 0) = Σ_{n=N}^{2N} Λ(n)²`.
* `main_explicit`: for any `c` with `𝔐 ⊆ (c, c + 1]`, `𝔪 = (c, c+1] \ 𝔐`, any `δ ∈ (0, 1/2]`,
  `w > 0`, `E₆` bounding the left side of (6) and `E₇` bounding
  `∫_{(ξ - w, ξ + w) ∩ 𝔪} |S|²` for EVERY real `ξ`:
  `Σ_{k ∈ [V, V+H], k ≥ 1} |Ψ(N,2k) - 𝔖(2k)(N-2k)|² ≤ 2 T ((H + 1) · 5(⌈2δ/w⌉ + 1) E₇ + T/(4δ)) + 2 E₆`,
  `T = Ψ(N, 0)`.

With `δ = L^{A+2}/H`, `w = 1/H`, `T ≪ N L`, `E₇ ≪ N L^{-A'-1}` this is the paper's reduction of
the Theorem to (6) and (7). Note: `E₇` must hold for every real `ξ`, not only `ξ ∈ [0, 1]` as the
paper's (7) says: `𝔪 ⊆ (1/Q, 1 + 1/Q]` reaches past 1, and no window with centre in `[0, 1]`
covers `𝔪 ∩ (1 + 1/H, 1 + 1/Q)`. See STATEMENTS.md, QUESTION Q-P0070-7.

KNOWN mathematics. AI-written Lean code, Claude, PC run 20261020T0603Z-352, unit U-1178.
Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.PerelliPintz1992.Kernel

namespace LeanLab.PerelliPintz1992
open Real ArithmeticFunction MeasureTheory Set

lemma measurableSet_majorArcs (N : ℕ) (A : ℝ) : MeasurableSet (majorArcs N A) := by
  unfold majorArcs
  exact MeasurableSet.biUnion (Set.to_countable _) fun _ _ =>
    MeasurableSet.biUnion (Set.to_countable _) fun _ _ => measurableSet_Ioo

/-- For `g ≥ 0` integrable on `s ∪ t`: `∫_{s ∪ t} g ≤ ∫_s g + ∫_t g`. -/
lemma setIntegral_union_le' {g : ℝ → ℝ} (hg0 : ∀ x, 0 ≤ g x) {s t : Set ℝ}
    (hs : MeasurableSet s) (ht : MeasurableSet t) (hi : IntegrableOn g (s ∪ t)) :
    ∫ x in s ∪ t, g x ≤ (∫ x in s, g x) + ∫ x in t, g x := by
  have hst : s ∪ t = s ∪ (t \ s) := by rw [union_sdiff_self]
  rw [hst, setIntegral_union disjoint_sdiff_right (ht.diff hs) (hi.mono_set subset_union_left)
    (hi.mono_set (sdiff_subset.trans subset_union_right))]
  have := setIntegral_mono_set (hi.mono_set subset_union_right)
    (Filter.Eventually.of_forall fun x => hg0 x) (Filter.Eventually.of_forall (sdiff_subset (s := t) (t := s)))
  linarith

/-- Finite union bound: `∫_{⋃ᵢ Sᵢ} g ≤ Σᵢ ∫_{Sᵢ} g` for `g ≥ 0`, when `g` is integrable on a
measurable set containing every `Sᵢ`. -/
lemma setIntegral_biUnion_le' {ι : Type*} {g : ℝ → ℝ} (hg0 : ∀ x, 0 ≤ g x) {U : Set ℝ}
    (hU : IntegrableOn g U) (Sf : ι → Set ℝ) (hS : ∀ i, MeasurableSet (Sf i))
    (hSU : ∀ i, Sf i ⊆ U) (I : Finset ι) :
    ∫ x in ⋃ i ∈ I, Sf i, g x ≤ ∑ i ∈ I, ∫ x in Sf i, g x := by
  classical
  induction I using Finset.induction_on with
  | empty => simp
  | insert i I hiI ih =>
    rw [Finset.set_biUnion_insert, Finset.sum_insert hiI]
    refine (setIntegral_union_le' hg0 (hS i)
      (Finset.measurableSet_biUnion I fun j _ => hS j) ?_).trans (by gcongr)
    exact hU.mono_set (union_subset (hSU i) (iUnion₂_subset fun j _ => hSU j))

/-- An open interval of half-width `δ` is covered by `⌈2δ/w⌉₊ + 1` open windows of half-width
`w` with centres `x - δ + i w`. -/
lemma Ioo_subset_windows (x δ w : ℝ) (hw : 0 < w) :
    Ioo (x - δ) (x + δ) ⊆ ⋃ i ∈ Finset.range (⌈2 * δ / w⌉₊ + 1),
      Ioo (x - δ + i * w - w) (x - δ + i * w + w) := by
  intro y hy
  obtain ⟨h1, h2⟩ := hy
  have hpos : 0 ≤ (y - x + δ) / w := div_nonneg (by linarith) hw.le
  set i := ⌊(y - x + δ) / w⌋₊ with hi
  have hfl := Nat.floor_le hpos
  have hlt := Nat.lt_floor_add_one ((y - x + δ) / w)
  simp only [mem_iUnion, Finset.mem_range, mem_Ioo]
  refine ⟨i, ?_, ?_, ?_⟩
  · have : (y - x + δ) / w < 2 * δ / w := by
      apply div_lt_div_of_pos_right _ hw; linarith
    have h3 : (i : ℝ) < ⌈2 * δ / w⌉₊ + 1 := by
      calc (i : ℝ) ≤ (y - x + δ) / w := hfl
        _ < 2 * δ / w := this
        _ ≤ ⌈2 * δ / w⌉₊ := Nat.le_ceil _
        _ < ⌈2 * δ / w⌉₊ + 1 := by linarith
    exact_mod_cast h3
  · have : (i : ℝ) * w ≤ y - x + δ := by
      rw [le_div_iff₀ hw] at hfl; linarith
    linarith
  · have : y - x + δ < ((i : ℝ) + 1) * w := by
      rw [div_lt_iff₀ hw] at hlt; linarith
    linarith

/-- Inside an interval of length at most `1`, with `δ ≤ 1/2`, `near(ξ, δ)` meets it only through
the shifts `j = -2, …, 2`. -/
lemma near_inter_subset {a ξ δ : ℝ} (hδ : δ ≤ 1 / 2) (hξ : ξ ∈ Icc a (a + 1)) :
    Icc a (a + 1) ∩ near ξ δ ⊆
      ⋃ j ∈ Finset.Icc (-2 : ℤ) 2, Ioo (ξ + j / 2 - δ) (ξ + j / 2 + δ) := by
  rintro α ⟨hα, hn⟩
  simp only [near, mem_iUnion, mem_Ioo] at hn
  obtain ⟨j, hj1, hj2⟩ := hn
  obtain ⟨hξ1, hξ2⟩ := hξ
  obtain ⟨hα1, hα2⟩ := hα
  have hjl : (-3 : ℝ) < j := by linarith
  have hju : (j : ℝ) < 3 := by linarith
  have hjl' : (-3 : ℤ) < j := by exact_mod_cast hjl
  have hju' : j < (3 : ℤ) := by exact_mod_cast hju
  simp only [mem_iUnion, Finset.mem_Icc, mem_Ioo]
  exact ⟨j, ⟨by omega, by omega⟩, hj1, hj2⟩

/-- Parseval for `S` on any unit interval: `∫_{(c, c+1]} |S|² = Ψ(N, 0)`. -/
lemma parseval_T (N : ℕ) (c : ℝ) : ∫ α in Ioc c (c + 1), ‖S N α‖ ^ 2 = Psi N 0 := by
  have h := psi_orth_shift N 0 c
  rw [intervalIntegral.integral_of_le (by linarith)] at h
  have hF : ∀ α, F N 0 α = ((‖S N α‖ ^ 2 : ℝ) : ℂ) := by
    intro α; simp [F, e]
  simp_rw [hF] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-- **The Theorem from (6) and (7), explicit form.** See the module docstring. -/
theorem main_explicit (N V H : ℕ) (A c δ w E6 E7 : ℝ) (hδ : 0 < δ) (hδ2 : δ ≤ 1 / 2)
    (hw : 0 < w) (hM : majorArcs N A ⊆ Ioc c (c + 1))
    (h6 : ∑ k ∈ kRange V H, ‖(∫ α in majorArcs N A, F N k α) -
        ((S2k k * ((N : ℝ) - 2 * k) : ℝ) : ℂ)‖ ^ 2 ≤ E6)
    (h7 : ∀ ξ : ℝ, ∫ α in Ioo (ξ - w) (ξ + w) ∩ (Ioc c (c + 1) \ majorArcs N A),
        ‖S N α‖ ^ 2 ≤ E7) :
    ∑ k ∈ kRange V H, err N k ^ 2 ≤
      2 * (Psi N 0 * ((H + 1) * (5 * ((⌈2 * δ / w⌉₊ + 1 : ℕ) : ℝ) * E7) +
        Psi N 0 / (4 * δ))) + 2 * E6 := by
  classical
  set M := majorArcs N A with hMdef
  set m := Ioc c (c + 1) \ M with hmdef
  have hMm : MeasurableSet M := measurableSet_majorArcs N A
  have hmm : MeasurableSet m := measurableSet_Ioc.diff hMm
  have hmI : m ⊆ Icc c (c + 1) := sdiff_subset.trans Ioc_subset_Icc_self
  set g : ℝ → ℝ := fun α => ‖S N α‖ ^ 2 with hgdef
  have hg0 : ∀ x, 0 ≤ g x := fun x => sq_nonneg _
  have hgI : IntegrableOn g (Icc c (c + 1)) :=
    ((continuous_S N).norm.pow 2).integrableOn_Icc
  set n := ⌈2 * δ / w⌉₊ with hn
  -- E7 ≥ 0
  have hE7 : 0 ≤ E7 := le_trans (setIntegral_nonneg_of_ae_restrict
    (Filter.Eventually.of_forall fun x => hg0 x)) (h7 0)
  set B : ℝ := 5 * ((n + 1 : ℕ) : ℝ) * E7 with hBdef
  have hB0 : 0 ≤ B := by positivity
  -- the window bound behind (5)
  have hB : ∀ ξ ∈ m, ∫ α in m ∩ near ξ δ, ‖S N α‖ ^ 2 ≤ B := by
    intro ξ hξ
    set I := Finset.Icc (-2 : ℤ) 2 ×ˢ Finset.range (n + 1) with hIdef
    let ctr : ℤ × ℕ → ℝ := fun p => ξ + (p.1 : ℝ) / 2 - δ + (p.2 : ℝ) * w
    let Sf : ℤ × ℕ → Set ℝ := fun p => Ioo (ctr p - w) (ctr p + w) ∩ m
    have hsub : m ∩ near ξ δ ⊆ ⋃ p ∈ I, Sf p := by
      intro α hα
      have hα' : α ∈ Icc c (c + 1) ∩ near ξ δ := ⟨hmI hα.1, hα.2⟩
      have := near_inter_subset hδ2 (hmI hξ) hα'
      simp only [mem_iUnion] at this
      obtain ⟨j, hj, hαj⟩ := this
      have h2 := Ioo_subset_windows (ξ + j / 2) δ w hw hαj
      simp only [mem_iUnion] at h2
      obtain ⟨i, hi, hαi⟩ := h2
      simp only [mem_iUnion]
      refine ⟨(j, i), Finset.mem_product.mpr ⟨hj, hi⟩, ?_, hα.1⟩
      simp only [ctr]
      exact hαi
    have hSm : ∀ p, Sf p ⊆ Icc c (c + 1) := fun p => inter_subset_right.trans hmI
    calc ∫ α in m ∩ near ξ δ, ‖S N α‖ ^ 2
        ≤ ∫ α in ⋃ p ∈ I, Sf p, g α := by
          refine setIntegral_mono_set ?_ (Filter.Eventually.of_forall fun x => hg0 x)
            (Filter.Eventually.of_forall hsub)
          exact hgI.mono_set (iUnion₂_subset fun p _ => hSm p)
      _ ≤ ∑ p ∈ I, ∫ α in Sf p, g α :=
          setIntegral_biUnion_le' hg0 hgI Sf (fun p => measurableSet_Ioo.inter hmm) hSm I
      _ ≤ ∑ p ∈ I, E7 := Finset.sum_le_sum fun p _ => h7 (ctr p)
      _ = B := by
          rw [Finset.sum_const, nsmul_eq_mul, hIdef, Finset.card_product, hBdef]
          simp
  -- (4)
  have h4 := eq4 N (kRange V H) c hMm hM
  have herr : ∑ k ∈ kRange V H, err N k ^ 2 =
      ∑ k ∈ kRange V H, ‖(Psi N k : ℂ) - ((S2k k * ((N : ℝ) - 2 * k) : ℝ) : ℂ)‖ ^ 2 := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, sq_abs, err]
  -- (5)
  have h5 := eq5 N V H hmm hmI hδ hB
  have hsubk : ∑ k ∈ kRange V H, ‖∫ α in m, F N k α‖ ^ 2 ≤
      ∑ k ∈ Finset.Icc V (V + H), ‖∫ α in m, F N k α‖ ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun _ _ _ => sq_nonneg _)
  -- T ≤ Ψ(N, 0)
  set T := ∫ α in m, ‖S N α‖ ^ 2 with hTdef
  have hT0 : 0 ≤ T := setIntegral_nonneg_of_ae_restrict
    (Filter.Eventually.of_forall fun x => hg0 x)
  have hTP : T ≤ Psi N 0 := by
    rw [← parseval_T N c]
    exact setIntegral_mono_set (hgI.mono_set Ioc_subset_Icc_self)
      (Filter.Eventually.of_forall fun x => hg0 x) (Filter.Eventually.of_forall sdiff_subset)
  have hmono : T * ((H + 1) * B + T / (4 * δ)) ≤
      Psi N 0 * ((H + 1) * B + Psi N 0 / (4 * δ)) := by
    have h4δ : 0 < 4 * δ := by linarith
    have : T / (4 * δ) ≤ Psi N 0 / (4 * δ) := div_le_div_of_nonneg_right hTP h4δ.le
    have hHB : 0 ≤ ((H : ℝ) + 1) * B := by positivity
    have : 0 ≤ T / (4 * δ) := div_nonneg hT0 h4δ.le
    nlinarith
  rw [herr]
  rw [← hmdef] at h4
  linarith

/-- Vacuity: every hypothesis of `main_explicit` holds at `N = 0`, `V = H = 0`, `c = 0`,
`δ = w = 1/2`, `E₇ = 0` and `E₆` the left side of (6): at `N = 0` the major arcs are empty and
`S = 0`. -/
lemma vacuity_main :
    majorArcs 0 1 ⊆ Ioc (0 : ℝ) (0 + 1) ∧
    (∀ ξ : ℝ, ∫ α in Ioo (ξ - 1 / 2) (ξ + 1 / 2) ∩ (Ioc (0 : ℝ) (0 + 1) \ majorArcs 0 1),
      ‖S 0 α‖ ^ 2 ≤ 0) := by
  refine ⟨?_, fun ξ => ?_⟩
  · intro x hx
    simp only [majorArcs, mem_iUnion, mem_setOf_eq] at hx
    obtain ⟨q, ⟨hq1, hq2⟩, _⟩ := hx
    have : L ((0 : ℕ) : ℝ) = 0 := by simp [L]
    rw [this, Real.zero_rpow (by unfold Bexp; norm_num)] at hq2
    have : (1 : ℝ) ≤ q := by exact_mod_cast hq1
    linarith
  · have hS : ∀ α, S 0 α = 0 := by intro α; simp [S]
    simp [hS]

#print axioms measurableSet_majorArcs
#print axioms setIntegral_biUnion_le'
#print axioms Ioo_subset_windows
#print axioms near_inter_subset
#print axioms parseval_T
#print axioms main_explicit

end LeanLab.PerelliPintz1992
