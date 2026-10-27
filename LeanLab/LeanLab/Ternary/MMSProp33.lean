/-
Matomaki-Maynard-Shao 2016, section 4.1: Theorem 4.1 implies Proposition 3.3.
P0028, arXiv 1610.02017 v2. We prove `prop33_of_thm41 : Thm41 → Prop33` in the corrected
forms of MMSTransference.lean, so Proposition 3.3 now rests only on the cited Theorem 4.1,
the asymmetric Eberhard-Green-Manners input.

Route, following section 4.1 with explicit choices:
* reduce to `ε ≤ 1/100` and `ε/4 ≤ α ≤ 1/2 − 3ε`, the paper's reductions;
* `δ = δ(ε/2)` from Theorem 4.1, `q = K!` with `K = ⌈2/δ⌉ + 1`, blocks of length
  `M = ⌊εδN/4⌋ + 1`, and pieces `{n ∈ [N] : (n−1)/M = j, n ≡ r mod q}`;
* trim `A` to `A′ ⊆ A` with at most `α|Q| + 1` elements in each piece `Q` and at least
  `α|Q|` in each piece of length `≥ ηN`; `B` is left untouched, Theorem 4.1 only
  speaks about `A`;
* a progression `P ⊂ [N]` of length `≥ δN` has step dividing `q`, so it is a union of
  whole pieces plus at most `2M` points in the two blocks holding its end points.
The paper trims `B` too; that is not needed.
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Ternary.MMSTransference
import LeanLab.Ternary.MMSProp32

namespace LeanLab.Ternary.MMS

open Finset

/-! ### Residue classes in an interval are progressions -/

theorem filter_mod_eq_image {lo hi q r : ℕ} (hq : 1 ≤ q)
    (hne : ((Icc lo hi).filter (fun n => n % q = r)).Nonempty) :
    ∃ a L : ℕ, 1 ≤ L ∧ lo ≤ a ∧
      (Icc lo hi).filter (fun n => n % q = r) = (range L).image (fun k => a + q * k) := by
  set S := (Icc lo hi).filter (fun n => n % q = r) with hS
  set a := S.min' hne with ha
  have haS : a ∈ S := S.min'_mem hne
  rw [hS, mem_filter, mem_Icc] at haS
  refine ⟨a, (hi - a) / q + 1, Nat.le_add_left 1 _, haS.1.1, ?_⟩
  ext n
  constructor
  · intro hn
    have hmin : a ≤ n := S.min'_le n hn
    rw [hS, mem_filter, mem_Icc] at hn
    have hmod : n % q = a % q := by rw [hn.2, haS.2]
    have hdvd : q ∣ n - a := (Nat.modEq_iff_dvd' hmin).mp hmod.symm
    obtain ⟨k, hk⟩ := hdvd
    refine mem_image.mpr ⟨k, mem_range.mpr ?_, by omega⟩
    have : q * k ≤ hi - a := by omega
    have : k ≤ (hi - a) / q := (Nat.le_div_iff_mul_le (by omega)).mpr (by linarith [mul_comm q k])
    omega
  · intro hn
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hn
    rw [mem_range] at hk
    rw [hS, mem_filter, mem_Icc]
    have h1 : q * k ≤ q * ((hi - a) / q) := Nat.mul_le_mul_left q (by omega)
    have h2 : q * ((hi - a) / q) ≤ hi - a := Nat.mul_div_le (hi - a) q
    refine ⟨⟨by omega, by omega⟩, ?_⟩
    rw [Nat.add_mul_mod_self_left, haS.2]

theorem isAPIn_filter_mod {N lo hi q r : ℕ} (hq : 1 ≤ q) (hlo : 1 ≤ lo) (hhi : hi ≤ N)
    (hne : ((Icc lo hi).filter (fun n => n % q = r)).Nonempty) :
    IsAPIn N ((Icc lo hi).filter (fun n => n % q = r)) := by
  obtain ⟨a, L, hL, -, he⟩ := filter_mod_eq_image hq hne
  refine ⟨a, q, L, hq, hL, he, fun n hn => ?_⟩
  rw [mem_filter, mem_Icc] at hn
  omega


theorem mem_ap_iff {a d L n : ℕ} (hd : 1 ≤ d) (hL : 1 ≤ L) :
    n ∈ (range L).image (fun k => a + d * k) ↔
      a ≤ n ∧ n ≤ a + d * (L - 1) ∧ n % d = a % d := by
  constructor
  · intro hn
    obtain ⟨k, hk, rfl⟩ := mem_image.mp hn
    rw [mem_range] at hk
    have : d * k ≤ d * (L - 1) := Nat.mul_le_mul_left d (by omega)
    refine ⟨by omega, by omega, ?_⟩
    rw [Nat.add_mul_mod_self_left]
  · rintro ⟨h1, h2, h3⟩
    obtain ⟨k, hk⟩ := (Nat.modEq_iff_dvd' h1).mp h3.symm
    refine mem_image.mpr ⟨k, mem_range.mpr ?_, by omega⟩
    have : d * k ≤ d * (L - 1) := by omega
    have := Nat.le_of_mul_le_mul_left this (by omega)
    omega

/-! ### Blocks and pieces -/

/-- The piece label of `n`: its block `(n − 1)/M` and its residue mod `q`. -/
def key (M q n : ℕ) : ℕ × ℕ := ((n - 1) / M, n % q)

/-- The piece with label `k` inside `[N]`. -/
def piece (N M q : ℕ) (k : ℕ × ℕ) : Finset ℕ := (Icc 1 N).filter (fun n => key M q n = k)

/-- The labels that occur in `[N]`. -/
def keys (N M q : ℕ) : Finset (ℕ × ℕ) := (Icc 1 N).image (key M q)

theorem block_iff {M n j : ℕ} (hM : 1 ≤ M) :
    (n - 1) / M = j ↔ j * M ≤ n - 1 ∧ n - 1 < j * M + M := by
  constructor
  · rintro rfl
    refine ⟨Nat.div_mul_le_self _ _, ?_⟩
    have := Nat.lt_div_mul_add (a := n - 1) (show 0 < M by omega)
    linarith
  · rintro ⟨h1, h2⟩
    apply le_antisymm
    · have : (n - 1) / M < j + 1 := by
        rw [Nat.div_lt_iff_lt_mul (by omega)]; linarith
      omega
    · exact (Nat.le_div_iff_mul_le (by omega)).mpr h1

theorem piece_eq {N M q : ℕ} (hM : 1 ≤ M) (j r : ℕ) :
    piece N M q (j, r) =
      (Icc (max 1 (j * M + 1)) (min N (j * M + M))).filter (fun n => n % q = r) := by
  ext n
  simp only [piece, key, mem_filter, mem_Icc, Prod.mk.injEq, block_iff hM]
  constructor
  · rintro ⟨⟨h1, h2⟩, ⟨h3, h4⟩, h5⟩
    exact ⟨⟨max_le h1 (by omega), le_min h2 (by omega)⟩, h5⟩
  · rintro ⟨⟨h1, h2⟩, h5⟩
    have := le_of_max_le_left h1
    have := le_of_max_le_right h1
    have := min_le_left N (j * M + M) |>.trans' h2
    have := min_le_right N (j * M + M) |>.trans' h2
    exact ⟨⟨by omega, by omega⟩, ⟨by omega, by omega⟩, h5⟩

theorem piece_isAPIn {N M q : ℕ} (hM : 1 ≤ M) (hq : 1 ≤ q) (k : ℕ × ℕ)
    (hne : (piece N M q k).Nonempty) : IsAPIn N (piece N M q k) := by
  obtain ⟨j, r⟩ := k
  rw [piece_eq hM] at hne ⊢
  exact isAPIn_filter_mod hq (le_max_left _ _) (min_le_left _ _) hne

theorem keys_card_le {N M q : ℕ} (hM : 1 ≤ M) (hq : 1 ≤ q) :
    (keys N M q).card ≤ (N / M + 1) * q := by
  have : keys N M q ⊆ range (N / M + 1) ×ˢ range q := by
    intro k hk
    obtain ⟨n, hn, rfl⟩ := mem_image.mp hk
    rw [mem_Icc] at hn
    simp only [key, mem_product, mem_range]
    refine ⟨?_, Nat.mod_lt _ (by omega)⟩
    have : (n - 1) / M ≤ N / M := Nat.div_le_div_right (by omega)
    omega
  exact (card_le_card this).trans (by simp)

/-- Fiberwise count over the pieces. -/
theorem card_eq_sum_fib {N M q : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 N) :
    S.card = ∑ k ∈ keys N M q, (S.filter (fun n => key M q n = k)).card :=
  card_eq_sum_card_fiberwise (fun n hn => mem_image_of_mem _ (hS hn))

theorem filter_key_eq_inter {N M q : ℕ} {S : Finset ℕ} (hS : S ⊆ Icc 1 N) (k : ℕ × ℕ) :
    S.filter (fun n => key M q n = k) = S ∩ piece N M q k := by
  ext n
  simp only [mem_filter, mem_inter, piece]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, hS h1, h2⟩
  · rintro ⟨h1, -, h2⟩; exact ⟨h1, h2⟩

theorem sum_card_piece {N M q : ℕ} :
    ∑ k ∈ keys N M q, (piece N M q k).card = N := by
  have := card_eq_sum_fib (M := M) (q := q) (subset_refl (Icc 1 N))
  simp only [Nat.card_Icc, add_tsub_cancel_right] at this
  exact this.symm


/-! ### Trimming `A` piece by piece -/

theorem exists_trim (N M q : ℕ) (A : Finset ℕ) (hA : A ⊆ Icc 1 N) (α : ℝ) (hα : 0 ≤ α) :
    ∃ A' ⊆ A, ∀ k ∈ keys N M q,
      ((A' ∩ piece N M q k).card : ℝ) < α * (piece N M q k).card + 1 ∧
      (α * (piece N M q k).card ≤ (A ∩ piece N M q k).card →
        α * (piece N M q k).card ≤ (A' ∩ piece N M q k).card) := by
  classical
  have hex : ∀ k : ℕ × ℕ, ∃ T ⊆ A ∩ piece N M q k,
      T.card = min (A ∩ piece N M q k).card ⌈α * (piece N M q k).card⌉₊ := fun k =>
    exists_subset_card_eq (min_le_left _ _)
  choose T hTsub hTcard using hex
  refine ⟨(keys N M q).biUnion T, ?_, ?_⟩
  · intro n hn
    obtain ⟨k, -, hk⟩ := mem_biUnion.mp hn
    exact (mem_inter.mp (hTsub k hk)).1
  · intro k hk
    have heq : (keys N M q).biUnion T ∩ piece N M q k = T k := by
      ext n
      constructor
      · intro hn
        obtain ⟨hn1, hn2⟩ := mem_inter.mp hn
        obtain ⟨k', -, hk'⟩ := mem_biUnion.mp hn1
        have h1 := (mem_filter.mp (mem_inter.mp (hTsub k' hk')).2).2
        have h2 := (mem_filter.mp hn2).2
        rw [h1] at h2
        rw [← h2]; exact hk'
      · intro hn
        exact mem_inter.mpr ⟨mem_biUnion.mpr ⟨k, hk, hn⟩, (mem_inter.mp (hTsub k hn)).2⟩
    rw [heq, hTcard]
    have hp : 0 ≤ α * (piece N M q k).card := by positivity
    constructor
    · calc ((min (A ∩ piece N M q k).card ⌈α * (piece N M q k).card⌉₊ : ℕ) : ℝ)
          ≤ (⌈α * (piece N M q k).card⌉₊ : ℝ) := by exact_mod_cast min_le_right _ _
        _ < α * (piece N M q k).card + 1 := Nat.ceil_lt_add_one hp
    · intro h
      rcases le_total (A ∩ piece N M q k).card ⌈α * (piece N M q k).card⌉₊ with h' | h'
      · rw [min_eq_left h']; exact h
      · rw [min_eq_right h']; exact Nat.le_ceil _

/-! ### A progression whose step divides `q` meets whole pieces, except near its ends -/

/-- Points of `[N]` in the blocks of `lo` and `hi`. -/
def ends (M lo hi : ℕ) (n : ℕ) : Prop := (n - 1) / M = (lo - 1) / M ∨ (n - 1) / M = (hi - 1) / M

instance (M lo hi n : ℕ) : Decidable (ends M lo hi n) := by unfold ends; infer_instance

theorem block_card_le {N M : ℕ} (hM : 1 ≤ M) (j : ℕ) :
    ((Icc 1 N).filter (fun n => (n - 1) / M = j)).card ≤ M := by
  have : (Icc 1 N).filter (fun n => (n - 1) / M = j) ⊆ Icc (j * M + 1) (j * M + M) := by
    intro n hn
    rw [mem_filter, mem_Icc, block_iff hM] at hn
    rw [mem_Icc]; omega
  exact (card_le_card this).trans (by simp)

theorem ends_card_le {N M lo hi : ℕ} (hM : 1 ≤ M) {P : Finset ℕ} (hP : P ⊆ Icc 1 N) :
    (P.filter (ends M lo hi)).card ≤ 2 * M := by
  have : P.filter (ends M lo hi) ⊆ (Icc 1 N).filter (fun n => (n - 1) / M = (lo - 1) / M) ∪
      (Icc 1 N).filter (fun n => (n - 1) / M = (hi - 1) / M) := by
    intro n hn
    rw [mem_filter] at hn
    rcases hn.2 with h | h
    · exact mem_union_left _ (mem_filter.mpr ⟨hP hn.1, h⟩)
    · exact mem_union_right _ (mem_filter.mpr ⟨hP hn.1, h⟩)
  calc _ ≤ _ := card_le_card this
    _ ≤ _ := card_union_le _ _
    _ ≤ M + M := add_le_add (block_card_le hM _) (block_card_le hM _)
    _ = 2 * M := by ring

theorem piece_trichotomy {N M q a d L : ℕ} (hM : 1 ≤ M) (hd : 1 ≤ d) (hL : 1 ≤ L)
    (hdq : d ∣ q) (k : ℕ × ℕ) :
    let P := (range L).image (fun t => a + d * t)
    piece N M q k ⊆ P ∨ P ∩ piece N M q k = ∅ ∨
      ∀ n ∈ P ∩ piece N M q k, ends M a (a + d * (L - 1)) n := by
  intro P
  by_cases h1 : piece N M q k ⊆ P
  · exact Or.inl h1
  by_cases h2 : P ∩ piece N M q k = ∅
  · exact Or.inr (Or.inl h2)
  right; right
  obtain ⟨n', hn'p, hn'P⟩ := not_subset.mp h1
  obtain ⟨m, hm⟩ := nonempty_iff_ne_empty.mpr h2
  obtain ⟨hmP, hmp⟩ := mem_inter.mp hm
  have hkm := (mem_filter.mp hmp).2
  have hkn := (mem_filter.mp hn'p).2
  have hmP' := (mem_ap_iff hd hL).mp hmP
  have hblk : (n' - 1) / M = (m - 1) / M := by
    rw [← hkm] at hkn; exact (Prod.mk.inj hkn).1
  have hres : n' % q = m % q := by
    rw [← hkm] at hkn; exact (Prod.mk.inj hkn).2
  have hresd : n' % d = m % d := by
    rw [← Nat.mod_mod_of_dvd n' hdq, ← Nat.mod_mod_of_dvd m hdq, hres]
  have hout : n' < a ∨ a + d * (L - 1) < n' := by
    by_contra hc
    push Not at hc
    exact hn'P ((mem_ap_iff hd hL).mpr ⟨hc.1, hc.2, hresd.trans hmP'.2.2⟩)
  intro x hx
  have hkx := (mem_filter.mp (mem_inter.mp hx).2).2
  have hxb : (x - 1) / M = (m - 1) / M := by
    rw [← hkm] at hkx; exact (Prod.mk.inj hkx).1
  rcases hout with h | h
  · left
    have e1 : (n' - 1) / M ≤ (a - 1) / M := Nat.div_le_div_right (by omega)
    have e2 : (a - 1) / M ≤ (m - 1) / M := Nat.div_le_div_right (by omega)
    omega
  · right
    have e1 : (a + d * (L - 1) - 1) / M ≤ (n' - 1) / M := Nat.div_le_div_right (by omega)
    have e2 : (m - 1) / M ≤ (a + d * (L - 1) - 1) / M := Nat.div_le_div_right (by omega)
    omega


/-- The upper bound: a trimmed set meets a progression with step dividing `q` in at most
`α|P| + #pieces + 2M` points. -/
theorem trim_upper {N M q a d L : ℕ} (hM : 1 ≤ M) (hd : 1 ≤ d) (hL : 1 ≤ L) (hdq : d ∣ q)
    (hPN : (range L).image (fun t => a + d * t) ⊆ Icc 1 N)
    {A' : Finset ℕ} {α : ℝ} (hα : 0 ≤ α)
    (hA' : ∀ k ∈ keys N M q, ((A' ∩ piece N M q k).card : ℝ) < α * (piece N M q k).card + 1) :
    ((A' ∩ (range L).image (fun t => a + d * t)).card : ℝ) ≤
      α * ((range L).image (fun t => a + d * t)).card + (keys N M q).card + 2 * M := by
  set P := (range L).image (fun t => a + d * t) with hPdef
  set E := P.filter (ends M a (a + d * (L - 1))) with hE
  have hAP : A' ∩ P ⊆ Icc 1 N := inter_subset_right.trans hPN
  have hEN : E ⊆ Icc 1 N := (filter_subset _ _).trans hPN
  have hper : ∀ k ∈ keys N M q, (((A' ∩ P) ∩ piece N M q k).card : ℝ) ≤
      α * (P ∩ piece N M q k).card + 1 + (E ∩ piece N M q k).card := by
    intro k hk
    have hnn1 : (0 : ℝ) ≤ α * (P ∩ piece N M q k).card := by positivity
    have hnn2 : (0 : ℝ) ≤ (E ∩ piece N M q k).card := by positivity
    have htri := piece_trichotomy (N := N) (a := a) hM hd hL hdq k
    simp only at htri
    rw [← hPdef] at htri
    rcases htri with h | h | h
    · have hsub : (A' ∩ P) ∩ piece N M q k ⊆ A' ∩ piece N M q k := fun n hn => by
        simp only [mem_inter] at hn ⊢; exact ⟨hn.1.1, hn.2⟩
      have hc : (((A' ∩ P) ∩ piece N M q k).card : ℝ) ≤ (A' ∩ piece N M q k).card := by
        exact_mod_cast card_le_card hsub
      have hPp : P ∩ piece N M q k = piece N M q k := inter_eq_right.mpr h
      rw [hPp]
      linarith [hA' k hk]
    · have hsub : (A' ∩ P) ∩ piece N M q k ⊆ P ∩ piece N M q k := fun n hn => by
        simp only [mem_inter] at hn ⊢; exact ⟨hn.1.2, hn.2⟩
      rw [h] at hsub
      rw [subset_empty.mp hsub]
      simp only [card_empty, Nat.cast_zero]
      linarith
    · have hsub : (A' ∩ P) ∩ piece N M q k ⊆ E ∩ piece N M q k := by
        intro n hn
        obtain ⟨hn1, hn2⟩ := mem_inter.mp hn
        have hnP := (mem_inter.mp hn1).2
        exact mem_inter.mpr ⟨mem_filter.mpr ⟨hnP, h n (mem_inter.mpr ⟨hnP, hn2⟩)⟩, hn2⟩
      have : (((A' ∩ P) ∩ piece N M q k).card : ℝ) ≤ (E ∩ piece N M q k).card := by
        exact_mod_cast card_le_card hsub
      linarith
  have s1 := card_eq_sum_fib (M := M) (q := q) hAP
  have s2 := card_eq_sum_fib (M := M) (q := q) hPN
  have s3 := card_eq_sum_fib (M := M) (q := q) hEN
  simp only [filter_key_eq_inter hAP, filter_key_eq_inter hPN, filter_key_eq_inter hEN] at s1 s2 s3
  have hEc : (E.card : ℝ) ≤ 2 * M := by exact_mod_cast ends_card_le hM hPN
  calc ((A' ∩ P).card : ℝ) = ∑ k ∈ keys N M q, (((A' ∩ P) ∩ piece N M q k).card : ℝ) := by
        rw [s1]; push_cast; rfl
    _ ≤ ∑ k ∈ keys N M q, (α * (P ∩ piece N M q k).card + 1 + (E ∩ piece N M q k).card) :=
        sum_le_sum hper
    _ = α * P.card + (keys N M q).card + E.card := by
        rw [sum_add_distrib, sum_add_distrib, ← mul_sum, s2, s3]
        push_cast; simp
    _ ≤ _ := by linarith


/-- The lower bound: trimming loses at most `ηN` points per piece. -/
theorem trim_lower {N M q : ℕ} (hM : 1 ≤ M) (hq : 1 ≤ q) {A A' : Finset ℕ}
    (hA'A : A' ⊆ A) (hA : A ⊆ Icc 1 N) {η α : ℝ} (hα1 : α ≤ 1) (hη : 0 ≤ η)
    (hdense : DenseSetOnAPs N η α A)
    (htrim : ∀ k ∈ keys N M q, α * (piece N M q k).card ≤ (A ∩ piece N M q k).card →
        α * (piece N M q k).card ≤ (A' ∩ piece N M q k).card) :
    α * N - (keys N M q).card * (η * N) ≤ A'.card := by
  have hA' : A' ⊆ Icc 1 N := hA'A.trans hA
  have hηN : 0 ≤ η * N := by positivity
  have hper : ∀ k ∈ keys N M q,
      α * (piece N M q k).card - η * N ≤ ((A' ∩ piece N M q k).card : ℝ) := by
    intro k hk
    by_cases hlong : η * N ≤ (piece N M q k).card
    · have hne : (piece N M q k).Nonempty := by
        obtain ⟨n, hn, rfl⟩ := mem_image.mp hk
        exact ⟨n, mem_filter.mpr ⟨hn, rfl⟩⟩
      have := htrim k hk (hdense _ (piece_isAPIn hM hq k hne) hlong)
      linarith
    · push Not at hlong
      have hc : (0 : ℝ) ≤ (piece N M q k).card := by positivity
      have : α * (piece N M q k).card ≤ (piece N M q k).card := by nlinarith
      have : (0 : ℝ) ≤ ((A' ∩ piece N M q k).card : ℝ) := by positivity
      linarith
  have s1 := card_eq_sum_fib (M := M) (q := q) hA'
  simp only [filter_key_eq_inter hA'] at s1
  have s2 : ∑ k ∈ keys N M q, ((piece N M q k).card : ℝ) = N := by
    exact_mod_cast sum_card_piece
  calc α * N - (keys N M q).card * (η * N)
      = ∑ k ∈ keys N M q, (α * (piece N M q k).card - η * N) := by
        rw [sum_sub_distrib, ← mul_sum, s2]; simp
    _ ≤ ∑ k ∈ keys N M q, ((A' ∩ piece N M q k).card : ℝ) := sum_le_sum hper
    _ = A'.card := by rw [s1]; push_cast; rfl

theorem rep_mono {A A' B : Finset ℕ} (h : A' ⊆ A) (n : ℕ) : rep A' B n ≤ rep A B n := by
  unfold rep
  apply card_le_card
  intro p hp
  simp only [mem_filter, mem_product] at hp ⊢
  exact ⟨⟨h hp.1.1, hp.1.2⟩, hp.2⟩


/-! ### Section 4.1, the core case `ε/4 ≤ α ≤ 1/2 − 3ε` -/

set_option maxHeartbeats 1000000 in
theorem prop33_core (H : Thm41) (ε : ℝ) (hε0 : 0 < ε) (hε1 : ε ≤ 1 / 100) :
    ∃ η > (0 : ℝ), ∃ N₀ : ℕ, ∀ (N : ℕ) (α : ℝ), N₀ ≤ N → ε / 4 ≤ α → α ≤ 1 / 2 - 3 * ε →
      ∀ A B : Finset ℕ, A ⊆ Icc 1 N → B ⊆ Icc 1 N →
      DenseSetOnAPs N η α A → DenseSetOnAPs N η α B →
      (4 * α - ε) * N ≤ (popular N η A B).card := by
  obtain ⟨δ, hδ, hT⟩ := H (ε / 2) (by linarith) (by linarith)
  set K : ℕ := ⌈2 / δ⌉₊ + 1 with hK
  set q : ℕ := K.factorial with hqdef
  have hq : 1 ≤ q := Nat.factorial_pos K
  have hq' : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hεδ : 0 < ε * δ := mul_pos hε0 hδ
  set C : ℝ := (4 / (ε * δ) + 1) * q with hC
  have hC1 : 1 ≤ C := by
    have : 0 ≤ 4 / (ε * δ) := by positivity
    nlinarith
  set η : ℝ := min (ε / (8 * C)) (ε * δ / 8) with hηdef
  have hη : 0 < η := lt_min (by positivity) (by positivity)
  have hη1 : η ≤ ε / (8 * C) := min_le_left _ _
  have hη2 : η ≤ ε * δ / 8 := min_le_right _ _
  have hηC : C * η ≤ ε / 8 := by
    calc C * η ≤ C * (ε / (8 * C)) := by gcongr
      _ = ε / 8 := by field_simp
  have hηle1 : η ≤ 1 := by
    have : ε / (8 * C) ≤ ε / 8 := by
      apply div_le_div_of_nonneg_left hε0.le (by norm_num) (by linarith)
    linarith
  refine ⟨η, hη, ⌈(C + 2) / (ε * δ) + 2 / δ⌉₊ + 1, ?_⟩
  intro N α hN hα0 hα1 A B hA hB hdA hdB
  -- size of N
  have hNr : (C + 2) / (ε * δ) + 2 / δ < N := by
    have := Nat.le_ceil ((C + 2) / (ε * δ) + 2 / δ)
    have : ((⌈(C + 2) / (ε * δ) + 2 / δ⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
    push_cast at this
    linarith
  have hpos1 : 0 ≤ (C + 2) / (ε * δ) := by positivity
  have hpos2 : 0 ≤ 2 / δ := by positivity
  have hNpos : (0 : ℝ) < N := by linarith
  have hN1 : 1 ≤ N := by exact_mod_cast hNpos
  have hδN : 2 < δ * N := by
    have : 2 / δ < N := by linarith
    rwa [div_lt_iff₀ hδ, mul_comm] at this
  have hεδN : C + 2 < ε * δ * N := by
    have : (C + 2) / (ε * δ) < N := by linarith
    rwa [div_lt_iff₀ hεδ, mul_comm] at this
  -- blocks
  set M : ℕ := ⌊ε * δ * N / 4⌋₊ + 1 with hMdef
  have hM : 1 ≤ M := Nat.le_add_left 1 _
  have hMr : ε * δ * N / 4 < M := by
    have := Nat.lt_floor_add_one (ε * δ * N / 4)
    rw [hMdef]; push_cast; exact this
  have hMr2 : (M : ℝ) ≤ ε * δ * N / 4 + 1 := by
    rw [hMdef]; push_cast
    have := Nat.floor_le (show 0 ≤ ε * δ * N / 4 by positivity)
    linarith
  have hkeys : ((keys N M q).card : ℝ) ≤ C := by
    have h1 : ((keys N M q).card : ℝ) ≤ ((N / M + 1) * q : ℕ) := by
      exact_mod_cast keys_card_le hM hq
    have h2 : ((N / M : ℕ) : ℝ) ≤ 4 / (ε * δ) := by
      have hMpos : (0 : ℝ) < M := by exact_mod_cast hM
      calc ((N / M : ℕ) : ℝ) ≤ (N : ℝ) / M := Nat.cast_div_le
        _ ≤ 4 / (ε * δ) := by
          rw [div_le_div_iff₀ hMpos hεδ]
          nlinarith
    push_cast at h1
    calc _ ≤ _ := h1
      _ ≤ (4 / (ε * δ) + 1) * q := by gcongr
  -- trimming A
  obtain ⟨A', hA'A, htrim⟩ := exists_trim N M q A hA α (by linarith)
  have hA'N : A' ⊆ Icc 1 N := hA'A.trans hA
  have hlow := trim_lower hM hq hA'A hA (by linarith) hη.le hdA (fun k hk => (htrim k hk).2)
  have hA'big : (α - ε / 8) * N ≤ A'.card := by
    have : ((keys N M q).card : ℝ) * (η * N) ≤ ε / 8 * N := by
      have h0 : (0 : ℝ) ≤ (keys N M q).card := by positivity
      calc ((keys N M q).card : ℝ) * (η * N) ≤ C * (η * N) := by
            apply mul_le_mul_of_nonneg_right hkeys; positivity
        _ = C * η * N := by ring
        _ ≤ ε / 8 * N := by gcongr
    linarith
  have hBbig : α * N ≤ B.card := by
    have := hdB (Icc 1 N) (isAPIn_Icc hN1 le_rfl) (by simp; nlinarith)
    rw [inter_eq_left.mpr hB] at this
    simpa using this
  -- popular sums transfer
  have hpop : popular N δ A' B ⊆ popular N η A B := by
    intro n hn
    simp only [popular, mem_filter, mem_range] at hn ⊢
    refine ⟨hn.1, ?_⟩
    have hmaxAB : ((max A.card B.card : ℕ) : ℝ) ≤ N := by
      have h1 : A.card ≤ N := by simpa using card_le_card hA
      have h2 : B.card ≤ N := by simpa using card_le_card hB
      exact_mod_cast max_le h1 h2
    have hmax' : (A'.card : ℝ) ≤ ((max A'.card B.card : ℕ) : ℝ) := by
      exact_mod_cast le_max_left _ _
    have hrep : (rep A' B n : ℝ) ≤ rep A B n := by exact_mod_cast rep_mono hA'A n
    have e1 : η * ((max A.card B.card : ℕ) : ℝ) ≤ η * N := by gcongr
    have e2 : η * N ≤ δ * (ε / 8 * N) := by
      have : η * N ≤ ε * δ / 8 * N := by gcongr
      linarith
    have e3 : δ * (ε / 8 * N) ≤ δ * A'.card := by
      apply mul_le_mul_of_nonneg_left _ hδ.le
      nlinarith
    have e4 : δ * (A'.card : ℝ) ≤ δ * ((max A'.card B.card : ℕ) : ℝ) := by gcongr
    linarith [hn.2]
  by_contra hcon
  push Not at hcon
  have hS : ((popular N δ A' B).card : ℝ) ≤ 4 * (min A'.card B.card : ℕ) - ε / 2 * N := by
    have h1 : ((popular N δ A' B).card : ℝ) ≤ (popular N η A B).card := by
      exact_mod_cast card_le_card hpop
    have h2 : (α - ε / 8) * N ≤ ((min A'.card B.card : ℕ) : ℝ) := by
      rcases le_total A'.card B.card with h | h
      · rw [min_eq_left h]; exact hA'big
      · rw [min_eq_right h]; nlinarith
    linarith
  obtain ⟨P, hP, hPlen, hPdens⟩ := hT N A' B hA'N hB hS
  obtain ⟨a, d, L, hd, hL, rfl, hPN⟩ := hP
  -- the step divides q
  have hcardL : ((range L).image (fun t => a + d * t)).card ≤ L := card_image_le.trans (by simp)
  have hLr : δ * N ≤ L := by
    have : (((range L).image (fun t => a + d * t)).card : ℝ) ≤ L := by exact_mod_cast hcardL
    linarith
  have htop := hPN (a + d * (L - 1)) (mem_image.mpr ⟨L - 1, mem_range.mpr (by omega), rfl⟩)
  have hbot := hPN (a + d * 0) (mem_image.mpr ⟨0, mem_range.mpr (by omega), rfl⟩)
  have hdK : d ≤ K := by
    by_contra hdK
    push Not at hdK
    have hd' : (2 / δ : ℝ) < d := by
      have : ((K : ℕ) : ℝ) < d := by exact_mod_cast hdK
      have : (2 / δ : ℝ) ≤ ⌈2 / δ⌉₊ := Nat.le_ceil _
      rw [hK] at *; push_cast at *; linarith
    have hnat : d * (L - 1) < N := by omega
    have hreal : (d : ℝ) * ((L : ℝ) - 1) < N := by
      have : ((d * (L - 1) : ℕ) : ℝ) < N := by exact_mod_cast hnat
      rw [Nat.cast_mul, Nat.cast_sub (by omega)] at this
      simpa using this
    have hL1 : δ * N / 2 ≤ (L : ℝ) - 1 := by linarith
    have : (2 / δ) * (δ * N / 2) = (N : ℝ) := by field_simp
    have : (2 / δ) * (δ * N / 2) ≤ (d : ℝ) * ((L : ℝ) - 1) := by
      apply mul_le_mul hd'.le hL1 (by positivity) (by positivity)
    linarith
  have hdq : d ∣ q := Nat.dvd_factorial (by omega) hdK
  -- the upper bound and the contradiction
  have hPN' : (range L).image (fun t => a + d * t) ⊆ Icc 1 N := fun n hn => by
    have := hPN n hn; exact mem_Icc.mpr this
  have hup := trim_upper hM hd hL hdq hPN' (A' := A') (by linarith : (0 : ℝ) ≤ α)
    (fun k hk => (htrim k hk).1)
  set Pc : ℝ := (((range L).image (fun t => a + d * t)).card : ℝ) with hPc
  have hdens : (1 / 2 + ε / 2 / 5) * Pc ≤ α * Pc + C + 2 * (ε * δ * N / 4 + 1) := by
    linarith [hup, hkeys, hMr2, hPdens]
  have hPc0 : δ * N ≤ Pc := hPlen
  have hP0 : 0 ≤ Pc := by rw [hPc]; positivity
  have h1 : α * Pc ≤ (1 / 2 - 3 * ε) * Pc := mul_le_mul_of_nonneg_right hα1 hP0
  have h2 : 3 * ε * (δ * N) ≤ 3 * ε * Pc := by gcongr
  have h3 : 0 ≤ ε / 2 / 5 * Pc := by positivity
  have e1 : (1 / 2 + ε / 2 / 5) * Pc = Pc / 2 + ε / 2 / 5 * Pc := by ring
  have e2 : (1 / 2 - 3 * ε) * Pc = Pc / 2 - 3 * ε * Pc := by ring
  have e3 : 3 * ε * (δ * N) = 3 * (ε * δ * N) := by ring
  have e4 : 2 * (ε * δ * N / 4 + 1) = (ε * δ * N) / 2 + 2 := by ring
  rw [e1] at hdens
  rw [e2] at h1
  rw [e3] at h2
  rw [e4] at hdens
  linarith


theorem denseSetOnAPs_mono {N : ℕ} {η α α' : ℝ} {A : Finset ℕ} (h : α' ≤ α)
    (hA : DenseSetOnAPs N η α A) : DenseSetOnAPs N η α' A := fun P hP hl =>
  (mul_le_mul_of_nonneg_right h (by positivity)).trans (hA P hP hl)

/-! ### Section 4.1 in full: Theorem 4.1 implies Proposition 3.3 -/

/-- **MMS section 4.1, Theorem 4.1 implies Proposition 3.3**, corrected forms, zero sorry.
The reductions: `ε` is replaced by `e = min(ε, 1/100)/13`; `α < e/4` is trivial; for
`α > 1/2 − 3e` we lower `α` to `1/2 − 3e` and lose `13e ≤ ε`. -/
theorem prop33_of_thm41 (H : Thm41) : Prop33 := by
  intro ε hε
  set e : ℝ := min ε (1 / 100) / 13 with he
  have hm0 : 0 < min ε (1 / 100) := lt_min hε (by norm_num)
  have hm1 : min ε (1 / 100) ≤ ε := min_le_left _ _
  have hm2 : min ε (1 / 100) ≤ 1 / 100 := min_le_right _ _
  have he0 : 0 < e := by positivity
  have he1 : e ≤ 1 / 100 := by rw [he]; linarith
  have he13 : 13 * e ≤ ε := by rw [he]; linarith
  obtain ⟨η, hη, N₀, h⟩ := prop33_core H e he0 he1
  refine ⟨η, hη, N₀, ?_⟩
  intro N α hN hα0 hα1 A B hA hB hdA hdB
  have hc : (0 : ℝ) ≤ (popular N η A B).card := by positivity
  have hNn : (0 : ℝ) ≤ N := by positivity
  by_cases hlow : α < e / 4
  · have : (4 * α - ε) * N ≤ 0 := by
      apply mul_nonpos_of_nonpos_of_nonneg _ hNn; linarith
    linarith
  push Not at hlow
  by_cases hmid : α ≤ 1 / 2 - 3 * e
  · have := h N α hN hlow hmid A B hA hB hdA hdB
    have : (4 * α - ε) * N ≤ (4 * α - e) * N := by
      apply mul_le_mul_of_nonneg_right _ hNn; linarith
    linarith
  · push Not at hmid
    have hα' : e / 4 ≤ 1 / 2 - 3 * e := by linarith
    have := h N (1 / 2 - 3 * e) hN hα' le_rfl A B hA hB
      (denseSetOnAPs_mono hmid.le hdA) (denseSetOnAPs_mono hmid.le hdB)
    have : (4 * α - ε) * N ≤ (4 * (1 / 2 - 3 * e) - e) * N := by
      apply mul_le_mul_of_nonneg_right _ hNn; linarith
    linarith

/-- Proposition 3.3 from the cited Theorem 4.1 only. -/
theorem mms_prop33_of_thm41 : Prop33 := prop33_of_thm41 mms_thm41

/-- Proposition 3.2 from the cited Theorem 4.1 only, through `prop32_of_prop33`
in MMSProp32.lean. -/
theorem mms_prop32_of_thm41 : Prop32 := prop32_of_prop33 mms_prop33_of_thm41

/-- Both results are conditional on Theorem 4.1 and on nothing else. -/
theorem prop32_of_thm41 (H : Thm41) : Prop32 := prop32_of_prop33 (prop33_of_thm41 H)

end LeanLab.Ternary.MMS
