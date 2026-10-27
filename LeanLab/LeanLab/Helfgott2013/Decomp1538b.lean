/-
Unit U-1538, run 20261026T0403Z-9802. P0001, H. A. Helfgott, The ternary Goldbach conjecture
is true, arXiv 1312.7748v2.
AI wrote this Lean code, Claude, checked only by the Lean kernel. Binary Goldbach is OPEN.

DECOMPOSE, part b: Proposition 6.2 on p. 47, proof on p. 48, in an abstract measure form.
The proof splits the minor arcs `(R/Z) \ M_{δ0,r0}` into the shells `M_{δ0,r+1} \ M_{δ0,r}`,
`r0 ≤ r < r1`, plus the far part `(R/Z) \ M_{δ0,r1}`, bounds `|S2|` on each shell by `g(r)`,
and feeds the shell masses `f(r)` to Lemma 6.1 of part a.

Here the space is any measurable space with a measure `μ`; `w ≥ 0` plays
`|S1|² / ∑ |a_n|²`, of total mass `1` by Parseval, and `s ≥ 0` plays `|S2|`. The sets `M r`
are any increasing family; part c specialises to the arcs of (3.5). `prop62` is an ASSEMBLY,
CONDITIONAL ON the leaves of parts a and b.

Encoding choices. The paper's `r1` is real; the proof sums `f(r)` over integers
`r0 ≤ r ≤ r1` with `f(r1)` the far part, so `r1` is taken to be a natural number here; see the
QUESTION in PROGRESS.md. The paper's side condition `δ0 ≤ x / 2 r1²` only prevents overlap of
arcs and is not used by the proof, since shells are set differences; it is dropped.
Hypotheses (6.4) and (6.5) are asked only at integers `r`, which is weaker than the paper.
-/
import Mathlib
import LeanLab.Helfgott2013.Decomp1538a

namespace LeanLab.Helfgott2013.U1538

open Finset MeasureTheory intervalIntegral

variable {X : Type*} [MeasurableSpace X]

/-- The shells of the proof of Prop. 6.2, p. 48: for `r < r1` the set `M (r+1) \ M r`, and
for `r ≥ r1` the far part `(M r)ᶜ`, used at `r = r1`. -/
def piece (M : ℕ → Set X) (r1 r : ℕ) : Set X := if r < r1 then M (r + 1) \ M r else (M r)ᶜ

/-! ### Leaves -/

/-- LEAF. Unit U-1538. Each shell is measurable when every `M r` is; p. 48, the sets in the
definition of `f(r)`. -/
theorem piece_measurable {M : ℕ → Set X} (hM : ∀ r, MeasurableSet (M r)) (r1 r : ℕ) :
    MeasurableSet (piece M r1 r) := by sorry

/-- LEAF. Unit U-1538. For increasing `M`, the shells with index in `[r0, r1]` are pairwise
disjoint; p. 48, proof of Prop. 6.2. -/
theorem piece_pairwise_disjoint {M : ℕ → Set X} (hmono : Monotone M) (r0 r1 : ℕ) :
    Set.Pairwise (↑(Icc r0 r1) : Set ℕ) (Function.onFun Disjoint (piece M r1)) := by sorry

/-- LEAF. Unit U-1538. For increasing `M` and `r0 ≤ r1`, the shells with index in `[r0, r1]`
cover exactly the complement of `M r0`; p. 48, the first display of the proof of Prop. 6.2. -/
theorem piece_iUnion {M : ℕ → Set X} (hmono : Monotone M) {r0 r1 : ℕ} (hr : r0 ≤ r1) :
    ⋃ r ∈ Icc r0 r1, piece M r1 r = (M r0)ᶜ := by sorry

/-- LEAF. Unit U-1538. A nonnegative integrable `w` times a nonnegative a.e. bounded measurable
`s` is integrable; p. 48, the integrand `|S1(α)|² |S2(α)|`, `S2` continuous on `R/Z`. -/
theorem integrable_mul_bdd {μ : Measure X} {w s : X → ℝ} (hwi : Integrable w μ)
    (hsm : AEStronglyMeasurable s μ) (hs0 : ∀ y, 0 ≤ s y) {C : ℝ}
    (hsC : ∀ᵐ y ∂μ, s y ≤ C) : Integrable (fun y => w y * s y) μ := by sorry

/-- LEAF. Unit U-1538. On the shell `r ≤ r1`, which lies outside `M r`, a bound `s ≤ G` off
`M r` gives `∫_{shell} w s ≤ G ∫_{shell} w` for `w ≥ 0`; p. 48, "Then, by (6.5)". -/
theorem piece_bound {μ : Measure X} {w s : X → ℝ} (hw0 : ∀ y, 0 ≤ w y) (hwi : Integrable w μ)
    (hsm : AEStronglyMeasurable s μ) (hs0 : ∀ y, 0 ≤ s y) {C : ℝ} (hsC : ∀ᵐ y ∂μ, s y ≤ C)
    {M : ℕ → Set X} (hM : ∀ r, MeasurableSet (M r)) (r1 r : ℕ) {G : ℝ}
    (hG : ∀ᵐ y ∂μ, y ∉ M r → s y ≤ G) :
    ∫ y in piece M r1 r, w y * s y ∂μ ≤ G * ∫ y in piece M r1 r, w y ∂μ := by sorry

/-- LEAF. Unit U-1538. For measurable `A ⊆ B` and integrable `w`,
`∫_{B \ A} w = ∫_B w - ∫_A w`; p. 48, the shell masses in (6.8). -/
theorem setIntegral_diff_of_subset {μ : Measure X} {w : X → ℝ} (hwi : Integrable w μ)
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (hAB : A ⊆ B) :
    ∫ y in B \ A, w y ∂μ = (∫ y in B, w y ∂μ) - ∫ y in A, w y ∂μ := by sorry

/-- LEAF. Unit U-1538. For measurable `A` and integrable `w`,
`∫_{Aᶜ} w = ∫ w - ∫_A w`; p. 48, the far part `(R/Z) \ M_{δ0,r1}` and the line
`= 1 - I0 = H(r1) - I0`. -/
theorem setIntegral_compl' {μ : Measure X} {w : X → ℝ} (hwi : Integrable w μ) {A : Set X}
    (hA : MeasurableSet A) : ∫ y in Aᶜ, w y ∂μ = (∫ y, w y ∂μ) - ∫ y in A, w y ∂μ := by sorry

/-- LEAF. Unit U-1538. For `g ≥ 0` non-increasing on `[r0, r1]`, the running maximum of
`g` over the integers `n, ..., r1` is `g(n)` for `r0 ≤ n ≤ r1`; p. 48, last line of the
proof of Prop. 6.2, `max_{r ≥ r0} g(r) = g(r0)`. -/
theorem hmax_of_antitoneOn (g : ℝ → ℝ) {r0 r1 n : ℕ}
    (hg0 : ∀ u ∈ Set.Icc (r0 : ℝ) r1, 0 ≤ g u) (hganti : AntitoneOn g (Set.Icc (r0 : ℝ) r1))
    (hn0 : r0 ≤ n) (hn1 : n ≤ r1) : hmax (fun r : ℕ => g r) r1 n = g n := by sorry

/-- LEAF. Unit U-1538. For `g ≥ 0` non-increasing on `[r0, r1]` and `H' ≥ 0` integrable there,
`∫_{r0}^{r1} (max_{r ≥ u} g(r)) H'(u) du ≤ ∫_{r0}^{r1} g(u) H'(u) du`, since
`max_{r ≥ u} g(r) = g(⌈u⌉) ≤ g(u)`; p. 48, last line of the proof of Prop. 6.2. -/
theorem integral_hmax_ceil_le (g H' : ℝ → ℝ) {r0 r1 : ℕ} (hr : r0 ≤ r1)
    (hg0 : ∀ u ∈ Set.Icc (r0 : ℝ) r1, 0 ≤ g u) (hganti : AntitoneOn g (Set.Icc (r0 : ℝ) r1))
    (hH'0 : ∀ u ∈ Set.Icc (r0 : ℝ) r1, 0 ≤ H' u)
    (hH'i : IntervalIntegrable H' volume (r0 : ℝ) r1) :
    ∫ u in (r0 : ℝ)..r1, hmax (fun r : ℕ => g r) r1 ⌈u⌉₊ * H' u ≤
      ∫ u in (r0 : ℝ)..r1, g u * H' u := by sorry

/-! ### Assemblies, CONDITIONAL ON the leaves of parts a and b -/

/-- ASSEMBLY, CONDITIONAL ON the leaves. The integral over the complement of `M r0` is the sum
of the integrals over the shells `r0 ≤ r ≤ r1`; p. 48. -/
theorem integral_compl_eq_sum_pieces {μ : Measure X} {φ : X → ℝ} (hφ : Integrable φ μ)
    {M : ℕ → Set X} (hM : ∀ r, MeasurableSet (M r)) (hmono : Monotone M) {r0 r1 : ℕ}
    (hr : r0 ≤ r1) :
    ∫ y in (M r0)ᶜ, φ y ∂μ = ∑ r ∈ Icc r0 r1, ∫ y in piece M r1 r, φ y ∂μ := by
  rw [← piece_iUnion hmono hr]
  exact integral_biUnion_finset _ (fun r _ => piece_measurable hM r1 r)
    (piece_pairwise_disjoint hmono r0 r1) fun r _ => hφ.integrableOn

/-- ASSEMBLY, CONDITIONAL ON the leaves. Partial sums of shell masses: for `r0 ≤ n < r1`,
`∑_{r0 ≤ r ≤ n} f(r) = ∫_{M(n+1)} w - ∫_{M r0} w`; p. 48, display (6.8). -/
theorem sum_pieces_partial {μ : Measure X} {w : X → ℝ} (hwi : Integrable w μ)
    {M : ℕ → Set X} (hM : ∀ r, MeasurableSet (M r)) (hmono : Monotone M) {r0 r1 : ℕ} :
    ∀ n, r0 ≤ n → n < r1 →
      ∑ r ∈ Icc r0 n, ∫ y in piece M r1 r, w y ∂μ =
        (∫ y in M (n + 1), w y ∂μ) - ∫ y in M r0, w y ∂μ := by
  intro n hn
  induction n, hn using Nat.le_induction with
  | base =>
    intro h1
    rw [Finset.Icc_self, Finset.sum_singleton, piece, if_pos h1]
    exact setIntegral_diff_of_subset hwi (hM _) (hM _) (hmono (Nat.le_succ _))
  | succ k hk ih =>
    intro h1
    rw [Finset.sum_Icc_succ_top (by omega), ih (by omega), piece, if_pos h1,
      setIntegral_diff_of_subset hwi (hM _) (hM _) (hmono (Nat.le_succ _))]
    ring

/-- ASSEMBLY, CONDITIONAL ON the leaves. Total of the shell masses: if `∫ w = 1` then
`∑_{r0 ≤ r ≤ r1} f(r) = 1 - I0`; p. 48, the line `= 1 - I0 = H(r1) - I0`. -/
theorem sum_pieces_total {μ : Measure X} {w : X → ℝ} (hwi : Integrable w μ)
    (hw1 : ∫ y, w y ∂μ = 1) {M : ℕ → Set X} (hM : ∀ r, MeasurableSet (M r))
    (hmono : Monotone M) {r0 r1 : ℕ} (hr : r0 ≤ r1) :
    ∑ r ∈ Icc r0 r1, ∫ y in piece M r1 r, w y ∂μ = 1 - ∫ y in M r0, w y ∂μ := by
  rcases Nat.eq_or_lt_of_le hr with h | h
  · subst h
    rw [Finset.Icc_self, Finset.sum_singleton, piece, if_neg (lt_irrefl _),
      setIntegral_compl' hwi (hM _), hw1]
  · obtain ⟨k, rfl⟩ : ∃ k, r1 = k + 1 := ⟨r1 - 1, by omega⟩
    rw [Finset.sum_Icc_succ_top (by omega),
      sum_pieces_partial hwi hM hmono k (by omega) (by omega), piece, if_neg (lt_irrefl _),
      setIntegral_compl' hwi (hM _), hw1]
    ring

/-- ASSEMBLY, CONDITIONAL ON the leaves of parts a and b. Proposition 6.2, p. 47, abstract
form. Let `w ≥ 0` with `∫ w = 1`, `0 ≤ s ≤ C` a.e., `M` increasing measurable, `r0 ≤ r1`
naturals, `H` non-decreasing with density `H'` on `[r0, r1]`, `H(r1) = 1`, and
(6.4) `∫_{M(r+1)} w ≤ H(r)`, (6.5) `s ≤ g(r)` off `M r`, for `r0 ≤ r ≤ r1`, with `g ≥ 0`
non-increasing on `[r0, r1]`. Then (6.6):
`∫_{(M r0)ᶜ} w s ≤ g(r0) (H(r0) - I0) + ∫_{r0}^{r1} g(r) H'(r) dr`, `I0 = ∫_{M r0} w` as in
(6.7). -/
theorem prop62 {μ : Measure X} {w s : X → ℝ} (hw0 : ∀ y, 0 ≤ w y) (hwi : Integrable w μ)
    (hw1 : ∫ y, w y ∂μ = 1) (hsm : AEStronglyMeasurable s μ) (hs0 : ∀ y, 0 ≤ s y) {C : ℝ}
    (hsC : ∀ᵐ y ∂μ, s y ≤ C) {M : ℕ → Set X} (hM : ∀ r, MeasurableSet (M r))
    (hmono : Monotone M) {r0 r1 : ℕ} (hr : r0 ≤ r1) {H H' g : ℝ → ℝ}
    (hH : NondecFTC H H' r0 r1) (hH1 : H r1 = 1)
    (h64 : ∀ r : ℕ, r0 ≤ r → r ≤ r1 → ∫ y in M (r + 1), w y ∂μ ≤ H r)
    (hg0 : ∀ u ∈ Set.Icc (r0 : ℝ) r1, 0 ≤ g u) (hganti : AntitoneOn g (Set.Icc (r0 : ℝ) r1))
    (h65 : ∀ r : ℕ, r0 ≤ r → r ≤ r1 → ∀ᵐ y ∂μ, y ∉ M r → s y ≤ g r) :
    ∫ y in (M r0)ᶜ, w y * s y ∂μ ≤
      g r0 * (H r0 - ∫ y in M r0, w y ∂μ) + ∫ u in (r0 : ℝ)..r1, g u * H' u := by
  set I0 := ∫ y in M r0, w y ∂μ with hI0
  set f : ℕ → ℝ := fun r => ∫ y in piece M r1 r, w y ∂μ with hfdef
  have hf : ∀ n, 0 ≤ f n := fun n =>
    setIntegral_nonneg (piece_measurable hM r1 n) fun y _ => hw0 y
  have hint := integrable_mul_bdd hwi hsm hs0 hsC
  have e1 := integral_compl_eq_sum_pieces hint hM hmono hr
  have e2 : ∑ r ∈ Icc r0 r1, ∫ y in piece M r1 r, w y * s y ∂μ ≤
      ∑ r ∈ Icc r0 r1, f r * (fun r : ℕ => g r) r := by
    refine Finset.sum_le_sum fun r hr' => ?_
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hr'
    have := piece_bound hw0 hwi hsm hs0 hsC hM r1 r (h65 r h1 h2)
    simp only [hfdef]
    linarith [mul_comm (g r) (∫ y in piece M r1 r, w y ∂μ)]
  have hF : NondecFTC (fun x => H x - I0) H' r0 r1 := by
    obtain ⟨h1, h2, h3⟩ := hH
    refine ⟨h1, h2, fun x y hx hxy hy => ?_⟩
    rw [← h3 x y hx hxy hy]
    ring
  have h61 : ∀ n ∈ Icc r0 r1, ∑ m ∈ Icc r0 n, f m ≤ (fun x => H x - I0) (n : ℝ) := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
    rcases Nat.lt_or_ge n r1 with h | h
    · rw [sum_pieces_partial hwi hM hmono n h1 h]
      linarith [h64 n h1 h2]
    · have hn1 : n = r1 := le_antisymm h2 h
      subst hn1
      rw [sum_pieces_total hwi hw1 hM hmono hr]
      show _ ≤ H n - I0
      linarith [hH1, hI0]
  have hgN : ∀ n ∈ Icc r0 r1, 0 ≤ (fun r : ℕ => g r) n := by
    intro n hn
    obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp hn
    exact hg0 n ⟨by exact_mod_cast h1, by exact_mod_cast h2⟩
  have L := lemma61 hr f (fun r : ℕ => g r) hf hgN (fun x => H x - I0) H' hF h61
  rw [hmax_of_antitoneOn g hg0 hganti le_rfl hr] at L
  have B6 := integral_hmax_ceil_le g H' hr hg0 hganti hH.1 hH.2.1
  rw [e1]
  linarith

end LeanLab.Helfgott2013.U1538
