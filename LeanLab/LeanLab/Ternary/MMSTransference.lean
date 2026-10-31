/-
Matomaki-Maynard-Shao 2016, the transference principle, sections 2 to 4.
P0028, arXiv 1610.02017 v2, Proc. LMS 2017, doi 10.1112/plms.12040.
Theorem 2.1, Propositions 3.1, 3.2, 3.3 and Theorem 4.1 are stated here as Props.
Section 4.1 and 4.2 say small N is "trivial" or "obvious"; it is not: Propositions 3.2
and 3.3 are false as printed for N = 2 and N = 1. The corrected forms add N ≥ N₀(ε).
AI-written Lean code, Claude, 2026-10-17. Checked only by the Lean kernel.
Ternary Goldbach is a theorem, Helfgott 2013; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Ternary.AlmostEqual

namespace LeanLab.Ternary.MMS

open Finset

/-! ### Arithmetic progressions in `[N] = {1, …, N}`, averages, convolution -/

/-- `P` is an arithmetic progression `{a, a + d, …, a + (L − 1) d}` with `d ≥ 1`, `L ≥ 1`,
inside `[N]`. -/
def IsAPIn (N : ℕ) (P : Finset ℕ) : Prop :=
  ∃ a d L : ℕ, 1 ≤ d ∧ 1 ≤ L ∧ P = (range L).image (fun k => a + d * k) ∧
    ∀ n ∈ P, 1 ≤ n ∧ n ≤ N

/-- The average `E_{n ∈ P} f(n)`. -/
noncomputable def avg (f : ℕ → ℝ) (P : Finset ℕ) : ℝ := (∑ n ∈ P, f n) / P.card

/-- Hypothesis of Propositions 3.1 (1) and 3.2: average at least `1/3 + ε` on every
progression `P ⊂ [N]` with `|P| ≥ ηN`. -/
def DenseOnAPs (N : ℕ) (η ε : ℝ) (f : ℕ → ℝ) : Prop :=
  ∀ P : Finset ℕ, IsAPIn N P → η * N ≤ P.card → 1 / 3 + ε ≤ avg f P

/-- `f₁ ∗ f₂ ∗ f₃ (n)` for functions on `[N]`: the sum over `a + b + c = n`, `a, b, c ∈ [N]`. -/
def conv3 (N : ℕ) (f₁ f₂ f₃ : ℕ → ℝ) (n : ℕ) : ℝ :=
  ∑ a ∈ Icc 1 N, ∑ b ∈ Icc 1 N,
    if a + b < n ∧ n - (a + b) ≤ N then f₁ a * f₂ b * f₃ (n - (a + b)) else 0

/-- Values in `[0, 1]` on `[N]`. -/
def UnitValued (N : ℕ) (f : ℕ → ℝ) : Prop := ∀ n ∈ Icc 1 N, 0 ≤ f n ∧ f n ≤ 1

/-! ### Proposition 3.2, the dense case -/

/-- Proposition 3.2 exactly as printed: for any `ε > 0` there are `η, c > 0` such that for
every `N` and `f₁, f₂, f₃ : [N] → [0, 1]` dense on progressions of length `≥ ηN`,
`f₁ ∗ f₂ ∗ f₃ (n) ≥ c N²` for each `n ∈ [N/2, N]`. -/
def Prop32Printed : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η > (0 : ℝ), ∃ c > (0 : ℝ), ∀ (N : ℕ) (f₁ f₂ f₃ : ℕ → ℝ),
    UnitValued N f₁ → UnitValued N f₂ → UnitValued N f₃ →
    DenseOnAPs N η ε f₁ → DenseOnAPs N η ε f₂ → DenseOnAPs N η ε f₃ →
    ∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N → c * (N : ℝ) ^ 2 ≤ conv3 N f₁ f₂ f₃ n

/-- Proposition 3.2 with the large-`N` condition the proof in section 4.2 actually uses. -/
def Prop32 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η > (0 : ℝ), ∃ c > (0 : ℝ), ∃ N₀ : ℕ, ∀ (N : ℕ) (f₁ f₂ f₃ : ℕ → ℝ),
    N₀ ≤ N →
    UnitValued N f₁ → UnitValued N f₂ → UnitValued N f₃ →
    DenseOnAPs N η ε f₁ → DenseOnAPs N η ε f₂ → DenseOnAPs N η ε f₃ →
    ∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N → c * (N : ℝ) ^ 2 ≤ conv3 N f₁ f₂ f₃ n

/-- P0028 Proposition 3.2, corrected form, cited. -/
theorem mms_prop32 : Prop32 := by sorry

theorem prop32_of_printed (H : Prop32Printed) : Prop32 := by
  intro ε hε
  obtain ⟨η, hη, c, hc, h⟩ := H ε hε
  exact ⟨η, hη, c, hc, 0, fun N f₁ f₂ f₃ _ => h N f₁ f₂ f₃⟩

/-- A progression is nonempty. -/
theorem IsAPIn.card_pos {N : ℕ} {P : Finset ℕ} (h : IsAPIn N P) : 0 < P.card := by
  obtain ⟨a, d, L, -, hL, rfl, -⟩ := h
  apply Finset.card_pos.mpr
  exact ⟨a + d * 0, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr (by omega), rfl⟩⟩

theorem avg_one {P : Finset ℕ} (hP : 0 < P.card) : avg (fun _ => (1 : ℝ)) P = 1 := by
  unfold avg
  have : (P.card : ℝ) ≠ 0 := by exact_mod_cast hP.ne'
  simp [this]

theorem denseOnAPs_one (N : ℕ) (η ε : ℝ) (hε : ε ≤ 2 / 3) :
    DenseOnAPs N η ε (fun _ => (1 : ℝ)) := by
  intro P hP _
  rw [avg_one hP.card_pos]
  linarith

theorem conv3_two_two (f₁ f₂ f₃ : ℕ → ℝ) : conv3 2 f₁ f₂ f₃ 2 = 0 := by
  unfold conv3
  apply Finset.sum_eq_zero
  intro a ha
  apply Finset.sum_eq_zero
  intro b hb
  rw [Finset.mem_Icc] at ha hb
  split_ifs with h
  · omega
  · rfl

/-- **Proposition 3.2 is false as printed**: take `ε = 1/3`, `N = 2`, `f₁ = f₂ = f₃ = 1`,
`n = 2 ∈ [N/2, N]`. Every hypothesis holds, but `2` is not a sum of three elements of
`[2]`, so the convolution is `0 < c N²`. The section 4.2 sentence "we may assume that N is
large enough in terms of ε, since otherwise the statement is obvious" is wrong for
`N ≤ 4`; the fix is `N ≥ N₀(ε)`, `Prop32`. -/
theorem prop32_printed_false : ¬ Prop32Printed := by
  intro H
  obtain ⟨η, -, c, hc, h⟩ := H (1 / 3) (by norm_num)
  have hu : UnitValued 2 (fun _ => (1 : ℝ)) := fun _ _ => ⟨zero_le_one, le_rfl⟩
  have hd := denseOnAPs_one 2 η (1 / 3) (by norm_num)
  have := h 2 _ _ _ hu hu hu hd hd hd 2 (by norm_num) le_rfl
  rw [conv3_two_two] at this
  norm_num at this
  linarith

/-! ### Proposition 3.3, popular sums -/

/-- `1_A ∗ 1_B (n)`, the number of `(a, b) ∈ A × B` with `a + b = n`. -/
def rep (A B : Finset ℕ) (n : ℕ) : ℕ := ((A ×ˢ B).filter (fun p => p.1 + p.2 = n)).card

/-- `S_η(A, B)` for `A, B ⊂ [N]`: the `η`-popular sums, all in `[0, 2N]`. -/
noncomputable def popular (N : ℕ) (η : ℝ) (A B : Finset ℕ) : Finset ℕ :=
  (range (2 * N + 1)).filter (fun n => η * (max A.card B.card : ℕ) ≤ (rep A B n : ℝ))

/-- `A` has density at least `α` on every progression in `[N]` of length at least `ηN`. -/
def DenseSetOnAPs (N : ℕ) (η α : ℝ) (A : Finset ℕ) : Prop :=
  ∀ P : Finset ℕ, IsAPIn N P → η * N ≤ P.card → α * P.card ≤ (A ∩ P).card

/-- Proposition 3.3 as printed. -/
def Prop33Printed : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η > (0 : ℝ), ∀ (N : ℕ) (α : ℝ), 0 ≤ α → α ≤ 1 / 2 →
    ∀ A B : Finset ℕ, A ⊆ Icc 1 N → B ⊆ Icc 1 N →
    DenseSetOnAPs N η α A → DenseSetOnAPs N η α B →
    (4 * α - ε) * N ≤ (popular N η A B).card

/-- Proposition 3.3 with `N ≥ N₀(ε)`. -/
def Prop33 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ η > (0 : ℝ), ∃ N₀ : ℕ, ∀ (N : ℕ) (α : ℝ), N₀ ≤ N → 0 ≤ α → α ≤ 1 / 2 →
    ∀ A B : Finset ℕ, A ⊆ Icc 1 N → B ⊆ Icc 1 N →
    DenseSetOnAPs N η α A → DenseSetOnAPs N η α B →
    (4 * α - ε) * N ≤ (popular N η A B).card

/-- P0028 Proposition 3.3, corrected form, cited. -/
theorem mms_prop33 : Prop33 := by sorry

theorem prop33_of_printed (H : Prop33Printed) : Prop33 := by
  intro ε hε
  obtain ⟨η, hη, h⟩ := H ε hε
  exact ⟨η, hη, 0, fun N α _ => h N α⟩

theorem popular_one_one_subset {η : ℝ} (hη : 0 < η) : popular 1 η {1} {1} ⊆ {2} := by
  intro n hn
  simp only [popular, Finset.mem_filter, Finset.mem_range] at hn
  obtain ⟨-, h⟩ := hn
  by_contra hne
  rw [Finset.mem_singleton] at hne
  have : rep {1} {1} n = 0 := by
    unfold rep
    rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro p hp
    simp only [Finset.mem_product, Finset.mem_singleton] at hp
    rw [hp.1, hp.2]
    omega
  rw [this] at h
  simp at h
  linarith

/-- **Proposition 3.3 is false as printed**: `ε = 1/2`, `N = 1`, `α = 1/2`, `A = B = {1}`.
Both sets are all of `[1]`, so every density hypothesis holds, but `S_η ⊆ {2}` has at most
one element while `(4α − ε) N = 3/2`. Section 4.1's "otherwise the assumptions imply that
A = B = [N] and the statement is trivial" is wrong for small `N`: `[N] + [N]` has only
`2N − 1` elements, below `(2 − ε) N` when `εN < 1`. The fix is `N ≥ N₀(ε)`, `Prop33`. -/
theorem prop33_printed_false : ¬ Prop33Printed := by
  intro H
  obtain ⟨η, hη, h⟩ := H (1 / 2) (by norm_num)
  have hsub : ({1} : Finset ℕ) ⊆ Icc 1 1 := by decide
  have hd : DenseSetOnAPs 1 η (1 / 2) {1} := by
    intro P hP _
    obtain ⟨a, d, L, -, -, -, hmem⟩ := hP
    have hPs : P ⊆ {1} := fun n hn => by
      have := hmem n hn
      rw [Finset.mem_singleton]; omega
    rw [Finset.inter_eq_right.mpr hPs]
    have : (0 : ℝ) ≤ P.card := by positivity
    linarith
  have h1 := h 1 (1 / 2) (by norm_num) (by norm_num) {1} {1} hsub hsub hd hd
  have h2 : (popular 1 η {1} {1}).card ≤ 1 :=
    (Finset.card_le_card (popular_one_one_subset hη)).trans (by simp)
  have h3 : ((popular 1 η {1} {1}).card : ℝ) ≤ 1 := by exact_mod_cast h2
  norm_num at h1
  linarith

/-! ### Theorem 4.1, the asymmetric Eberhard-Green-Manners input -/

/-- Theorem 4.1 exactly as printed, "for any ε > 0": if `|S_δ(A, B)| ≤ 4 min(|A|, |B|) − εN`
then `A` has density at least `1/2 + ε/5` on some progression in `[N]` of length at least `δN`. -/
def Thm41Printed : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ δ > (0 : ℝ), ∀ (N : ℕ) (A B : Finset ℕ), A ⊆ Icc 1 N → B ⊆ Icc 1 N →
    ((popular N δ A B).card : ℝ) ≤ 4 * (min A.card B.card : ℕ) - ε * N →
    ∃ P : Finset ℕ, IsAPIn N P ∧ δ * N ≤ P.card ∧ (1 / 2 + ε / 5) * P.card ≤ (A ∩ P).card

/-- Theorem 4.1 for `0 < ε < 1`, the range the paper uses, with `ε/2` in section 4.1. -/
def Thm41 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ δ > (0 : ℝ), ∀ (N : ℕ) (A B : Finset ℕ),
    A ⊆ Icc 1 N → B ⊆ Icc 1 N →
    ((popular N δ A B).card : ℝ) ≤ 4 * (min A.card B.card : ℕ) - ε * N →
    ∃ P : Finset ℕ, IsAPIn N P ∧ δ * N ≤ P.card ∧ (1 / 2 + ε / 5) * P.card ≤ (A ∩ P).card

/-- P0028 Theorem 4.1 for `ε < 1`, cited; the paper attributes it to Eberhard-Green-Manners.
An earlier draft of this file cited the printed form, which is inconsistent, see below. -/
theorem mms_thm41 : Thm41 := by sorry

theorem thm41_of_printed (H : Thm41Printed) : Thm41 := fun ε hε _ => H ε hε

/-- **Theorem 4.1 as printed is false for `ε > 5/2`**: with `ε = 3`, `N = 1`, `A = B = {1}`,
`|S_δ| ≤ 1 = 4 − 3`, so the hypothesis holds, but density `1/2 + 3/5 > 1` is impossible.
Harmless for the paper, which applies it with small `ε`; it matters for us, since citing
the printed form with `sorry` would let Lean prove `False`. Found by the VERIFY subagent. -/
theorem thm41_printed_false : ¬ Thm41Printed := by
  intro H
  obtain ⟨δ, hδ, h⟩ := H 3 (by norm_num)
  have hsub : ({1} : Finset ℕ) ⊆ Icc 1 1 := by decide
  have h2 : (popular 1 δ {1} {1}).card ≤ 1 :=
    (Finset.card_le_card (popular_one_one_subset hδ)).trans (by simp)
  have h3 : ((popular 1 δ {1} {1}).card : ℝ) ≤ 1 := by exact_mod_cast h2
  obtain ⟨P, hP, -, hd⟩ := h 1 {1} {1} hsub hsub (by norm_num; linarith)
  have hpos : (0 : ℝ) < P.card := by exact_mod_cast hP.card_pos
  have hle : (({1} : Finset ℕ) ∩ P).card ≤ P.card := Finset.card_le_card Finset.inter_subset_right
  have hle' : ((({1} : Finset ℕ) ∩ P).card : ℝ) ≤ P.card := by exact_mod_cast hle
  linarith

/-! ### Proposition 3.1, the transference principle -/

/-- `f̂(γ) = Σ_{n ∈ [N]} f(n) e(−nγ)`. -/
noncomputable def fhat (N : ℕ) (f : ℕ → ℝ) (γ : ℝ) : ℂ :=
  ∑ n ∈ Icc 1 N, (f n : ℂ) * Complex.exp (-(2 * Real.pi * Complex.I * (n * γ)))

/-- `‖f̂‖_q = (∫₀¹ |f̂(γ)|^q dγ)^{1/q}`. -/
noncomputable def fhatLq (N : ℕ) (f : ℕ → ℝ) (q : ℝ) : ℝ :=
  (∫ γ in (0 : ℝ)..1, ‖fhat N f γ‖ ^ q) ^ (1 / q)

/-- The three hypotheses of Proposition 3.1 for one `f`. -/
def Prop31Hyp (N : ℕ) (η ε K q : ℝ) (f : ℕ → ℝ) : Prop :=
  (∀ n ∈ Icc 1 N, 0 ≤ f n) ∧ DenseOnAPs N η ε f ∧
  (∃ ν : ℕ → ℝ, (∀ n ∈ Icc 1 N, f n ≤ ν n) ∧
    ∀ γ : ℝ, ‖fhat N ν γ - fhat N (fun _ => 1) γ‖ ≤ η * N) ∧
  fhatLq N f q ≤ K * (N : ℝ) ^ (1 - 1 / q)

/-- Proposition 3.1 as printed, with `c(ε) − O_{ε,K,q}(η)` read as: there is `c(ε) > 0`,
and for each `K ≥ 1`, `2 < q < 3` a constant `C`, with the bound `(c − Cη) N²` for all
`η ∈ (0, 1)`, `N`, and `n ∈ [N/2, N]`. It inherits the small-`N` failure of Proposition
3.2 for `η < c/C`; we do not prove that here because it needs the `L^q` hypothesis. -/
def Prop31Printed : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ c > (0 : ℝ), ∀ K q : ℝ, 1 ≤ K → 2 < q → q < 3 → ∃ C : ℝ,
    ∀ η : ℝ, 0 < η → η < 1 → ∀ (N : ℕ) (f₁ f₂ f₃ : ℕ → ℝ),
    Prop31Hyp N η ε K q f₁ → Prop31Hyp N η ε K q f₂ → Prop31Hyp N η ε K q f₃ →
    ∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N → (c - C * η) * (N : ℝ) ^ 2 ≤ conv3 N f₁ f₂ f₃ n

/-- Proposition 3.1 with `N ≥ N₀(ε, K, q, η)`, the form section 4.3 proves. -/
def Prop31 : Prop :=
  ∀ ε : ℝ, 0 < ε → ε < 1 → ∃ c > (0 : ℝ), ∀ K q : ℝ, 1 ≤ K → 2 < q → q < 3 → ∃ C : ℝ,
    ∀ η : ℝ, 0 < η → η < 1 → ∃ N₀ : ℕ, ∀ (N : ℕ) (f₁ f₂ f₃ : ℕ → ℝ), N₀ ≤ N →
    Prop31Hyp N η ε K q f₁ → Prop31Hyp N η ε K q f₂ → Prop31Hyp N η ε K q f₃ →
    ∀ n : ℕ, (N : ℝ) / 2 ≤ n → n ≤ N → (c - C * η) * (N : ℝ) ^ 2 ≤ conv3 N f₁ f₂ f₃ n

/-- P0028 Proposition 3.1, corrected form, cited. -/
theorem mms_prop31 : Prop31 := by sorry

theorem prop31_of_printed (H : Prop31Printed) : Prop31 := by
  intro ε hε hε1
  obtain ⟨c, hc, h⟩ := H ε hε hε1
  refine ⟨c, hc, fun K q hK hq hq' => ?_⟩
  obtain ⟨C, hC⟩ := h K q hK hq hq'
  exact ⟨C, fun η hη hη1 => ⟨0, fun N f₁ f₂ f₃ _ => hC η hη hη1 N f₁ f₂ f₃⟩⟩

/-! ### Theorem 2.1 -/

/-- `W = ∏_{p ≤ w} p` with `w = 0.1 log log x`. -/
noncomputable def wheel (x : ℝ) : ℕ :=
  ∏ p ∈ (range (⌊(0.1 : ℝ) * Real.log (Real.log x)⌋₊ + 1)).filter Nat.Prime, p

/-- The integers of `[a, b]`. -/
noncomputable def ints (a b : ℝ) : Finset ℕ := Icc ⌈a⌉₊ ⌊b⌋₊

/-- `e(t) = exp(2πit)`. -/
noncomputable def e (t : ℝ) : ℂ := Complex.exp (2 * Real.pi * Complex.I * t)

/-- The prime indicator `ρ`. -/
noncomputable def ρ (n : ℕ) : ℝ := if n.Prime then 1 else 0

/-- Hypothesis (1) of Theorem 2.1, the majorant's Fourier condition, over
`x − x^θ/3 ≤ n ≤ x + x^θ`, the paper's interval. -/
def Hyp1 (θ x αp η : ℝ) (ρp : ℕ → ℝ) : Prop :=
  ∀ c : ℕ, Nat.Coprime c (wheel x) → ∀ γ : ℝ,
    ‖∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
        ((ρp n : ℂ) * e (n * γ)) -
      ((αp / Real.log x * (wheel x / (wheel x).totient) : ℝ) : ℂ) *
      ∑ n ∈ (ints (x - x ^ θ / 3) (x + x ^ θ)).filter (fun n => n ≡ c [MOD wheel x]),
        e (n * γ)‖ ≤ η * x ^ θ / ((wheel x).totient * Real.log x)

/-- Hypothesis (2) of Theorem 2.1, primes in progressions in short intervals:
for `I = [a, b] ⊂ [x − x^θ/3, x + x^θ]` with `|I| ≥ x^{θ−ε}`, `d ≤ log x`, `(c, d) = 1`. -/
def Hyp2 (θ ε x αm : ℝ) : Prop :=
  ∀ a b : ℝ, x - x ^ θ / 3 ≤ a → b ≤ x + x ^ θ → x ^ (θ - ε) ≤ b - a →
    ∀ d c : ℕ, 1 ≤ d → (d : ℝ) ≤ Real.log x → Nat.Coprime c d →
      αm * (b - a) / (d.totient * Real.log x) ≤
        ∑ n ∈ (ints a b).filter (fun n => n ≡ c [MOD d]), ρ n

/-- The conclusion of Theorem 2.1: every odd integer in `[3x − x^θ/3, 3x + x^θ/3]` is a sum
of three primes in `[x − x^θ/3, x + x^θ]`. -/
def Thm21Conclusion (θ x : ℝ) : Prop :=
  ∀ n : ℕ, Odd n → 3 * x - x ^ θ / 3 ≤ n → (n : ℝ) ≤ 3 * x + x ^ θ / 3 →
    ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = n ∧
      x - x ^ θ / 3 ≤ p₁ ∧ (p₁ : ℝ) ≤ x + x ^ θ ∧
      x - x ^ θ / 3 ≤ p₂ ∧ (p₂ : ℝ) ≤ x + x ^ θ ∧
      x - x ^ θ / 3 ≤ p₃ ∧ (p₃ : ℝ) ≤ x + x ^ θ

/-- Theorem 2.1. The paper lets `η` be small in terms of `3α⁻ − α⁺`; we let `η₀` depend on
`θ, ε, α⁺, α⁻`, a weaker and safer reading, and let "x large" depend on all of them. -/
def Thm21 : Prop :=
  ∀ θ ε : ℝ, 0 < θ → θ < 1 → 0 < ε → ε < 1 → ∀ αp αm : ℝ, 0 < αp → 0 < αm →
    αp < 3 * αm → ∃ η₀ > (0 : ℝ), ∀ η : ℝ, 0 < η → η ≤ η₀ → ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
    ∀ ρp : ℕ → ℝ, (∀ n ∈ ints (x - x ^ θ / 3) (x + x ^ θ), ρ n ≤ ρp n) →
    Hyp1 θ x αp η ρp → Hyp2 θ ε x αm → Thm21Conclusion θ x

/-- P0028 Theorem 2.1, cited. -/
theorem mms_thm21 : Thm21 := by sorry

/-! ### From Theorem 2.1's conclusion to Theorem 1.1's form, zero sorry -/

/-- If the conclusion of Theorem 2.1 holds for every large real `x`, then every large odd
`n` is a sum of three primes within `n^θ` of `n/3`: take `x = n/3`, so `|p − n/3| ≤ x^θ ≤ n^θ`. -/
theorem almostEqual_of_thm21Conclusion {θ : ℝ} (hθ : 0 < θ)
    (H : ∃ X : ℝ, ∀ x : ℝ, X ≤ x → Thm21Conclusion θ x) : AlmostEqualVinogradov θ := by
  obtain ⟨X, hX⟩ := H
  refine ⟨⌈3 * |X|⌉₊ + 1, fun n ho hn => ?_⟩
  have hn' : (⌈3 * |X|⌉₊ : ℝ) + 1 ≤ n := by exact_mod_cast hn
  have hc := Nat.le_ceil (3 * |X|)
  have hXa := le_abs_self X
  have hx0 : (0 : ℝ) < (n : ℝ) / 3 := by
    have : (0 : ℝ) ≤ 3 * |X| := by positivity
    linarith
  have hxX : X ≤ (n : ℝ) / 3 := by linarith
  have hpos : (0 : ℝ) ≤ ((n : ℝ) / 3) ^ θ := by positivity
  obtain ⟨a, b, c, ha, hb, hc', hs, a1, a2, b1, b2, c1, c2⟩ :=
    hX _ hxX n ho (by linarith) (by linarith)
  have hle : ((n : ℝ) / 3) ^ θ ≤ (n : ℝ) ^ θ :=
    Real.rpow_le_rpow hx0.le (by linarith) hθ.le
  refine ⟨a, b, c, ha, hb, hc', hs, ?_, ?_, ?_⟩ <;> rw [abs_le] <;> constructor <;> linarith

/-- So Theorem 2.1, with its two hypotheses supplied for every large `x`, gives
`AlmostEqualVinogradov θ`. This is the shape of the deduction of Theorem 1.1 in section 5,
with the analytic inputs, Proposition 5.1 and Baker-Harman-Pintz, left as hypotheses. -/
theorem almostEqual_of_thm21 (h21 : Thm21) {θ ε αp αm : ℝ} (hθ : 0 < θ) (hθ1 : θ < 1)
    (hε : 0 < ε) (hε1 : ε < 1) (hp : 0 < αp) (hm : 0 < αm) (h3 : αp < 3 * αm)
    (inputs : ∀ η > (0 : ℝ), ∃ X : ℝ, ∀ x : ℝ, X ≤ x → ∃ ρp : ℕ → ℝ,
      (∀ n ∈ ints (x - x ^ θ / 3) (x + x ^ θ), ρ n ≤ ρp n) ∧
      Hyp1 θ x αp η ρp ∧ Hyp2 θ ε x αm) :
    AlmostEqualVinogradov θ := by
  obtain ⟨η₀, hη₀, h⟩ := h21 θ ε hθ hθ1 hε hε1 αp αm hp hm h3
  obtain ⟨X₁, hX₁⟩ := h η₀ hη₀ le_rfl
  obtain ⟨X₂, hX₂⟩ := inputs η₀ hη₀
  apply almostEqual_of_thm21Conclusion hθ
  refine ⟨max X₁ X₂, fun x hx => ?_⟩
  obtain ⟨ρp, h1, h2, h3'⟩ := hX₂ x ((le_max_right _ _).trans hx)
  exact hX₁ x ((le_max_left _ _).trans hx) ρp h1 h2 h3'

end LeanLab.Ternary.MMS
