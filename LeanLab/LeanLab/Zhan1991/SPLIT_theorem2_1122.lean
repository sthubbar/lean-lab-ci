/-
P0068 Zhan 1991, Theorem 2, split into cited LEAF steps. Burst 20261122.
Source: papers/Zhan1991.pdf, journal pages 261 to 269, pdf pages 3 to 11, read from page images
rendered at 110 and 220 dpi. Every LEAF below is a step of Zhan's proof, with page and display.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Readings: `≪` is `∃ K N₀, ∀ N ≥ N₀, ‖·‖ ≤ K · bound`; `L = log N`; `χ₀` is `1` in
`DirichletCharacter ℂ q`. Constants `c₁, c₂, c₃` are chosen in the order the paper chooses them:
`c₁` large, then `c₂` large in terms of `c₁` and `B`, then `c₃` large; this is the order behind
"we may take c₂ ≥ c₁ + 1", "c₂ ≥ 2B + 1" and "if c₃ is sufficiently large", pages 263 to 269.
-/
import LeanLab.Zhan1991.Theorems235

namespace LeanLab.Zhan1991
open Finset Real
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

noncomputable section

/-! ### Definitions, each cited -/

/-- The twisted sum of display (3.1), page 263: `Σ_{N-A<n≤N} Λ(n) χ(n) e(nλ)`. -/
def Schi {q : ℕ} (χ : DirichletCharacter ℂ q) (lam : ℝ) (N : ℕ) (A : ℝ) : ℂ :=
  ∑ n ∈ shortWin N A, (Λ n : ℂ) * χ n * ee (n * lam)

/-- Estimate (1.3), `S(α; N, A) ≪ A L^{-B}`, with fixed constants `c₁, c₂, K, N₀`, under the
hypotheses of Theorem 2, page 260, on the range `lo N ≤ A ≤ hi N`. -/
def Est13 (B c1 c2 K N₀ : ℝ) (lo hi : ℕ → ℝ) : Prop :=
  ∀ (N : ℕ) (A α lam : ℝ) (a : ℤ) (q : ℕ), N₀ ≤ N → lo N ≤ A → A ≤ hi N →
    Cond12 α (A ^ 2 / N * Real.log N ^ (-c1)) a q lam → Real.log N ^ c2 ≤ q →
    ‖Sexp α N A‖ ≤ K * A * Real.log N ^ (-B)

/-- The hypotheses of Theorem 2, page 260, after the reduction to `A ≤ N^{2/3}` of pages 262
and 263, with `α` replaced by its data `q, λ`: `N^{3/5} L^{c₃} ≤ A ≤ N^{2/3}`,
`L^{c₂} ≤ q ≤ τ`, `|λ| ≤ 1/(qτ)`, `τ = A² N⁻¹ L^{-c₁}`, condition (1.2). -/
def Hyp2 (c1 c2 c3 : ℝ) (N : ℕ) (A lam : ℝ) (q : ℕ) : Prop :=
  (N : ℝ) ^ (3 / 5 : ℝ) * Real.log N ^ c3 ≤ A ∧ A ≤ (N : ℝ) ^ (2 / 3 : ℝ) ∧ 1 ≤ q ∧
    Real.log N ^ c2 ≤ q ∧ (q : ℝ) ≤ A ^ 2 / N * Real.log N ^ (-c1) ∧
    |lam| ≤ 1 / (q * (A ^ 2 / N * Real.log N ^ (-c1)))

/-- `M_X(s) = Σ_{n≤X} μ(n) n^{-s}` of the Heath-Brown identity, page 263, as an arithmetic
function. -/
def muTrunc (X : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if (n : ℝ) ≤ X then (μ n : ℝ) else 0, by simp⟩

/-- The coefficients `a_j(n)` of page 263: `log n` for `j = 1`, `1` for `1 < j ≤ 10`,
`μ(n)` for `10 < j ≤ 20`. -/
def aj (j n : ℕ) : ℂ :=
  if j = 1 then (Real.log n : ℂ) else if j ≤ 10 then 1 else (μ n : ℂ)

/-- The dyadic range `I_j = (N_j, 2N_j]` of display (3.5), page 264, cut to positive integers. -/
def dyad (x : ℝ) : Finset ℕ :=
  (Finset.Icc 1 ⌊2 * x⌋₊).filter (fun n => x < n)

/-- `f_j(s, χ) = Σ_{n ∈ I_j} a_j(n) χ(n) n^{-s}`, display (3.6), page 264. -/
def fj {q : ℕ} (j : ℕ) (x : ℝ) (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∑ n ∈ dyad x, aj j n * χ n * (n : ℂ) ^ (-s)

/-- `F(s, χ) = Π_{j=1}^{20} f_j(s, χ)`, display (3.6), page 264; `Nv j` is `N_{j+1}`. -/
def Fprod {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q) (s : ℂ) : ℂ :=
  ∏ j : Fin 20, fj (j.val + 1) (Nv j) χ s

/-- Condition (3.5), page 264: `N ≪ Π N_j ≪ N` and `N_j ≤ X = N^{1/10}` for `11 ≤ j ≤ 20`.
The implied constants are read as `2^{-21}` and `1`, which is what `N - A < n₁⋯n₂₀ ≤ N`,
`A ≤ N/2` and `n_j ∈ (N_j, 2N_j]` give. -/
def Cond35 (N : ℕ) (Nv : Fin 20 → ℝ) : Prop :=
  (∀ j, (1 / 2 : ℝ) ≤ Nv j) ∧ (N : ℝ) / 2 ^ 21 ≤ ∏ j, Nv j ∧ ∏ j, Nv j ≤ N ∧
    ∀ j : Fin 20, 10 ≤ j.val → Nv j ≤ (N : ℝ) ^ (1 / 10 : ℝ)

/-- `T = q^{1/2} (N A⁻¹ + |λ| N) N^{2ε}`, display (3.7), page 264. -/
def Tcut (q : ℕ) (N : ℕ) (A lam ε : ℝ) : ℝ :=
  (q : ℝ) ^ (1 / 2 : ℝ) * (N / A + |lam| * N) * (N : ℝ) ^ (2 * ε)

/-- `T₀ = 4π (|λ| N + N A⁻¹)`, page 265. -/
def T0cut (N : ℕ) (A lam : ℝ) : ℝ := 4 * π * (|lam| * N + N / A)

/-- The weight `min (A, N / min_{N-A≤u≤N} |t + 2πλu|)` of (3.8), page 265, read as `A` when the
inner minimum is `0`. -/
def wt38 (N : ℕ) (A lam t : ℝ) : ℝ :=
  let m := sInf ((fun u => |t + 2 * π * lam * u|) '' Set.Icc ((N : ℝ) - A) N)
  if m = 0 then A else min A (N / m)

/-! ### Cited lemmas of Section II, LEAF statements -/

/-- Lemma 1 of the paper, cited from Titchmarsh, page 261, first derivative test: for real `F, G`
on `(a, b)` with `G/F'` monotone, `|F'| ≥ m > 0` and `|G| ≤ M`,
`∫_a^b G(u) e(F(u)) du ≪ M/m`. Continuity of `F'` and `G` is added. -/
def Lemma1 : Prop :=
  ∃ K : ℝ, ∀ (a b m M : ℝ) (F F' G : ℝ → ℝ), a ≤ b → 0 < m →
    (∀ u ∈ Set.Icc a b, HasDerivAt F (F' u) u) → ContinuousOn F' (Set.Icc a b) →
    ContinuousOn G (Set.Icc a b) →
    (MonotoneOn (fun u => G u / F' u) (Set.Icc a b) ∨
      AntitoneOn (fun u => G u / F' u) (Set.Icc a b)) →
    (∀ u ∈ Set.Icc a b, m ≤ |F' u|) → (∀ u ∈ Set.Icc a b, |G u| ≤ M) →
    ‖∫ u in a..b, (G u : ℂ) * ee (F u)‖ ≤ K * M / m

/-- Lemma 6 of the paper, cited [9], page 262, mean value theorem with characters:
`∫_U^{U+T} Σ_χ |Σ_{n=M+1}^{M+N} a_n χ(n) n^{-s}|² dt ≪ Σ (qT + n) |a_n|² n^{-2σ}`,
`s = σ + it`, for all `T ≥ 1` and real `U`. -/
def Lemma6 : Prop :=
  ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (M Nn : ℕ) (c : ℕ → ℂ) (T U σ : ℝ), 1 ≤ T →
    ∫ t in U..(U + T), ∑ χ : DirichletCharacter ℂ q,
      ‖∑ n ∈ Finset.Icc (M + 1) (M + Nn), c n * χ n * (n : ℂ) ^ (-((σ : ℂ) + t * Complex.I))‖ ^ 2
    ≤ K * ∑ n ∈ Finset.Icc (M + 1) (M + Nn), (q * T + n) * ‖c n‖ ^ 2 * (n : ℝ) ^ (-2 * σ)

/-- Lemma 7 of the paper, cited [1], page 262: for `1/2 ≤ σ ≤ 1 + (log qT)⁻¹`, `2 ≤ |t| ≤ T`,
any `χ mod q`, `L^{(k)}(σ+it, χ) ≪ (qT)^{(1-σ)/2 + ε}`, `k = 0, 1`. -/
def Lemma7 : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K : ℝ, ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (σ t T : ℝ)
    (k : ℕ), k ≤ 1 → 1 / 2 ≤ σ → σ ≤ 1 + 1 / Real.log (q * T) → 2 ≤ |t| → |t| ≤ T →
    ‖iteratedDeriv k (DirichletCharacter.LFunction χ) (σ + t * Complex.I)‖
      ≤ K * ((q : ℝ) * T) ^ ((1 - σ) / 2 + ε)

/-- LEAF: Lemma 1, page 261, cited from Titchmarsh. Class MEDIUM. -/
theorem zhan_lemma1_leaf : Lemma1 := by
  sorry

/-- LEAF: Lemma 2, page 261 display (2.1), cited from Zhan [4]; the `k = 1` case is derived as in
[1] Lemma 11. Class HARD. The Prop is `Lemma2` of Theorems235.lean. -/
theorem zhan_lemma2_leaf : Lemma2 := by
  sorry

/-- LEAF: Lemma 3, page 261 display (2.2), cited from Jutila [3]; the `k = 1` case as for
Lemma 2. Class HARD. The Prop is `Lemma3` of Theorems235.lean. -/
theorem zhan_lemma3_leaf : Lemma3 := by
  sorry

/-- LEAF: Lemma 6, page 262, cited [9], mean value theorem for Dirichlet polynomials with
characters. Class MEDIUM. -/
theorem zhan_lemma6_leaf : Lemma6 := by
  sorry

/-- LEAF: Lemma 7, page 262, cited [1], hybrid convexity bound for `L^{(k)}`. Class HARD. -/
theorem zhan_lemma7_leaf : Lemma7 := by
  sorry

/-! ### Top level steps of the Proof of Theorem 2, pages 262 to 269 -/

/-- Estimate (1.3) on the small range `N^{3/5} L^{c₃} ≤ A ≤ N^{2/3}`, the case the proof treats
after the reduction of pages 262 and 263. -/
def SmallRange : Prop :=
  ∀ B : ℝ, 0 < B → ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∃ c2m : ℝ, ∀ c2 ≥ c2m, ∃ c3 : ℝ, 0 < c3 ∧
    ∃ K N₀ : ℝ, Est13 B c1 c2 K N₀ (fun N => (N : ℝ) ^ (3 / 5 : ℝ) * Real.log N ^ c3)
      (fun N => (N : ℝ) ^ (2 / 3 : ℝ))

/-- Estimate (1.3) on the large range `N L⁻¹ ≤ A ≤ N`, page 263. -/
def LargeRange : Prop :=
  ∀ B : ℝ, 0 < B → ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∃ c2m : ℝ, ∀ c2 ≥ c2m,
    ∃ K N₀ : ℝ, Est13 B c1 c2 K N₀ (fun N => (N : ℝ) / Real.log N) (fun N => (N : ℝ))

/-- The reduction of pages 262 and 263 as an implication with the same `B, c₁, c₂, c₃`:
(1.3) on `N^{3/5} L^{c₃} ≤ A ≤ N^{2/3}` gives (1.3) on `N^{2/3} ≤ A ≤ N L⁻¹`. -/
def MiddleReduction : Prop :=
  ∀ B c1 c2 c3 K N₀ : ℝ, 0 < B → 0 < c1 → 0 < c2 → 0 < c3 →
    Est13 B c1 c2 K N₀ (fun N => (N : ℝ) ^ (3 / 5 : ℝ) * Real.log N ^ c3)
      (fun N => (N : ℝ) ^ (2 / 3 : ℝ)) →
    ∃ K' N₀' : ℝ, Est13 B c1 c2 K' N₀' (fun N => (N : ℝ) ^ (2 / 3 : ℝ))
      (fun N => (N : ℝ) / Real.log N)

/-- LEAF: page 262 last display and page 263 first line, the reduction from
`N^{2/3} ≤ A ≤ N L⁻¹` to `A ≤ N^{2/3}`: cut `(N-A, N]` into `J` blocks of length
`A₁ ∈ [N^{2/3}/2, N^{2/3}]` and apply (1.3) to each block, `≪ J · A₁ L^{-B} ≪ A L^{-B}`.
Class HARD. QUESTION: the paper applies (1.3) to each block with the same `α`, but (1.2) with
`τ₁ = A₁² N⁻¹ L^{-c₁}` need not hold, since `q ≤ τ = A² N⁻¹ L^{-c₁}` may exceed `τ₁`; for
`α = 1/q` with `q` near `N L^{-c₁-2}` each block sum is of size about `A₁`, so the blockwise
bound fails though the total may still be small. The implication is stated, not the blockwise
step. -/
theorem middle_reduction_leaf : MiddleReduction := by
  sorry

/-- LEAF: page 263 lines 1 and 2, "As for `N L⁻¹ ≤ A ≤ N`, (1.3) follows immediately from
Vinogradov's classical result". Class MEDIUM. Needs `c₁` large, since `q ≤ τ ≤ N L^{-c₁}` enters
Vinogradov's bound through `(Nq)^{1/2}`. -/
theorem large_range_leaf : LargeRange := by
  sorry

/-- The bound of display (3.1), page 263, after the reduction:
`Σ_{χ≠χ₀} |Σ_{N-A<n≤N} Λ(n) χ(n) e(nλ)| ≪ q^{1/2} A L^{-B-1}`. -/
def Eq31 : Prop :=
  ∀ B : ℝ, 0 < B → ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∃ c2m : ℝ, ∀ c2 ≥ c2m, ∃ c3 : ℝ, 0 < c3 ∧
    ∃ K N₀ : ℝ, ∀ (N : ℕ) (A lam : ℝ) (q : ℕ) [NeZero q], N₀ ≤ N → Hyp2 c1 c2 c3 N A lam q →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1), ‖Schi χ lam N A‖
        ≤ K * (q : ℝ) ^ (1 / 2 : ℝ) * A * Real.log N ^ (-B - 1)

/-- The "well-known approach" display on page 263, before (3.1): with `α = a/q + λ`,
`(a, q) = 1`, `S(α; N, A) ≪ L q^{-1/2} Σ_{χ≠χ₀} |Σ Λ(n) χ(n) e(nλ)| + L² + L A q^{-1/2}`.
The side conditions `1 ≤ A ≤ N` and `q ≤ N` are added; they hold under Theorem 2. -/
def WellKnown : Prop :=
  ∃ K N₀ : ℝ, ∀ (N : ℕ) (A α lam : ℝ) (a : ℤ) (q : ℕ) [NeZero q], N₀ ≤ N → 1 ≤ A →
    A ≤ N → α = a / q + lam → Int.gcd a q = 1 → (q : ℝ) ≤ N →
    ‖Sexp α N A‖ ≤ K * (Real.log N * (q : ℝ) ^ (-(1 / 2) : ℝ) *
      (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1), ‖Schi χ lam N A‖)
      + Real.log N ^ (2 : ℝ) + Real.log N * A * (q : ℝ) ^ (-(1 / 2) : ℝ))

/-- LEAF: page 263, the display chain from `S(α; N, A)` to `≪ L q^{-1/2} Σ_{χ≠χ₀} |…| + L² +
L A q^{-1/2}`: drop `(n, q) > 1` at cost `O(L²)`, expand `e(an/q)` in characters, Gauss sums.
Class MEDIUM. -/
theorem wellKnown_leaf : WellKnown := by
  sorry

/-- PROVED, page 263, "Hence, if we take `c₂ ≥ 2B + 1`, it is sufficient to show (3.1)": the
small range estimate follows from the well-known display and (3.1), using `L^{c₂} ≤ q`,
`A ≥ L^{c₃}` and `q ≤ τ ≤ N`. QUESTION: with `c₂ = 2B + 1` the term `L A q^{-1/2}` is only
`≪ A L^{1/2-B}`; the proof takes `c₂ ≥ 2B + 2`, harmless since `c₂` is free. -/
theorem smallRange_of_wellKnown_eq31 (hW : WellKnown) (h31 : Eq31) : SmallRange := by
  intro B hB
  obtain ⟨c1m, h31⟩ := h31 B hB
  refine ⟨max c1m 0, fun c1 hc1 => ?_⟩
  obtain ⟨c2m, h31'⟩ := h31 c1 (le_trans (le_max_left _ _) hc1)
  have hc10 : 0 ≤ c1 := le_trans (le_max_right _ _) hc1
  refine ⟨max c2m (2 * B + 2), fun c2 hc2 => ?_⟩
  obtain ⟨c3, hc3, K, N₀, e⟩ := h31' c2 (le_trans (le_max_left _ _) hc2)
  have hc2B : 2 * B + 2 ≤ c2 := le_trans (le_max_right _ _) hc2
  obtain ⟨KW, NW, eW⟩ := hW
  refine ⟨max c3 (B + 2), lt_of_lt_of_le hc3 (le_max_left _ _), max KW 0 * (max K 0 + 2),
    max (max N₀ NW) 3, ?_⟩
  intro N A α lam a q hN hlo hhi hcond hq
  beta_reduce at hlo hhi
  obtain ⟨hα, hgcd, hlam, hq1, hqτ⟩ := hcond
  have : NeZero q := ⟨by omega⟩
  have hN3 : (3 : ℝ) ≤ N := le_trans (le_max_right _ _) hN
  have hN0 : N₀ ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNW : NW ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  set L := Real.log (N : ℝ) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]; linarith [Real.exp_one_lt_d9]
  have hLpos : 0 < L := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hNp1 : 1 ≤ (N : ℝ) ^ (3 / 5 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
  have hlo' : (N : ℝ) ^ (3 / 5 : ℝ) * L ^ c3 ≤ A :=
    le_trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_left _ _)) (by positivity)) hlo
  have hAL : L ^ (B + 2) ≤ A :=
    le_trans (le_trans (Real.rpow_le_rpow_of_exponent_le hL1 (le_max_right c3 _))
      (le_mul_of_one_le_left (by positivity) hNp1)) hlo
  have hA1 : 1 ≤ A := le_trans (Real.one_le_rpow hL1 (by linarith)) hAL
  have hAN : A ≤ N := by
    refine le_trans hhi ?_
    calc (N : ℝ) ^ (2 / 3 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = N := Real.rpow_one _
  have hqN : (q : ℝ) ≤ N := by
    refine le_trans hqτ ?_
    have h1 : L ^ (-c1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
    have h2 : A ^ 2 / N ≤ N := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    calc A ^ 2 / N * L ^ (-c1) ≤ A ^ 2 / N * 1 :=
          mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ N := by linarith
  have hW' := eW N A α lam a q hNW hA1 hAN hα hgcd hqN
  have h31v := e N A lam q hN0 ⟨hlo', hhi, hq1, hq, hqτ, hlam⟩
  set Sc := ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
    ‖Schi χ lam N A‖ with hSdef
  have hS0 : 0 ≤ Sc := Finset.sum_nonneg (fun _ _ => norm_nonneg _)
  have hLB : 0 ≤ L ^ (-B) := Real.rpow_nonneg hLpos.le _
  have hX : 0 ≤ A * L ^ (-B) := mul_nonneg (by linarith) hLB
  -- identities
  have eL : L * L ^ (-B - 1) = L ^ (-B) := by
    have := Real.rpow_add hLpos 1 (-B - 1)
    rw [Real.rpow_one] at this; rw [← this]; congr 1; ring
  have eL2 : L ^ (2 : ℝ) = L ^ (B + 2) * L ^ (-B) := by
    rw [← Real.rpow_add hLpos]; congr 1; ring
  have hqh : 0 < (q : ℝ) ^ (1 / 2 : ℝ) := by positivity
  have eq : (q : ℝ) ^ (-(1 / 2) : ℝ) = ((q : ℝ) ^ (1 / 2 : ℝ))⁻¹ := Real.rpow_neg hq0.le _
  have hqL : L ^ (B + 1) ≤ (q : ℝ) ^ (1 / 2 : ℝ) := by
    have h1 : L ^ (2 * B + 2) ≤ q :=
      le_trans (Real.rpow_le_rpow_of_exponent_le hL1 hc2B) hq
    have h2 := Real.rpow_le_rpow (by positivity) h1 (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [← Real.rpow_mul hLpos.le] at h2
    have : (2 * B + 2) * (1 / 2) = B + 1 := by ring
    rwa [this] at h2
  have hqinv : (q : ℝ) ^ (-(1 / 2) : ℝ) ≤ L ^ (-B - 1) := by
    rw [eq, show -B - 1 = -(B + 1) by ring, Real.rpow_neg hLpos.le]
    exact inv_anti₀ (by positivity) hqL
  have T1 : L * (q : ℝ) ^ (-(1 / 2) : ℝ) * Sc ≤ max K 0 * (A * L ^ (-B)) := by
    have hs : Sc ≤ max K 0 * (q : ℝ) ^ (1 / 2 : ℝ) * A * L ^ (-B - 1) := by
      refine le_trans h31v ?_
      have : 0 ≤ (q : ℝ) ^ (1 / 2 : ℝ) * A * L ^ (-B - 1) := by positivity
      have := mul_le_mul_of_nonneg_right (le_max_left K 0) this
      simpa [mul_assoc] using this
    have h0 : 0 ≤ L * (q : ℝ) ^ (-(1 / 2) : ℝ) := by positivity
    calc L * (q : ℝ) ^ (-(1 / 2) : ℝ) * Sc
        ≤ L * (q : ℝ) ^ (-(1 / 2) : ℝ) * (max K 0 * (q : ℝ) ^ (1 / 2 : ℝ) * A * L ^ (-B - 1)) :=
          mul_le_mul_of_nonneg_left hs h0
      _ = max K 0 * (A * (L * L ^ (-B - 1))) *
            ((q : ℝ) ^ (1 / 2 : ℝ))⁻¹ * (q : ℝ) ^ (1 / 2 : ℝ) := by rw [eq]; ring
      _ = max K 0 * (A * L ^ (-B)) := by
          rw [eL, mul_assoc _ _ ((q : ℝ) ^ (1 / 2 : ℝ)), inv_mul_cancel₀ hqh.ne', mul_one]
  have T2 : L ^ (2 : ℝ) ≤ A * L ^ (-B) := by
    rw [eL2]; exact mul_le_mul_of_nonneg_right hAL hLB
  have T3 : L * A * (q : ℝ) ^ (-(1 / 2) : ℝ) ≤ A * L ^ (-B) := by
    calc L * A * (q : ℝ) ^ (-(1 / 2) : ℝ) ≤ L * A * L ^ (-B - 1) :=
          mul_le_mul_of_nonneg_left hqinv (by positivity)
      _ = A * (L * L ^ (-B - 1)) := by ring
      _ = A * L ^ (-B) := by rw [eL]
  have hY0 : 0 ≤ L * (q : ℝ) ^ (-(1 / 2) : ℝ) * Sc + L ^ (2 : ℝ) +
      L * A * (q : ℝ) ^ (-(1 / 2) : ℝ) := by positivity
  have hY : L * (q : ℝ) ^ (-(1 / 2) : ℝ) * Sc + L ^ (2 : ℝ) +
      L * A * (q : ℝ) ^ (-(1 / 2) : ℝ) ≤ (max K 0 + 2) * (A * L ^ (-B)) := by
    nlinarith
  calc ‖Sexp α N A‖ ≤ KW * (L * (q : ℝ) ^ (-(1 / 2) : ℝ) * Sc + L ^ (2 : ℝ) +
        L * A * (q : ℝ) ^ (-(1 / 2) : ℝ)) := hW'
    _ ≤ max KW 0 * (L * (q : ℝ) ^ (-(1 / 2) : ℝ) * Sc + L ^ (2 : ℝ) +
        L * A * (q : ℝ) ^ (-(1 / 2) : ℝ)) := mul_le_mul_of_nonneg_right (le_max_left _ _) hY0
    _ ≤ max KW 0 * ((max K 0 + 2) * (A * L ^ (-B))) :=
        mul_le_mul_of_nonneg_left hY (le_max_right _ _)
    _ = max KW 0 * (max K 0 + 2) * A * L ^ (-B) := by ring

/-- PROVED helper for the support argument of Heath-Brown's identity, page 263: if `f` vanishes
on `n ≤ a` and `g` on `n ≤ b`, then `f * g` vanishes on `n ≤ ab`. -/
theorem af_mul_vanish (f g : ArithmeticFunction ℝ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hf : ∀ n : ℕ, (n : ℝ) ≤ a → f n = 0) (hg : ∀ n : ℕ, (n : ℝ) ≤ b → g n = 0) :
    ∀ n : ℕ, (n : ℝ) ≤ a * b → (f * g) n = 0 := by
  intro n hn
  rw [ArithmeticFunction.mul_apply]
  apply Finset.sum_eq_zero
  intro x hx
  rw [Nat.mem_divisorsAntidiagonal] at hx
  by_cases h : (x.1 : ℝ) ≤ a
  · simp [hf _ h]
  by_cases h' : (x.2 : ℝ) ≤ b
  · simp [hg _ h']
  exfalso
  push Not at h h'
  have e : (n : ℝ) = x.1 * x.2 := by exact_mod_cast hx.1.symm
  have := mul_lt_mul'' h h' ha hb
  linarith

/-- Evaluation at `n` as an additive map, a helper for reading the identity of page 263
coefficientwise. -/
def evalHom (n : ℕ) : ArithmeticFunction ℝ →+ ℝ :=
  { toFun := fun f => f n, map_zero' := rfl, map_add' := fun _ _ => rfl }

/-- PROVED, page 263, Heath-Brown's identity
`-ζ'/ζ = Σ_{j=1}^k C(k,j) (-1)^{j-1} ζ' ζ^{j-1} M^j - (ζ'/ζ)(1 - ζM)^k`, `M = M_X`, read
coefficientwise for `n ≤ X^k`, where the last term has no coefficient:
`Λ(n) = Σ_{j=1}^k (-1)^{j-1} C(k,j) (log * ζ^{j-1} * M_X^j)(n)`. The paper takes `k = 10`,
`X = N^{1/10}`, so `X ≥ 1`; the hypothesis `1 ≤ X` is needed, since for `X = -5`, `k = 2`
the truncation `M_X` is `0` and the identity would force `Λ(n) = 0` for `n ≤ 25`. -/
theorem heathBrown_identity (k : ℕ) (X : ℝ) (hX : 1 ≤ X) (n : ℕ) (hn : 1 ≤ n)
    (hnX : (n : ℝ) ≤ X ^ k) :
    (Λ n : ℝ) = ∑ j ∈ Finset.Icc 1 k, (-1 : ℝ) ^ (j - 1) * (k.choose j : ℝ) *
      ((ArithmeticFunction.log * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (j - 1) *
        muTrunc X ^ j) n) := by
  set Z : ArithmeticFunction ℝ := (ArithmeticFunction.zeta : ArithmeticFunction ℝ) with hZ
  set M := muTrunc X with hM
  set E : ArithmeticFunction ℝ := 1 - Z * M with hE
  -- E vanishes up to X
  have hE0 : ∀ m : ℕ, (m : ℝ) ≤ X → E m = 0 := by
    intro m hm
    have h1 : (Z * M) m = (Z * (μ : ArithmeticFunction ℝ)) m := by
      rw [hZ, ArithmeticFunction.coe_zeta_mul_apply, ArithmeticFunction.coe_zeta_mul_apply]
      apply Finset.sum_congr rfl
      intro i hi
      have hile : i ≤ m := Nat.divisor_le hi
      have : (i : ℝ) ≤ X := le_trans (by exact_mod_cast hile) hm
      simp [hM, muTrunc, this]
    rw [hE, sub_eq_add_neg, ArithmeticFunction.add_apply, ArithmeticFunction.neg_apply, h1, hZ,
      ArithmeticFunction.coe_zeta_mul_coe_moebius]; ring
  have hEk : ∀ j : ℕ, 1 ≤ j → ∀ m : ℕ, (m : ℝ) ≤ X ^ j → (E ^ j) m = 0 := by
    intro j hj
    induction j with
    | zero => omega
    | succ j ih =>
      rcases Nat.eq_zero_or_pos j with h0 | hpos
      · subst h0; simpa using hE0
      · rw [pow_succ]
        exact af_mul_vanish _ _ _ _ (by positivity) (by linarith) (ih hpos) hE0
  rcases Nat.eq_zero_or_pos k with hk0 | hk
  · subst hk0
    have : n = 1 := by
      have : (n : ℝ) ≤ 1 := by simpa using hnX
      have : n ≤ 1 := by exact_mod_cast this
      omega
    subst this; simp
  have hΛ1 : ∀ m : ℕ, (m : ℝ) ≤ 1 → (Λ m : ℝ) = 0 := by
    intro m hm
    have : m ≤ 1 := by exact_mod_cast hm
    interval_cases m <;> simp
  have hvan : ((Λ : ArithmeticFunction ℝ) * E ^ k) n = 0 :=
    af_mul_vanish _ _ 1 (X ^ k) zero_le_one (by positivity) hΛ1 (hEk k hk) n (by simpa using hnX)
  have hIcc : Finset.Icc 1 k = Finset.Ico (0 + 1) (k + 1) := by ext; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  have hpow : 1 - E ^ k = ∑ j ∈ Finset.Icc 1 k,
      (((-1 : ℤ) ^ (j - 1) * (k.choose j : ℤ) : ℤ) : ArithmeticFunction ℝ) * (Z * M) ^ j := by
    have hE' : E = -(Z * M) + 1 := by rw [hE]; ring
    rw [hE', add_pow, Finset.sum_range_succ', hIcc, ← Finset.sum_Ico_add', ← Finset.range_eq_Ico]
    simp only [pow_zero, one_pow, mul_one, Nat.choose_zero_right, Nat.cast_one, Nat.sub_zero]
    rw [sub_add_cancel_right, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro m _
    rw [neg_pow]
    push_cast
    ring
  have hring : (Λ : ArithmeticFunction ℝ) * (1 - E ^ k) = ∑ j ∈ Finset.Icc 1 k,
      (((-1 : ℤ) ^ (j - 1) * (k.choose j : ℤ) : ℤ) : ArithmeticFunction ℝ) *
        (ArithmeticFunction.log * Z ^ (j - 1) * M ^ j) := by
    rw [hpow, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by simp at hj; omega⟩
    rw [← ArithmeticFunction.vonMangoldt_mul_zeta, Nat.add_sub_cancel]
    ring
  have hsplit : (Λ n : ℝ) = ((Λ : ArithmeticFunction ℝ) * (1 - E ^ k)) n +
      ((Λ : ArithmeticFunction ℝ) * E ^ k) n := by
    rw [← ArithmeticFunction.add_apply, ← mul_add, sub_add_cancel, mul_one]
  rw [hsplit, hvan, add_zero, hring]
  change evalHom n (∑ j ∈ Finset.Icc 1 k, _) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [← zsmul_eq_mul, map_zsmul, zsmul_eq_mul]
  push_cast
  rfl

/-- Display (3.8), page 265, with the factor `A` restored on the right:
`Σ_{χ≠χ₀} ∫_{-T}^{T} min(A, N / min_u |t + 2πλu|) |F(1/2+it, χ)| dt ≪ (qN)^{1/2} A L^{-B-c₀}`,
for every decomposition satisfying (3.5) and `T` from (3.7). -/
def Eq38 : Prop :=
  ∀ B : ℝ, 0 < B → ∀ c0 : ℝ, 0 < c0 → ∀ ε : ℝ, 0 < ε → ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∃ c2m : ℝ,
    ∀ c2 ≥ c2m, ∃ c3 : ℝ, 0 < c3 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (A lam : ℝ) (q : ℕ) [NeZero q] (Nv : Fin 20 → ℝ), N₀ ≤ N →
      Hyp2 c1 c2 c3 N A lam q → Cond35 N Nv →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.Icc (-Tcut q N A lam ε) (Tcut q N A lam ε),
          wt38 N A lam t * ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
        ≤ K * ((q : ℝ) * N) ^ (1 / 2 : ℝ) * A * Real.log N ^ (-B - c0)

/-- LEAF: pages 263 to 265, displays (3.2) to (3.7) and Lemma 1: Heath-Brown's identity with
`k = 10`, Perron's formula (3.3), dyadic splitting (3.4) and (3.5), the line shift to
`Re s = 1/2`, partial summation against `e(λu)` and Lemma 1 for the inner `u` integral reduce
(3.1) to (3.8). Class HARD. -/
theorem eq31_of_eq38_leaf (h38 : Eq38) : Eq31 := by
  sorry

/-- Display (3.11), page 265: `Σ_{χ≠χ₀} ∫_{T₁}^{T₁+H} |F(1/2+it, χ)| dt ≪ (qN)^{1/2} L^{-B-c₀}`
for `|T₁| ≤ 2T₀`, `H = N A⁻¹`. -/
def Eq311 : Prop :=
  ∀ B : ℝ, 0 < B → ∀ c0 : ℝ, 0 < c0 → ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∃ c2m : ℝ,
    ∀ c2 ≥ c2m, ∃ c3 : ℝ, 0 < c3 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (A lam : ℝ) (q : ℕ) [NeZero q] (Nv : Fin 20 → ℝ) (T1 : ℝ), N₀ ≤ N →
      Hyp2 c1 c2 c3 N A lam q → Cond35 N Nv → |T1| ≤ 2 * T0cut N A lam →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.Ioc T1 (T1 + N / A), ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
        ≤ K * ((q : ℝ) * N) ^ (1 / 2 : ℝ) * Real.log N ^ (-B - c0)

/-- Display (3.12), page 265: `Σ_{χ≠χ₀} ∫_{T₂}^{2T₂} |F(1/2+it, χ)| dt ≪ (q N⁻¹)^{1/2} A T₂
L^{-B-c₀}` for `T₀ ≤ |T₂| ≤ 2T`; the range between `T₂` and `2T₂` is taken unoriented and the
right side uses `|T₂|`. -/
def Eq312 : Prop :=
  ∀ B : ℝ, 0 < B → ∀ c0 : ℝ, 0 < c0 → ∀ ε : ℝ, 0 < ε → ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∃ c2m : ℝ,
    ∀ c2 ≥ c2m, ∃ c3 : ℝ, 0 < c3 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (A lam : ℝ) (q : ℕ) [NeZero q] (Nv : Fin 20 → ℝ) (T2 : ℝ), N₀ ≤ N →
      Hyp2 c1 c2 c3 N A lam q → Cond35 N Nv → T0cut N A lam ≤ |T2| →
      |T2| ≤ 2 * Tcut q N A lam ε →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.uIoc T2 (2 * T2), ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
        ≤ K * ((q : ℝ) / N) ^ (1 / 2 : ℝ) * A * |T2| * Real.log N ^ (-B - c0)

/-- LEAF: page 265, displays (3.9) and (3.10): split `|t| ≤ T₀` into intervals of length
`H = N A⁻¹ ≥ 4π|λ|A`, weight `A` on the one with `|t + 2πλN| ≤ H` and `N/(kH)` on the `k`-th,
and the tail `T₀ ≤ |t| ≤ T` with weight `≪ N/|t|` cut dyadically; so (3.11) and (3.12) give
(3.8). Class MEDIUM. -/
theorem eq38_of_eq311_eq312_leaf (h311 : Eq311) (h312 : Eq312) : Eq38 := by
  sorry

/-- LEAF: pages 265 to 269, proof of (3.11): Propositions 1, 2, 3 with Lemmas 2, 3, 6, 7 and
(3.13) to (3.18), then Cases a) and b) on how many `N_j > N^{1/5}`. Class HARD. -/
theorem eq311_leaf : Eq311 := by
  sorry

/-- LEAF: page 269, last paragraph, proof of (3.12), "essentially the same as that of (3.11)"
with the usual power moments of `L`-functions in place of Lemmas 2 and 3. Class HARD. -/
theorem eq312_leaf : Eq312 := by
  sorry

/-! ### Assembly, PROVED from the LEAF steps -/

/-- Theorem 2 from the three ranges of pages 262 and 263: the small range `A ≤ N^{2/3}`, the
reduction of the middle range `N^{2/3} ≤ A ≤ N L⁻¹` to it, and Vinogradov's large range. -/
theorem theorem2_of_ranges (hs : SmallRange) (hr : MiddleReduction) (hl : LargeRange) :
    Theorem2 := by
  intro B hB
  obtain ⟨a1, h1⟩ := hs B hB
  obtain ⟨a3, h3⟩ := hl B hB
  obtain ⟨b1, h1'⟩ := h1 (max (max a1 a3) 1) (le_trans (le_max_left _ _) (le_max_left _ _))
  obtain ⟨b3, h3'⟩ := h3 (max (max a1 a3) 1) (le_trans (le_max_right _ _) (le_max_left _ _))
  obtain ⟨c3, hc3, K1, N1, e1⟩ :=
    h1' (max (max b1 b3) 1) (le_trans (le_max_left _ _) (le_max_left _ _))
  obtain ⟨K3, N3, e3⟩ := h3' (max (max b1 b3) 1) (le_trans (le_max_right _ _) (le_max_left _ _))
  have hc1 : (0 : ℝ) < max (max a1 a3) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have hc2 : (0 : ℝ) < max (max b1 b3) 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  obtain ⟨K2, N2, e2⟩ := hr B _ _ c3 K1 N1 hB hc1 hc2 hc3 e1
  refine ⟨max (max a1 a3) 1, max (max b1 b3) 1, c3, hc1, hc2, hc3,
    max (max K1 K2) K3, max (max N1 N2) N3, ?_⟩
  intro N A α lam a q hN hlo hhi hcond hq
  have hL : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hA : 0 ≤ A := le_trans (by positivity) hlo
  have hX : 0 ≤ A * Real.log N ^ (-B) := mul_nonneg hA (Real.rpow_nonneg hL _)
  have key : ∀ K', K' ≤ max (max K1 K2) K3 →
      K' * A * Real.log N ^ (-B) ≤ max (max K1 K2) K3 * A * Real.log N ^ (-B) := by
    intro K' hK'
    rw [mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hK' hX
  have hN1 : N1 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN2 : N2 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN3 : N3 ≤ N := le_trans (le_max_right _ _) hN
  rcases le_total A ((N : ℝ) ^ (2 / 3 : ℝ)) with h | h
  · exact le_trans (e1 N A α lam a q hN1 hlo h hcond hq)
      (key _ (le_trans (le_max_left _ _) (le_max_left _ _)))
  · rcases le_total A ((N : ℝ) / Real.log N) with h' | h'
    · exact le_trans (e2 N A α lam a q hN2 h h' hcond hq)
        (key _ (le_trans (le_max_right _ _) (le_max_left _ _)))
    · exact le_trans (e3 N A α lam a q hN3 h' hhi hcond hq) (key _ (le_max_right _ _))

/-- Theorem 2 assembled from the LEAF chain: (3.11) and (3.12) give (3.8), (3.8) gives (3.1),
(3.1) with the well-known display gives the small range, then the three ranges. Its axioms
include `sorryAx` through the LEAFs; the assembly steps themselves are proved. -/
theorem theorem2_from_leaves : Theorem2 :=
  theorem2_of_ranges
    (smallRange_of_wellKnown_eq31 wellKnown_leaf
      (eq31_of_eq38_leaf (eq38_of_eq311_eq312_leaf eq311_leaf eq312_leaf)))
    middle_reduction_leaf large_range_leaf

end

end LeanLab.Zhan1991
