/-
P0068 Zhan 1991, the step from (3.8) to (3.1), pages 263 to 265, split into cited LEAF steps.
Source: papers/P0068.pdf, pdf pages 5 to 7, read from page images rendered at 150 dpi.
This file refines the LEAF `eq31_of_eq38_leaf` of SPLIT_theorem2_1122.lean, which is not edited.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Chain, with `X = N^{1/10}`, `L = log N`, `ε = 1/20`, `c₀ = 21`:
* H1, PROVED from `heathBrown_identity` with `k = 10`: the partial sum (3.2) is the combination
  `Σ_{j ≤ 10} (-1)^{j-1} C(10,j) Σ_{N-A<n≤u} (log * ζ^{j-1} * M_X^j)(n) χ(n)`.
* H3, LEAF: each convolution sum is a sum of `O(L^20)` dyadic sums of the type (3.4), (3.5).
* H2, LEAF: Perron's truncated formula (3.3), (3.4) on `Re s = c = 1 + L⁻¹`.
* H4, LEAF: the shift of the line to `Re s = 1/2`, page 264, error `T⁻¹ N^{1+ε}`.
* H5, LEAF from Lemma 1: partial summation against `e(λu)`, differentiation in `u`, Fubini and
  Lemma 1 for the inner `u` integral, page 264 last two displays and page 265 first display.
* T, PROVED: the choice (3.7) of `T` makes the error `≪ q^{-1/2} A L^{-B-1}` per character.
* The assembly `eq31_of_eq38_split` is PROVED from these.
-/
import LeanLab.Zhan1991.SPLIT_theorem2_1122

namespace LeanLab.Zhan1991
open Finset Real
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

noncomputable section

/-! ### Definitions, each cited -/

/-- The partial sum (3.2), page 263: `Σ_{N-A<n≤u} Λ(n) χ(n)`. -/
def Psum {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (A u : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n), (Λ n : ℂ) * χ n

/-- The `j`-th term of Heath-Brown's identity with `k = 10`, `X = N^{1/10}`, page 263, summed
against `χ` over `N - A < n ≤ u`: `Σ (log * ζ^{j-1} * M_X^j)(n) χ(n)`. -/
def HBsum {q : ℕ} (j : ℕ) (χ : DirichletCharacter ℂ q) (N : ℕ) (A u : ℝ) : ℂ :=
  ∑ n ∈ (Finset.Icc 1 ⌊u⌋₊).filter (fun n : ℕ => (N : ℝ) - A < n),
    (((ArithmeticFunction.log * (ArithmeticFunction.zeta : ArithmeticFunction ℝ) ^ (j - 1) *
      muTrunc ((N : ℝ) ^ (1 / 10 : ℝ)) ^ j) n : ℝ) : ℂ) * χ n

/-- The dyadic sum of (3.4) before Perron's formula, page 264:
`Σ_{n_j ∈ I_j, N-A < n₁⋯n₂₀ ≤ u} a₁(n₁)χ(n₁)⋯a₂₀(n₂₀)χ(n₂₀)`, `I_j = (N_j, 2N_j]`. -/
def Dsum {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q) (N : ℕ) (A u : ℝ) : ℂ :=
  ∑ n ∈ (Fintype.piFinset fun j : Fin 20 => dyad (Nv j)).filter
      (fun n => (N : ℝ) - A < ∏ j, (n j : ℝ) ∧ ∏ j, (n j : ℝ) ≤ u),
    ∏ j : Fin 20, aj (j.val + 1) (n j) * χ (n j)

/-- The line integral of (3.4), page 264, on `Re s = σ`, written in `t` with `s = σ + it`:
`(1/2πi) ∫_{σ-iT}^{σ+iT} F(s,χ) (u^s - (N-A)^s) s⁻¹ ds`. -/
def Vline {q : ℕ} (Nv : Fin 20 → ℝ) (χ : DirichletCharacter ℂ q) (N : ℕ) (A σ T u : ℝ) : ℂ :=
  (1 / (2 * π) : ℂ) * ∫ t in (-T)..T, Fprod Nv χ ((σ : ℂ) + t * Complex.I) *
    (((u : ℂ) ^ ((σ : ℂ) + t * Complex.I) - (((N : ℝ) - A : ℝ) : ℂ) ^ ((σ : ℂ) + t * Complex.I))
      / ((σ : ℂ) + t * Complex.I))

/-! ### The LEAF steps, each a cited piece of pages 263 to 265 -/

/-- Splitting each range of summation into intervals `x < n ≤ 2x`, top of page 264. -/
def DyadicSplit : Prop :=
  ∃ K N₀ : ℝ, ∀ (N : ℕ) (A : ℝ), N₀ ≤ N → 0 ≤ A → A ≤ (N : ℝ) ^ (2 / 3 : ℝ) →
    ∀ j ∈ Finset.Icc 1 10, ∃ ι : Finset (Fin 20 → ℝ),
      (ι.card : ℝ) ≤ K * Real.log N ^ (20 : ℝ) ∧ (∀ Nv ∈ ι, Cond35 N Nv) ∧
      ∀ (q : ℕ) (χ : DirichletCharacter ℂ q) (u : ℝ), (N : ℝ) - A ≤ u → u ≤ N →
        HBsum j χ N A u = ∑ Nv ∈ ι, Dsum Nv χ N A u

/-- Perron's summation formula (3.3), (3.4) with `c = 1 + L⁻¹`, error `O(T⁻¹ N^{1+ε})`. -/
def PerronTrunc : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ) (A T u : ℝ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (Nv : Fin 20 → ℝ), N₀ ≤ N → 0 ≤ A →
    A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → Cond35 N Nv → 2 ≤ T → T ≤ N → (N : ℝ) - A ≤ u → u ≤ N →
    ‖Dsum Nv χ N A u - Vline Nv χ N A (1 + 1 / Real.log N) T u‖ ≤ K * (N : ℝ) ^ (1 + ε) / T

/-- The shift of the line of integration from `Re s = c` to `Re s = 1/2`, page 264, with error
`O(N^{1+ε}/T + max_{1/2 ≤ σ ≤ c} N^σ N^{1-σ}/T)`. -/
def LineShift : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ) (A T u : ℝ) (q : ℕ)
    (χ : DirichletCharacter ℂ q) (Nv : Fin 20 → ℝ), N₀ ≤ N → 0 ≤ A →
    A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → Cond35 N Nv → 2 ≤ T → T ≤ N → (N : ℝ) - A ≤ u → u ≤ N →
    ‖Vline Nv χ N A (1 + 1 / Real.log N) T u - Vline Nv χ N A (1 / 2) T u‖
      ≤ K * (N : ℝ) ^ (1 + ε) / T

/-- Partial summation and Lemma 1, page 264 last two displays and page 265 first display: if the
partial sums (3.2) agree with a combination of the line integrals on `Re s = 1/2` up to `E` on
`[N-A, N]`, then `Σ Λ(n)χ(n)e(nλ) ≪ N^{-1/2} Σ |c_i| ∫ min(A, N/min_u |t+2πλu|) |F_i| dt
+ (1 + 2π|λ|A) E`. -/
def PartialSumLemma1 : Prop :=
  ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ) (A lam T : ℝ) (q : ℕ) (χ : DirichletCharacter ℂ q)
    (κ : Type) (ι : Finset κ) (Nf : κ → Fin 20 → ℝ) (c : κ → ℂ) (E : ℝ),
    N₀ ≤ N → 1 ≤ A → A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → 1 ≤ T →
    (∀ u : ℝ, (N : ℝ) - A ≤ u → u ≤ N →
      ‖Psum χ N A u - ∑ i ∈ ι, c i * Vline (Nf i) χ N A (1 / 2) T u‖ ≤ E) →
    ‖Schi χ lam N A‖ ≤ K * (N : ℝ) ^ (-(1 / 2) : ℝ) * (∑ i ∈ ι, ‖c i‖ *
        ∫ t in Set.Icc (-T) T, wt38 N A lam t * ‖Fprod (Nf i) χ (1 / 2 + t * Complex.I)‖)
      + (1 + 2 * π * |lam| * A) * E

/-- The choice (3.7) of `T`, page 264: `2 ≤ T ≤ N` and the summed error
`q (1 + 2π|λ|A) L^20 T⁻¹ N^{1+ε} ≪ q^{1/2} A L^{-B-1}`. -/
def TChoice : Prop :=
  ∀ B c1 c2 c3 ε : ℝ, 0 < B → 0 < c1 → 0 < c2 → c1 ≤ c3 → 0 < ε → ε ≤ 1 / 20 →
    ∃ K N₀ : ℝ, ∀ (N : ℕ) (A lam : ℝ) (q : ℕ), N₀ ≤ N → Hyp2 c1 c2 c3 N A lam q →
      2 ≤ Tcut q N A lam ε ∧ Tcut q N A lam ε ≤ N ∧
      (q : ℝ) * (1 + 2 * π * |lam| * A) *
          (Real.log N ^ (20 : ℝ) * (N : ℝ) ^ (1 + ε) / Tcut q N A lam ε)
        ≤ K * (q : ℝ) ^ (1 / 2 : ℝ) * A * Real.log N ^ (-B - 1)

/-- LEAF: page 264 top, "splitting up each range of the summation in (3.3) into intervals of the
form `x < n ≤ 2x`, `S^(1)` becomes the sum of `O(L^20)` sums" with (3.5). The variables of the
`j`-th Heath-Brown term not used are put in `I = (1/2, 1]`; the `μ` variables are cut at the
points `X 2^{-k}` so that `n ≤ X` is kept exactly. Class MEDIUM. -/
theorem dyadic_split_leaf : DyadicSplit := by
  sorry

/-- LEAF: page 263 display (3.3) and page 264 display (3.4), Perron's summation formula with
`c = 1 + L⁻¹`, error `O(T⁻¹ N^{1+ε})`, using `|a₁(n₁)⋯a₂₀(n₂₀)| ≪ N^{ε/2}`; `T ≤ N` makes the
lattice point term `N^ε` part of the error. Class MEDIUM. -/
theorem perron_trunc_leaf : PerronTrunc := by
  sorry

/-- LEAF: page 264, the shift of the integration line from `Re s = c` to `Re s = 1/2`, with the
horizontal segments bounded by `max_{1/2 ≤ σ ≤ c} N^σ N^{1-σ}/T` up to `N^ε`. Class MEDIUM. -/
theorem line_shift_leaf : LineShift := by
  sorry

/-- LEAF: page 264, the displays after "Hence" and the display after "The inner integral above
can be estimated by Lemma 1", and page 265 first display: partial summation against `e(λu)`,
differentiation of the `S^(2)` integral in `u`, Fubini, and Lemma 1 for
`∫_{N-A}^N u^{-1/2} e(t log u/2π + λu) du ≪ N^{-1/2} min(A, N/min_u |t + 2πλu|)`, applied on the
at most two pieces where `G/F'` is monotone. Class MEDIUM. -/
theorem partialSum_lemma1_leaf (h1 : Lemma1) : PartialSumLemma1 := by
  sorry

/-- PROVED, page 264 display (3.7), "if we take `T = q^{1/2}(NA⁻¹ + |λ|N)N^{2ε}`": the error
`T⁻¹(1 + |λ|A)N^{1+ε}` summed over the `≤ q` characters and `O(L^20)` sums is
`≪ q^{1/2} A L^{-B-1}`, using `L^{B+21} ≤ (B+21)^{B+21} ε^{-B-21} N^ε`; also `2 ≤ T ≤ N`
under Hyp2 with `c₃ ≥ c₁`, since `q^{1/2} N A⁻¹ ≤ N^{1/2}` and `q^{1/2}|λ|N ≤ N^{4/5}`. -/
theorem tChoice_proved : TChoice := by
  intro B c1 c2 c3 ε hB hc1 hc2 hc13 hε hε20
  set β : ℝ := B + 21 with hβ
  have hβpos : 0 < β := by linarith
  set δ : ℝ := ε / β with hδ
  have hδpos : 0 < δ := div_pos hε hβpos
  refine ⟨2 * π * (δ ^ β)⁻¹, 1024, ?_⟩
  intro N A lam q hN hyp
  obtain ⟨hlo, hhi, hq1, -, hqτ, hlam⟩ := hyp
  have hNpos : (0 : ℝ) < N := by linarith
  set L := Real.log (N : ℝ) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hNpos]; linarith [Real.exp_one_lt_d9]
  have hLpos : 0 < L := by linarith
  have hs : (2 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
    have e : (1024 : ℝ) = (2 : ℝ) ^ (10 : ℝ) := by
      rw [show (10 : ℝ) = ((10 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]; norm_num
    have h := Real.rpow_le_rpow (by norm_num : (0 : ℝ) ≤ 1024) hN (by norm_num : (0 : ℝ) ≤ 1 / 10)
    rw [e, ← Real.rpow_mul (by norm_num)] at h
    norm_num at h
    exact h
  have hN1 : (1 : ℝ) ≤ N := by linarith
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  have hq1' : (1 : ℝ) ≤ q := by exact_mod_cast hq1
  have hA1 : 1 ≤ A := by
    refine le_trans ?_ hlo
    have := Real.one_le_rpow hN1 (show (0 : ℝ) ≤ 3 / 5 by norm_num)
    have := Real.one_le_rpow hL1 (show (0 : ℝ) ≤ c3 by linarith)
    nlinarith
  have hApos : 0 < A := by linarith
  -- powers of N
  have pw : ∀ a b : ℝ, (N : ℝ) ^ a * (N : ℝ) ^ b = (N : ℝ) ^ (a + b) := fun a b =>
    (Real.rpow_add hNpos a b).symm
  have hN13 : (N : ℝ) ^ (1 / 10 : ℝ) ≤ (N : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
  have hNA : (N : ℝ) ^ (1 / 3 : ℝ) ≤ N / A := by
    rw [le_div_iff₀ hApos]
    calc (N : ℝ) ^ (1 / 3 : ℝ) * A ≤ (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_left hhi (by positivity)
      _ = N := by rw [pw]; norm_num
  obtain ⟨r, hr⟩ : ∃ r : ℝ, r = (q : ℝ) ^ (1 / 2 : ℝ) := ⟨_, rfl⟩
  have hr1 : 1 ≤ r := hr ▸ Real.one_le_rpow hq1' (by norm_num)
  have hr0 : 0 < r := by linarith
  have hrr : r * r = q := by rw [hr, ← Real.rpow_add hq0]; norm_num
  obtain ⟨τ, hτ⟩ : ∃ τ : ℝ, τ = A ^ 2 / N * L ^ (-c1) := ⟨_, rfl⟩
  rw [← hτ] at hqτ hlam
  have hLc1 : 0 < L ^ (-c1) := Real.rpow_pos_of_pos hLpos _
  have hτpos : 0 < τ := by rw [hτ]; exact mul_pos (div_pos (pow_pos hApos 2) hNpos) hLc1
  obtain ⟨P, hP⟩ : ∃ P : ℝ, P = N / A + |lam| * N := ⟨_, rfl⟩
  have hPpos : 0 < P := by
    rw [hP]; exact add_pos_of_pos_of_nonneg (div_pos hNpos hApos) (mul_nonneg (abs_nonneg _) hNpos.le)
  obtain ⟨n1, hn1⟩ : ∃ n1 : ℝ, n1 = (N : ℝ) ^ ε := ⟨_, rfl⟩
  have hn1pos : 0 < n1 := by rw [hn1]; exact Real.rpow_pos_of_pos hNpos _
  have hTdef : Tcut q N A lam ε = r * P * (n1 * n1) := by
    rw [Tcut, hr, hP, hn1, pw, show ε + ε = 2 * ε by ring]
  have hn11 : n1 * n1 ≤ (N : ℝ) ^ (1 / 10 : ℝ) := by
    rw [hn1, pw]; exact Real.rpow_le_rpow_of_exponent_le hN1 (by linarith)
  have hn11' : 1 ≤ n1 * n1 := by
    have := Real.one_le_rpow hN1 hε.le; rw [hn1]; nlinarith
  refine ⟨?_, ?_, ?_⟩
  · rw [hTdef]
    have : N / A ≤ P := by rw [hP]; have := abs_nonneg lam; nlinarith
    have h2 : 2 ≤ P := by linarith
    calc (2 : ℝ) ≤ P := h2
      _ ≤ r * P := le_mul_of_one_le_left hPpos.le hr1
      _ ≤ r * P * (n1 * n1) := le_mul_of_one_le_right (mul_pos hr0 hPpos).le hn11'
  · -- T ≤ N
    have ha : r * (N / A) ≤ (N : ℝ) ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      apply Real.le_sqrt_of_sq_le
      have h1 : (r * (N / A)) ^ 2 = (r * r) * N ^ 2 / A ^ 2 := by
        field_simp
      rw [h1, hrr, div_le_iff₀ (pow_pos hApos 2)]
      have h2 : (q : ℝ) * N ^ 2 ≤ τ * N ^ 2 := mul_le_mul_of_nonneg_right hqτ (by positivity)
      have h3 : τ * N ^ 2 = N * L ^ (-c1) * A ^ 2 := by rw [hτ]; field_simp
      have h4 : L ^ (-c1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL1 (by linarith)
      have : (N : ℝ) * L ^ (-c1) * A ^ 2 ≤ N * A ^ 2 := by
        have h0 : 0 ≤ (N : ℝ) * A ^ 2 := by positivity
        calc (N : ℝ) * L ^ (-c1) * A ^ 2 = ((N : ℝ) * A ^ 2) * L ^ (-c1) := by ring
          _ ≤ ((N : ℝ) * A ^ 2) * 1 := mul_le_mul_of_nonneg_left h4 h0
          _ = N * A ^ 2 := by ring
      linarith
    have hb : r * (|lam| * N) ≤ (N : ℝ) ^ (4 / 5 : ℝ) := by
      have hl : |lam| ≤ 1 / (q * τ) := hlam
      have h1 : r * (|lam| * N) ≤ r * (N / (q * τ)) := by
        apply mul_le_mul_of_nonneg_left _ (by linarith)
        rw [div_eq_mul_one_div]; rw [mul_comm]; exact mul_le_mul_of_nonneg_left hl hNpos.le
      have h2 : r * (N / (q * τ)) ≤ N / τ := by
        rw [← hrr, show r * (N / (r * r * τ)) = N / τ / r by field_simp]
        exact div_le_self (by positivity) hr1
      have h3 : N / τ = N ^ 2 * L ^ c1 / A ^ 2 := by
        rw [hτ, Real.rpow_neg hLpos.le]; field_simp
      have hA2 : (N : ℝ) ^ (6 / 5 : ℝ) * L ^ c1 ≤ A ^ 2 := by
        have hc : L ^ c1 ≤ L ^ (2 * c3) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
        have ea : ((N : ℝ) ^ (3 / 5 : ℝ)) ^ 2 = (N : ℝ) ^ (6 / 5 : ℝ) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hNpos.le]; norm_num
        have eb : (L ^ c3) ^ 2 = L ^ (2 * c3) := by
          rw [← Real.rpow_natCast, ← Real.rpow_mul hLpos.le]; congr 1; push_cast; ring
        have e : ((N : ℝ) ^ (3 / 5 : ℝ) * L ^ c3) ^ 2 = (N : ℝ) ^ (6 / 5 : ℝ) * L ^ (2 * c3) := by
          rw [mul_pow, ea, eb]
        have hlo2 : ((N : ℝ) ^ (3 / 5 : ℝ) * L ^ c3) ^ 2 ≤ A ^ 2 :=
          pow_le_pow_left₀ (mul_nonneg (by positivity) (Real.rpow_nonneg hLpos.le _)) hlo 2
        rw [e] at hlo2
        have : (N : ℝ) ^ (6 / 5 : ℝ) * L ^ c1 ≤ (N : ℝ) ^ (6 / 5 : ℝ) * L ^ (2 * c3) :=
          mul_le_mul_of_nonneg_left hc (by positivity)
        linarith
      have h4 : (N : ℝ) ^ 2 * L ^ c1 / A ^ 2 ≤ (N : ℝ) ^ (4 / 5 : ℝ) := by
        rw [div_le_iff₀ (pow_pos hApos 2)]
        have e2 : (N : ℝ) ^ 2 = (N : ℝ) ^ (4 / 5 : ℝ) * (N : ℝ) ^ (6 / 5 : ℝ) := by
          rw [pw]; norm_num
        rw [e2]
        have := mul_le_mul_of_nonneg_left hA2 (show 0 ≤ (N : ℝ) ^ (4 / 5 : ℝ) by positivity)
        calc (N : ℝ) ^ (4 / 5 : ℝ) * (N : ℝ) ^ (6 / 5 : ℝ) * L ^ c1
            = (N : ℝ) ^ (4 / 5 : ℝ) * ((N : ℝ) ^ (6 / 5 : ℝ) * L ^ c1) := by ring
          _ ≤ (N : ℝ) ^ (4 / 5 : ℝ) * A ^ 2 := this
      linarith
    have h12 : (N : ℝ) ^ (1 / 2 : ℝ) ≤ (N : ℝ) ^ (4 / 5 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    have hrP : r * P ≤ 2 * (N : ℝ) ^ (4 / 5 : ℝ) := by rw [hP, mul_add]; linarith
    rw [hTdef]
    have e3 : (N : ℝ) = (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (9 / 10 : ℝ) := by
      rw [pw]; norm_num
    have h45 : (N : ℝ) ^ (4 / 5 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) = (N : ℝ) ^ (9 / 10 : ℝ) := by
      rw [pw]; norm_num
    calc r * P * (n1 * n1) ≤ 2 * (N : ℝ) ^ (4 / 5 : ℝ) * (N : ℝ) ^ (1 / 10 : ℝ) :=
          mul_le_mul hrP hn11 (mul_pos hn1pos hn1pos).le (by positivity)
      _ = 2 * (N : ℝ) ^ (9 / 10 : ℝ) := by rw [mul_assoc, h45]
      _ ≤ (N : ℝ) ^ (1 / 10 : ℝ) * (N : ℝ) ^ (9 / 10 : ℝ) :=
          mul_le_mul_of_nonneg_right hs (by positivity)
      _ = N := e3.symm
  · -- the error
    have hLE : L ^ (20 : ℝ) / n1 ≤ (δ ^ β)⁻¹ * L ^ (-B - 1) := by
      have hlog : L ≤ (N : ℝ) ^ δ / δ := Real.log_le_rpow_div hNpos.le hδpos
      have hpow : L ^ β ≤ ((N : ℝ) ^ δ / δ) ^ β := Real.rpow_le_rpow hLpos.le hlog hβpos.le
      have hdb : δ * β = ε := by rw [hδ]; field_simp
      have e1 : ((N : ℝ) ^ δ / δ) ^ β = n1 / δ ^ β := by
        rw [Real.div_rpow (by positivity) hδpos.le, ← Real.rpow_mul hNpos.le, hdb, hn1]
      have e2 : L ^ (20 : ℝ) = L ^ β * L ^ (-B - 1) := by
        rw [← Real.rpow_add hLpos]; congr 1; rw [hβ]; ring
      rw [e2, div_le_iff₀ hn1pos]
      rw [e1] at hpow
      have hd : 0 < δ ^ β := Real.rpow_pos_of_pos hδpos _
      calc L ^ β * L ^ (-B - 1) ≤ n1 / δ ^ β * L ^ (-B - 1) :=
            mul_le_mul_of_nonneg_right hpow (Real.rpow_nonneg hLpos.le _)
        _ = (δ ^ β)⁻¹ * L ^ (-B - 1) * n1 := by ring
    have hg : (1 + 2 * π * |lam| * A) * N ≤ 2 * π * A * P := by
      rw [hP]
      have hpi : 1 ≤ 2 * π := by linarith [Real.pi_gt_three]
      have e : 2 * π * A * (N / A + |lam| * N) = 2 * π * N + 2 * π * |lam| * A * N := by
        field_simp
      rw [e]
      have hNN : (N : ℝ) ≤ 2 * π * N := le_mul_of_one_le_left hNpos.le hpi
      calc (1 + 2 * π * |lam| * A) * N = N + 2 * π * |lam| * A * N := by ring
        _ ≤ 2 * π * N + 2 * π * |lam| * A * N := by linarith
    have hN1e : (N : ℝ) ^ (1 + ε) = N * n1 := by rw [hn1, ← pw, Real.rpow_one]
    rw [hN1e, hTdef, ← hr]
    have hL20 : 0 ≤ L ^ (20 : ℝ) := Real.rpow_nonneg hLpos.le _
    calc (q : ℝ) * (1 + 2 * π * |lam| * A) * (L ^ (20 : ℝ) * (N * n1) / (r * P * (n1 * n1)))
        = r * ((1 + 2 * π * |lam| * A) * N) * (L ^ (20 : ℝ) / n1) / P := by
          rw [← hrr]; field_simp
      _ ≤ r * (2 * π * A * P) * (L ^ (20 : ℝ) / n1) / P := by
          apply div_le_div_of_nonneg_right _ hPpos.le
          apply mul_le_mul_of_nonneg_right _ (div_nonneg (Real.rpow_nonneg hLpos.le _) hn1pos.le)
          exact mul_le_mul_of_nonneg_left hg (by linarith)
      _ = 2 * π * r * A * (L ^ (20 : ℝ) / n1) := by field_simp
      _ ≤ 2 * π * r * A * ((δ ^ β)⁻¹ * L ^ (-B - 1)) :=
          mul_le_mul_of_nonneg_left hLE (mul_nonneg (mul_nonneg (by positivity) hr0.le) hApos.le)
      _ = 2 * π * (δ ^ β)⁻¹ * r * A * L ^ (-B - 1) := by ring


/-! ### PROVED steps -/

/-- PROVED, page 263, Heath-Brown's identity with `k = 10`, `X = N^{1/10}` applied to (3.2). -/
theorem psum_heathBrown {q : ℕ} (χ : DirichletCharacter ℂ q) (N : ℕ) (A u : ℝ) (hN : 1 ≤ N)
    (hu0 : 0 ≤ u) (hu : u ≤ N) :
    Psum χ N A u = ∑ j ∈ Finset.Icc 1 10,
      ((-1 : ℂ) ^ (j - 1) * (Nat.choose 10 j : ℂ)) * HBsum j χ N A u := by
  have hN' : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hX : (1 : ℝ) ≤ (N : ℝ) ^ (1 / 10 : ℝ) := Real.one_le_rpow hN' (by norm_num)
  have hX10 : ((N : ℝ) ^ (1 / 10 : ℝ)) ^ (10 : ℕ) = N := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]; norm_num
  unfold Psum HBsum
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Finset.mem_filter, Finset.mem_Icc] at hn
  have hnN : (n : ℝ) ≤ ((N : ℝ) ^ (1 / 10 : ℝ)) ^ 10 := by
    rw [hX10]
    have h1 : (n : ℝ) ≤ (⌊u⌋₊ : ℝ) := by exact_mod_cast hn.1.2
    linarith [Nat.floor_le hu0]
  rw [heathBrown_identity 10 _ hX n hn.1.1 hnN]
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- PROVED: the hypotheses of Theorem 2 are monotone in `c₃`, since `L ≥ 1`. -/
theorem hyp2_mono_c3 {c1 c2 c3 c3' : ℝ} {N : ℕ} {A lam : ℝ} {q : ℕ} (h : c3 ≤ c3')
    (hL : 1 ≤ Real.log N) (hH : Hyp2 c1 c2 c3' N A lam q) : Hyp2 c1 c2 c3 N A lam q := by
  obtain ⟨h1, h2⟩ := hH
  exact ⟨le_trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hL h)
    (by positivity)) h1, h2⟩

/-- PROVED: the number of Dirichlet characters mod `q` is at most `q`. -/
theorem card_chars_le (q : ℕ) [NeZero q] :
    ((Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1)).card ≤ (q : ℝ) := by
  have h1 := Finset.card_filter_le (Finset.univ : Finset (DirichletCharacter ℂ q)) (· ≠ 1)
  have h2 : (Finset.univ : Finset (DirichletCharacter ℂ q)).card = q.totient := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  have h3 := Nat.totient_le q
  exact_mod_cast le_trans h1 (h2 ▸ h3)

/-- PROVED, pages 263 to 265: (3.8) gives (3.1) from the five steps H2 to H5 and (3.7), with
Heath-Brown's identity proved above. Constants: `ε = 1/20`, `c₀ = 21`, `c₃` replaced by
`max c₃ c₁`. -/
theorem eq31_of_parts (h38 : Eq38) (hD : DyadicSplit) (hP : PerronTrunc) (hS : LineShift)
    (hH : PartialSumLemma1) (hT : TChoice) : Eq31 := by
  intro B hB
  obtain ⟨c1m, h38⟩ := h38 B hB 21 (by norm_num) (1 / 20) (by norm_num)
  refine ⟨max c1m 1, fun c1 hc1 => ?_⟩
  obtain ⟨c2m, h38⟩ := h38 c1 (le_trans (le_max_left _ _) hc1)
  have hc1p : 0 < c1 := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hc1)
  refine ⟨max c2m 1, fun c2 hc2 => ?_⟩
  obtain ⟨c3, hc3, K8, N8, e38⟩ := h38 c2 (le_trans (le_max_left _ _) hc2)
  have hc2p : 0 < c2 := lt_of_lt_of_le one_pos (le_trans (le_max_right _ _) hc2)
  obtain ⟨KD, ND, eD⟩ := hD
  obtain ⟨KP, NP, hKP, eP⟩ := hP (1 / 20) (by norm_num)
  obtain ⟨KS, NS, hKS, eS⟩ := hS (1 / 20) (by norm_num)
  obtain ⟨KH, NH, hKH, eH⟩ := hH
  obtain ⟨KT, NT, eT⟩ := hT B c1 c2 (max c3 c1) (1 / 20) hB hc1p hc2p (le_max_right _ _)
    (by norm_num) le_rfl
  set Cc : ℝ := 1024 * 10 * KD with hCc
  refine ⟨max c3 c1, lt_of_lt_of_le hc3 (le_max_left _ _),
    KH * Cc * max K8 0 + (KP + KS) * Cc * KT,
    max (max (max N8 ND) (max NP NS)) (max (max NH NT) 3), ?_⟩
  intro N A lam q _ hN hyp
  have hN8 : N8 ≤ N := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_left _ _))) hN
  have hND : ND ≤ N := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) (le_max_left _ _))) hN
  have hNP : NP ≤ N := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_right _ _) (le_max_left _ _))) hN
  have hNS : NS ≤ N := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_right _ _) (le_max_left _ _))) hN
  have hNH : NH ≤ N := le_trans (le_trans (le_max_left _ _)
    (le_trans (le_max_left _ _) (le_max_right _ _))) hN
  have hNT : NT ≤ N := le_trans (le_trans (le_max_right _ _)
    (le_trans (le_max_left _ _) (le_max_right _ _))) hN
  have hN3 : (3 : ℝ) ≤ N := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hN)
  set L := Real.log (N : ℝ) with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]; linarith [Real.exp_one_lt_d9]
  have hLpos : 0 < L := by linarith
  have hN1 : 1 ≤ N := by exact_mod_cast (show (1 : ℝ) ≤ N by linarith)
  have hyp3 : Hyp2 c1 c2 c3 N A lam q := hyp2_mono_c3 (le_max_left _ _) hL1 hyp
  have hlo := hyp.1
  have hhi := hyp.2.1
  have hA1 : 1 ≤ A := by
    refine le_trans ?_ hlo
    have := Real.one_le_rpow (show (1 : ℝ) ≤ N by linarith) (show (0 : ℝ) ≤ 3 / 5 by norm_num)
    have := Real.one_le_rpow hL1 (le_trans hc3.le (le_max_left c3 c1))
    nlinarith
  have hA0 : 0 ≤ A := by linarith
  obtain ⟨hT2, hTN, hTerr⟩ := eT N A lam q hNT hyp
  have hAN : A ≤ N := by
    refine le_trans hhi ?_
    calc (N : ℝ) ^ (2 / 3 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = N := Real.rpow_one _
  set T := Tcut q N A lam (1 / 20) with hTdef
  have hT1 : (1 : ℝ) ≤ T := by linarith
  have hTpos : 0 < T := by linarith
  have hDj := eD N A hND hA0 hhi
  choose! ιf hιcard hιc hιeq using hDj
  set ι : Finset (Σ _ : ℕ, Fin 20 → ℝ) := (Finset.Icc 1 10).sigma ιf with hιdef
  set c : (Σ _ : ℕ, Fin 20 → ℝ) → ℂ :=
    fun p => (-1 : ℂ) ^ (p.1 - 1) * (Nat.choose 10 p.1 : ℂ) with hcdef
  set X : ℝ := (N : ℝ) ^ (1 + 1 / 20 : ℝ) / T with hXdef
  set Ctot : ℝ := ∑ p ∈ ι, ‖c p‖ with hCtot
  have hc_le : ∀ p, ‖c p‖ ≤ 1024 := by
    intro p
    have h := Nat.choose_le_two_pow 10 p.1
    have h' : ((Nat.choose 10 p.1 : ℕ) : ℝ) ≤ 1024 := by exact_mod_cast h
    simpa [hcdef, norm_mul, norm_pow] using h'
  have hLpow : 0 < L ^ (20 : ℝ) := Real.rpow_pos_of_pos hLpos _
  have hKD : 0 ≤ KD := by
    by_contra hneg
    push Not at hneg
    have h1 := hιcard 1 (by simp)
    have h2 := mul_neg_of_neg_of_pos hneg hLpow
    have h3 : (0 : ℝ) ≤ ((ιf 1).card : ℝ) := Nat.cast_nonneg _
    linarith
  have hCbound : Ctot ≤ Cc * L ^ (20 : ℝ) := by
    calc Ctot = ∑ j ∈ Finset.Icc 1 10, ∑ Nv ∈ ιf j, ‖c ⟨j, Nv⟩‖ := by
          rw [hCtot, hιdef, Finset.sum_sigma]
      _ ≤ ∑ j ∈ Finset.Icc 1 10, ((ιf j).card : ℝ) * 1024 := by
          apply Finset.sum_le_sum
          intro j _
          refine le_trans (Finset.sum_le_card_nsmul _ _ 1024 (fun x _ => hc_le _)) ?_
          rw [nsmul_eq_mul]
      _ ≤ ∑ j ∈ Finset.Icc 1 10, (KD * L ^ (20 : ℝ)) * 1024 :=
          Finset.sum_le_sum fun j hj => mul_le_mul_of_nonneg_right (hιcard j hj) (by norm_num)
      _ = Cc * L ^ (20 : ℝ) := by
          rw [Finset.sum_const, Nat.card_Icc, nsmul_eq_mul, hCc]; push_cast; ring
  have hCtot0 : 0 ≤ Ctot := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hrep : ∀ χ : DirichletCharacter ℂ q, ∀ u : ℝ, (N : ℝ) - A ≤ u → u ≤ N →
      ‖Psum χ N A u - ∑ p ∈ ι, c p * Vline p.2 χ N A (1 / 2) T u‖
        ≤ Ctot * ((KP + KS) * X) := by
    intro χ u hu1 hu2
    have hu0 : 0 ≤ u := by linarith
    have e1 : Psum χ N A u = ∑ p ∈ ι, c p * Dsum p.2 χ N A u := by
      rw [psum_heathBrown χ N A u hN1 hu0 hu2, hιdef, Finset.sum_sigma]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hιeq j hj q χ u hu1 hu2, Finset.mul_sum]
    rw [e1, ← Finset.sum_sub_distrib, hCtot, Finset.sum_mul]
    refine le_trans (norm_sum_le _ _) (Finset.sum_le_sum fun p hp => ?_)
    rw [← mul_sub, norm_mul]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hp2 : Cond35 N p.2 := by
      rw [hιdef, Finset.mem_sigma] at hp; exact hιc p.1 hp.1 p.2 hp.2
    have a1 := eP N A T u q χ p.2 hNP hA0 hhi hp2 hT2 hTN hu1 hu2
    have a2 := eS N A T u q χ p.2 hNS hA0 hhi hp2 hT2 hTN hu1 hu2
    calc ‖Dsum p.2 χ N A u - Vline p.2 χ N A (1 / 2) T u‖
        ≤ ‖Dsum p.2 χ N A u - Vline p.2 χ N A (1 + 1 / L) T u‖ +
          ‖Vline p.2 χ N A (1 + 1 / L) T u - Vline p.2 χ N A (1 / 2) T u‖ :=
          norm_sub_le_norm_sub_add_norm_sub _ _ _
      _ ≤ KP * (N : ℝ) ^ (1 + 1 / 20 : ℝ) / T + KS * (N : ℝ) ^ (1 + 1 / 20 : ℝ) / T :=
          add_le_add a1 a2
      _ = (KP + KS) * X := by rw [hXdef]; ring
  set F := (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1) with hF
  set Y : ℝ := ((q : ℝ) * N) ^ (1 / 2 : ℝ) * A * L ^ (-B - 21) with hY
  have hY0 : 0 ≤ Y := mul_nonneg (mul_nonneg (by positivity) hA0) (Real.rpow_nonneg hLpos.le _)
  set g : ℝ := 1 + 2 * π * |lam| * A with hg
  have hg0 : 0 ≤ g := add_nonneg zero_le_one (mul_nonneg (by positivity) hA0)
  have hper : ∀ χ ∈ F, ‖Schi χ lam N A‖ ≤ KH * (N : ℝ) ^ (-(1 / 2) : ℝ) *
      (∑ p ∈ ι, ‖c p‖ * ∫ t in Set.Icc (-T) T,
        wt38 N A lam t * ‖Fprod p.2 χ (1 / 2 + t * Complex.I)‖) + g * (Ctot * ((KP + KS) * X)) := by
    intro χ _
    have h := eH N A lam T q χ (Σ _ : ℕ, Fin 20 → ℝ) ι (fun p => p.2) c
      (Ctot * ((KP + KS) * X)) hNH hA1 hhi hT1 (hrep χ)
    exact h
  have hI : ∀ p ∈ ι, ∑ χ ∈ F, ∫ t in Set.Icc (-T) T,
      wt38 N A lam t * ‖Fprod p.2 χ (1 / 2 + t * Complex.I)‖ ≤ max K8 0 * Y := by
    intro p hp
    have hp2 : Cond35 N p.2 := by
      rw [hιdef, Finset.mem_sigma] at hp; exact hιc p.1 hp.1 p.2 hp.2
    have h := e38 N A lam q p.2 hN8 hyp3 hp2
    refine le_trans h ?_
    have : K8 * ((q : ℝ) * N) ^ (1 / 2 : ℝ) * A * L ^ (-B - 21) = K8 * Y := by
      rw [hY]; ring
    rw [this]
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) hY0
  have hswap : ∑ χ ∈ F, ∑ p ∈ ι, ‖c p‖ * ∫ t in Set.Icc (-T) T,
        wt38 N A lam t * ‖Fprod p.2 χ (1 / 2 + t * Complex.I)‖
      = ∑ p ∈ ι, ‖c p‖ * ∑ χ ∈ F, ∫ t in Set.Icc (-T) T,
        wt38 N A lam t * ‖Fprod p.2 χ (1 / 2 + t * Complex.I)‖ := by
    rw [Finset.sum_comm]; simp_rw [Finset.mul_sum]
  have hb2 : ∑ p ∈ ι, ‖c p‖ * ∑ χ ∈ F, ∫ t in Set.Icc (-T) T,
        wt38 N A lam t * ‖Fprod p.2 χ (1 / 2 + t * Complex.I)‖ ≤ Ctot * (max K8 0 * Y) := by
    rw [hCtot, Finset.sum_mul]
    exact Finset.sum_le_sum fun p hp => mul_le_mul_of_nonneg_left (hI p hp) (norm_nonneg _)
  have hNh : 0 ≤ (N : ℝ) ^ (-(1 / 2) : ℝ) := by positivity
  have hsum : ∑ χ ∈ F, ‖Schi χ lam N A‖ ≤ KH * (N : ℝ) ^ (-(1 / 2) : ℝ) * (Ctot * (max K8 0 * Y))
      + (F.card : ℝ) * (g * (Ctot * ((KP + KS) * X))) := by
    refine le_trans (Finset.sum_le_sum hper) ?_
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, hswap, Finset.sum_const, nsmul_eq_mul]
    exact add_le_add (mul_le_mul_of_nonneg_left hb2 (mul_nonneg hKH.le hNh)) le_rfl
  have eN : (N : ℝ) ^ (-(1 / 2) : ℝ) * ((q : ℝ) * N) ^ (1 / 2 : ℝ) = (q : ℝ) ^ (1 / 2 : ℝ) := by
    rw [Real.mul_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity)]
    have : (0 : ℝ) < (N : ℝ) ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos (by linarith) _
    field_simp
  have eLL : L ^ (20 : ℝ) * L ^ (-B - 21) = L ^ (-B - 1) := by
    rw [← Real.rpow_add hLpos]; congr 1; ring
  have t1 : KH * (N : ℝ) ^ (-(1 / 2) : ℝ) * (Ctot * (max K8 0 * Y))
      ≤ KH * Cc * max K8 0 * ((q : ℝ) ^ (1 / 2 : ℝ) * A * L ^ (-B - 1)) := by
    have hk : 0 ≤ KH * (N : ℝ) ^ (-(1 / 2) : ℝ) * (max K8 0 * Y) :=
      mul_nonneg (mul_nonneg hKH.le hNh) (mul_nonneg (le_max_right _ _) hY0)
    calc KH * (N : ℝ) ^ (-(1 / 2) : ℝ) * (Ctot * (max K8 0 * Y))
        = (KH * (N : ℝ) ^ (-(1 / 2) : ℝ) * (max K8 0 * Y)) * Ctot := by ring
      _ ≤ (KH * (N : ℝ) ^ (-(1 / 2) : ℝ) * (max K8 0 * Y)) * (Cc * L ^ (20 : ℝ)) :=
          mul_le_mul_of_nonneg_left hCbound hk
      _ = KH * Cc * max K8 0 * (((N : ℝ) ^ (-(1 / 2) : ℝ) * ((q : ℝ) * N) ^ (1 / 2 : ℝ)) *
            (L ^ (20 : ℝ) * L ^ (-B - 21))) * A := by rw [hY]; ring
      _ = KH * Cc * max K8 0 * ((q : ℝ) ^ (1 / 2 : ℝ) * A * L ^ (-B - 1)) := by
          rw [eN, eLL]; ring
  have hX0 : 0 ≤ X := div_nonneg (by positivity) hTpos.le
  have hW : 0 ≤ (KP + KS) * X := mul_nonneg (by linarith) hX0
  have hCc0 : 0 ≤ Cc := by rw [hCc]; positivity
  have t2 : (F.card : ℝ) * (g * (Ctot * ((KP + KS) * X)))
      ≤ (KP + KS) * Cc * KT * ((q : ℝ) ^ (1 / 2 : ℝ) * A * L ^ (-B - 1)) := by
    calc (F.card : ℝ) * (g * (Ctot * ((KP + KS) * X)))
        ≤ (q : ℝ) * (g * (Cc * L ^ (20 : ℝ) * ((KP + KS) * X))) :=
          mul_le_mul (card_chars_le q)
            (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hCbound hW) hg0)
            (mul_nonneg hg0 (mul_nonneg hCtot0 hW)) (by positivity)
      _ = (KP + KS) * Cc * ((q : ℝ) * (1 + 2 * π * |lam| * A) *
            (L ^ (20 : ℝ) * (N : ℝ) ^ (1 + 1 / 20 : ℝ) / T)) := by rw [hXdef, hg]; ring
      _ ≤ (KP + KS) * Cc * (KT * (q : ℝ) ^ (1 / 2 : ℝ) * A * L ^ (-B - 1)) :=
          mul_le_mul_of_nonneg_left hTerr (mul_nonneg (by linarith) hCc0)
      _ = (KP + KS) * Cc * KT * ((q : ℝ) ^ (1 / 2 : ℝ) * A * L ^ (-B - 1)) := by ring
  calc ∑ χ ∈ F, ‖Schi χ lam N A‖
      ≤ KH * Cc * max K8 0 * ((q : ℝ) ^ (1 / 2 : ℝ) * A * L ^ (-B - 1)) +
        (KP + KS) * Cc * KT * ((q : ℝ) ^ (1 / 2 : ℝ) * A * L ^ (-B - 1)) :=
        le_trans hsum (add_le_add t1 t2)
    _ = (KH * Cc * max K8 0 + (KP + KS) * Cc * KT) * (q : ℝ) ^ (1 / 2 : ℝ) * A *
        L ^ (-B - 1) := by ring

/-- PROVED from the LEAF steps: (3.8) gives (3.1), pages 263 to 265. This refines
`eq31_of_eq38_leaf` of SPLIT_theorem2_1122.lean; Lemma 1 enters through H5. -/
theorem eq31_of_eq38_split (h38 : Eq38) : Eq31 :=
  eq31_of_parts h38 dyadic_split_leaf perron_trunc_leaf line_shift_leaf
    (partialSum_lemma1_leaf zhan_lemma1_leaf) tChoice_proved

end

end LeanLab.Zhan1991
