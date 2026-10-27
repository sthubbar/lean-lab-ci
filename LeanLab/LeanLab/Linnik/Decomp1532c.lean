/-
Unit U-1532, run 20261026T0004Z-24325, DECOMPOSE.
Gallagher 1975, Primes and powers of 2, Invent. Math. 29, 125-142, base g = 2.

File c: display (6) for `k ≥ k₀`, p. 139, the one analytic input still open in the lab's
proof of Theorems 1 and 2. The integral over `[0, 1]` is split as on p. 138 into the major arcs
`𝔐`, the part `C(𝔐) ∩ ℰ` where `|G| ≥ (1 - η)L`, and `C(𝔐) ∩ C(ℰ)`, with
`η = (log k)/k` and `θ = 2 ε(η)`, `ε(η) = (4/log 2) η log(e/η)` the exponent of Lemma 2.
Leaves: display (5) on the major arcs, Lemma 11 off the major arcs, four parameter facts, the
measurability of `𝔐`, and the identity of the two spellings of `G`.
Assemblies: `display6Large_of_leaves`, display (6) for large `k`, and from it Theorems 1 and 2,
display (3) and (4) p. 125, through the lab's proved Lemma 12 and Lemma 2.

AI-written Lean code, Claude, 2026-10-26. Checked only by the Lean kernel.
Binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Linnik.Decomp1532b
import LeanLab.Linnik.Gallagher1975Lemma2
import LeanLab.Romanov.GallagherBridge

namespace LeanLab.Linnik.Decomp1532c

open Finset MeasureTheory
open LeanLab.Linnik.Decomp1532b (majorArcs)
open LeanLab.Linnik.U7204 (Sg)
open LeanLab.Linnik.U1426ChainWire (Gs continuous_Gs)

/-- `η = (log k)/k`, p. 139. -/
noncomputable def etaK (k : ℕ) : ℝ := Real.log k / k

/-- `ε(η) = (4/log 2) η log(e/η)`, the exponent of the lab's Lemma 2 for g = 2, p. 132. -/
noncomputable def epsK (k : ℕ) : ℝ :=
  4 / Real.log 2 * etaK k * Real.log (Real.exp 1 / etaK k)

/-- `θ = 2 ε(η)`, the choice `θ = 2Cη log(e/η)` of p. 139. -/
noncomputable def thetaK (k : ℕ) : ℝ := 2 * epsK k

/-- LEAF. Unit U-1532. The major arcs form a measurable set, p. 127, display (2). -/
theorem measurableSet_majorArcs (N : ℕ) (P : ℝ) : MeasurableSet (majorArcs N P) := by
  sorry

/-- LEAF. Unit U-1532. The two spellings of `G(α) = Σ_{ν=1}^{L} e(2^ν α)` in the lab agree,
p. 132. -/
theorem G_eq_Gs (L : ℕ) (α : ℝ) : LeanLab.Linnik.Gallagher1975Lemma1.G L α = Gs L α := by
  sorry

/-- LEAF. Unit U-1532. Display (5), p. 138, for g = 2 where `D/φ(D) = 2`: there are `c > 0`,
`C` and `θ₀ > 0` such that for `0 < θ ≤ θ₀`, `k ≥ 2` and `N ≥ N_{k,θ}`, with `P = N^θ`,
`∫_𝔐 |S G^k|² ≤ 2 N L^{2k}/log² N · (1 + C(log² k / k + e^{-c/θ}))`. It follows from
Theorem 3, p. 127, and Lemmas 5, 6, 8 and 10. -/
theorem major_arc_bound : ∃ c C θ₀ : ℝ, 0 < c ∧ 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
    ∀ k : ℕ, 2 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N →
      ∫ α in majorArcs N ((N : ℝ) ^ θ), ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2 ≤
        2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2 *
          (1 + C * (Real.log k ^ 2 / k + Real.exp (-c / θ))) := by
  sorry

/-- LEAF. Unit U-1532. Lemma 11, display (1) p. 137, Vinogradov and Montgomery: there are `C`,
`θ₀ > 0` and `E` such that for `0 < θ ≤ θ₀`, `N ≥ 2`, `P = N^θ` and `α ∈ [0, 1]` off the major
arcs, `|S(α)| ≤ C N P^{-1/2} L^E`. -/
theorem lemma11 : ∃ C θ₀ : ℝ, ∃ E : ℕ, 0 < θ₀ ∧ ∀ θ : ℝ, 0 < θ → θ ≤ θ₀ →
    ∀ N : ℕ, 2 ≤ N → ∀ α ∈ Set.Icc (0 : ℝ) 1, α ∉ majorArcs N ((N : ℝ) ^ θ) →
      ‖Sg N α‖ ≤ C * N * (Nat.log 2 N : ℝ) ^ E / (N : ℝ) ^ (θ / 2) := by
  sorry

/-- LEAF. Unit U-1532. `θ = 2(4/log 2) η log(e/η)` with `η = (log k)/k` is positive and tends
to 0, so `θ ≤ θ₀` for large `k`, p. 139. -/
theorem thetaK_small (θ₀ : ℝ) (hθ₀ : 0 < θ₀) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 0 < thetaK k ∧ thetaK k ≤ θ₀ := by
  sorry

/-- LEAF. Unit U-1532. With this `θ`, `θ ≍ log² k / k`, so `e^{-c/θ} ≤ log²(2k)/k` for large
`k`, which absorbs the term `e^{-c/θ}` of display (5) into display (6), p. 139. -/
theorem exp_neg_le (c : ℝ) (hc : 0 < c) :
    ∃ K : ℕ, ∀ k : ℕ, K ≤ k → Real.exp (-c / thetaK k) ≤ Real.log (2 * k) ^ 2 / k := by
  sorry

/-- LEAF. Unit U-1532. `0 < η = (log k)/k ≤ 1/16` for large `k`, the range where Lemma 2 of
p. 132 applies, p. 139. -/
theorem etaK_small : ∃ K : ℕ, ∀ k : ℕ, K ≤ k → 0 < etaK k ∧ etaK k ≤ 1 / 16 := by
  sorry

/-- LEAF. Unit U-1532. Any fixed power of `L = [log₂ N]` is beaten by any fixed power of `N`:
`A L^E ≤ N^ε` for large `N`; the last step `= o_η(N L^{2k-2})` of p. 139, line 3. -/
theorem power_le (A : ℝ) (E : ℕ) (ε : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → A * (Nat.log 2 N : ℝ) ^ E ≤ (N : ℝ) ^ ε := by
  sorry

/-- PROVED. The three way split of p. 138 for a continuous integrand. -/
theorem split3 (f : ℝ → ℝ) (hf : Continuous f) {M E : Set ℝ} (hM : MeasurableSet M)
    (hMs : M ⊆ Set.Icc 0 1) (hE : MeasurableSet E) :
    ∫ α in Set.Icc (0 : ℝ) 1, f α = (∫ α in M, f α) + (∫ α in (Set.Icc 0 1 \ M) ∩ E, f α) +
      ∫ α in (Set.Icc 0 1 \ M) \ E, f α := by
  have hI : IntegrableOn f (Set.Icc (0 : ℝ) 1) := hf.integrableOn_Icc
  have h1 := integral_inter_add_sdiff hM hI
  have h2 := integral_inter_add_sdiff (s := Set.Icc (0 : ℝ) 1 \ M) hE
    (hI.mono_set Set.diff_subset)
  rw [Set.inter_eq_right.mpr hMs] at h1
  linarith

/-- PROVED. On a set of finite measure at most `V` where `|S| ≤ B`,
`∫ |S G^k|² ≤ B² L^{2k} V`, using `|G| ≤ L`. -/
theorem sup_piece {k N : ℕ} {S : Set ℝ} {B V : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ α ∈ S, ‖Sg N α‖ ≤ B) (hV0 : 0 ≤ V) (hV : volume S ≤ ENNReal.ofReal V) :
    ∫ α in S, ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2 ≤
      B ^ 2 * (Nat.log 2 N : ℝ) ^ (2 * k) * V := by
  have hfin : volume S < ⊤ := lt_of_le_of_lt hV ENNReal.ofReal_lt_top
  have hbound : ∀ α ∈ S, ‖‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2‖ ≤
      B ^ 2 * (Nat.log 2 N : ℝ) ^ (2 * k) := by
    intro α hα
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), norm_mul, norm_pow]
    have hG := LeanLab.Linnik.U7206.norm_Gs_le (Nat.log 2 N) α
    rw [show B ^ 2 * (Nat.log 2 N : ℝ) ^ (2 * k) = (B * (Nat.log 2 N : ℝ) ^ k) ^ 2 by ring]
    gcongr
    exact hB α hα
  have h1 := norm_setIntegral_le_of_norm_le_const hfin hbound
  have hreal : volume.real S ≤ V := by
    rw [measureReal_def]
    exact ENNReal.toReal_le_of_le_ofReal hV0 hV
  calc ∫ α in S, ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2
      ≤ ‖∫ α in S, ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2‖ := Real.le_norm_self _
    _ ≤ B ^ 2 * (Nat.log 2 N : ℝ) ^ (2 * k) * volume.real S := h1
    _ ≤ B ^ 2 * (Nat.log 2 N : ℝ) ^ (2 * k) * V := mul_le_mul_of_nonneg_left hreal (by positivity)

/-- PROVED. The algebra of the `C(𝔐) ∩ ℰ` piece, p. 139, line 3. -/
theorem alg_piece2 {C l n x k : ℝ} {E j : ℕ} (hx : 0 < x) (hn : 0 < n) (hk : 0 < k) (hl : 0 ≤ l)
    (hA : 4 * C ^ 2 * k * l ^ (2 * E + 2) ≤ x) :
    (|C| * n * l ^ E / x) ^ 2 * (l ^ j * l ^ 2) * (4 * (x / n)) ≤ n * l ^ j / k := by
  have hid : (|C| * n * l ^ E / x) ^ 2 * (l ^ j * l ^ 2) * (4 * (x / n)) =
      (4 * C ^ 2 * k * l ^ (2 * E + 2)) * (n * l ^ j / k) / x := by
    rw [div_pow, mul_pow, mul_pow, sq_abs]
    field_simp
    ring
  rw [hid]
  have h0 : 0 ≤ n * l ^ j / k := by positivity
  calc (4 * C ^ 2 * k * l ^ (2 * E + 2)) * (n * l ^ j / k) / x
      ≤ x * (n * l ^ j / k) / x :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hA h0) hx.le
    _ = n * l ^ j / k := by field_simp

/-- PROVED. The final bookkeeping of p. 139: the three pieces add up to display (6). -/
theorem alg_final {I1 I2 I3 main W y C5 R e2 : ℝ} (hI1 : I1 ≤ main * (1 + 2 * |C5| * y))
    (hI2 : I2 ≤ y * W) (hI3 : I3 ≤ R * e2 * y * W) (hW : W ≤ main / 2) (hy : 0 ≤ y)
    (hR : 0 ≤ R) (he : 0 ≤ e2) (hmain : 0 ≤ main) :
    I1 + I2 + I3 ≤ main * (1 + (2 * |C5| + 1 + R * e2) * y) := by
  have h1 : 0 ≤ (1 + R * e2) * y := by positivity
  have h2 := mul_le_mul_of_nonneg_left hW h1
  have h3 : 0 ≤ (1 + R * e2) * y * main := by positivity
  nlinarith

/-- PROVED. Piece `C(𝔐) ∩ ℰ` of p. 139 from Lemma 11, the lab's Lemma 2, and `A L^{2E+2} ≤ P^{1/2}`:
`∫ ≤ N L^{2k-2}/k`. -/
theorem piece2 {k N : ℕ} (hk : 3 ≤ k) (hN8 : 8 ≤ N) {C11 : ℝ} {E : ℕ}
    (hη0 : 0 < etaK k) (hη : etaK k ≤ 1 / 16)
    (h11 : ∀ α ∈ Set.Icc (0 : ℝ) 1, α ∉ majorArcs N ((N : ℝ) ^ thetaK k) →
      ‖Sg N α‖ ≤ C11 * N * (Nat.log 2 N : ℝ) ^ E / (N : ℝ) ^ (thetaK k / 2))
    (hA : 4 * C11 ^ 2 * k * (Nat.log 2 N : ℝ) ^ (2 * E + 2) ≤ (N : ℝ) ^ (thetaK k / 2)) :
    ∫ α in (Set.Icc 0 1 \ majorArcs N ((N : ℝ) ^ thetaK k)) ∩
        {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖},
      ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2 ≤
        (N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2) / k := by
  have hN2 : 2 ≤ N := by omega
  have hL3 : 3 ≤ Nat.log 2 N := Nat.le_log_of_pow_le (by norm_num) (by norm_num; omega)
  have hLr3 : (3 : ℝ) ≤ (Nat.log 2 N : ℝ) := by exact_mod_cast hL3
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hk0 : (0 : ℝ) < k := by exact_mod_cast (show 0 < k by omega)
  have hx : 0 < (N : ℝ) ^ (thetaK k / 2) := Real.rpow_pos_of_pos hNr _
  have hB : ∀ α ∈ (Set.Icc 0 1 \ majorArcs N ((N : ℝ) ^ thetaK k)) ∩
      {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖},
      ‖Sg N α‖ ≤ |C11| * N * (Nat.log 2 N : ℝ) ^ E / (N : ℝ) ^ (thetaK k / 2) := by
    intro α hα
    refine (h11 α hα.1.1 hα.1.2).trans ?_
    apply div_le_div_of_nonneg_right _ hx.le
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hNr.le
  have hη4 : etaK k ≤ 1 / 4 := by linarith
  have hηa : 0 < 4 * etaK k * ((Nat.log 2 N : ℕ) : ℝ) := by positivity
  have hηb : 4 * etaK k * ((Nat.log 2 N : ℕ) : ℝ) ≤ ((Nat.log 2 N - 1 : ℕ) : ℝ) := by
    rw [Nat.cast_sub (by omega)]
    push_cast
    nlinarith
  have hL2 := LeanLab.Linnik.Gallagher1975Lemma1.lemma2 N hN2 (etaK k) hηa hηb hη4
  have hsub : (Set.Icc 0 1 \ majorArcs N ((N : ℝ) ^ thetaK k)) ∩
      {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖} ⊆
      LeanLab.Linnik.Gallagher1975Lemma1.bigSet (Nat.log 2 N) (etaK k) ∪ {1} := by
    intro α hα
    have hI : α ∈ Set.Icc (0 : ℝ) 1 := hα.1.1
    have hE : (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖ := hα.2
    rcases eq_or_lt_of_le hI.2 with h1 | h1
    · right; exact h1
    · left
      refine ⟨⟨hI.1, h1⟩, ?_⟩
      rw [G_eq_Gs]
      exact hE
  have hV : volume ((Set.Icc 0 1 \ majorArcs N ((N : ℝ) ^ thetaK k)) ∩
      {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖}) ≤
      ENNReal.ofReal (4 * (N : ℝ) ^ (epsK k - 1)) := by
    calc _ ≤ volume (LeanLab.Linnik.Gallagher1975Lemma1.bigSet (Nat.log 2 N) (etaK k) ∪ {1}) :=
          measure_mono hsub
      _ ≤ volume (LeanLab.Linnik.Gallagher1975Lemma1.bigSet (Nat.log 2 N) (etaK k)) +
            volume ({1} : Set ℝ) := measure_union_le _ _
      _ = volume (LeanLab.Linnik.Gallagher1975Lemma1.bigSet (Nat.log 2 N) (etaK k)) := by
          rw [Real.volume_singleton, add_zero]
      _ ≤ ENNReal.ofReal (4 * (N : ℝ) ^ (epsK k - 1)) := hL2
  have h := sup_piece (k := k) (by positivity) hB (by positivity) hV
  have hθx : epsK k = thetaK k / 2 := by rw [thetaK]; ring
  have hVx : (N : ℝ) ^ (epsK k - 1) = (N : ℝ) ^ (thetaK k / 2) / N := by
    rw [hθx, Real.rpow_sub_one hNr.ne']
  have hpow : (Nat.log 2 N : ℝ) ^ (2 * k) =
      (Nat.log 2 N : ℝ) ^ (2 * k - 2) * (Nat.log 2 N : ℝ) ^ 2 := by
    rw [← pow_add]; congr 1; omega
  rw [hVx, hpow] at h
  exact h.trans (alg_piece2 hx hNr hk0 (Nat.cast_nonneg _) hA)

/-- PROVED. Piece `C(𝔐) ∩ C(ℰ)` of p. 139 from the lab's proved Lemma 12 arc bound:
`∫ ≤ R e² y N L^{2k-2}` with `y = log²(2k)/k`, `R = 8(9 + 2R₁)`. -/
theorem piece3 {k N : ℕ} (hk : 3 ≤ k) {M : Set ℝ} (hM : MeasurableSet M) :
    ∫ α in (Set.Icc 0 1 \ M) \
        {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖},
      ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2 ≤
        8 * (9 + 2 * LeanLab.Romanov.R₁) * Real.exp 2 * (Real.log (2 * k) ^ 2 / k) *
          ((N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2)) := by
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk
  have hk0 : (0 : ℝ) < k := by linarith
  have hEm : MeasurableSet {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖} :=
    measurableSet_le measurable_const (continuous_Gs _).norm.measurable
  have hA : MeasurableSet ((Set.Icc (0 : ℝ) 1 \ M) \
      {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖}) :=
    (measurableSet_Icc.diff hM).diff hEm
  have hAs : (Set.Icc (0 : ℝ) 1 \ M) \
      {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖} ⊆ Set.Icc 0 1 :=
    fun α h => h.1.1
  have hGb : ∀ α ∈ (Set.Icc (0 : ℝ) 1 \ M) \
      {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖},
      ‖Gs (Nat.log 2 N) α‖ ≤ (1 - Real.log k / k) * (Nat.log 2 N : ℝ) := by
    intro α hα
    have h : ¬ ((1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖) := hα.2
    rw [not_le] at h
    exact h.le
  have h := LeanLab.Romanov.gallagher_eta_arc_le (by omega : 2 ≤ k) N hA hAs hGb
  have hR := LeanLab.Romanov.R₁_pos
  have hlog2k : 1 ≤ Real.log (2 * k) := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hy1 : 1 / (k : ℝ) ≤ Real.log (2 * k) ^ 2 / k :=
    div_le_div_of_nonneg_right (by nlinarith) hk0.le
  have hk2 : Real.exp 2 / (k : ℝ) ^ 2 ≤ Real.exp 2 * (Real.log (2 * k) ^ 2 / k) := by
    have h1 : Real.exp 2 / (k : ℝ) ^ 2 ≤ Real.exp 2 * (1 / k) := by
      rw [div_le_iff₀ (by positivity)]
      have : Real.exp 2 * (1 / k) * (k : ℝ) ^ 2 = Real.exp 2 * k := by field_simp
      rw [this]
      nlinarith [Real.exp_pos 2]
    exact h1.trans (mul_le_mul_of_nonneg_left hy1 (Real.exp_pos 2).le)
  have hW0 : 0 ≤ (N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2) := by positivity
  calc _ ≤ (Real.exp 2 / (k : ℝ) ^ 2) * (Nat.log 2 N : ℝ) ^ (2 * k - 2) *
          (8 * (9 + 2 * LeanLab.Romanov.R₁) * N) := h
    _ = 8 * (9 + 2 * LeanLab.Romanov.R₁) * (Real.exp 2 / (k : ℝ) ^ 2) *
          ((N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2)) := by ring
    _ ≤ 8 * (9 + 2 * LeanLab.Romanov.R₁) * (Real.exp 2 * (Real.log (2 * k) ^ 2 / k)) *
          ((N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2)) := by
        apply mul_le_mul_of_nonneg_right _ hW0
        exact mul_le_mul_of_nonneg_left hk2 (by positivity)
    _ = _ := by ring

/-- ASSEMBLY, CONDITIONAL ON the leaves `measurableSet_majorArcs`, `G_eq_Gs`,
`major_arc_bound`, `lemma11`, `thetaK_small`, `exp_neg_le`, `etaK_small` and `power_le`,
with the lab's proved Lemma 2, `lemma2`, and Lemma 12, `gallagher_eta_arc_le`.
Display (6) for `k ≥ k₀`, p. 139, in the lab's form `Display6Large`. -/
theorem display6Large_of_leaves : LeanLab.Linnik.U7206.Display6Large := by
  obtain ⟨c, C5, θ0, hc, hθ0, h5⟩ := major_arc_bound
  obtain ⟨C11, θ1, E, hθ1, h11⟩ := lemma11
  obtain ⟨K1, hK1⟩ := thetaK_small (min θ0 θ1) (lt_min hθ0 hθ1)
  obtain ⟨K2, hK2⟩ := exp_neg_le c hc
  obtain ⟨K3, hK3⟩ := etaK_small
  have hR := LeanLab.Romanov.R₁_pos
  refine ⟨2 * |C5| + 1 + 8 * (9 + 2 * LeanLab.Romanov.R₁) * Real.exp 2,
    max (max K1 K2) (max K3 3), fun k hk => ?_⟩
  have hk1 : K1 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hk
  have hk2 : K2 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hk
  have hk3 : K3 ≤ k := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hk
  have hk3' : 3 ≤ k := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hk
  obtain ⟨hθpos, hθle⟩ := hK1 k hk1
  have hθ0' : thetaK k ≤ θ0 := hθle.trans (min_le_left _ _)
  have hθ1' : thetaK k ≤ θ1 := hθle.trans (min_le_right _ _)
  obtain ⟨hηpos, hηle⟩ := hK3 k hk3
  obtain ⟨Nk5, hN5⟩ := h5 (thetaK k) hθpos hθ0' k (by omega)
  obtain ⟨N7, hN7⟩ := power_le (4 * C11 ^ 2 * k) (2 * E + 2) (thetaK k / 2) (by positivity)
  refine ⟨max (max Nk5 N7) 8, fun N hN => ?_⟩
  have hN5' : Nk5 ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hN7' : N7 ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hN8 : 8 ≤ N := le_trans (le_max_right _ _) hN
  have hkr : (3 : ℝ) ≤ k := by exact_mod_cast hk3'
  have hk0 : (0 : ℝ) < k := by linarith
  have hNr : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hMm := measurableSet_majorArcs N ((N : ℝ) ^ thetaK k)
  have hMs : majorArcs N ((N : ℝ) ^ thetaK k) ⊆ Set.Icc 0 1 := fun α h => h.1
  have hEm : MeasurableSet {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖} :=
    measurableSet_le measurable_const (continuous_Gs _).norm.measurable
  have hf : Continuous fun α => ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2 :=
    ((LeanLab.Linnik.U7206.continuous_Sg N).mul ((continuous_Gs _).pow k)).norm.pow 2
  rw [split3 _ hf hMm hMs hEm]
  -- piece 1
  have hlogN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hLge : Real.log N ≤ (Nat.log 2 N : ℝ) := LeanLab.Linnik.U7206.log_le_L hN8
  have hI1 := hN5 N hN5'
  have hlogk : Real.log k ^ 2 / k ≤ Real.log (2 * k) ^ 2 / k := by
    apply div_le_div_of_nonneg_right _ hk0.le
    have h0 : 0 ≤ Real.log k := Real.log_nonneg (by linarith)
    have h1 : Real.log k ≤ Real.log (2 * k) := Real.log_le_log hk0 (by linarith)
    exact pow_le_pow_left₀ h0 h1 2
  have hexp : Real.exp (-c / thetaK k) ≤ Real.log (2 * k) ^ 2 / k := hK2 k hk2
  have hsum0 : 0 ≤ Real.log k ^ 2 / k + Real.exp (-c / thetaK k) := by positivity
  have hC : C5 * (Real.log k ^ 2 / k + Real.exp (-c / thetaK k)) ≤
      2 * |C5| * (Real.log (2 * k) ^ 2 / k) := by
    calc C5 * (Real.log k ^ 2 / k + Real.exp (-c / thetaK k))
        ≤ |C5| * (Real.log k ^ 2 / k + Real.exp (-c / thetaK k)) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) hsum0
      _ ≤ |C5| * (2 * (Real.log (2 * k) ^ 2 / k)) :=
          mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg _)
      _ = 2 * |C5| * (Real.log (2 * k) ^ 2 / k) := by ring
  have hmain0 : 0 ≤ 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2 := by positivity
  have hI1' := hI1.trans (mul_le_mul_of_nonneg_left (by linarith : 1 + C5 * (Real.log k ^ 2 / k +
    Real.exp (-c / thetaK k)) ≤ 1 + 2 * |C5| * (Real.log (2 * k) ^ 2 / k)) hmain0)
  -- piece 2
  have hA := hN7 N hN7'
  have hI2 := piece2 hk3' hN8 hηpos hηle (h11 (thetaK k) hθpos hθ1' N (by omega)) hA
  have hy1 : 1 / (k : ℝ) ≤ Real.log (2 * k) ^ 2 / k := by
    have hlog2k : 1 ≤ Real.log (2 * k) := by
      rw [Real.le_log_iff_exp_le (by linarith)]
      have := Real.exp_one_lt_d9
      linarith
    exact div_le_div_of_nonneg_right (by nlinarith) hk0.le
  have hW0 : 0 ≤ (N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2) := by positivity
  have hI2' : ∫ α in (Set.Icc 0 1 \ majorArcs N ((N : ℝ) ^ thetaK k)) ∩
        {α | (1 - etaK k) * (Nat.log 2 N : ℝ) ≤ ‖Gs (Nat.log 2 N) α‖},
      ‖Sg N α * Gs (Nat.log 2 N) α ^ k‖ ^ 2 ≤
        (Real.log (2 * k) ^ 2 / k) * ((N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2)) := by
    refine hI2.trans ?_
    rw [div_eq_mul_one_div, mul_comm]
    exact mul_le_mul_of_nonneg_right hy1 hW0
  -- piece 3
  have hI3 := piece3 (N := N) hk3' hMm
  -- W ≤ main / 2
  have hpow : (Nat.log 2 N : ℝ) ^ (2 * k) =
      (Nat.log 2 N : ℝ) ^ (2 * k - 2) * (Nat.log 2 N : ℝ) ^ 2 := by
    rw [← pow_add]; congr 1; omega
  have hW : (N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2) ≤
      2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2 / 2 := by
    have hq : 1 ≤ (Nat.log 2 N : ℝ) ^ 2 / Real.log N ^ 2 :=
      (one_le_div (by positivity)).mpr (pow_le_pow_left₀ hlogN.le hLge 2)
    have : 2 * N * (Nat.log 2 N : ℝ) ^ (2 * k) / Real.log N ^ 2 / 2 =
        (N : ℝ) * (Nat.log 2 N : ℝ) ^ (2 * k - 2) * ((Nat.log 2 N : ℝ) ^ 2 / Real.log N ^ 2) := by
      rw [hpow]; field_simp
    rw [this]
    nlinarith
  exact alg_final hI1' hI2' hI3 hW (by positivity) (by positivity) (Real.exp_pos 2).le hmain0

/-- ASSEMBLY, CONDITIONAL ON the leaves of this file listed at `display6Large_of_leaves`.
Gallagher's Theorem 1, display (3) p. 125, for g = 2, through the lab's proved Lemma 12. -/
theorem theorem1_of_leaves : LeanLab.Linnik.Gallagher1975.Theorem1 :=
  LeanLab.Romanov.gallagher_theorem1_of_large display6Large_of_leaves

/-- ASSEMBLY, CONDITIONAL ON the leaves of this file listed at `display6Large_of_leaves`.
Gallagher's Theorem 2, display (4) p. 125, for g = 2: for `k ≥ 2` and even `N ≥ N_k`,
`r''_k(N) = 2N L^k / log² N · (1 + O(log² k / k))`. -/
theorem theorem2_of_leaves :
    ∃ K : ℝ, ∀ k : ℕ, 2 ≤ k → ∃ Nk : ℕ, ∀ N : ℕ, Nk ≤ N → Even N →
      |(LeanLab.Linnik.Gallagher1975Thm2.rpp k N : ℝ) -
        2 * N * (Nat.log 2 N : ℝ) ^ k / Real.log N ^ 2| ≤
        K * (Real.log k ^ 2 / k) * (2 * N * (Nat.log 2 N : ℝ) ^ k / Real.log N ^ 2) :=
  LeanLab.Romanov.gallagher_theorem2_of_large display6Large_of_leaves

end LeanLab.Linnik.Decomp1532c
