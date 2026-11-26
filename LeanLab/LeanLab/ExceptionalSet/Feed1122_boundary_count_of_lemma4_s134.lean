/-
# The boundary count of P0082, p. 368, CONDITIONAL ON Lemma 4

Session S134 burst-20261122. The count after display 32 of P0082, p. 368, derived from
Lemma 4 of P0082, p. 359, taken at `α = 1`, as the named open statement `Lemma4`.

AI wrote this Lean code, checked only by the Lean kernel. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.State1539Data264

namespace LeanLab.ExceptionalSet.U1539

open Real Finset
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- Eventually `L ^ p ≤ exp (c L ^ a)` for `c, a > 0`. -/
lemma s134_rpow_le_exp (p c a : ℝ) (hc : 0 < c) (ha : 0 < a) :
    ∀ᶠ L : ℝ in Filter.atTop, L ^ p ≤ Real.exp (c * L ^ a) := by
  have h1 := (tendsto_rpow_atTop (half_pos ha)).eventually_ge_atTop (2 * |p| / (a * c))
  filter_upwards [h1, Filter.eventually_gt_atTop 1] with L hL hL1
  have hL0 : 0 < L := by linarith
  rw [← Real.exp_log (rpow_pos_of_pos hL0 p), Real.exp_le_exp, Real.log_rpow hL0]
  have hlog := Real.log_le_rpow_div hL0.le (half_pos ha)
  have hlogpos : 0 ≤ Real.log L := Real.log_nonneg hL1.le
  have hsq : L ^ a = L ^ (a / 2) * L ^ (a / 2) := by rw [← Real.rpow_add hL0]; ring_nf
  have hpos : 0 ≤ L ^ (a / 2) := (rpow_pos_of_pos hL0 _).le
  calc p * Real.log L ≤ |p| * Real.log L := mul_le_mul_of_nonneg_right (le_abs_self p) hlogpos
    _ ≤ |p| * (L ^ (a / 2) / (a / 2)) := mul_le_mul_of_nonneg_left hlog (abs_nonneg p)
    _ = (2 * |p| / (a * c)) * L ^ (a / 2) * c := by field_simp
    _ ≤ L ^ (a / 2) * L ^ (a / 2) * c := by gcongr
    _ = c * L ^ a := by rw [hsq]; ring

/-- CONDITIONAL ON `Lemma4`, P0082 p. 359. The count after display 32 of P0082, p. 368:
the `n` of the window with `{F(n)}` below `Δ/2` or above `1 - Δ/2` number at most
`B N (Δ + ℰ^(-1/3) / (log X)²)`. Proof: Lemma 4 at `α = 1` with `[z₂, z₁) = [0, Δ/2)` and
`[1 - Δ/2, 1)`, one extra index `n = N/2`, and the error `exp(-κ' (log N)^(3-2γ))`
absorbed into `ℰ^(-1/3) / (log N)^(2γ)` for `κ ≤ min κ' 1`. -/
theorem leaf_boundary_count_of_lemma4_s134 (h4 : Lemma4) (γ : ℝ) (h1 : 1 < γ)
    (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Δ : ℝ, 0 < Δ →
        (((Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ =>
            Int.fract (F γ n) < Δ / 2 ∨ 1 - Δ / 2 < Int.fract (F γ n))).card : ℝ)
          ≤ B * N * (Δ + calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2) := by
  obtain ⟨κ', B', hκ', hB'⟩ := h4 γ h1 h2
  have ha : 0 < 3 - 2 * γ := by linarith
  have ha1 : 3 - 2 * γ ≤ 1 := by linarith
  refine ⟨min κ' 1, lt_min hκ' one_pos, fun κ hκ hκle => ?_⟩
  have hκ1 : κ ≤ κ' := hκle.trans (min_le_left _ _)
  have hκ2 : κ ≤ 1 := hκle.trans (min_le_right _ _)
  refine ⟨2 * |B'| + 2, by positivity, ?_⟩
  have hevL : ∀ᶠ L : ℝ in Filter.atTop, 1 ≤ L ∧
      L ^ (2 * γ) ≤ Real.exp (2 * κ' / 3 * L ^ (3 - 2 * γ)) ∧
      L ^ (2 * γ) ≤ Real.exp (2 / 3 * L ^ (1 : ℝ)) :=
    (Filter.eventually_ge_atTop 1).and ((s134_rpow_le_exp _ _ _ (by positivity) ha).and
      (s134_rpow_le_exp _ _ _ (by norm_num) one_pos))
  have hT : Filter.Tendsto (fun N : ℕ => Real.log N) Filter.atTop Filter.atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1
    ((hT.eventually hevL).and (Filter.eventually_ge_atTop 2))
  refine ⟨N₀, fun N hN Δ hΔ => ?_⟩
  obtain ⟨⟨hL1, hLa, hL1'⟩, hN2⟩ := hN₀ N hN
  set L := Real.log (N : ℝ) with hL_def
  have hL0 : 0 < L := by linarith
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hNexp : (N : ℝ) = Real.exp L := (Real.exp_log hNpos).symm
  have hFN : F γ N = Real.exp (L ^ γ) := rfl
  have hlogF : Real.log (F γ N) ^ 2 = L ^ (2 * γ) := by
    rw [hFN, Real.log_exp, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; ring_nf
  have hE : calE γ κ N ^ (-(1 / 3 : ℝ)) = Real.exp (-(κ / 3) * L ^ (3 - 2 * γ)) := by
    unfold calE; rw [← Real.exp_mul, ← hL_def]; ring_nf
  have hLpow : 0 < L ^ (2 * γ) := rpow_pos_of_pos hL0 _
  set e := Real.exp (-κ' * L ^ (3 - 2 * γ)) with he
  set g := calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2 with hg
  have hLa0 : 0 ≤ L ^ (3 - 2 * γ) := (rpow_pos_of_pos hL0 _).le
  -- e ≤ g
  have heg : e ≤ g := by
    rw [hg, hlogF, hE, le_div_iff₀ hLpow]
    calc e * L ^ (2 * γ) ≤ e * Real.exp (2 * κ' / 3 * L ^ (3 - 2 * γ)) :=
          mul_le_mul_of_nonneg_left hLa (Real.exp_pos _).le
      _ = Real.exp (-(κ' / 3) * L ^ (3 - 2 * γ)) := by rw [he, ← Real.exp_add]; ring_nf
      _ ≤ Real.exp (-(κ / 3) * L ^ (3 - 2 * γ)) := by
          rw [Real.exp_le_exp]; nlinarith
  -- 1 ≤ N g
  have hNg : 1 ≤ N * g := by
    have hLaL : L ^ (3 - 2 * γ) ≤ L := by
      simpa using Real.rpow_le_rpow_of_exponent_le hL1 ha1
    rw [Real.rpow_one] at hL1'
    rw [hg, hlogF, hE, hNexp, mul_div_assoc', le_div_iff₀ hLpow, one_mul, ← Real.exp_add]
    calc L ^ (2 * γ) ≤ Real.exp (2 / 3 * L) := hL1'
      _ ≤ _ := by rw [Real.exp_le_exp]; nlinarith
  have hg0 : 0 ≤ g := (Real.exp_pos _).le.trans heg
  -- the count
  have hcardIcc : (((Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ =>
      Int.fract (F γ n) < Δ / 2 ∨ 1 - Δ / 2 < Int.fract (F γ n))).card : ℝ) ≤ N := by
    have h := Finset.card_filter_le (Finset.Icc ((N + 1) / 2) N) (fun n : ℕ =>
      Int.fract (F γ n) < Δ / 2 ∨ 1 - Δ / 2 < Int.fract (F γ n))
    rw [Nat.card_Icc] at h
    exact_mod_cast h.trans (by omega)
  rcases le_or_gt 1 Δ with hΔ1 | hΔ1
  · refine hcardIcc.trans ?_
    have : (N : ℝ) * 1 ≤ (2 * |B'| + 2) * N * (Δ + g) := by
      have : (1 : ℝ) ≤ (2 * |B'| + 2) * (Δ + g) := by
        have := abs_nonneg B'; nlinarith
      nlinarith
    simpa using this
  -- Δ < 1: Lemma 4 at α = 1
  have hF1 : 1 < F γ N := by
    rw [hFN, Real.one_lt_exp_iff]; exact rpow_pos_of_pos hL0 _
  have hα : F γ N ^ (-(1 / 2 : ℝ)) < |(1 : ℝ)| := by
    rw [abs_one]; exact Real.rpow_lt_one_of_one_lt_of_neg hF1 (by norm_num)
  have hA := hB' N (by omega) 1 hα abs_one.le (Δ / 2) 0 le_rfl (by linarith) (by linarith)
  have hB := hB' N (by omega) 1 hα abs_one.le 1 (1 - Δ / 2) (by linarith) (by linarith) le_rfl
  set SA := (Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
      0 ≤ Int.fract (1 * F γ n) ∧ Int.fract (1 * F γ n) < Δ / 2) with hSA
  set SB := (Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
      1 - Δ / 2 ≤ Int.fract (1 * F γ n) ∧ Int.fract (1 * F γ n) < 1) with hSB
  have hsub : (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ =>
      Int.fract (F γ n) < Δ / 2 ∨ 1 - Δ / 2 < Int.fract (F γ n)) ⊆
      insert (N / 2) (SA ∪ SB) := by
    intro n hn
    simp only [hSA, hSB, Finset.mem_filter, Finset.mem_Icc, Finset.mem_insert,
      Finset.mem_union, Finset.mem_Ioc, one_mul] at hn ⊢
    by_cases h : n = N / 2
    · left; exact h
    right
    have hIoc : N / 2 < n ∧ n ≤ N := ⟨by omega, hn.1.2⟩
    rcases hn.2 with h' | h'
    · left; exact ⟨hIoc, Int.fract_nonneg _, h'⟩
    · right; exact ⟨hIoc, h'.le, Int.fract_lt_one _⟩
  have hcard : (((Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ =>
      Int.fract (F γ n) < Δ / 2 ∨ 1 - Δ / 2 < Int.fract (F γ n))).card : ℝ) ≤
      1 + SA.card + SB.card := by
    have h := (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans
      (Nat.add_le_add_right (Finset.card_union_le SA SB) 1))
    have : ((((Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ =>
      Int.fract (F γ n) < Δ / 2 ∨ 1 - Δ / 2 < Int.fract (F γ n))).card : ℕ) : ℝ) ≤
        ((SA.card + SB.card + 1 : ℕ) : ℝ) := by exact_mod_cast h
    push_cast at this; linarith
  have hA' : (SA.card : ℝ) ≤ Δ / 2 * N / 2 + B' * N * e := by
    have := (abs_le.1 hA).2; simp only [sub_zero] at this; linarith
  have hB'' : (SB.card : ℝ) ≤ Δ / 2 * N / 2 + B' * N * e := by
    have := (abs_le.1 hB).2
    have hs : (1 - (1 - Δ / 2)) * (N : ℝ) / 2 = Δ / 2 * N / 2 := by ring
    rw [hs] at this; linarith
  have hBe : B' * N * e ≤ |B'| * N * g := by
    have hNe : 0 ≤ (N : ℝ) * e := by positivity
    calc B' * N * e = B' * (N * e) := by ring
      _ ≤ |B'| * (N * e) := mul_le_mul_of_nonneg_right (le_abs_self _) hNe
      _ ≤ |B'| * (N * g) := mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left heg hNpos.le) (abs_nonneg _)
      _ = |B'| * N * g := by ring
  have hNg2 : (0 : ℝ) ≤ |B'| * N * Δ := by positivity
  nlinarith [hcard, hA', hB'', hBe, hNg, hNg2, mul_pos hNpos hΔ]

end LeanLab.ExceptionalSet.U1539
