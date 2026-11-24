/-
The count after display 32 of P0082, Brudern and Perelli 1998, p. 368, from Lemma 4 with `α = 1`.
This proves the statement of the MEDIUM leaf `leaf_boundary_count` of `Feed1122LeafEvenMoment`,
on branch claude/ExceptionalSet-feed1122-SPLIT_lemma6, CONDITIONAL ON the sealed open statement
`Lemma4` of `State1539Data264`, p. 359. It does not wire that leaf: `Lemma4` is still open here,
and `lemma4_split` of `SPLIT_lemma4` rests on the leaf `leaf_absorption`, which is FALSE, see
`Refute_leaf_absorption`. So the leaf reduces to Lemma 4 plus the proved glue below.

AI wrote this Lean code, checked only by the Lean kernel. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.State1539

namespace LeanLab.ExceptionalSet.U1539.Feed1122BoundaryCount
open Real Finset Filter
open LeanLab.ExceptionalSet.U1539
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- `(log N)^s exp(-b (log N)^p) ≤ 1` eventually, for `p, b > 0`. -/
theorem bc_growth (p s b : ℝ) (hp : 0 < p) (hb : 0 < b) :
    ∀ᶠ N : ℕ in atTop, Real.log N ^ s * Real.exp (-b * Real.log N ^ p) ≤ 1 := by
  have hg : Tendsto (fun N : ℕ => Real.log N ^ p) atTop atTop :=
    (tendsto_rpow_atTop hp).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hf := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero (s / p) b hb).comp hg
  have hL : ∀ᶠ N : ℕ in atTop, 0 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 0
  filter_upwards [hf.eventually (Iic_mem_nhds one_pos), hL] with N hN hL0
  simp only [Function.comp, Set.mem_Iic] at hN
  rwa [← Real.rpow_mul hL0, mul_div_cancel₀ _ hp.ne'] at hN

/-- `κ (log N)^p ≤ log N` eventually, for `p < 1`. -/
theorem bc_linear (p κ : ℝ) (hp : p < 1) (hκ : 0 < κ) :
    ∀ᶠ N : ℕ in atTop, κ * Real.log N ^ p ≤ Real.log N := by
  have hg : Tendsto (fun N : ℕ => Real.log N ^ (1 - p)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith)).comp (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hL : ∀ᶠ N : ℕ in atTop, 1 ≤ Real.log N :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop 1
  filter_upwards [hg.eventually_ge_atTop κ, hL] with N hN hL1
  have hL0 : 0 < Real.log N := by linarith
  have hpow : 0 ≤ Real.log N ^ p := Real.rpow_nonneg hL0.le _
  calc κ * Real.log N ^ p ≤ Real.log N ^ (1 - p) * Real.log N ^ p :=
        mul_le_mul_of_nonneg_right hN hpow
    _ = Real.log N := by rw [← Real.rpow_add hL0]; simp

/-- The count after display 32 of P0082, p. 368, by Lemma 4 with `α = 1`, CONDITIONAL ON the
sealed open statement `Lemma4` of this folder. The conclusion is word for word the statement of
the MEDIUM leaf `leaf_boundary_count` of `Feed1122LeafEvenMoment`: the `n` of the window with
`{F(n)} < Δ/2` or `{F(n)} > 1 - Δ/2` lie in the intervals `[0, Δ/2)` and `[1 - Δ/2, 1)` plus
possibly the left end `(N+1)/2`, Lemma 4 counts each up to `B N exp(-κ (log N)^(3-2γ))`, and that
error beats `ℰ^(-1/3)/(log X)²` for every `κ' ≤ κ` because `log X = (log N)^γ`. -/
theorem leaf_boundary_count_of_lemma4 (h4 : Lemma4) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Δ : ℝ, 0 < Δ →
        (((Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ =>
            Int.fract (F γ n) < Δ / 2 ∨ 1 - Δ / 2 < Int.fract (F γ n))).card : ℝ)
          ≤ B * N * (Δ + calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2) := by
  classical
  obtain ⟨κ, B, hκ, hL4⟩ := h4 γ h1 h2
  have hp : 0 < 3 - 2 * γ := by linarith
  have hp1 : 3 - 2 * γ < 1 := by linarith
  refine ⟨κ, hκ, fun κ' hκ' hκ'le => ⟨3 + 2 * |B|, by positivity, ?_⟩⟩
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 ((bc_growth (3 - 2 * γ) (2 * γ) (2 * κ / 3) hp
    (by positivity)).and ((bc_linear (3 - 2 * γ) κ hp1 hκ).and (eventually_ge_atTop 2)))
  refine ⟨N₀, fun N hN Δ hΔ => ?_⟩
  obtain ⟨hgr, hlin, hN2⟩ := hN₀ N hN
  have hN1 : (1 : ℝ) < N := by exact_mod_cast (by omega : 1 < N)
  have hNpos : (0 : ℝ) < N := by linarith
  set L := Real.log N with hLdef
  have hL0 : 0 < L := Real.log_pos hN1
  set e := Real.exp (-κ * L ^ (3 - 2 * γ)) with hedef
  set E := calE γ κ' N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2 with hEdef
  have hpowp : 0 ≤ L ^ (3 - 2 * γ) := Real.rpow_nonneg hL0.le _
  -- the analytic comparison e ≤ E
  have heE : e ≤ E := by
    have hlogF : Real.log (F γ N) ^ 2 = L ^ (2 * γ) := by
      unfold F; rw [Real.log_exp, ← Real.rpow_natCast, ← Real.rpow_mul hL0.le]; congr 1; push_cast; ring
    have hcal : calE γ κ' N ^ (-(1 / 3 : ℝ)) = Real.exp (-(κ' / 3) * L ^ (3 - 2 * γ)) := by
      unfold calE; rw [← Real.exp_mul]; congr 1; ring
    have hLg : 0 < L ^ (2 * γ) := Real.rpow_pos_of_pos hL0 _
    rw [hEdef, hlogF, hcal, le_div_iff₀ hLg]
    have hsplit : Real.exp (-κ * L ^ (3 - 2 * γ)) =
        Real.exp (-(2 * κ / 3) * L ^ (3 - 2 * γ)) * Real.exp (-(κ / 3) * L ^ (3 - 2 * γ)) := by
      rw [← Real.exp_add]; congr 1; ring
    have hmono : Real.exp (-(κ / 3) * L ^ (3 - 2 * γ)) ≤ Real.exp (-(κ' / 3) * L ^ (3 - 2 * γ)) :=
      Real.exp_le_exp.mpr (by nlinarith)
    have hpos3 : 0 < Real.exp (-(κ / 3) * L ^ (3 - 2 * γ)) := Real.exp_pos _
    rw [hedef, hsplit]
    calc Real.exp (-(2 * κ / 3) * L ^ (3 - 2 * γ)) * Real.exp (-(κ / 3) * L ^ (3 - 2 * γ)) * L ^ (2 * γ)
        = (L ^ (2 * γ) * Real.exp (-(2 * κ / 3) * L ^ (3 - 2 * γ))) *
            Real.exp (-(κ / 3) * L ^ (3 - 2 * γ)) := by ring
      _ ≤ 1 * Real.exp (-(κ / 3) * L ^ (3 - 2 * γ)) := mul_le_mul_of_nonneg_right hgr hpos3.le
      _ ≤ _ := by rw [one_mul]; exact hmono
  have hE0 : 0 ≤ e := (Real.exp_pos _).le
  have hNe : 1 ≤ N * e := by
    have : Real.exp 0 ≤ Real.exp (L + -κ * L ^ (3 - 2 * γ)) := Real.exp_le_exp.mpr (by nlinarith)
    rw [Real.exp_zero, Real.exp_add, hLdef, Real.exp_log hNpos] at this
    exact this
  set S := (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ =>
      Int.fract (F γ n) < Δ / 2 ∨ 1 - Δ / 2 < Int.fract (F γ n)) with hSdef
  have hB0 : 0 ≤ |B| := abs_nonneg B
  rcases le_or_gt 1 Δ with hΔ1 | hΔ1
  · -- trivial range
    have hcard : (S.card : ℝ) ≤ 2 * N := by
      have h1' : S.card ≤ N + 1 - (N + 1) / 2 := by
        rw [← Nat.card_Icc]; exact card_filter_le _ _
      have : S.card ≤ 2 * N := by omega
      exact_mod_cast this
    have hEpos : 0 ≤ E := le_trans hE0 heE
    have k0 : (2 : ℝ) ≤ (3 + 2 * |B|) * Δ := by nlinarith
    have k1 : 2 * (N : ℝ) ≤ (3 + 2 * |B|) * N * Δ := by nlinarith
    have k2 : 0 ≤ (3 + 2 * |B|) * N * E := by positivity
    rw [mul_add]; linarith
  · have hF : F γ N ^ (-(1 / 2 : ℝ)) < |(1 : ℝ)| := by
      rw [abs_one]
      apply Real.rpow_lt_one_of_one_lt_of_neg _ (by norm_num)
      unfold F
      have hx := Real.rpow_pos_of_pos hL0 γ
      have := Real.add_one_lt_exp hx.ne'
      linarith
    have hA := hL4 N (by omega) 1 hF (abs_one.le) (Δ / 2) 0 le_rfl (by linarith) (by linarith)
    have hC := hL4 N (by omega) 1 hF (abs_one.le) 1 (1 - Δ / 2) (by linarith) (by linarith) le_rfl
    have hBe : B * N * Real.exp (-κ * Real.log N ^ (3 - 2 * γ)) ≤ |B| * N * e := by
      rw [← hLdef, ← hedef]
      have := le_abs_self B
      have : 0 ≤ (N : ℝ) * e := by positivity
      nlinarith
    set A := (Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
        (0 : ℝ) ≤ Int.fract (1 * F γ n) ∧ Int.fract (1 * F γ n) < Δ / 2)
    set C := (Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
        1 - Δ / 2 ≤ Int.fract (1 * F γ n) ∧ Int.fract (1 * F γ n) < 1)
    have hsub : S ⊆ insert ((N + 1) / 2) (A ∪ C) := by
      intro n hn
      simp only [hSdef, mem_filter, mem_Icc] at hn
      rw [mem_insert]
      rcases eq_or_lt_of_le hn.1.1 with h | h
      · exact Or.inl h.symm
      · right
        have hmem : n ∈ Finset.Ioc (N / 2) N := mem_Ioc.mpr ⟨by omega, hn.1.2⟩
        rcases hn.2 with h' | h'
        · exact mem_union_left _ (mem_filter.mpr ⟨hmem, by rw [one_mul]; exact Int.fract_nonneg _,
            by rw [one_mul]; exact h'⟩)
        · exact mem_union_right _ (mem_filter.mpr ⟨hmem, by rw [one_mul]; exact h'.le,
            by rw [one_mul]; exact Int.fract_lt_one _⟩)
    have hcard : (S.card : ℝ) ≤ 1 + A.card + C.card := by
      have := (card_le_card hsub).trans ((card_insert_le _ _).trans
        (Nat.add_le_add_right (card_union_le A C) 1))
      have : (S.card : ℝ) ≤ ((A.card + C.card + 1 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    have hA' : (A.card : ℝ) ≤ Δ / 2 * N / 2 + |B| * N * e := by
      have := (abs_le.mp hA).2; simp only [sub_zero] at this; linarith
    have hC' : (C.card : ℝ) ≤ Δ / 2 * N / 2 + |B| * N * e := by
      have := (abs_le.mp hC).2
      rw [show (1 : ℝ) - (1 - Δ / 2) = Δ / 2 by ring] at this; linarith
    have hfin : (S.card : ℝ) ≤ Δ * N / 2 + (1 + 2 * |B|) * (N * e) := by nlinarith
    have hNE : N * e ≤ N * E := mul_le_mul_of_nonneg_left heE hNpos.le
    have h3 : (1 + 2 * |B|) * (N * e) ≤ (3 + 2 * |B|) * (N * E) := by
      have hNE0 : 0 ≤ N * e := by positivity
      nlinarith
    have h4' : Δ * N / 2 ≤ (3 + 2 * |B|) * N * Δ := by
      have hDN : 0 ≤ Δ * N := by positivity
      have e1 : (3 + 2 * |B|) * N * Δ = (3 + 2 * |B|) * (Δ * N) := by ring
      rw [e1]; nlinarith
    rw [mul_add]
    have e2 : (3 + 2 * |B|) * N * E = (3 + 2 * |B|) * (N * E) := by ring
    rw [e2]; linarith
end LeanLab.ExceptionalSet.U1539.Feed1122BoundaryCount

#print axioms LeanLab.ExceptionalSet.U1539.Feed1122BoundaryCount.bc_growth
#print axioms LeanLab.ExceptionalSet.U1539.Feed1122BoundaryCount.bc_linear
#print axioms LeanLab.ExceptionalSet.U1539.Feed1122BoundaryCount.leaf_boundary_count_of_lemma4
