/-
The leaf `leaf_boundary_count` of `Feed1122LeafEvenMoment`, the count after display 32 of
Brudern-Perelli 1998, P0082, p. 368, by the paper's Lemma 4, p. 359, with `α = 1`.

* `boundary_growth`: the growth comparison, PROVED.
* `leaf_boundary_count_of_lemma4`: the exact type of `leaf_boundary_count`, PROVED
  CONDITIONAL ON the sealed statement `Lemma4`.
* `leaf_boundary_count_of_leaves`: the exact type of `leaf_boundary_count`, from the
  existing open statement `lemma4` of `State1539`; no new sorry.

The window `[(N+1)/2, N]` exceeds the window `(N/2, N]` of Lemma 4 by at most the one point
`N/2`, which costs `1 ≤ N ℰ^(-1/3) / (log X)^2`. The two boundary pieces
`[0, Δ/2)` and `[1 - Δ/2, 1)` are each counted by Lemma 4 for `Δ < 1`; for `Δ ≥ 1` the
trivial count `N` suffices.

AI wrote this Lean code, checked only by the Lean kernel. Binary Goldbach is open.
-/
import LeanLab.ExceptionalSet.Feed1122LeafEvenMoment

namespace LeanLab.ExceptionalSet.U1539

open Real Finset Filter
open LeanLab.ExceptionalSet.BrudernPerelli1998 (F)

/-- The growth comparison behind the remark after display 32 of P0082, p. 368: for
`1 < γ < 3/2` and `c, κ > 0`, eventually in `x = log N`, `x^γ ≤ exp(c x^(3-2γ))`,
`x^γ ≤ exp(x/4)` and `κ/3 · x^(3-2γ) ≤ x/2`. -/
theorem boundary_growth (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) (c κ : ℝ) (hc : 0 < c)
    (hκ : 0 < κ) :
    ∀ᶠ x : ℝ in atTop, 1 ≤ x ∧ x ^ γ ≤ Real.exp (c * x ^ (3 - 2 * γ)) ∧
      x ^ γ ≤ Real.exp (x / 4) ∧ κ / 3 * x ^ (3 - 2 * γ) ≤ x / 2 := by
  have hs : 0 < 3 - 2 * γ := by linarith
  have hγ : 0 < γ := by linarith
  have hA := (isLittleO_log_rpow_atTop hs).bound (show 0 < c / γ by positivity)
  have hB := Real.isLittleO_log_id_atTop.bound (show 0 < 1 / (4 * γ) by positivity)
  have hC := (tendsto_order.1 (tendsto_rpow_neg_atTop (show 0 < 2 * γ - 2 by linarith))).2
    (3 / (2 * κ)) (by positivity)
  filter_upwards [hA, hB, hC, eventually_ge_atTop (1 : ℝ)] with x hxA hxB hxC hx1
  have hx0 : 0 < x := by linarith
  have hlog0 : 0 ≤ Real.log x := Real.log_nonneg hx1
  have hxs0 : 0 ≤ x ^ (3 - 2 * γ) := Real.rpow_nonneg hx0.le _
  rw [Real.norm_of_nonneg hlog0, Real.norm_of_nonneg hxs0] at hxA
  rw [Real.norm_of_nonneg hlog0, id, Real.norm_of_nonneg hx0.le] at hxB
  have hxγ : x ^ γ = Real.exp (γ * Real.log x) := by
    rw [Real.rpow_def_of_pos hx0, mul_comm]
  refine ⟨hx1, ?_, ?_, ?_⟩
  · rw [hxγ]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hxA hγ.le
    calc γ * Real.log x ≤ γ * (c / γ * x ^ (3 - 2 * γ)) := this
      _ = c * x ^ (3 - 2 * γ) := by field_simp
  · rw [hxγ]
    apply Real.exp_le_exp.mpr
    have := mul_le_mul_of_nonneg_left hxB hγ.le
    calc γ * Real.log x ≤ γ * (1 / (4 * γ) * x) := this
      _ = x / 4 := by field_simp
  · have hsplit : x ^ (3 - 2 * γ) = x ^ (-(2 * γ - 2)) * x := by
      rw [show (3 - 2 * γ) = -(2 * γ - 2) + 1 by ring, Real.rpow_add hx0, Real.rpow_one]
    rw [hsplit]
    have hle : x ^ (-(2 * γ - 2)) ≤ 3 / (2 * κ) := hxC.le
    calc κ / 3 * (x ^ (-(2 * γ - 2)) * x) ≤ κ / 3 * (3 / (2 * κ) * x) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact mul_le_mul_of_nonneg_right hle hx0.le
      _ = x / 2 := by field_simp

/-- `leaf_boundary_count` of `Feed1122LeafEvenMoment`, its statement copied verbatim, PROVED
CONDITIONAL ON `Lemma4`, P0082 p. 359, applied with `α = 1` to the two boundary pieces
`[0, Δ/2)` and `[1 - Δ/2, 1)`, as in the count after display 32, p. 368. -/
theorem leaf_boundary_count_of_lemma4 (h4 : Lemma4) (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Δ : ℝ, 0 < Δ →
        (((Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ =>
            Int.fract (F γ n) < Δ / 2 ∨ 1 - Δ / 2 < Int.fract (F γ n))).card : ℝ)
          ≤ B * N * (Δ + calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2) := by
  obtain ⟨κ₄, B₄, hκ₄, hL4⟩ := h4 γ h1 h2
  refine ⟨3 * κ₄ / 2, by positivity, fun κ hκ hκle => ?_⟩
  refine ⟨2 + 2 * |B₄|, by positivity, ?_⟩
  have hev := (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually
    (boundary_growth γ h1 h2 (κ₄ / 4) κ (by positivity) hκ)
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.1 (hev.and (eventually_ge_atTop 2))
  refine ⟨N₀, fun N hN Δ hΔ => ?_⟩
  obtain ⟨⟨hL1, hG1, hG2, hG3⟩, hN2⟩ := hN₀ N hN
  simp only [Function.comp] at hL1 hG1 hG2 hG3
  have hNpos : (0 : ℝ) < N := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN2
    linarith
  have hlogF : Real.log (F γ N) = Real.log (N : ℝ) ^ γ := by
    simp [F, Real.log_exp]
  have hcalE : calE γ κ N ^ (-(1 / 3 : ℝ)) =
      Real.exp (-(κ / 3 * Real.log (N : ℝ) ^ (3 - 2 * γ))) := by
    rw [calE, ← Real.exp_mul]
    congr 1
    ring
  have hFexp : F γ N = Real.exp (Real.log (N : ℝ) ^ γ) := rfl
  have hNexp : (N : ℝ) = Real.exp (Real.log (N : ℝ)) := (Real.exp_log hNpos).symm
  rw [hlogF, hcalE]
  set L := Real.log (N : ℝ) with hLdef
  set s := 3 - 2 * γ with hsdef
  set E := Real.exp (-(κ / 3 * L ^ s)) / (L ^ γ) ^ 2 with hEdef
  have hL0 : 0 < L := by linarith
  have hLγ : 0 < L ^ γ := Real.rpow_pos_of_pos hL0 _
  have hLs : 0 ≤ L ^ s := Real.rpow_nonneg hL0.le _
  have hE0 : 0 ≤ E := by positivity
  have ha : Real.exp (-κ₄ * L ^ s) ≤ E := by
    rw [hEdef, le_div_iff₀ (by positivity)]
    have hsq : (L ^ γ) ^ 2 ≤ Real.exp (κ₄ / 2 * L ^ s) := by
      calc (L ^ γ) ^ 2 ≤ Real.exp (κ₄ / 4 * L ^ s) ^ 2 := pow_le_pow_left₀ hLγ.le hG1 2
        _ = Real.exp (κ₄ / 2 * L ^ s) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
    calc Real.exp (-κ₄ * L ^ s) * (L ^ γ) ^ 2
        ≤ Real.exp (-κ₄ * L ^ s) * Real.exp (κ₄ / 2 * L ^ s) :=
          mul_le_mul_of_nonneg_left hsq (Real.exp_pos _).le
      _ = Real.exp (-(κ₄ / 2 * L ^ s)) := by
          rw [← Real.exp_add]
          congr 1
          ring
      _ ≤ Real.exp (-(κ / 3 * L ^ s)) := by
          apply Real.exp_le_exp.mpr
          have : κ / 3 ≤ κ₄ / 2 := by linarith
          nlinarith
  have hb : 1 ≤ (N : ℝ) * E := by
    rw [hEdef, hNexp, mul_div_assoc', le_div_iff₀ (by positivity), one_mul, ← Real.exp_add]
    calc (L ^ γ) ^ 2 ≤ Real.exp (L / 4) ^ 2 := pow_le_pow_left₀ hLγ.le hG2 2
      _ = Real.exp (L / 2) := by
          rw [← Real.exp_nat_mul]
          congr 1
          push_cast
          ring
      _ ≤ Real.exp (L + -(κ / 3 * L ^ s)) := by
          apply Real.exp_le_exp.mpr
          linarith
  have hB4 : B₄ ≤ |B₄| := le_abs_self _
  have hB40 : 0 ≤ |B₄| := abs_nonneg _
  have hNE : 0 ≤ (N : ℝ) * E := by positivity
  rcases lt_or_ge Δ 1 with hΔ1 | hΔ1
  · have hα : F γ N ^ (-(1 / 2 : ℝ)) < |(1 : ℝ)| := by
      rw [abs_one]
      apply Real.rpow_lt_one_of_one_lt_of_neg _ (by norm_num)
      rw [hFexp]
      exact Real.one_lt_exp_iff.mpr hLγ
    have hA := hL4 N (by omega) 1 hα (by simp) (Δ / 2) 0 le_rfl (by positivity)
      (by linarith)
    have hBB := hL4 N (by omega) 1 hα (by simp) 1 (1 - Δ / 2) (by linarith) (by linarith)
      le_rfl
    simp only [one_mul] at hA hBB
    have hcA := (abs_le.mp hA).2
    have hcB := (abs_le.mp hBB).2
    have hsub : (Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ =>
          Int.fract (F γ n) < Δ / 2 ∨ 1 - Δ / 2 < Int.fract (F γ n)) ⊆
        ((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
            0 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < Δ / 2) ∪
          (Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
            1 - Δ / 2 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < 1)) ∪ {N / 2} := by
      intro n hn
      simp only [mem_filter, mem_Icc, mem_Ioc, mem_union, mem_singleton] at hn ⊢
      obtain ⟨⟨hn1, hn2⟩, hP⟩ := hn
      by_cases hn3 : n = N / 2
      · right
        exact hn3
      · left
        have hn4 : N / 2 < n := by omega
        rcases hP with h | h
        · left
          exact ⟨⟨hn4, hn2⟩, Int.fract_nonneg _, h⟩
        · right
          exact ⟨⟨hn4, hn2⟩, h.le, Int.fract_lt_one _⟩
    have hcard := (card_le_card hsub).trans
      ((card_union_le _ _).trans (Nat.add_le_add_right (card_union_le _ _) _))
    rw [card_singleton] at hcard
    have hcardR : (((Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ =>
          Int.fract (F γ n) < Δ / 2 ∨ 1 - Δ / 2 < Int.fract (F γ n))).card : ℝ) ≤
        (((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
            0 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < Δ / 2)).card : ℝ) +
        (((Finset.Ioc (N / 2) N).filter (fun n : ℕ =>
            1 - Δ / 2 ≤ Int.fract (F γ n) ∧ Int.fract (F γ n) < 1)).card : ℝ) + 1 := by
      exact_mod_cast hcard
    have he4 : 0 < Real.exp (-κ₄ * L ^ s) := Real.exp_pos _
    have ht : B₄ * N * Real.exp (-κ₄ * L ^ s) ≤ |B₄| * N * E := by
      calc B₄ * N * Real.exp (-κ₄ * L ^ s) ≤ |B₄| * N * Real.exp (-κ₄ * L ^ s) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hB4 hNpos.le) he4.le
        _ ≤ |B₄| * N * E := mul_le_mul_of_nonneg_left ha (by positivity)
    have hgoal : (2 + 2 * |B₄|) * N * (Δ + E) =
        2 * (N * Δ) + 2 * (|B₄| * N * Δ) + 2 * (N * E) + 2 * (|B₄| * N * E) := by ring
    have hpos1 : 0 ≤ |B₄| * N * Δ := by positivity
    have hpos2 : 0 ≤ N * Δ := by positivity
    rw [hgoal]
    linarith
  · have hc1 := card_filter_le (Finset.Icc ((N + 1) / 2) N) (fun n : ℕ =>
          Int.fract (F γ n) < Δ / 2 ∨ 1 - Δ / 2 < Int.fract (F γ n))
    have hc2 : (Finset.Icc ((N + 1) / 2) N).card ≤ N := by
      rw [Nat.card_Icc]
      omega
    have hcR : (((Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ =>
          Int.fract (F γ n) < Δ / 2 ∨ 1 - Δ / 2 < Int.fract (F γ n))).card : ℝ) ≤ N := by
      exact_mod_cast hc1.trans hc2
    have hND : (N : ℝ) * 1 ≤ N * Δ := mul_le_mul_of_nonneg_left hΔ1 hNpos.le
    have hgoal : (2 + 2 * |B₄|) * N * (Δ + E) =
        2 * (N * Δ) + 2 * (|B₄| * N * Δ) + 2 * (N * E) + 2 * (|B₄| * N * E) := by ring
    have hpos1 : 0 ≤ |B₄| * N * Δ := by positivity
    have hpos3 : 0 ≤ |B₄| * N * E := by positivity
    rw [hgoal]
    linarith

/-- `leaf_boundary_count` of `Feed1122LeafEvenMoment`, its statement copied verbatim, from the
existing open statement `lemma4` of `State1539`, Lemma 4 of P0082, p. 359. No new sorry;
CONDITIONAL ON `lemma4`. -/
theorem leaf_boundary_count_of_leaves (γ : ℝ) (h1 : 1 < γ) (h2 : γ < 3 / 2) :
    ∃ κ₀ : ℝ, 0 < κ₀ ∧ ∀ κ : ℝ, 0 < κ → κ ≤ κ₀ →
      ∃ B : ℝ, 0 < B ∧ ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N → ∀ Δ : ℝ, 0 < Δ →
        (((Finset.Icc ((N + 1) / 2) N).filter (fun n : ℕ =>
            Int.fract (F γ n) < Δ / 2 ∨ 1 - Δ / 2 < Int.fract (F γ n))).card : ℝ)
          ≤ B * N * (Δ + calE γ κ N ^ (-(1 / 3 : ℝ)) / Real.log (F γ N) ^ 2) :=
  leaf_boundary_count_of_lemma4 lemma4 γ h1 h2

/-- Twin check: the same type as the leaf. -/
example : type_of% @leaf_boundary_count_of_leaves = type_of% @leaf_boundary_count := rfl

end LeanLab.ExceptionalSet.U1539

#print axioms LeanLab.ExceptionalSet.U1539.boundary_growth
#print axioms LeanLab.ExceptionalSet.U1539.leaf_boundary_count_of_lemma4
#print axioms LeanLab.ExceptionalSet.U1539.leaf_boundary_count_of_leaves
