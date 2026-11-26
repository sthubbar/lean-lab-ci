/-
P0068 Zhan 1991, Proposition 2 for (3.12), page 269 last paragraph with page 267, displays
(3.14) and (3.15), split into two new cited LEAFs plus the mean value LEAF of
SPLIT_prop3_312_S9.lean. Burst 20261124, session S9, unit S9-07. Source: papers/P0068.pdf,
journal pages 267 and 269, pdf pages 9 and 11. AI-written Lean code, Claude. Checked only by
the Lean kernel. Binary Goldbach is OPEN.

Page 267: by Lemma 3 and Hölder, (3.14) and (3.15) bound the fourth moments of `f_{j₁}` and
`f_{j₂}`; again by Hölder, with Lemma 6 and (3.13) for `G = Π_{j ≠ j₁, j₂} f_j`, (3.11) follows.
Page 269: for (3.12) the usual fourth power moment of `L(s, χ)` over `[T₂, 2T₂]` replaces
Lemma 3, so `Σ_χ ∫_{T₂}^{2T₂} |f_{j_i}|⁴ ≪ q|T₂| L^c` with no factor `N^ε`. Then
`Σ_χ ∫ |F| ≪ (q|T₂|)^{1/2} (q|T₂| + N N_{j₁}⁻¹ N_{j₂}⁻¹)^{1/2} L^c`, and
`N N_{j₁}⁻¹ N_{j₂}⁻¹ ≤ N (N A⁻¹)^{-4/3} = A (A N⁻¹)^{1/3} ≤ A N^{-1/9} ≤ A L^{-E}` for large `N`,
so the chain of Proposition 1 for (3.12) closes. The analytic steps are LEAFs; the rest is
PROVED. For (3.12) the `N^ε` obstruction noted for (3.11) in the sibling note
Zhan1991-S9-04-prop2-question.md does not arise.
-/
import LeanLab.Zhan1991.SPLIT_prop1_312_S9

namespace LeanLab.Zhan1991
open Finset Real Filter

noncomputable section

/-- LEAF: page 267, the two applications of Hölder's inequality in the proof of Proposition 2,
run over `[T₂, 2T₂]` as page 269 says: for `j₁ ≠ j₂`, with `G = Π_{j ≠ j₁, j₂} f_j`,
`Σ_χ ∫ |F| ≤ (Σ_χ ∫ |f_{j₁}|⁴)^{1/4} (Σ_χ ∫ |f_{j₂}|⁴)^{1/4} (Σ_χ ∫ |G|²)^{1/2}`.
Class EASY. -/
theorem holder_312_leaf_S9 (Nv : Fin 20 → ℝ) (q : ℕ) [NeZero q] (i j : Fin 20) (hij : i ≠ j)
    (T2 : ℝ) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.uIoc T2 (2 * T2), ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
      ≤ (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.uIoc T2 (2 * T2),
            ‖fj (i.val + 1) (Nv i) χ (1 / 2 + t * Complex.I)‖ ^ 4) ^ (1 / 4 : ℝ) *
        (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.uIoc T2 (2 * T2),
            ‖fj (j.val + 1) (Nv j) χ (1 / 2 + t * Complex.I)‖ ^ 4) ^ (1 / 4 : ℝ) *
        Real.sqrt (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.uIoc T2 (2 * T2),
            ‖∏ k ∈ ({i, j} : Finset (Fin 20))ᶜ, fj (k.val + 1) (Nv k) χ
              (1 / 2 + t * Complex.I)‖ ^ 2) := by
  sorry

/-- LEAF: Proposition 2 for (3.12), page 269 last paragraph with page 267, displays (3.14) and
(3.15): Perron's formula for `f_j`, the line shift with Lemma 7 and the usual fourth power
moment `Σ_χ ∫_{T₂}^{2T₂} |L'(1/2+it, χ)|⁴ dt ≪ q|T₂| L^c` in place of Lemma 3 give, when all
`N_k ≤ N A⁻¹ L^{c₅}` and `T₀ ≤ |T₂| ≤ 2T`,
`Σ_{χ≠χ₀} ∫_{T₂}^{2T₂} |f_j(1/2+it, χ)|⁴ dt ≪ q|T₂| L^{c₈}`. For `j > 10` in the paper's
numbering, `N_j ≤ N^{1/10}` and the mean value theorem for `f_j²` gives the same bound.
Class HARD. -/
theorem f_fourth_moment_312_leaf_S9 : ∀ ε : ℝ, 0 < ε → ∀ c5 : ℝ, 0 < c5 → ∃ c8 : ℝ, 0 ≤ c8 ∧
    ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∃ c2m : ℝ, ∀ c2 ≥ c2m, ∃ c3 : ℝ, 0 < c3 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (A lam : ℝ) (q : ℕ) [NeZero q] (Nv : Fin 20 → ℝ) (T2 : ℝ) (j : Fin 20),
      N₀ ≤ N → Hyp2 c1 c2 c3 N A lam q → Cond35 N Nv → T0cut N A lam ≤ |T2| →
      |T2| ≤ 2 * Tcut q N A lam ε → (∀ k, Nv k ≤ (N : ℝ) / A * Real.log N ^ c5) →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.uIoc T2 (2 * T2), ‖fj (j.val + 1) (Nv j) χ (1 / 2 + t * Complex.I)‖ ^ 4
        ≤ K * Real.log N ^ c8 * q * |T2| := by
  sorry

/-- PROVED: `L^E ≤ x^{1/9}` for all large `x`, from `log x ^ E = o(x^{1/9})`. -/
theorem logpow_le_ninth_S9 (E : ℝ) : ∃ N₀ : ℝ, ∀ x : ℝ, N₀ ≤ x →
    Real.log x ^ E ≤ x ^ (1 / 9 : ℝ) := by
  have h := (isLittleO_log_rpow_rpow_atTop E (by norm_num : (0 : ℝ) < 1 / 9)).bound one_pos
  obtain ⟨a, ha⟩ := eventually_atTop.mp (h.and (eventually_ge_atTop (3 : ℝ)))
  refine ⟨a, fun x hx => ?_⟩
  obtain ⟨h1, h3⟩ := ha x hx
  have hl : 0 ≤ Real.log x := Real.log_nonneg (by linarith)
  rw [Real.norm_of_nonneg (Real.rpow_nonneg hl _),
    Real.norm_of_nonneg (Real.rpow_nonneg (by linarith) _), one_mul] at h1
  exact h1

/-- PROVED, page 267 read for (3.12): if `N_{j₁} N_{j₂} M ≤ N`,
`N_{j₁} N_{j₂} ≥ H^{4/3+δ}` with `H = N A⁻¹ ≥ 1`, and `L^E ≤ H^{1/3}`, then `M ≤ A L^{-E}`. -/
theorem prop2_312_M_S9 {N A L E δ P M : ℝ} (hA : 0 < A) (hH : 1 ≤ N / A) (hδ : 0 ≤ δ)
    (hL : 0 < L) (hM : 0 ≤ M) (hPM : P * M ≤ N) (hP : (N / A) ^ ((4 / 3 : ℝ) + δ) ≤ P)
    (hLE : L ^ E ≤ (N / A) ^ (1 / 3 : ℝ)) : M ≤ A * L ^ (-E) := by
  set H := N / A with hHdef
  have hH0 : 0 < H := by linarith
  have hN : N = A * H := by rw [hHdef]; field_simp
  have h43 : H * H ^ (1 / 3 : ℝ) ≤ H ^ ((4 / 3 : ℝ) + δ) := by
    calc H * H ^ (1 / 3 : ℝ) = H ^ (4 / 3 : ℝ) := by
          rw [show (4 / 3 : ℝ) = 1 + 1 / 3 by norm_num, Real.rpow_add hH0, Real.rpow_one]
      _ ≤ H ^ ((4 / 3 : ℝ) + δ) := Real.rpow_le_rpow_of_exponent_le hH (by linarith)
  have h3 : 0 < H ^ (1 / 3 : ℝ) := by positivity
  have hMH : M * H ^ (1 / 3 : ℝ) ≤ A := by
    have : H * (M * H ^ (1 / 3 : ℝ)) ≤ H * A := by
      calc H * (M * H ^ (1 / 3 : ℝ)) = (H * H ^ (1 / 3 : ℝ)) * M := by ring
        _ ≤ P * M := mul_le_mul_of_nonneg_right (le_trans h43 hP) hM
        _ ≤ N := hPM
        _ = H * A := by rw [hN]; ring
    exact le_of_mul_le_mul_left this hH0
  have hLE0 : 0 < L ^ E := by positivity
  rw [Real.rpow_neg hL.le, ← div_eq_mul_inv, le_div_iff₀ hLE0]
  calc M * L ^ E ≤ M * H ^ (1 / 3 : ℝ) := mul_le_mul_of_nonneg_left hLE hM
    _ ≤ A := hMH

/-- PROVED from the LEAFs `holder_312_leaf_S9`, `f_fourth_moment_312_leaf_S9` and
`mv_FJ_312_leaf_S9`: Proposition 2 for (3.12), `Prop2_312`. Constants:
`E = 2 (B + c₀) + c₈ + c₇`, `c₁ ≥ max(c₁', E)`, the rest from the fourth moment LEAF,
`K = (2 max(K₄, 0) max(K₆, 0))^{1/2}`, `N₀` also so large that `L^E ≤ N^{1/9}`. -/
theorem prop2_312_of_leaves_S9 : Prop2_312 := by
  intro δ hδ B _ c0 _ ε hε c5 hc5
  obtain ⟨c7, hc7, KB, N0B, hMV⟩ := mv_FJ_312_leaf_S9
  obtain ⟨c8, hc8, hF⟩ := f_fourth_moment_312_leaf_S9 ε hε c5 hc5
  set E : ℝ := 2 * (B + c0) + c8 + c7 with hEdef
  obtain ⟨N0L, hN0L⟩ := logpow_le_ninth_S9 E
  obtain ⟨c1m', hF1⟩ := hF
  refine ⟨max c1m' E, fun c1 hc1 => ?_⟩
  obtain ⟨c2m', hF2⟩ := hF1 c1 (le_trans (le_max_left _ _) hc1)
  refine ⟨c2m', fun c2 hc2 => ?_⟩
  obtain ⟨c3, hc3, KC, N0C, hFC⟩ := hF2 c2 hc2
  refine ⟨c3, hc3, Real.sqrt (2 * max KC 0 * max KB 0), max (max N0B N0C) (max N0L 3), ?_⟩
  intro N A lam q _ Nv T2 hN0 hH hC hT0 hT' hall hpair
  obtain ⟨i, j, hij, hp⟩ := hpair
  have hN3 : (3 : ℝ) ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN0
  have hNL : N0L ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN0
  have hNB : N0B ≤ N := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN0
  have hNC : N0C ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN0
  set L := Real.log N with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hL0 : 0 < L := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  have hH' := hH
  obtain ⟨hA1, hA2, _, _, hq3, _⟩ := hH'
  have hA : 0 < A := lt_of_lt_of_le (by positivity) hA1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  have hN13 : (N : ℝ) ^ (1 / 3 : ℝ) ≤ N / A := by
    rw [le_div_iff₀ hA]
    calc (N : ℝ) ^ (1 / 3 : ℝ) * A ≤ (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_left hA2 (by positivity)
      _ = N := by rw [← Real.rpow_add hNpos]; norm_num
  have hHge : 1 ≤ (N : ℝ) / A :=
    le_trans (Real.one_le_rpow (by linarith) (by norm_num)) hN13
  have hTH : (N : ℝ) / A ≤ |T2| := le_trans (T0cut_ge_H_S9 hA hNpos.le) hT0
  have hLE : L ^ E ≤ ((N : ℝ) / A) ^ (1 / 3 : ℝ) := by
    calc L ^ E ≤ (N : ℝ) ^ (1 / 9 : ℝ) := hN0L N hNL
      _ = ((N : ℝ) ^ (1 / 3 : ℝ)) ^ (1 / 3 : ℝ) := by
          rw [← Real.rpow_mul hNpos.le]; norm_num
      _ ≤ ((N : ℝ) / A) ^ (1 / 3 : ℝ) :=
          Real.rpow_le_rpow (by positivity) hN13 (by norm_num)
  have hfi := hFC N A lam q Nv T2 i hNC hH hC hT0 hT' hall
  have hfj := hFC N A lam q Nv T2 j hNC hH hC hT0 hT' hall
  have hmv := hMV N q Nv ({i, j} : Finset (Fin 20))ᶜ T2 hNB hC (le_trans hHge hTH)
  have hhol := holder_312_leaf_S9 Nv q i j hij T2
  set M := ∏ k ∈ ({i, j} : Finset (Fin 20))ᶜ, Nv k with hMdef
  have hM0 : 0 ≤ M := Finset.prod_nonneg (fun k _ => le_trans (by norm_num) (hC.1 k))
  have hMN : Nv i * Nv j * M ≤ N := by
    have := Finset.prod_mul_prod_compl ({i, j} : Finset (Fin 20)) Nv
    rw [Finset.prod_pair hij] at this
    rw [this]; exact hC.2.2.1
  have hMA : M ≤ A * L ^ (-E) := prop2_312_M_S9 hA hHge hδ.le hL0 hM0 hMN hp hLE
  have har := prop1_312_arith_S9 (N := N) (q := (q : ℝ)) (L := L) (E := E) (T := |T2|) hL hA
    hNpos hq0 (le_trans (le_max_right _ _) hc1) le_rfl hq3 hTH hM0 hMA
  set KC' := max KC 0
  set KB' := max KB 0
  have hKC : 0 ≤ KC' := le_max_right _ _
  have hKB : 0 ≤ KB' := le_max_right _ _
  have hX : 0 ≤ (q : ℝ) * |T2| + M := by positivity
  have hL8 : 0 ≤ L ^ c8 := by positivity
  have hLc7 : 0 ≤ L ^ c7 := by positivity
  have hW : 0 ≤ |T2| * A / N := by positivity
  set Z := KC' * L ^ c8 * q * |T2| with hZ
  have hZ0 : 0 ≤ Z := by positivity
  have b1 : KC * L ^ c8 * q * |T2| ≤ Z := by
    rw [hZ]; gcongr; exact le_max_left _ _
  have b2 : KB * ((q : ℝ) * |T2| + M) * L ^ c7 ≤ KB' * ((q : ℝ) * |T2| + M) * L ^ c7 := by
    gcongr; exact le_max_left _ _
  have hnn : ∀ k : Fin 20, 0 ≤ ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter
      (· ≠ 1), ∫ t in Set.uIoc T2 (2 * T2),
        ‖fj (k.val + 1) (Nv k) χ (1 / 2 + t * Complex.I)‖ ^ 4 :=
    fun k => Finset.sum_nonneg (fun χ _ => MeasureTheory.integral_nonneg (fun t => by positivity))
  have q1 := Real.rpow_le_rpow (hnn i) (le_trans hfi b1) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have q2 := Real.rpow_le_rpow (hnn j) (le_trans hfj b1) (by norm_num : (0 : ℝ) ≤ 1 / 4)
  have hsq : Z ^ (1 / 4 : ℝ) * Z ^ (1 / 4 : ℝ) = Real.sqrt Z := by
    rw [← Real.rpow_add' hZ0 (by norm_num), Real.sqrt_eq_rpow]; norm_num
  rw [show ∀ x : ℝ, Real.sqrt (2 * KC' * KB') * x * A * |T2| * L ^ (-B - c0)
      = Real.sqrt (2 * KC' * KB') * (x * A * |T2| * L ^ (-B - c0)) from fun x => by ring,
    eq312_rhs_S9 hNpos hq0.le]
  refine le_trans hhol ?_
  calc _ ≤ Z ^ (1 / 4 : ℝ) * Z ^ (1 / 4 : ℝ) *
        Real.sqrt (KB' * ((q : ℝ) * |T2| + M) * L ^ c7) := by
        apply mul_le_mul (mul_le_mul q1 q2 (Real.rpow_nonneg (hnn j) _)
          (Real.rpow_nonneg hZ0 _)) (Real.sqrt_le_sqrt (le_trans hmv b2))
          (Real.sqrt_nonneg _) (by positivity)
    _ = Real.sqrt (KC' * L ^ c8 * q * |T2|) *
        Real.sqrt (KB' * ((q : ℝ) * |T2| + M) * L ^ c7) := by rw [hsq]
    _ = Real.sqrt ((KC' * KB' * (L ^ c8 * L ^ c7)) *
          (((q : ℝ) * |T2|) * ((q : ℝ) * |T2| + M))) := by
        rw [← Real.sqrt_mul (by positivity)]
        congr 1; ring
    _ ≤ Real.sqrt ((KC' * KB' * (L ^ c8 * L ^ c7)) *
          (2 * ((q : ℝ) * N) * (|T2| * A / N) ^ 2 * L ^ (-E))) := by
        gcongr
    _ = Real.sqrt (2 * KC' * KB') *
          (((q : ℝ) * N) ^ (1 / 2 : ℝ) * (|T2| * A / N) * L ^ (-B - c0)) := by
        have hqN : (0 : ℝ) ≤ (q : ℝ) * N := by positivity
        have hpow : L ^ c8 * L ^ c7 * L ^ (-E) = (L ^ (-B - c0)) ^ 2 := by
          rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_natCast,
            ← Real.rpow_mul hL0.le]
          congr 1; rw [hEdef]; push_cast; ring
        have : (KC' * KB' * (L ^ c8 * L ^ c7)) *
              (2 * ((q : ℝ) * N) * (|T2| * A / N) ^ 2 * L ^ (-E))
            = (2 * KC' * KB') * ((q : ℝ) * N) * ((|T2| * A / N) * L ^ (-B - c0)) ^ 2 := by
          rw [mul_pow, ← hpow]; ring
        rw [this, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by positivity), Real.sqrt_eq_rpow ((q : ℝ) * N)]
        ring

/-- The LEAF `prop2_312_leaf` of SPLIT_eq312_1122d.lean, wired through the split. -/
theorem prop2_312_split_S9 : Prop2_312 := prop2_312_of_leaves_S9

/-- (3.12) from the six LEAFs of the three splits of worker C, burst 20261124. -/
theorem eq312_of_S9_leaves : Eq312 :=
  eq312_of_props prop1_312_of_leaves_S9 prop2_312_of_leaves_S9 prop3_312_of_leaves_S9

end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.logpow_le_ninth_S9
#print axioms LeanLab.Zhan1991.prop2_312_M_S9
#print axioms LeanLab.Zhan1991.prop2_312_of_leaves_S9
#print axioms LeanLab.Zhan1991.eq312_of_S9_leaves
