/-
P0068 Zhan 1991, Proposition 1 for (3.12), page 269 last paragraph with pages 266 and 267,
split into one new cited LEAF plus the two LEAFs of SPLIT_prop3_312_S9.lean. Burst 20261124,
session S9, unit S9-06. Source: papers/P0068.pdf, journal pages 266, 267 and 269, pdf pages 8,
9 and 11. AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Page 266: by (3.5), `1 ≤ j₀ ≤ 10`; Perron's formula for `f_{j₀}`, the line shift with Lemma 7
and, by page 269, the usual second power moment of `L(s, χ)` over `[T₂, 2T₂]` in place of
Lemma 2 give `Σ_{χ≠χ₀} ∫_{T₂}^{2T₂} |f_{j₀}(1/2+it, χ)|² dt ≪ q|T₂| L^c`. Page 266 bottom and
page 267 top: Cauchy, Lemma 6 and (3.13) give
`Σ_χ ∫ |F| ≪ (q|T₂|)^{1/2} (q|T₂| + N N_{j₀}⁻¹)^{1/2} L^{c}
≪ (qN)^{1/2} (|T₂| A / N) L^{-B-c₀}` if `N_{j₀} ≥ N A⁻¹ L^{c₅}`, `|T₂| ≥ N A⁻¹` and `c₁, c₅`
are large. The `f_{j₀}` bound is the new LEAF; Cauchy and the mean value bound are the LEAFs
of Proposition 3 for (3.12); the rest is PROVED.
-/
import LeanLab.Zhan1991.SPLIT_prop3_312_S9

namespace LeanLab.Zhan1991
open Finset Real

noncomputable section

/-- LEAF: Proposition 1 for (3.12), page 269 last paragraph with page 266: for `j₀ ≤ 10` in the
paper's numbering, here `j.val < 10`, and `N_{j₀} ≥ N A⁻¹ L^{c₅}`, Perron's formula for `f_{j₀}`
with `c = 1/2 + L⁻¹`, the shift to the line `Re w = 0` with Lemma 7, Cauchy in `v` and the usual
second power moment `Σ_χ ∫_{T₂}^{2T₂} |L'(1/2+it, χ)|² dt ≪ q|T₂| L^c` in place of Lemma 2 give
`Σ_{χ≠χ₀} ∫_{T₂}^{2T₂} |f_{j₀}(1/2+it, χ)|² dt ≪ q|T₂| L^{c₈}` for `T₀ ≤ |T₂| ≤ 2T`. The power
`c₈` is fixed before `ε` and `c₅`; for (3.11) the paper has `L⁵`. Class HARD. -/
theorem f_j0_moment_312_leaf_S9 : ∃ c8 : ℝ, 0 ≤ c8 ∧ ∀ ε : ℝ, 0 < ε → ∃ c5m : ℝ, 0 < c5m ∧
    ∀ c5 ≥ c5m, ∃ c1m : ℝ, ∀ c1 ≥ c1m, ∃ c2m : ℝ, ∀ c2 ≥ c2m, ∃ c3 : ℝ, 0 < c3 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (A lam : ℝ) (q : ℕ) [NeZero q] (Nv : Fin 20 → ℝ) (T2 : ℝ) (j : Fin 20),
      N₀ ≤ N → Hyp2 c1 c2 c3 N A lam q → Cond35 N Nv → T0cut N A lam ≤ |T2| →
      |T2| ≤ 2 * Tcut q N A lam ε → j.val < 10 → (N : ℝ) / A * Real.log N ^ c5 ≤ Nv j →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.uIoc T2 (2 * T2), ‖fj (j.val + 1) (Nv j) χ (1 / 2 + t * Complex.I)‖ ^ 2
        ≤ K * Real.log N ^ c8 * q * |T2| := by
  sorry

/-- PROVED, page 266: by (3.5), an `N_{j₀} ≥ N A⁻¹ L^{c₅}` has `j₀ ≤ 10`, since
`N_j ≤ N^{1/10}` for `j > 10` while `N A⁻¹ ≥ N^{1/3}` for `A ≤ N^{2/3}`. -/
theorem j0_le_ten_312_S9 {N : ℕ} {A c5 : ℝ} {Nv : Fin 20 → ℝ} {j : Fin 20} (hN : 1 < (N : ℝ))
    (hA : 0 < A) (hA2 : A ≤ (N : ℝ) ^ (2 / 3 : ℝ)) (hc5 : 1 ≤ Real.log N ^ c5)
    (hC : Cond35 N Nv) (hj : (N : ℝ) / A * Real.log N ^ c5 ≤ Nv j) : j.val < 10 := by
  by_contra h
  push_neg at h
  have h1 := hC.2.2.2 j h
  have hN0 : (0 : ℝ) ≤ N := by linarith
  have h3 : (N : ℝ) ^ (1 / 3 : ℝ) ≤ N / A := by
    rw [le_div_iff₀ hA]
    calc (N : ℝ) ^ (1 / 3 : ℝ) * A ≤ (N : ℝ) ^ (1 / 3 : ℝ) * (N : ℝ) ^ (2 / 3 : ℝ) :=
          mul_le_mul_of_nonneg_left hA2 (by positivity)
      _ = N := by rw [← Real.rpow_add (by linarith)]; norm_num
  have h4 : (N : ℝ) ^ (1 / 10 : ℝ) < (N : ℝ) ^ (1 / 3 : ℝ) :=
    Real.rpow_lt_rpow_of_exponent_lt hN (by norm_num)
  have h5 : (N : ℝ) / A ≤ (N : ℝ) / A * Real.log N ^ c5 :=
    le_mul_of_one_le_right (by positivity) hc5
  linarith

/-- PROVED, page 267 top, read for (3.12): with `a = qT`, `T ≥ N/A` and `M ≤ A L^{-c₅}`,
`a (a + M) ≤ 2 q N (T A / N)² L^{-E}` once `c₁, c₅ ≥ E`. -/
theorem prop1_312_arith_S9 {N : ℕ} {A q L E c1 c5 M T : ℝ} (hL : 1 ≤ L) (hA : 0 < A)
    (hN : 0 < (N : ℝ)) (hq0 : 0 < q) (hc1 : E ≤ c1) (hc5 : E ≤ c5)
    (hq2 : q ≤ A ^ 2 / N * L ^ (-c1)) (hT : N / A ≤ T) (hM : 0 ≤ M)
    (hMA : M ≤ A * L ^ (-c5)) :
    (q * T) * (q * T + M) ≤ 2 * (q * N) * (T * A / N) ^ 2 * L ^ (-E) := by
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have e1 : L ^ (-c1) ≤ L ^ (-E) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have e5 : L ^ (-c5) ≤ L ^ (-E) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have hR : (q * N) * (T * A / N) ^ 2 = q * T ^ 2 * A ^ 2 / N := by field_simp
  have hTA : (N : ℝ) ≤ T * A := by rw [div_le_iff₀ hA] at hT; linarith
  have hTA1 : 1 ≤ T * A / N := by rw [le_div_iff₀ hN]; linarith
  have t1 : (q * T) * (q * T) ≤ (q * N) * (T * A / N) ^ 2 * L ^ (-E) := by
    rw [hR]
    have h := mul_le_mul_of_nonneg_right hq2 (by positivity : (0 : ℝ) ≤ q * T ^ 2)
    have h' : A ^ 2 / N * L ^ (-c1) * (q * T ^ 2) = q * T ^ 2 * A ^ 2 / N * L ^ (-c1) := by
      ring
    rw [h'] at h
    calc (q * T) * (q * T) = q * (q * T ^ 2) := by ring
      _ ≤ q * T ^ 2 * A ^ 2 / N * L ^ (-c1) := h
      _ ≤ q * T ^ 2 * A ^ 2 / N * L ^ (-E) := mul_le_mul_of_nonneg_left e1 (by positivity)
  have t2 : q * T * M ≤ (q * N) * (T * A / N) ^ 2 * L ^ (-E) := by
    rw [hR]
    calc q * T * M ≤ q * T * (A * L ^ (-c5)) := mul_le_mul_of_nonneg_left hMA (by positivity)
      _ ≤ q * T * A * L ^ (-E) := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left e5 (by positivity)
      _ = q * T * A * 1 * L ^ (-E) := by ring
      _ ≤ q * T * A * (T * A / N) * L ^ (-E) := by gcongr
      _ = q * T ^ 2 * A ^ 2 / N * L ^ (-E) := by ring
  nlinarith

/-- PROVED from the LEAFs `f_j0_moment_312_leaf_S9`, `cauchy_312_leaf_S9` and
`mv_FJ_312_leaf_S9`: Proposition 1 for (3.12), `Prop1_312`. Constants:
`E = 2 (B + c₀) + c₈ + c₇`, `c₅ = max(c₅', E)`, `c₁ ≥ max(c₁', E)`, the rest from the `f_{j₀}`
LEAF, `K = (2 max(K₁, 0) max(K₆, 0))^{1/2}`. -/
theorem prop1_312_of_leaves_S9 : Prop1_312 := by
  intro B _ c0 _ ε hε
  obtain ⟨c7, hc7, KB, N0B, hMV⟩ := mv_FJ_312_leaf_S9
  obtain ⟨c8, hc8, hF⟩ := f_j0_moment_312_leaf_S9
  obtain ⟨c5m, hc5m, hF⟩ := hF ε hε
  set E : ℝ := 2 * (B + c0) + c8 + c7 with hEdef
  set c5 := max c5m E with hc5def
  have hc5pos : 0 < c5 := lt_of_lt_of_le hc5m (le_max_left _ _)
  obtain ⟨c1m', hF1⟩ := hF c5 (le_max_left _ _)
  refine ⟨c5, hc5pos, max c1m' E, fun c1 hc1 => ?_⟩
  obtain ⟨c2m', hF2⟩ := hF1 c1 (le_trans (le_max_left _ _) hc1)
  refine ⟨c2m', fun c2 hc2 => ?_⟩
  obtain ⟨c3, hc3, KC, N0C, hFC⟩ := hF2 c2 hc2
  refine ⟨c3, hc3, Real.sqrt (2 * max KC 0 * max KB 0), max (max N0B N0C) 3, ?_⟩
  intro N A lam q _ Nv T2 hN0 hH hC hT0 hT' hj
  obtain ⟨j, hj⟩ := hj
  have hN3 : (3 : ℝ) ≤ N := le_trans (le_max_right _ _) hN0
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
  have hHge : 1 ≤ (N : ℝ) / A := by
    rw [le_div_iff₀ hA, one_mul]
    calc A ≤ (N : ℝ) ^ (2 / 3 : ℝ) := hA2
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = N := Real.rpow_one _
  have hTH : (N : ℝ) / A ≤ |T2| := le_trans (T0cut_ge_H_S9 hA hNpos.le) hT0
  have hT1 : 1 ≤ |T2| := le_trans hHge hTH
  have hLc5 : 1 ≤ L ^ c5 := Real.one_le_rpow hL hc5pos.le
  have hj10 : j.val < 10 := j0_le_ten_312_S9 (by linarith) hA hA2 hLc5 hC hj
  have hfC := hFC N A lam q Nv T2 j hNC hH hC hT0 hT' hj10 hj
  have hmv := hMV N q Nv {j}ᶜ T2 hNB hC hT1
  have hcs := cauchy_312_leaf_S9 Nv q {j} T2
  simp only [Finset.prod_singleton] at hcs
  set M := ∏ i ∈ ({j} : Finset (Fin 20))ᶜ, Nv i with hMdef
  have hM0 : 0 ≤ M := Finset.prod_nonneg (fun i _ => le_trans (by norm_num) (hC.1 i))
  have hMN : Nv j * M ≤ N := by
    have := Finset.prod_mul_prod_compl ({j} : Finset (Fin 20)) Nv
    rw [Finset.prod_singleton] at this
    rw [this]; exact hC.2.2.1
  have hMA : M ≤ A * L ^ (-c5) := by
    have hpos : 0 < (N : ℝ) / A * L ^ c5 := by positivity
    have h1 : (N : ℝ) / A * L ^ c5 * M ≤ N := le_trans (mul_le_mul_of_nonneg_right hj hM0) hMN
    rw [Real.rpow_neg hL0.le]
    rw [← le_div_iff₀' hpos] at h1
    calc M ≤ N / ((N : ℝ) / A * L ^ c5) := h1
      _ = A * (L ^ c5)⁻¹ := by field_simp
  have har := prop1_312_arith_S9 (N := N) (q := (q : ℝ)) (L := L) (E := E) (T := |T2|) hL hA
    hNpos hq0 (le_trans (le_max_right _ _) hc1) (le_max_right _ _) hq3 hTH hM0 hMA
  set KC' := max KC 0
  set KB' := max KB 0
  have hKC : 0 ≤ KC' := le_max_right _ _
  have hKB : 0 ≤ KB' := le_max_right _ _
  have hX : 0 ≤ (q : ℝ) * |T2| + M := by positivity
  have hL8 : 0 ≤ L ^ c8 := by positivity
  have hLc7 : 0 ≤ L ^ c7 := by positivity
  have hW : 0 ≤ |T2| * A / N := by positivity
  have b1 : KC * L ^ c8 * q * |T2| ≤ KC' * L ^ c8 * q * |T2| := by
    gcongr; exact le_max_left _ _
  have b2 : KB * ((q : ℝ) * |T2| + M) * L ^ c7 ≤ KB' * ((q : ℝ) * |T2| + M) * L ^ c7 := by
    gcongr; exact le_max_left _ _
  rw [show ∀ x : ℝ, Real.sqrt (2 * KC' * KB') * x * A * |T2| * L ^ (-B - c0)
      = Real.sqrt (2 * KC' * KB') * (x * A * |T2| * L ^ (-B - c0)) from fun x => by ring,
    eq312_rhs_S9 hNpos hq0.le]
  refine le_trans hcs ?_
  calc _ ≤ Real.sqrt (KC' * L ^ c8 * q * |T2|) *
        Real.sqrt (KB' * ((q : ℝ) * |T2| + M) * L ^ c7) := by
        gcongr
        · exact le_trans hfC b1
        · exact le_trans hmv b2
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

/-- The LEAF `prop1_312_leaf` of SPLIT_eq312_1122d.lean, wired through the split. -/
theorem prop1_312_split_S9 : Prop1_312 := prop1_312_of_leaves_S9

end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.j0_le_ten_312_S9
#print axioms LeanLab.Zhan1991.prop1_312_arith_S9
#print axioms LeanLab.Zhan1991.prop1_312_of_leaves_S9
