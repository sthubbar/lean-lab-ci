/-
P0068 Zhan 1991, Proposition 3 for (3.12), page 269 last paragraph with pages 267 and 268,
display (3.16), split into two cited LEAFs. Burst 20261124, session S9, unit S9-08.
Source: papers/P0068.pdf, journal pages 268 and 269, pdf pages 10 and 11. AI-written Lean code,
Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.

Page 269: "The proof of (3.12) is essentially the same as that of (3.11) ... we only need the
usual power moments of L-functions". For Proposition 3 the proof of page 268 runs over
`t ∈ [T₂, 2T₂]` in place of `(T₁, T₁ + H]`: Cauchy with `F = F₁ F₂`, then the mean value theorem
for Dirichlet polynomials over an interval of length `|T₂|`, Lemma 6, and (3.13) give
`Σ_χ ∫ |F_i|² ≪ (q|T₂| + M_i) L^{c₀}`. The chain
`(q|T₂| + M₁)(q|T₂| + M₂) ≪ qN (|T₂| A / N)² L^{-E}` uses `q ≤ A² N⁻¹ L^{-c₁}`,
`M_i ≤ A L^{-c₆}`, `M₁ M₂ ≤ N`, `q ≥ L^{c₂}` and `|T₂| ≥ T₀ ≥ N A⁻¹`. The two analytic steps
are LEAFs; the chain and the assembly are PROVED below. The products `Π_{j ∈ J} f_j` are
written out, so no new definition is needed.
-/
import LeanLab.Zhan1991.SPLIT_eq312_1122d

namespace LeanLab.Zhan1991
open Finset Real

noncomputable section

/-- LEAF: page 268, first inequality of the proof of Proposition 3, run over `[T₂, 2T₂]` as
page 269 says: Cauchy's inequality over `χ ≠ χ₀` and `t` with `F = F₁ F₂`,
`F₁ = Π_{J₁} f_j`, `F₂ = Π_{J \ J₁} f_j`. Class EASY. -/
theorem cauchy_312_leaf_S9 (Nv : Fin 20 → ℝ) (q : ℕ) [NeZero q] (J1 : Finset (Fin 20))
    (T2 : ℝ) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.uIoc T2 (2 * T2), ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
      ≤ Real.sqrt (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.uIoc T2 (2 * T2),
            ‖∏ j ∈ J1, fj (j.val + 1) (Nv j) χ (1 / 2 + t * Complex.I)‖ ^ 2) *
        Real.sqrt (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.uIoc T2 (2 * T2),
            ‖∏ j ∈ J1ᶜ, fj (j.val + 1) (Nv j) χ (1 / 2 + t * Complex.I)‖ ^ 2) := by
  sorry

/-- LEAF: page 268, second and third lines of the proof of Proposition 3, run over `[T₂, 2T₂]`
as page 269 says: the mean value theorem for Dirichlet polynomials over an interval of length
`|T₂| ≥ 1`, Lemma 6, applied to `F_J = Σ_{n ≤ M} b(n) χ(n) n^{-s}`, `b(n) ≪ d₂₀(n) L`, and the
divisor moment bounds (3.13) give
`Σ_{χ≠χ₀} ∫_{T₂}^{2T₂} |F_J(1/2+it, χ)|² dt ≪ (q|T₂| + M) L^{c₀}`, `M = Π_{j ∈ J} N_j`.
The exponent `c₀` of the paper is named `c7`. Class HARD. -/
theorem mv_FJ_312_leaf_S9 : ∃ c7 : ℝ, 0 ≤ c7 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (q : ℕ) [NeZero q] (Nv : Fin 20 → ℝ) (J : Finset (Fin 20)) (T2 : ℝ),
      N₀ ≤ N → Cond35 N Nv → 1 ≤ |T2| →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.uIoc T2 (2 * T2),
            ‖∏ j ∈ J, fj (j.val + 1) (Nv j) χ (1 / 2 + t * Complex.I)‖ ^ 2
        ≤ K * ((q : ℝ) * |T2| + ∏ j ∈ J, Nv j) * Real.log N ^ c7 := by
  sorry

/-- PROVED, page 268 last two lines, read for (3.12): with `a = q T`, `T ≥ N/A`,
`M₁, M₂ ≤ A L^{-c₆}` and `M₁ M₂ ≤ N`,
`(a + M₁)(a + M₂) ≤ 4 q N (T A / N)² L^{-E}` once `c₁, c₂, c₆ ≥ E`. -/
theorem prop3_312_arith_S9 {N : ℕ} {A q L E c1 c2 c6 M1 M2 T : ℝ} (hL : 1 ≤ L) (hA : 0 < A)
    (hN : 0 < (N : ℝ)) (hq0 : 0 < q) (hc1 : E ≤ c1) (hc2 : E ≤ c2) (hc6 : E ≤ c6)
    (hq1 : L ^ c2 ≤ q) (hq2 : q ≤ A ^ 2 / N * L ^ (-c1)) (hT : N / A ≤ T)
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM1A : M1 ≤ A * L ^ (-c6)) (hM2A : M2 ≤ A * L ^ (-c6))
    (hMM : M1 * M2 ≤ N) :
    (q * T + M1) * (q * T + M2) ≤ 4 * (q * N) * (T * A / N) ^ 2 * L ^ (-E) := by
  have hL0 : 0 < L := by linarith
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) hT
  have e1 : L ^ (-c1) ≤ L ^ (-E) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have e6 : L ^ (-c6) ≤ L ^ (-E) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have e2 : L ^ (-E) * L ^ c2 ≥ 1 := by
    rw [← Real.rpow_add hL0]
    exact Real.one_le_rpow hL (by linarith)
  have hE0 : 0 < L ^ (-E) := Real.rpow_pos_of_pos hL0 _
  have hR : (q * N) * (T * A / N) ^ 2 = q * T ^ 2 * A ^ 2 / N := by field_simp
  have hTA : (N : ℝ) ≤ T * A := by rw [div_le_iff₀ hA] at hT; linarith
  have hTA1 : 1 ≤ T * A / N := by rw [le_div_iff₀ hN]; linarith
  -- (qT)² ≤ R L^{-E}
  have t1 : (q * T) * (q * T) ≤ (q * N) * (T * A / N) ^ 2 * L ^ (-E) := by
    rw [hR]
    have h := mul_le_mul_of_nonneg_right hq2 (by positivity : (0 : ℝ) ≤ q * T ^ 2)
    have h' : A ^ 2 / N * L ^ (-c1) * (q * T ^ 2) = q * T ^ 2 * A ^ 2 / N * L ^ (-c1) := by
      ring
    rw [h'] at h
    calc (q * T) * (q * T) = q * (q * T ^ 2) := by ring
      _ ≤ q * T ^ 2 * A ^ 2 / N * L ^ (-c1) := h
      _ ≤ q * T ^ 2 * A ^ 2 / N * L ^ (-E) := mul_le_mul_of_nonneg_left e1 (by positivity)
  have tM : ∀ M : ℝ, 0 ≤ M → M ≤ A * L ^ (-c6) →
      q * T * M ≤ (q * N) * (T * A / N) ^ 2 * L ^ (-E) := by
    intro M hM hMA
    rw [hR]
    calc q * T * M ≤ q * T * (A * L ^ (-c6)) := mul_le_mul_of_nonneg_left hMA (by positivity)
      _ ≤ q * T * A * L ^ (-E) := by
          rw [← mul_assoc]; exact mul_le_mul_of_nonneg_left e6 (by positivity)
      _ = q * T * A * 1 * L ^ (-E) := by ring
      _ ≤ q * T * A * (T * A / N) * L ^ (-E) := by gcongr
      _ = q * T ^ 2 * A ^ 2 / N * L ^ (-E) := by ring
  have t3 : M1 * M2 ≤ (q * N) * (T * A / N) ^ 2 * L ^ (-E) := by
    have hsq : 1 ≤ (T * A / N) ^ 2 := one_le_pow₀ hTA1
    calc M1 * M2 ≤ N := hMM
      _ ≤ N * (L ^ (-E) * L ^ c2) := le_mul_of_one_le_right hN.le e2
      _ ≤ N * (L ^ (-E) * q) := by gcongr
      _ = (q * N) * 1 * L ^ (-E) := by ring
      _ ≤ (q * N) * (T * A / N) ^ 2 * L ^ (-E) := by gcongr
  have := tM M1 hM1 hM1A
  have := tM M2 hM2 hM2A
  nlinarith

/-- PROVED: `T₀ = 4π (|λ| N + N A⁻¹) ≥ N A⁻¹ ≥ 1` for `0 < A ≤ N`, page 265. -/
theorem T0cut_ge_H_S9 {N : ℕ} {A lam : ℝ} (hA : 0 < A) (hN : 0 ≤ (N : ℝ)) :
    (N : ℝ) / A ≤ T0cut N A lam := by
  unfold T0cut
  have h1 : 0 ≤ |lam| * N := by positivity
  have h2 : 0 ≤ (N : ℝ) / A := by positivity
  nlinarith [Real.pi_gt_three]

/-- PROVED: the target of (3.12) written as `(qN)^{1/2} (|T₂| A / N) L^{-B-c₀}`. -/
theorem eq312_rhs_S9 {N : ℕ} {q A T L e : ℝ} (hN : 0 < (N : ℝ)) (hq : 0 ≤ q) :
    (q / N) ^ (1 / 2 : ℝ) * A * T * L ^ e = (q * N) ^ (1 / 2 : ℝ) * (T * A / N) * L ^ e := by
  rw [← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow]
  have h : q * N = q / N * (N : ℝ) ^ 2 := by field_simp
  rw [h, Real.sqrt_mul (by positivity), Real.sqrt_sq hN.le]
  field_simp

/-- PROVED from the two LEAFs: Proposition 3 for (3.12), `Prop3_312`. Constants:
`E = 2 (B + c₀ + c₇)`, `c₆, c₁, c₂ ≥ E`, `c₃ = 1`, `K = 2 max(K₆, 0)`, `N₀ = max(N₀', 3)`. -/
theorem prop3_312_of_leaves_S9 : Prop3_312 := by
  intro B _ c0 _ ε _
  obtain ⟨c7, hc7, KB, N0B, hMV⟩ := mv_FJ_312_leaf_S9
  set E : ℝ := 2 * (B + c0 + c7) with hEdef
  refine ⟨E, fun c6 hc6 => ⟨E, fun c1 hc1 => ⟨E, fun c2 hc2 => ⟨1, one_pos,
    2 * max KB 0, max N0B 3, ?_⟩⟩⟩⟩
  intro N A lam q _ Nv T2 hN0 hH hC hT0 _ J1 hJ1 hJ2
  have hN3 : (3 : ℝ) ≤ N := le_trans (le_max_right _ _) hN0
  have hNB : N0B ≤ N := le_trans (le_max_left _ _) hN0
  set L := Real.log N with hLdef
  have hL : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9; linarith
  have hL0 : 0 < L := by linarith
  have hNpos : (0 : ℝ) < N := by linarith
  obtain ⟨hA1, hA2, _, hq1, hq3, _⟩ := hH
  have hA : 0 < A := lt_of_lt_of_le (by positivity) hA1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (Nat.pos_of_ne_zero (NeZero.ne q))
  have hHge : 1 ≤ (N : ℝ) / A := by
    rw [le_div_iff₀ hA, one_mul]
    calc A ≤ (N : ℝ) ^ (2 / 3 : ℝ) := hA2
      _ ≤ (N : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le (by linarith) (by norm_num)
      _ = N := Real.rpow_one _
  have hTH : (N : ℝ) / A ≤ |T2| := le_trans (T0cut_ge_H_S9 hA hNpos.le) hT0
  have hT1 : 1 ≤ |T2| := le_trans hHge hTH
  have hpos : ∀ J : Finset (Fin 20), 0 ≤ ∏ j ∈ J, Nv j :=
    fun J => Finset.prod_nonneg (fun j _ => le_trans (by norm_num) (hC.1 j))
  have hMM : (∏ j ∈ J1, Nv j) * ∏ j ∈ J1ᶜ, Nv j ≤ N := by
    rw [Finset.prod_mul_prod_compl]; exact hC.2.2.1
  have h1 := hMV N q Nv J1 T2 hNB hC hT1
  have h2 := hMV N q Nv J1ᶜ T2 hNB hC hT1
  have hcs := cauchy_312_leaf_S9 Nv q J1 T2
  set K' := max KB 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  set M1 := ∏ j ∈ J1, Nv j
  set M2 := ∏ j ∈ J1ᶜ, Nv j
  have hLc7 : 0 ≤ L ^ c7 := (Real.rpow_pos_of_pos hL0 _).le
  have b1 : KB * ((q : ℝ) * |T2| + M1) * L ^ c7 ≤ K' * ((q : ℝ) * |T2| + M1) * L ^ c7 := by
    gcongr
    · have := hpos J1; positivity
    · exact le_max_left _ _
  have b2 : KB * ((q : ℝ) * |T2| + M2) * L ^ c7 ≤ K' * ((q : ℝ) * |T2| + M2) * L ^ c7 := by
    gcongr
    · have := hpos J1ᶜ; positivity
    · exact le_max_left _ _
  have har := prop3_312_arith_S9 (N := N) (q := (q : ℝ)) (L := L) (E := E) (T := |T2|) hL hA
    hNpos hq0 hc1 hc2 hc6 hq1 hq3 hTH (hpos J1) (hpos J1ᶜ) hJ1 hJ2 hMM
  have hX1 : 0 ≤ (q : ℝ) * |T2| + M1 := by have := hpos J1; positivity
  have hX2 : 0 ≤ (q : ℝ) * |T2| + M2 := by have := hpos J1ᶜ; positivity
  have hW : 0 ≤ |T2| * A / N := by positivity
  rw [show ∀ x : ℝ, 2 * max KB 0 * x * A * |T2| * L ^ (-B - c0)
      = 2 * max KB 0 * (x * A * |T2| * L ^ (-B - c0)) from fun x => by ring,
    eq312_rhs_S9 hNpos hq0.le]
  refine le_trans hcs ?_
  calc _ ≤ Real.sqrt (K' * ((q : ℝ) * |T2| + M1) * L ^ c7) *
        Real.sqrt (K' * ((q : ℝ) * |T2| + M2) * L ^ c7) := by
        gcongr
        · exact le_trans h1 b1
        · exact le_trans h2 b2
    _ = Real.sqrt ((K' * L ^ c7) ^ 2 *
          (((q : ℝ) * |T2| + M1) * ((q : ℝ) * |T2| + M2))) := by
        rw [← Real.sqrt_mul (by positivity)]
        congr 1; ring
    _ = K' * L ^ c7 * Real.sqrt (((q : ℝ) * |T2| + M1) * ((q : ℝ) * |T2| + M2)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    _ ≤ K' * L ^ c7 * Real.sqrt (4 * ((q : ℝ) * N) * (|T2| * A / N) ^ 2 * L ^ (-E)) := by
        gcongr
    _ = 2 * K' * (((q : ℝ) * N) ^ (1 / 2 : ℝ) * (|T2| * A / N) * L ^ (-B - c0)) := by
        have hqN : (0 : ℝ) ≤ (q : ℝ) * N := by positivity
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_mul (by norm_num), Real.sqrt_sq hW,
          show Real.sqrt 4 = 2 by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
          Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hL0.le]
        have : L ^ c7 * L ^ (-E * (1 / 2)) = L ^ (-B - c0) := by
          rw [← Real.rpow_add hL0]; congr 1; rw [hEdef]; ring
        calc K' * L ^ c7 * (2 * ((q : ℝ) * N) ^ (1 / 2 : ℝ) * (|T2| * A / N) *
              L ^ (-E * (1 / 2)))
            = 2 * K' * (((q : ℝ) * N) ^ (1 / 2 : ℝ) * (|T2| * A / N) *
              (L ^ c7 * L ^ (-E * (1 / 2)))) := by ring
          _ = _ := by rw [this]

/-- The LEAF `prop3_312_leaf` of SPLIT_eq312_1122d.lean, wired through the split. -/
theorem prop3_312_split_S9 : Prop3_312 := prop3_312_of_leaves_S9

end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.prop3_312_arith_S9
#print axioms LeanLab.Zhan1991.T0cut_ge_H_S9
#print axioms LeanLab.Zhan1991.eq312_rhs_S9
#print axioms LeanLab.Zhan1991.prop3_312_of_leaves_S9
