/-
P0068 Zhan 1991, Proposition 3 of pages 267 and 268, display (3.16), split into two cited LEAFs.
Burst 20261124, session S9, unit S9-05. Source: papers/P0068.pdf, journal page 268, pdf page 10,
read from the page image rendered at 130 dpi. AI-written Lean code, Claude. Checked only by the
Lean kernel. Binary Goldbach is OPEN.

Page 268, proof of Proposition 3: with `F_i = Π_{j ∈ J_i} f_j`, Cauchy's inequality gives
`Σ_χ ∫ |F| ≤ (Σ_χ ∫ |F₁|²)^{1/2} (Σ_χ ∫ |F₂|²)^{1/2}`; Lemma 6 and (3.13) give
`Σ_χ ∫ |F_i|² ≪ (qH + M_i) L^{c₀}`; then
`(qH + M₁)^{1/2} (qH + M₂)^{1/2} L^{c₀} ≪ (qH + (qHAL^{-c₆})^{1/2} + N^{1/2}) L^{c₀} ≪ (qN)^{1/2} L^{-B-c₀}`
if `c₁, c₂, c₆` are large. The two analytic steps are LEAFs; the last chain is PROVED below.
-/
import LeanLab.Zhan1991.SPLIT_eq311_1122d

namespace LeanLab.Zhan1991
open Finset Real

noncomputable section

/-- `F_i(s, χ) = Π_{j ∈ J_i} f_j(s, χ)`, page 268 of the proof of Proposition 3; `Nv j` is
`N_{j+1}` as in `Fprod`. -/
def FJ311 {q : ℕ} (Nv : Fin 20 → ℝ) (J : Finset (Fin 20)) (χ : DirichletCharacter ℂ q)
    (s : ℂ) : ℂ :=
  ∏ j ∈ J, fj (j.val + 1) (Nv j) χ s

/-- LEAF: page 268, first inequality of the proof of Proposition 3: Cauchy's inequality over
`χ ≠ χ₀` and `t ∈ (T₁, T₁ + H]` with `F = F₁ F₂`, `F₁ = Π_{J₁} f_j`, `F₂ = Π_{J \ J₁} f_j`.
Class EASY. -/
theorem cauchy_311_leaf_S9 (Nv : Fin 20 → ℝ) (q : ℕ) [NeZero q] (J1 : Finset (Fin 20))
    (T1 H : ℝ) :
    ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
        ∫ t in Set.Ioc T1 (T1 + H), ‖Fprod Nv χ (1 / 2 + t * Complex.I)‖
      ≤ Real.sqrt (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.Ioc T1 (T1 + H), ‖FJ311 Nv J1 χ (1 / 2 + t * Complex.I)‖ ^ 2) *
        Real.sqrt (∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.Ioc T1 (T1 + H), ‖FJ311 Nv J1ᶜ χ (1 / 2 + t * Complex.I)‖ ^ 2) := by
  sorry

/-- LEAF: page 268, second and third lines of the proof of Proposition 3: Lemma 6 with
`T = H ≥ 1` applied to the Dirichlet polynomial `F_i = Σ_{n ≤ M_i} b_i(n) χ(n) n^{-s}`,
`b_i(n) ≪ d₂₀(n) L`, and the divisor moment bounds (3.13) give
`Σ_{χ≠χ₀} ∫_{T₁}^{T₁+H} |F_i(1/2+it, χ)|² dt ≪ (qH + M_i) L^{c₀}` with `M_i = Π_{j ∈ J_i} N_j`.
The exponent `c₀` of the paper is named `c7` here, since `c0` is already the free exponent of
(3.11). Class HARD. -/
theorem mv_FJ_311_leaf_S9 : ∃ c7 : ℝ, 0 ≤ c7 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (q : ℕ) [NeZero q] (Nv : Fin 20 → ℝ) (J : Finset (Fin 20)) (T1 H : ℝ),
      N₀ ≤ N → Cond35 N Nv → 1 ≤ H →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.Ioc T1 (T1 + H), ‖FJ311 Nv J χ (1 / 2 + t * Complex.I)‖ ^ 2
        ≤ K * ((q : ℝ) * H + ∏ j ∈ J, Nv j) * Real.log N ^ c7 := by
  sorry

/-- PROVED, page 268, last two lines of the proof of Proposition 3: with `a = qH = qN/A`,
`M₁, M₂ ≤ A L^{-c₆}` and `M₁ M₂ ≤ N`,
`(a + M₁)(a + M₂) ≤ 4 q N L^{-E}` once `c₁, c₂, c₆ ≥ E`. -/
theorem prop3_arith_S9 {N : ℕ} {A q L E c1 c2 c6 M1 M2 : ℝ} (hL : 1 ≤ L) (hA : 0 < A)
    (hN : 0 < (N : ℝ)) (hq0 : 0 < q) (hc1 : E ≤ c1) (hc2 : E ≤ c2) (hc6 : E ≤ c6)
    (hq1 : L ^ c2 ≤ q) (hq2 : q ≤ A ^ 2 / N * L ^ (-c1))
    (hM1 : 0 ≤ M1) (hM2 : 0 ≤ M2) (hM1A : M1 ≤ A * L ^ (-c6)) (hM2A : M2 ≤ A * L ^ (-c6))
    (hMM : M1 * M2 ≤ N) :
    (q * (N / A) + M1) * (q * (N / A) + M2) ≤ 4 * (q * N) * L ^ (-E) := by
  have hL0 : 0 < L := by linarith
  have e1 : L ^ (-c1) ≤ L ^ (-E) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have e6 : L ^ (-c6) ≤ L ^ (-E) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have e2 : L ^ (-E) * L ^ c2 ≥ 1 := by
    rw [← Real.rpow_add hL0]
    exact Real.one_le_rpow hL (by linarith)
  have hE0 : 0 < L ^ (-E) := Real.rpow_pos_of_pos hL0 _
  -- a² ≤ qN L^{-E}
  have t1 : (q * (N / A)) * (q * (N / A)) ≤ (q * N) * L ^ (-E) := by
    have : q * N / A ^ 2 ≤ L ^ (-E) := by
      rw [div_le_iff₀ (by positivity)]
      have h := mul_le_mul_of_nonneg_right hq2 hN.le
      have h' : A ^ 2 / N * L ^ (-c1) * N = A ^ 2 * L ^ (-c1) := by field_simp
      rw [h'] at h
      calc q * N ≤ A ^ 2 * L ^ (-c1) := h
        _ ≤ A ^ 2 * L ^ (-E) := mul_le_mul_of_nonneg_left e1 (by positivity)
        _ = L ^ (-E) * A ^ 2 := by ring
    calc (q * (N / A)) * (q * (N / A)) = (q * N) * (q * N / A ^ 2) := by field_simp
      _ ≤ (q * N) * L ^ (-E) := mul_le_mul_of_nonneg_left this (by positivity)
  have tM : ∀ M : ℝ, 0 ≤ M → M ≤ A * L ^ (-c6) → q * (N / A) * M ≤ (q * N) * L ^ (-E) := by
    intro M hM hMA
    calc q * (N / A) * M ≤ q * (N / A) * (A * L ^ (-c6)) :=
          mul_le_mul_of_nonneg_left hMA (by positivity)
      _ = (q * N) * L ^ (-c6) := by field_simp
      _ ≤ (q * N) * L ^ (-E) := mul_le_mul_of_nonneg_left e6 (by positivity)
  have t3 : M1 * M2 ≤ (q * N) * L ^ (-E) := by
    calc M1 * M2 ≤ N := hMM
      _ ≤ N * (L ^ (-E) * L ^ c2) := le_mul_of_one_le_right hN.le e2
      _ ≤ N * (L ^ (-E) * q) := by gcongr
      _ = (q * N) * L ^ (-E) := by ring
  have := tM M1 hM1 hM1A
  have := tM M2 hM2 hM2A
  nlinarith

/-- PROVED from the two LEAFs: Proposition 3 of page 268, `Prop3_311_1122d`. Constants:
`E = 2 (B + c₀ + c₇)`, `c₆, c₁, c₂ ≥ E`, `c₃ = 1`, `K = 2 max(K₆, 0)`, `N₀ = max(N₀', 3)`. -/
theorem prop3_311_of_leaves_S9 : Prop3_311_1122d := by
  intro B _ c0 _
  obtain ⟨c7, hc7, KB, N0B, hMV⟩ := mv_FJ_311_leaf_S9
  set E : ℝ := 2 * (B + c0 + c7) with hEdef
  refine ⟨E, fun c6 hc6 => ⟨E, fun c1 hc1 => ⟨E, fun c2 hc2 => ⟨1, one_pos,
    2 * max KB 0, max N0B 3, ?_⟩⟩⟩⟩
  intro N A lam q _ Nv T1 hN0 hH hC hT1 J1 hJ1 hJ2
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
  have hpos : ∀ J : Finset (Fin 20), 0 ≤ ∏ j ∈ J, Nv j :=
    fun J => Finset.prod_nonneg (fun j _ => le_trans (by norm_num) (hC.1 j))
  have hMM : (∏ j ∈ J1, Nv j) * ∏ j ∈ J1ᶜ, Nv j ≤ N := by
    rw [Finset.prod_mul_prod_compl]; exact hC.2.2.1
  have h1 := hMV N q Nv J1 T1 (N / A) hNB hC hHge
  have h2 := hMV N q Nv J1ᶜ T1 (N / A) hNB hC hHge
  have hcs := cauchy_311_leaf_S9 Nv q J1 T1 (N / A)
  set K' := max KB 0 with hK'
  have hK'0 : 0 ≤ K' := le_max_right _ _
  set M1 := ∏ j ∈ J1, Nv j
  set M2 := ∏ j ∈ J1ᶜ, Nv j
  have hLc7 : 0 ≤ L ^ c7 := (Real.rpow_pos_of_pos hL0 _).le
  have b1 : KB * ((q : ℝ) * (N / A) + M1) * L ^ c7 ≤ K' * ((q : ℝ) * (N / A) + M1) * L ^ c7 := by
    gcongr
    · have := hpos J1; positivity
    · exact le_max_left _ _
  have b2 : KB * ((q : ℝ) * (N / A) + M2) * L ^ c7 ≤ K' * ((q : ℝ) * (N / A) + M2) * L ^ c7 := by
    gcongr
    · have := hpos J1ᶜ; positivity
    · exact le_max_left _ _
  have har := prop3_arith_S9 (N := N) (q := (q : ℝ)) (L := L) (E := E) hL hA hNpos hq0
    hc1 hc2 hc6 hq1 hq3 (hpos J1) (hpos J1ᶜ) hJ1 hJ2 hMM
  have hX1 : 0 ≤ (q : ℝ) * (N / A) + M1 := by have := hpos J1; positivity
  have hX2 : 0 ≤ (q : ℝ) * (N / A) + M2 := by have := hpos J1ᶜ; positivity
  refine le_trans hcs ?_
  calc _ ≤ Real.sqrt (K' * ((q : ℝ) * (N / A) + M1) * L ^ c7) *
        Real.sqrt (K' * ((q : ℝ) * (N / A) + M2) * L ^ c7) := by
        gcongr
        · exact le_trans h1 b1
        · exact le_trans h2 b2
    _ = Real.sqrt ((K' * L ^ c7) ^ 2 *
          (((q : ℝ) * (N / A) + M1) * ((q : ℝ) * (N / A) + M2))) := by
        rw [← Real.sqrt_mul (by positivity)]
        congr 1; ring
    _ = K' * L ^ c7 * Real.sqrt (((q : ℝ) * (N / A) + M1) * ((q : ℝ) * (N / A) + M2)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
    _ ≤ K' * L ^ c7 * Real.sqrt (4 * ((q : ℝ) * N) * L ^ (-E)) := by
        gcongr
    _ = 2 * K' * ((q : ℝ) * N) ^ (1 / 2 : ℝ) * L ^ (-B - c0) := by
        have hqN : (0 : ℝ) ≤ (q : ℝ) * N := by positivity
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul (by norm_num),
          show Real.sqrt 4 = 2 by
            rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)],
          Real.sqrt_eq_rpow, Real.sqrt_eq_rpow, ← Real.rpow_mul hL0.le]
        have : L ^ c7 * L ^ (-E * (1 / 2)) = L ^ (-B - c0) := by
          rw [← Real.rpow_add hL0]; congr 1; rw [hEdef]; ring
        calc K' * L ^ c7 * (2 * ((q : ℝ) * N) ^ (1 / 2 : ℝ) * L ^ (-E * (1 / 2)))
            = 2 * K' * ((q : ℝ) * N) ^ (1 / 2 : ℝ) * (L ^ c7 * L ^ (-E * (1 / 2))) := by ring
          _ = _ := by rw [this]

/-- The LEAF `prop3_311_leaf_1122d` of SPLIT_eq311_1122d.lean, wired through the split. -/
theorem prop3_311_split_S9 : Prop3_311_1122d := prop3_311_of_leaves_S9

end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.prop3_arith_S9
#print axioms LeanLab.Zhan1991.prop3_311_of_leaves_S9
