/-
P0068 Zhan 1991, Proposition 1 of pages 266 and 267, split into one new cited LEAF plus the two
LEAFs of SPLIT_prop3_311_S9.lean. Burst 20261124, session S9, unit S9-03. Source:
papers/P0068.pdf, journal pages 266 and 267, pdf pages 8 and 9, read from the page images
rendered at 130 dpi. AI-written Lean code, Claude. Checked only by the Lean kernel.
Binary Goldbach is OPEN.

Page 266: by (3.5), `1 ≤ j₀ ≤ 10`; Perron's formula for `f₁`, the line shift with Lemma 7 and
Lemma 2 give `Σ_{χ≠χ₀} ∫_{T₁}^{T₁+H} |f₁(1/2+it, χ)|² dt ≪ L⁵ q H`. Page 266 bottom and page 267
top: Cauchy, Lemma 6 and (3.13) give
`Σ_χ ∫ |F| ≤ (Σ ∫ |f₁|²)^{1/2} (Σ ∫ |Π_{j≥2} f_j|²)^{1/2} ≪ (qH)^{1/2} (qH + N N₁⁻¹)^{1/2} L^{c₀}
≪ (qN)^{1/2} L^{-B-c₀}` if `N₁ ≥ N A⁻¹ L^{c₅}` and `c₁, c₅` are large. The `f₁` bound is the new
LEAF; Cauchy and Lemma 6 with (3.13) are the LEAFs of Proposition 3; the rest is PROVED.
-/
import LeanLab.Zhan1991.SPLIT_prop3_311_S9

namespace LeanLab.Zhan1991
open Finset Real

noncomputable section

/-- LEAF: Proposition 1, page 266: for `j₀ ≤ 10` in the paper's numbering, here `j.val < 10`, and
`N_{j₀} ≥ N A⁻¹ L^{c₅}`, Perron's formula for `f_{j₀}` with `c = 1/2 + L⁻¹` for `|t| ≤ 3T₀`, the
shift of the integral to the line `Re w = 0` with Lemma 7, Cauchy in `v` and Lemma 2 give
`Σ_{χ≠χ₀} ∫_{T₁}^{T₁+H} |f_{j₀}(1/2+it, χ)|² dt ≪ L⁵ q H`, `H = N A⁻¹`. The paper writes the
case `j₀ = 1`, coefficient `log n`; for `2 ≤ j₀ ≤ 10` the coefficient is `1` and `L'` is read as
`L`, which the paper's "without loss of generality" covers. Class HARD. -/
theorem f_j0_moment_311_leaf_S9 : ∃ c5m : ℝ, 0 < c5m ∧ ∀ c5 ≥ c5m, ∃ c1m : ℝ, ∀ c1 ≥ c1m,
    ∃ c2m : ℝ, ∀ c2 ≥ c2m, ∃ c3 : ℝ, 0 < c3 ∧ ∃ K N₀ : ℝ,
    ∀ (N : ℕ) (A lam : ℝ) (q : ℕ) [NeZero q] (Nv : Fin 20 → ℝ) (T1 : ℝ) (j : Fin 20),
      N₀ ≤ N → Hyp2 c1 c2 c3 N A lam q → Cond35 N Nv → |T1| ≤ 2 * T0cut N A lam →
      j.val < 10 → (N : ℝ) / A * Real.log N ^ c5 ≤ Nv j →
      ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)).filter (· ≠ 1),
          ∫ t in Set.Ioc T1 (T1 + N / A), ‖fj (j.val + 1) (Nv j) χ (1 / 2 + t * Complex.I)‖ ^ 2
        ≤ K * Real.log N ^ (5 : ℝ) * q * (N / A) := by
  sorry

/-- PROVED, page 266: by (3.5), an `N_{j₀} ≥ N A⁻¹ L^{c₅}` has `j₀ ≤ 10`, since
`N_j ≤ N^{1/10}` for `j > 10` while `N A⁻¹ ≥ N^{1/3}` for `A ≤ N^{2/3}`. -/
theorem j0_le_ten_S9 {N : ℕ} {A c5 : ℝ} {Nv : Fin 20 → ℝ} {j : Fin 20} (hN : 1 < (N : ℝ))
    (hA : 0 < A) (hA2 : A ≤ (N : ℝ) ^ (2 / 3 : ℝ)) (hc5 : 1 ≤ Real.log N ^ c5)
    (hC : Cond35 N Nv) (hj : (N : ℝ) / A * Real.log N ^ c5 ≤ Nv j) : j.val < 10 := by
  by_contra h
  push Not at h
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

/-- PROVED, page 267 top: with `a = qH = qN/A` and `M ≤ A L^{-c₅}`,
`a (a + M) ≤ 2 q N L^{-E}` once `c₁, c₅ ≥ E`. -/
theorem prop1_arith_S9 {N : ℕ} {A q L E c1 c5 M : ℝ} (hL : 1 ≤ L) (hA : 0 < A)
    (hN : 0 < (N : ℝ)) (hq0 : 0 < q) (hc1 : E ≤ c1) (hc5 : E ≤ c5)
    (hq2 : q ≤ A ^ 2 / N * L ^ (-c1)) (hM : 0 ≤ M) (hMA : M ≤ A * L ^ (-c5)) :
    (q * (N / A)) * (q * (N / A) + M) ≤ 2 * (q * N) * L ^ (-E) := by
  have e1 : L ^ (-c1) ≤ L ^ (-E) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
  have e5 : L ^ (-c5) ≤ L ^ (-E) := Real.rpow_le_rpow_of_exponent_le hL (by linarith)
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
  have t2 : q * (N / A) * M ≤ (q * N) * L ^ (-E) := by
    calc q * (N / A) * M ≤ q * (N / A) * (A * L ^ (-c5)) :=
          mul_le_mul_of_nonneg_left hMA (by positivity)
      _ = (q * N) * L ^ (-c5) := by field_simp
      _ ≤ (q * N) * L ^ (-E) := mul_le_mul_of_nonneg_left e5 (by positivity)
  nlinarith

/-- PROVED from the LEAFs `f_j0_moment_311_leaf_S9`, `cauchy_311_leaf_S9` and
`mv_FJ_311_leaf_S9`: Proposition 1 of pages 266 and 267, `Prop1_311_1122d`. Constants:
`E = 2 (B + c₀) + 5 + c₇`, `c₅ = max(c₅', E)`, `c₁ ≥ max(c₁', E)`, the rest from the `f_{j₀}` LEAF,
`K = (2 max(K₁, 0) max(K₆, 0))^{1/2}`. -/
theorem prop1_311_of_leaves_S9 : Prop1_311_1122d := by
  intro B _ c0 _
  obtain ⟨c7, hc7, KB, N0B, hMV⟩ := mv_FJ_311_leaf_S9
  obtain ⟨c5m, hc5m, hF⟩ := f_j0_moment_311_leaf_S9
  set E : ℝ := 2 * (B + c0) + 5 + c7 with hEdef
  set c5 := max c5m E with hc5def
  have hc5pos : 0 < c5 := lt_of_lt_of_le hc5m (le_max_left _ _)
  obtain ⟨c1m', hF1⟩ := hF c5 (le_max_left _ _)
  refine ⟨c5, hc5pos, max c1m' E, fun c1 hc1 => ?_⟩
  obtain ⟨c2m', hF2⟩ := hF1 c1 (le_trans (le_max_left _ _) hc1)
  refine ⟨c2m', fun c2 hc2 => ?_⟩
  obtain ⟨c3, hc3, KC, N0C, hFC⟩ := hF2 c2 hc2
  refine ⟨c3, hc3, Real.sqrt (2 * max KC 0 * max KB 0), max (max N0B N0C) 3, ?_⟩
  intro N A lam q _ Nv T1 hN0 hH hC hT1 hj
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
  have hLc5 : 1 ≤ L ^ c5 := Real.one_le_rpow hL hc5pos.le
  have hj10 : j.val < 10 := j0_le_ten_S9 (by linarith) hA hA2 hLc5 hC hj
  have hfC := hFC N A lam q Nv T1 j hNC hH hC hT1 hj10 hj
  have hmv := hMV N q Nv {j}ᶜ T1 (N / A) hNB hC hHge
  have hcs := cauchy_311_leaf_S9 Nv q {j} T1 (N / A)
  have hsing : ∀ χ : DirichletCharacter ℂ q, ∀ t : ℝ,
      FJ311 Nv {j} χ (1 / 2 + t * Complex.I) = fj (j.val + 1) (Nv j) χ (1 / 2 + t * Complex.I) := by
    intro χ t; simp [FJ311]
  simp only [hsing] at hcs
  -- the bound on the complementary product
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
  have har := prop1_arith_S9 (N := N) (q := (q : ℝ)) (L := L) (E := E) hL hA hNpos hq0
    (le_trans (le_max_right _ _) hc1) (le_max_right _ _) hq3 hM0 hMA
  set KC' := max KC 0
  set KB' := max KB 0
  have hKC : 0 ≤ KC' := le_max_right _ _
  have hKB : 0 ≤ KB' := le_max_right _ _
  have hX : 0 ≤ (q : ℝ) * (N / A) + M := by positivity
  have hL5 : 0 ≤ L ^ (5 : ℝ) := by positivity
  have hLc7 : 0 ≤ L ^ c7 := by positivity
  have b1 : KC * L ^ (5 : ℝ) * q * (N / A) ≤ KC' * L ^ (5 : ℝ) * q * (N / A) := by
    gcongr; exact le_max_left _ _
  have b2 : KB * ((q : ℝ) * (N / A) + M) * L ^ c7 ≤ KB' * ((q : ℝ) * (N / A) + M) * L ^ c7 := by
    gcongr; exact le_max_left _ _
  refine le_trans hcs ?_
  calc _ ≤ Real.sqrt (KC' * L ^ (5 : ℝ) * q * (N / A)) *
        Real.sqrt (KB' * ((q : ℝ) * (N / A) + M) * L ^ c7) := by
        gcongr
        · exact le_trans hfC b1
        · exact le_trans hmv b2
    _ = Real.sqrt ((KC' * KB' * (L ^ (5 : ℝ) * L ^ c7)) *
          (((q : ℝ) * (N / A)) * ((q : ℝ) * (N / A) + M))) := by
        rw [← Real.sqrt_mul (by positivity)]
        congr 1; ring
    _ ≤ Real.sqrt ((KC' * KB' * (L ^ (5 : ℝ) * L ^ c7)) * (2 * ((q : ℝ) * N) * L ^ (-E))) := by
        gcongr
    _ = Real.sqrt (2 * KC' * KB') * ((q : ℝ) * N) ^ (1 / 2 : ℝ) * L ^ (-B - c0) := by
        have hqN : (0 : ℝ) ≤ (q : ℝ) * N := by positivity
        have hpow : L ^ (5 : ℝ) * L ^ c7 * L ^ (-E) = (L ^ (-B - c0)) ^ 2 := by
          rw [← Real.rpow_add hL0, ← Real.rpow_add hL0, ← Real.rpow_natCast,
            ← Real.rpow_mul hL0.le]
          congr 1; rw [hEdef]; push_cast; ring
        have : (KC' * KB' * (L ^ (5 : ℝ) * L ^ c7)) * (2 * ((q : ℝ) * N) * L ^ (-E))
            = (2 * KC' * KB') * ((q : ℝ) * N) * (L ^ (-B - c0)) ^ 2 := by
          rw [← hpow]; ring
        rw [this, Real.sqrt_mul (by positivity), Real.sqrt_mul (by positivity),
          Real.sqrt_sq (by positivity), Real.sqrt_eq_rpow ((q : ℝ) * N)]

/-- The LEAF `prop1_311_leaf_1122d` of SPLIT_eq311_1122d.lean, wired through the split. -/
theorem prop1_311_split_S9 : Prop1_311_1122d := prop1_311_of_leaves_S9

end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.j0_le_ten_S9
#print axioms LeanLab.Zhan1991.prop1_arith_S9
#print axioms LeanLab.Zhan1991.prop1_311_of_leaves_S9
