/-
P0068 Zhan 1991, page 263 display (3.3): `perron_sum_leaf_pt` of PerronTrunc1122d.lean with a
sorry free proof, `perron_sum_proof_A2`. Burst 20261124, session S9, unit A-extra-5. The proof of
`perron_sum_leaf_pt` in PerronTrunc1122d.lean is repeated verbatim with the three LEAFs of
PerronSum1122d.lean replaced by their PROVED twins `perron_coef_proof_A2`,
`perron_fiber_proof_A2` and `perron_harmonic_proof_A2`.
AI-written Lean code, Claude. Checked only by the Lean kernel. Binary Goldbach is OPEN.
-/
import LeanLab.Zhan1991.PerronTrunc1122d
import LeanLab.Zhan1991.PerronCoefProof_A2
import LeanLab.Zhan1991.PerronFiberProof_A2
import LeanLab.Zhan1991.HarmonicProof_A2

namespace LeanLab.Zhan1991
open Finset Real
open scoped ArithmeticFunction.vonMangoldt ArithmeticFunction.Moebius

noncomputable section

/-- The same statement as `perron_sum_leaf_pt`, page 263 display (3.3), PROVED from the proved
coefficient, divisor and harmonic bounds. -/
theorem perron_sum_proof_A2 : ∀ ε : ℝ, 0 < ε → ∃ K N₀ : ℝ, 0 < K ∧ ∀ (N : ℕ) (A T u : ℝ)
    (q : ℕ) (χ : DirichletCharacter ℂ q) (Nv : Fin 20 → ℝ), N₀ ≤ N → 0 ≤ A →
    A ≤ (N : ℝ) ^ (2 / 3 : ℝ) → Cond35 N Nv → 2 ≤ T → T ≤ N → (N : ℝ) - A ≤ u → u ≤ N →
    ∑ n ∈ Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)),
      ‖coef_pt χ n‖ * (Bterm_pt (1 + 1 / Real.log N) T (u / Pn_pt n) +
        Bterm_pt (1 + 1 / Real.log N) T (((N : ℝ) - A) / Pn_pt n))
      ≤ K * (N : ℝ) ^ (1 + ε) / T := by
  intro ε hε
  obtain ⟨KA, NA, hKA, hA⟩ := perron_coef_proof_A2 (ε / 3) (by positivity)
  obtain ⟨KB, NB, hKB, hB⟩ := perron_fiber_proof_A2 (ε / 3) (by positivity)
  obtain ⟨KC, NC, hKC, hC⟩ := perron_harmonic_proof_A2 (ε / 3) (by positivity)
  refine ⟨2 * KA * KB * KC, max (max NA NB) (max NC 2), by positivity, ?_⟩
  intro N A T u q χ Nv hN hA0 hA2 hC35 hT2 hTN hu1 hu2
  have hNA' : NA ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hN
  have hNB' : NB ≤ (N : ℝ) := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hN
  have hNC' : NC ≤ (N : ℝ) := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hN
  have hN2 : (2 : ℝ) ≤ N := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hNA : 0 < (N : ℝ) - A := by
    have : (N : ℝ) ^ (2 / 3 : ℝ) < (N : ℝ) ^ (1 : ℝ) :=
      Real.rpow_lt_rpow_of_exponent_lt (by linarith) (by norm_num)
    rw [Real.rpow_one] at this
    linarith
  have hT0 : 0 < T := by linarith
  set c : ℝ := 1 + 1 / Real.log N with hcdef
  have hc : 0 < c := by
    have : 0 ≤ 1 / Real.log N := by
      apply div_nonneg zero_le_one; exact Real.log_natCast_nonneg N
    linarith
  have hBnn : ∀ y : ℝ, 0 < y → 0 ≤ Bterm_pt c T y := by
    intro y hy
    unfold Bterm_pt
    split_ifs
    · positivity
    · have : 0 ≤ min 1 (1 / (T * |Real.log y|)) := le_min zero_le_one (by positivity)
      have := Real.rpow_nonneg hy.le c; positivity
  set box := Fintype.piFinset (fun j : Fin 20 => dyad (Nv j)) with hbox
  have hPn : ∀ n : Fin 20 → ℕ, Pn_pt n = ((∏ j, n j : ℕ) : ℝ) := by
    intro n; unfold Pn_pt; push_cast; rfl
  have hmaps : ∀ n ∈ box, (∏ j, n j) ∈ Finset.Icc (1 : ℕ) (2 ^ 20 * N) := by
    intro n hn
    have hmem : ∀ j, 1 ≤ n j ∧ (n j : ℝ) ≤ 2 * Nv j := by
      intro j
      have h := Fintype.mem_piFinset.mp hn j
      unfold dyad at h
      have h1 := Finset.mem_Icc.mp (Finset.mem_filter.mp h).1
      refine ⟨h1.1, ?_⟩
      have h2 : (n j : ℝ) ≤ (⌊2 * Nv j⌋₊ : ℝ) := by exact_mod_cast h1.2
      have h3 : (⌊2 * Nv j⌋₊ : ℝ) ≤ 2 * Nv j := Nat.floor_le (by linarith [hC35.1 j])
      linarith
    rw [Finset.mem_Icc]
    constructor
    · exact Finset.one_le_prod (fun j _ => (hmem j).1)
    · have hr : ((∏ j, n j : ℕ) : ℝ) ≤ ((2 ^ 20 * N : ℕ) : ℝ) := by
        rw [Nat.cast_prod, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        calc (∏ j, (n j : ℝ)) ≤ ∏ j, (2 * Nv j) :=
              Finset.prod_le_prod₀ (fun j _ => Nat.cast_nonneg _) (fun j _ => (hmem j).2)
          _ = 2 ^ 20 * ∏ j, Nv j := by rw [Finset.prod_mul_distrib]; simp
          _ ≤ 2 ^ 20 * (N : ℝ) := by linarith [hC35.2.2.1]
      exact_mod_cast hr
  have hkey : ∀ v : ℝ, 0 < v → v ≤ N → ∑ n ∈ box, Bterm_pt c T (v / Pn_pt n) ≤
      KB * (N : ℝ) ^ (ε / 3) * (KC * (N : ℝ) ^ (1 + ε / 3) / T) := by
    intro v hv0 hvN
    rw [← Finset.sum_fiberwise_of_maps_to hmaps]
    calc ∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ 20 * N), ∑ n ∈ box.filter (fun n => ∏ j, n j = m),
          Bterm_pt c T (v / Pn_pt n)
        = ∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ 20 * N),
            ((box.filter (fun n => ∏ j, n j = m)).card : ℝ) * Bterm_pt c T (v / (m : ℝ)) := by
          apply Finset.sum_congr rfl
          intro m _
          rw [Finset.sum_congr rfl (g := fun _ => Bterm_pt c T (v / (m : ℝ)))]
          · simp [Finset.sum_const, nsmul_eq_mul]
          · intro n hn
            rw [hPn n, (Finset.mem_filter.mp hn).2]
      _ ≤ ∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ 20 * N),
            (KB * (N : ℝ) ^ (ε / 3)) * Bterm_pt c T (v / (m : ℝ)) := by
          apply Finset.sum_le_sum
          intro m hm
          have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (Finset.mem_Icc.mp hm).1
          exact mul_le_mul_of_nonneg_right (hB N Nv m hNB' (Finset.mem_Icc.mp hm).2)
            (hBnn _ (div_pos hv0 (by linarith)))
      _ = KB * (N : ℝ) ^ (ε / 3) * ∑ m ∈ Finset.Icc (1 : ℕ) (2 ^ 20 * N),
            Bterm_pt c T (v / (m : ℝ)) := by rw [Finset.mul_sum]
      _ ≤ KB * (N : ℝ) ^ (ε / 3) * (KC * (N : ℝ) ^ (1 + ε / 3) / T) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have := hC N T v hNC' hT2 hTN hv0 hvN
          simpa only [Bterm_pt] using this
  have hcoef : ∀ n ∈ box, ‖coef_pt χ n‖ ≤ KA * (N : ℝ) ^ (ε / 3) := by
    intro n hn
    exact hA N q χ Nv n hNA' hC35 hn
  have hS1 := hkey u (lt_of_lt_of_le hNA hu1) hu2
  have hS2 := hkey ((N : ℝ) - A) hNA (by linarith)
  have hP : ∀ n ∈ box, 0 < Pn_pt n := fun n hn => Pn_pos_pt hn
  calc ∑ n ∈ box, ‖coef_pt χ n‖ * (Bterm_pt c T (u / Pn_pt n) +
          Bterm_pt c T (((N : ℝ) - A) / Pn_pt n))
      ≤ ∑ n ∈ box, (KA * (N : ℝ) ^ (ε / 3)) * (Bterm_pt c T (u / Pn_pt n) +
          Bterm_pt c T (((N : ℝ) - A) / Pn_pt n)) := by
        apply Finset.sum_le_sum
        intro n hn
        exact mul_le_mul_of_nonneg_right (hcoef n hn)
          (add_nonneg (hBnn _ (div_pos (lt_of_lt_of_le hNA hu1) (hP n hn)))
            (hBnn _ (div_pos hNA (hP n hn))))
    _ = KA * (N : ℝ) ^ (ε / 3) * (∑ n ∈ box, Bterm_pt c T (u / Pn_pt n) +
          ∑ n ∈ box, Bterm_pt c T (((N : ℝ) - A) / Pn_pt n)) := by
        rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ KA * (N : ℝ) ^ (ε / 3) * (2 * (KB * (N : ℝ) ^ (ε / 3) *
          (KC * (N : ℝ) ^ (1 + ε / 3) / T))) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        linarith
    _ = 2 * KA * KB * KC * (N : ℝ) ^ (1 + ε) / T := by
        have e : (N : ℝ) ^ (ε / 3) * ((N : ℝ) ^ (ε / 3) * (N : ℝ) ^ (1 + ε / 3)) =
            (N : ℝ) ^ (1 + ε) := by
          rw [← Real.rpow_add hNpos, ← Real.rpow_add hNpos]; congr 1; ring
        rw [← e]
        field_simp

end

end LeanLab.Zhan1991

#print axioms LeanLab.Zhan1991.perron_sum_proof_A2
