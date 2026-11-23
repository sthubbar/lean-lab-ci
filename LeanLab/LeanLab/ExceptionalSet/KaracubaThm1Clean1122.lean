/-
Clean wiring of `KaracubaThm1Named`, burst-20261122 S24, unit P1122-0112.

`KaracubaThm1Named` of DQLemma10Decisions is Theorem 1 of A. A. Karacuba, Trudy Mat. Inst.
Steklov 112 (1971) 241-255, p. 244, proved p. 245-248, lab copy
`papers/Karacuba1971-TrudyMIAN112.pdf`. This file derives it from Karacuba's two cited inputs
only: Lemma 1, p. 243, Vinogradov's mean value theorem, `KarLemma1`, and Lemma 2, p. 243-244,
Vinogradov's Weyl sum estimate, `KarLemma2`. Every theorem here prints only propext,
Classical.choice and Quot.sound: CONDITIONAL ON `KarLemma1` and `KarLemma2`, nothing admitted.

Route.
* Case `n ≥ n0`, p. 245-248: `taylor_sum_bound_clean1122` is the assembly proof of
  `leaf_karW_taylor_sum_bound_split`, SPLIT_leaf_karW_taylor_sum_bound, verbatim, with its one
  LEAF `leaf_karW_display8` replaced by the PROVED `leaf_karW_display8_split` of
  SPLIT_leaf_karW_display8. `W_bound_clean1122` is the assembly proof of `leaf_W_bound_split`,
  SPLIT_leaf_W_bound, verbatim, with its LEAF `leaf_karW_taylor_sum_bound` replaced by
  `taylor_sum_bound_clean1122`. Then `largeCase_of_W` of KaracubaSplit.
* Case `2 ≤ n < n0`, p. 248: `leaf_small_case_repaired` of SmallCaseRepair1122, which avoids
  the leaves `leaf_small_block_sum_bound` and `leaf_polynomial_block_sum` found FALSE as stated
  in this burst.
* `karacubaTheorem1_of_cases` of KaracubaSplit joins the two cases, with the reduction to
  `P ≥ e^{c n²}` of p. 245 line 1.

The statements copied here are the existing ones, unchanged; only admitted inputs are replaced
by proved ones.

AI wrote the Lean code, Claude. Binary Goldbach is OPEN.
-/
import LeanLab.ExceptionalSet.DQLemma10Decisions
import LeanLab.ExceptionalSet.SPLIT_leaf_karW_display8
import LeanLab.ExceptionalSet.SmallCaseRepair1122

namespace LeanLab.ExceptionalSet.U1539.KaracubaSplit

open LeanLab.ExceptionalSet.U1539

/-- The statement of `leaf_karW_taylor_sum_bound`, Karacuba p. 245-248, PROVED from Lemmas 1, 3
and 4 through `leaf_karW_display8_split`; the proof is that of
`leaf_karW_taylor_sum_bound_split`. CONDITIONAL ON `KarLemma1`. -/
theorem taylor_sum_bound_clean1122 (h1 : KarLemma1) (h3 : KarLemma3) (h4 : KarLemma4) :
    ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 →
      c0 < 1 → c1 < 1 → c2 + c4 < c1 →
      ∃ B ρ cc : ℝ, 0 < B ∧ 0 < ρ ∧ ρ ≤ c1 / 3 ∧ ρ ≤ c3 ∧ ρ ≤ c4 ∧ 0 < cc ∧
        ∀ (N P n : ℕ) (f : ℝ → ℝ) (T : Finset ℕ) (a : ℕ), 0 < P → 2 ≤ n →
          karN0 c1 c2 c4 ≤ n → Real.exp (cc * (n : ℝ) ^ 2) ≤ P →
          KarHyp c0 c1 c2 c3 N P n f T → N ≤ a → a + karP2 c1 n P ^ 2 ≤ N + P →
          ‖∑ y ∈ Finset.range (karP2 c1 n P + 1), ∑ z ∈ Finset.range (karP2 c1 n P + 1),
            eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
              iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j))‖
          ≤ B * ((karP2 c1 n P : ℝ) + 1) ^ 2 *
            (P : ℝ) ^ (-(ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + (Real.log (8 / (ρ * c0 ^ 2))) ^ 2) ^ 2))) := by
  intro c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 hc241
  obtain ⟨C0, cc0, hC0, hcc0, h8⟩ :=
    leaf_karW_display8_split h1 h3 h4 c0 c1 c2 c3 c4 hc0 hc1 hc2 hc3 hc4 hc01 hc11 hc241
  set ρ := min (c1 / 3) (min c3 c4) with hρ
  have hρpos : 0 < ρ := lt_min (by positivity) (lt_min hc3 hc4)
  have hρ1 : ρ ≤ c1 / 3 := min_le_left _ _
  have hρ3 : ρ ≤ c3 := (min_le_right _ _).trans (min_le_left _ _)
  have hρ4 : ρ ≤ c4 := (min_le_right _ _).trans (min_le_right _ _)
  set L := Real.log (8 / (ρ * c0 ^ 2)) with hL
  have hρc : ρ * c0 ^ 2 < 1 := by
    have : c0 ^ 2 < 1 := by nlinarith
    have : ρ < 1 := by linarith
    nlinarith [sq_nonneg c0]
  have hL0 : 0 ≤ L := by
    rw [hL]; apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity)]; linarith
  set e0 : ℝ := ρ * c0 ^ 2 / (32 * (4 + L ^ 2) ^ 2) with he0
  have he0pos : 0 < e0 := by rw [he0]; positivity
  obtain ⟨C1, hC1, habs⟩ := karW_absorb_B1 (L + 1 / 2) (3 * e0) (by linarith) (by linarith)
  refine ⟨C0 * C1, ρ, max cc0 1, mul_pos hC0 hC1, hρpos, hρ1, hρ3, hρ4,
    lt_of_lt_of_le one_pos (le_max_right _ _), ?_⟩
  intro N P n f T a hP hn hn0 hbig hH ha haP
  have hn12r : (12 : ℝ) ≤ n := le_trans (le_max_left _ _) hn0
  have hn12 : 12 ≤ n := by exact_mod_cast hn12r
  have hHc := hH
  obtain ⟨_, _, hT, hcard, _⟩ := hHc
  set σ : ℝ := ∑ s ∈ T, (s : ℝ) with hσ
  have hσlo := karW_sum_T_lower hc0 hT hcard
  have hσup := karW_sum_T_upper hT
  rw [← hσ] at hσlo hσup
  have hnpos : (0 : ℝ) < n := by linarith
  have hσpos : 0 < σ := lt_of_lt_of_le (by positivity) hσlo
  have hnn : ((n * (n + 1) : ℕ) : ℝ) = (n : ℝ) * (n + 1) := by push_cast; ring
  have hxA : ρ * σ < ((n * (n + 1) : ℕ) : ℝ) := by
    rw [hnn]
    have : ρ * σ ≤ σ / 3 := by
      have : ρ ≤ 1 / 3 := by linarith
      nlinarith
    have : (0 : ℝ) < (n : ℝ) * (n + 1) := by positivity
    linarith
  have hq0 : (0 : ℝ) ≤ 1 - 1 / (n : ℝ) := by
    have : 1 / (n : ℝ) ≤ 1 := by rw [div_le_one hnpos]; linarith
    linarith
  have hq1 : 1 - 1 / (n : ℝ) < 1 := by
    have : 0 < 1 / (n : ℝ) := by positivity
    linarith
  obtain ⟨l, hl1, hlo, hhi⟩ := karW_choice_l (mul_pos hρpos hσpos) hxA hq0 hq1
  have hlL := karW_l_le hρpos hc0 hn hl1 hσlo hhi
  rw [← hL] at hlL
  obtain ⟨hk1, hk2, hk3⟩ := karW_k_bounds (l := l) hn12 hL0 hlL
  set k : ℕ := n * l + ⌊((n * (n + 1) : ℕ) : ℝ) / 4 + 1⌋₊ with hk
  have hkpos : (0 : ℝ) < k := lt_of_lt_of_le (by positivity) hk2
  have hexp := karW_exponent_compare (n := n) hρpos hc0 (by omega) hL0 hσlo hkpos hk3
  -- `P > 1`
  have hPbig : Real.exp (cc0 * (n : ℝ) ^ 2) ≤ P := by
    refine le_trans (Real.exp_le_exp.2 ?_) hbig
    exact mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
  have hP1 : (1 : ℝ) < P := by
    refine lt_of_lt_of_le ?_ hbig
    rw [← Real.exp_zero]; apply Real.exp_lt_exp.2
    have : (0 : ℝ) < max cc0 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
    positivity
  have hW := h8 N P n f T a l hP hn hn0 hPbig hH ha haP hl1 hlo hhi
  have hB1 := habs n l k (P : ℝ) hn12 hl1 hk1 hk2 (by linarith) hP1
  set Bk := ((30 * (k : ℝ) ^ 2) ^ n * (9 * (n : ℝ)) ^ n * (20 * (n : ℝ)) ^ (n * (n + 1) * l) *
      (Real.log (P : ℝ)) ^ n) ^ (1 / (4 * (k : ℝ) ^ 2)) with hBk
  have hBk0 : 0 ≤ Bk := by
    rw [hBk]; apply Real.rpow_nonneg
    have : 0 < Real.log (P : ℝ) := Real.log_pos hP1
    positivity
  have hPpos : (0 : ℝ) < P := by linarith
  set Mp := ((karP2 c1 n P : ℝ) + 1) ^ 2 with hMp
  have hMp0 : 0 ≤ Mp := by positivity
  -- combine the two powers of `P`
  have hpow : (P : ℝ) ^ (3 * e0 / (n : ℝ) ^ 2) * (P : ℝ) ^ (-(ρ * σ / (8 * (k : ℝ) ^ 2)))
      ≤ (P : ℝ) ^ (-(ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2))) := by
    rw [← Real.rpow_add hPpos]
    apply Real.rpow_le_rpow_of_exponent_le hP1.le
    have he : 3 * e0 / (n : ℝ) ^ 2 = 3 * (ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2)) := by
      rw [he0]; field_simp
    rw [he]; linarith
  calc ‖_‖ ≤ C0 * Bk * Mp * (P : ℝ) ^ (-(ρ * σ / (8 * (k : ℝ) ^ 2))) := hW
    _ ≤ C0 * (C1 * (P : ℝ) ^ (3 * e0 / (n : ℝ) ^ 2)) * Mp *
          (P : ℝ) ^ (-(ρ * σ / (8 * (k : ℝ) ^ 2))) := by
        gcongr
    _ = C0 * C1 * Mp * ((P : ℝ) ^ (3 * e0 / (n : ℝ) ^ 2) *
          (P : ℝ) ^ (-(ρ * σ / (8 * (k : ℝ) ^ 2)))) := by ring
    _ ≤ C0 * C1 * Mp * (P : ℝ) ^ (-(ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2))) := by
        gcongr

/-- The statement of `leaf_W_bound`, Karacuba p. 245-248, PROVED from Lemmas 1, 3 and 4; the
proof is that of `leaf_W_bound_split` with `taylor_sum_bound_clean1122`. CONDITIONAL ON
`KarLemma1`. -/
theorem W_bound_clean1122 (h1 : KarLemma1) (h3 : KarLemma3) (h4 : KarLemma4) : ∀ c0 c1 c2 c3 c4 : ℝ, 0 < c0 → 0 < c1 → 0 < c2 → 0 < c3 → 0 < c4 → c0 < 1 → c1 < 1 → c2 + c4 < c1 → KarWBound c0 c1 c2 c3 c4 := by
  intro c0 c1 c2 c3 c4 h0 h1' h2 h3' h4' h01 h11 h241
  obtain ⟨C, hCpos, hC⟩ := leaf_karW_taylor_reduction
  obtain ⟨B, ρ, cc, hBpos, hρpos, hρc1, hρc3, hρc4, hcc, hBb⟩ :=
    taylor_sum_bound_clean1122 h1 h3 h4 c0 c1 c2 c3 c4 h0 h1' h2 h3' h4' h01 h11 h241
  set L := Real.log (8 / (ρ * c0 ^ 2)) with hL
  set γ := ρ * c0 ^ 2 / (64 * (4 + L ^ 2) ^ 2) with hγdef
  have hLpos : (0 : ℝ) < 4 + L ^ 2 := by positivity
  have hnum : (0 : ℝ) < ρ * c0 ^ 2 := mul_pos hρpos (pow_pos h0 2)
  have hγpos : 0 < γ := by
    rw [hγdef]
    exact div_pos hnum (by positivity)
  have hγ1 : γ ≤ 1 := by
    rw [hγdef, div_le_one (by positivity)]
    have hlt : ρ * c0 ^ 2 < 1 := by nlinarith
    have hsq : (16 : ℝ) ≤ (4 + L ^ 2) ^ 2 := by nlinarith [sq_nonneg L]
    nlinarith
  refine ⟨B + C, γ, cc, by linarith, hγpos, hcc, ?_⟩
  intro N P n hP hn hpred hbig f T hH a ha haP
  set M := karP2 c1 n P with hM
  set K := ((M : ℝ) + 1) ^ 2 with hK
  set S : ℂ := ∑ y ∈ Finset.range (M + 1), ∑ z ∈ Finset.range (M + 1),
    eC (f (a : ℝ) + ∑ j ∈ Finset.Icc 1 n,
      iteratedDeriv j f (a : ℝ) / (j.factorial : ℝ) * (((y * z : ℕ) : ℝ) ^ j)) with hS
  have hHall := hH
  obtain ⟨hU, hDer, -, -, -⟩ := hHall
  have hPr : (0 : ℝ) < P := by exact_mod_cast hP
  have hP1 : (1 : ℝ) ≤ (P : ℝ) := by exact_mod_cast hP
  have hnpos : (0 : ℝ) < (n : ℝ) ^ 2 := by
    have : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (by omega : 0 < n)
    positivity
  have hK0 : (0 : ℝ) ≤ K := by rw [hK]; positivity
  have hTay : ‖karW f M a - S‖ ≤ C * K * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) := by
    have := hC c1 N P n f T a hP hn hU hDer ha haP
    simpa [hM, hK, hS] using this
  have hAna : ‖S‖ ≤ B * K * (P : ℝ) ^ (-(ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2))) := by
    have := hBb N P n f T a hP hn hpred hbig hH ha haP
    simpa [hM, hK, hS, hL] using this
  have hle1 : (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) ≤ (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) := by
    apply Real.rpow_le_rpow_of_exponent_le hP1
    have := div_le_div_of_nonneg_right hγ1 hnpos.le
    linarith
  have hexp : γ / (n : ℝ) ^ 2 ≤ ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2) := by
    rw [hγdef, div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [hnum, hLpos, hnpos, mul_pos hnum (mul_pos hLpos hnpos)]
  have hle2 : (P : ℝ) ^ (-(ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2)))
      ≤ (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) := by
    apply Real.rpow_le_rpow_of_exponent_le hP1
    linarith
  have hmain : ‖karW f M a‖ ≤
      C * K * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) +
        B * K * (P : ℝ) ^ (-(ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2))) := by
    have hsplit : karW f M a = (karW f M a - S) + S := by ring
    calc ‖karW f M a‖ = ‖(karW f M a - S) + S‖ := congrArg (fun z : ℂ => ‖z‖) hsplit
      _ ≤ ‖karW f M a - S‖ + ‖S‖ := norm_add_le _ _
      _ ≤ _ := add_le_add hTay hAna
  have hcomp :
      C * K * (P : ℝ) ^ (-(1 / (n : ℝ) ^ 2)) +
        B * K * (P : ℝ) ^ (-(ρ * c0 ^ 2 / (32 * (n : ℝ) ^ 2 * (4 + L ^ 2) ^ 2)))
      ≤ (B + C) * K * (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) := by
    have hA := mul_le_mul_of_nonneg_left hle1 (by positivity : (0 : ℝ) ≤ C * K)
    have hB' := mul_le_mul_of_nonneg_left hle2 (by positivity : (0 : ℝ) ≤ B * K)
    have hring : (B + C) * K * (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2))
        = C * K * (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) +
          B * K * (P : ℝ) ^ (-(γ / (n : ℝ) ^ 2)) := by ring
    rw [hring]
    linarith
  linarith [hmain, hcomp]

/-- Karacuba's Theorem 1, p. 244, the named hypothesis `KaracubaThm1Named`, from his cited
Lemma 1, Vinogradov's mean value theorem, and Lemma 2, Vinogradov's Weyl sum estimate. Lemma 3
from `leaf_karLemma3`, proved in Decomp538a, Lemma 4 from `karLemma4`. CONDITIONAL ON
`KarLemma1` and `KarLemma2` only. -/
theorem karacubaThm1Named_of_vinogradov (h1 : KarLemma1) (h2 : KarLemma2) :
    DQLemma10.KaracubaThm1Named :=
  DQLemma10.karacubaThm1Named_iff.mpr <|
    karacubaTheorem1_of_cases
      (fun c0 c1 c2 c3 c4 h0 h1' h2' h3 h4 h01 h11 h241 =>
        largeCase_of_W h11
          (W_bound_clean1122 h1 leaf_karLemma3 karLemma4 c0 c1 c2 c3 c4
            h0 h1' h2' h3 h4 h01 h11 h241))
      (leaf_small_case_repaired h2)

/-- Lemma 10 of Brudern-Perelli 1998, p. 370-371, the type `Lemma10` of `U1539.lemma10`, from
Karacuba's two cited Vinogradov lemmas, through `DQLemma10.lemma10_of_named` and the PROVED
`leaf_s1_case`. CONDITIONAL ON `KarLemma1` and `KarLemma2` only. -/
theorem lemma10_of_vinogradov (h1 : KarLemma1) (h2 : KarLemma2) : Lemma10 :=
  DQLemma10.lemma10_of_named (karacubaThm1Named_of_vinogradov h1 h2) leaf_s1_case

end LeanLab.ExceptionalSet.U1539.KaracubaSplit
