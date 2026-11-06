/-
Perelli 1996, pages 486 and 487, equations 26 through 28.
Split the weighted prime mean comparison into its three displayed steps.
All integrals use one period from zero to one. The printed period starts at 1/Q.
The rational arcs enclose the printed Farey cells. The principal comparison
includes the kernel tail correction for this enlargement.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Decomp289a
import LeanLab.Perelli1996.Ramanujan103
import LeanLab.Perelli1996.Localization103

namespace LeanLab.Perelli1996.Decomp400e
open Finset Real Polynomial MeasureTheory
open LeanLab.Perelli1996.Decomp88 LeanLab.Perelli1996.Decomp289a
noncomputable section

/-- Page 486 before equation 26. Periodic enclosing arcs of radius one over q Q.
These contain the printed Farey cells and are the domains of the remainder mass. -/
def meanMajorArcs (F : ℤ[X]) (N H B : ℝ) : Set ℝ :=
  {α | ∃ q : ℕ, 0 < q ∧ (q : ℝ) ≤ Real.log N ^ B ∧
    ∃ a : ℤ, Nat.Coprime a.natAbs q ∧
      |α - (a : ℝ) / q| ≤ 1 / ((q : ℝ) * meanOrder F N H B)}

/-- Page 486 equation 26. Real part of the major arc prime mean integral. -/
def majorPrimeMean (F : ℤ[X]) (M : ℕ) (N H B : ℝ) : ℝ :=
  (∫ α in Set.Icc 0 1 ∩ meanMajorArcs F N H B,
    primeSum M α ^ 2 * Section2.polynomialKernel F N H (-α)).re

/-- Pages 486 and 487 equations 27 and 28. The truncated singular mean.
The Ramanujan sum at a negative integer equals its value at that integer's absolute value.
The cutoff hypotheses in the leaves ensure nonnegative polynomial values. -/
def truncatedWeightedMean (F : ℤ[X]) (N H B : ℝ) : ℝ :=
  (∑ n ∈ win F N H, ((Fv F n : ℝ) : ℂ) *
    ∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊,
      ((ArithmeticFunction.moebius q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2) *
        Ramanujan103.ramanujanSum q (Fv F n).toNat).re

/-- LEAF. Page 486 equation 26. Parseval and the secondary Weyl decay discard the minor arcs.
This is only the comparison with the major integral, before the character expansion.
The period from zero to one is the periodic form of the printed shifted period. -/
theorem leaf_minor_mean (F : ℤ[X]) (hF : Admissible F)
    (hW : Section2.WeylLemma F) (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B → ∀ c : ℝ, 0 < c →
      ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      (∀ n ∈ win F N H, 0 ≤ Fv F n ∧ (Fv F n).toNat ≤ ⌊c * N⌋₊) →
      |(∑ n ∈ win F N H, R (Fv F n).toNat) -
        majorPrimeMean F ⌊c * N⌋₊ N H B| ≤ C * H * N * Real.log N ^ (-A) := by
  let k : ℝ := F.natDegree
  let K := Section2.weylExponent F
  have hk : 0 < k := by dsimp [k]; exact_mod_cast (show 0 < F.natDegree by have := hF.1; omega)
  have hK : 0 < K := by dsimp [K, Section2.weylExponent]; positivity
  let B₀ := k ^ 2 + 2 * K * (A + 1) + 4
  have hB₀ : 0 < B₀ := by dsimp [B₀]; positivity
  refine ⟨B₀, hB₀, ?_⟩
  intro B hBB c hc
  have hB : 0 < B := hB₀.trans_le hBB
  have hB4 : 4 ≤ B := by
    have hnon : 0 ≤ 2 * K * (A + 1) := by positivity
    dsimp [B₀] at hBB
    nlinarith [sq_nonneg k]
  have hD : 0 < (4 * B) / 8 + (F.natDegree : ℝ) ^ 2 / 2 - 1 := by nlinarith [sq_nonneg k]
  obtain ⟨CK, NK, hCK, hNK, hw⟩ :=
    Section2.weyl_decay_of_denominator_bounds F hF hW (4 * B) hD
  obtain ⟨CP, NP, hCP, hNP, hp⟩ := Parseval103.prime_second_moment_scaled c hc
  let δ := 1 / (12 * k) + ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨NG, hNG, hg⟩ := Section3.power_error_log_saving δ B hδ
  let N₀ := max (max NK NP) (max NG (Real.exp 1))
  refine ⟨CK * CP, N₀, mul_pos hCK hCP,
    hNK.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro N H hN hH hHu hcut
  have hNK' : NK ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNP' : NP ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hNG' : NG ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNE : Real.exp 1 ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hN3 : 3 ≤ N := hNK.trans hNK'
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    simpa using Real.log_le_log (Real.exp_pos 1) hNE
  have hL : 0 < Real.log N := by linarith
  have hH1 : 1 ≤ H := (Real.one_le_rpow hN1 (by positivity)).trans hH
  have hH0 : 0 < H := by linarith
  have hupper : H ≤ N ^ (1 / (F.natDegree : ℝ)) :=
    hHu.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  have hpower : N ^ δ ≤ H * Real.log N ^ (-B) := by
    apply hg N H hNG'
    convert hH using 1
    dsimp [δ, k]
    congr 1
    ring
  have hrec : 1 / H ≤ Real.log N ^ (-B) := by
    apply (div_le_iff₀ hH0).mpr
    have hnδ := Real.one_le_rpow hN1 hδ.le
    nlinarith
  let Q := meanOrder F N H B
  have hQ : 1 ≤ Q := by
    have hHpow : H ≤ H ^ F.natDegree :=
      le_self_pow₀ hH1 (by have := hF.1; omega)
    calc
      1 ≤ N ^ δ := Real.one_le_rpow hN1 hδ.le
      _ ≤ H * Real.log N ^ (-B) := hpower
      _ ≤ Q := by dsimp [Q, meanOrder]; gcongr
  have hQ0 : 0 < Q := by linarith
  let E := -(4 * B - 4 * k ^ 2) / (8 * K)
  have hpoint (α : ℝ) (hα : α ∉ meanMajorArcs F N H B) :
      ‖Section2.polynomialKernel F N H α‖ ≤ CK * H * Real.log N ^ E := by
    obtain ⟨q, hq, hqQ, a, hcop, happ⟩ := Farey103.dirichlet_real_order α Q hQ
    have hqR : (0 : ℝ) < q := by exact_mod_cast hq
    have hlarge : Real.log N ^ B < (q : ℝ) := by
      apply lt_of_not_ge
      intro hsmall
      exact hα ⟨q, hq, hsmall, a, hcop, happ.le⟩
    have happ' : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
      refine happ.le.trans ?_
      apply one_div_le_one_div_of_le (sq_pos_of_pos hqR)
      nlinarith
    have hh := hw N H α hNK' hH1 hupper a q hq hcop happ'
    have hex : -(4 * B) / 4 = -B := by ring
    have hqsave : 1 / (q : ℝ) ≤ Real.log N ^ (-B) := by
      rw [Real.rpow_neg hL.le]
      simpa only [one_div] using
        one_div_le_one_div_of_le (Real.rpow_pos_of_pos hL B) hlarge.le
    have hqH : (q : ℝ) / H ^ F.natDegree ≤ Real.log N ^ (-B) := by
      apply (div_le_iff₀ (pow_pos hH0 _)).mpr
      simpa [Q, meanOrder, mul_comm] using hqQ
    simpa only [hex, k, K, E] using hh (by simpa only [hex] using hqsave)
      (by simpa only [hex] using hrec) (by simpa only [hex] using hqH)
  have hmeas : MeasurableSet (meanMajorArcs F N H B) := by
    unfold meanMajorArcs
    simp only [Set.setOf_exists, Set.setOf_and]
    measurability
  let M := ⌊c * N⌋₊
  let f := fun α : ℝ => primeSum M α ^ 2 * Section2.polynomialKernel F N H (-α)
  have hf : Continuous f := by
    dsimp [f, primeSum, Section2.polynomialKernel, Kernel.e]
    fun_prop
  have hfull : (∫ α in Set.Icc (0 : ℝ) 1, f α) =
      ((∑ n ∈ win F N H, R (Fv F n).toNat : ℝ) : ℂ) := by
    have hexp : f = fun α => ∑ n ∈ win F N H, coefficientIntegrand M (Fv F n).toNat α := by
      funext α
      dsimp [f, Section2.polynomialKernel]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      unfold coefficientIntegrand
      congr 2
      have hv : ((Fv F n).toNat : ℝ) = (Fv F n : ℝ) := by
        exact_mod_cast Int.toNat_of_nonneg (hcut n hn).1
      rw [hv]
      ring
    rw [hexp, integral_finsetSum]
    · rw [Complex.ofReal_sum]
      apply Finset.sum_congr rfl
      intro n hn
      exact Decomp88.leaf_fourier M _ (hcut n hn).2
    · intro n hn
      apply Continuous.integrableOn_Icc
      unfold coefficientIntegrand primeSum Kernel.e
      fun_prop
  let s := Set.Icc (0 : ℝ) 1 \ meanMajorArcs F N H B
  have hs : MeasurableSet s := measurableSet_Icc.diff hmeas
  have hsub : s ⊆ Set.Icc (0 : ℝ) 1 := Set.sdiff_subset
  have hsplit := integral_inter_add_sdiff hmeas
    (show IntegrableOn f (Set.Icc (0 : ℝ) 1) from hf.integrableOn_Icc)
  have herror : |(∑ n ∈ win F N H, R (Fv F n).toNat) -
      majorPrimeMean F M N H B| = |(∫ α in s, f α).re| := by
    have hr := congrArg Complex.re hsplit
    rw [hfull] at hr
    simp only [Complex.add_re, Complex.ofReal_re] at hr
    change (∫ α in Set.Icc 0 1 ∩ meanMajorArcs F N H B, f α).re +
      (∫ α in s, f α).re = _ at hr
    change |_ - (∫ α in Set.Icc 0 1 ∩ meanMajorArcs F N H B, f α).re| = _
    congr 1
    linarith
  have hsqcont : Continuous (fun α : ℝ => ‖primeSum M α‖ ^ 2) := by
    unfold primeSum Kernel.e
    fun_prop
  have hmass : (∫ α in s, ‖primeSum M α‖ ^ 2) ≤ CP * N * Real.log N := by
    exact (setIntegral_mono_set hsqcont.integrableOn_Icc
      (Filter.Eventually.of_forall (fun α => sq_nonneg ‖primeSum M α‖))
      (Filter.Eventually.of_forall hsub)).trans (hp N hNP')
  have hnorm (α : ℝ) (hα : α ∈ s) :
      ‖f α‖ ≤ (CK * H * Real.log N ^ E) * ‖primeSum M α‖ ^ 2 := by
    have hneg : -α ∉ meanMajorArcs F N H B := by
      rintro ⟨q, hq, hqP, a, hcop, ha⟩
      apply hα.2
      refine ⟨q, hq, hqP, -a, by simpa using hcop, ?_⟩
      have heq : α - ((-a : ℤ) : ℝ) / q = -(-α - (a : ℝ) / q) := by push_cast; ring
      rw [heq, abs_neg]
      exact ha
    dsimp [f]
    rw [norm_mul, norm_pow]
    have ht := mul_le_mul_of_nonneg_left (hpoint (-α) hneg) (sq_nonneg ‖primeSum M α‖)
    nlinarith only [ht]
  have hi : (∫ α in s, ‖f α‖) ≤
      CK * H * Real.log N ^ E * (∫ α in s, ‖primeSum M α‖ ^ 2) := by
    rw [← integral_const_mul]
    exact setIntegral_mono_on (hf.norm.integrableOn_Icc.mono_set hsub)
      ((hsqcont.const_mul _).integrableOn_Icc.mono_set hsub) hs hnorm
  have hE : E + 1 ≤ -A := by
    have hh : -(4 * B - 4 * k ^ 2) / (8 * K) ≤ -A - 1 := by
      apply (div_le_iff₀ (by positivity : 0 < 8 * K)).mpr
      dsimp [B₀] at hBB
      nlinarith
    dsimp [E]
    linarith
  calc
    _ = |(∫ α in s, f α).re| := herror
    _ ≤ ‖∫ α in s, f α‖ := Complex.abs_re_le_norm _
    _ ≤ ∫ α in s, ‖f α‖ := norm_integral_le_integral_norm _
    _ ≤ CK * H * Real.log N ^ E * (∫ α in s, ‖primeSum M α‖ ^ 2) := hi
    _ ≤ CK * H * Real.log N ^ E * (CP * N * Real.log N) := by gcongr
    _ = CK * CP * H * N * Real.log N ^ (E + 1) := by
      rw [Real.rpow_add hL, Real.rpow_one]
      ring
    _ ≤ CK * CP * H * N * Real.log N ^ (-A) := by
      gcongr

/-- LEAF. Page 486 equation 27. Insert the principal kernel and keep the remainder mass.
Cauchy Schwarz gives the square root term. The enclosing arc variant includes
the principal kernel tail correction at the Farey cell endpoints.
This leaf does not discard the minor arcs
or replace the finite Ramanujan sum by the full singular series. -/
theorem leaf_principal_mean (F : ℤ[X]) (hF : Admissible F)
    (A ε B c : ℝ) (hA : 0 < A) (hε : 0 < ε) (hB : 0 < B) (hc : 0 < c) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      (∀ n ∈ win F N H, 0 ≤ Fv F n ∧ (Fv F n).toNat ≤ ⌊c * N⌋₊) →
      |majorPrimeMean F ⌊c * N⌋₊ N H B - truncatedWeightedMean F N H B| ≤
        C * H * (remainderMass F c N H B +
          Real.sqrt (N * Real.log N * remainderMass F c N H B)) +
        C * H * N * Real.log N ^ (-A) := by
  sorry

/-- LEAF. Page 487 equation 28, by the tail argument of page 481 equations 3 and 4.
Only the finite singular series is replaced by the full singular series here. -/
theorem leaf_singular_tail (F : ℤ[X]) (hF : Admissible F)
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∃ B₀ : ℝ, 0 < B₀ ∧ ∀ B : ℝ, B₀ ≤ B →
      ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      |truncatedWeightedMean F N H B -
        ∑ n ∈ win F N H, (Fv F n : ℝ) * Sing (Fv F n).toNat| ≤
          C * H * N * Real.log N ^ (-A) := by
  sorry

/-- Pages 486 and 487 equations 26 through 28. The exact existing weighted mean target.
CONDITIONAL ON the three smaller leaves and the existing Weyl input.
The assembly has no sorry of its own. -/
theorem leaf_weighted_mean (F : ℤ[X]) (hF : Admissible F)
    (A ε : ℝ) (hA : 0 < A) (hε : 0 < ε) :
    ∃ B c C N₀ : ℝ, 0 < B ∧ 0 < c ∧ 0 < C ∧ 3 ≤ N₀ ∧
      ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
      |(∑ n ∈ win F N H, R (Fv F n).toNat) -
        ∑ n ∈ win F N H, (Fv F n : ℝ) * Sing (Fv F n).toNat| ≤
        C * H * (remainderMass F c N H B +
          Real.sqrt (N * Real.log N * remainderMass F c N H B)) +
        C * H * N * Real.log N ^ (-A) := by
  obtain ⟨B₁, hB₁, hm⟩ := leaf_minor_mean F hF (Decomp88.leaf_weyl F) A ε hA hε
  obtain ⟨B₂, hB₂, hs⟩ := leaf_singular_tail F hF A ε hA hε
  let B := max B₁ B₂
  have hB : 0 < B := hB₁.trans_le (le_max_left _ _)
  obtain ⟨c, NK, hc, hNK, hcut⟩ := Decomp88.leaf_cutoff F hF
  obtain ⟨CM, NM, hCM, hNM, hm⟩ := hm B (le_max_left _ _) c hc
  obtain ⟨CS, NS, hCS, hNS, hs⟩ := hs B (le_max_right _ _)
  obtain ⟨CP, NP, hCP, hNP, hp⟩ := leaf_principal_mean F hF A ε B c hA hε hB hc
  let N₀ := max (max NK NM) (max NS NP)
  refine ⟨B, c, CM + CP + CS, N₀, hB, hc, by positivity,
    hNK.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro N H hN hH hHu
  have hNK' : NK ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNM' : NM ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hNS' : NS ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNP' : NP ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hN3 : 3 ≤ N := hNK.trans hNK'
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 ≤ N := by linarith
  have hH0 : 0 ≤ H := (Real.rpow_nonneg hN0 _).trans hH
  have hupper : H ≤ N ^ (1 / (F.natDegree : ℝ)) :=
    hHu.trans (Real.rpow_le_rpow_of_exponent_le hN1 (by linarith))
  have hcut' := hcut N H hNK' hH0 hupper
  have hm' := hm N H hNM' hH hHu hcut'
  have hp' := hp N H hNP' hH hHu hcut'
  have hs' := hs N H hNS' hH hHu
  have hmass := remainderMass_nonneg F c N H B
  have hnon : 0 ≤ H * (remainderMass F c N H B +
      Real.sqrt (N * Real.log N * remainderMass F c N H B)) := by positivity
  have htri := abs_sub_le
    (∑ n ∈ win F N H, R (Fv F n).toNat)
    (majorPrimeMean F ⌊c * N⌋₊ N H B)
    (∑ n ∈ win F N H, (Fv F n : ℝ) * Sing (Fv F n).toNat)
  have htri' := abs_sub_le (majorPrimeMean F ⌊c * N⌋₊ N H B)
    (truncatedWeightedMean F N H B)
    (∑ n ∈ win F N H, (Fv F n : ℝ) * Sing (Fv F n).toNat)
  nlinarith [mul_nonneg (add_nonneg hCM.le hCS.le) hnon]

/-- Pages 487 and 489 equations 30, 32 and 37. Reuse the existing error absorption
with the newly split weighted mean. CONDITIONAL ON its OPEN leaves,
the existing character remainder input and the higher degree Weyl input. -/
theorem leaf_prime_mean_estimate (F : ℤ[X]) (hF : Admissible F) :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C N₀ : ℝ,
      ∀ N H : ℝ, N₀ ≤ N → N ^ (1 / (6 * (F.natDegree : ℝ)) + ε) ≤ H →
        H ≤ N ^ (1 / (F.natDegree : ℝ) - ε) →
        |(∑ n ∈ win F N H, R (Fv F n).toNat) -
          (F.leadingCoeff : ℝ) * N * ∑ n ∈ win F N H, Sing (Fv F n).toNat| ≤
            C * H * N * Real.log N ^ (-A) := by
  intro A ε hA hε
  obtain ⟨B, c, CW, NW, hB, hc, hCW, hNW, hw⟩ := leaf_weighted_mean F hF A ε hA hε
  obtain ⟨CT, NT, hCT, hNT, ht⟩ := leaf_leading_term F hF A ε hA hε
  obtain ⟨CR, NR, hCR, hNR, hr⟩ := leaf_remainder_mean F hF c B A ε hc hB hA hε
  refine ⟨CW * (CR + Real.sqrt CR + 1) + CT,
    max (Real.exp 1 + 3) (max NW (max NT NR)), ?_⟩
  intro N H hN hH hHu
  have hNexp : Real.exp 1 + 3 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by have := Real.exp_pos 1; linarith
  have hL : 1 ≤ Real.log N := by
    have := Real.log_le_log (Real.exp_pos 1) (show Real.exp 1 ≤ N by linarith)
    simpa using this
  have hL0 : 0 < Real.log N := by linarith
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH
  have hNW' := (le_max_left NW (max NT NR)).trans ((le_max_right _ _).trans hN)
  have hNT' := (le_max_left NT NR).trans ((le_max_right NW _).trans ((le_max_right _ _).trans hN))
  have hNR' := (le_max_right NT NR).trans ((le_max_right NW _).trans ((le_max_right _ _).trans hN))
  have hr' := hr N H hNR' hH hHu
  have hpow := Real.rpow_le_rpow_of_exponent_le hL (show -2 * A - 1 ≤ -A by linarith)
  have hsmall : remainderMass F c N H B ≤ CR * N * Real.log N ^ (-A) :=
    hr'.trans (mul_le_mul_of_nonneg_left hpow (by positivity))
  have hsq : Real.sqrt (N * Real.log N * remainderMass F c N H B) ≤
      Real.sqrt CR * N * Real.log N ^ (-A) := by
    apply (Real.sqrt_le_iff).2
    refine ⟨by positivity, ?_⟩
    calc N * Real.log N * remainderMass F c N H B
        ≤ N * Real.log N * (CR * N * Real.log N ^ (-2 * A - 1)) :=
          mul_le_mul_of_nonneg_left hr' (by positivity)
      _ = (Real.sqrt CR * N * Real.log N ^ (-A)) ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hCR.le,
          ← Real.rpow_mul_natCast hL0.le]
        have he : Real.log N * Real.log N ^ (-2 * A - 1) = Real.log N ^ (-A * 2) := by
          calc
            _ = Real.log N ^ (1 : ℝ) * Real.log N ^ (-2 * A - 1) := by rw [Real.rpow_one]
            _ = Real.log N ^ (1 + (-2 * A - 1)) := (Real.rpow_add hL0 _ _).symm
            _ = _ := by congr 1; ring
        calc _ = CR * N ^ 2 * (Real.log N * Real.log N ^ (-2 * A - 1)) := by ring
          _ = _ := by rw [he]; norm_num
  calc _ ≤ |(∑ n ∈ win F N H, R (Fv F n).toNat) -
          ∑ n ∈ win F N H, (Fv F n : ℝ) * Sing (Fv F n).toNat| +
        |(∑ n ∈ win F N H, (Fv F n : ℝ) * Sing (Fv F n).toNat) -
          (F.leadingCoeff : ℝ) * N * ∑ n ∈ win F N H, Sing (Fv F n).toNat| :=
          abs_sub_le _ _ _
    _ ≤ (CW * H * (remainderMass F c N H B +
          Real.sqrt (N * Real.log N * remainderMass F c N H B)) +
          CW * H * N * Real.log N ^ (-A)) + CT * H * N * Real.log N ^ (-A) :=
          add_le_add (hw N H hNW' hH hHu) (ht N H hNT' hH hHu)
    _ ≤ (CW * H * (CR * N * Real.log N ^ (-A) +
          Real.sqrt CR * N * Real.log N ^ (-A)) +
          CW * H * N * Real.log N ^ (-A)) + CT * H * N * Real.log N ^ (-A) := by
          gcongr
    _ = _ := by ring

end
end LeanLab.Perelli1996.Decomp400e
