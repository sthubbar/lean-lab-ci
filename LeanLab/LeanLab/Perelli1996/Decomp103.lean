/-
P0083 Perelli 1996, pages 481 through 483.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Definitions103
import LeanLab.Perelli1996.Parseval103
import LeanLab.Perelli1996.Farey103

namespace LeanLab.Perelli1996.Decomp103
open Finset Real Polynomial MeasureTheory
open LeanLab.Perelli1996.Decomp88
noncomputable section

/-- The divisor weight from equation 3 plus the logarithm from equation 2. -/
def majorWeight (m : ℕ) (N : ℝ) : ℝ :=
  (m : ℝ) * m.divisors.card / m.totient + Real.log N

/-- LEAF. Page 481 equations 2 and 3, squared.
Vaughan 1981 Chapter 3 supplies the major arc approximation.
This states the required variant for the sealed rectangular major arcs. -/
theorem leaf_major_pointwise (F : ℤ[X]) (hF : Admissible F)
    (c : ℝ) (hc : 0 < c) (A ε B : ℝ) (hA : 0 < A) (hε : 0 < ε) (hB : 0 < B) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      (∀ n ∈ win F N H, 0 ≤ Fv F n ∧ (Fv F n).toNat ≤ ⌊c * N⌋₊) →
      ∀ n ∈ win F N H,
      ‖(∫ α in Set.Icc 0 1 ∩ majorArcs N B,
          coefficientIntegrand ⌊c * N⌋₊ (Fv F n).toNat α) -
        ((Fv F n : ℝ) * Sing (Fv F n).toNat : ℂ)‖ ^ 2 ≤
        C * N ^ 2 * (Real.log N ^ (-2 * B) * majorWeight (Fv F n).toNat N ^ 2 +
          Real.log N ^ (-A)) := by
  sorry

/-- LEAF. Page 481 between equations 3 and 4.
Nair 1992 supplies the short interval mean of the divisor weight. -/
theorem leaf_nair_mean (F : ℤ[X]) (hF : Admissible F) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ ε : ℝ, 0 < ε →
      ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∑ n ∈ win F N H, majorWeight (Fv F n).toNat N ^ 2 ≤
        C * H * Real.log N ^ d := by
  sorry

/-- The polynomial window holds at most H plus one integers. -/
theorem card_win_le (F : ℤ[X]) {N H : ℝ} (hN : 0 ≤ N) (hH : 0 ≤ H) :
    ((win F N H).card : ℝ) ≤ H + 1 := by
  unfold win
  rw [Nat.card_Icc]
  have hx : 0 ≤ N ^ (1 / (F.natDegree : ℝ)) := Real.rpow_nonneg hN _
  have hlo := Nat.le_ceil (N ^ (1 / (F.natDegree : ℝ)))
  have hhi := Nat.floor_le (show 0 ≤ N ^ (1 / (F.natDegree : ℝ)) + H by positivity)
  rcases Nat.lt_or_ge (⌊N ^ (1 / (F.natDegree : ℝ)) + H⌋₊ + 1)
      ⌈N ^ (1 / (F.natDegree : ℝ))⌉₊ with h | h
  · rw [Nat.sub_eq_zero_of_le h.le]
    simp only [Nat.cast_zero]
    linarith
  · rw [Nat.cast_sub h]
    push_cast
    linarith

/-- Equation 4, CONDITIONAL ON the pointwise approximation and Nair mean leaves. -/
theorem major (F : ℤ[X]) (hF : Admissible F) (c : ℝ) (hc : 0 < c) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ A ε B : ℝ, 0 < A → 0 < ε → 0 < B →
      ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      (∀ n ∈ win F N H, 0 ≤ Fv F n ∧ (Fv F n).toNat ≤ ⌊c * N⌋₊) →
      majorError F ⌊c * N⌋₊ N H B ≤
        C * H * N ^ 2 * (Real.log N ^ (-2 * B + d) + Real.log N ^ (-A)) := by
  obtain ⟨d, hd, hmean⟩ := leaf_nair_mean F hF
  refine ⟨d, hd, ?_⟩
  intro A ε B hA hε hB
  obtain ⟨CP, NP, hCP, hNP, hpoint⟩ := leaf_major_pointwise F hF c hc A ε B hA hε hB
  obtain ⟨CM, NM, hCM, hNM, hmean⟩ := hmean ε hε
  refine ⟨CP * (CM + 2), max NP NM, by positivity, hNP.trans (le_max_left _ _), ?_⟩
  intro N H hN hH hHu hcut
  have hNP' := (le_max_left NP NM).trans hN
  have hNM' := (le_max_right NP NM).trans hN
  have hN3 := hNP.trans hNP'
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hexp : 0 ≤ 1 / (3 * (F.natDegree : ℝ)) + ε := by positivity
  have hH1 : 1 ≤ H := (Real.one_le_rpow (by linarith) hexp).trans hH
  have hcard : ((win F N H).card : ℝ) ≤ 2 * H :=
    (card_win_le F hN0.le (by linarith)).trans (by linarith)
  have hsum := Finset.sum_le_sum (hpoint N H hNP' hH hHu hcut)
  have hm := hmean N H hNM' hH hHu
  unfold majorError
  calc
    _ ≤ ∑ n ∈ win F N H, CP * N ^ 2 *
        (Real.log N ^ (-2 * B) * majorWeight (Fv F n).toNat N ^ 2 + Real.log N ^ (-A)) := hsum
    _ = CP * N ^ 2 * (Real.log N ^ (-2 * B) *
        (∑ n ∈ win F N H, majorWeight (Fv F n).toNat N ^ 2) +
        ((win F N H).card : ℝ) * Real.log N ^ (-A)) := by
      rw [← Finset.mul_sum]
      congr 1
      rw [Finset.sum_add_distrib, ← Finset.mul_sum]
      simp
    _ ≤ CP * N ^ 2 * (Real.log N ^ (-2 * B) * (CM * H * Real.log N ^ d) +
        (2 * H) * Real.log N ^ (-A)) := by gcongr
    _ = CP * CM * H * N ^ 2 * Real.log N ^ (-2 * B + d) +
        2 * CP * H * N ^ 2 * Real.log N ^ (-A) := by
      rw [show Real.log N ^ (-2 * B) * (CM * H * Real.log N ^ d) =
        CM * H * (Real.log N ^ (-2 * B) * Real.log N ^ d) by ring,
        ← Real.rpow_add hL]
      ring
    _ ≤ _ := by
      have h1 : CP * CM ≤ CP * (CM + 2) := by nlinarith
      have h2 : 2 * CP ≤ CP * (CM + 2) := by nlinarith
      rw [mul_add]
      gcongr

/-- The weighted inner integral in page 481 equation 5. -/
def kernelMoment (F : ℤ[X]) (M : ℕ) (N H B ξ : ℝ) : ℝ :=
  ∫ α in minorArcs N B, ‖primeSum M α‖ ^ 2 *
    ‖Section2.polynomialKernel F N H (α - ξ)‖

/-- The largest minor prime mass in an interval of width one over the larger Farey order.
This enlarges every shifted secondary arc in page 483 equation 12. -/
def shortMass (M : ℕ) (N B Q : ℝ) : ℝ :=
  sSup {x | ∃ t : ℝ, x =
    ∫ α in minorArcs N B ∩ Set.Icc t (t + 1 / (4 * Q ^ 2)), ‖primeSum M α‖ ^ 2}

/-- Every local prime second moment is nonnegative, including an unbounded supremum. -/
theorem localMass_nonneg (M : ℕ) (N B Q : ℝ) : 0 ≤ localMass M N B Q := by
  unfold localMass
  apply Real.sSup_nonneg
  rintro x ⟨q, hq, hqQ, a, ha, rfl⟩
  exact integral_nonneg (fun _ => sq_nonneg _)

/-- Every short interval prime second moment is nonnegative. -/
theorem shortMass_nonneg (M : ℕ) (N B Q : ℝ) : 0 ≤ shortMass M N B Q := by
  unfold shortMass
  apply Real.sSup_nonneg
  rintro x ⟨t, rfl⟩
  exact integral_nonneg (fun _ => sq_nonneg _)

/-- LEAF. Page 481 equation 5, Parseval followed by the prime second moment bound.
The arbitrary nonnegative U bounds the weighted inner integral uniformly. -/
theorem leaf_parseval (F : ℤ[X]) (c : ℝ) (hc : 0 < c) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H B U : ℝ, N₀ ≤ N →
      0 ≤ U →
      (∀ n ∈ win F N H, 0 ≤ Fv F n) →
      (∀ ξ ∈ minorArcs N B, kernelMoment F ⌊c * N⌋₊ N H B ξ ≤ U) →
      minorError F ⌊c * N⌋₊ N H B ≤ C * N * Real.log N * U := by
  obtain ⟨C, N₀, hC, hN₀, hmoment⟩ := Parseval103.prime_second_moment_scaled c hc
  refine ⟨C, N₀, hC, hN₀, ?_⟩
  intro N H B U hN hU hpos hbound
  let M := ⌊c * N⌋₊
  let s := minorArcs N B
  have hs : s ⊆ Set.Icc (0 : ℝ) 1 := Set.diff_subset
  have hms : MeasurableSet s := by dsimp [s, minorArcs, majorArcs]; measurability
  have hf : Continuous (fun α : ℝ => primeSum M α ^ 2) := by
    unfold primeSum Kernel.e
    fun_prop
  have hfreq (n : ℕ) (hn : n ∈ win F N H) : ((Fv F n).toNat : ℝ) = (Fv F n : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (hpos n hn)
  have hq := Parseval103.quadratic_le s hs hms (fun α => primeSum M α ^ 2) hf
    (win F N H) (fun n => (Fv F n : ℝ)) U hU
    (by intro ξ hξ; simpa only [norm_pow, kernelMoment, Section2.polynomialKernel, M, s] using hbound ξ hξ)
  have herr : minorError F M N H B =
      ∑ n ∈ win F N H, ‖∫ α in s, primeSum M α ^ 2 *
        Kernel.e (-(Fv F n : ℝ) * α)‖ ^ 2 := by
    unfold minorError
    apply Finset.sum_congr rfl
    intro n hn
    simp only [coefficientIntegrand, hfreq n hn, s]
  rw [← herr] at hq
  have hfull : (∫ ξ in s, ‖primeSum M ξ ^ 2‖) ≤ C * N * Real.log N := by
    calc
      _ = ∫ ξ in s, ‖primeSum M ξ‖ ^ 2 := by simp only [norm_pow]
      _ ≤ ∫ ξ in Set.Icc (0 : ℝ) 1, ‖primeSum M ξ‖ ^ 2 := by
        apply setIntegral_mono_set
        · have hp : Continuous (fun ξ : ℝ => ‖primeSum M ξ‖ ^ 2) := by
            unfold primeSum Kernel.e
            fun_prop
          exact hp.integrableOn_Icc
        · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
        · exact Filter.Eventually.of_forall (fun _ h => hs h)
      _ ≤ _ := hmoment N hN
  exact hq.trans (by nlinarith [mul_le_mul_of_nonneg_right hfull hU])

/-- LEAF. Pages 482 and 483 equations 9 through 12.
The Weyl input bounds the complement of the secondary arcs.
At most L to the B over two short intervals cover the secondary arcs. -/
theorem leaf_weyl_localization (F : ℤ[X]) (hF : Admissible F)
    (hW : Section2.WeylLemma F) (c : ℝ) (hc : 0 < c)
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ ξ ∈ minorArcs N B,
      kernelMoment F ⌊c * N⌋₊ N H B ξ ≤
        C * H * Real.log N ^ (B / 2) *
          shortMass ⌊c * N⌋₊ N B (fareyOrder F N H B) +
        C * H * N * Real.log N ^
          (-(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
            (8 * Section2.weylExponent F) - 1) := by
  sorry

/-- LEAF. Page 483 equations 12 through 14.
A short interval meets at most two Farey cells of order Q.
Each cell lies in its enclosing puncturedArc from task88. -/
theorem leaf_farey_cover (M : ℕ) (N B Q : ℝ) (hQ : 2 ≤ Q) :
    shortMass M N B Q ≤ 2 * localMass M N B Q := by
  unfold shortMass
  apply csSup_le
  · exact ⟨∫ α in minorArcs N B ∩ Set.Icc (0 : ℝ) (0 + 1 / (4 * Q ^ 2)),
      ‖primeSum M α‖ ^ 2, 0, rfl⟩
  · rintro x ⟨t, rfl⟩
    obtain ⟨q, hq, hqQ, a, ha, r, hr, hrQ, b, hb, hcover⟩ := Farey103.rational_two_cover t Q hQ
    let s := minorArcs N B ∩ Set.Icc t (t + 1 / (4 * Q ^ 2))
    let u := puncturedArc N B Q q a
    let v := puncturedArc N B Q r b
    have hsub : s ⊆ u ∪ v := by
      intro α hα
      have hnot : α ∉ majorArcs N B := hα.1.2
      rcases hcover hα.2 with hu | hv
      · exact Or.inl ⟨hu, hnot⟩
      · exact Or.inr ⟨hv, hnot⟩
    have hmeas (k : ℕ) (z : ℤ) : MeasurableSet (puncturedArc N B Q k z) := by
      unfold puncturedArc majorArcs
      measurability
    have hint (k : ℕ) (z : ℤ) : IntegrableOn (fun α => ‖primeSum M α‖ ^ 2)
        (puncturedArc N B Q k z) := by
      have hcont : Continuous (fun α : ℝ => ‖primeSum M α‖ ^ 2) := by
        unfold primeSum Kernel.e
        fun_prop
      exact hcont.integrableOn_Icc.mono_set Set.diff_subset
    have hlocal (k : ℕ) (z : ℤ) (hk : 0 < k) (hkQ : (k : ℝ) ≤ Q)
        (hz : Nat.Coprime z.natAbs k) :
        (∫ α in puncturedArc N B Q k z, ‖primeSum M α‖ ^ 2) ≤ localMass M N B Q := by
      unfold localMass
      exact le_csSup (Farey103.localMass_bddAbove M N B Q hQ) ⟨k, hk, hkQ, z, hz, rfl⟩
    have htwo := Farey103.integral_two_cover (fun α => ‖primeSum M α‖ ^ 2)
      (fun _ => sq_nonneg _) s u v (hmeas q a) (hmeas r b) (hint q a) (hint r b) hsub
    calc
      _ ≤ (∫ α in u, ‖primeSum M α‖ ^ 2) + ∫ α in v, ‖primeSum M α‖ ^ 2 := htwo
      _ ≤ localMass M N B Q + localMass M N B Q := add_le_add
        (hlocal q a hq hqQ ha) (hlocal r b hr hrQ hb)
      _ = _ := by ring

/-- The sealed minor reduction from Parseval, Weyl localization and Farey covering.
CONDITIONAL ON the three smaller leaves. -/
theorem minor (F : ℤ[X]) (hF : Admissible F)
    (hW : Section2.WeylLemma F) (c : ℝ) (hc : 0 < c)
    (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B)
    (hparam : ∃ NP : ℝ, 3 ≤ NP ∧ ∀ N H : ℝ, NP ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H → 2 ≤ fareyOrder F N H B) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      (∀ n ∈ win F N H, 0 ≤ Fv F n ∧ (Fv F n).toNat ≤ ⌊c * N⌋₊) →
      minorError F ⌊c * N⌋₊ N H B ≤
        C * H * N * Real.log N ^ (B / 2 + 1) *
          localMass ⌊c * N⌋₊ N B (fareyOrder F N H B) +
        C * H * N ^ 2 * Real.log N ^
          (-(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
            (8 * Section2.weylExponent F)) := by
  obtain ⟨CP, NP, hCP, hNP, hp⟩ := leaf_parseval F c hc
  obtain ⟨CW, NW, hCW, hNW, hw⟩ := leaf_weyl_localization F hF hW c hc ε B hε hB
  obtain ⟨NG, hNG, hg⟩ := hparam
  refine ⟨2 * CP * CW, max NP (max NW NG), by positivity,
    hNP.trans (le_max_left _ _), ?_⟩
  intro N H hN hH hHu hcut
  have hNP' := (le_max_left NP (max NW NG)).trans hN
  have hNW' := (le_max_left NW NG).trans ((le_max_right NP (max NW NG)).trans hN)
  have hNG' := (le_max_right NW NG).trans ((le_max_right NP (max NW NG)).trans hN)
  have hN3 := hNP.trans hNP'
  have hN0 : 0 < N := by linarith
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  let Q := fareyOrder F N H B
  let M := ⌊c * N⌋₊
  let E := -(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
    (8 * Section2.weylExponent F)
  let U := 2 * CW * H * Real.log N ^ (B / 2) * localMass M N B Q +
    CW * H * N * Real.log N ^ (E - 1)
  have hm := localMass_nonneg M N B Q
  have hU : 0 ≤ U := by dsimp [U]; positivity
  have hcover := leaf_farey_cover M N B Q (hg N H hNG' hH)
  have hinner : ∀ ξ ∈ minorArcs N B, kernelMoment F M N H B ξ ≤ U := by
    intro ξ hξ
    calc
      _ ≤ CW * H * Real.log N ^ (B / 2) * shortMass M N B Q +
        CW * H * N * Real.log N ^ (E - 1) := hw N H hNW' hH hHu ξ hξ
      _ ≤ CW * H * Real.log N ^ (B / 2) * (2 * localMass M N B Q) +
        CW * H * N * Real.log N ^ (E - 1) := by gcongr
      _ = U := by dsimp [U]; ring
  have hp' := hp N H B U hNP' hU (fun n hn => (hcut n hn).1) hinner
  calc
    _ ≤ CP * N * Real.log N * U := hp'
    _ = 2 * CP * CW * H * N * Real.log N ^ (B / 2 + 1) * localMass M N B Q +
        CP * CW * H * N ^ 2 * Real.log N ^ E := by
      dsimp [U]
      rw [Real.rpow_add hL, Real.rpow_one,
        show Real.log N ^ E = Real.log N * Real.log N ^ (E - 1) by
          calc
            _ = Real.log N ^ (1 + (E - 1)) := by congr 1; ring
            _ = _ := by rw [Real.rpow_add hL, Real.rpow_one]]
      ring
    _ ≤ _ := by
      have hcoef : CP * CW ≤ 2 * CP * CW := by nlinarith [mul_pos hCP hCW]
      gcongr

end
end LeanLab.Perelli1996.Decomp103
