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

/-- Equation 9: the Weyl decay exponent once the three denominator bounds hold. -/
private theorem wl_weyl_decay (F : ℤ[X]) (hF : Admissible F)
    (hW : Section2.WeylLemma F) (B : ℝ)
    (hD : 0 < B / 8 + (F.natDegree : ℝ) ^ 2 / 2 - 1) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H α : ℝ, N₀ ≤ N →
      1 ≤ H → H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∀ a : ℤ, ∀ q : ℕ, 0 < q → Nat.Coprime a.natAbs q →
      |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 →
      1 / (q : ℝ) ≤ Real.log N ^ (-B / 4) →
      1 / H ≤ Real.log N ^ (-B / 4) →
      (q : ℝ) / H ^ F.natDegree ≤ Real.log N ^ (-B / 4) →
      ‖Section2.polynomialKernel F N H α‖ ≤ C * H *
        Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) / (8 * Section2.weylExponent F)) := by
  let D := B / 8 + (F.natDegree : ℝ) ^ 2 / 2 - 1
  let K := Section2.weylExponent F
  have hK : 0 < K := by dsimp [K, Section2.weylExponent]; positivity
  obtain ⟨C, N₀, hC, hN₀, hw⟩ := hW hF D hD
  refine ⟨C * 4 ^ (1 / K), N₀, by positivity, hN₀, ?_⟩
  intro N H α hN hH hHu a q hq hcop happ h1 h2 h3
  have hN3 := hN₀.trans hN
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hw' := hw N H α hN hH hHu a q hq hcop happ
  have hfour : -2 * D + (F.natDegree : ℝ) ^ 2 - 2 = -B / 4 := by dsimp [D]; ring
  rw [hfour] at hw'
  have hbase : 1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree +
      Real.log N ^ (-B / 4) ≤ 4 * Real.log N ^ (-B / 4) := by linarith
  have hnon : 0 ≤ 1 / (q : ℝ) + 1 / H + (q : ℝ) / H ^ F.natDegree +
      Real.log N ^ (-B / 4) := by positivity
  have hroot := Real.rpow_le_rpow hnon hbase (show 0 ≤ 1 / K by positivity)
  calc
    _ ≤ C * H * (4 * Real.log N ^ (-B / 4)) ^ (1 / K) *
      Real.log N ^ ((D + 1) / K) := by
      exact hw'.trans (by gcongr)
    _ = _ := by
      rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 4) (Real.rpow_nonneg hL.le _),
        ← Real.rpow_mul hL.le]
      have hexp : (-B / 4) * (1 / K) + (D + 1) / K =
          -(B - 4 * (F.natDegree : ℝ) ^ 2) / (8 * K) := by dsimp [D]; ring
      calc
        _ = (C * 4 ^ (1 / K)) * H *
            (Real.log N ^ ((-B / 4) * (1 / K)) * Real.log N ^ ((D + 1) / K)) := by ring
        _ = _ := by rw [← Real.rpow_add hL, hexp]

/-- The reciprocal interval length satisfies the secondary arc threshold. -/
private theorem wl_inv_H (F : ℤ[X]) (hF : Admissible F) (ε B : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      1 / H ≤ Real.log N ^ (-B / 4) := by
  let δ := 1 / (3 * (F.natDegree : ℝ)) + ε
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have hb := (isLittleO_log_rpow_rpow_atTop (B / 4) hδ).bound (by norm_num : (0 : ℝ) < 1)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp hb
  refine ⟨max 3 N₁, le_max_left _ _, ?_⟩
  intro N H hN hH
  have hN3 : 3 ≤ N := (le_max_left _ _).trans hN
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH
  have hlog := hN₁ N ((le_max_right _ _).trans hN)
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hL.le _),
    abs_of_nonneg (Real.rpow_nonneg hN0.le _), one_mul] at hlog
  have hlogH : Real.log N ^ (B / 4) ≤ H := hlog.trans hH
  rw [show -B / 4 = -(B / 4) by ring, Real.rpow_neg hL.le]
  simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hL _) hlogH

/-- The secondary order is at least two and its square reciprocal exceeds sixteen. -/
private theorem wl_order_bounds (F : ℤ[X]) (hF : Admissible F) (ε B : ℝ) (hε : 0 < ε) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      16 ≤ H ^ F.natDegree * Real.log N ^ (-B / 4) ∧ 2 ≤ fareyOrder F N H B := by
  have ht2 := (isLittleO_log_rpow_rpow_atTop (B / 4) (by norm_num : (0 : ℝ) < 1 / 3)).bound
    (by norm_num : (0 : ℝ) < 1 / 16)
  obtain ⟨N₂, hN₂⟩ := Filter.eventually_atTop.mp ht2
  refine ⟨max 3 N₂, le_max_left _ _, ?_⟩
  intro N H hN hH
  have hN3 : 3 ≤ N := le_trans (le_max_left _ _) hN
  have hN1 : 1 ≤ N := by linarith
  have hN0 : 0 < N := by linarith
  have hlog : 0 < Real.log N := Real.log_pos (by linarith)
  have hb2 := hN₂ N (le_trans (le_max_right _ _) hN)
  simp only [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg hlog.le (B / 4)),
    abs_of_nonneg (Real.rpow_nonneg hN0.le (1 / 3))] at hb2
  have hk : (0 : ℝ) < F.natDegree := by exact_mod_cast (lt_of_lt_of_le Nat.zero_lt_one hF.1)
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH
  have hpow : N ^ ((1 / (3 * (F.natDegree : ℝ)) + ε) * F.natDegree) ≤ H ^ F.natDegree := by
    have h := pow_le_pow_left₀ (Real.rpow_nonneg hN0.le _) hH F.natDegree
    rwa [← Real.rpow_natCast, ← Real.rpow_mul hN0.le] at h
  have hbase : (1 : ℝ) / 3 ≤ (1 / (3 * (F.natDegree : ℝ)) + ε) * F.natDegree := by
    have hid : 1 / (3 * (F.natDegree : ℝ)) * F.natDegree = (1 : ℝ) / 3 := by field_simp
    rw [add_mul, hid]
    have := mul_pos hε hk
    linarith
  have hlow := (Real.rpow_le_rpow_of_exponent_le hN1 hbase).trans hpow
  have harg : 16 ≤ H ^ F.natDegree * Real.log N ^ (-B / 4) := by
    have hL : 0 < Real.log N ^ (B / 4) := Real.rpow_pos_of_pos hlog _
    have hratio : 16 ≤ H ^ F.natDegree / Real.log N ^ (B / 4) := by
      apply (le_div_iff₀ hL).mpr
      linarith
    rw [show -B / 4 = -(B / 4) by ring, Real.rpow_neg hlog.le, ← div_eq_mul_inv]
    exact hratio
  unfold fareyOrder
  have hs : 4 ≤ Real.sqrt (H ^ F.natDegree * Real.log N ^ (-B / 4)) := by
    exact (Real.le_sqrt (by norm_num) (by positivity)).mpr (by norm_num; exact harg)
  exact ⟨harg, by linarith⟩

/-- The short interval prime mass set is bounded above. -/
private theorem shortMass_bddAbove' (M : ℕ) (N B Q : ℝ) :
    BddAbove {x | ∃ t : ℝ, x =
      ∫ α in minorArcs N B ∩ Set.Icc t (t + 1 / (4 * Q ^ 2)), ‖primeSum M α‖ ^ 2} := by
  refine ⟨(Real.log 4 + 4) * (M : ℝ) * Real.log ((M : ℝ) + 1), ?_⟩
  rintro x ⟨t, rfl⟩
  have hcont : Continuous (fun α : ℝ => ‖primeSum M α‖ ^ 2) := by
    unfold primeSum Kernel.e
    fun_prop
  calc
    _ ≤ ∫ α in Set.Icc (0 : ℝ) 1, ‖primeSum M α‖ ^ 2 := by
      apply setIntegral_mono_set hcont.integrableOn_Icc
      · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
      · exact Filter.Eventually.of_forall (fun _ h => Set.diff_subset h.1)
    _ ≤ _ := Parseval103.prime_second_moment M

/-- Every window integral is bounded by the short interval prime mass. -/
private theorem le_shortMass (M : ℕ) (N B Q t : ℝ) :
    (∫ α in minorArcs N B ∩ Set.Icc t (t + 1 / (4 * Q ^ 2)), ‖primeSum M α‖ ^ 2) ≤
      shortMass M N B Q := by
  unfold shortMass
  exact le_csSup (shortMass_bddAbove' M N B Q) ⟨t, rfl⟩

/-- A finite union of sets carries at most the sum of the set integrals. -/
private theorem integral_iUnion_finset_le {ι : Type*} (A : ι → Set ℝ) (t : Set ℝ)
    (g : ℝ → ℝ) (hInt : IntegrableOn g t) (hg : ∀ x, 0 ≤ g x)
    (hmeas : ∀ i, MeasurableSet (t ∩ A i)) (s : Finset ι) :
    (∫ x in t ∩ (⋃ i ∈ s, A i), g x) ≤ ∑ i ∈ s, ∫ x in t ∩ A i, g x := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert j s hj ih =>
      have hU : (⋃ i ∈ insert j s, A i) = A j ∪ ⋃ i ∈ s, A i :=
        Finset.set_biUnion_insert j s A
      rw [hU, Finset.sum_insert hj]
      have hinter : t ∩ ⋃ i ∈ s, A i = ⋃ i ∈ s, (t ∩ A i) := by
        ext x
        simp only [Set.mem_inter_iff, Set.mem_iUnion, exists_prop]
        tauto
      have hmeasU : MeasurableSet (t ∩ ⋃ i ∈ s, A i) := by
        rw [hinter]
        exact Finset.measurableSet_biUnion s (fun i _ => hmeas i)
      have hcover : t ∩ (A j ∪ ⋃ i ∈ s, A i) ⊆
          (t ∩ A j) ∪ (t ∩ ⋃ i ∈ s, A i) := by
        rintro x ⟨hxt, hx | hx⟩
        · exact Or.inl ⟨hxt, hx⟩
        · exact Or.inr ⟨hxt, hx⟩
      have hintU : IntegrableOn g (t ∩ ⋃ i ∈ s, A i) := hInt.mono_set Set.inter_subset_left
      calc
        _ ≤ (∫ x in t ∩ A j, g x) + ∫ x in t ∩ ⋃ i ∈ s, A i, g x :=
          Farey103.integral_two_cover g hg (t ∩ (A j ∪ ⋃ i ∈ s, A i)) (t ∩ A j)
            (t ∩ ⋃ i ∈ s, A i) (hmeas j) hmeasU
            (hInt.mono_set Set.inter_subset_left) hintU hcover
        _ ≤ (∫ x in t ∩ A j, g x) + ∑ i ∈ s, ∫ x in t ∩ A i, g x := by
          exact add_le_add le_rfl ih

/-- Equation 9 on the complement of the secondary rational arcs. -/
private theorem wl_weyl_secondary (F : ℤ[X]) (hF : Admissible F)
    (hW : Section2.WeylLemma F) (ε B : ℝ) (hε : 0 < ε) (hB : 0 < B)
    (hD : 0 < B / 8 + (F.natDegree : ℝ) ^ 2 / 2 - 1) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H α : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      (∀ q : ℕ, 0 < q → (q : ℝ) ≤ Real.log N ^ (B / 4) →
        ∀ a : ℤ, Nat.Coprime a.natAbs q →
          1 / ((q : ℝ) * (H ^ F.natDegree * Real.log N ^ (-B / 4))) <
            |α - (a : ℝ) / q|) →
      ‖Section2.polynomialKernel F N H α‖ ≤ C * H *
        Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) / (8 * Section2.weylExponent F)) := by
  obtain ⟨C, NW, hC, hNW, hw⟩ := wl_weyl_decay F hF hW B hD
  obtain ⟨NH, hNH, hh⟩ := wl_inv_H F hF ε B hε
  obtain ⟨NG, hNG, hg⟩ := wl_order_bounds F hF ε B hε
  refine ⟨C, NW + NH + NG + 3, hC, by linarith, ?_⟩
  intro N H α hN hH hHu hminor
  have hNW' : NW ≤ N := by linarith
  have hNH' : NH ≤ N := by linarith
  have hNG' : NG ≤ N := by linarith
  have hN3 : 3 ≤ N := hNW.trans hNW'
  have hN0 : 0 < N := by linarith
  have hN1 : 1 ≤ N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH
  have hH1 : 1 ≤ H := (Real.one_le_rpow hN1 (by positivity)).trans hH
  let Q := H ^ F.natDegree * Real.log N ^ (-B / 4)
  have hQ0 : 0 < Q := by dsimp [Q]; positivity
  have hQ1 : 1 ≤ Q := by
    have h16 := (hg N H hNG' hH).1
    dsimp [Q]
    linarith
  obtain ⟨q, hq, hqQ, a, hcop, happ⟩ := Farey103.dirichlet_real_order α Q hQ1
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hsmall : ¬ (q : ℝ) ≤ Real.log N ^ (B / 4) := by
    intro hbad
    exact (not_lt_of_ge happ.le) (hminor q hq hbad a hcop)
  have hqLarge : Real.log N ^ (B / 4) ≤ q := (lt_of_not_ge hsmall).le
  have happ' : |α - (a : ℝ) / q| ≤ 1 / (q : ℝ) ^ 2 := by
    refine happ.le.trans ?_
    apply one_div_le_one_div_of_le (sq_pos_of_pos hq0)
    nlinarith
  apply hw N H α hNW' hH1 hHu a q hq hcop happ'
  · rw [show -B / 4 = -(B / 4) by ring, Real.rpow_neg hL.le]
    simpa only [one_div] using one_div_le_one_div_of_le (Real.rpow_pos_of_pos hL _) hqLarge
  · exact hh N H hNH' hH
  · exact (div_le_iff₀ (pow_pos hH0 _)).mpr (by simpa [Q, mul_comm] using hqQ)

set_option maxHeartbeats 1600000 in
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
  classical
  obtain ⟨C₁, N₁, hC₁, hN₁, hmom⟩ := Parseval103.prime_second_moment_scaled c hc
  obtain ⟨NO, hNO, hord⟩ := wl_order_bounds F hF ε B hε
  have hexp0 : (0 : ℝ) ≤ Real.exp 1 := (Real.exp_pos 1).le
  by_cases hD : 0 < B / 8 + (F.natDegree : ℝ) ^ 2 / 2 - 1
  · obtain ⟨C₂, N₂, hC₂, hN₂, hdecay⟩ := wl_weyl_secondary F hF hW ε B hε hB hD
    refine ⟨max 512 (max (2 * C₁) (C₁ * C₂)), N₁ + (N₂ + (NO + (Real.exp 1 + 3))),
      by positivity, by linarith, ?_⟩
    intro N H hN hH hHu ξ hξ
    have hN1le : N₁ ≤ N := by linarith
    have hN2le : N₂ ≤ N := by linarith
    have hNOle : NO ≤ N := by linarith
    have hNexp : Real.exp 1 ≤ N := by linarith
    have hN3 : 3 ≤ N := hN₁.trans hN1le
    have hN0 : 0 < N := by linarith
    have hNgt1 : 1 ≤ N := by linarith
    have hL : 0 < Real.log N := Real.log_pos (by linarith)
    have hL1 : 1 ≤ Real.log N := by
      have h := Real.log_le_log (Real.exp_pos 1) hNexp
      simpa using h
    have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH
    have hH1 : 1 ≤ H := (Real.one_le_rpow hNgt1 (by positivity)).trans hH
    have hξb : |ξ| ≤ 1 := by
      have h := Set.diff_subset hξ
      rw [abs_le]
      exact ⟨by linarith [h.1], by linarith [h.2]⟩
    set Q : ℝ := fareyOrder F N H B with hQ
    set Qbar : ℝ := H ^ F.natDegree * Real.log N ^ (-B / 4) with hQbar
    obtain ⟨hQbar16, hQ2⟩ := hord N H hNOle hH
    have hQbar0 : 0 < Qbar := by rw [hQbar]; positivity
    have hQ0 : 0 < Q := by linarith
    have hQsq : 4 * Q ^ 2 = Qbar := by
      rw [hQ, hQbar]
      unfold fareyOrder
      have hpos : 0 < H ^ F.natDegree * Real.log N ^ (-B / 4) := by positivity
      rw [div_pow, Real.sq_sqrt hpos.le]
      ring
    have hquarter : 1 / (4 * Q ^ 2) = 1 / Qbar := by rw [hQsq]
    let Qlim : ℕ := ⌈Real.log N ^ (B / 4)⌉₊
    let Arc : ℕ × ℕ → Set ℝ := fun p =>
      Set.Icc (((p.2 : ℝ) - 3 * (Qlim : ℝ)) / (p.1 : ℝ) + ξ - 1 / ((p.1 : ℝ) * Qbar))
        (((p.2 : ℝ) - 3 * (Qlim : ℝ)) / (p.1 : ℝ) + ξ + 1 / ((p.1 : ℝ) * Qbar))
    let T : Finset (ℕ × ℕ) := (Finset.Icc 1 Qlim) ×ˢ Finset.range (6 * Qlim + 1)
    let Sec : Set ℝ := ⋃ p ∈ T, Arc p
    let g : ℝ → ℝ := fun α => ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 *
      ‖Section2.polynomialKernel F N H (α - ξ)‖
    have hcontS : Continuous (fun α : ℝ => ‖primeSum ⌊c * N⌋₊ α‖ ^ 2) := by
      unfold primeSum Kernel.e
      fun_prop
    have hcontK : Continuous (fun α : ℝ => ‖Section2.polynomialKernel F N H (α - ξ)‖) := by
      unfold Section2.polynomialKernel Kernel.e
      fun_prop
    have hcontg : Continuous g := hcontS.mul hcontK
    have hmajor : MeasurableSet (majorArcs N B) := by unfold majorArcs; measurability
    have hminorMeas : MeasurableSet (minorArcs N B) := measurableSet_Icc.diff hmajor
    have hIntg : IntegrableOn g (minorArcs N B) := hcontg.integrableOn_Icc.mono_set Set.diff_subset
    have hg_nonneg : ∀ α : ℝ, 0 ≤ g α := fun α => mul_nonneg (sq_nonneg _) (norm_nonneg _)
    have hKle : ∀ α : ℝ, ‖Section2.polynomialKernel F N H (α - ξ)‖ ≤ H + 1 := by
      intro α
      have hcard := card_win_le F hN0.le hH0.le
      calc ‖Section2.polynomialKernel F N H (α - ξ)‖
          = ‖∑ n ∈ win F N H, Kernel.e ((Fv F n : ℝ) * (α - ξ))‖ := rfl
        _ ≤ ∑ n ∈ win F N H, ‖Kernel.e ((Fv F n : ℝ) * (α - ξ))‖ := norm_sum_le _ _
        _ = ((win F N H).card : ℝ) := by simp [Kernel.e, Complex.norm_exp]
        _ ≤ H + 1 := hcard
    have hminorSq : (∫ α in minorArcs N B, ‖primeSum ⌊c * N⌋₊ α‖ ^ 2) ≤
        C₁ * N * Real.log N := by
      refine le_trans ?_ (hmom N hN1le)
      apply setIntegral_mono_set hcontS.integrableOn_Icc
      · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
      · exact Filter.Eventually.of_forall (fun _ h => Set.diff_subset h)
    have harc_le : ∀ p ∈ T,
        (∫ α in minorArcs N B ∩ Arc p, g α) ≤ 8 * (H + 1) * shortMass ⌊c * N⌋₊ N B Q := by
      rintro ⟨q, j⟩ hp
      obtain ⟨hpq, hpj⟩ := Finset.mem_product.mp hp
      have hq1 : 1 ≤ q := (Finset.mem_Icc.mp hpq).1
      have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
      set x0 : ℝ := ((j : ℝ) - 3 * (Qlim : ℝ)) / (q : ℝ) + ξ with hx0
      have hstep1 : (∫ α in minorArcs N B ∩ Arc (q, j), g α) ≤
          (H + 1) * ∫ α in minorArcs N B ∩ Arc (q, j), ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := by
        calc (∫ α in minorArcs N B ∩ Arc (q, j), g α)
            ≤ ∫ α in minorArcs N B ∩ Arc (q, j),
                (H + 1) * ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := by
              apply integral_mono
              · exact hIntg.mono_set Set.inter_subset_left
              · exact (continuous_const.mul hcontS).integrableOn_Icc.mono_set
                  (Set.inter_subset_left.trans Set.diff_subset)
              · intro α
                dsimp only [g]
                calc ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 * ‖Section2.polynomialKernel F N H (α - ξ)‖
                    ≤ ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 * (H + 1) :=
                      mul_le_mul_of_nonneg_left (hKle α) (sq_nonneg _)
                  _ = (H + 1) * ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := by ring
          _ = (H + 1) * ∫ α in minorArcs N B ∩ Arc (q, j), ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 :=
              integral_const_mul _ _
      have hrle : 1 / ((q : ℝ) * Qbar) ≤ 1 / (4 * Q ^ 2) := by
        rw [hquarter]
        apply one_div_le_one_div_of_le (by positivity)
        nlinarith [hqR, hQbar16]
      have hsub : Arc (q, j) ⊆ Set.Icc (x0 - 1 / (4 * Q ^ 2)) (x0 + 1 / (4 * Q ^ 2)) := by
        intro α hα
        have hα' : ((j : ℝ) - 3 * (Qlim : ℝ)) / (q : ℝ) + ξ - 1 / ((q : ℝ) * Qbar) ≤ α ∧
            α ≤ ((j : ℝ) - 3 * (Qlim : ℝ)) / (q : ℝ) + ξ + 1 / ((q : ℝ) * Qbar) := hα
        rw [hx0]
        constructor <;> linarith [hα'.1, hα'.2, hrle]
      have hcover : minorArcs N B ∩ Arc (q, j) ⊆
          (minorArcs N B ∩ Set.Icc (x0 - 1 / (4 * Q ^ 2)) x0) ∪
            (minorArcs N B ∩ Set.Icc x0 (x0 + 1 / (4 * Q ^ 2))) := by
        rintro α ⟨hαm, hαA⟩
        have h := hsub hαA
        by_cases hle : α ≤ x0
        · exact Or.inl ⟨hαm, h.1, hle⟩
        · exact Or.inr ⟨hαm, le_of_lt (not_le.mp hle), h.2⟩
      have hmeasu : MeasurableSet (minorArcs N B ∩ Set.Icc (x0 - 1 / (4 * Q ^ 2)) x0) :=
        hminorMeas.inter measurableSet_Icc
      have hmeasv : MeasurableSet (minorArcs N B ∩ Set.Icc x0 (x0 + 1 / (4 * Q ^ 2))) :=
        hminorMeas.inter measurableSet_Icc
      have hintS : IntegrableOn (fun α : ℝ => ‖primeSum ⌊c * N⌋₊ α‖ ^ 2) (minorArcs N B) :=
        hcontS.integrableOn_Icc.mono_set Set.diff_subset
      have htwo := Farey103.integral_two_cover (fun α : ℝ => ‖primeSum ⌊c * N⌋₊ α‖ ^ 2)
        (fun _ => sq_nonneg _) (minorArcs N B ∩ Arc (q, j))
        (minorArcs N B ∩ Set.Icc (x0 - 1 / (4 * Q ^ 2)) x0)
        (minorArcs N B ∩ Set.Icc x0 (x0 + 1 / (4 * Q ^ 2))) hmeasu hmeasv
        (hintS.mono_set Set.inter_subset_left) (hintS.mono_set Set.inter_subset_left) hcover
      have hw1 : (∫ α in minorArcs N B ∩ Set.Icc (x0 - 1 / (4 * Q ^ 2)) x0,
          ‖primeSum ⌊c * N⌋₊ α‖ ^ 2) ≤ shortMass ⌊c * N⌋₊ N B Q := by
        have h := le_shortMass ⌊c * N⌋₊ N B Q (x0 - 1 / (4 * Q ^ 2))
        rwa [show x0 - 1 / (4 * Q ^ 2) + 1 / (4 * Q ^ 2) = x0 by ring] at h
      have hw2 : (∫ α in minorArcs N B ∩ Set.Icc x0 (x0 + 1 / (4 * Q ^ 2)),
          ‖primeSum ⌊c * N⌋₊ α‖ ^ 2) ≤ shortMass ⌊c * N⌋₊ N B Q :=
        le_shortMass ⌊c * N⌋₊ N B Q x0
      have hstep2 : (∫ α in minorArcs N B ∩ Arc (q, j), ‖primeSum ⌊c * N⌋₊ α‖ ^ 2) ≤
          2 * shortMass ⌊c * N⌋₊ N B Q := by
        calc _ ≤ (∫ α in minorArcs N B ∩ Set.Icc (x0 - 1 / (4 * Q ^ 2)) x0,
              ‖primeSum ⌊c * N⌋₊ α‖ ^ 2) +
              ∫ α in minorArcs N B ∩ Set.Icc x0 (x0 + 1 / (4 * Q ^ 2)),
                ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := htwo
          _ ≤ shortMass ⌊c * N⌋₊ N B Q + shortMass ⌊c * N⌋₊ N B Q := add_le_add hw1 hw2
          _ = 2 * shortMass ⌊c * N⌋₊ N B Q := by ring
      have hs0 : 0 ≤ shortMass ⌊c * N⌋₊ N B Q := shortMass_nonneg _ _ _ _
      calc (∫ α in minorArcs N B ∩ Arc (q, j), g α)
          ≤ (H + 1) * ∫ α in minorArcs N B ∩ Arc (q, j), ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := hstep1
        _ ≤ (H + 1) * (2 * shortMass ⌊c * N⌋₊ N B Q) :=
            mul_le_mul_of_nonneg_left hstep2 (by linarith : (0 : ℝ) ≤ H + 1)
        _ ≤ 8 * (H + 1) * shortMass ⌊c * N⌋₊ N B Q := by nlinarith [hs0]
    have hSecMeas : ∀ p : ℕ × ℕ, MeasurableSet (minorArcs N B ∩ Arc p) :=
      fun p => hminorMeas.inter measurableSet_Icc
    have hsum_le : (∫ α in minorArcs N B ∩ Sec, g α) ≤
        ∑ p ∈ T, ∫ α in minorArcs N B ∩ Arc p, g α :=
      integral_iUnion_finset_le Arc (minorArcs N B) g hIntg hg_nonneg hSecMeas T
    have hQlimR : (Qlim : ℝ) ≤ 2 * Real.log N ^ (B / 4) := by
      have h2 : (Qlim : ℝ) ≤ Real.log N ^ (B / 4) + 1 := by
        have hp : (0 : ℝ) ≤ Real.log N ^ (B / 4) := (Real.rpow_pos_of_pos hL _).le
        have h := Nat.ceil_lt_add_one hp
        simp only [Qlim]
        exact h.le
      have h1 : (1 : ℝ) ≤ Real.log N ^ (B / 4) := Real.one_le_rpow hL1 (by positivity)
      linarith
    have hQlim1 : 1 ≤ Qlim := by
      have h2 : 0 < Real.log N ^ (B / 4) := Real.rpow_pos_of_pos hL _
      have hpos : 0 < Qlim := by
        simp only [Qlim]
        exact Nat.ceil_pos.mpr h2
      omega
    have hcardT : (T.card : ℝ) ≤ 28 * Real.log N ^ (B / 2) := by
      have hcardN : (Finset.Icc 1 Qlim).card ≤ Qlim := by
        rw [Nat.card_Icc]
        omega
      have hcardj : (Finset.range (6 * Qlim + 1)).card ≤ 7 * Qlim := by
        rw [Finset.card_range]
        omega
      have hcardT' : T.card ≤ Qlim * (7 * Qlim) := by
        have hc : T.card = (Finset.Icc 1 Qlim).card * (Finset.range (6 * Qlim + 1)).card := by
          simp only [T, Finset.card_product]
        rw [hc]
        exact Nat.mul_le_mul hcardN hcardj
      have hsq : Real.log N ^ (B / 2) = Real.log N ^ (B / 4) * Real.log N ^ (B / 4) := by
        rw [← Real.rpow_add hL]
        congr 1
        ring
      have hcast : ((Qlim * (7 * Qlim) : ℕ) : ℝ) = 7 * (Qlim : ℝ) * (Qlim : ℝ) := by
        push_cast
        ring
      have hstep1 : (T.card : ℝ) ≤ 7 * (Qlim : ℝ) * (Qlim : ℝ) := by
        rw [← hcast]
        exact_mod_cast hcardT'
      have hstep2 : 7 * (Qlim : ℝ) * (Qlim : ℝ) ≤ 7 * (2 * Real.log N ^ (B / 4)) *
          (2 * Real.log N ^ (B / 4)) := by
        have h0 : (0 : ℝ) ≤ (Qlim : ℝ) := Nat.cast_nonneg Qlim
        apply mul_le_mul
        · nlinarith
        · exact hQlimR
        · exact h0
        · positivity
      calc (T.card : ℝ) ≤ 7 * (Qlim : ℝ) * (Qlim : ℝ) := hstep1
        _ ≤ 7 * (2 * Real.log N ^ (B / 4)) * (2 * Real.log N ^ (B / 4)) := hstep2
        _ = 28 * Real.log N ^ (B / 2) := by rw [hsq]; ring
    have hTsum : ∑ p ∈ T, (∫ α in minorArcs N B ∩ Arc p, g α) ≤
        512 * H * Real.log N ^ (B / 2) * shortMass ⌊c * N⌋₊ N B Q := by
      have hs0 : 0 ≤ shortMass ⌊c * N⌋₊ N B Q := shortMass_nonneg _ _ _ _
      have hL2 : 0 < Real.log N ^ (B / 2) := Real.rpow_pos_of_pos hL _
      have hstep : ∑ p ∈ T, (∫ α in minorArcs N B ∩ Arc p, g α) ≤
          ∑ p ∈ T, (8 * (H + 1) * shortMass ⌊c * N⌋₊ N B Q) := Finset.sum_le_sum harc_le
      have hconst : ∑ p ∈ T, (8 * (H + 1) * shortMass ⌊c * N⌋₊ N B Q) =
          (T.card : ℝ) * (8 * (H + 1) * shortMass ⌊c * N⌋₊ N B Q) := by
        rw [Finset.sum_const, nsmul_eq_mul]
      rw [hconst] at hstep
      have hmono : (T.card : ℝ) * (8 * (H + 1) * shortMass ⌊c * N⌋₊ N B Q) ≤
          (28 * Real.log N ^ (B / 2)) * (8 * (H + 1) * shortMass ⌊c * N⌋₊ N B Q) := by
        apply mul_le_mul_of_nonneg_right hcardT
        have hsa := shortMass_nonneg ⌊c * N⌋₊ N B Q
        have hsb : (0 : ℝ) ≤ 8 * (H + 1) := by linarith
        exact mul_nonneg hsb hsa
      have hfin : (28 * Real.log N ^ (B / 2)) * (8 * (H + 1) * shortMass ⌊c * N⌋₊ N B Q) ≤
          512 * H * Real.log N ^ (B / 2) * shortMass ⌊c * N⌋₊ N B Q := by
        have hH2 : H + 1 ≤ 2 * H := by linarith
        have e1 : (28 * Real.log N ^ (B / 2)) * (8 * (H + 1) * shortMass ⌊c * N⌋₊ N B Q) =
            224 * Real.log N ^ (B / 2) * (H + 1) * shortMass ⌊c * N⌋₊ N B Q := by ring
        rw [e1]
        have hLH : 0 ≤ Real.log N ^ (B / 2) * (H + 1) * shortMass ⌊c * N⌋₊ N B Q := by
          have hsa := shortMass_nonneg ⌊c * N⌋₊ N B Q
          have hsb : (0 : ℝ) ≤ Real.log N ^ (B / 2) * (H + 1) := by positivity
          exact mul_nonneg hsb hsa
        have hLH2 : Real.log N ^ (B / 2) * (H + 1) * shortMass ⌊c * N⌋₊ N B Q ≤
            Real.log N ^ (B / 2) * (2 * H) * shortMass ⌊c * N⌋₊ N B Q := by
          apply mul_le_mul_of_nonneg_right _ hs0
          apply mul_le_mul_of_nonneg_left hH2 hL2.le
        nlinarith [hLH, hLH2]
      exact hstep.trans (hmono.trans hfin)
    have hmeasSec : MeasurableSet Sec := by
      simp only [Sec]
      exact Finset.measurableSet_biUnion T (fun p _ => measurableSet_Icc)
    have hT_le : (∫ α in minorArcs N B \ Sec, g α) ≤
        C₂ * H * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
          (8 * Section2.weylExponent F)) * (C₁ * N * Real.log N) := by
      have hhyp : ∀ α ∈ minorArcs N B \ Sec, ∀ q : ℕ, 0 < q →
          (q : ℝ) ≤ Real.log N ^ (B / 4) → ∀ a : ℤ, Nat.Coprime a.natAbs q →
          1 / ((q : ℝ) * Qbar) < |(α - ξ) - (a : ℝ) / q| := by
        intro α hα q hq hqq a hcop
        by_contra hcon
        push Not at hcon
        have hαI : α ∈ Set.Icc (0 : ℝ) 1 := Set.diff_subset hα.1
        have hqQlim : q ≤ Qlim := by
          have h1 : (q : ℝ) ≤ (⌈Real.log N ^ (B / 4)⌉₊ : ℝ) := hqq.trans (Nat.le_ceil _)
          have h2 : (q : ℝ) ≤ (Qlim : ℝ) := by
            simp only [Qlim]
            exact h1
          exact_mod_cast h2
        have hqR : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
        have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
        have hprod : 1 ≤ (q : ℝ) * Qbar := by nlinarith [hqR, hQbar16]
        have hsmall : 1 / ((q : ℝ) * Qbar) ≤ 1 := by
          rw [div_le_one (by positivity)]
          exact hprod
        have hβ : |α - ξ| ≤ 2 := by
          have h1 : |α| ≤ 1 := by
            rw [abs_le]
            exact ⟨by linarith [hαI.1], by linarith [hαI.2]⟩
          calc |α - ξ| ≤ |α| + |ξ| := abs_sub α ξ
            _ ≤ 2 := by linarith [h1, hξb]
        have hbound : |(a : ℝ) / q| ≤ |α - ξ| + 1 / ((q : ℝ) * Qbar) := by
          have h2 : |(a : ℝ) / q| ≤ |(a : ℝ) / q - (α - ξ)| + |α - ξ| := by
            have h := abs_add_le ((a : ℝ) / q - (α - ξ)) (α - ξ)
            rwa [show ((a : ℝ) / q - (α - ξ)) + (α - ξ) = (a : ℝ) / q by ring] at h
          have h3 : |(a : ℝ) / q - (α - ξ)| = |(α - ξ) - (a : ℝ) / q| := abs_sub_comm _ _
          linarith [h2, h3, hcon]
        have habs : |(a : ℝ)| ≤ 3 * (Qlim : ℝ) := by
          have hmul : |(a : ℝ) / q| * (q : ℝ) = |(a : ℝ)| := by
            rw [abs_div, abs_of_pos hqpos]
            field_simp
          have h1 : |(a : ℝ) / q| * (q : ℝ) ≤ (|α - ξ| + 1 / ((q : ℝ) * Qbar)) * (q : ℝ) :=
            mul_le_mul_of_nonneg_right hbound hqpos.le
          rw [hmul] at h1
          have h2 : |α - ξ| + 1 / ((q : ℝ) * Qbar) ≤ 3 := by linarith
          have h3 : (|α - ξ| + 1 / ((q : ℝ) * Qbar)) * (q : ℝ) ≤ 3 * (q : ℝ) :=
            mul_le_mul_of_nonneg_right h2 hqpos.le
          have h4 : (q : ℝ) ≤ (Qlim : ℝ) := by exact_mod_cast hqQlim
          linarith
        have hlow : -(3 * (Qlim : ℝ)) ≤ (a : ℝ) := (abs_le.mp habs).1
        have hhigh : (a : ℝ) ≤ 3 * (Qlim : ℝ) := (abs_le.mp habs).2
        have hnonneg : (0 : ℤ) ≤ a + 3 * (Qlim : ℤ) := by
          have hh : (-(3 * (Qlim : ℤ))) ≤ a := by exact_mod_cast hlow
          linarith
        have htop : a + 3 * (Qlim : ℤ) ≤ 6 * (Qlim : ℤ) := by
          have hh : a ≤ 3 * (Qlim : ℤ) := by exact_mod_cast hhigh
          linarith
        have hcast : (((a + 3 * (Qlim : ℤ)).toNat : ℤ)) = a + 3 * (Qlim : ℤ) :=
          Int.toNat_of_nonneg hnonneg
        have hlt : (a + 3 * (Qlim : ℤ)).toNat < 6 * Qlim + 1 := by
          have h1 : ((a + 3 * (Qlim : ℤ)).toNat : ℤ) ≤ 6 * (Qlim : ℤ) := by
            rw [hcast]
            exact htop
          have h2 : (a + 3 * (Qlim : ℤ)).toNat ≤ 6 * Qlim := by exact_mod_cast h1
          omega
        have hmem : (q, (a + 3 * (Qlim : ℤ)).toNat) ∈ T := by
          simp only [T, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
          exact ⟨⟨hq, hqQlim⟩, hlt⟩
        have harc_eq : ((a + 3 * (Qlim : ℤ)).toNat : ℝ) - 3 * (Qlim : ℝ) = (a : ℝ) := by
          have h1 : ((((a + 3 * (Qlim : ℤ)).toNat : ℤ)) : ℝ) = ((a + 3 * (Qlim : ℤ) : ℤ) : ℝ) := by
            rw [hcast]
          push_cast at h1
          linarith
        have hmemArc : α ∈ Arc (q, (a + 3 * (Qlim : ℤ)).toNat) := by
          have e : ((a + 3 * (Qlim : ℤ)).toNat : ℝ) - 3 * (Qlim : ℝ) = (a : ℝ) := harc_eq
          simp only [Arc, e, Set.mem_Icc]
          rw [abs_le] at hcon
          constructor <;> linarith [hcon.1, hcon.2]
        have hmemSec : α ∈ Sec := by
          simp only [Sec]
          exact Set.mem_iUnion.mpr ⟨(q, (a + 3 * (Qlim : ℤ)).toNat),
            Set.mem_iUnion.mpr ⟨hmem, hmemArc⟩⟩
        exact hα.2 hmemSec
      have hpoint : ∀ α ∈ minorArcs N B \ Sec,
          ‖Section2.polynomialKernel F N H (α - ξ)‖ ≤
            C₂ * H * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
              (8 * Section2.weylExponent F)) := by
        intro α hα
        refine hdecay N H (α - ξ) hN2le hH hHu ?_
        intro q hq hqq a hcop
        have h := hhyp α hα q hq hqq a hcop
        rwa [← hQbar]
      have hcontW : Continuous (fun α : ℝ =>
          (C₂ * H * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
            (8 * Section2.weylExponent F))) * ‖primeSum ⌊c * N⌋₊ α‖ ^ 2) :=
        continuous_const.mul hcontS
      have hce : (0 : ℝ) ≤ C₂ * H * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
          (8 * Section2.weylExponent F)) := by positivity
      calc (∫ α in minorArcs N B \ Sec, g α)
          ≤ ∫ α in minorArcs N B \ Sec, (C₂ * H * Real.log N ^
              (-(B - 4 * (F.natDegree : ℝ) ^ 2) / (8 * Section2.weylExponent F))) *
                ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := by
            apply integral_mono_ae
            · exact hIntg.mono_set Set.diff_subset
            · exact hcontW.integrableOn_Icc.mono_set (Set.diff_subset.trans Set.diff_subset)
            · filter_upwards [ae_restrict_mem (hminorMeas.diff hmeasSec)] with α hα
              dsimp only [g]
              calc ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 * ‖Section2.polynomialKernel F N H (α - ξ)‖
                  ≤ ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 * (C₂ * H * Real.log N ^
                      (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
                        (8 * Section2.weylExponent F))) :=
                    mul_le_mul_of_nonneg_left (hpoint α hα) (sq_nonneg _)
                _ = (C₂ * H * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
                      (8 * Section2.weylExponent F))) * ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := by ring
        _ = (C₂ * H * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
              (8 * Section2.weylExponent F))) * ∫ α in minorArcs N B \ Sec,
                ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := integral_const_mul _ _
        _ ≤ (C₂ * H * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
              (8 * Section2.weylExponent F))) * (C₁ * N * Real.log N) := by
            apply mul_le_mul_of_nonneg_left _ hce
            calc (∫ α in minorArcs N B \ Sec, ‖primeSum ⌊c * N⌋₊ α‖ ^ 2)
                ≤ ∫ α in Set.Icc (0 : ℝ) 1, ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 :=
                  setIntegral_mono_set hcontS.integrableOn_Icc
                    (Filter.Eventually.of_forall (fun _ => sq_nonneg _))
                    (Filter.Eventually.of_forall (fun _ h => Set.diff_subset h.1))
              _ ≤ C₁ * N * Real.log N := hmom N hN1le
    have hsplit : (∫ α in minorArcs N B, g α) =
        (∫ α in minorArcs N B ∩ Sec, g α) + ∫ α in minorArcs N B \ Sec, g α := by
      have hunion : (minorArcs N B ∩ Sec) ∪ (minorArcs N B \ Sec) = minorArcs N B := by
        ext α
        constructor
        · rintro (h | h)
          · exact h.1
          · exact h.1
        · intro h
          by_cases hs : α ∈ Sec
          · exact Or.inl ⟨h, hs⟩
          · exact Or.inr ⟨h, hs⟩
      have hdisj : Disjoint (minorArcs N B ∩ Sec) (minorArcs N B \ Sec) := by
        rw [Set.disjoint_left]
        rintro α ⟨-, hs⟩ ⟨-, hns⟩
        exact hns hs
      have h := setIntegral_union hdisj (hminorMeas.diff hmeasSec)
        (hIntg.mono_set Set.inter_subset_left) (hIntg.mono_set Set.diff_subset)
      rwa [hunion] at h
    have hexp : -(B - 4 * (F.natDegree : ℝ) ^ 2) / (8 * Section2.weylExponent F) + 1 =
        -(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
          (8 * Section2.weylExponent F) - 1 := by
      have hK : Section2.weylExponent F ≠ 0 := by
        unfold Section2.weylExponent
        positivity
      field_simp
      ring
    have hW : Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
        (8 * Section2.weylExponent F)) * Real.log N =
        Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
          (8 * Section2.weylExponent F) + 1) := by
      have h := Real.rpow_add hL
        (-(B - 4 * (F.natDegree : ℝ) ^ 2) / (8 * Section2.weylExponent F)) 1
      simp only [Real.rpow_one] at h
      exact h.symm
    have hshort0 : 0 ≤ shortMass ⌊c * N⌋₊ N B Q := shortMass_nonneg _ _ _ _
    have hLB : 0 ≤ Real.log N ^ (B / 2) := (Real.rpow_pos_of_pos hL _).le
    have hLE : 0 ≤ Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
        16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) :=
      (Real.rpow_pos_of_pos hL _).le
    have hsecond : C₂ * H * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
        (8 * Section2.weylExponent F)) * (C₁ * N * Real.log N) =
        C₁ * C₂ * H * N * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
          16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) := by
      have e1 : C₂ * H * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
          (8 * Section2.weylExponent F)) * (C₁ * N * Real.log N) =
          C₁ * C₂ * H * N * (Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
            (8 * Section2.weylExponent F)) * Real.log N) := by ring
      rw [e1, hW, hexp]
    have hterm1 : 512 * H * Real.log N ^ (B / 2) * shortMass ⌊c * N⌋₊ N B Q ≤
        max 512 (max (2 * C₁) (C₁ * C₂)) * H * Real.log N ^ (B / 2) *
          shortMass ⌊c * N⌋₊ N B Q := by
      have h512 : (512 : ℝ) ≤ max 512 (max (2 * C₁) (C₁ * C₂)) := le_max_left _ _
      have h0 : 0 ≤ H * Real.log N ^ (B / 2) * shortMass ⌊c * N⌋₊ N B Q := by
        have hsa := shortMass_nonneg ⌊c * N⌋₊ N B Q
        have hsb : (0 : ℝ) ≤ H * Real.log N ^ (B / 2) := by positivity
        exact mul_nonneg hsb hsa
      calc 512 * H * Real.log N ^ (B / 2) * shortMass ⌊c * N⌋₊ N B Q =
          512 * (H * Real.log N ^ (B / 2) * shortMass ⌊c * N⌋₊ N B Q) := by ring
        _ ≤ max 512 (max (2 * C₁) (C₁ * C₂)) *
              (H * Real.log N ^ (B / 2) * shortMass ⌊c * N⌋₊ N B Q) :=
            mul_le_mul_of_nonneg_right h512 h0
        _ = _ := by ring
    have hterm2 : C₁ * C₂ * H * N * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
        16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) ≤
        max 512 (max (2 * C₁) (C₁ * C₂)) * H * N *
          Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
            16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) := by
      have hcc : C₁ * C₂ ≤ max 512 (max (2 * C₁) (C₁ * C₂)) :=
        le_trans (le_max_right _ _) (le_max_right _ _)
      have h0 : 0 ≤ H * N * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
          16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) := by positivity
      calc C₁ * C₂ * H * N * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
            16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) =
          (C₁ * C₂) * (H * N * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
            16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1)) := by ring
        _ ≤ max 512 (max (2 * C₁) (C₁ * C₂)) * (H * N * Real.log N ^
            (-(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
              (8 * Section2.weylExponent F) - 1)) := mul_le_mul_of_nonneg_right hcc h0
        _ = _ := by ring
    calc kernelMoment F ⌊c * N⌋₊ N H B ξ
        = ∫ α in minorArcs N B, g α := rfl
      _ = (∫ α in minorArcs N B ∩ Sec, g α) + ∫ α in minorArcs N B \ Sec, g α := hsplit
      _ ≤ 512 * H * Real.log N ^ (B / 2) * shortMass ⌊c * N⌋₊ N B Q +
          C₂ * H * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2) /
            (8 * Section2.weylExponent F)) * (C₁ * N * Real.log N) :=
          add_le_add (hsum_le.trans hTsum) hT_le
      _ = 512 * H * Real.log N ^ (B / 2) * shortMass ⌊c * N⌋₊ N B Q +
          C₁ * C₂ * H * N * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
            16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) := by
          rw [hsecond]
      _ ≤ max 512 (max (2 * C₁) (C₁ * C₂)) * H * Real.log N ^ (B / 2) *
            shortMass ⌊c * N⌋₊ N B Q +
          max 512 (max (2 * C₁) (C₁ * C₂)) * H * N *
            Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
              (8 * Section2.weylExponent F) - 1) := add_le_add hterm1 hterm2
  · refine ⟨2 * C₁ + 1, N₁ + (Real.exp 1 + 3), by positivity, by linarith, ?_⟩
    intro N H hN hH hHu ξ hξ
    have hN1le : N₁ ≤ N := by linarith
    have hNexp : Real.exp 1 ≤ N := by linarith
    have hN3 : 3 ≤ N := hN₁.trans hN1le
    have hN0 : 0 < N := by linarith
    have hNgt1 : 1 ≤ N := by linarith
    have hH1 : 1 ≤ H := (Real.one_le_rpow hNgt1 (by positivity)).trans hH
    have hL : 0 < Real.log N := Real.log_pos (by linarith)
    have hL1 : 1 ≤ Real.log N := by
      have h := Real.log_le_log (Real.exp_pos 1) hNexp
      simpa using h
    have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH
    have hKpos : 0 < Section2.weylExponent F := by
      unfold Section2.weylExponent
      positivity
    have hBle : B ≤ 4 * (F.natDegree : ℝ) ^ 2 := by
      have hle : B / 8 + (F.natDegree : ℝ) ^ 2 / 2 - 1 ≤ 0 := not_lt.mp hD
      have hk : (1 : ℝ) ≤ (F.natDegree : ℝ) := by exact_mod_cast hF.1
      nlinarith
    have hpow1 : 1 ≤ -(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
        (8 * Section2.weylExponent F) - 1 := by
      rw [le_sub_iff_add_le, le_div_iff₀ (by positivity)]
      nlinarith [hBle, hKpos]
    have hKle : ∀ α : ℝ, ‖Section2.polynomialKernel F N H (α - ξ)‖ ≤ H + 1 := by
      intro α
      have hcard := card_win_le F hN0.le hH0.le
      calc ‖Section2.polynomialKernel F N H (α - ξ)‖
          = ‖∑ n ∈ win F N H, Kernel.e ((Fv F n : ℝ) * (α - ξ))‖ := rfl
        _ ≤ ∑ n ∈ win F N H, ‖Kernel.e ((Fv F n : ℝ) * (α - ξ))‖ := norm_sum_le _ _
        _ = ((win F N H).card : ℝ) := by simp [Kernel.e, Complex.norm_exp]
        _ ≤ H + 1 := hcard
    have hcontS : Continuous (fun α : ℝ => ‖primeSum ⌊c * N⌋₊ α‖ ^ 2) := by
      unfold primeSum Kernel.e
      fun_prop
    have hcontK : Continuous (fun α : ℝ => ‖Section2.polynomialKernel F N H (α - ξ)‖) := by
      unfold Section2.polynomialKernel Kernel.e
      fun_prop
    have hminorSq : (∫ α in minorArcs N B, ‖primeSum ⌊c * N⌋₊ α‖ ^ 2) ≤
        C₁ * N * Real.log N := by
      refine le_trans ?_ (hmom N hN1le)
      apply setIntegral_mono_set hcontS.integrableOn_Icc
      · exact Filter.Eventually.of_forall (fun _ => sq_nonneg _)
      · exact Filter.Eventually.of_forall (fun _ h => Set.diff_subset h)
    have hstep : (∫ α in minorArcs N B, ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 *
        ‖Section2.polynomialKernel F N H (α - ξ)‖) ≤
        (H + 1) * ∫ α in minorArcs N B, ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := by
      calc _ ≤ ∫ α in minorArcs N B, (H + 1) * ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := by
            apply integral_mono
            · exact (hcontS.mul hcontK).integrableOn_Icc.mono_set Set.diff_subset
            · exact (continuous_const.mul hcontS).integrableOn_Icc.mono_set Set.diff_subset
            · intro α
              calc ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 * ‖Section2.polynomialKernel F N H (α - ξ)‖
                  ≤ ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 * (H + 1) :=
                    mul_le_mul_of_nonneg_left (hKle α) (sq_nonneg _)
                _ = (H + 1) * ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := by ring
        _ = (H + 1) * ∫ α in minorArcs N B, ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 :=
            integral_const_mul _ _
    have hpow : Real.log N ≤ Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
        16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) := by
      have h := Real.rpow_le_rpow_of_exponent_le hL1 hpow1
      simpa using h
    have hcoef : C₁ * (H + 1) * N ≤ (2 * C₁ + 1) * H * N := by
      have h1 : C₁ * (H + 1) * N = C₁ * H * N + C₁ * N := by ring
      have hcN : 0 ≤ C₁ * N := mul_nonneg hC₁.le hN0.le
      have hCHN : 0 ≤ C₁ * H * N := by positivity
      have h2 : C₁ * N ≤ C₁ * H * N := by
        nlinarith [hcN, hCHN, hH1, hC₁]
      have h4 : 0 ≤ H * N := by positivity
      nlinarith [h1, h2, hCHN, h4, hcN]
    have hfin : (H + 1) * (C₁ * N * Real.log N) ≤
        (2 * C₁ + 1) * H * N *
          Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
            (8 * Section2.weylExponent F) - 1) := by
      have h1 : (H + 1) * (C₁ * N * Real.log N) = C₁ * (H + 1) * N * Real.log N := by ring
      rw [h1]
      have h2 : C₁ * (H + 1) * N * Real.log N ≤ C₁ * (H + 1) * N *
          Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
            (8 * Section2.weylExponent F) - 1) := by
        have := mul_le_mul_of_nonneg_left hpow (by positivity : (0 : ℝ) ≤ C₁ * (H + 1) * N)
        calc C₁ * (H + 1) * N * Real.log N = (C₁ * (H + 1) * N) * Real.log N := by ring
          _ ≤ (C₁ * (H + 1) * N) * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
              16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) := this
          _ = C₁ * (H + 1) * N * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
              16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) := by ring
      have h3 : C₁ * (H + 1) * N * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
          16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) ≤
          (2 * C₁ + 1) * H * N * Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 -
            16 * Section2.weylExponent F) / (8 * Section2.weylExponent F) - 1) := by
        apply mul_le_mul_of_nonneg_right _ (by positivity)
        exact hcoef
      exact h2.trans h3
    have hterm : (2 * C₁ + 1) * H * N *
          Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
            (8 * Section2.weylExponent F) - 1) ≤
        (2 * C₁ + 1) * H * Real.log N ^ (B / 2) *
          shortMass ⌊c * N⌋₊ N B (fareyOrder F N H B) +
        (2 * C₁ + 1) * H * N *
          Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
            (8 * Section2.weylExponent F) - 1) := by
      have h1 : 0 ≤ (2 * C₁ + 1) * H * Real.log N ^ (B / 2) *
          shortMass ⌊c * N⌋₊ N B (fareyOrder F N H B) := by
        have hsa := shortMass_nonneg ⌊c * N⌋₊ N B (fareyOrder F N H B)
        have hsb : (0 : ℝ) ≤ (2 * C₁ + 1) * H * Real.log N ^ (B / 2) := by positivity
        exact mul_nonneg hsb hsa
      linarith [h1]
    calc kernelMoment F ⌊c * N⌋₊ N H B ξ
        = ∫ α in minorArcs N B, ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 *
            ‖Section2.polynomialKernel F N H (α - ξ)‖ := rfl
      _ ≤ (H + 1) * ∫ α in minorArcs N B, ‖primeSum ⌊c * N⌋₊ α‖ ^ 2 := hstep
      _ ≤ (H + 1) * (C₁ * N * Real.log N) :=
          mul_le_mul_of_nonneg_left hminorSq (by linarith)
      _ ≤ (2 * C₁ + 1) * H * N *
            Real.log N ^ (-(B - 4 * (F.natDegree : ℝ) ^ 2 - 16 * Section2.weylExponent F) /
              (8 * Section2.weylExponent F) - 1) := hfin
      _ ≤ _ := hterm


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

/-- Helper. Pointwise split of the squared major weight into the divisor part and the
logarithmic part. Used to reduce the Nair mean leaf to a pure divisor mean. -/
theorem majorWeight_sq_le (m : ℕ) (N : ℝ) :
    majorWeight m N ^ 2 ≤
      2 * (((m : ℝ) * m.divisors.card / m.totient) ^ 2) + 2 * Real.log N ^ 2 := by
  unfold majorWeight
  nlinarith [sq_nonneg ((m : ℝ) * m.divisors.card / m.totient - Real.log N)]

/-- Helper. Page 481 equation 4, reduced to the Nair 1992 short interval mean of the
divisor part of the weight. CONDITIONAL ON that divisor mean input. -/
theorem nair_mean_of_divisor_mean (F : ℤ[X]) (hF : Admissible F)
    (hNair : ∃ e : ℝ, 0 ≤ e ∧ ∀ ε : ℝ, 0 < ε → ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧
      ∀ N H : ℝ, N₀ ≤ N → N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
        H ≤ N ^ (1 / (F.natDegree : ℝ)) →
        ∑ n ∈ win F N H,
          (((Fv F n).toNat : ℝ) * (Fv F n).toNat.divisors.card /
            (Fv F n).toNat.totient) ^ 2 ≤ C * H * Real.log N ^ e) :
    ∃ d : ℝ, 0 ≤ d ∧ ∀ ε : ℝ, 0 < ε →
      ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      ∑ n ∈ win F N H, majorWeight (Fv F n).toNat N ^ 2 ≤
        C * H * Real.log N ^ d := by
  obtain ⟨e, he, hdiv⟩ := hNair
  refine ⟨e + 2, by linarith, ?_⟩
  intro ε hε
  obtain ⟨C, N₀, hC, hN₀, hsum⟩ := hdiv ε hε
  refine ⟨2 * C + 4, max 3 N₀, by linarith, hN₀.trans (le_max_right _ _), ?_⟩
  intro N H hN hH1 hH2
  have hN3 : 3 ≤ N := (le_max_left 3 N₀).trans hN
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hH0 : 0 < H := (Real.rpow_pos_of_pos hN0 _).trans_le hH1
  have hL1 : 1 ≤ Real.log N := by
    have h := Real.log_le_log (Real.exp_pos 1) (by linarith : Real.exp 1 ≤ N)
    simpa using h
  have hlogLE : Real.log N ^ 2 ≤ Real.log N ^ (e + 2) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hlogLEe : Real.log N ^ e ≤ Real.log N ^ (e + 2) :=
    Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have hstep := Finset.sum_le_sum (fun n _ => majorWeight_sq_le (Fv F n).toNat N)
  have hcard := card_win_le F hN0.le hH0.le
  calc ∑ n ∈ win F N H, majorWeight (Fv F n).toNat N ^ 2
      ≤ ∑ n ∈ win F N H,
          2 * (((Fv F n).toNat : ℝ) * (Fv F n).toNat.divisors.card /
            (Fv F n).toNat.totient) ^ 2 + 2 * Real.log N ^ 2 := hstep
    _ = 2 * ∑ n ∈ win F N H,
          (((Fv F n).toNat : ℝ) * (Fv F n).toNat.divisors.card /
            (Fv F n).toNat.totient) ^ 2 +
        ((win F N H).card : ℝ) * (2 * Real.log N ^ 2) := by
        simp only [Finset.mul_sum, Finset.sum_add_distrib, Finset.sum_const,
          nsmul_eq_mul]
        ring
    _ ≤ 2 * (C * H * Real.log N ^ e) + (H + 1) * (2 * Real.log N ^ (e + 2)) := by
        have hs := hsum N H ((le_max_right 3 N₀).trans hN) hH1 hH2
        refine add_le_add ?_ ?_
        · exact mul_le_mul_of_nonneg_left hs (by linarith)
        · exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_right hcard (by positivity)) hlogLE
    _ ≤ (2 * C + 4) * H * Real.log N ^ (e + 2) := by
        have h2H : (H : ℝ) + 1 ≤ 2 * H := by linarith
        have hle2 : 0 ≤ Real.log N ^ (e + 2) := (Real.rpow_pos_of_pos hL _).le
        calc 2 * (C * H * Real.log N ^ e) + (H + 1) * (2 * Real.log N ^ (e + 2))
            ≤ 2 * (C * H * Real.log N ^ (e + 2)) +
              (2 * H) * (2 * Real.log N ^ (e + 2)) := by
              refine add_le_add ?_ ?_
              · exact mul_le_mul_of_nonneg_left
                  (mul_le_mul_of_nonneg_right hlogLEe (by positivity)) (by positivity)
              · exact mul_le_mul_of_nonneg_right
                  (mul_le_mul_of_nonneg_left h2H (by positivity)) hle2
          _ = (2 * C + 4) * H * Real.log N ^ (e + 2) := by ring

/-- Helper. Page 481 equations 2 and 3, squared, reduced to the Vaughan 1981 Chapter 3
major arc approximation. CONDITIONAL ON that major arc error input with the divisor
weight logarithmic saving. -/
theorem major_pointwise_of_vaughan (F : ℤ[X]) (hF : Admissible F)
    (c : ℝ) (hc : 0 < c) (A ε B : ℝ) (hA : 0 < A) (hε : 0 < ε) (hB : 0 < B)
    (hV : ∃ CV NV : ℝ, 0 < CV ∧ 3 ≤ NV ∧ ∀ N : ℝ, NV ≤ N → ∀ m : ℕ, m ≤ ⌊c * N⌋₊ →
      ‖(∫ α in Set.Icc 0 1 ∩ majorArcs N B, coefficientIntegrand ⌊c * N⌋₊ m α) -
        ((m : ℝ) * Sing m : ℂ)‖ ≤
        CV * N * (Real.log N ^ (-B) * majorWeight m N + Real.log N ^ (-A / 2))) :
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
  obtain ⟨CV, NV, hCV, hNV, hV⟩ := hV
  refine ⟨2 * CV ^ 2, NV, by nlinarith [sq_pos_of_pos hCV], hNV, ?_⟩
  intro N H hN hH1 hH2 hcut n hn
  obtain ⟨hpos, hle⟩ := hcut n hn
  have hN0 : 0 < N := by linarith
  have hL : 0 < Real.log N := Real.log_pos (by linarith)
  have hcast : ((Fv F n).toNat : ℝ) = (Fv F n : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg hpos
  have hv := hV N hN (Fv F n).toNat hle
  rw [hcast] at hv
  have hsplit : (Real.log N ^ (-A / 2)) ^ 2 = Real.log N ^ (-A) := by
    rw [← Real.rpow_mul hL.le]
    congr 1
    ring
  have hsplitB : (Real.log N ^ (-B) * majorWeight (Fv F n).toNat N) ^ 2 =
      Real.log N ^ (-2 * B) * majorWeight (Fv F n).toNat N ^ 2 := by
    rw [mul_pow, ← Real.rpow_mul hL.le]
    congr 1
    ring
  have htri : (Real.log N ^ (-B) * majorWeight (Fv F n).toNat N +
      Real.log N ^ (-A / 2)) ^ 2 ≤
      2 * (Real.log N ^ (-B) * majorWeight (Fv F n).toNat N) ^ 2 +
        2 * (Real.log N ^ (-A / 2)) ^ 2 := by
    nlinarith [sq_nonneg (Real.log N ^ (-B) * majorWeight (Fv F n).toNat N -
      Real.log N ^ (-A / 2))]
  calc ‖(∫ α in Set.Icc 0 1 ∩ majorArcs N B,
      coefficientIntegrand ⌊c * N⌋₊ (Fv F n).toNat α) -
      ((Fv F n : ℝ) * Sing (Fv F n).toNat : ℂ)‖ ^ 2
      ≤ (CV * N * (Real.log N ^ (-B) * majorWeight (Fv F n).toNat N +
          Real.log N ^ (-A / 2))) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hv 2
    _ = CV ^ 2 * N ^ 2 * (Real.log N ^ (-B) * majorWeight (Fv F n).toNat N +
          Real.log N ^ (-A / 2)) ^ 2 := by ring
    _ ≤ CV ^ 2 * N ^ 2 * (2 * (Real.log N ^ (-B) *
            majorWeight (Fv F n).toNat N) ^ 2 +
          2 * (Real.log N ^ (-A / 2)) ^ 2) :=
          mul_le_mul_of_nonneg_left htri (by positivity)
    _ = (2 * CV ^ 2) * N ^ 2 * (Real.log N ^ (-2 * B) *
          majorWeight (Fv F n).toNat N ^ 2 + Real.log N ^ (-A)) := by
        rw [hsplitB, hsplit]
        ring

end
end LeanLab.Perelli1996.Decomp103
