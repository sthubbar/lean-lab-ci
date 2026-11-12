/-
Perelli 1996, page 481, equations 2 and 3.
Separate the finite major coefficient comparison from the arithmetic tail.
The primary rectangular arcs agree with page 480.
AI wrote the Lean code. Binary Goldbach is open.
-/
import LeanLab.Perelli1996.Decomp103
import LeanLab.Perelli1996.RamanujanInt400
import LeanLab.Perelli1996.Cor1b
import LeanLab.Perelli1996.Series320
import LeanLab.Perelli1996.PrincipalModel320
import LeanLab.Perelli1996.ArcModel320

namespace LeanLab.Perelli1996.Decomp320a
open Finset Real Polynomial MeasureTheory
open LeanLab.Perelli1996.Decomp88 LeanLab.Perelli1996.Decomp103
noncomputable section

/-- Page 481 equations 2 and 3. The finite singular series through the real cutoff P. -/
def singularPartial (m : ℕ) (P : ℝ) : ℂ :=
  ∑ q ∈ Icc 1 ⌊P⌋₊,
    ((ArithmeticFunction.moebius q : ℂ) ^ 2 / (q.totient : ℂ) ^ 2) *
      RamanujanInt400.ramanujanSumInt q (-(m : ℤ))

/-- Page 480 before equation 1. Polynomial values on the window are eventually positive. -/
theorem window_pos (F : ℤ[X]) (hF : Admissible F) :
    ∃ N₀ : ℝ, 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N → ∀ n ∈ win F N H,
      0 < (Fv F n).toNat := by
  obtain ⟨X₀, hX₀, hX⟩ := poly_lower F hF
  have hk : (0 : ℝ) < F.natDegree := by exact_mod_cast (show 0 < F.natDegree by have := hF.1; omega)
  obtain ⟨N₁, hN₁⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (one_div_pos.mpr hk)).eventually
      (Filter.eventually_ge_atTop (max X₀ 1)))
  refine ⟨max 3 N₁, le_max_left _ _, ?_⟩
  intro N H hN n hn
  have hlo : max X₀ 1 ≤ (n : ℝ) :=
    (hN₁ N ((le_max_right _ _).trans hN)).trans
      ((Nat.le_ceil _).trans (by exact_mod_cast (Finset.mem_Icc.mp hn).1))
  have hp := hX n ((le_max_left _ _).trans hlo)
  have hn1 : (1 : ℝ) ≤ n := (le_max_right _ _).trans hlo
  have hv : (0 : ℝ) < Fv F n := by
    have : (0 : ℝ) < (n : ℝ) ^ F.natDegree := pow_pos (by linarith) _
    linarith
  have hvI : 0 < Fv F n := by exact_mod_cast hv
  omega

/-- Page 481 equation 2, the prime sum comparison on the primary arcs.
On the arc at a over q with q at most L^B, Vaughan 1981 Chapter 3, Lemma 3.1 with the
Siegel Walfisz theorem, replaces the prime sum by mu q over phi q times the kernel T.
Summing the squared model over the reduced residues a gives the Ramanujan coefficient
Series320.coefficient m q times the central kernel integral over radius L^B over N.
Cited input: Vaughan 1981 Chapter 3; Perelli 1996 page 481 equation 2.
PROVED from ArcModel320.arc_model, whose pieces leaf_arc_pointwise, via the lab's
PNTPort Siegel Walfisz major arc lemma, and leaf_arc_integral_split are proved. -/
theorem leaf_prime_model (F : ℤ[X]) (hF : Admissible F)
    (c : ℝ) (hc : 0 < c) (A ε B : ℝ) (hA : 0 < A) (hε : 0 < ε) (hB : 0 < B) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      (∀ n ∈ win F N H, 0 ≤ Fv F n ∧ (Fv F n).toNat ≤ ⌊c * N⌋₊) →
      ∀ n ∈ win F N H,
      ‖(∫ α in Set.Icc 0 1 ∩ majorArcs N B,
          coefficientIntegrand ⌊c * N⌋₊ (Fv F n).toNat α) -
        (∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊, Series320.coefficient (Fv F n).toNat q) *
          (∫ α in (-(Real.log N ^ B / N))..(Real.log N ^ B / N),
            Kernel.T 0 (⌊c * N⌋₊ + 1) α ^ 2 * Kernel.e (-((Fv F n).toNat : ℝ) * α))‖ ≤
        C * N * (Real.log N ^ (1 - B) + Real.log N ^ (-A / 2)) := by
  obtain ⟨C, N₀, hC, hN₀, h⟩ := ArcModel320.arc_model c hc A B hA hB
  refine ⟨C, N₀, hC, hN₀, ?_⟩
  intro N H hN _ _ _ n _
  have hN0 : 0 < N := by linarith
  have hL : 0 ≤ Real.log N := Real.log_nonneg (by linarith)
  refine (h N hN _).trans ?_
  have hy : 0 ≤ Real.log N ^ (1 - B) := Real.rpow_nonneg hL _
  exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_left hy) (by positivity)

/-- Page 481 equation 2: the finite singular partial sum written with Series320 coefficients. -/
theorem singularPartial_eq (m : ℕ) (P : ℝ) :
    singularPartial m P = ∑ q ∈ Icc 1 ⌊P⌋₊, Series320.coefficient m q := by
  unfold singularPartial Series320.coefficient
  apply Finset.sum_congr rfl
  intro q hq
  rw [RamanujanInt400.ramanujanSumInt_eq_natAbs q (-(m : ℤ)) (Finset.mem_Icc.mp hq).1]
  simp only [Int.natAbs_neg, Int.natAbs_natCast]

/-- Page 481 equation 2 before completing the singular series.
PROVED from leaf_prime_model; the principal model error is PROVED in PrincipalModel320.
Vaughan Chapter 3 supplies the prime approximation.
The primary rectangular arcs are exactly the arcs defined on page 480. -/
theorem leaf_finite_major (F : ℤ[X]) (hF : Admissible F)
    (c : ℝ) (hc : 0 < c) (A ε B : ℝ) (hA : 0 < A) (hε : 0 < ε) (hB : 0 < B) :
    ∃ C N₀ : ℝ, 0 < C ∧ 3 ≤ N₀ ∧ ∀ N H : ℝ, N₀ ≤ N →
      N ^ (1 / (3 * (F.natDegree : ℝ)) + ε) ≤ H →
      H ≤ N ^ (1 / (F.natDegree : ℝ)) →
      (∀ n ∈ win F N H, 0 ≤ Fv F n ∧ (Fv F n).toNat ≤ ⌊c * N⌋₊) →
      ∀ n ∈ win F N H,
      ‖(∫ α in Set.Icc 0 1 ∩ majorArcs N B,
          coefficientIntegrand ⌊c * N⌋₊ (Fv F n).toNat α) -
        (Fv F n : ℂ) * singularPartial (Fv F n).toNat (Real.log N ^ B)‖ ≤
        C * N * (Real.log N ^ (1 - B) + Real.log N ^ (-A / 2)) := by
  obtain ⟨CP, NP, hCP, hNP, hprime⟩ := leaf_prime_model F hF c hc A ε B hA hε hB
  obtain ⟨CM, hCM, hmodel⟩ := PrincipalModel320.finite_model_error_scaled c hc
  obtain ⟨NA, hNA, harc⟩ := arc_parameters F hF ε B hε hB
  obtain ⟨NW, hNW, hpos⟩ := window_pos F hF
  refine ⟨CP + CM, max (max NP NA) (max NW (Real.exp 1)), by positivity,
    hNP.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro N H hN hH hHu hcut n hn
  have hNP' : NP ≤ N := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNA' : NA ≤ N := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hNW' : NW ≤ N := ((le_max_left _ _).trans (le_max_right _ _)).trans hN
  have hNe : Real.exp 1 ≤ N := ((le_max_right _ _).trans (le_max_right _ _)).trans hN
  have hN0 : 0 < N := (Real.exp_pos 1).trans_le hNe
  have hL1 : 1 ≤ Real.log N := by simpa using Real.log_le_log (Real.exp_pos 1) hNe
  have hL : 0 < Real.log N := by linarith
  set m := (Fv F n).toNat with hm_def
  have hmpos : 0 < m := hpos N H hNW' n hn
  have hmcast : (m : ℝ) = (Fv F n : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (hcut n hn).1
  have hmC : (Fv F n : ℂ) = (m : ℂ) := by
    have : ((Fv F n : ℝ) : ℂ) = ((m : ℝ) : ℂ) := by rw [hmcast]
    simpa using this
  have hmN : (m : ℝ) ≤ c * N :=
    (by exact_mod_cast (hcut n hn).2 : (m : ℝ) ≤ (⌊c * N⌋₊ : ℝ)).trans
      (Nat.floor_le (by positivity))
  have hmM : m ≤ ⌊c * N⌋₊ := (hcut n hn).2
  have hP : 0 < Real.log N ^ B := Real.rpow_pos_of_pos hL B
  have hhalf := (harc N H hNA' hH).1
  have h1 := hprime N H hNP' hH hHu hcut n hn
  have h2 := hmodel N (Real.log N ^ B) hNe hP hhalf m ⌊c * N⌋₊ hmpos hmM hmN
    (Icc 1 ⌊Real.log N ^ B⌋₊)
  have hscale : Real.log N / Real.log N ^ B = Real.log N ^ (1 - B) := by
    rw [Real.rpow_sub hL, Real.rpow_one]
  rw [mul_div_assoc, hscale] at h2
  rw [singularPartial_eq, hmC]
  set I : ℂ := ∫ α in Set.Icc 0 1 ∩ majorArcs N B, coefficientIntegrand ⌊c * N⌋₊ m α
  set S : ℂ := ∑ q ∈ Icc 1 ⌊Real.log N ^ B⌋₊, Series320.coefficient m q
  set J : ℂ := ∫ α in (-(Real.log N ^ B / N))..(Real.log N ^ B / N),
    Kernel.T 0 (⌊c * N⌋₊ + 1) α ^ 2 * Kernel.e (-(m : ℝ) * α)
  have htri : ‖I - (m : ℂ) * S‖ ≤ ‖I - S * J‖ + ‖S * J - (m : ℂ) * S‖ := by
    have : I - (m : ℂ) * S = (I - S * J) + (S * J - (m : ℂ) * S) := by ring
    rw [this]
    exact norm_add_le _ _
  have hA2 : 0 ≤ Real.log N ^ (-A / 2) := by positivity
  have hB1 : 0 ≤ Real.log N ^ (1 - B) := by positivity
  calc ‖I - (m : ℂ) * S‖ ≤ ‖I - S * J‖ + ‖S * J - (m : ℂ) * S‖ := htri
    _ ≤ CP * N * (Real.log N ^ (1 - B) + Real.log N ^ (-A / 2)) +
        CM * N * Real.log N ^ (1 - B) := add_le_add h1 h2
    _ ≤ (CP + CM) * N * (Real.log N ^ (1 - B) + Real.log N ^ (-A / 2)) := by
      nlinarith [mul_nonneg (mul_nonneg hCM.le hN0.le) hA2]

/-- LEAF. Page 481 equation 3 and the singular series expansion used in equation 2.
Only the arithmetic completion of the finite Ramanujan series is estimated here. -/
theorem leaf_singular_tail :
    ∃ C : ℝ, 0 < C ∧ ∀ m : ℕ, 0 < m → ∀ P : ℝ, 1 ≤ P →
      ‖(Sing m : ℂ) - singularPartial m P‖ ≤
        C * ((m : ℝ) * m.divisors.card / m.totient) / P := by
  obtain ⟨C, hC, htail⟩ := Series320.partial_tail
  refine ⟨C, hC, ?_⟩
  intro m hm P hP
  have heq : singularPartial m P = ∑ q ∈ Icc 1 ⌊P⌋₊, Series320.coefficient m q := by
    unfold singularPartial Series320.coefficient
    apply Finset.sum_congr rfl
    intro q hq
    rw [RamanujanInt400.ramanujanSumInt_eq_natAbs q (-(m : ℤ)) (Finset.mem_Icc.mp hq).1]
    simp only [Int.natAbs_neg, Int.natAbs_natCast]
  rw [heq]
  exact htail m hm P hP

/-- The exact sealed pointwise target assembled from the two smaller comparisons.
PROVED from leaf_finite_major and leaf_singular_tail. -/
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
  obtain ⟨CF, NF, hCF, hNF, hfinite⟩ := leaf_finite_major F hF c hc A ε B hA hε hB
  obtain ⟨CT, hCT, htail⟩ := leaf_singular_tail
  obtain ⟨NP, hNP, hpos⟩ := window_pos F hF
  let K := CF + c * CT
  refine ⟨4 * K ^ 2, max (max NF NP) (Real.exp 1), by dsimp [K]; positivity,
    hNF.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
  intro N H hN hH hHu hcut n hn
  have hNF' := ((le_max_left _ _).trans (le_max_left _ _)).trans hN
  have hNP' := ((le_max_right _ _).trans (le_max_left _ _)).trans hN
  have hN3 : 3 ≤ N := hNF.trans hNF'
  have hN0 : 0 < N := by linarith
  have hL1 : 1 ≤ Real.log N := by
    simpa using Real.log_le_log (Real.exp_pos 1) ((le_max_right _ _).trans hN)
  have hL : 0 < Real.log N := by linarith
  let m := (Fv F n).toNat
  let w : ℝ := (m : ℝ) * m.divisors.card / m.totient
  have hmpos : 0 < m := hpos N H hNP' n hn
  have hmcast : (m : ℝ) = (Fv F n : ℝ) := by
    exact_mod_cast Int.toNat_of_nonneg (hcut n hn).1
  have hmN : (m : ℝ) ≤ c * N :=
    (by exact_mod_cast (hcut n hn).2 : (m : ℝ) ≤ (⌊c * N⌋₊ : ℝ)).trans
      (Nat.floor_le (by positivity))
  have hw : 0 ≤ w := by dsimp [w]; positivity
  have ht := htail m hmpos (Real.log N ^ B) (Real.one_le_rpow hL1 hB.le)
  have hpart := hfinite N H hNF' hH hHu hcut n hn
  let I : ℂ := ∫ α in Set.Icc 0 1 ∩ majorArcs N B,
    coefficientIntegrand ⌊c * N⌋₊ m α
  have htriangle : ‖I - (Fv F n : ℂ) * (Sing m : ℂ)‖ ≤
      CF * N * (Real.log N ^ (1 - B) + Real.log N ^ (-A / 2)) +
        c * N * (CT * w / Real.log N ^ B) := by
    calc
      _ ≤ ‖I - (Fv F n : ℂ) * singularPartial m (Real.log N ^ B)‖ +
          ‖(Fv F n : ℂ) * (singularPartial m (Real.log N ^ B) - (Sing m : ℂ))‖ := by
            have heq : I - (Fv F n : ℂ) * (Sing m : ℂ) =
                (I - (Fv F n : ℂ) * singularPartial m (Real.log N ^ B)) +
                (Fv F n : ℂ) * (singularPartial m (Real.log N ^ B) - (Sing m : ℂ)) := by ring
            rw [heq]
            exact norm_add_le _ _
      _ ≤ CF * N * (Real.log N ^ (1 - B) + Real.log N ^ (-A / 2)) +
          c * N * (CT * w / Real.log N ^ B) := by
            apply add_le_add hpart
            rw [norm_mul, norm_sub_rev]
            have hnorm : ‖(Fv F n : ℂ)‖ = (m : ℝ) := by
              rw [← Complex.ofReal_intCast, Complex.norm_real, Real.norm_eq_abs,
                ← hmcast, abs_of_nonneg (Nat.cast_nonneg _)]
            rw [hnorm]
            exact mul_le_mul hmN ht (norm_nonneg _) (by positivity)
  have hpow1 : Real.log N ^ (1 - B) = Real.log N ^ (-B) * Real.log N := by
    rw [show 1 - B = -B + 1 by ring, Real.rpow_add hL, Real.rpow_one]
  have hpow2 : CT * w / Real.log N ^ B = CT * (Real.log N ^ (-B) * w) := by
    rw [Real.rpow_neg hL.le]
    ring
  have hK : 0 < K := by dsimp [K]; positivity
  have hbound : ‖I - (Fv F n : ℂ) * (Sing m : ℂ)‖ ≤
      K * N * (Real.log N ^ (-B) * majorWeight m N + Real.log N ^ (-A / 2)) := by
    refine htriangle.trans ?_
    rw [hpow1, hpow2]
    change CF * N * (Real.log N ^ (-B) * Real.log N + Real.log N ^ (-A / 2)) +
      c * N * (CT * (Real.log N ^ (-B) * w)) ≤
      K * N * (Real.log N ^ (-B) * (w + Real.log N) + Real.log N ^ (-A / 2))
    have hcoeff1 : CF ≤ K := by dsimp [K]; linarith [mul_pos hc hCT]
    have hcoeff2 : c * CT ≤ K := by dsimp [K]; linarith
    have hx : 0 ≤ Real.log N ^ (-B) * Real.log N + Real.log N ^ (-A / 2) := by positivity
    have hy : 0 ≤ Real.log N ^ (-B) * w := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hcoeff1 (mul_nonneg hN0.le hx),
      mul_le_mul_of_nonneg_right hcoeff2 (mul_nonneg hN0.le hy)]
  have hsquare := pow_le_pow_left₀ (norm_nonneg _) hbound 2
  have hadd := add_sq_le (a := Real.log N ^ (-B) * majorWeight m N)
    (b := Real.log N ^ (-A / 2))
  have he1 : (Real.log N ^ (-B) * majorWeight m N) ^ 2 =
      Real.log N ^ (-2 * B) * majorWeight m N ^ 2 := by
    rw [mul_pow, ← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 2
    ring
  have he2 : (Real.log N ^ (-A / 2)) ^ 2 = Real.log N ^ (-A) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hL.le]
    congr 1
    ring
  rw [he1, he2] at hadd
  have hnon : 0 ≤ Real.log N ^ (-2 * B) * majorWeight m N ^ 2 + Real.log N ^ (-A) := by positivity
  change ‖I - (Fv F n : ℂ) * (Sing m : ℂ)‖ ^ 2 ≤ _
  calc
    _ ≤ (K * N * (Real.log N ^ (-B) * majorWeight m N + Real.log N ^ (-A / 2))) ^ 2 := hsquare
    _ = K ^ 2 * N ^ 2 * (Real.log N ^ (-B) * majorWeight m N + Real.log N ^ (-A / 2)) ^ 2 := by ring
    _ ≤ K ^ 2 * N ^ 2 * (2 * (Real.log N ^ (-2 * B) * majorWeight m N ^ 2 + Real.log N ^ (-A))) :=
      mul_le_mul_of_nonneg_left hadd (by positivity)
    _ ≤ _ := by nlinarith [mul_nonneg (show 0 ≤ K ^ 2 * N ^ 2 by positivity) hnon]

end
end LeanLab.Perelli1996.Decomp320a
