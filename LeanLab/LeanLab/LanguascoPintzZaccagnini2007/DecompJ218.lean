import LeanLab.LanguascoPintzZaccagnini2007.Truncation131
import LeanLab.LanguascoPintzZaccagnini2007.Lemma62
import LeanLab.LanguascoPintzZaccagnini2007.Residues131

/-!
P0045 U-1608. Re-cut of the major arc decomposition of display 25, page 8.
The old leaves are kept as text and refuted in Audit1608.lean.
Open leaves here: `major_arcs_j1_131`, Corollary 4.2 for the BINARY integral,
and `major_arcs_combine131`, displays 15 to 24, the singular series average.
`major_arcs_j2_131`, displays 12 to 14, is proved here from Lemma 6.2.
`major_asymptotic131_assembly` is proved from these and has no sorry of its own.
Decomp131.lean now imports this file, so `major_asymptotic131` is this assembly.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real Filter MeasureTheory
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

/-- Display 4 on page 3: the BINARY major arc integral R_M(n), which is the
integral of S^2 e(-n alpha), that is `majorContribution131` at k = 0. -/
def binaryMajor131 (X n : ℕ) (P : ℝ) : ℝ := majorContribution131 0 X n P

/-- The even integers of [X/2, X], the range of m in Lemma 6.2, page 9.
Display 12 evaluates R_M at n = N - 2^ν1 - ... - 2^νk, which can fall just below 2X/3
when N is near 2X/3, so the J(X) of Corollary 4.2 does not cover it. -/
def evenWindow131 (X : ℕ) : Finset ℕ :=
  (Icc 1 X).filter (fun n : ℕ => Even n ∧ (X : ℝ) / 2 ≤ n)

/-- Page 6: q' is the product of the odd primes dividing q, without multiplicity. -/
def oddRad131 (r : ℕ) : ℕ := ∏ p ∈ r.primeFactors.filter (fun p => 2 < p), p

/-- Display 5: the exponent tuples in [1, L']^k, L' = L - sqrt L. -/
abbrev tuples131 (k X : ℕ) : Finset (Fin k → ℕ) :=
  exponentTuples131 k ⌊Lg X - Real.sqrt (Lg X)⌋₊

/-- Display 5: M = 2^ν1 + ... + 2^νk. -/
def tuplePower131 {k : ℕ} (ν : Fin k → ℕ) : ℕ := ∑ i, 2 ^ ν i

/-- Corollary 4.2 and display 10, page 6: at most K₁ moduli, each with r' at least c L^2. -/
def ExceptionalModuli131 (K₁ : ℕ) (c : ℝ) (X : ℕ) (E : Finset ℕ) : Prop :=
  E.card ≤ K₁ ∧ ∀ r ∈ E, c * Lg X ^ 2 ≤ oddRad131 r

/-- Display 9, page 6: n lies in J_1, that is r does not divide C* n for all r in E. -/
def Nonexceptional131 (Cstar : ℕ) (E : Finset ℕ) (n : ℕ) : Prop :=
  ∀ r ∈ E, ¬ r ∣ Cstar * n

/-- Pointwise factors of the singular series are nonnegative. -/
theorem singF_nonneg131 (n : ℕ) (p : {p : ℕ // p.Prime}) : 0 ≤ singF n p := by
  unfold singF
  have h2 : (2 : ℝ) ≤ p.1 := by exact_mod_cast p.2.two_le
  split_ifs with h
  · exact div_nonneg (by linarith) (by linarith)
  · have h1 : (1 : ℝ) ≤ (p.1 : ℝ) - 1 := by linarith
    have h3 : 1 ≤ ((p.1 : ℝ) - 1) ^ 2 := one_le_pow₀ h1
    have h4 : 1 / ((p.1 : ℝ) - 1) ^ 2 ≤ 1 := by
      rw [div_le_one (by linarith)]
      exact h3
    linarith

/-- The singular series is nonnegative. -/
theorem Sing_nonneg131 (n : ℕ) : 0 ≤ Sing n := by
  have hS : Sing n = ∏' p, singF n p := rfl
  rw [hS]
  by_cases hm : Multipliable (singF n)
  · exact ge_of_tendsto hm.hasProd
      (Eventually.of_forall fun S => prod_nonneg fun p _ => singF_nonneg131 n p)
  · rw [tprod_eq_one_of_not_multipliable hm]
    norm_num

/-- The major arcs lie in a bounded interval. -/
theorem majorArcs_bounded131 (X : ℕ) (P : ℝ) :
    majorArcs131 X P ⊆ Set.Icc (-(1 / arcQ131 X P)) (1 + 1 / arcQ131 X P) := by
  rintro α ⟨q, a, hq, hqP, ha, -, h1, h2⟩
  have hq0 : (1 : ℝ) ≤ q := by exact_mod_cast hq
  have hP : 0 < P := by linarith
  have hQ : 0 ≤ arcQ131 X P := by unfold arcQ131; positivity
  have hQi : 0 ≤ 1 / arcQ131 X P := by positivity
  have hb : 1 / ((q : ℝ) * arcQ131 X P) ≤ 1 / arcQ131 X P := by
    have he : 1 / ((q : ℝ) * arcQ131 X P) = (1 / (q : ℝ)) * (1 / arcQ131 X P) := by
      rw [div_mul_div_comm, one_mul]
    rw [he]
    exact mul_le_of_le_one_left hQi (by rw [div_le_one (by linarith)]; exact hq0)
  have ham := mem_Icc.mp ha
  have ha1 : (a : ℝ) / q ≤ 1 := by
    rw [div_le_one (by linarith)]
    exact_mod_cast ham.2
  have ha0 : 0 ≤ (a : ℝ) / q := by positivity
  exact ⟨by linarith, by linarith⟩

/-- A tuple power is at most j 2^M. -/
theorem tuplePower_le131 {j M : ℕ} {ν : Fin j → ℕ} (hν : ν ∈ exponentTuples131 j M) :
    tuplePower131 ν ≤ j * 2 ^ M := by
  unfold tuplePower131
  have h : ∀ i ∈ (univ : Finset (Fin j)), 2 ^ ν i ≤ 2 ^ M := fun i _ =>
    Nat.pow_le_pow_right (by norm_num) (mem_Icc.mp (Fintype.mem_piFinset.mp hν i)).2
  calc ∑ i, 2 ^ ν i ≤ ∑ _i : Fin j, 2 ^ M := sum_le_sum h
    _ = j * 2 ^ M := by simp

/-- A tuple power is even, since every exponent is at least 1. -/
theorem tuplePower_even131 {j M : ℕ} {ν : Fin j → ℕ} (hν : ν ∈ exponentTuples131 j M) :
    Even (tuplePower131 ν) := by
  unfold tuplePower131
  rw [even_iff_two_dvd]
  refine dvd_sum fun i _ => ?_
  exact dvd_pow_self 2 (by
    have := (mem_Icc.mp (Fintype.mem_piFinset.mp hν i)).1
    omega)

/-- Page 3: 2^(L') is o(X), so the shifts in display 5 are at most X/6 for large X. -/
theorem tuple_window131 (k : ℕ) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      1 ≤ Lg X ∧ 6 * k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ ≤ X := by
  have ht : Tendsto (fun X : ℕ => Lg X) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hs : Tendsto (fun X : ℕ => Real.exp (Real.log 2 * Real.sqrt (Lg X))) atTop atTop :=
    Real.tendsto_exp_atTop.comp ((Real.tendsto_sqrt_atTop.comp ht).const_mul_atTop hlog)
  obtain ⟨X₀, hX₀⟩ := ((ht.eventually_ge_atTop 1).and
    (hs.eventually_ge_atTop (6 * (k : ℝ)))).exists_forall_of_atTop
  refine ⟨max 1 X₀, fun X hX => ?_⟩
  obtain ⟨hL, hE⟩ := hX₀ X (le_trans (le_max_right _ _) hX)
  refine ⟨hL, ?_⟩
  have hX1 : (0 : ℝ) < X := by
    have : 1 ≤ X := le_trans (le_max_left _ _) hX
    exact_mod_cast this
  have hsq : Real.sqrt (Lg X) ≤ Lg X :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have ht0 : 0 ≤ Lg X - Real.sqrt (Lg X) := by linarith
  have hfl := Nat.floor_le ht0
  set M := ⌊Lg X - Real.sqrt (Lg X)⌋₊
  have h2M : (2 : ℝ) ^ M ≤ (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hfl
  have hXe : (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) * (2 : ℝ) ^ (Real.sqrt (Lg X)) = X := by
    rw [← Real.rpow_add (by norm_num), sub_add_cancel]
    exact Real.rpow_logb (by norm_num) (by norm_num) hX1
  have hE' : 6 * (k : ℝ) ≤ (2 : ℝ) ^ (Real.sqrt (Lg X)) := by
    rw [Real.rpow_def_of_pos (by norm_num)]
    exact hE
  have hp : (0 : ℝ) ≤ (2 : ℝ) ^ M := by positivity
  have hq : (0 : ℝ) ≤ (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) := by positivity
  have hmain : 6 * (k : ℝ) * (2 : ℝ) ^ M ≤ X := by
    calc 6 * (k : ℝ) * (2 : ℝ) ^ M
        ≤ (2 : ℝ) ^ (Real.sqrt (Lg X)) * (2 : ℝ) ^ (Lg X - Real.sqrt (Lg X)) :=
          mul_le_mul hE' h2M hp (by positivity)
      _ = X := by rw [mul_comm]; exact hXe
  exact_mod_cast hmain

/-- Natural number form of membership in J(X). -/
theorem evenJ_nat131 {X N : ℕ} (hN : N ∈ evenJ131 X) :
    1 ≤ N ∧ N ≤ X ∧ Even N ∧ 2 * X ≤ 3 * N := by
  obtain ⟨h1, h2, h3⟩ := mem_filter.mp hN
  obtain ⟨h4, h5⟩ := mem_Icc.mp h1
  refine ⟨h4, h5, h2, ?_⟩
  have : 2 * (X : ℝ) ≤ 3 * N := by linarith
  exact_mod_cast this

/-- Shifted arguments stay in the window of Lemma 6.2. -/
theorem window_mem131 {X N M : ℕ} (hN : N ∈ evenJ131 X) (hM : 6 * M ≤ X) (hev : Even M) :
    N - M ∈ evenWindow131 X := by
  obtain ⟨h1, h2, h3, h4⟩ := evenJ_nat131 hN
  have hle : M ≤ N := by omega
  refine mem_filter.mpr ⟨mem_Icc.mpr ⟨by omega, by omega⟩, (Nat.even_sub hle).mpr ?_, ?_⟩
  · exact iff_of_true h3 hev
  · have : X ≤ 2 * (N - M) := by omega
    have h' : (X : ℝ) ≤ 2 * ((N - M : ℕ) : ℝ) := by exact_mod_cast this
    linarith

/-- Display 5 on page 4, proved: the k-fold integral is the sum of the binary integrals
at the shifted arguments N - M. -/
theorem major_expand131 (k X N : ℕ) (P : ℝ)
    (h : ∀ ν ∈ tuples131 k X, tuplePower131 ν ≤ N) :
    majorContribution131 k X N P =
      ∑ ν ∈ tuples131 k X, binaryMajor131 X (N - tuplePower131 ν) P := by
  have hpoint : ∀ α : ℝ,
      primeSum131 X α ^ 2 * powerSum131 X α ^ k * phase131 (-(N : ℝ) * α) =
      ∑ ν ∈ tuples131 k X, primeSum131 X α ^ 2 * powerSum131 X α ^ 0 *
        phase131 (-((N - tuplePower131 ν : ℕ) : ℝ) * α) := by
    intro α
    rw [powerSum_pow131, mul_sum, sum_mul]
    refine sum_congr rfl fun ν hν => ?_
    have hc : ((N - tuplePower131 ν : ℕ) : ℝ) = (N : ℝ) - tuplePower131 ν :=
      Nat.cast_sub (h ν hν)
    have he : phase131 (((∑ i, 2 ^ ν i : ℕ) : ℝ) * α) * phase131 (-(N : ℝ) * α) =
        phase131 (-((N : ℝ) - tuplePower131 ν) * α) := by
      rw [phase_add131]
      congr 1
      unfold tuplePower131
      ring
    rw [hc, pow_zero, mul_one, mul_assoc, he]
  have hint : ∀ ν ∈ tuples131 k X, IntegrableOn (fun α : ℝ =>
      primeSum131 X α ^ 2 * powerSum131 X α ^ 0 *
        phase131 (-((N - tuplePower131 ν : ℕ) : ℝ) * α)) (majorArcs131 X P) := by
    intro ν _
    have hc : Continuous (fun α : ℝ =>
        primeSum131 X α ^ 2 * powerSum131 X α ^ 0 *
          phase131 (-((N - tuplePower131 ν : ℕ) : ℝ) * α)) :=
      (((primeSum_continuous131 X).pow 2).mul ((powerSum_continuous131 X).pow 0)).mul
        (phase_continuous131.comp (continuous_const.mul continuous_id))
    exact (hc.continuousOn.integrableOn_compact isCompact_Icc).mono_set (majorArcs_bounded131 X P)
  have hi : (∫ α in majorArcs131 X P,
        primeSum131 X α ^ 2 * powerSum131 X α ^ k * phase131 (-(N : ℝ) * α)) =
      ∑ ν ∈ tuples131 k X, ∫ α in majorArcs131 X P,
        primeSum131 X α ^ 2 * powerSum131 X α ^ 0 *
          phase131 (-((N - tuplePower131 ν : ℕ) : ℝ) * α) := by
    calc _ = ∫ α in majorArcs131 X P, ∑ ν ∈ tuples131 k X,
          primeSum131 X α ^ 2 * powerSum131 X α ^ 0 *
            phase131 (-((N - tuplePower131 ν : ℕ) : ℝ) * α) :=
          integral_congr_ae (Eventually.of_forall hpoint)
      _ = _ := integral_finsetSum _ hint
  unfold binaryMajor131 majorContribution131
  rw [hi, Complex.re_sum]

/-- Elementary split of displays 11 and 12: good terms by a relative bound,
bad terms by a bound on the sum over bad indices. -/
theorem split_bound131 {ι : Type*} (T : Finset ι) (bad : ι → Prop) [DecidablePred bad]
    (a b s : ι → ℝ) (η D : ℝ)
    (hη : 0 ≤ η) (hD : 0 ≤ D) (hb : ∀ ν ∈ T, 0 ≤ b ν) (hs : ∀ ν ∈ T, 0 ≤ s ν)
    (hgood : ∀ ν ∈ T, ¬ bad ν → |a ν - b ν| ≤ η * b ν)
    (hbad : ∀ ν ∈ T, bad ν → |a ν - b ν| ≤ D * s ν) :
    |∑ ν ∈ T, a ν - ∑ ν ∈ T, b ν| ≤ η * ∑ ν ∈ T, b ν + D * ∑ ν ∈ T.filter bad, s ν := by
  rw [sum_filter, mul_sum, mul_sum, ← sum_add_distrib, ← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun ν hν => ?_)
  by_cases h : bad ν
  · rw [if_pos h]
    have := hbad ν hν h
    have := mul_nonneg hη (hb ν hν)
    linarith
  · rw [if_neg h]
    simpa using hgood ν hν h

/-- Pages 6 and 7: the part of r' prime to C*. It divides n whenever r divides C* n. -/
def oddFree131 (Cstar r : ℕ) : ℕ :=
  ∏ p ∈ (r.primeFactors.filter (fun p => 2 < p)).filter (fun p => ¬ p ∣ Cstar), p

theorem oddFree_odd131 (Cstar r : ℕ) : Odd (oddFree131 Cstar r) := by
  refine Finset.prod_induction (fun p => p) Odd (fun _ _ ha hb => ha.mul hb) odd_one
    (fun p hp => ?_)
  obtain ⟨hp1, -⟩ := mem_filter.mp hp
  obtain ⟨hp2, hp3⟩ := mem_filter.mp hp1
  exact (Nat.prime_of_mem_primeFactors hp2).odd_of_ne_two (by omega)

theorem oddRad_le131 {Cstar : ℕ} (hC : 0 < Cstar) (r : ℕ) :
    oddRad131 r ≤ oddFree131 Cstar r * Cstar := by
  have h := Finset.prod_filter_mul_prod_filter_not (r.primeFactors.filter (fun p => 2 < p))
    (fun p => ¬ p ∣ Cstar) (fun p => p)
  have hU : ∏ p ∈ (r.primeFactors.filter (fun p => 2 < p)).filter (fun p => ¬ ¬ p ∣ Cstar), p ∣
      Cstar := by
    refine Finset.prod_primes_dvd Cstar (fun p hp => ?_) (fun p hp => ?_)
    · exact (Nat.prime_of_mem_primeFactors
        (mem_filter.mp (mem_filter.mp hp).1).1).prime
    · exact not_not.mp (mem_filter.mp hp).2
  have hU' := Nat.le_of_dvd hC hU
  unfold oddRad131 oddFree131
  rw [← h]
  exact Nat.mul_le_mul_left _ hU'

theorem oddFree_dvd131 {Cstar r n : ℕ} (h : r ∣ Cstar * n) : oddFree131 Cstar r ∣ n := by
  refine Finset.prod_primes_dvd n (fun p hp => ?_) (fun p hp => ?_)
  · exact (Nat.prime_of_mem_primeFactors (mem_filter.mp (mem_filter.mp hp).1).1).prime
  · obtain ⟨hp1, hp2⟩ := mem_filter.mp hp
    have hp3 := (mem_filter.mp hp1).1
    have hpp := Nat.prime_of_mem_primeFactors hp3
    have hd := (Nat.dvd_of_mem_primeFactors hp3).trans h
    exact ((Nat.Prime.dvd_mul hpp).mp hd).resolve_left hp2

/-- The averaging step of pages 6 and 7: fix all exponents but one and apply a bound
for A(m, s) on the window. -/
theorem tuple_sum_dvd_le131 {j X N s : ℕ} {ε' : ℝ}
    (hA : ∀ m : ℕ, (X : ℝ) / 2 ≤ m → m ≤ X → Amr X m s ≤ ε' * Lg X)
    (hε' : 0 ≤ ε') (hL : 1 ≤ Lg X)
    (hw : 6 * (j + 1) * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ ≤ X) (hN : N ∈ evenJ131 X) :
    ∑ ν ∈ exponentTuples131 (j + 1) ⌊Lg X - Real.sqrt (Lg X)⌋₊,
        (if s ∣ N - tuplePower131 ν then Sing (N - tuplePower131 ν) else 0) ≤
      ε' * Lg X ^ (j + 1) := by
  obtain ⟨hN1, hN2, -, hN4⟩ := evenJ_nat131 hN
  have hsq : Real.sqrt (Lg X) ≤ Lg X :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  have ht0 : 0 ≤ Lg X - Real.sqrt (Lg X) := by linarith
  have hfl := Nat.floor_le ht0
  have hML : ((⌊Lg X - Real.sqrt (Lg X)⌋₊ : ℕ) : ℝ) ≤ Lg X := by
    linarith [Real.sqrt_nonneg (Lg X)]
  set M := ⌊Lg X - Real.sqrt (Lg X)⌋₊ with hMdef
  have hpi : exponentTuples131 (j + 1) M =
      ((Icc 1 M) ×ˢ exponentTuples131 j M).map
        (Fin.consEquiv (fun _ : Fin (j + 1) => ℕ)).toEmbedding := by
    have := Finset.filter_piFinset_eq_map_consEquiv (fun _ : Fin (j + 1) => Icc 1 M)
      (fun _ => True)
    simp only [Finset.filter_true] at this
    exact this
  rw [hpi, Finset.sum_map, Finset.sum_product_right]
  have hin : ∀ t ∈ exponentTuples131 j M,
      ∑ a ∈ Icc 1 M,
        (if s ∣ N - tuplePower131 ((Fin.consEquiv (fun _ : Fin (j + 1) => ℕ)).toEmbedding (a, t))
          then Sing (N - tuplePower131
            ((Fin.consEquiv (fun _ : Fin (j + 1) => ℕ)).toEmbedding (a, t))) else 0) ≤
        ε' * Lg X := by
    intro t ht
    have htp := tuplePower_le131 ht
    have h6 : 6 * tuplePower131 t + 6 * 2 ^ M ≤ X := by
      have : 6 * (j + 1) * 2 ^ M = 6 * (j * 2 ^ M) + 6 * 2 ^ M := by ring
      omega
    have hm1 : (X : ℝ) / 2 ≤ ((N - tuplePower131 t : ℕ) : ℝ) := by
      have : X ≤ 2 * (N - tuplePower131 t) := by omega
      have h' : (X : ℝ) ≤ 2 * ((N - tuplePower131 t : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    have hm2 : N - tuplePower131 t ≤ X := by omega
    refine le_trans (le_of_eq ?_) (hA _ hm1 hm2)
    unfold Amr
    rw [sum_filter]
    refine sum_congr rfl fun a ha => ?_
    have ha2 : 2 ^ a ≤ 2 ^ M := Nat.pow_le_pow_right (by norm_num) (mem_Icc.mp ha).2
    have hlt : 2 ^ a < N - tuplePower131 t := by omega
    have hp : tuplePower131 ((Fin.consEquiv (fun _ : Fin (j + 1) => ℕ)).toEmbedding (a, t)) =
        2 ^ a + tuplePower131 t := by
      simp only [tuplePower131, Equiv.toEmbedding_apply, Fin.consEquiv_apply,
        Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ]
    have hsub : N - (2 ^ a + tuplePower131 t) = N - tuplePower131 t - 2 ^ a := by omega
    rw [hp, hsub]
    by_cases hd : s ∣ N - tuplePower131 t - 2 ^ a
    · rw [if_pos hd, if_pos ⟨hlt, hd⟩]
    · rw [if_neg hd, if_neg (fun h => hd h.2)]
  calc _ ≤ ∑ _t ∈ exponentTuples131 j M, ε' * Lg X := sum_le_sum hin
    _ = (M : ℝ) ^ j * (ε' * Lg X) := by
      rw [sum_const, exponentTuples_card131, nsmul_eq_mul, Nat.cast_pow]
    _ ≤ Lg X ^ j * (ε' * Lg X) :=
      mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (Nat.cast_nonneg _) hML j)
        (mul_nonneg hε' (by linarith))
    _ = ε' * Lg X ^ (j + 1) := by ring

/-- PROVED from Lemma 6.2. Displays 12 to 14 on pages 6 and 7: for moduli as in Corollary 4.2,
the singular series sum over tuples with N - M in J_2 is at most any fixed fraction of L^k.
This is the honest J_2 estimate; the old leaf with this name compared integrals instead. -/
theorem major_arcs_j2_131 (k : ℕ) (hk : 1 ≤ k) (K₁ Cstar : ℕ) (hC : 0 < Cstar) (c : ℝ)
    (hc : 0 < c) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ E : Finset ℕ, ExceptionalModuli131 K₁ c X E →
      ∀ N ∈ evenJ131 X, ∀ B ⊆ tuples131 k X,
        (∀ ν ∈ B, ¬ Nonexceptional131 Cstar E (N - tuplePower131 ν)) →
        ∑ ν ∈ B, Sing (N - tuplePower131 ν) ≤ ε * Lg X ^ k := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  have hK : (0 : ℝ) < (K₁ : ℝ) + 1 := by positivity
  set ε' : ℝ := ε / ((K₁ : ℝ) + 1) with hε'def
  have hε' : 0 < ε' := div_pos hε hK
  have hεK : ((K₁ : ℝ) + 1) * ε' = ε := by
    rw [hε'def]
    field_simp
  obtain ⟨r₀, X₁, h62⟩ := lemma62_proved ε' hε'
  obtain ⟨X₂, hX₂⟩ := tuple_window131 (j + 1)
  have ht : Tendsto (fun X : ℕ => Lg X) atTop atTop :=
    (Real.tendsto_logb_atTop (by norm_num : (1 : ℝ) < 2)).comp tendsto_natCast_atTop_atTop
  obtain ⟨X₃, hX₃⟩ := (ht.eventually_ge_atTop
    ((r₀ : ℝ) * Cstar / c)).exists_forall_of_atTop
  refine ⟨max X₁ (max X₂ X₃), fun X hX E hE N hN B hB hbad => ?_⟩
  have hx1 : X₁ ≤ X := le_trans (le_max_left _ _) hX
  have hx2 : X₂ ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hx3 : X₃ ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
  obtain ⟨hL, hw⟩ := hX₂ X hx2
  have hL3 := hX₃ X hx3
  have hCr : (0 : ℝ) < Cstar := by exact_mod_cast hC
  have hLk : 0 ≤ Lg X ^ (j + 1) := by positivity
  have hsmall : ∀ r ∈ E, r₀ ≤ oddFree131 Cstar r := by
    intro r hr
    have h1 := hE.2 r hr
    have h2 : (oddRad131 r : ℝ) ≤ oddFree131 Cstar r * Cstar := by
      exact_mod_cast oddRad_le131 hC r
    have h3 : (r₀ : ℝ) * Cstar ≤ c * Lg X := by
      rw [div_le_iff₀ hc] at hL3
      linarith
    have h4 : c * Lg X ≤ c * Lg X ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) hc.le
    have h5 : (r₀ : ℝ) * Cstar ≤ oddFree131 Cstar r * Cstar := by linarith
    exact_mod_cast le_of_mul_le_mul_right h5 hCr
  have hLnn : 0 ≤ Lg X := by linarith
  have hone : ∀ r ∈ E, ∑ ν ∈ tuples131 (j + 1) X,
      (if oddFree131 Cstar r ∣ N - tuplePower131 ν then Sing (N - tuplePower131 ν) else 0) ≤
        ε' * Lg X ^ (j + 1) := by
    intro r hr
    have ho := oddFree_odd131 Cstar r
    have hA : ∀ m : ℕ, (X : ℝ) / 2 ≤ m → m ≤ X → Amr X m (oddFree131 Cstar r) ≤ ε' * Lg X :=
      fun m hm1 hm2 => h62 X hx1 m _ hm1 hm2 ho.pos ho (hsmall r hr)
    exact tuple_sum_dvd_le131 hA hε'.le hL hw hN
  have hnn : ∀ (ν : Fin (j + 1) → ℕ), ∀ r ∈ E, 0 ≤
      (if oddFree131 Cstar r ∣ N - tuplePower131 ν then
        Sing (N - tuplePower131 ν) else 0) := by
    intro ν r _
    split_ifs
    · exact Sing_nonneg131 _
    · exact le_rfl
  calc ∑ ν ∈ B, Sing (N - tuplePower131 ν)
      ≤ ∑ ν ∈ B, ∑ r ∈ E,
        (if oddFree131 Cstar r ∣ N - tuplePower131 ν then Sing (N - tuplePower131 ν) else 0) := by
        refine sum_le_sum fun ν hν => ?_
        have hex : ∃ r ∈ E, r ∣ Cstar * (N - tuplePower131 ν) := by
          by_contra hcon
          exact hbad ν hν (fun r hr hd => hcon ⟨r, hr, hd⟩)
        obtain ⟨r, hr, hd⟩ := hex
        have hs := single_le_sum (hnn ν) hr
        rwa [if_pos (oddFree_dvd131 hd)] at hs
    _ ≤ ∑ ν ∈ tuples131 (j + 1) X, ∑ r ∈ E,
        (if oddFree131 Cstar r ∣ N - tuplePower131 ν then Sing (N - tuplePower131 ν) else 0) :=
        sum_le_sum_of_subset_of_nonneg hB fun ν _ _ => sum_nonneg (hnn ν)
    _ = ∑ r ∈ E, ∑ ν ∈ tuples131 (j + 1) X,
        (if oddFree131 Cstar r ∣ N - tuplePower131 ν then Sing (N - tuplePower131 ν) else 0) :=
        sum_comm
    _ ≤ ∑ _r ∈ E, ε' * Lg X ^ (j + 1) := sum_le_sum hone
    _ = (E.card : ℝ) * (ε' * Lg X ^ (j + 1)) := by rw [sum_const, nsmul_eq_mul]
    _ ≤ ((K₁ : ℝ) + 1) * (ε' * Lg X ^ (j + 1)) := by
        refine mul_le_mul_of_nonneg_right ?_ (mul_nonneg hε'.le hLk)
        have : (E.card : ℝ) ≤ K₁ := by exact_mod_cast hE.1
        linarith
    _ = ε * Lg X ^ (j + 1) := by
        linear_combination (Lg X ^ (j + 1)) * hεK

/-- The statement of the leaf `major_arcs_j1_131`, Corollary 4.2. -/
def Cor42Statement131 : Prop :=
  ∀ η : ℝ, 0 < η →
    ∃ (K₁ Cstar : ℕ) (c A : ℝ), 0 < Cstar ∧ 0 < c ∧ 0 ≤ A ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∃ (P : ℝ) (E : Finset ℕ), AdmissibleP131 X P ∧ ExceptionalModuli131 K₁ c X E ∧
        (∀ n ∈ evenWindow131 X, Nonexceptional131 Cstar E n →
          |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) ∧
        (∀ n ∈ evenWindow131 X, |binaryMajor131 X n P| ≤ A * n * Sing n)

/-- The statement of the leaf `major_arcs_combine131`, displays 15 to 24. -/
def SingularAverageStatement131 : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ ε : ℝ, 0 < ε →
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ N ∈ evenJ131 X,
      |∑ ν ∈ tuples131 k X,
          ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) -
        coefficient131 k N * N * Lg X ^ k| ≤ ε * N * Lg X ^ k

/-- LEAF, CITED. Corollary 4.2 on page 6 together with its last sentence, for the BINARY
major arc integral R_M(n) of display 4. The moduli E are the generalised exceptional moduli,
display 9 is `Nonexceptional131`, and display 10 is the bound on `oddRad131`.
P is produced by the statement, not given: page 3 says P cannot be fixed directly.
The constant A may depend on eta, which the use in display 14 allows.
The window [X/2, X] replaces J(X) because displays 11 and 12 use n = N - M below 2X/3 when N
is near 2X/3; Lemma 6.2 is stated on the same window, and Zaccagnini circle.pdf 7.2 states
the corollary for all even n up to the size parameter.
Source outside P0045: Pintz, ELAZ 2004, Theorem 10, cited as Lemma 4.1; Jutila; Iwaniec. -/
theorem major_arcs_j1_131 (η : ℝ) (hη : 0 < η) :
    ∃ (K₁ Cstar : ℕ) (c A : ℝ), 0 < Cstar ∧ 0 < c ∧ 0 ≤ A ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
      ∃ (P : ℝ) (E : Finset ℕ), AdmissibleP131 X P ∧ ExceptionalModuli131 K₁ c X E ∧
        (∀ n ∈ evenWindow131 X, Nonexceptional131 Cstar E n →
          |binaryMajor131 X n P - n * Sing n| ≤ η * n * Sing n) ∧
        (∀ n ∈ evenWindow131 X, |binaryMajor131 X n P| ≤ A * n * Sing n) := by
  sorry

/-- LEAF. Displays 15 to 24 on pages 7 and 8, with the factor 2c0 restored from display 2.
The weighted singular series sum over tuples in [1, L']^k is 2c0 C(k,N) N L^k up to
o(N L^k), uniformly on even N in J(X). This is arithmetic: Lemma 6.1, the expansion of S(n)
in display 2, display 19, display 20 with A'(N) of display 28, and the bound 30.
No analytic input. The parts already in the lab are `block_jcount_bounds131`,
`coefficient_tail_small131` and `sing_le_two_H`. -/
theorem major_arcs_combine131 (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∀ N ∈ evenJ131 X,
      |∑ ν ∈ tuples131 k X,
          ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) -
        coefficient131 k N * N * Lg X ^ k| ≤ ε * N * Lg X ^ k := by
  sorry

/-- LEAF. Page 3, an admissible P always exists for large X. -/
theorem admissible_P_exists131 :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∃ P : ℝ, AdmissibleP131 X P := by
  refine ⟨1, fun X hX => ⟨(X : ℝ) ^ ((2:ℝ) / 5), ?_⟩⟩
  dsimp [AdmissibleP131]
  exact ⟨le_rfl, Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hX) (by norm_num)⟩

/-- The uniform bound for the corrected coefficient, displays 19, 23 and 26. -/
theorem coefficient_le131 {k : ℕ} (hk : 1 ≤ k) (N : ℕ) :
    coefficient131 k N ≤ 2 * LeanLab.ChenExplicit.twinC * ∑' d, seriesTerm d := by
  unfold coefficient131
  exact mul_le_mul_of_nonneg_left (Ck_le_series131 hk N)
    (mul_nonneg (by norm_num) LeanLab.ChenExplicit.twinC_pos.le)

/-- CONDITIONAL on the two leaf statements, with no sorry of its own. Display 25 follows
from Corollary 4.2, the proved J_2 estimate and the singular series average. -/
theorem major_asymptotic_of_leaves131 (hj1 : Cor42Statement131)
    (hcomb : SingularAverageStatement131) (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∃ P : ℝ, AdmissibleP131 X P ∧
      ∀ N ∈ evenJ131 X,
        |majorContribution131 k X N P - coefficient131 k N * N * Lg X ^ k| ≤
          ε * N * Lg X ^ k := by
  classical
  set B : ℝ := 2 * LeanLab.ChenExplicit.twinC * ∑' d, seriesTerm d with hB
  have hB0 : 0 ≤ B := by
    refine le_trans ?_ (coefficient_le131 hk 0)
    exact mul_nonneg (mul_nonneg (by norm_num) LeanLab.ChenExplicit.twinC_pos.le)
      (by linarith [Ck_ge_one131 hk 0])
  have hB1 : 0 < B + 1 := by linarith
  set η : ℝ := ε / (3 * (B + 1)) with hηdef
  have hη : 0 < η := div_pos hε (mul_pos (by norm_num) hB1)
  obtain ⟨K₁, Cstar, c, A, hC, hc, hA, X₁, hX₁⟩ := hj1 η hη
  have hA1 : 0 < A + 1 := by linarith
  have hε₂ : 0 < ε / (3 * (A + 1)) := div_pos hε (mul_pos (by norm_num) hA1)
  obtain ⟨X₂, hX₂⟩ := major_arcs_j2_131 k hk K₁ Cstar hC c hc _ hε₂
  obtain ⟨X₃, hX₃⟩ := hcomb k hk (ε / 3) (by positivity)
  obtain ⟨X₄, hX₄⟩ := hcomb k hk 1 one_pos
  obtain ⟨X₅, hX₅⟩ := tuple_window131 k
  refine ⟨max X₁ (max X₂ (max X₃ (max X₄ X₅))), fun X hX => ?_⟩
  have hx1 : X₁ ≤ X := by omega
  have hx2 : X₂ ≤ X := by omega
  have hx3 : X₃ ≤ X := by omega
  have hx4 : X₄ ≤ X := by omega
  have hx5 : X₅ ≤ X := by omega
  obtain ⟨P, E, hP, hE, hgood, hup⟩ := hX₁ X hx1
  refine ⟨P, hP, fun N hN => ?_⟩
  obtain ⟨hL, hw⟩ := hX₅ X hx5
  have hL0 : 0 ≤ Lg X := by linarith
  have hLk : 0 ≤ Lg X ^ k := by positivity
  obtain ⟨hN1, hN2, -, hN4⟩ := evenJ_nat131 hN
  have hNr : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hsm : ∀ ν ∈ tuples131 k X, 6 * tuplePower131 ν ≤ X := by
    intro ν hν
    have := tuplePower_le131 hν
    have h6 : 6 * (k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊) =
        6 * k * 2 ^ ⌊Lg X - Real.sqrt (Lg X)⌋₊ := by ring
    omega
  have hle : ∀ ν ∈ tuples131 k X, tuplePower131 ν ≤ N := by
    intro ν hν
    have := hsm ν hν
    omega
  have hwin : ∀ ν ∈ tuples131 k X, N - tuplePower131 ν ∈ evenWindow131 X := fun ν hν =>
    window_mem131 hN (hsm ν hν) (tuplePower_even131 hν)
  set Bad := (tuples131 k X).filter
    (fun ν => ¬ Nonexceptional131 Cstar E (N - tuplePower131 ν)) with hBad
  have hsplit : |∑ ν ∈ tuples131 k X, binaryMajor131 X (N - tuplePower131 ν) P -
      ∑ ν ∈ tuples131 k X, ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν)| ≤
      η * ∑ ν ∈ tuples131 k X, ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) +
        (A + 1) * N * ∑ ν ∈ Bad, Sing (N - tuplePower131 ν) := by
    refine split_bound131 (tuples131 k X)
      (fun ν => ¬ Nonexceptional131 Cstar E (N - tuplePower131 ν))
      (fun ν => binaryMajor131 X (N - tuplePower131 ν) P)
      (fun ν => ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν))
      (fun ν => Sing (N - tuplePower131 ν)) η ((A + 1) * N) hη.le
      (mul_nonneg hA1.le hNr)
      (fun ν _ => mul_nonneg (Nat.cast_nonneg _) (Sing_nonneg131 _))
      (fun ν _ => Sing_nonneg131 _) ?_ ?_
    · intro ν hν hb
      have h := hgood _ (hwin ν hν) (not_not.mp hb)
      have e : η * ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) =
          η * (((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν)) := by ring
      rw [e] at h
      exact h
    · intro ν hν _
      show |binaryMajor131 X (N - tuplePower131 ν) P -
          ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν)| ≤
        (A + 1) * N * Sing (N - tuplePower131 ν)
      have hu := abs_le.mp (hup _ (hwin ν hν))
      have hS := Sing_nonneg131 (N - tuplePower131 ν)
      have hn : ((N - tuplePower131 ν : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le _ _
      have hn0 : (0 : ℝ) ≤ ((N - tuplePower131 ν : ℕ) : ℝ) := Nat.cast_nonneg _
      have h0 := mul_nonneg hn0 hS
      have h1 : A * ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) ≤
          A * N * Sing (N - tuplePower131 ν) :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hA) hS
      have h2 : ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) ≤
          N * Sing (N - tuplePower131 ν) := mul_le_mul_of_nonneg_right hn hS
      rw [abs_le]
      constructor <;> linarith [hu.1, hu.2]
  have hjj := hX₂ X hx2 E hE N hN Bad (filter_subset _ _) (fun ν hν => (mem_filter.mp hν).2)
  have hc3 := hX₃ X hx3 N hN
  have hc1 := hX₄ X hx4 N hN
  rw [← major_expand131 k X N P hle] at hsplit
  set W := ∑ ν ∈ tuples131 k X,
    ((N - tuplePower131 ν : ℕ) : ℝ) * Sing (N - tuplePower131 ν) with hW
  set M := majorContribution131 k X N P with hM
  have hNL : 0 ≤ (N : ℝ) * Lg X ^ k := mul_nonneg hNr hLk
  have hcoef : coefficient131 k N * N * Lg X ^ k ≤ B * ((N : ℝ) * Lg X ^ k) := by
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (coefficient_le131 hk N) hNL
  have hWup : W ≤ (B + 1) * ((N : ℝ) * Lg X ^ k) := by
    have := (abs_le.mp hc1).2
    nlinarith
  have hterm1 : η * W ≤ ε / 3 * ((N : ℝ) * Lg X ^ k) := by
    have h := mul_le_mul_of_nonneg_left hWup hη.le
    have he : η * ((B + 1) * ((N : ℝ) * Lg X ^ k)) = ε / 3 * ((N : ℝ) * Lg X ^ k) := by
      rw [hηdef]
      field_simp
    rw [he] at h
    exact h
  have hterm2 : (A + 1) * N * ∑ ν ∈ Bad, Sing (N - tuplePower131 ν) ≤
      ε / 3 * ((N : ℝ) * Lg X ^ k) := by
    have h := mul_le_mul_of_nonneg_left hjj (mul_nonneg hA1.le hNr)
    have he : (A + 1) * N * (ε / (3 * (A + 1)) * Lg X ^ k) =
        ε / 3 * ((N : ℝ) * Lg X ^ k) := by
      field_simp
    rw [he] at h
    exact h
  have hfin := abs_sub_le M W (coefficient131 k N * N * Lg X ^ k)
  have hc3' : |W - coefficient131 k N * N * Lg X ^ k| ≤ ε / 3 * ((N : ℝ) * Lg X ^ k) := by
    calc _ ≤ _ := hc3
      _ = _ := by ring
  calc _ ≤ _ := hfin
    _ ≤ ε / 3 * ((N : ℝ) * Lg X ^ k) + ε / 3 * ((N : ℝ) * Lg X ^ k) +
        ε / 3 * ((N : ℝ) * Lg X ^ k) := by linarith
    _ = ε * N * Lg X ^ k := by ring

/-- Assembly of the major arc asymptotic, display 25, from the re-cut decomposition. -/
theorem major_asymptotic131_assembly (k : ℕ) (hk : 1 ≤ k) (ε : ℝ) (hε : 0 < ε) :
    ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X → ∃ P : ℝ, AdmissibleP131 X P ∧
      ∀ N ∈ evenJ131 X,
        |majorContribution131 k X N P - coefficient131 k N * N * Lg X ^ k| ≤
          ε * N * Lg X ^ k :=
  major_asymptotic_of_leaves131 major_arcs_j1_131 major_arcs_combine131 k hk ε hε

end

end LeanLab.LPZ2007
