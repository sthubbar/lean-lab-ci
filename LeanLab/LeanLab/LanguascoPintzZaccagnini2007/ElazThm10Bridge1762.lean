import LeanLab.LanguascoPintzZaccagnini2007.Decomp481a
import LeanLab.LanguascoPintzZaccagnini2007.Convolution131
import LeanLab.LPZ2007.Prep1121J131FourInputs

/-!
U-1762. Pintz, Recent results on the Goldbach conjecture, ELAZ 2004 proceedings,
Franz Steiner 2006, pages 220 to 254, Theorem 10, journal page 245, read on the page image
of `papers/Pintz2006-ELAZ.pdf` page 28, with the notation of pages 243 and 244.

`ElazTheorem10Statement1762` encodes the printed Theorem 10 at the instance used by P0045,
theta = 0.41 with the window [X^0.4, X^0.41] for P. Clause by clause:
* (15.4): S(alpha) is the sum of log p e(p alpha) over primes X_1 < p <= X, X_1 = X^(1 - eps_1).
  The exponent eps_1 may depend on H and T here, which only weakens the hypothesis.
* (15.5), (15.6): R_1(m) is the integral of S^2(alpha) e(-m alpha) over the major arcs (15.2).
* (15.13), (15.14): the zero box, `zeroBox481`, primitive characters of modulus at most P.
* (15.17): A = 1 at a zero and A = -1 at the pole. P0045 prints the opposite convention;
  `elazSign_mul1762` shows the two products A(rho_i) A(rho_j) agree.
* (15.18): even m in [X/2, X], remainder O(X e^(-cH)) + O(X / sqrt T), no factor sigma(m).
* (15.19): |sigma(chi_i, chi_j, m)| <= sigma(m), with equality at the pole pair.
* (15.20), (15.21): |sigma| <= eps unless r_i | C(eps) m, r_j | C(eps) m and
  cond(chi_i conj chi_j) < eps^-3. The conductor enters through an existential `cnd`, which
  only weakens the hypothesis; the bridge does not use the third condition.
* Zeros with multiplicity: the same multiplicity clause as `Lemma41Statement481`.

The one step that is not a weakening is the change of the prime sum: P0045 and
`Lemma41Statement481` use von Mangoldt weights over 1..X. `elaz_major_transfer1762` proves,
by Parseval and Mathlib's Chebyshev bounds, that the two major arc integrals differ by at most
X e^(-cH) for X large, and `lemma41_window_of_elaz1762` assembles the rest.

Result: `Lemma41Statement481` and its window form on [X/2, X] follow from the printed
Theorem 10 with no further input. AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.LPZ2007

open Finset Real MeasureTheory Filter
open scoped Classical

noncomputable section

/-- ELAZ (15.4): the coefficient log p for primes X^(1 - eps_1) < p, zero otherwise. -/
def elazCoeff1762 (X : ℕ) (ε₁ : ℝ) (m : ℕ) : ℝ :=
  if m.Prime ∧ (X : ℝ) ^ (1 - ε₁) < m then Real.log m else 0

/-- ELAZ (15.4): S(alpha), the prime sum over X_1 < p <= X with weight log p. -/
def elazPrimeSum1762 (X : ℕ) (ε₁ α : ℝ) : ℂ :=
  ∑ m ∈ Icc 1 X, ((elazCoeff1762 X ε₁ m : ℝ) : ℂ) * phase131 ((m : ℝ) * α)

/-- ELAZ (15.6): R_1(m), the major arc integral with the ELAZ prime sum. -/
def elazMajor1762 (X n : ℕ) (P ε₁ : ℝ) : ℂ :=
  ∫ α in majorArcs131 X P, elazPrimeSum1762 X ε₁ α ^ 2 * phase131 (-(n : ℝ) * α)

/-- ELAZ (15.17): A = -1 at the pole, index 0, and A = 1 at every zero. -/
def elazSign1762 {K : ℕ} (i : Fin (K + 1)) : ℂ := if i = 0 then -1 else 1

/-- The two sign conventions give the same products A(rho_i) A(rho_j). -/
theorem elazSign_mul1762 {K : ℕ} (i j : Fin (K + 1)) :
    elazSign1762 i * elazSign1762 j = zeroSign481 i * zeroSign481 j := by
  unfold elazSign1762 zeroSign481
  split_ifs <;> ring

/-- ELAZ Theorem 10, page 245, as printed, at theta = 0.41 and eps = 0.01 for the P window,
on even m in [X/2, X]. -/
def ElazTheorem10Statement1762 : Prop :=
  ∃ c ε₀ B H₀ T₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ 0 ≤ B ∧
    ∃ Cε : ℝ → ℕ, (∀ ε, 0 < Cε ε) ∧
    ∀ H T : ℝ, H₀ ≤ H → T₀ ≤ T →
      ∃ ε₁ : ℝ, 0 < ε₁ ∧ ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        ∃ P : ℝ, AdmissibleP131 X P ∧
        ∃ (K : ℕ) (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
          (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ) (cnd : Fin (K + 1) → Fin (K + 1) → ℕ),
          (z 0).1 = 1 ∧ (z 0).2.2 = 1 ∧
          (∀ i, i ≠ 0 → z i ∈ zeroBox481 X H T P) ∧
          (∀ w, ((univ.filter (fun i => i ≠ 0 ∧ z i = w)).card : ℕ) ≤
            analyticOrderNatAt (Lfun481 w.2.1) w.2.2) ∧
          (∀ n ∈ evenWindow131 X, Sg 0 0 n = (Sing n : ℂ)) ∧
          (∀ i j n, n ∈ evenWindow131 X → ‖Sg i j n‖ ≤ Sing n) ∧
          (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ evenWindow131 X →
            ¬ ((z i).1 ∣ Cε ε * n ∧ (z j).1 ∣ Cε ε * n ∧ (cnd i j : ℝ) < ε ^ (-3 : ℤ)) →
              ‖Sg i j n‖ ≤ ε) ∧
          ∀ n ∈ evenWindow131 X,
            ‖elazMajor1762 X n P ε₁ -
              ∑ i, ∑ j, Sg i j n * elazSign1762 i * elazSign1762 j *
                gammaPair481 (z i).2.2 (z j).2.2 n‖ ≤
              B * ((X : ℝ) * Real.exp (-c * H) + X / Real.sqrt T)

/-- `Lemma41Statement481` with the window `W X` in place of `evenJ131 X`. -/
def Lemma41OnWindow1762 (W : ℕ → Finset ℕ) : Prop :=
  ∃ c ε₀ B H₀ T₀ : ℝ, 0 < c ∧ 0 < ε₀ ∧ 0 ≤ B ∧
    ∃ Cε : ℝ → ℕ, (∀ ε, 0 < Cε ε) ∧
    ∀ H T : ℝ, H₀ ≤ H → T₀ ≤ T →
      ∃ X₀ : ℕ, ∀ X : ℕ, X₀ ≤ X →
        ∃ P : ℝ, AdmissibleP131 X P ∧
        ∃ (K : ℕ) (z : Fin (K + 1) → Σ r : ℕ, DirichletCharacter ℂ r × ℂ)
          (Sg : Fin (K + 1) → Fin (K + 1) → ℕ → ℂ),
          (z 0).1 = 1 ∧ (z 0).2.2 = 1 ∧
          (∀ i, i ≠ 0 → z i ∈ zeroBox481 X H T P) ∧
          (∀ w, ((univ.filter (fun i => i ≠ 0 ∧ z i = w)).card : ℕ) ≤
            analyticOrderNatAt (Lfun481 w.2.1) w.2.2) ∧
          (∀ n ∈ W X, Sg 0 0 n = (Sing n : ℂ)) ∧
          (∀ i j n, n ∈ W X → ‖Sg i j n‖ ≤ Sing n) ∧
          (∀ ε : ℝ, 0 < ε → ε < ε₀ → ∀ i j n, n ∈ W X →
            (¬ (z i).1 ∣ Cε ε * n ∨ ¬ (z j).1 ∣ Cε ε * n) → ‖Sg i j n‖ ≤ ε) ∧
          ∀ n ∈ W X,
            |binaryMajor131 X n P -
              (∑ i, ∑ j, Sg i j n * zeroSign481 i * zeroSign481 j *
                gammaPair481 (z i).2.2 (z j).2.2 n).re| ≤
              B * ((X : ℝ) * Real.exp (-c * H) + X / Real.sqrt T)

theorem lemma41OnWindow_evenJ1762 : Lemma41OnWindow1762 evenJ131 ↔ Lemma41Statement481 :=
  Iff.rfl

/-- The window statement is antitone in the window. -/
theorem lemma41OnWindow_mono1762 {W V : ℕ → Finset ℕ} (hWV : ∀ X, V X ⊆ W X)
    (h : Lemma41OnWindow1762 W) : Lemma41OnWindow1762 V := by
  obtain ⟨c, ε₀, B, H₀, T₀, hc, hε₀, hB, Cε, hCε, h⟩ := h
  refine ⟨c, ε₀, B, H₀, T₀, hc, hε₀, hB, Cε, hCε, fun H T hH hT => ?_⟩
  obtain ⟨X₀, h⟩ := h H T hH hT
  refine ⟨X₀, fun X hX => ?_⟩
  obtain ⟨P, hP, K, z, Sg, h0, h1, hbox, hmult, hpole, hbd, hsmall, hrem⟩ := h X hX
  exact ⟨P, hP, K, z, Sg, h0, h1, hbox, hmult, fun n hn => hpole n (hWV X hn),
    fun i j n hn => hbd i j n (hWV X hn),
    fun ε h1 h2 i j n hn => hsmall ε h1 h2 i j n (hWV X hn),
    fun n hn => hrem n (hWV X hn)⟩

theorem evenJ_subset_window1762 (X : ℕ) : evenJ131 X ⊆ evenWindow131 X := by
  intro n hn
  simp only [evenJ131, evenWindow131, mem_filter] at hn ⊢
  refine ⟨hn.1, hn.2.1, le_trans ?_ hn.2.2⟩
  have : (0 : ℝ) ≤ X := Nat.cast_nonneg X
  linarith

/-! ### Parseval on a shifted unit interval -/

theorem parseval_icc1762 (a : ℕ → ℂ) (X : ℕ) (s : ℝ) :
    (∫ α in s..s + 1, ‖∑ m ∈ Icc 1 X, a m * phase131 ((m : ℝ) * α)‖ ^ 2) =
      ∑ m ∈ Icc 1 X, ‖a m‖ ^ 2 := by
  set b : ℕ → ℂ := fun n => if 1 ≤ n then a n else 0 with hb
  have hsum : ∀ α : ℝ, (∑ m ∈ Icc 1 X, a m * phase131 ((m : ℝ) * α)) =
      ∑ m ∈ range (X + 1), b m * LeanLab.PNTPort.LargeSieve.e (m * α) := by
    intro α
    rw [range_eq_Ico]
    apply sum_subset_zero_on_sdiff
    · intro m hm
      simp only [mem_Icc] at hm
      simp only [mem_Ico]
      omega
    · intro m hm
      simp only [Finset.mem_sdiff, mem_Ico, mem_Icc] at hm
      have : m = 0 := by omega
      simp [hb, this]
    · intro m hm
      simp only [mem_Icc] at hm
      simp [hb, hm.1, phase_eq_library131]
  have hsq : ∀ m ∈ Icc 1 X, ‖a m‖ ^ 2 = ‖b m‖ ^ 2 := by
    intro m hm
    simp only [mem_Icc] at hm
    simp [hb, hm.1]
  have hsq' : (∑ m ∈ Icc 1 X, ‖a m‖ ^ 2) = ∑ m ∈ range (X + 1), ‖b m‖ ^ 2 := by
    rw [range_eq_Ico]
    apply sum_subset_zero_on_sdiff
    · intro m hm
      simp only [mem_Icc] at hm
      simp only [mem_Ico]
      omega
    · intro m hm
      simp only [Finset.mem_sdiff, mem_Ico, mem_Icc] at hm
      have : m = 0 := by omega
      simp [hb, this]
    · exact hsq
  simp_rw [hsum]
  rw [hsq']
  have hp : Function.Periodic
      (fun α : ℝ => ‖∑ m ∈ range (X + 1), b m * LeanLab.PNTPort.LargeSieve.e (m * α)‖ ^ 2) 1 := by
    intro α
    simp only
    congr 2
    apply sum_congr rfl
    intro m _
    rw [show (m : ℝ) * (α + 1) = m * α + (m : ℤ) by push_cast; ring,
      ← phase_eq_library131, ← phase_add131, phase_int131, mul_one, phase_eq_library131]
  rw [hp.intervalIntegral_add_eq s (-(1 / 2 : ℝ))]
  norm_num only [neg_add_cancel_left]
  have h := LeanLab.PNTPort.Gallagher.parseval b (X + 1)
  convert h using 1

/-! ### Coefficients -/

theorem elazCoeff_nonneg1762 (X : ℕ) (ε₁ : ℝ) (m : ℕ) : 0 ≤ elazCoeff1762 X ε₁ m := by
  unfold elazCoeff1762
  split_ifs
  · exact Real.log_natCast_nonneg m
  · exact le_rfl

theorem elazCoeff_le1762 (X : ℕ) (ε₁ : ℝ) (m : ℕ) :
    elazCoeff1762 X ε₁ m ≤ ArithmeticFunction.vonMangoldt m := by
  unfold elazCoeff1762
  split_ifs with h
  · rw [ArithmeticFunction.vonMangoldt_apply_prime h.1]
  · exact ArithmeticFunction.vonMangoldt_nonneg

/-- The pointwise square bound behind the Cauchy step. -/
theorem mul_le_half_weighted1762 {a b t : ℝ} (ht : 0 < t) :
    a * b ≤ (t * a ^ 2 + t⁻¹ * b ^ 2) / 2 := by
  have e : t⁻¹ * (t * a - b) ^ 2 = t * a ^ 2 - 2 * a * b + t⁻¹ * b ^ 2 := by
    field_simp
    ring
  nlinarith [mul_nonneg (inv_nonneg.2 ht.le) (sq_nonneg (t * a - b))]

/-- The Lambda sum minus the ELAZ sum, as one exponential polynomial. -/
theorem primeSum_sub_elaz1762 (X : ℕ) (ε₁ α : ℝ) :
    primeSum131 X α - elazPrimeSum1762 X ε₁ α =
      ∑ m ∈ Icc 1 X, (((ArithmeticFunction.vonMangoldt m - elazCoeff1762 X ε₁ m : ℝ)) : ℂ) *
        phase131 ((m : ℝ) * α) := by
  unfold primeSum131 elazPrimeSum1762
  rw [← sum_sub_distrib]
  apply sum_congr rfl
  intro m _
  push_cast
  ring

theorem primeSum_add_elaz1762 (X : ℕ) (ε₁ α : ℝ) :
    primeSum131 X α + elazPrimeSum1762 X ε₁ α =
      ∑ m ∈ Icc 1 X, (((ArithmeticFunction.vonMangoldt m + elazCoeff1762 X ε₁ m : ℝ)) : ℂ) *
        phase131 ((m : ℝ) * α) := by
  unfold primeSum131 elazPrimeSum1762
  rw [← sum_add_distrib]
  apply sum_congr rfl
  intro m _
  push_cast
  ring

theorem expPoly_continuous1762 (X : ℕ) (a : ℕ → ℂ) :
    Continuous (fun α : ℝ => ∑ m ∈ Icc 1 X, a m * phase131 ((m : ℝ) * α)) := by
  apply continuous_finsetSum
  intro m _
  exact continuous_const.mul (phase_continuous131.comp (continuous_const.mul continuous_id))

/-- Parseval plus the weighted Cauchy step: the two major arc integrals differ by at most
(t D + U / t) / 2, with D and U the coefficient energies of the difference and the sum. -/
theorem elaz_major_transfer1762 {X : ℕ} {P ε₁ t : ℝ} (hX : 0 < X) (hP : 0 < P)
    (hQ : P + 2 ≤ arcQ131 X P) (ht : 0 < t) (n : ℕ) :
    ‖(∫ α in majorArcs131 X P, primeSum131 X α ^ 2 * powerSum131 X α ^ 0 *
        phase131 (-(n : ℝ) * α)) - elazMajor1762 X n P ε₁‖ ≤
      (t * ∑ m ∈ Icc 1 X, (ArithmeticFunction.vonMangoldt m - elazCoeff1762 X ε₁ m) ^ 2 +
        t⁻¹ * ∑ m ∈ Icc 1 X, (ArithmeticFunction.vonMangoldt m + elazCoeff1762 X ε₁ m) ^ 2) / 2 := by
  set s : ℝ := 1 / arcQ131 X P with hs
  have hsub : majorArcs131 X P ⊆ Set.Icc s (s + 1) := majorArcs_subset131 hX hP hQ
  set D : ℝ → ℂ := fun α => ∑ m ∈ Icc 1 X,
    (((ArithmeticFunction.vonMangoldt m - elazCoeff1762 X ε₁ m : ℝ)) : ℂ) *
      phase131 ((m : ℝ) * α) with hD
  set U : ℝ → ℂ := fun α => ∑ m ∈ Icc 1 X,
    (((ArithmeticFunction.vonMangoldt m + elazCoeff1762 X ε₁ m : ℝ)) : ℂ) *
      phase131 ((m : ℝ) * α) with hU
  have hDc : Continuous D := expPoly_continuous1762 X _
  have hUc : Continuous U := expPoly_continuous1762 X _
  have hSc : Continuous (primeSum131 X) := primeSum_continuous131 X
  have hEc : Continuous (elazPrimeSum1762 X ε₁) := by
    unfold elazPrimeSum1762
    exact expPoly_continuous1762 X _
  have hph : Continuous (fun α : ℝ => phase131 (-(n : ℝ) * α)) :=
    phase_continuous131.comp (continuous_const.mul continuous_id)
  have hmeas := majorArcs_measurable131 X P
  have hfin : volume (Set.Icc s (s + 1)) ≠ ⊤ := by simp
  have hint : ∀ f : ℝ → ℂ, Continuous f → IntegrableOn f (majorArcs131 X P) := by
    intro f hf
    exact (hf.integrableOn_Icc).mono_set hsub
  have hdiff : (∫ α in majorArcs131 X P, primeSum131 X α ^ 2 * powerSum131 X α ^ 0 *
        phase131 (-(n : ℝ) * α)) - elazMajor1762 X n P ε₁ =
      ∫ α in majorArcs131 X P, D α * U α * phase131 (-(n : ℝ) * α) := by
    unfold elazMajor1762
    have hc1 : Continuous (fun α => primeSum131 X α ^ 2 * powerSum131 X α ^ 0 *
        phase131 (-(n : ℝ) * α)) :=
      ((hSc.pow 2).mul ((powerSum_continuous131 X).pow 0)).mul hph
    have hc2 : Continuous (fun α => elazPrimeSum1762 X ε₁ α ^ 2 * phase131 (-(n : ℝ) * α)) :=
      (hEc.pow 2).mul hph
    rw [← integral_sub (hint _ hc1) (hint _ hc2)]
    apply integral_congr_ae
    filter_upwards with α
    have h1 := primeSum_sub_elaz1762 X ε₁ α
    have h2 := primeSum_add_elaz1762 X ε₁ α
    simp only [hD, hU, ← h1, ← h2, pow_zero, mul_one]
    ring
  rw [hdiff]
  have hnorm : ∀ α, ‖D α * U α * phase131 (-(n : ℝ) * α)‖ = ‖D α‖ * ‖U α‖ := by
    intro α
    rw [norm_mul, norm_mul, phase_norm131, mul_one]
  calc ‖∫ α in majorArcs131 X P, D α * U α * phase131 (-(n : ℝ) * α)‖
      ≤ ∫ α in majorArcs131 X P, ‖D α * U α * phase131 (-(n : ℝ) * α)‖ :=
        norm_integral_le_integral_norm _
    _ = ∫ α in majorArcs131 X P, ‖D α‖ * ‖U α‖ := by simp_rw [hnorm]
    _ ≤ ∫ α in Set.Icc s (s + 1), ‖D α‖ * ‖U α‖ := by
        apply setIntegral_mono_set
        · exact (by fun_prop : Continuous fun α => ‖D α‖ * ‖U α‖).integrableOn_Icc
        · filter_upwards with α
          positivity
        · exact hsub.eventuallyLE
    _ ≤ ∫ α in Set.Icc s (s + 1), (t * ‖D α‖ ^ 2 + t⁻¹ * ‖U α‖ ^ 2) / 2 := by
        apply setIntegral_mono_on
        · exact (by fun_prop : Continuous fun α => ‖D α‖ * ‖U α‖).integrableOn_Icc
        · exact (by fun_prop :
            Continuous fun α => (t * ‖D α‖ ^ 2 + t⁻¹ * ‖U α‖ ^ 2) / 2).integrableOn_Icc
        · exact measurableSet_Icc
        · intro α _
          exact mul_le_half_weighted1762 ht
    _ = (t * ∫ α in s..s + 1, ‖D α‖ ^ 2) / 2 + (t⁻¹ * ∫ α in s..s + 1, ‖U α‖ ^ 2) / 2 := by
        rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
        rw [intervalIntegral.integral_div, intervalIntegral.integral_add, add_div,
          intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
        · exact (by fun_prop : Continuous fun α => t * ‖D α‖ ^ 2).intervalIntegrable _ _
        · exact (by fun_prop : Continuous fun α => t⁻¹ * ‖U α‖ ^ 2).intervalIntegrable _ _
    _ = _ := by
        rw [hD, hU, parseval_icc1762, parseval_icc1762, add_div]
        congr 3 <;> (apply sum_congr rfl; intro m _; rw [Complex.norm_real, Real.norm_eq_abs, sq_abs])

/-! ### Coefficient energies -/

theorem sum_energy1762 (X : ℕ) (ε₁ : ℝ) :
    ∑ m ∈ Icc 1 X, (ArithmeticFunction.vonMangoldt m + elazCoeff1762 X ε₁ m) ^ 2 ≤
      24 * X * Real.log X := by
  have h := LeanLab.BhowmikGrimmelt2026.mangoldt_energy84 X
  calc ∑ m ∈ Icc 1 X, (ArithmeticFunction.vonMangoldt m + elazCoeff1762 X ε₁ m) ^ 2
      ≤ ∑ m ∈ Icc 1 X, 4 * ArithmeticFunction.vonMangoldt m ^ 2 := by
        apply sum_le_sum
        intro m _
        have h0 := elazCoeff_nonneg1762 X ε₁ m
        have h1 := elazCoeff_le1762 X ε₁ m
        nlinarith
    _ = 4 * ∑ m ∈ Icc 1 X, ArithmeticFunction.vonMangoldt m ^ 2 := by rw [mul_sum]
    _ ≤ 24 * X * Real.log X := by linarith

theorem diff_energy1762 (X : ℕ) (ε₁ : ℝ) :
    ∑ m ∈ Icc 1 X, (ArithmeticFunction.vonMangoldt m - elazCoeff1762 X ε₁ m) ^ 2 ≤
      Real.log X * (2 * Real.sqrt X * Real.log X + (X : ℝ) ^ (1 - ε₁) * Real.log X) := by
  rcases Nat.eq_zero_or_pos X with hX0 | hXpos
  · subst hX0
    simp
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hXpos
  have hL : 0 ≤ Real.log X := Real.log_natCast_nonneg X
  set X₁ : ℝ := (X : ℝ) ^ (1 - ε₁) with hX₁
  have hX₁0 : 0 ≤ X₁ := Real.rpow_nonneg (Nat.cast_nonneg X) _
  -- pointwise split of the difference
  have hsplit : ∀ m ∈ Icc 1 X,
      ArithmeticFunction.vonMangoldt m - elazCoeff1762 X ε₁ m ≤
        (if ¬ m.Prime then ArithmeticFunction.vonMangoldt m else 0) +
          (if (m : ℝ) ≤ X₁ then Real.log X else 0) := by
    intro m hm
    have hmX : (m : ℝ) ≤ X := by exact_mod_cast (mem_Icc.mp hm).2
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast (mem_Icc.mp hm).1
    have hlogm : Real.log m ≤ Real.log X := Real.log_le_log (by linarith) hmX
    unfold elazCoeff1762
    by_cases hp : m.Prime
    · rw [ArithmeticFunction.vonMangoldt_apply_prime hp]
      by_cases hlt : X₁ < m
      · have hy : m.Prime ∧ (X : ℝ) ^ (1 - ε₁) < m := ⟨hp, hlt⟩
        rw [if_pos hy, if_neg (not_not.mpr hp)]
        split_ifs <;> linarith
      · have hle : (m : ℝ) ≤ X₁ := not_lt.mp hlt
        have hn : ¬ (m.Prime ∧ (X : ℝ) ^ (1 - ε₁) < m) := fun h => hlt h.2
        rw [if_neg hn, if_neg (not_not.mpr hp), if_pos hle]
        linarith
    · rw [if_neg (fun h => hp h.1), if_pos hp, sub_zero]
      have : 0 ≤ (if (m : ℝ) ≤ X₁ then Real.log X else 0) := by split_ifs <;> linarith
      linarith
  have hnp : ∑ m ∈ Icc 1 X, (if ¬ m.Prime then ArithmeticFunction.vonMangoldt m else 0) =
      Chebyshev.psi X - Chebyshev.theta X := by
    rw [Chebyshev.psi_sub_theta_eq_sum_not_prime, Nat.floor_natCast, sum_filter]
    rfl
  have hsmall : ∑ m ∈ Icc 1 X, (if (m : ℝ) ≤ X₁ then Real.log X else 0) ≤
      X₁ * Real.log X := by
    rw [← sum_filter, sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ hL
    have hsub : (Icc 1 X).filter (fun m : ℕ => (m : ℝ) ≤ X₁) ⊆ Icc 1 ⌊X₁⌋₊ := by
      intro m hm
      simp only [mem_filter, mem_Icc] at hm ⊢
      exact ⟨hm.1.1, Nat.le_floor hm.2⟩
    calc ((Icc 1 X).filter (fun m : ℕ => (m : ℝ) ≤ X₁)).card
        ≤ ((Icc 1 ⌊X₁⌋₊).card : ℝ) := by exact_mod_cast card_le_card hsub
      _ = (⌊X₁⌋₊ : ℝ) := by simp
      _ ≤ X₁ := Nat.floor_le hX₁0
  have hpt : Chebyshev.psi X - Chebyshev.theta X ≤ 2 * Real.sqrt X * Real.log X :=
    Chebyshev.psi_sub_theta_le hX1
  have hsumd : ∑ m ∈ Icc 1 X, (ArithmeticFunction.vonMangoldt m - elazCoeff1762 X ε₁ m) ≤
      2 * Real.sqrt X * Real.log X + X₁ * Real.log X := by
    calc _ ≤ ∑ m ∈ Icc 1 X, ((if ¬ m.Prime then ArithmeticFunction.vonMangoldt m else 0) +
          (if (m : ℝ) ≤ X₁ then Real.log X else 0)) := sum_le_sum hsplit
      _ = _ := sum_add_distrib
      _ ≤ _ := by rw [hnp]; linarith
  calc ∑ m ∈ Icc 1 X, (ArithmeticFunction.vonMangoldt m - elazCoeff1762 X ε₁ m) ^ 2
      ≤ ∑ m ∈ Icc 1 X, Real.log X *
          (ArithmeticFunction.vonMangoldt m - elazCoeff1762 X ε₁ m) := by
        apply sum_le_sum
        intro m hm
        have hmX : (m : ℝ) ≤ X := by exact_mod_cast (mem_Icc.mp hm).2
        have h0 := elazCoeff_nonneg1762 X ε₁ m
        have h1 := elazCoeff_le1762 X ε₁ m
        have hΛ : ArithmeticFunction.vonMangoldt m ≤ Real.log X :=
          ArithmeticFunction.vonMangoldt_le_log.trans
            (Real.log_le_log (by exact_mod_cast (mem_Icc.mp hm).1) hmX)
        nlinarith
    _ = Real.log X * ∑ m ∈ Icc 1 X,
          (ArithmeticFunction.vonMangoldt m - elazCoeff1762 X ε₁ m) := by rw [mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left hsumd hL

/-! ### Absorption into X e^(-cH) -/

theorem absorb1762 {ε₁ κ : ℝ} (hε₁ : 0 < ε₁) (hκ : 0 < κ) :
    ∃ a : ℝ, 3 ≤ a ∧ ∀ x : ℝ, a ≤ x → ∀ E1 E2 : ℝ,
      E1 ≤ 24 * x * Real.log x →
      E2 ≤ Real.log x * (2 * Real.sqrt x * Real.log x + x ^ (1 - ε₁) * Real.log x) →
      (x ^ (min ε₁ (1 / 2) / 2) * E2 + (x ^ (min ε₁ (1 / 2) / 2))⁻¹ * E1) / 2 ≤ κ * x := by
  set δ : ℝ := min ε₁ (1 / 2) / 2 with hδdef
  have hδ : 0 < δ := by
    have : 0 < min ε₁ (1 / 2) := lt_min hε₁ (by norm_num)
    linarith
  have hδ1 : 2 * δ ≤ 1 / 2 := by
    have := min_le_right ε₁ (1 / 2 : ℝ)
    linarith
  have hδ2 : 2 * δ ≤ ε₁ := by
    have := min_le_left ε₁ (1 / 2 : ℝ)
    linarith
  have hs : 0 < Real.sqrt (κ / 14) := Real.sqrt_pos.2 (by positivity)
  have hlo := (isLittleO_log_rpow_atTop (half_pos hδ)).bound hs
  obtain ⟨a, ha⟩ := Filter.eventually_atTop.mp (hlo.and (eventually_ge_atTop (3 : ℝ)))
  refine ⟨max a 3, le_max_right _ _, ?_⟩
  intro x hx E1 E2 hE1 hE2
  obtain ⟨hb, hx3⟩ := ha x (le_trans (le_max_left _ _) hx)
  have hx0 : 0 < x := by linarith
  have hx1 : 1 ≤ x := by linarith
  set L := Real.log x with hLdef
  have hL1 : 1 ≤ L := by
    rw [hLdef, Real.le_log_iff_exp_le hx0]
    have := Real.exp_one_lt_d9
    linarith
  set u : ℝ := x ^ δ with hudef
  have hu : 0 < u := Real.rpow_pos_of_pos hx0 δ
  have hhalf : (x ^ (δ / 2)) ^ 2 = u := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le, hudef]
    norm_num
  have hsq : L ^ 2 ≤ (κ / 14) * u := by
    have hb' : L ≤ Real.sqrt (κ / 14) * x ^ (δ / 2) := by
      have hpos : 0 ≤ x ^ (δ / 2) := Real.rpow_nonneg hx0.le _
      simpa [Real.norm_eq_abs, abs_of_nonneg (by linarith : (0 : ℝ) ≤ L),
        abs_of_nonneg hpos] using hb
    have h0 : 0 ≤ L := by linarith
    calc L ^ 2 ≤ (Real.sqrt (κ / 14) * x ^ (δ / 2)) ^ 2 := pow_le_pow_left₀ h0 hb' 2
      _ = (κ / 14) * u := by
        rw [mul_pow, Real.sq_sqrt (by positivity), hhalf]
  have hu2 : u ^ 2 = x ^ (2 * δ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx0.le]
    norm_num
    ring_nf
  have hA1 : u ^ 2 * Real.sqrt x ≤ x := by
    rw [hu2, Real.sqrt_eq_rpow, ← Real.rpow_add hx0]
    calc x ^ (2 * δ + 1 / 2) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one x
  have hA2 : u ^ 2 * x ^ (1 - ε₁) ≤ x := by
    rw [hu2, ← Real.rpow_add hx0]
    calc x ^ (2 * δ + (1 - ε₁)) ≤ x ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hx1 (by linarith)
      _ = x := Real.rpow_one x
  have hw : L ^ 2 / u ≤ κ / 14 := (div_le_iff₀ hu).2 (by linarith)
  have hw0 : 0 ≤ L ^ 2 / u := by positivity
  have hA : u * E2 ≤ 3 * x * (L ^ 2 / u) := by
    have h1 : u * E2 ≤ u * (L * (2 * Real.sqrt x * L + x ^ (1 - ε₁) * L)) :=
      mul_le_mul_of_nonneg_left hE2 hu.le
    have h2 : u * (L * (2 * Real.sqrt x * L + x ^ (1 - ε₁) * L)) =
        (L ^ 2 / u) * (2 * (u ^ 2 * Real.sqrt x) + u ^ 2 * x ^ (1 - ε₁)) := by
      field_simp
    have h3 : 2 * (u ^ 2 * Real.sqrt x) + u ^ 2 * x ^ (1 - ε₁) ≤ 3 * x := by linarith
    calc u * E2 ≤ _ := h1
      _ = _ := h2
      _ ≤ (L ^ 2 / u) * (3 * x) := mul_le_mul_of_nonneg_left h3 hw0
      _ = _ := by ring
  have hB : u⁻¹ * E1 ≤ 24 * x * (L ^ 2 / u) := by
    have h1 : u⁻¹ * E1 ≤ u⁻¹ * (24 * x * L) :=
      mul_le_mul_of_nonneg_left hE1 (inv_nonneg.2 hu.le)
    have h2 : u⁻¹ * (24 * x * L) ≤ u⁻¹ * (24 * x * L ^ 2) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.2 hu.le)
      have : L ≤ L ^ 2 := by nlinarith
      nlinarith
    calc u⁻¹ * E1 ≤ _ := h1.trans h2
      _ = _ := by rw [div_eq_mul_inv]; ring
  have hxw : x * (L ^ 2 / u) ≤ x * (κ / 14) := mul_le_mul_of_nonneg_left hw hx0.le
  nlinarith

/-! ### Assembly -/

/-- For X large, the admissible P leaves room for the arcs: P + 2 <= X / P. -/
theorem admissible_arc_room1762 {X : ℕ} {P : ℝ} (hP : AdmissibleP131 X P)
    (hX3 : (3 : ℝ) ≤ X) (h18 : (3 : ℝ) ≤ (X : ℝ) ^ ((18 : ℝ) / 100)) :
    0 < P ∧ P + 2 ≤ arcQ131 X P := by
  have hX0 : (0 : ℝ) < X := by linarith
  have hX1 : (1 : ℝ) ≤ X := by linarith
  have hP1 : 1 ≤ P := le_trans (Real.one_le_rpow hX1 (by norm_num)) hP.1
  have hP0 : 0 < P := by linarith
  refine ⟨hP0, ?_⟩
  unfold arcQ131
  rw [le_div_iff₀ hP0]
  have hsplit : (X : ℝ) = (X : ℝ) ^ ((18 : ℝ) / 100) * (X : ℝ) ^ ((41 : ℝ) / 100) *
      (X : ℝ) ^ ((41 : ℝ) / 100) := by
    rw [← Real.rpow_add hX0, ← Real.rpow_add hX0]
    norm_num
  have hP2 : P * P ≤ (X : ℝ) ^ ((41 : ℝ) / 100) * (X : ℝ) ^ ((41 : ℝ) / 100) :=
    mul_le_mul hP.2 hP.2 hP0.le (Real.rpow_nonneg hX0.le _)
  have hpos : 0 ≤ (X : ℝ) ^ ((41 : ℝ) / 100) * (X : ℝ) ^ ((41 : ℝ) / 100) := by positivity
  nlinarith

/-- ELAZ Theorem 10 as printed gives Lemma 4.1 of P0045 on the window [X/2, X]. -/
theorem lemma41_window_of_elaz1762 (hE : ElazTheorem10Statement1762) :
    Lemma41OnWindow1762 evenWindow131 := by
  obtain ⟨c, ε₀, B, H₀, T₀, hc, hε₀, hB, Cε, hCε, h⟩ := hE
  refine ⟨c, ε₀, B + 1, H₀, T₀, hc, hε₀, by linarith, Cε, hCε, fun H T hH hT => ?_⟩
  obtain ⟨ε₁, hε₁, X₀, hX⟩ := h H T hH hT
  obtain ⟨a, ha3, habs⟩ := absorb1762 hε₁ (Real.exp_pos (-c * H))
  obtain ⟨b, hb⟩ := Filter.eventually_atTop.mp
    ((tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 18 / 100)).eventually_ge_atTop 3)
  refine ⟨max X₀ (max ⌈a⌉₊ ⌈b⌉₊), fun X hXge => ?_⟩
  have hXX₀ : X₀ ≤ X := le_trans (le_max_left _ _) hXge
  have hXa : a ≤ X := (Nat.ceil_le.mp (le_trans (le_trans (le_max_left _ _)
    (le_max_right _ _)) hXge))
  have hXb : b ≤ X := (Nat.ceil_le.mp (le_trans (le_trans (le_max_right _ _)
    (le_max_right _ _)) hXge))
  have hX3 : (3 : ℝ) ≤ X := le_trans ha3 hXa
  have hXpos : 0 < X := by exact_mod_cast (show (0 : ℝ) < X by linarith)
  obtain ⟨P, hP, K, z, Sg, cnd, h0, h1, hbox, hmult, hpole, hbd, hsmall, hrem⟩ := hX X hXX₀
  obtain ⟨hP0, hQ⟩ := admissible_arc_room1762 hP hX3 (hb _ hXb)
  refine ⟨P, hP, K, z, Sg, h0, h1, hbox, hmult, hpole, hbd, ?_, ?_⟩
  · intro ε hε hε' i j n hn hnd
    apply hsmall ε hε hε' i j n hn
    rintro ⟨hi, hj, _⟩
    rcases hnd with hnd | hnd
    · exact hnd hi
    · exact hnd hj
  · intro n hn
    set δ : ℝ := min ε₁ (1 / 2) / 2 with hδ
    have ht : 0 < (X : ℝ) ^ δ := Real.rpow_pos_of_pos (by linarith) δ
    have htr := elaz_major_transfer1762 (ε₁ := ε₁) hXpos hP0 hQ ht n
    have hsmallI := habs X hXa _ _ (sum_energy1762 X ε₁) (diff_energy1762 X ε₁)
    set IΛ : ℂ := ∫ α in majorArcs131 X P, primeSum131 X α ^ 2 * powerSum131 X α ^ 0 *
      phase131 (-(n : ℝ) * α) with hIΛ
    set Sz : ℂ := ∑ i, ∑ j, Sg i j n * zeroSign481 i * zeroSign481 j *
      gammaPair481 (z i).2.2 (z j).2.2 n with hSz
    have hSum : (∑ i, ∑ j, Sg i j n * elazSign1762 i * elazSign1762 j *
        gammaPair481 (z i).2.2 (z j).2.2 n) = Sz := by
      rw [hSz]
      apply sum_congr rfl
      intro i _
      apply sum_congr rfl
      intro j _
      rw [mul_assoc (Sg i j n), elazSign_mul1762, ← mul_assoc]
    have hr := hrem n hn
    rw [hSum] at hr
    have hbin : binaryMajor131 X n P = IΛ.re := rfl
    rw [hbin, ← Complex.sub_re]
    have hT : 0 ≤ (X : ℝ) / Real.sqrt T := by positivity
    have hE0 : 0 ≤ (X : ℝ) * Real.exp (-c * H) := by positivity
    calc |(IΛ - Sz).re| ≤ ‖IΛ - Sz‖ := Complex.abs_re_le_norm _
      _ = ‖(IΛ - elazMajor1762 X n P ε₁) + (elazMajor1762 X n P ε₁ - Sz)‖ := by ring_nf
      _ ≤ ‖IΛ - elazMajor1762 X n P ε₁‖ + ‖elazMajor1762 X n P ε₁ - Sz‖ := norm_add_le _ _
      _ ≤ Real.exp (-c * H) * X + B * ((X : ℝ) * Real.exp (-c * H) + X / Real.sqrt T) :=
          add_le_add (htr.trans hsmallI) hr
      _ ≤ (B + 1) * ((X : ℝ) * Real.exp (-c * H) + X / Real.sqrt T) := by nlinarith

/-- ELAZ Theorem 10 as printed gives `Lemma41Statement481`, the cited leaf
`pintz_explicit_formula481`, with no further input. -/
theorem lemma41Statement_of_elaz1762 (hE : ElazTheorem10Statement1762) :
    Lemma41Statement481 :=
  (lemma41OnWindow_evenJ1762).1
    (lemma41OnWindow_mono1762 evenJ_subset_window1762 (lemma41_window_of_elaz1762 hE))

/-- The LPZ2007 four input route with the explicit formula input taken from the printed
ELAZ Theorem 10. CONDITIONAL ON `ElazTheorem10Statement1762`, `JutilaStatement481`,
`RealZeroStatement481` and `IwaniecStatement481`. -/
theorem repaired_mainJ131_of_elaz1762 (hE : ElazTheorem10Statement1762)
    (hjut : JutilaStatement481) (hzero : RealZeroStatement481) (hiw : IwaniecStatement481) :
    RepairedMainJ131 :=
  repaired_mainJ131_of_four_inputs1121 (lemma41Statement_of_elaz1762 hE) hjut hzero hiw

/-! ### Corollary 4.2 on the window [X/2, X] -/

theorem evenWindow_facts1762 (X n : ℕ) (hn : n ∈ evenWindow131 X) :
    1 ≤ n ∧ (X : ℝ) ≤ 2 * n ∧ Even n := by
  simp only [evenWindow131, mem_filter, mem_Icc] at hn
  refine ⟨hn.1.1, ?_, hn.2.1⟩
  linarith [hn.2.2]

/-- P0045 journal page 775, Corollary 4.2 on the window [X/2, X] that displays 11 and 12 use.
The window is the printed range of m in Pintz ELAZ Theorem 10. CONDITIONAL ON
`ElazTheorem10Statement1762`, `JutilaStatement481`, `RealZeroStatement481` and
`IwaniecStatement481`. -/
theorem cor42_window_of_elaz1762 (hE : ElazTheorem10Statement1762)
    (hjut : JutilaStatement481) (hzero : RealZeroStatement481) (hiw : IwaniecStatement481) :
    Cor42OnWindow131 evenWindow131 := by
  intro η hη
  obtain ⟨K₁, Cstar, A, H, T, hC, hA, hH, hT, Xf, hf⟩ :=
    explicit_formula_reduction_window1762 evenWindow131 evenWindow_facts1762
      (lemma41_window_of_elaz1762 hE) hjut indexed_zero_count481 gamma_pair_bound481 η hη
  obtain ⟨c, hc, Xr, hr⟩ := exceptional_radical481 davenport_classification481
    hzero hiw H T hH hT
  refine ⟨K₁, Cstar, c, A, hC, hc, hA, max Xf Xr, ?_⟩
  intro X hX
  obtain ⟨P, E, hP, hcard, hsource, hgood, hall⟩ :=
    hf X ((le_max_left _ _).trans hX)
  refine ⟨P, E, hP, ⟨hcard, ?_⟩, hgood, hall⟩
  intro r hmem
  obtain ⟨z, hz, hzr⟩ := hsource r hmem
  simpa only [hzr] using hr X ((le_max_right _ _).trans hX) P hP z hz

/-- The leaf statement `Cor42Statement131` of `major_arcs_j1_131`, from the same four inputs. -/
theorem cor42Statement_of_elaz1762 (hE : ElazTheorem10Statement1762)
    (hjut : JutilaStatement481) (hzero : RealZeroStatement481) (hiw : IwaniecStatement481) :
    Cor42Statement131 :=
  cor42_window_of_elaz1762 hE hjut hzero hiw

end

end LeanLab.LPZ2007

#print axioms LeanLab.LPZ2007.lemma41_window_of_elaz1762
#print axioms LeanLab.LPZ2007.lemma41Statement_of_elaz1762
#print axioms LeanLab.LPZ2007.repaired_mainJ131_of_elaz1762
#print axioms LeanLab.LPZ2007.cor42_window_of_elaz1762
#print axioms LeanLab.LPZ2007.cor42Statement_of_elaz1762
