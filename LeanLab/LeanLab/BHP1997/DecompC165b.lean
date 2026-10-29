/-
P0069, Sections 2 to 5. CODEX task165.
The paper hypotheses and weight constructions are separate OPEN leaves.
The exact sieve_data assembly is CONDITIONAL on those leaves.
AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.DecompC165a
import LeanLab.BHP1997.DecompC165c
import LeanLab.BHP1997.DecompC165d
import LeanLab.BHP1997.Decomp132
import LeanLab.BHP1997.Thm2Sing
import LeanLab.BHP1997.Characters132

namespace LeanLab.BHP1997.DecompC165b
open Classical Complex Decomp132

/-- Page 2, the positive scale Y times the singular series divided by
log x times log Y. Positivity is proved separately for x greater than 1. -/
noncomputable def correlationScale (ε x : ℝ) (N : ℕ) : ℝ :=
  x ^ (11 / 20 + ε) / (Real.log x * Real.log (x ^ (11 / 20 + ε))) * Thm2.sing (N / 2)

/-- Page 3, the exceptional set in 1.6 for one pair of real weights. -/
noncomputable def badSet (ε u v K : ℝ) (a b : ℝ → ℕ → ℝ) (x : ℝ) : Finset ℕ :=
  (Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊).filter
    (fun N => Even N ∧ K * |u * v| * correlationScale ε x N / Real.log x <
      |convolution (leftInterval ε x) (rightInterval ε x) (a x) (b x) N -
        u * v * correlationScale ε x N|)

/-- Page 3, Theorem 2 applied to one pair of real weights satisfying
conditions i to iv. CONDITIONAL on Theorem 2 at epsilon and B. -/
theorem pair_correlation {ε B u v : ℝ} {a b : ℝ → ℕ → ℝ}
    (h2 : Thm2.Theorem2 ε B) (ha : LeftConditions ε B u a)
    (hb : RightConditions ε B v b) :
    ∀ A : ℝ, 0 < A → ∃ K C : ℝ, ∀ x : ℝ, C ≤ x →
      ((badSet ε u v K a b x).card : ℝ) <
        x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) / Real.log x ^ A := by
  obtain ⟨hai, ⟨Ca, hCa⟩, harough⟩ := ha
  obtain ⟨⟨Cb, hCb⟩, hbiii, E, hbiv⟩ := hb
  have hdiv : ∃ C : ℝ, ∀ x k,
      ‖(a x k : ℂ)‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B ∧
      ‖(b x k : ℂ)‖ ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B := by
    refine ⟨max Ca Cb, ?_⟩
    intro x k
    have hpow : 0 ≤ ((k.divisors.card : ℕ) : ℝ) ^ B := Real.rpow_nonneg (by positivity) _
    constructor
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (hCa x k).trans (mul_le_mul_of_nonneg_right (le_max_left Ca Cb) hpow)
    · simpa only [Complex.norm_real, Real.norm_eq_abs] using
        (hCb x k).trans (mul_le_mul_of_nonneg_right (le_max_right Ca Cb) hpow)
  have hrough : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ k : ℕ,
      Nat.gcd k (Thm2.primorialBelow (Real.log x ^ A)) ≠ 1 → (a x k : ℂ) = 0 := by
    intro A hA
    obtain ⟨C, hC⟩ := harough A hA
    exact ⟨C, fun x hx k hk => by simp [hC x hx k hk]⟩
  have hout := h2 (fun x k => (a x k : ℂ)) (fun x k => (b x k : ℂ)) u v E
    hai hdiv hrough hbiii (by simpa only [sieveQ, rightInterval] using hbiv)
  intro A hA
  obtain ⟨K, C, hC⟩ := hout A hA
  refine ⟨K, C, fun x hx => ?_⟩
  have hc := hC x hx
  convert hc using 1
  congr 2
  apply Finset.filter_congr
  intro N hN
  have hconv : (∑ k ∈ leftInterval ε x, ∑ m ∈ rightInterval ε x,
      if k + m = N then (a x k : ℂ) * (b x m : ℂ) else 0) =
      (convolution (leftInterval ε x) (rightInterval ε x) (a x) (b x) N : ℂ) := by
    simp only [convolution, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro k hk
    apply Finset.sum_congr rfl
    intro m hm
    split_ifs <;> simp
  simp only [correlationScale, leftInterval, rightInterval] at *
  rw [hconv]
  simp only [← Complex.ofReal_mul, ← Complex.ofReal_div, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  ring_nf

/-- LEAF. Section 2, pages 5 to 11, proof of Theorem 2 from conditions
 i to iv on page 3 and the circle estimates 2.1 onward. OPEN. -/
theorem section2_circle_method : Thm2.Theorem2Paper := by
  sorry

/-- LEAF. Section 3, pages 11 to 21, Theorem 4 and its mean value lemmas.
Reuse the proved exponent lemmas. The finer analytic leaves are in DecompC165c. CONDITIONAL. -/
theorem section3_mean_values : Thm4.Theorem4Paper := by
  exact DecompC165c.section3_mean_values

/-- LEAF. Section 4, pages 24 to 41, the lower weight a0.
The discarded region integrals on page 41 give u0 greater than 0.9953.
Use the Section 3 mean values for condition i and the sifted construction
for condition ii. The lower weight has density at most 1. OPEN. -/
theorem section4_lower (h4 : Thm4.Theorem4Paper) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (u0 : ℝ) (a0 : ℝ → ℕ → ℝ),
        0.9953 < u0 ∧ u0 ≤ 1 ∧ LeftConditions ε B u0 a0 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ k ∈ leftInterval ε x, a0 x k ≤ primeWeight k := by
  sorry

/-- LEAF. Section 4, pages 41 and 42, Lemma 28 and the upper weight a1.
The five and seven dimensional discarded integrals give u1 below 1.0001.
The upper density is at least 1. The bound is on page 42. OPEN. -/
theorem section4_upper (h4 : Thm4.Theorem4Paper) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (u1 : ℝ) (a1 : ℝ → ℕ → ℝ),
        1 ≤ u1 ∧ u1 < 1.0001 ∧ LeftConditions ε B u1 a1 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ k ∈ leftInterval ε x, primeWeight k ≤ a1 x k := by
  sorry

/-- LEAF. Section 5, pages 43 to 53, Lemmas 29 to 35 and the two short
weights. Condition iv is 5.1 to 5.3 followed by Lemma 29. The final
Buchstab integrals yield v0 greater than 0.05 and v1 below 2.2.
The page 22 Lemma 9 and Section 3 mean values are explicit inputs.
The finer construction leaves are in DecompC165d. CONDITIONAL. -/
theorem section5_weights (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9) :
    ∃ B0 η : ℝ, 0 < η ∧ ∀ B ε : ℝ, B0 ≤ B → 0 < ε → ε < η →
      ∃ (v0 v1 : ℝ) (b0 b1 : ℝ → ℕ → ℝ),
        0.05 < v0 ∧ v0 ≤ v1 ∧ v1 < 2.2 ∧
        RightConditions ε B v0 b0 ∧ RightConditions ε B v1 b1 ∧
        ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
          ∀ m ∈ rightInterval ε x,
            b0 x m ≤ primeWeight m ∧ primeWeight m ≤ b1 x m := by
  exact DecompC165d.section5_weights h4 h9

/-- LEAF. Pages 2 to 4, applying Theorem 2 three times gives the
correlations before 1.5 outside the union of three exceptional sets.
Spend one extra log power on their cardinalities. Positivity of sing,
proved in Thm2Sing, gives r. The fixed positive margin absorbs the
relative errors for large x. This is the remaining elementary transfer.
PROVED as an implication from Theorem 2 and the four weight conditions. -/
theorem correlation_transfer
    {ε B u0 u1 v0 v1 : ℝ} {a0 a1 b0 b1 : ℝ → ℕ → ℝ}
    (h2 : Thm2.Theorem2 ε B)
    (hε : 0 < ε) (hε1 : ε < 8.8 / 10 ^ 5)
    (hu0 : 0.99 < u0) (hu : u0 ≤ u1) (hu1 : u1 < 1.01)
    (hv0 : 0.05 < v0) (hv : v0 ≤ v1) (hv1 : v1 < 2.2)
    (ha0 : LeftConditions ε B u0 a0) (ha1 : LeftConditions ε B u1 a1)
    (hb0 : RightConditions ε B v0 b0) (hb1 : RightConditions ε B v1 b1)
    (hsand : ∃ X : ℝ, ∀ x : ℝ, X ≤ x →
      (∀ k ∈ leftInterval ε x, a0 x k ≤ primeWeight k ∧ primeWeight k ≤ a1 x k) ∧
      (∀ m ∈ rightInterval ε x, b0 x m ≤ primeWeight m ∧ primeWeight m ≤ b1 x m)) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
        ∃ (I J : Finset ℕ) (a0 a1 b0 b1 : ℕ → ℝ) (E : Finset ℕ),
          (∀ k ∈ I, a0 k ≤ primeWeight k ∧ primeWeight k ≤ a1 k) ∧
          (∀ m ∈ J, b0 m ≤ primeWeight m ∧ primeWeight m ≤ b1 m) ∧
          (E.card : ℝ) < x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) /
            Real.log x ^ A ∧
          ∀ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊,
            Even N → N ∉ E → ∃ r : ℝ, 0 < r ∧
              |convolution I J a0 b1 N - u0 * v1 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 ∧
              |convolution I J a1 b0 N - u1 * v0 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 ∧
              |convolution I J a1 b1 N - u1 * v1 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 := by
  intro A hA
  obtain ⟨K01, C01, h01⟩ := pair_correlation h2 ha0 hb1 (A + 1) (by linarith)
  obtain ⟨K10, C10, h10⟩ := pair_correlation h2 ha1 hb0 (A + 1) (by linarith)
  obtain ⟨K11, C11, h11⟩ := pair_correlation h2 ha1 hb1 (A + 1) (by linarith)
  obtain ⟨Xs, hs⟩ := hsand
  let m := u0 * v1 + u1 * v0 - u1 * v1
  have hm : 0 < m := constants15 hu0 hu hu1 hv0 hv hv1
  let D := max 1 (max (max (K01 * |u0 * v1|) (K10 * |u1 * v0|)) (K11 * |u1 * v1|))
  have hD : 0 < D := lt_of_lt_of_le (by norm_num) (le_max_left _ _)
  have hD01 : K01 * |u0 * v1| ≤ D :=
    le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)
  have hD10 : K10 * |u1 * v0| ≤ D :=
    le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)
  have hD11 : K11 * |u1 * v1| ≤ D := le_trans (le_max_right _ _) (le_max_right _ _)
  let R := 4 + 6 * D / m
  let X := max (max Xs C01) (max (max C10 C11) (Real.exp (R + 1)))
  refine ⟨X, fun x hx => ?_⟩
  have hxS : Xs ≤ x := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hx
  have hx01 : C01 ≤ x := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hx
  have hx10 : C10 ≤ x :=
    le_trans (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have hx11 : C11 ≤ x :=
    le_trans (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) (le_max_right _ _)) hx
  have hxexp : Real.exp (R + 1) ≤ x :=
    le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx
  have hR : 4 < R := by
    have hp : 0 < 6 * D / m := by positivity
    dsimp [R]
    linarith
  have hx1 : 1 < x := lt_of_lt_of_le
    (Real.one_lt_exp_iff.mpr (by linarith)) hxexp
  have hx0 : 0 < x := by linarith
  have hlogR : R + 1 ≤ Real.log x := by
    simpa using Real.log_le_log (Real.exp_pos _) hxexp
  have hlog : 0 < Real.log x := Real.log_pos hx1
  have hlog3 : 3 < Real.log x := by linarith
  have hDlog : 6 * D ≤ m * Real.log x := by
    have ht : 6 * D / m ≤ Real.log x := by dsimp [R] at hlogR; linarith
    have hh := (div_le_iff₀ hm).mp ht
    nlinarith
  let E01 := badSet ε u0 v1 K01 a0 b1 x
  let E10 := badSet ε u1 v0 K10 a1 b0 x
  let E11 := badSet ε u1 v1 K11 a1 b1 x
  let E := (E01 ∪ E10) ∪ E11
  refine ⟨leftInterval ε x, rightInterval ε x, a0 x, a1 x, b0 x, b1 x, E,
    (hs x hxS).1, (hs x hxS).2, ?_, ?_⟩
  · have hcard : E.card ≤ E01.card + E10.card + E11.card :=
      (Finset.card_union_le _ _).trans
        (Nat.add_le_add_right (Finset.card_union_le _ _) _)
    have hcast : (E.card : ℝ) ≤ (E01.card : ℝ) + (E10.card : ℝ) + (E11.card : ℝ) := by
      exact_mod_cast hcard
    have hc01 := h01 x hx01
    have hc10 := h10 x hx10
    have hc11 := h11 x hx11
    have hsmall : (E.card : ℝ) <
        3 * (x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) / Real.log x ^ (A + 1)) := by
      dsimp only [E01, E10, E11] at hcast
      linarith
    apply lt_trans hsmall
    rw [← mul_div_assoc, Real.rpow_add hlog, Real.rpow_one,
      div_lt_div_iff₀ (by positivity) (by positivity)]
    have hp : 0 < x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) * Real.log x ^ A := by
      positivity
    nlinarith [mul_lt_mul_of_pos_left hlog3 hp]
  · intro N hN hEven hNE
    let r := correlationScale ε x N
    have hr : 0 < r := by
      dsimp [r, correlationScale]
      have hlogY : 0 < Real.log (x ^ (11 / 20 + ε)) := by
        rw [Real.log_rpow hx0]
        positivity
      exact mul_pos (div_pos (Real.rpow_pos_of_pos hx0 _) (mul_pos hlog hlogY)) (Thm2.sing_pos _)
    refine ⟨r, hr, ?_, ?_, ?_⟩
    all_goals
      have hnot01 : N ∉ E01 := by
        intro hn
        apply hNE
        exact Finset.mem_union_left _ (Finset.mem_union_left _ hn)
      have hnot10 : N ∉ E10 := by
        intro hn
        apply hNE
        exact Finset.mem_union_left _ (Finset.mem_union_right _ hn)
      have hnot11 : N ∉ E11 := by
        intro hn
        apply hNE
        exact Finset.mem_union_right _ hn
      have hbound (u v K : ℝ) (a b : ℝ → ℕ → ℝ)
          (hn : N ∉ badSet ε u v K a b x) (hK : K * |u * v| ≤ D) :
          |convolution (leftInterval ε x) (rightInterval ε x) (a x) (b x) N - u * v * r| ≤ m * r / 6 := by
        have he : |convolution (leftInterval ε x) (rightInterval ε x) (a x) (b x) N - u * v * r| ≤
            K * |u * v| * r / Real.log x := by
          apply le_of_not_gt
          intro hbad
          exact hn (Finset.mem_filter.mpr ⟨hN, hEven, hbad⟩)
        apply he.trans
        apply (div_le_iff₀ hlog).mpr
        have h1 := mul_le_mul_of_nonneg_right hK hr.le
        have h2 := mul_le_mul_of_nonneg_right hDlog hr.le
        nlinarith
    · exact hbound u0 v1 K01 a0 b1 hnot01 hD01
    · exact hbound u1 v0 K10 a1 b0 hnot10 hD10
    · exact hbound u1 v1 K11 a1 b1 hnot11 hD11

/-- Pages 1 to 4 and Sections 2 to 5. The exact existing sieve_data
statement follows from three local OPEN leaves, the Sections 3 and 5 decompositions
and the proved correlation transfer.
No direct sorry.
CONDITIONAL on all named analytic inputs. -/
theorem sieve_data :
    ∃ ε u0 u1 v0 v1 : ℝ, 0 < ε ∧ ε < 8.8 / 10 ^ 5 ∧
      0.99 < u0 ∧ u0 ≤ u1 ∧ u1 < 1.01 ∧ 0.05 < v0 ∧ v0 ≤ v1 ∧ v1 < 2.2 ∧
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x →
        ∃ (I J : Finset ℕ) (a0 a1 b0 b1 : ℕ → ℝ) (E : Finset ℕ),
          (∀ k ∈ I, a0 k ≤ primeWeight k ∧ primeWeight k ≤ a1 k) ∧
          (∀ m ∈ J, b0 m ≤ primeWeight m ∧ primeWeight m ≤ b1 m) ∧
          (E.card : ℝ) < x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5))) /
            Real.log x ^ A ∧
          ∀ N ∈ Finset.Icc ⌈x⌉₊ ⌊x + x ^ ((11 / 20 + ε) * (2 * (1 / 16 - 1 / 10 ^ 5)))⌋₊,
            Even N → N ∉ E → ∃ r : ℝ, 0 < r ∧
              |convolution I J a0 b1 N - u0 * v1 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 ∧
              |convolution I J a1 b0 N - u1 * v0 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 ∧
              |convolution I J a1 b1 N - u1 * v1 * r| ≤
                (u0 * v1 + u1 * v0 - u1 * v1) * r / 6 := by
  have h4 := section3_mean_values
  obtain ⟨Bl, ηl, hηl, hl⟩ := section4_lower h4
  obtain ⟨Bu, ηu, hηu, hu⟩ := section4_upper h4
  obtain ⟨Br, ηr, hηr, hr⟩ := section5_weights h4 DecompC165a.lemma9
  obtain ⟨η2, hη2, h2⟩ := section2_circle_method (max Bl (max Bu Br))
  let η := min η2 (min ηl (min ηu (min ηr (8.8 / 10 ^ 5))))
  have hη : 0 < η := by dsimp [η]; positivity
  let ε := η / 2
  have hε : 0 < ε := by dsimp [ε]; positivity
  have hεη : ε < η := by dsimp [ε]; linarith
  have hε2 : ε < η2 := lt_of_lt_of_le hεη (min_le_left _ _)
  have hεl : ε < ηl := lt_of_lt_of_le hεη
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hεu : ε < ηu := lt_of_lt_of_le hεη
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hεr : ε < ηr := lt_of_lt_of_le hεη
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hε1 : ε < 8.8 / 10 ^ 5 := lt_of_lt_of_le hεη
    (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_right _ _))))
  let B := max Bl (max Bu Br)
  obtain ⟨u0, a0, hu0, hu01, ha0, X0, hs0⟩ := hl B ε (le_max_left _ _) hε hεl
  obtain ⟨u1, a1, hu11, hu1, ha1, X1, hs1⟩ := hu B ε
    (le_trans (le_max_left _ _) (le_max_right _ _)) hε hεu
  obtain ⟨v0, v1, b0, b1, hv0, hv, hv1, hb0, hb1, Xb, hsb⟩ := hr B ε
    (le_trans (le_max_right _ _) (le_max_right _ _)) hε hεr
  have hu0' : 0.99 < u0 := by linarith
  have hu' : u0 ≤ u1 := le_trans hu01 hu11
  have hu1' : u1 < 1.01 := by linarith
  refine ⟨ε, u0, u1, v0, v1, hε, hε1, hu0', hu', hu1', hv0, hv, hv1, ?_⟩
  exact correlation_transfer (h2 ε hε hε2) hε hε1 hu0' hu' hu1' hv0 hv hv1
    ha0 ha1 hb0 hb1 ⟨max X0 (max X1 Xb), fun x hx =>
      ⟨fun k hk => ⟨hs0 x (le_trans (le_max_left _ _) hx) k hk,
        hs1 x (le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hx) k hk⟩,
       hsb x (le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hx)⟩⟩

end LeanLab.BHP1997.DecompC165b
