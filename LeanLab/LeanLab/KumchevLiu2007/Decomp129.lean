/-
Theorem 1 of Kumchev and Liu, arXiv 0801.0130, page 2.
Decomposition of the end of Section 4, page 16, eq. 55 and Proposition 2.
The analytic leaves remain CITED. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp1534a
import LeanLab.KumchevLiu2007.Decomp1534c
import LeanLab.KumchevLiu2007.Decomp129a
import LeanLab.KumchevLiu2007.Decomp129s

namespace LeanLab.KumchevLiu2007.Task129

open Real Complex LeanLab.KumchevLiu2007
open scoped BigOperators Topology
attribute [local instance] Classical.propDecidable

/-- The parameter Y of page 2 before eq. 4. -/
noncomputable def windowY (X ε : ℝ) : ℝ := X ^ (7 / 12 + ε / 2)

/-- Integer solutions in the half open windows of page 2 eqs. 4 to 6.
For large X in the nonempty H range of Theorem 1, Y is less than X. -/
noncomputable def windowPairs (X Y : ℝ) (n : ℕ) : Finset (ℕ × ℕ) :=
  ((Finset.range (⌊X⌋₊ + 1)).product (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
    (fun v => X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
      Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧ (v.2 : ℝ) < Real.sqrt Y ∧ v.1 + v.2 ^ 2 = n)

/-- The representation count R2 of page 2 eq. 4. -/
noncomputable def primeCount (X Y : ℝ) (n : ℕ) : ℕ :=
  ((windowPairs X Y n).filter (fun v => v.1.Prime ∧ v.2.Prime)).card

/-- The logarithmically weighted integer count r2 of page 2 eq. 6. -/
noncomputable def integerMain (X Y : ℝ) (n : ℕ) : ℝ :=
  ∑ v ∈ windowPairs X Y n, 1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ))

/-- The truncated singular series of page 2 eq. 7, using the existing A2. -/
noncomputable def series2 (n : ℕ) (P : ℝ) : ℂ :=
  ∑ q ∈ Finset.Icc 1 ⌊P⌋₊, U1534.A2 n q

/-- The main term r2 times the truncated singular series in page 2 eq. 9. -/
noncomputable def main2 (X Y P : ℝ) (n : ℕ) : ℂ := integerMain X Y n * series2 n P

/-- The sifted count R of page 8 eqs. 12 and 34. -/
noncomputable def roughCount (X Y P : ℝ) (n : ℕ) : ℕ :=
  ((windowPairs X Y n).filter (fun v => v.1.Prime ∧
    ∀ p : ℕ, p.Prime → p ∣ v.2 → Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p : ℝ))).card

/-- The residual R0 in page 8 eq. 35, defined as the difference of counts.
This definition does not assert its prime factorization description. -/
noncomputable def residualCount (X Y P : ℝ) (n : ℕ) : ℝ :=
  (roughCount X Y P n : ℝ) - (primeCount X Y n : ℝ)

/-- CITED. Theorem 1, page 2 eq. 9. The exponent B depends only on A.
C bounds the exceptional set and K bounds the relative error. -/
def kumchev_liu_thm1 : Prop :=
  ∀ A : ℝ, 0 < A → ∃ B : ℝ, 0 < B ∧
    ∀ δ ε : ℝ, 0 < δ → 0 < ε → ∃ C K X0 : ℝ, 0 < C ∧ 0 < K ∧ 2 ≤ X0 ∧
      ∀ X H : ℝ, X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          K * ‖main2 X (windowY X ε) (Real.log X ^ B) n‖ * Real.log X ^ (-1 + δ) <
          ‖(primeCount X (windowY X ε) n : ℂ) -
            main2 X (windowY X ε) (Real.log X ^ B) n‖) X H : ℝ) ≤
          C * H / Real.log X ^ A

/-- LEAF. Page 16 eq. 55 from eqs. 48, 49, 53 and 54.
This includes extension to H at most X by subdivision, which is not written out
in the paper. It requires the short interval Siegel Walfisz input on page 15,
Lemma 3.4 and the singular series estimates. The external sources include Liu
and Zhan 1997 Lemma 5.1 and Mikawa and Peneva 2007 Lemma 2, as cited on
page 15. It remains CITED. -/
theorem circle_input (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ ε : ℝ, 0 < ε →
      ∃ C K X0 : ℝ, 0 < C ∧ 0 < K ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          K * ‖main2 X (windowY X ε) (Real.log X ^ B) n‖ *
            (Real.log X ^ (-1 : ℝ) * Real.log (Real.log X)) <
          ‖(roughCount X (windowY X ε) (Real.log X ^ B) n : ℂ) -
            main2 X (windowY X ε) (Real.log X ^ B) n‖) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  sorry

/-- The sieve level z = exp of L to the 1 minus delta/2, chosen on page 17
before display 58 when Lemma 3.7 is applied with D = Y to the 1/9. -/
noncomputable def sieveLevel (X δ : ℝ) : ℝ := Real.exp (Real.log X ^ (1 - δ / 2))

/-- The partial singular product P2(n, z) of page 13 display 45 for j = 2.
Higher prime powers vanish because A2 contains the Moebius function.
This duplicates Task129b.product2, which cannot be imported here. -/
noncomputable def partialProduct2 (n : ℕ) (Q : ℝ) : ℂ :=
  ∏ p ∈ (Finset.range (⌊Q⌋₊ + 1)).filter Nat.Prime, (1 + U1534.A2 n p)

/-- The sieve density g(p) of page 17 for a prime p: phi(p) to the -1 times the
number |R_p| of incongruent solutions of x^2 = n mod p when p does not divide n,
and 0 when p divides n. Page 17, definition of r(d) and g(d) with d = p. -/
noncomputable def sieveDensity (n p : ℕ) : ℝ :=
  if p ∣ n then 0 else
    (((Finset.range p).filter (fun x => x ^ 2 % p = n % p)).card : ℝ) / (Nat.totient p : ℝ)

/-- The sieve product V(z) of Lemma 3.7 on page 13 and display 58 on page 17,
the product of 1 - g(p) over primes p at most z. -/
noncomputable def sieveV (n : ℕ) (z : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (⌊z⌋₊ + 1)).filter Nat.Prime, (1 - sieveDensity n p)

/-- The sifted pair count on the right of page 16 display 56, indexed by the
pair m1, m2 of the window: m1 has no prime factor below z, m2 is not prime and
has all prime factors at least z0 = Y to the 1/4 P to the -2. For large X such
m2 is a product p1 p2 with p1 in I3 and p1 at most p2, so this count is at most
the sum of Phi(m, z) over the sequence A of page 16. -/
noncomputable def siftedPairs (X Y P z : ℝ) (n : ℕ) : ℕ :=
  ((windowPairs X Y n).filter (fun v => (∀ p : ℕ, p.Prime → p ∣ v.1 → z ≤ (p : ℝ)) ∧
    ¬ v.2.Prime ∧ ∀ p : ℕ, p.Prime → p ∣ v.2 → Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p : ℝ))).card

/-- Page 16 display 56 and page 8 display 35. R0(n) counts the pairs with m1
prime and m2 rough but not prime; when the cutoff z0 is below the window I2 and
z is below the window I1, every such m1 has no prime factor below z, so R0(n)
is at most the sifted count. PROVED, elementary. -/
theorem residual_le_sifted (X Y P z : ℝ) (n : ℕ)
    (hcut : Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ Real.sqrt Y / 2) (hz : z ≤ X - Y) :
    |residualCount X Y P n| ≤ (siftedPairs X Y P z n : ℝ) := by
  classical
  set W := windowPairs X Y n with hW
  set F := W.filter (fun v => v.1.Prime ∧
    ∀ p : ℕ, p.Prime → p ∣ v.2 → Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p : ℝ)) with hF
  have h1 := Finset.card_filter_add_card_filter_not (s := F) (fun v => v.2.Prime)
  have h2 : F.filter (fun v => v.2.Prime) = W.filter (fun v => v.1.Prime ∧ v.2.Prime) := by
    ext v
    simp only [Finset.mem_filter, hF]
    constructor
    · rintro ⟨⟨hv, hp, _⟩, hq⟩
      exact ⟨hv, hp, hq⟩
    · rintro ⟨hv, hp, hq⟩
      refine ⟨⟨hv, hp, ?_⟩, hq⟩
      intro p hp' hd
      rw [(Nat.prime_dvd_prime_iff_eq hp' hq).mp hd]
      exact hcut.trans (Finset.mem_filter.mp hv).2.2.2.1
  have h1' : (F.card : ℝ) = ((F.filter (fun v => v.2.Prime)).card : ℝ) +
      ((F.filter (fun v => ¬ v.2.Prime)).card : ℝ) := by exact_mod_cast h1.symm
  have hres : residualCount X Y P n = ((F.filter (fun v => ¬ v.2.Prime)).card : ℝ) := by
    show (F.card : ℝ) - ((W.filter (fun v => v.1.Prime ∧ v.2.Prime)).card : ℝ) = _
    rw [← h2, h1']
    ring
  rw [hres, abs_of_nonneg (Nat.cast_nonneg _)]
  unfold siftedPairs
  rw [← hW]
  exact_mod_cast Finset.card_le_card (by
    intro v hv
    simp only [Finset.mem_filter, hF] at hv ⊢
    obtain ⟨⟨hvW, hp, hrough⟩, hnp⟩ := hv
    refine ⟨hvW, ?_, hnp, hrough⟩
    intro p hp' hd
    rw [(Nat.prime_dvd_prime_iff_eq hp' hp).mp hd]
    exact hz.trans (Finset.mem_filter.mp hvW).2.1)

/-- SPLIT LEAF of sieve_upper_input. Page 16 display 57 and page 17 display 58:
Lemma 3.7, the Rosser Iwaniec upper bound sieve cited from Iwaniec Theorem 1,
applied with D = Y to the 1/9 and z = exp of L to the 1 - delta/2 to the
sequence A of page 16, with N of display 57 at most a constant times
Y to the 1/2 L to the -2 log L by the prime number theorem and the remainder
sum bounded through Bombieri Vinogradov and Cauchy's inequality. The left side
is the sifted pair count, which is at most the sum of Phi(m, z) over A for
large X. A can be taken arbitrarily large. CITED. -/
theorem sifted_sieve_input (A B δ ε : ℝ) (hA : 0 < A) (hB : 0 < B) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ K X1 : ℝ, 0 < K ∧ ∀ X : ℝ, X1 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + windowY X ε ^ (1 - ε) →
      (siftedPairs X (windowY X ε) (Real.log X ^ B) (sieveLevel X δ) n : ℝ) ≤
        K * (windowY X ε ^ (1 / 2 : ℝ) * Real.log X ^ (-2 : ℝ) *
            Real.log (Real.log X) * sieveV n (sieveLevel X δ) +
          windowY X ε ^ (1 / 2 : ℝ) * Real.log X ^ (-A)) := by
  sorry

/-- Page 2 before display 4 and page 16. For X at least 2^9 and epsilon at
most 11/18, the cutoff z0 = Y to the 1/4 P to the -2 with P at least 1 lies
below the lower end sqrt Y / 2 of the window I2. -/
theorem cutoff_below_window {X ε P : ℝ} (hX : 512 ≤ X) (hε : 0 < ε) (hP : 1 ≤ P) :
    windowY X ε ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ Real.sqrt (windowY X ε) / 2 := by
  set Y := windowY X ε with hY
  have hX1 : 1 ≤ X := by linarith
  have hY16 : 16 ≤ Y := by
    have h1 : X ^ (1 / 2 : ℝ) ≤ Y :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    have h2 : (16 : ℝ) ≤ X ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      exact Real.le_sqrt_of_sq_le (by linarith)
    linarith
  have hY0 : 0 ≤ Y := by linarith
  have h4 : (2 : ℝ) ≤ Y ^ (1 / 4 : ℝ) := by
    have h := Real.rpow_le_rpow (by norm_num) hY16 (show (0 : ℝ) ≤ 1 / 4 by norm_num)
    have e : (16 : ℝ) ^ (1 / 4 : ℝ) = 2 := by
      rw [show (16 : ℝ) = 2 ^ (4 : ℕ) by norm_num, show (1 / 4 : ℝ) = ((4 : ℕ) : ℝ)⁻¹ by norm_num,
        Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
    linarith
  have hsq : Real.sqrt Y = Y ^ (1 / 4 : ℝ) * Y ^ (1 / 4 : ℝ) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_add (by linarith)]
    norm_num
  have hPz : P ^ (-2 : ℤ) ≤ 1 := by
    rw [zpow_neg]
    exact inv_le_one_of_one_le₀ (one_le_zpow₀ hP (by norm_num))
  have hq0 : 0 ≤ Y ^ (1 / 4 : ℝ) := Real.rpow_nonneg hY0 _
  rw [hsq]
  calc Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ Y ^ (1 / 4 : ℝ) * 1 := mul_le_mul_of_nonneg_left hPz hq0
    _ ≤ Y ^ (1 / 4 : ℝ) * Y ^ (1 / 4 : ℝ) / 2 := by nlinarith

/-- Page 2 and page 17. For X large in terms of delta, with epsilon at most
11/18, the sieve level z = exp of L to the 1 - delta/2 is below X - Y, the
lower end of the window I1. -/
theorem sieveLevel_below_window {X δ ε : ℝ} (hδ : 0 < δ) (hε1 : ε ≤ 11 / 18) (hX : 512 ≤ X)
    (hL : max 2 ((2 : ℝ) ^ (2 / δ)) ≤ Real.log X) :
    sieveLevel X δ ≤ X - windowY X ε := by
  have hX1 : 1 ≤ X := by linarith
  have hXpos : 0 < X := by linarith
  set L := Real.log X with hLdef
  have hL2 : 2 ≤ L := le_trans (le_max_left _ _) hL
  have hLpos : 0 < L := by linarith
  have hYle : windowY X ε * 2 ≤ X := by
    have h1 : windowY X ε ≤ X ^ (8 / 9 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)
    have h2 : (2 : ℝ) ≤ X ^ (1 / 9 : ℝ) := by
      have h := Real.rpow_le_rpow (by norm_num) hX (show (0 : ℝ) ≤ 1 / 9 by norm_num)
      have e : (512 : ℝ) ^ (1 / 9 : ℝ) = 2 := by
        rw [show (512 : ℝ) = 2 ^ (9 : ℕ) by norm_num, show (1 / 9 : ℝ) = ((9 : ℕ) : ℝ)⁻¹ by norm_num,
          Real.pow_rpow_inv_natCast (by norm_num) (by norm_num)]
      linarith
    have h3 : X ^ (8 / 9 : ℝ) * X ^ (1 / 9 : ℝ) = X := by
      rw [← Real.rpow_add hXpos]; norm_num
    have h0 : 0 ≤ X ^ (8 / 9 : ℝ) := Real.rpow_nonneg hXpos.le _
    nlinarith
  have hLd : (2 : ℝ) ≤ L ^ (δ / 2) := by
    have h := Real.rpow_le_rpow (by positivity) (le_trans (le_max_right _ _) hL)
      (show 0 ≤ δ / 2 by linarith)
    rwa [← Real.rpow_mul (by norm_num), show 2 / δ * (δ / 2) = 1 by field_simp,
      Real.rpow_one] at h
  have hsplit : L ^ (1 - δ / 2) * L ^ (δ / 2) = L := by
    rw [← Real.rpow_add hLpos]; norm_num
  have hlz0 : 0 ≤ L ^ (1 - δ / 2) := Real.rpow_nonneg hLpos.le _
  have hhalf : L ^ (1 - δ / 2) ≤ L / 2 := by nlinarith
  have hlog2 : Real.log 2 ≤ L / 2 := by
    have := Real.log_two_lt_d9; linarith
  have hz : sieveLevel X δ ≤ X / 2 := by
    unfold sieveLevel
    rw [← Real.exp_log (show 0 < X / 2 by positivity)]
    apply Real.exp_le_exp.mpr
    rw [Real.log_div hXpos.ne' (by norm_num)]
    linarith
  linarith

/-- SPLIT LEAF of residual_sieve_pointwise. Page 16 display 56, page 16 display 57
and page 17 display 58. R0(n) is at most the sum of Phi(m, z) over the sequence A
of page 16. Lemma 3.7, the Rosser Iwaniec upper bound sieve cited from Iwaniec
Theorem 1, applied with D = Y to the 1/9 and z = exp of L to the 1 - delta/2,
with N of display 57 bounded by Y to the 1/2 L to the -2 log L through the prime
number theorem, and the remainder sum bounded through Bombieri Vinogradov,
gives R0(n) at most a constant times N V(z) + Y to the 1/2 L to the -A, where A
can be taken arbitrarily large. Stated for n in H2 with X < n at most
X + Y to the 1 - epsilon, the range of Proposition 2. SPLIT burst 9: derived from
residual_le_sifted, display 56, and the CITED leaf sifted_sieve_input. -/
theorem sieve_upper_input (A B δ ε : ℝ) (hA : 0 < A) (hB : 0 < B) (hδ : 0 < δ)
    (hδ1 : δ < 1) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ K X1 : ℝ, 0 < K ∧ ∀ X : ℝ, X1 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + windowY X ε ^ (1 - ε) →
      |residualCount X (windowY X ε) (Real.log X ^ B) n| ≤
        K * (windowY X ε ^ (1 / 2 : ℝ) * Real.log X ^ (-2 : ℝ) *
            Real.log (Real.log X) * sieveV n (sieveLevel X δ) +
          windowY X ε ^ (1 / 2 : ℝ) * Real.log X ^ (-A)) := by
  obtain ⟨K, X1, hK, h⟩ := sifted_sieve_input A B δ ε hA hB hδ hδ1 hε hε1
  refine ⟨K, max X1 (max 512 (Real.exp (max 2 ((2 : ℝ) ^ (2 / δ))))), hK, ?_⟩
  intro X hX n hn hXn hnle
  have hX1 : X1 ≤ X := le_trans (le_max_left _ _) hX
  have h512 : 512 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hL : max 2 ((2 : ℝ) ^ (2 / δ)) ≤ Real.log X := by
    have hE := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hX
    have := Real.log_le_log (Real.exp_pos _) hE
    rwa [Real.log_exp] at this
  have hL1 : 1 ≤ Real.log X := by linarith [le_max_left 2 ((2 : ℝ) ^ (2 / δ))]
  have hP : 1 ≤ Real.log X ^ B := Real.one_le_rpow hL1 hB.le
  exact (residual_le_sifted _ _ _ _ n (cutoff_below_window h512 hε hP)
    (sieveLevel_below_window hδ hε1 h512 hL)).trans (h X hX1 n hn hXn hnle)

/-- SPLIT LEAF of residual_sieve_pointwise. Page 17 display 59: for n in H2,
the product of 1 - g(p) over p at most z is at most a constant times the
product of 1 - 1/p times P2(n, z), hence at most a constant times
P2(n, z) / log z. Uses display 46 on page 14 and Mertens' product. CITED. -/
theorem sieve_product_input :
    ∃ K Q0 : ℝ, 0 < K ∧ ∀ Q : ℝ, Q0 ≤ Q → ∀ n : ℕ, InH2 n →
      sieveV n Q ≤ K * ‖partialProduct2 n Q‖ / Real.log Q := by
  -- PROVED burst 8 p3: Task129s.sieve_product_explicit, K = 1 and Q0 = 2.
  refine ⟨1, 2, one_pos, fun Q hQ n _ => ?_⟩
  exact Task129s.sieve_product_explicit Q hQ n

/-- SPLIT LEAF shared by residual_sieve_pointwise and product_series_almost_all.
Page 13 display 48, lower bound: P2(n, P) is at least a constant times
(log P) to the -1. The paper cites Schwarz Sections 2 and 3; it rests on
property iii on page 13, A2(n, p) > -1 for n in H2, and display 46. CITED. -/
theorem product_lower_input :
    ∃ c Q0 : ℝ, 0 < c ∧ ∀ Q : ℝ, Q0 ≤ Q → ∀ n : ℕ, InH2 n →
      c / Real.log Q ≤ ‖partialProduct2 n Q‖ := by
  -- PROVED burst 8 p3: Task129a.P2_lower_explicit, ported from the sibling
  -- branch claude/KumchevLiu2007-circle_input-p2, c = exp(-44) and Q0 = 2.
  obtain ⟨c, Q0, hc, _, h⟩ := Task129a.P2_lower_explicit
  exact ⟨c, Q0, hc, fun Q hQ n hn => h Q hQ n hn⟩

/-- SPLIT LEAF of product_series_almost_all. Lemma 3.8 on page 14, display 49,
for j = 2, a local twin of Task129b.lemma38_two with partialProduct2 in place of
the identical Task129b.product2 and intervalNumbers unfolded. Decomp129 cannot
import the proof chain, since that chain imports Decomp129. The clean supply is
Task342e.lemma38_two_proved; the exact supply theorem is
Supply129r.lemma38_two_local_supply. CITED here. -/
theorem lemma38_two_local (A ε : ℝ) (hA : 2 ≤ A) (hε : 0 < ε) :
    ∃ C x0 : ℝ, 0 < C ∧ 2 ≤ x0 ∧
    ∀ x y P Q : ℝ, x0 ≤ x → x ^ ε ≤ y → y ≤ x → 0 < P → P ≤ Q →
      Q ≤ Real.exp (Real.log x ^ (1 - ε)) →
      (∑ n ∈ Finset.Ioc ⌊x⌋₊ ⌊x + y⌋₊, ‖series2 n P - partialProduct2 n Q‖ ^ 2) ≤
        C * (y / P * Real.log x + y / Real.log x ^ A) := by
  sorry

/-- Page 17, choice z = exp of L to the 1 - delta/2: log z = L to the 1 - delta/2. -/
theorem log_sieveLevel (X δ : ℝ) :
    Real.log (sieveLevel X δ) = Real.log X ^ (1 - δ / 2) := by
  simp [sieveLevel]

/-- Page 17. A real Q with Q^2 at most L lies below z = exp of L to the 1 - delta/2. -/
theorem le_sieveLevel {X δ Q : ℝ} (hδ : δ < 1) (hL1 : 1 ≤ Real.log X)
    (hQ : Q ^ 2 ≤ Real.log X) : Q ≤ sieveLevel X δ := by
  set L := Real.log X
  have hL0 : 0 ≤ L := by linarith
  have h1 : Q ≤ Real.sqrt L := by
    have := Real.le_sqrt_of_sq_le hQ
    exact this
  have h2 : Real.sqrt L ≤ L ^ (1 - δ / 2) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
  have h3 : L ^ (1 - δ / 2) ≤ sieveLevel X δ := by
    unfold sieveLevel
    linarith [Real.add_one_le_exp (L ^ (1 - δ / 2))]
  linarith

/-- Page 17, the constraint P = L^B at most z of Lemma 3.8: for L large in
terms of B and delta, L^B is at most exp of L to the 1 - delta/2. -/
theorem pow_le_sieveLevel (B δ : ℝ) (hB : 0 < B) (hδ : δ < 1) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ X : ℝ, M ≤ Real.log X → Real.log X ^ B ≤ sieveLevel X δ := by
  set s := (1 - δ / 2) / 2 with hs
  have hs0 : 0 < s := by rw [hs]; linarith
  refine ⟨max 1 ((B / s) ^ (1 / s)), le_max_left _ _, ?_⟩
  intro X hX
  set L := Real.log X
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hX
  have hLpos : 0 < L := by linarith
  have hBs : 0 ≤ B / s := by positivity
  have hpow : B / s ≤ L ^ s := by
    have h := Real.rpow_le_rpow (Real.rpow_nonneg hBs _) (le_trans (le_max_right _ _) hX) hs0.le
    rwa [one_div, Real.rpow_inv_rpow hBs hs0.ne'] at h
  have hlog : Real.log L ≤ L ^ s / s := Real.log_le_rpow_div hLpos.le hs0
  have hLs : 0 ≤ L ^ s := Real.rpow_nonneg hLpos.le _
  have hkey : B * Real.log L ≤ L ^ (1 - δ / 2) := by
    have e : L ^ (1 - δ / 2) = L ^ s * L ^ s := by
      rw [← Real.rpow_add hLpos]; congr 1; rw [hs]; ring
    rw [e]
    calc B * Real.log L ≤ B * (L ^ s / s) := mul_le_mul_of_nonneg_left hlog hB.le
      _ = B / s * L ^ s := by ring
      _ ≤ L ^ s * L ^ s := mul_le_mul_of_nonneg_right hpow hLs
  rw [Real.rpow_def_of_pos hLpos]
  unfold sieveLevel
  apply Real.exp_le_exp.mpr
  linarith [mul_comm (Real.log L) B]

/-- Chebyshev counting, used on page 17 to pass from the mean square bound of
Lemma 3.8 to an exceptional set: elements where f exceeds t number at most
the sum of f over the interval divided by t. -/
theorem cnt_mul_le_sum {S : ℕ → Prop} {X H t : ℝ} (f : ℕ → ℝ) (hX : 0 ≤ X)
    (hf : ∀ n, 0 ≤ f n) (hS : ∀ n : ℕ, X < (n : ℝ) → S n → t < f n) :
    (cntIoc S X H : ℝ) * t ≤ ∑ n ∈ Finset.Ioc ⌊X⌋₊ ⌊X + H⌋₊, f n := by
  classical
  set T := (Finset.range (⌊X + H⌋₊ + 1)).filter (fun n : ℕ => X < (n : ℝ) ∧ S n)
  have hsub : T ⊆ Finset.Ioc ⌊X⌋₊ ⌊X + H⌋₊ := by
    intro n hn
    obtain ⟨hr, hXn, _⟩ := Finset.mem_filter.mp hn
    refine Finset.mem_Ioc.mpr ⟨(Nat.floor_lt hX).mpr hXn, ?_⟩
    exact Nat.lt_succ_iff.mp (Finset.mem_range.mp hr)
  have hcard : (cntIoc S X H : ℝ) * t = ∑ n ∈ T, t := by
    simp [cntIoc, T, Finset.sum_const, nsmul_eq_mul]
  rw [hcard]
  calc ∑ n ∈ T, t ≤ ∑ n ∈ T, f n := by
        apply Finset.sum_le_sum
        intro n hn
        obtain ⟨_, hXn, hSn⟩ := Finset.mem_filter.mp hn
        exact (hS n hXn hSn).le
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)

/-- SPLIT LEAF of residual_input. Proof of Proposition 2, pages 16 and 17,
displays 56, 57, 58 and 59 together with the lower bound in display 48 on page 13.
The upper bound sieve of Lemma 3.7 with D = Y to the 1/9 and z = sieveLevel,
fed by the prime number theorem for N in display 57 and by Bombieri Vinogradov
for the remainders r(d), gives R0(n) at most a constant times
Y to the 1/2 times L to the -3 + delta times P2(n, z), for every n in H2 with
X < n at most X + H and H at most Y to the 1 - epsilon, as written on page 17.
R0 is the difference residualCount by display 35 on page 8. The restriction
epsilon at most 11/18 is the nonempty H range of Theorem 1. SPLIT burst 9: derived
from sieve_upper_input, sieve_product_input and product_lower_input. -/
theorem residual_sieve_pointwise (B δ ε : ℝ) (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ K1 X1 : ℝ, 0 < K1 ∧ ∀ X : ℝ, X1 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + windowY X ε ^ (1 - ε) →
      |residualCount X (windowY X ε) (Real.log X ^ B) n| ≤
        K1 * windowY X ε ^ (1 / 2 : ℝ) * Real.log X ^ (-3 + δ) *
          ‖partialProduct2 n (sieveLevel X δ)‖ := by
  obtain ⟨K, Xs, hK, hs⟩ := sieve_upper_input 4 B δ ε (by norm_num) hB hδ hδ1 hε hε1
  obtain ⟨K', Q1, hK', hq⟩ := sieve_product_input
  obtain ⟨c, Q2, hc, hl⟩ := product_lower_input
  refine ⟨K * (K' * (2 / δ) + 1 / c), max Xs (Real.exp (max 1 (max (Q1 ^ 2) (Q2 ^ 2)))),
    by positivity, ?_⟩
  intro X hX n hn hXn hnle
  have hXs : Xs ≤ X := le_trans (le_max_left _ _) hX
  have hM : max 1 (max (Q1 ^ 2) (Q2 ^ 2)) ≤ Real.log X := by
    have hE := le_trans (le_max_right _ _) hX
    have := Real.log_le_log (Real.exp_pos _) hE
    rwa [Real.log_exp] at this
  have hR := hs X hXs n hn hXn hnle
  set L := Real.log X with hLdef
  have hL1 : 1 ≤ L := le_trans (le_max_left _ _) hM
  have hLpos : 0 < L := by linarith
  have hQ1 : Q1 ≤ sieveLevel X δ :=
    le_sieveLevel hδ1 hL1 (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hM))
  have hQ2 : Q2 ≤ sieveLevel X δ :=
    le_sieveLevel hδ1 hL1 (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hM))
  have hV := hq _ hQ1 n hn
  have hP := hl _ hQ2 n hn
  rw [log_sieveLevel] at hV hP
  set z := sieveLevel X δ with hz
  set Pn := ‖partialProduct2 n z‖ with hPn
  set Y2 := windowY X ε ^ (1 / 2 : ℝ) with hY2
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) (le_trans (le_max_right _ _) hX)
  have hY : 0 ≤ Y2 := Real.rpow_nonneg (Real.rpow_nonneg hXpos.le _) _
  have hlz : 0 < L ^ (1 - δ / 2) := Real.rpow_pos_of_pos hLpos _
  have hPn0 : 0 ≤ Pn := norm_nonneg _
  have hlogL : Real.log L ≤ L ^ (δ / 2) / (δ / 2) :=
    Real.log_le_rpow_div hLpos.le (by linarith)
  have hlogL0 : 0 ≤ Real.log L := Real.log_nonneg hL1
  have hW : 0 ≤ K' * Pn / L ^ (1 - δ / 2) := by positivity
  have t1 : Real.log L * sieveV n z ≤ (2 / δ) * (L ^ (δ / 2) * (K' * Pn / L ^ (1 - δ / 2))) := by
    calc Real.log L * sieveV n z ≤ Real.log L * (K' * Pn / L ^ (1 - δ / 2)) :=
          mul_le_mul_of_nonneg_left hV hlogL0
      _ ≤ (L ^ (δ / 2) / (δ / 2)) * (K' * Pn / L ^ (1 - δ / 2)) :=
          mul_le_mul_of_nonneg_right hlogL hW
      _ = _ := by field_simp
  have e1 : L ^ (-2 : ℝ) * L ^ (δ / 2) / L ^ (1 - δ / 2) = L ^ (-3 + δ) := by
    rw [div_eq_mul_inv, ← Real.rpow_neg hLpos.le, ← Real.rpow_add hLpos,
      ← Real.rpow_add hLpos]
    ring_nf
  have T1 : Y2 * L ^ (-2 : ℝ) * Real.log L * sieveV n z ≤
      Y2 * L ^ (-3 + δ) * Pn * (K' * (2 / δ)) := by
    have h : L ^ (-2 : ℝ) * (Real.log L * sieveV n z) ≤ L ^ (-3 + δ) * Pn * (K' * (2 / δ)) := by
      calc L ^ (-2 : ℝ) * (Real.log L * sieveV n z) ≤
            L ^ (-2 : ℝ) * ((2 / δ) * (L ^ (δ / 2) * (K' * Pn / L ^ (1 - δ / 2)))) :=
            mul_le_mul_of_nonneg_left t1 (Real.rpow_nonneg hLpos.le _)
        _ = (L ^ (-2 : ℝ) * L ^ (δ / 2) / L ^ (1 - δ / 2)) * Pn * (K' * (2 / δ)) := by ring
        _ = _ := by rw [e1]
    calc Y2 * L ^ (-2 : ℝ) * Real.log L * sieveV n z =
          Y2 * (L ^ (-2 : ℝ) * (Real.log L * sieveV n z)) := by ring
      _ ≤ Y2 * (L ^ (-3 + δ) * Pn * (K' * (2 / δ))) := mul_le_mul_of_nonneg_left h hY
      _ = _ := by ring
  have hLle : L ^ (1 - δ / 2) ≤ L := by
    have := Real.rpow_le_rpow_of_exponent_le hL1 (show 1 - δ / 2 ≤ 1 by linarith)
    rwa [Real.rpow_one] at this
  have hPc : L ^ (-1 : ℝ) ≤ Pn * (1 / c) := by
    rw [Real.rpow_neg_one]
    have h1 : c / L ≤ c / L ^ (1 - δ / 2) := div_le_div_of_nonneg_left hc.le hlz hLle
    have h2 : c / L ≤ Pn := h1.trans hP
    rw [mul_one_div, le_div_iff₀ hc]
    calc L⁻¹ * c = c / L := by ring
      _ ≤ Pn := h2
  have T2 : Y2 * L ^ (-4 : ℝ) ≤ Y2 * L ^ (-3 + δ) * Pn * (1 / c) := by
    have hL4 : L ^ (-4 : ℝ) = L ^ (-3 : ℝ) * L ^ (-1 : ℝ) := by
      rw [← Real.rpow_add hLpos]; norm_num
    have h3 : L ^ (-3 : ℝ) ≤ L ^ (-3 + δ) := Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
    have h4 : L ^ (-4 : ℝ) ≤ L ^ (-3 + δ) * (Pn * (1 / c)) := by
      rw [hL4]
      exact mul_le_mul h3 hPc (Real.rpow_nonneg hLpos.le _) (Real.rpow_nonneg hLpos.le _)
    calc Y2 * L ^ (-4 : ℝ) ≤ Y2 * (L ^ (-3 + δ) * (Pn * (1 / c))) :=
          mul_le_mul_of_nonneg_left h4 hY
      _ = _ := by ring
  calc |residualCount X (windowY X ε) (L ^ B) n| ≤
        K * (Y2 * L ^ (-2 : ℝ) * Real.log L * sieveV n z + Y2 * L ^ (-4 : ℝ)) := hR
    _ ≤ K * (Y2 * L ^ (-3 + δ) * Pn * (K' * (2 / δ)) + Y2 * L ^ (-3 + δ) * Pn * (1 / c)) :=
        mul_le_mul_of_nonneg_left (add_le_add T1 T2) hK.le
    _ = K * (K' * (2 / δ) + 1 / c) * Y2 * L ^ (-3 + δ) * Pn := by ring

/-- SPLIT LEAF of residual_input. Page 16, the comparison r2(n) of order
Y to the 1/2 times L to the -2 used with display 57 to turn the bound
R0(n) of order Y to the 1/2 L to the -3 + delta P2(n, z) into the relative
bound of Proposition 2. For n - X at most Y to the 1 - epsilon, every m2 in
the window I2 of page 2 display 5 gives an admissible pair, and each weight in
display 6 is at least L to the -2. Elementary. PROVED 2026-11-12 PROVE PASS:
each m2 with sqrt Y / 2 at most m2 below sqrt Y gives the pair n - m2^2, m2,
and there are at least sqrt Y / 4 such m2. AI wrote the Lean code. -/
theorem integerMain_lower (ε : ℝ) (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ c X1 : ℝ, 0 < c ∧ ∀ X : ℝ, X1 ≤ X → ∀ n : ℕ, X < (n : ℝ) →
      (n : ℝ) ≤ X + windowY X ε ^ (1 - ε) →
      c * windowY X ε ^ (1 / 2 : ℝ) * Real.log X ^ (-2 : ℝ) ≤
        integerMain X (windowY X ε) n := by
  set T := max 9 (24 / (7 * ε)) with hT
  refine ⟨1 / 4, Real.exp T, by norm_num, ?_⟩
  intro X hX n hXn hnY
  have hXpos : 0 < X := lt_of_lt_of_le (Real.exp_pos _) hX
  set L := Real.log X with hL
  have hLT : T ≤ L := by rw [← Real.log_exp T]; exact Real.log_le_log (Real.exp_pos _) hX
  have hL9 : 9 ≤ L := le_trans (le_max_left _ _) hLT
  have hLε : 24 / (7 * ε) ≤ L := le_trans (le_max_right _ _) hLT
  have hεL : 24 ≤ 7 * ε * L := by rw [div_le_iff₀ (by positivity)] at hLε; linarith
  have hX10 : 10 ≤ X := by
    have h1 := Real.add_one_le_exp T
    have h2 : Real.exp T ≤ X := hX
    linarith [le_max_left 9 (24 / (7 * ε))]
  set e := 7 / 12 + ε / 2 with he
  have he7 : 7 / 12 ≤ e := by linarith
  have he8 : e ≤ 8 / 9 := by linarith
  have hYdef : windowY X ε = X ^ e := rfl
  set Y := windowY X ε with hY
  have hYpos : 0 < Y := by rw [hYdef]; exact Real.rpow_pos_of_pos hXpos _
  have hlogY : Real.log Y = e * L := by rw [hYdef]; exact Real.log_rpow hXpos e
  have hlog2 : Real.log 2 < 0.7 := by
    have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
  have hY16 : 16 ≤ Y := by
    have h16 : Real.log 16 = 4 * Real.log 2 := by
      rw [show (16:ℝ) = 2 ^ 4 by norm_num, Real.log_pow]; norm_num
    calc (16:ℝ) = Real.exp (Real.log 16) := (Real.exp_log (by norm_num)).symm
      _ ≤ Real.exp (Real.log Y) := by
          apply Real.exp_le_exp.mpr; rw [hlogY, h16]; nlinarith
      _ = Y := Real.exp_log hYpos
  have hX2Y : 2 * Y ≤ X := by
    calc 2 * Y = Real.exp (Real.log 2 + Real.log Y) := by
          rw [Real.exp_add, Real.exp_log (by norm_num), Real.exp_log hYpos]
      _ ≤ Real.exp L := by
          apply Real.exp_le_exp.mpr; rw [hlogY]; nlinarith
      _ = X := Real.exp_log hXpos
  have hY4 : 4 * Y ^ (1 - ε) < Y := by
    have h4 : Real.log 4 = 2 * Real.log 2 := by
      rw [show (4:ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
    calc 4 * Y ^ (1 - ε) = Real.exp (Real.log 4 + Real.log Y * (1 - ε)) := by
          rw [Real.rpow_def_of_pos hYpos, Real.exp_add, Real.exp_log (by norm_num)]
      _ < Real.exp (Real.log Y) := by
          apply Real.exp_lt_exp.mpr; rw [hlogY, h4]
          nlinarith [mul_le_mul_of_nonneg_right he7 (by positivity : (0:ℝ) ≤ ε * L)]
      _ = Y := Real.exp_log hYpos
  set s := Real.sqrt Y with hs
  have hss : s * s = Y := Real.mul_self_sqrt hYpos.le
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs4 : 4 ≤ s := by nlinarith
  have hsY : s ≤ Y := by nlinarith
  set K := Finset.Ico ⌈s / 2⌉₊ ⌈s⌉₊ with hK
  have hKcard : s / 4 ≤ (K.card : ℝ) := by
    rw [hK, Nat.card_Ico, Nat.cast_sub (Nat.ceil_mono (by linarith : s / 2 ≤ s))]
    have h1 := Nat.le_ceil s
    have h2 := Nat.ceil_lt_add_one (by linarith : (0:ℝ) ≤ s / 2)
    linarith
  let f : ℕ → ℕ × ℕ := fun k => (n - k ^ 2, k)
  have hmem : ∀ k ∈ K, (s / 2 ≤ (k : ℝ) ∧ (k : ℝ) < s) := by
    intro k hk
    rw [hK, Finset.mem_Ico] at hk
    exact ⟨Nat.ceil_le.mp hk.1, Nat.lt_ceil.mp hk.2⟩
  have hfacts : ∀ k ∈ K, f k ∈ windowPairs X Y n ∧
      1 / (L * L) ≤ 1 / (Real.log ((f k).1 : ℝ) * Real.log ((f k).2 : ℝ)) := by
    intro k hk
    obtain ⟨hk1, hk2⟩ := hmem k hk
    have hk0 : (0:ℝ) ≤ k := Nat.cast_nonneg k
    have hkY : (k : ℝ) ^ 2 < Y := by nlinarith
    have hkY4 : Y / 4 ≤ (k : ℝ) ^ 2 := by nlinarith
    have hkn : k ^ 2 ≤ n := by
      have : ((k ^ 2 : ℕ) : ℝ) ≤ n := by push_cast; linarith
      exact_mod_cast this
    have hm1 : ((n - k ^ 2 : ℕ) : ℝ) = (n : ℝ) - (k : ℝ) ^ 2 := by
      rw [Nat.cast_sub hkn]; push_cast; ring
    have hm1lo : X - Y < ((n - k ^ 2 : ℕ) : ℝ) := by rw [hm1]; linarith
    have hm1hi : ((n - k ^ 2 : ℕ) : ℝ) < X := by rw [hm1]; linarith
    refine ⟨?_, ?_⟩
    · rw [windowPairs, Finset.mem_filter]
      exact ⟨Finset.mem_product.mpr ⟨Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hm1hi.le)),
        Finset.mem_range.mpr (Nat.lt_succ_of_le (Nat.le_floor hk2.le))⟩,
        hm1lo.le, hm1hi, hk1, hk2, Nat.sub_add_cancel hkn⟩
    · simp only [f]
      have hl1 : 0 < Real.log ((n - k ^ 2 : ℕ) : ℝ) := Real.log_pos (by linarith)
      have hl1' : Real.log ((n - k ^ 2 : ℕ) : ℝ) ≤ L := Real.log_le_log (by linarith) hm1hi.le
      have hl2 : 0 < Real.log (k : ℝ) := Real.log_pos (by linarith)
      have hl2' : Real.log (k : ℝ) ≤ L := Real.log_le_log (by linarith) (by linarith)
      apply one_div_le_one_div_of_le (by positivity)
      exact mul_le_mul hl1' hl2' hl2.le (by linarith)
  have hinj : Set.InjOn f K := fun a _ b _ h => congrArg Prod.snd h
  have hnonneg : ∀ v ∈ windowPairs X Y n, v ∉ K.image f →
      0 ≤ 1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ)) := by
    intro v _ _
    have := Real.log_natCast_nonneg v.1
    have := Real.log_natCast_nonneg v.2
    positivity
  have hsub : K.image f ⊆ windowPairs X Y n := by
    intro v hv
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp hv
    exact (hfacts k hk).1
  have hLpos : 0 < L := by linarith
  have hrw : (1 / 4 : ℝ) * Y ^ (1 / 2 : ℝ) * L ^ (-2 : ℝ) = (s / 4) * (1 / (L * L)) := by
    rw [← Real.sqrt_eq_rpow, Real.rpow_neg hLpos.le, Real.rpow_two]; ring
  rw [hrw]
  unfold integerMain
  calc (s / 4) * (1 / (L * L)) ≤ (K.card : ℝ) * (1 / (L * L)) :=
        mul_le_mul_of_nonneg_right hKcard (by positivity)
    _ = ∑ k ∈ K, 1 / (L * L) := by rw [Finset.sum_const, nsmul_eq_mul]
    _ ≤ ∑ k ∈ K, 1 / (Real.log ((f k).1 : ℝ) * Real.log ((f k).2 : ℝ)) :=
        Finset.sum_le_sum (fun k hk => (hfacts k hk).2)
    _ = ∑ v ∈ K.image f, 1 / (Real.log (v.1 : ℝ) * Real.log (v.2 : ℝ)) :=
        by rw [Finset.sum_image hinj]
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg hsub hnonneg

/-- SPLIT LEAF of residual_input. Page 17, last display of the proof of
Proposition 2: by display 47 and Lemma 3.8 on page 14 with x = X, y = H and
Q = z, P2(n, z) = S2(n, P) times 1 + O of L to the -1 for all but
O of H L to the -A integers n in H2 in the interval, provided P is at least
L to the A + 5. Lemma 3.8 allows every y from x to the epsilon up to x, so
the full H range of Theorem 1 is covered as written. SPLIT burst 9: derived from
lemma38_two_local and product_lower_input by Chebyshev counting. -/
theorem product_series_almost_all (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ δ ε : ℝ, 0 < δ → δ < 1 → 0 < ε →
      ∃ C K2 X0 : ℝ, 0 < C ∧ 0 ≤ K2 ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          K2 * Real.log X ^ (-1 : ℝ) * ‖series2 n (Real.log X ^ B)‖ <
          ‖partialProduct2 n (sieveLevel X δ) - series2 n (Real.log X ^ B)‖) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  obtain ⟨c, Q2, hc, hl⟩ := product_lower_input
  refine ⟨A + 5, by linarith, ?_⟩
  intro B hB δ ε hδ hδ1 hε
  have hBpos : 0 < B := by linarith
  set ε' := min (δ / 2) (7 / 18) with hε'
  have hε'pos : 0 < ε' := lt_min (by linarith) (by norm_num)
  have hε'δ : ε' ≤ δ / 2 := min_le_left _ _
  have hε'7 : ε' ≤ 7 / 18 := min_le_right _ _
  obtain ⟨C, x0, hC, hx0, hm⟩ := lemma38_two_local (max 2 (A + 4)) ε' (le_max_left _ _) hε'pos
  obtain ⟨M, hM1, hMz⟩ := pow_le_sieveLevel B δ hBpos hδ1
  refine ⟨2 * C, 2 / c, max x0 (Real.exp (max M (max (Q2 ^ 2) (2 / c)))), by positivity,
    by positivity, le_trans hx0 (le_max_left _ _), ?_⟩
  intro X H hX hH hHX
  have hx0X : x0 ≤ X := le_trans (le_max_left _ _) hX
  have hXpos : 0 < X := by linarith
  have hLM : max M (max (Q2 ^ 2) (2 / c)) ≤ Real.log X := by
    have hE := le_trans (le_max_right _ _) hX
    have := Real.log_le_log (Real.exp_pos _) hE
    rwa [Real.log_exp] at this
  have hHpos : 0 < H := lt_of_lt_of_le (Real.rpow_pos_of_pos hXpos _) hH
  have hX1 : 1 ≤ X := by linarith
  have hyε : X ^ ε' ≤ H :=
    le_trans (Real.rpow_le_rpow_of_exponent_le hX1 (by linarith)) hH
  have hPz := hMz X (le_trans (le_max_left _ _) hLM)
  set L := Real.log X with hLdef
  have hL1 : 1 ≤ L := le_trans hM1 (le_trans (le_max_left _ _) hLM)
  have hLpos : 0 < L := by linarith
  have hQ2z : Q2 ≤ sieveLevel X δ :=
    le_sieveLevel hδ1 hL1 (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) hLM))
  have hLc : 2 / c ≤ L := le_trans (le_max_right _ _) (le_trans (le_max_right _ _) hLM)
  have hP := hl _ hQ2z
  rw [log_sieveLevel] at hP
  have hzle : sieveLevel X δ ≤ Real.exp (L ^ (1 - ε')) := by
    unfold sieveLevel
    exact Real.exp_le_exp.mpr (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith))
  have hPpos : 0 < L ^ B := Real.rpow_pos_of_pos hLpos B
  have hsum := hm X H (L ^ B) (sieveLevel X δ) hx0X hyε hHX hPpos hPz hzle
  set z := sieveLevel X δ with hz
  set P := L ^ B with hPdef
  have hlz : 0 < L ^ (1 - δ / 2) := Real.rpow_pos_of_pos hLpos _
  have hLle : L ^ (1 - δ / 2) ≤ L := by
    have := Real.rpow_le_rpow_of_exponent_le hL1 (show 1 - δ / 2 ≤ 1 by linarith)
    rwa [Real.rpow_one] at this
  have hu0 : 0 ≤ L⁻¹ := inv_nonneg.mpr hLpos.le
  have hu : L⁻¹ ≤ c / 2 := by
    rw [inv_le_comm₀ hLpos (by positivity)]
    calc (c / 2)⁻¹ = 2 / c := by rw [inv_div]
      _ ≤ L := hLc
  have key : ∀ n : ℕ, X < (n : ℝ) → (InH2 n ∧ 2 / c * L ^ (-1 : ℝ) * ‖series2 n P‖ <
      ‖partialProduct2 n z - series2 n P‖) →
      L⁻¹ * L⁻¹ * (L⁻¹ * L⁻¹) < ‖series2 n P - partialProduct2 n z‖ ^ 2 := by
    rintro n - ⟨hn, hbad⟩
    rw [Real.rpow_neg_one] at hbad
    have hpn := hP n hn
    set d := ‖partialProduct2 n z - series2 n P‖ with hd
    set s := ‖series2 n P‖ with hs
    set p := ‖partialProduct2 n z‖ with hp
    have hlt : L⁻¹ * L⁻¹ < d := by
      by_contra hcon
      push_neg at hcon
      have hcp : c * L⁻¹ ≤ p := by
        have h1 : c / L ≤ c / L ^ (1 - δ / 2) := div_le_div_of_nonneg_left hc.le hlz hLle
        calc c * L⁻¹ = c / L := by ring
          _ ≤ p := h1.trans hpn
      have htri : p - s ≤ d := norm_sub_norm_le _ _
      have huu : L⁻¹ * L⁻¹ ≤ c / 2 * L⁻¹ := mul_le_mul_of_nonneg_right hu hu0
      have hsl : c / 2 * L⁻¹ ≤ s := by linarith
      have hfin : L⁻¹ * L⁻¹ ≤ 2 / c * L⁻¹ * s := by
        calc L⁻¹ * L⁻¹ = 2 / c * L⁻¹ * (c / 2 * L⁻¹) := by field_simp
          _ ≤ 2 / c * L⁻¹ * s := mul_le_mul_of_nonneg_left hsl (by positivity)
      linarith
    have h0 : 0 ≤ L⁻¹ * L⁻¹ := by positivity
    rw [norm_sub_rev, sq]
    exact mul_self_lt_mul_self h0 hlt
  have hcheb := cnt_mul_le_sum (S := fun n => InH2 n ∧ 2 / c * L ^ (-1 : ℝ) * ‖series2 n P‖ <
      ‖partialProduct2 n z - series2 n P‖) (H := H)
    (fun n => ‖series2 n P - partialProduct2 n z‖ ^ 2) hXpos.le (fun n => by positivity) key
  have ht : 0 < L⁻¹ * L⁻¹ * (L⁻¹ * L⁻¹) := by positivity
  have hcnt := le_trans hcheb hsum
  have e4 : (L⁻¹ * L⁻¹ * (L⁻¹ * L⁻¹))⁻¹ = L ^ (4 : ℝ) := by
    rw [show (4 : ℝ) = ((4 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    field_simp
  have hA' : A + 4 ≤ max 2 (A + 4) := le_max_right _ _
  have b1 : H / P * L * L ^ (4 : ℝ) ≤ H * L ^ (-A) := by
    have : H / P * L * L ^ (4 : ℝ) = H * L ^ (-B + 1 + 4) := by
      rw [Real.rpow_add hLpos, Real.rpow_add hLpos, Real.rpow_neg hLpos.le, Real.rpow_one]
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) hHpos.le
  have b2 : H / L ^ (max 2 (A + 4)) * L ^ (4 : ℝ) ≤ H * L ^ (-A) := by
    have : H / L ^ (max 2 (A + 4)) * L ^ (4 : ℝ) = H * L ^ (-(max 2 (A + 4)) + 4) := by
      rw [Real.rpow_add hLpos, Real.rpow_neg hLpos.le]
      ring
    rw [this]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)) hHpos.le
  have hfinal : (cntIoc (fun n => InH2 n ∧ 2 / c * L ^ (-1 : ℝ) * ‖series2 n P‖ <
      ‖partialProduct2 n z - series2 n P‖) X H : ℝ) ≤
      C * (H / P * L + H / L ^ (max 2 (A + 4))) * L ^ (4 : ℝ) := by
    rw [← e4, ← div_eq_mul_inv, le_div_iff₀ ht]
    exact hcnt
  calc _ ≤ C * (H / P * L + H / L ^ (max 2 (A + 4))) * L ^ (4 : ℝ) := hfinal
    _ = C * (H / P * L * L ^ (4 : ℝ) + H / L ^ (max 2 (A + 4)) * L ^ (4 : ℝ)) := by ring
    _ ≤ C * (H * L ^ (-A) + H * L ^ (-A)) := mul_le_mul_of_nonneg_left (add_le_add b1 b2) hC.le
    _ = 2 * C * H / L ^ A := by rw [Real.rpow_neg hLpos.le]; ring

/-- SPLIT LEAF of residual_input, NOT WRITTEN IN THE PAPER. Proposition 2 on
page 16 is stated only for H at most Y to the 1 - epsilon, while Theorem 1 on
page 2 allows H up to X. This leaf is the remaining range X + Y to the
1 - epsilon < n at most X + H, with the windows of page 2 displays 4 to 6
still anchored at X. The CITED docstring of residual_input already names this
extension, and PROGRESS.md records it as BLOCKED NO WRITTEN PROOF. CITED. -/
theorem residual_full_range_extension (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ δ ε : ℝ, 0 < δ → 0 < ε →
      ∃ C K X0 : ℝ, 0 < C ∧ 0 < K ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => X + windowY X ε ^ (1 - ε) < (n : ℝ) ∧ InH2 n ∧
          K * ‖main2 X (windowY X ε) (Real.log X ^ B) n‖ * Real.log X ^ (-1 + δ) <
          |residualCount X (windowY X ε) (Real.log X ^ B) n|) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  sorry

/-- Arithmetic of page 16 Proposition 2 and page 17: a relative error
bound P2 = S2 times 1 + O of L to the -1 gives a norm comparison. -/
theorem norm_le_of_rel_close {a b : ℂ} {K2 Li : ℝ} (hK2 : 0 ≤ K2) (hLi0 : 0 ≤ Li)
    (hLi : Li ≤ 1) (h : ‖a - b‖ ≤ K2 * Li * ‖b‖) : ‖a‖ ≤ (1 + K2) * ‖b‖ := by
  have htri : ‖a‖ ≤ ‖a - b‖ + ‖b‖ := by
    simpa using norm_add_le (a - b) b
  have hb : 0 ≤ ‖b‖ := norm_nonneg b
  have : K2 * Li * ‖b‖ ≤ K2 * ‖b‖ := by
    have := mul_le_mul_of_nonneg_left hLi hK2
    exact mul_le_mul_of_nonneg_right (by simpa using this) hb
  nlinarith

/-- Arithmetic of page 17, combining the sieve bound R0 of order
Y to the 1/2 L to the -3 + delta P2(n, z), the comparison P2 = S2 times
1 + O of L to the -1, and r2 at least c Y to the 1/2 L to the -2. -/
theorem residual_compare_core {R I S Q K1 K2 c Ke Y2 L2 Ld L3d L3 : ℝ}
    (hK1 : 0 < K1) (hK2 : 0 ≤ K2) (hc : 0 < c) (hKe : 0 < Ke) (hS : 0 ≤ S)
    (hY2 : 0 < Y2) (hL2 : 0 < L2) (hLd : 0 < Ld) (hL3d : 0 ≤ L3d)
    (hexp : L2 * Ld = L3) (hmono : L3d ≤ L3)
    (hres : R ≤ K1 * Y2 * L3d * Q) (hQ : Q ≤ (1 + K2) * S) (hI : c * Y2 * L2 ≤ I) :
    R ≤ (Ke + K1 * (1 + K2) / c) * (I * S) * Ld := by
  have hA0 : 0 ≤ K1 * Y2 * L3d := by positivity
  have h1 : R ≤ K1 * Y2 * L3d * ((1 + K2) * S) :=
    hres.trans (mul_le_mul_of_nonneg_left hQ hA0)
  have h2 : K1 * Y2 * L3d * ((1 + K2) * S) ≤ K1 * Y2 * L3 * ((1 + K2) * S) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity)
    exact mul_le_mul_of_nonneg_left hmono (by positivity)
  have h3 : K1 * Y2 * L3 * ((1 + K2) * S) =
      (K1 * (1 + K2) / c) * (c * Y2 * L2) * S * Ld := by
    rw [← hexp]; field_simp
  have h4 : (K1 * (1 + K2) / c) * (c * Y2 * L2) * S * Ld ≤
      (K1 * (1 + K2) / c) * I * S * Ld := by
    have hk : 0 ≤ K1 * (1 + K2) / c := by positivity
    have := mul_le_mul_of_nonneg_left hI hk
    have := mul_le_mul_of_nonneg_right this hS
    exact mul_le_mul_of_nonneg_right this hLd.le
  have hI0 : 0 ≤ I := le_trans (by positivity) hI
  have h5 : (K1 * (1 + K2) / c) * I * S * Ld ≤ (Ke + K1 * (1 + K2) / c) * (I * S) * Ld := by
    have h0 : 0 ≤ I * S * Ld := by positivity
    nlinarith
  linarith

/-- LEAF. Proposition 2, pages 16 and 17, applied to the residual of eq. 35.
This includes the parameter reductions and subdivision needed for the full H range.
The published inputs are the prime number theorem, Bombieri Vinogradov and the
Rosser Iwaniec sieve of Lemma 3.7. SPLIT: derived below from the four leaves
residual_sieve_pointwise, integerMain_lower, product_series_almost_all and
residual_full_range_extension, with no sorry of its own. -/
theorem residual_input (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ δ ε : ℝ, 0 < δ → 0 < ε →
      ∃ C K X0 : ℝ, 0 < C ∧ 0 < K ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          K * ‖main2 X (windowY X ε) (Real.log X ^ B) n‖ * Real.log X ^ (-1 + δ) <
          |residualCount X (windowY X ε) (Real.log X ^ B) n|) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  obtain ⟨Bp, hBp, hp⟩ := product_series_almost_all A hA
  obtain ⟨Be, hBe, he⟩ := residual_full_range_extension A hA
  refine ⟨max Bp Be, lt_of_lt_of_le hBp (le_max_left _ _), ?_⟩
  intro B hB δ ε hδ hε
  have hBpos : 0 < B := lt_of_lt_of_le hBp (le_trans (le_max_left _ _) hB)
  by_cases hε1 : ε ≤ 11 / 18
  swap
  · refine ⟨1, 1, 2, one_pos, one_pos, le_refl _, ?_⟩
    intro X H hX hH hHX
    exfalso
    have hX1 : 1 < X := by linarith
    have hexp : 7 / 18 + ε ≤ 1 :=
      (Real.rpow_le_rpow_left_iff hX1).mp (by simpa only [Real.rpow_one] using hH.trans hHX)
    exact hε1 (by linarith)
  set δ' := min δ (1 / 2) with hδ'def
  have hδ'pos : 0 < δ' := lt_min hδ (by norm_num)
  have hδ'1 : δ' < 1 := lt_of_le_of_lt (min_le_right _ _) (by norm_num)
  have hδ'le : δ' ≤ δ := min_le_left _ _
  obtain ⟨K1, X1, hK1, h1⟩ := residual_sieve_pointwise B δ' ε hBpos hδ'pos hδ'1 hε hε1
  obtain ⟨c, X3, hc, h3⟩ := integerMain_lower ε hε hε1
  obtain ⟨C2, K2, X2, hC2, hK2, hX2, h2⟩ :=
    hp B (le_trans (le_max_left _ _) hB) δ' ε hδ'pos hδ'1 hε
  obtain ⟨Ce, Ke, Xe, hCe, hKe, hXe, hext⟩ :=
    he B (le_trans (le_max_right _ _) hB) δ ε hδ hε
  refine ⟨C2 + Ce, Ke + K1 * (1 + K2) / c, max (max X1 X2) (max X3 (max Xe 3)),
    by positivity, by positivity, le_trans hX2 (le_trans (le_max_right _ _) (le_max_left _ _)), ?_⟩
  intro X H hX hH hHX
  have hX1 : X1 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hX2' : X2 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have hX3 : X3 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hX
  have hXe' : Xe ≤ X := le_trans (le_trans (le_trans (le_max_left _ _) (le_max_right _ _))
    (le_max_right _ _)) hX
  have hX3' : 3 ≤ X := le_trans (le_trans (le_trans (le_max_right _ _) (le_max_right _ _))
    (le_max_right _ _)) hX
  have hXpos : 0 < X := by linarith
  have hL1 : 1 ≤ Real.log X := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos _) (le_trans (le_of_lt Real.exp_one_lt_d9) (by linarith))
  have hLpos : 0 < Real.log X := by linarith
  set L := Real.log X with hLdef
  set Y := windowY X ε with hYdef
  set P := L ^ B with hPdef
  have hYpos : 0 < Y := Real.rpow_pos_of_pos hXpos _
  let exc2 := fun n : ℕ => InH2 n ∧ K2 * L ^ (-1 : ℝ) * ‖series2 n P‖ <
    ‖partialProduct2 n (sieveLevel X δ') - series2 n P‖
  let excE := fun n : ℕ => X + Y ^ (1 - ε) < (n : ℝ) ∧ InH2 n ∧
    Ke * ‖main2 X Y P n‖ * L ^ (-1 + δ) < |residualCount X Y P n|
  have sub : ∀ n : ℕ, (InH2 n ∧ (Ke + K1 * (1 + K2) / c) * ‖main2 X Y P n‖ * L ^ (-1 + δ) <
      |residualCount X Y P n|) → X < (n : ℝ) → exc2 n ∨ excE n := by
    intro n ⟨hn, hbad⟩ hXn
    have hl : 0 < L ^ (-1 + δ) := Real.rpow_pos_of_pos hLpos _
    have hm : 0 ≤ ‖main2 X Y P n‖ * L ^ (-1 + δ) := by positivity
    by_cases hloc : (n : ℝ) ≤ X + Y ^ (1 - ε)
    · left
      refine ⟨hn, ?_⟩
      by_contra hgood
      have hgood' : ‖partialProduct2 n (sieveLevel X δ') - series2 n P‖ ≤
          K2 * L ^ (-1 : ℝ) * ‖series2 n P‖ := le_of_not_gt hgood
      have hLinv : L ^ (-1 : ℝ) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos hL1 (by norm_num)
      have hLinv0 : 0 ≤ L ^ (-1 : ℝ) := Real.rpow_nonneg hLpos.le _
      have hprod := norm_le_of_rel_close hK2 hLinv0 hLinv hgood'
      have hres := h1 X hX1 n hn hXn hloc
      have hr2 := h3 X hX3 n hXn hloc
      have hnorm : ‖main2 X Y P n‖ = |integerMain X Y n| * ‖series2 n P‖ := by
        simp only [main2, norm_mul, Complex.norm_real, Real.norm_eq_abs]
      have hexp : L ^ (-2 : ℝ) * L ^ (-1 + δ) = L ^ (-3 + δ) := by
        rw [← Real.rpow_add hLpos]; ring_nf
      have hmono : L ^ (-3 + δ') ≤ L ^ (-3 + δ) :=
        Real.rpow_le_rpow_of_exponent_le hL1 (by linarith)
      have hcore := residual_compare_core hK1 hK2 hc hKe (norm_nonneg (series2 n P))
        (Real.rpow_pos_of_pos hYpos (1 / 2 : ℝ)) (Real.rpow_pos_of_pos hLpos (-2 : ℝ)) hl
        (Real.rpow_nonneg hLpos.le (-3 + δ')) hexp hmono hres hprod
        (hr2.trans (le_abs_self _))
      rw [hnorm] at hbad
      exact absurd hcore (not_le.mpr hbad)
    · right
      refine ⟨lt_of_not_ge hloc, hn, ?_⟩
      have hKK : 0 ≤ K1 * (1 + K2) / c := by positivity
      have : Ke * ‖main2 X Y P n‖ * L ^ (-1 + δ) ≤
          (Ke + K1 * (1 + K2) / c) * ‖main2 X Y P n‖ * L ^ (-1 + δ) := by
        nlinarith
      linarith
  have hcnt : cntIoc (fun n => InH2 n ∧ (Ke + K1 * (1 + K2) / c) * ‖main2 X Y P n‖ *
      L ^ (-1 + δ) < |residualCount X Y P n|) X H ≤ cntIoc exc2 X H + cntIoc excE X H := by
    refine le_trans ?_ (U1534.cnt_or_le exc2 excE X H)
    unfold cntIoc
    apply Finset.card_le_card
    intro n
    simp only [Finset.mem_filter]
    rintro ⟨hn1, hXn, hS⟩
    exact ⟨hn1, hXn, sub n hS hXn⟩
  have hcntR : (cntIoc (fun n => InH2 n ∧ (Ke + K1 * (1 + K2) / c) * ‖main2 X Y P n‖ *
      L ^ (-1 + δ) < |residualCount X Y P n|) X H : ℝ) ≤
      (cntIoc exc2 X H : ℝ) + (cntIoc excE X H : ℝ) := by exact_mod_cast hcnt
  have hb2 := h2 X H hX2' hH hHX
  have hbe := hext X H hXe' hH hHX
  calc _ ≤ (cntIoc exc2 X H : ℝ) + (cntIoc excE X H : ℝ) := hcntR
    _ ≤ C2 * H / L ^ A + Ce * H / L ^ A := add_le_add hb2 hbe
    _ = (C2 + Ce) * H / L ^ A := by ring

/-- LEAF. Page 16 eq. 55 to eq. 9. The logarithm is absorbed by any positive
power of L. This statement only uses real analysis. -/
theorem log_absorption (δ : ℝ) (hδ : 0 < δ) :
    ∃ L0 : ℝ, 1 ≤ L0 ∧ ∀ L : ℝ, L0 ≤ L →
      L ^ (-1 : ℝ) * Real.log L ≤ L ^ (-1 + δ) := by
  obtain ⟨L0, hL⟩ := Filter.eventually_atTop.mp ((isLittleO_log_rpow_atTop hδ).bound zero_lt_one)
  refine ⟨max L0 1, le_max_right _ _, ?_⟩
  intro L h
  have hL1 : 1 ≤ L := le_trans (le_max_right _ _) h
  have hLp : 0 < L := by linarith
  have hb : Real.log L ≤ L ^ δ := by
    have hb := hL L (le_trans (le_max_left _ _) h)
    simpa [Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hL1),
      abs_of_pos (Real.rpow_pos_of_pos hLp _)] using hb
  calc L ^ (-1 : ℝ) * Real.log L ≤ L ^ (-1 : ℝ) * L ^ δ :=
      mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg hLp.le _)
    _ = L ^ (-1 + δ) := (Real.rpow_add hLp _ _).symm

/-- LEAF. Page 16 eq. 55 and Proposition 2. Triangle inequality combines the
circle method error and the residual. -/
theorem combine_errors {R V G : ℂ} {a b : ℝ}
    (hV : ‖V - G‖ ≤ a) (hR : ‖V - R‖ ≤ b) : ‖R - G‖ ≤ a + b := by
  calc ‖R - G‖ ≤ ‖R - V‖ + ‖V - G‖ := norm_sub_le_norm_sub_add_norm_sub R V G
    _ = ‖V - R‖ + ‖V - G‖ := by rw [norm_sub_rev R V]
    _ ≤ b + a := add_le_add hR hV
    _ = a + b := add_comm _ _

/-- Theorem 1 assembled from the analytic leaves and the elementary error bounds.
The assembly has no sorry of its own. Its analytic inputs remain CITED. -/
theorem thm1_from_leaves : kumchev_liu_thm1 := by
  intro A hA
  obtain ⟨Bc, hBc, hc⟩ := circle_input A hA
  obtain ⟨Br, hBr, hr⟩ := residual_input A hA
  let B := max Bc Br
  refine ⟨B, lt_of_lt_of_le hBc (le_max_left _ _), ?_⟩
  intro δ ε hδ hε
  obtain ⟨Cc, Kc, Xc, hCc, hKc, hXc, hc⟩ := hc B (le_max_left _ _) ε hε
  obtain ⟨Cr, Kr, Xr, hCr, hKr, hXr, hr⟩ := hr B (le_max_right _ _) δ ε hδ hε
  obtain ⟨L0, hL0, hL⟩ := log_absorption δ hδ
  refine ⟨Cc + Cr, Kc + Kr, max (max Xc Xr) (Real.exp L0),
    by positivity, by positivity, le_trans hXc (le_trans (le_max_left _ _) (le_max_left _ _)), ?_⟩
  intro X H hX hH hHX
  have hXc' : Xc ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hX
  have hXr' : Xr ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hX
  have he : Real.exp L0 ≤ X := le_trans (le_max_right _ _) hX
  have hXp : 0 < X := lt_of_lt_of_le (Real.exp_pos _) he
  have hlog : L0 ≤ Real.log X := by
    rw [← Real.log_exp L0]
    exact Real.log_le_log (Real.exp_pos _) he
  let Y := windowY X ε
  let P := Real.log X ^ B
  let badc := fun n => InH2 n ∧ Kc * ‖main2 X Y P n‖ *
    (Real.log X ^ (-1 : ℝ) * Real.log (Real.log X)) <
    ‖(roughCount X Y P n : ℂ) - main2 X Y P n‖
  let badr := fun n => InH2 n ∧ Kr * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) <
    |residualCount X Y P n|
  have sub : ∀ n, (InH2 n ∧ (Kc + Kr) * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) <
      ‖(primeCount X Y n : ℂ) - main2 X Y P n‖) → badc n ∨ badr n := by
    intro n ⟨hn, hbad⟩
    by_contra h
    have hgood := not_or.mp h
    have hcv : ‖(roughCount X Y P n : ℂ) - main2 X Y P n‖ ≤
        Kc * ‖main2 X Y P n‖ * (Real.log X ^ (-1 : ℝ) * Real.log (Real.log X)) := by
      exact le_of_not_gt (fun hh => hgood.1 ⟨hn, hh⟩)
    have hrv : |residualCount X Y P n| ≤
        Kr * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) := by
      exact le_of_not_gt (fun hh => hgood.2 ⟨hn, hh⟩)
    have hcv' : ‖(roughCount X Y P n : ℂ) - main2 X Y P n‖ ≤
        Kc * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) :=
      hcv.trans (mul_le_mul_of_nonneg_left (hL _ hlog) (by positivity))
    have hrv' : ‖(roughCount X Y P n : ℂ) - (primeCount X Y n : ℂ)‖ ≤
        Kr * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) := by
      have heq : (roughCount X Y P n : ℂ) - (primeCount X Y n : ℂ) =
          (residualCount X Y P n : ℂ) := by
        simp only [residualCount, Complex.ofReal_sub, Complex.ofReal_natCast]
      rw [heq, Complex.norm_real, Real.norm_eq_abs]
      exact hrv
    have hcombined := combine_errors hcv' hrv'
    have heq : Kc * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) +
        Kr * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) =
        (Kc + Kr) * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) := by ring
    rw [heq] at hcombined
    exact (not_lt_of_ge hcombined) hbad
  have hcount := le_trans (U1534.cnt_mono sub X H) (U1534.cnt_or_le badc badr X H)
  have hcountR : (cntIoc (fun n => InH2 n ∧
      (Kc + Kr) * ‖main2 X Y P n‖ * Real.log X ^ (-1 + δ) <
      ‖(primeCount X Y n : ℂ) - main2 X Y P n‖) X H : ℝ) ≤
      (cntIoc badc X H : ℝ) + (cntIoc badr X H : ℝ) := by exact_mod_cast hcount
  have hcb := hc X H hXc' hH hHX
  have hrb := hr X H hXr' hH hHX
  calc _ ≤ (cntIoc badc X H : ℝ) + (cntIoc badr X H : ℝ) := hcountR
    _ ≤ Cc * H / Real.log X ^ A + Cr * H / Real.log X ^ A := add_le_add hcb hrb
    _ = (Cc + Cr) * H / Real.log X ^ A := by ring

/-- Page 2 displays 4 to 6. No window pair can reach n at least X + Y. -/
theorem windowPairs_empty_above (X Y : ℝ) (hY : 0 ≤ Y) (n : ℕ)
    (hn : X + Y ≤ (n : ℝ)) : windowPairs X Y n = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨_, hlo, hhi, hqlo, hqhi, heq⟩ := Finset.mem_filter.mp hv
  have hq2 : (v.2 : ℝ) ^ 2 ≤ Y := by
    have hsq := (sq_le_sq₀ (Nat.cast_nonneg v.2) (Real.sqrt_nonneg Y)).mpr hqhi.le
    nlinarith only [hsq, Real.sq_sqrt hY]
  have hcast : (v.1 : ℝ) + (v.2 : ℝ)^2 = (n : ℝ) := by exact_mod_cast heq
  linarith

/-- Page 2 displays 4 to 6 and page 8 display 35. The counts and main term
vanish beyond the support of the fixed representation windows. -/
theorem counts_vanish_above (X Y P : ℝ) (hY : 0 ≤ Y) (n : ℕ) (hn : X + Y ≤ (n : ℝ)) :
    primeCount X Y n = 0 ∧ roughCount X Y P n = 0 ∧
      main2 X Y P n = 0 ∧ residualCount X Y P n = 0 := by
  simp [primeCount, roughCount, main2, integerMain, residualCount,
    windowPairs_empty_above X Y hY n hn]

/-- Page 8 display 35. Every prime pair is counted by the sifted count
when the cutoff is below the lower endpoint of I2, so the residual is nonnegative. -/
theorem residualCount_nonneg (X Y P : ℝ) (n : ℕ)
    (hcut : Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ Real.sqrt Y / 2) :
    0 ≤ residualCount X Y P n := by
  classical
  have hsub : (windowPairs X Y n).filter (fun v => v.1.Prime ∧ v.2.Prime) ⊆
      (windowPairs X Y n).filter (fun v => v.1.Prime ∧
        ∀ p : ℕ, p.Prime → p ∣ v.2 → Y ^ (1 / 4 : ℝ) * P ^ (-2 : ℤ) ≤ (p : ℝ)) := by
    intro v hv
    obtain ⟨hv, hp, hq⟩ := Finset.mem_filter.mp hv
    refine Finset.mem_filter.mpr ⟨hv, hp, ?_⟩
    intro p hp hdiv
    have heq : p = v.2 := (Nat.prime_dvd_prime_iff_eq hp hq).mp hdiv
    rw [heq]
    exact hcut.trans (Finset.mem_filter.mp hv).2.2.2.1
  unfold residualCount
  apply sub_nonneg.mpr
  exact_mod_cast Finset.card_le_card hsub

/-- Page 2 before display 4 and Theorem 1. The nonempty interval range
forces Y below X, which justifies natural integer indices in the windows. -/
theorem windowY_lt_of_range {X H ε : ℝ} (hX : 1 < X)
    (hH : X ^ (7 / 18 + ε) ≤ H) (hHX : H ≤ X) : windowY X ε < X := by
  have hexp : 7 / 18 + ε ≤ 1 :=
    (Real.rpow_le_rpow_left_iff hX).mp (by simpa only [Real.rpow_one] using hH.trans hHX)
  have htheta : 7 / 12 + ε / 2 < 1 := by linarith
  simpa only [windowY, Real.rpow_one] using Real.rpow_lt_rpow_of_exponent_lt hX htheta

end LeanLab.KumchevLiu2007.Task129
