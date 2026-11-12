/-
Theorem 1 of Kumchev and Liu, arXiv 0801.0130, page 2.
Decomposition of the end of Section 4, page 16, eq. 55 and Proposition 2.
The analytic leaves remain CITED. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.KumchevLiu2007.Decomp1534a
import LeanLab.KumchevLiu2007.Decomp1534c

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

/-- SPLIT LEAF of residual_input. Proof of Proposition 2, pages 16 and 17,
displays 56, 57, 58 and 59 together with the lower bound in display 48 on page 13.
The upper bound sieve of Lemma 3.7 with D = Y to the 1/9 and z = sieveLevel,
fed by the prime number theorem for N in display 57 and by Bombieri Vinogradov
for the remainders r(d), gives R0(n) at most a constant times
Y to the 1/2 times L to the -3 + delta times P2(n, z), for every n in H2 with
X < n at most X + H and H at most Y to the 1 - epsilon, as written on page 17.
R0 is the difference residualCount by display 35 on page 8. The restriction
epsilon at most 11/18 is the nonempty H range of Theorem 1. CITED. -/
theorem residual_sieve_pointwise (B δ ε : ℝ) (hB : 0 < B) (hδ : 0 < δ) (hδ1 : δ < 1)
    (hε : 0 < ε) (hε1 : ε ≤ 11 / 18) :
    ∃ K1 X1 : ℝ, 0 < K1 ∧ ∀ X : ℝ, X1 ≤ X → ∀ n : ℕ, InH2 n → X < (n : ℝ) →
      (n : ℝ) ≤ X + windowY X ε ^ (1 - ε) →
      |residualCount X (windowY X ε) (Real.log X ^ B) n| ≤
        K1 * windowY X ε ^ (1 / 2 : ℝ) * Real.log X ^ (-3 + δ) *
          ‖partialProduct2 n (sieveLevel X δ)‖ := by
  sorry

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
the full H range of Theorem 1 is covered as written. CITED. -/
theorem product_series_almost_all (A : ℝ) (hA : 0 < A) :
    ∃ B0 : ℝ, 0 < B0 ∧ ∀ B : ℝ, B0 ≤ B → ∀ δ ε : ℝ, 0 < δ → δ < 1 → 0 < ε →
      ∃ C K2 X0 : ℝ, 0 < C ∧ 0 ≤ K2 ∧ 2 ≤ X0 ∧ ∀ X H : ℝ,
        X0 ≤ X → X ^ (7 / 18 + ε) ≤ H → H ≤ X →
        (cntIoc (fun n => InH2 n ∧
          K2 * Real.log X ^ (-1 : ℝ) * ‖series2 n (Real.log X ^ B)‖ <
          ‖partialProduct2 n (sieveLevel X δ) - series2 n (Real.log X ^ B)‖) X H : ℝ) ≤
          C * H / Real.log X ^ A := by
  sorry

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
