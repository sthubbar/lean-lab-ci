import LeanLab.Halupczok2012.Decomp598Theorem6LeavesKawadaS136Major
import LeanLab.Halupczok2012.Decomp329e

/-!
S136 round 2 split of `leaf_major_sigma_zero` of `Decomp598Theorem6LeavesKawadaS136Major`,
Kawada 1993 section 3, first paragraph, for `k = 2`. https://doi.org/10.5802/jtnb.839

Kawada proves the case `σ(b;a,q) = 0` for the count itself, not for the major arc integral.
So the major arc integral is recovered as the full circle integral, which is the count by
`leaf_circle_identity`, minus the minor arc integral, bounded by `leaf_minor_arcs`. The one
new leaf is the count bound `leaf_sigma_zero_count`. The assembly
`leaf_major_sigma_zero_of_leaves` has the statement of `leaf_major_sigma_zero` byte for byte;
it is CONDITIONAL ON the existing leaves `leaf_circle_identity` and `leaf_minor_arcs`.

AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp598Theorem6LeavesKawadaS136bSigmaZero

open Finset MeasureTheory
open scoped Classical
open LeanLab.Halupczok2012 LeanLab.Halupczok2012.Decomp598Theorem6LeavesKawada

/-- Kawada section 3 first paragraph, case `(a2, q2) > 1`: no prime `p2 > X2 ≥ q2` is
`≡ a2 (q2)`, so the count vanishes. -/
theorem binSumAP_eq_zero_of_gcd (X2 Y : ℝ) (q2 : ℕ) (a2 : ℤ) (m : ℕ)
    (hq1 : 1 ≤ q2) (hq : (q2 : ℝ) ≤ X2) (hg : Int.gcd a2 q2 ≠ 1) :
    binSumAP X2 Y q2 a2 m = 0 := by
  unfold binSumAP
  refine sum_eq_zero fun p hp => ?_
  exfalso
  obtain ⟨-, hpp, -, hXp, -, hmod⟩ := mem_filter.mp hp
  have hlt : q2 < p := by exact_mod_cast lt_of_le_of_lt hq hXp
  have hnd : ¬ p ∣ q2 := fun h => absurd (Nat.le_of_dvd hq1 h) (not_le.mpr hlt)
  have hcop : IsCoprime (p : ℤ) (q2 : ℤ) :=
    Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hpp).mpr hnd)
  obtain ⟨t, ht⟩ := hmod.dvd
  have ha : a2 = (p : ℤ) + (q2 : ℤ) * t := by linarith
  have : IsCoprime a2 (q2 : ℤ) := by
    rw [ha]; exact hcop.add_mul_left_left t
  exact hg (Int.isCoprime_iff_gcd_eq_one.mp this)

/-- Kawada section 3 first paragraph, case `(a2 - m, q2) > 1`: every `p3 = m - p2` divides
`q2`, so the count is at most `d(q2) (log m)^2`. -/
theorem binSumAP_le_of_gcd_sub (X2 Y : ℝ) (q2 : ℕ) (a2 : ℤ) (m : ℕ)
    (hq1 : 1 ≤ q2) (hg : Int.gcd (a2 - m) q2 ≠ 1) :
    binSumAP X2 Y q2 a2 m ≤ (q2.divisors.card : ℝ) * Real.log m ^ 2 := by
  unfold binSumAP
  set s := (range (m + 1)).filter (fun p => p.Prime ∧ (m - p).Prime ∧ X2 < p ∧
    (p : ℝ) ≤ X2 + Y ∧ (p : ℤ) ≡ a2 [ZMOD q2]) with hs
  have hdiv : ∀ p ∈ s, (m - p) ∣ q2 := by
    intro p hp
    obtain ⟨hpm, -, hp3, -, -, hmod⟩ := mem_filter.mp hp
    have hpm' : p ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hpm)
    by_contra hnd
    have hcop : IsCoprime ((m - p : ℕ) : ℤ) (q2 : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr ((Nat.Prime.coprime_iff_not_dvd hp3).mpr hnd)
    obtain ⟨t, ht⟩ := hmod.dvd
    have ha : a2 - m = -((m - p : ℕ) : ℤ) + (q2 : ℤ) * t := by
      push_cast [hpm']; linarith
    have : IsCoprime (a2 - m) (q2 : ℤ) := by
      rw [ha]; exact hcop.neg_left.add_mul_left_left t
    exact hg (Int.isCoprime_iff_gcd_eq_one.mp this)
  have hcard : s.card ≤ q2.divisors.card := by
    refine card_le_card_of_injOn (fun p => m - p) (fun p hp => ?_) ?_
    · exact Nat.mem_divisors.mpr ⟨hdiv p hp, by omega⟩
    · intro p hp p' hp' h
      have h1 := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp).1)
      have h2 := Nat.lt_succ_iff.mp (mem_range.mp (mem_filter.mp hp').1)
      simp only at h
      omega
  have hterm : ∀ p ∈ s, Real.log p * Real.log ((m - p : ℕ) : ℝ) ≤ Real.log m ^ 2 := by
    intro p hp
    obtain ⟨hpm, hp2, hp3, -⟩ := mem_filter.mp hp
    have hpm' : p ≤ m := Nat.lt_succ_iff.mp (mem_range.mp hpm)
    have l1 : 0 ≤ Real.log p := Real.log_natCast_nonneg p
    have l2 : 0 ≤ Real.log ((m - p : ℕ) : ℝ) := Real.log_natCast_nonneg _
    have u1 : Real.log p ≤ Real.log m :=
      Real.log_le_log (by exact_mod_cast hp2.pos) (by exact_mod_cast hpm')
    have u2 : Real.log ((m - p : ℕ) : ℝ) ≤ Real.log m :=
      Real.log_le_log (by exact_mod_cast hp3.pos) (by exact_mod_cast Nat.sub_le m p)
    rw [sq]; exact mul_le_mul u1 u2 l2 (l1.trans u1)
  calc _ ≤ ∑ p ∈ s, Real.log m ^ 2 := sum_le_sum hterm
    _ = s.card * Real.log m ^ 2 := by rw [sum_const, nsmul_eq_mul]
    _ ≤ _ := mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (sq_nonneg _)


/-- `Sqa (2k) q2 a2 = 0` forces one of the two gcd cases, since `S` of an even number is
positive by `twinC_pos`. -/
theorem sqa_zero_cases (k q2 : ℕ) (a2 : ℤ) (hq : 1 ≤ q2) (h : Sqa (2 * k) q2 a2 = 0) :
    Int.gcd a2 q2 ≠ 1 ∨ Int.gcd (a2 - ((2 * k : ℕ) : ℤ)) q2 ≠ 1 := by
  by_contra hc
  push_neg at hc
  unfold Sqa at h
  have hev : Even (2 * k * q2) := (even_two_mul k).mul_right q2
  rw [if_pos ⟨even_two_mul k, hc.1, hc.2⟩] at h
  have hS : 0 < S (2 * k * q2) := by
    unfold S
    rw [if_pos hev]
    have := LeanLab.Halupczok2012.Decomp329e.twinC_pos
    refine mul_pos (by positivity) (prod_pos fun p hp => ?_)
    obtain ⟨hp1, hp2⟩ := mem_filter.mp hp
    have hpp := Nat.prime_of_mem_primeFactors hp1
    have h3 : (3 : ℝ) ≤ p := by
      have := hpp.two_le
      exact_mod_cast (show 3 ≤ p by omega)
    exact div_pos (by linarith) (by linarith)
  have htot : (0 : ℝ) < Nat.totient q2 := by exact_mod_cast Nat.totient_pos.mpr hq
  exact (div_pos hS htot).ne' h

theorem binSumAP_nonneg (X2 Y : ℝ) (q2 : ℕ) (a2 : ℤ) (m : ℕ) : 0 ≤ binSumAP X2 Y q2 a2 m := by
  unfold binSumAP
  exact sum_nonneg fun p _ => mul_nonneg (Real.log_natCast_nonneg _) (Real.log_natCast_nonneg _)

theorem kRange_card_le (X Y : ℝ) (hX : 0 ≤ X) (hY : 0 ≤ Y) :
    ((kRange X Y).card : ℝ) ≤ Y + 1 := by
  have hsub : kRange X Y ⊆ Ioc ⌊X⌋₊ ⌊X + Y⌋₊ := by
    intro k hk
    obtain ⟨-, h1, h2⟩ := mem_filter.mp hk
    exact mem_Ioc.mpr ⟨(Nat.floor_lt hX).mpr h1, Nat.le_floor h2⟩
  have hle : ⌊X⌋₊ ≤ ⌊X + Y⌋₊ := Nat.floor_le_floor (by linarith)
  have h1 := card_le_card hsub
  rw [Nat.card_Ioc] at h1
  have h2 : ((kRange X Y).card : ℝ) ≤ ((⌊X + Y⌋₊ - ⌊X⌋₊ : ℕ) : ℝ) := by exact_mod_cast h1
  rw [Nat.cast_sub hle] at h2
  have h3 : (⌊X + Y⌋₊ : ℝ) ≤ X + Y := Nat.floor_le (by linarith)
  have h4 : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
  linarith

/-- LEAF: Kawada 1993 section 3, first paragraph, for k = 2: when `Sqa (2k) q2 a2 = 0`,
either `(a2, q2) > 1` and no prime `p2 > X2 ≥ q2` is `≡ a2 (q2)`, or `(2k - a2, q2) > 1` and
`p3 = 2k - p2` divides `q2`, so each count is `≪ ω(q2) L^2`; summed over `k` and
`q2 ≤ Q2 ≪ Y X2^{-1/2}` this is `≪ Y^{3/2} L^3`. Class MEDIUM. -/
theorem leaf_sigma_zero_count :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ B : ℝ, 0 < B ∧
    ∀ c1 c3 : ℝ, 0 < c1 → 0 < c3 → ∀ a2 : ℤ, ∃ K Y0 : ℝ,
    ∀ X1 X2 Y Q2 : ℝ, Y0 ≤ Y → c1 * X1 ^ (2 / 3 + ε) ≤ Y →
      Y ≤ X1 → Y ≤ X2 → X2 ≤ 2 * X1 - Y →
      1 ≤ Q2 → Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-B) →
      ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ (kRange X1 Y).filter (fun k => Sqa (2 * k) q2 a2 = 0),
        |binSumAP X2 Y q2 a2 (2 * k)| ≤ K * Y ^ 2 * Real.log Y ^ (-A) := by
  intro A ε hA hε
  refine ⟨A + 3, by linarith, fun c1 c3 hc1 hc3 a2 => ?_⟩
  refine ⟨18 * c3 ^ 2, max (max (c3 ^ 2) 1) (Real.exp (1 + |Real.log c1|)), ?_⟩
  intro X1 X2 Y Q2 hY0 h1 h2 h3 h4 hQ1 hQ2
  have hYc : c3 ^ 2 ≤ Y := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY0
  have hY1 : 1 ≤ Y := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY0
  have hYe : Real.exp (1 + |Real.log c1|) ≤ Y := le_trans (le_max_right _ _) hY0
  have hYpos : 0 < Y := by linarith
  set L := Real.log Y with hLdef
  have hLe : 1 + |Real.log c1| ≤ L := by
    rw [← Real.log_exp (1 + |Real.log c1|)]
    exact Real.log_le_log (Real.exp_pos _) hYe
  have hL : 1 ≤ L := by have := abs_nonneg (Real.log c1); linarith
  have hLpos : 0 < L := by linarith
  have hX2 : 0 < X2 := by linarith
  have hX1 : 1 ≤ X1 := by linarith
  set s := X2 ^ (-(1 / 2) : ℝ) with hsdef
  have hs0 : 0 < s := Real.rpow_pos_of_pos hX2 _
  have hs2 : s ^ 2 * X2 = 1 := by
    rw [hsdef, ← Real.rpow_natCast, ← Real.rpow_mul hX2.le]
    norm_num
    rw [Real.rpow_neg_one]; field_simp
  set T := L ^ (-(A + 3)) with hTdef
  have hT0 : 0 < T := Real.rpow_pos_of_pos hLpos _
  have hT1 : T ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hL (by linarith)
  have hQ2' : Q2 ≤ c3 * Y * s * T := hQ2
  -- q2 ≤ X2
  have hqX : ∀ q2 ∈ Icc 1 ⌊Q2⌋₊, (q2 : ℝ) ≤ X2 := by
    intro q2 hq
    have hqQ : (q2 : ℝ) ≤ Q2 := (Nat.cast_le.mpr (mem_Icc.mp hq).2).trans (Nat.floor_le (by linarith))
    have hA : c3 * Y * s * T ≤ c3 * X2 * s := by
      have : c3 * Y * s * T ≤ c3 * Y * s := by
        have : 0 ≤ c3 * Y * s := by positivity
        nlinarith
      refine this.trans ?_
      have := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h3 hc3.le) hs0.le
      linarith
    have hB : c3 * X2 * s ≤ X2 := by
      have hsq : (c3 * X2 * s) ^ 2 ≤ X2 ^ 2 := by
        have : (c3 * X2 * s) ^ 2 = c3 ^ 2 * X2 * (s ^ 2 * X2) := by ring
        rw [this, hs2]; nlinarith
      exact (pow_le_pow_iff_left₀ (by positivity) hX2.le two_ne_zero).mp hsq
    linarith
  -- log bound
  have hlogX1 : Real.log (4 * X1) ≤ 3 * L := by
    have hc := Real.log_le_log (by positivity) h1
    rw [Real.log_mul hc1.ne' (by positivity), Real.log_rpow (by linarith)] at hc
    have hl1 : 0 ≤ Real.log X1 := Real.log_nonneg hX1
    have hab := neg_abs_le (Real.log c1)
    have hl4 : Real.log 4 < 3 / 2 := by
      have : Real.log 4 = 2 * Real.log 2 := by
        rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
      have := Real.log_two_lt_d9; linarith
    rw [Real.log_mul (by norm_num) (by linarith)]
    nlinarith
  have hterm : ∀ q2 ∈ Icc 1 ⌊Q2⌋₊, ∀ k ∈ kRange X1 Y,
      |binSumAP X2 Y q2 a2 (2 * k)| * (if Sqa (2 * k) q2 a2 = 0 then 1 else 0) ≤
        (q2 : ℝ) * (9 * L ^ 2) := by
    intro q2 hq k hk
    have hq1 : 1 ≤ q2 := (mem_Icc.mp hq).1
    have hqpos : (0 : ℝ) ≤ q2 := Nat.cast_nonneg _
    split_ifs with hz
    · rw [mul_one, abs_of_nonneg (binSumAP_nonneg _ _ _ _ _)]
      obtain ⟨-, hk1, hk2⟩ := mem_filter.mp hk
      have hk0 : (1 : ℝ) ≤ ((2 * k : ℕ) : ℝ) := by
        push_cast; have : (1 : ℝ) ≤ k := by
          have : (0 : ℕ) < k := by exact_mod_cast (show (0 : ℝ) < k by linarith)
          exact_mod_cast this
        linarith
      have hlk : Real.log ((2 * k : ℕ) : ℝ) ≤ 3 * L := by
        refine le_trans (Real.log_le_log (by linarith) ?_) hlogX1
        push_cast; linarith
      have hlk0 : 0 ≤ Real.log ((2 * k : ℕ) : ℝ) := Real.log_nonneg hk0
      have hsq : Real.log ((2 * k : ℕ) : ℝ) ^ 2 ≤ 9 * L ^ 2 := by nlinarith
      rcases sqa_zero_cases k q2 a2 hq1 hz with hg | hg
      · rw [binSumAP_eq_zero_of_gcd X2 Y q2 a2 _ hq1 (hqX q2 hq) hg]
        positivity
      · refine (binSumAP_le_of_gcd_sub X2 Y q2 a2 (2 * k) hq1 hg).trans ?_
        have hd : (q2.divisors.card : ℝ) ≤ q2 := by exact_mod_cast Nat.card_divisors_le_self q2
        exact mul_le_mul hd hsq (sq_nonneg _) hqpos
    · rw [mul_zero]; positivity
  have hcard := kRange_card_le X1 Y (by linarith) hYpos.le
  have hsumq : ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, (q2 : ℝ) ≤ Q2 ^ 2 := by
    have hn : (⌊Q2⌋₊ : ℝ) ≤ Q2 := Nat.floor_le (by linarith)
    calc ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, (q2 : ℝ) ≤ ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, (⌊Q2⌋₊ : ℝ) :=
          sum_le_sum fun q2 hq => Nat.cast_le.mpr (mem_Icc.mp hq).2
      _ = (Icc 1 ⌊Q2⌋₊).card * (⌊Q2⌋₊ : ℝ) := by rw [sum_const, nsmul_eq_mul]
      _ ≤ (⌊Q2⌋₊ : ℝ) * ⌊Q2⌋₊ := by
          rw [Nat.card_Icc]; gcongr; simp
      _ ≤ Q2 ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) ⌊Q2⌋₊]
  have hQsq : Q2 ^ 2 ≤ c3 ^ 2 * Y ^ 2 * s ^ 2 * T ^ 2 := by
    have : Q2 ^ 2 ≤ (c3 * Y * s * T) ^ 2 := pow_le_pow_left₀ (by linarith) hQ2' 2
    linarith [show (c3 * Y * s * T) ^ 2 = c3 ^ 2 * Y ^ 2 * s ^ 2 * T ^ 2 by ring]
  have hTL : T ^ 2 * L ^ 2 ≤ L ^ (-A) := by
    rw [hTdef, ← Real.rpow_natCast, ← Real.rpow_natCast L 2, ← Real.rpow_mul hLpos.le,
      ← Real.rpow_add hLpos]
    exact Real.rpow_le_rpow_of_exponent_le hL (by push_cast; linarith)
  have hYs : Y * s ^ 2 ≤ 1 := by
    rw [← hs2]; nlinarith [sq_nonneg s]
  calc _ = ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ kRange X1 Y,
        |binSumAP X2 Y q2 a2 (2 * k)| * (if Sqa (2 * k) q2 a2 = 0 then 1 else 0) := by
        refine sum_congr rfl fun q2 _ => ?_
        rw [sum_filter]; refine sum_congr rfl fun k _ => ?_
        split_ifs <;> simp
    _ ≤ ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ kRange X1 Y, (q2 : ℝ) * (9 * L ^ 2) :=
        sum_le_sum fun q2 hq => sum_le_sum fun k hk => hterm q2 hq k hk
    _ = (∑ q2 ∈ Icc 1 ⌊Q2⌋₊, (q2 : ℝ)) * ((kRange X1 Y).card * (9 * L ^ 2)) := by
        rw [sum_mul]; refine sum_congr rfl fun q2 _ => ?_
        rw [sum_const, nsmul_eq_mul]; ring
    _ ≤ (c3 ^ 2 * Y ^ 2 * s ^ 2 * T ^ 2) * ((2 * Y) * (9 * L ^ 2)) := by
        apply mul_le_mul (hsumq.trans hQsq) _ (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    _ = 18 * c3 ^ 2 * Y ^ 2 * (Y * s ^ 2) * (T ^ 2 * L ^ 2) := by ring
    _ ≤ 18 * c3 ^ 2 * Y ^ 2 * 1 * L ^ (-A) := by
        have h0 : 0 ≤ T ^ 2 * L ^ 2 := by positivity
        have h5 : 0 ≤ 18 * c3 ^ 2 * Y ^ 2 := by positivity
        exact mul_le_mul (mul_le_mul_of_nonneg_left hYs h5) hTL h0 (by positivity)
    _ = _ := by ring

/-- Assembly: `leaf_major_sigma_zero` from `leaf_sigma_zero_count`, `leaf_circle_identity`
and `leaf_minor_arcs`. Statement identical to
`Decomp598Theorem6LeavesKawadaS136Major.leaf_major_sigma_zero`. -/
theorem leaf_major_sigma_zero_of_leaves :
    ∀ A ε : ℝ, 0 < A → 0 < ε → ∃ C0 : ℝ, ∀ C : ℝ, C0 ≤ C → ∃ B : ℝ, 0 < B ∧
    ∀ c1 c3 : ℝ, 0 < c1 → 0 < c3 → ∀ a2 : ℤ, ∃ K Y0 : ℝ,
    ∀ X1 X2 Y Q2 : ℝ, Y0 ≤ Y → c1 * X1 ^ (2 / 3 + ε) ≤ Y →
      Y ≤ X1 → Y ≤ X2 → X2 ≤ 2 * X1 - Y →
      1 ≤ Q2 → Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-B) →
      ∑ q2 ∈ Icc 1 ⌊Q2⌋₊, ∑ k ∈ (kRange X1 Y).filter (fun k => Sqa (2 * k) q2 a2 = 0),
        ‖∫ α in unitDom X1 ∩ kMajor A C Y, circF X1 X2 Y q2 a2 (2 * k) α‖ ≤
          K * Y ^ 2 * Real.log Y ^ (-A) := by
  intro A ε hA hε
  obtain ⟨Cm, hm⟩ := leaf_minor_arcs A ε hA hε
  obtain ⟨Bc, hBc, hc⟩ := leaf_sigma_zero_count A ε hA hε
  refine ⟨Cm, fun C hC => ?_⟩
  obtain ⟨Bm, hBm, hm⟩ := hm C hC
  refine ⟨max Bm Bc, lt_max_of_lt_left hBm, fun c1 c3 hc1 hc3 a2 => ?_⟩
  obtain ⟨Km, Ym, hm⟩ := hm c1 c3 hc1 hc3 a2
  obtain ⟨Kc, Yc, hc⟩ := hc c1 c3 hc1 hc3 a2
  refine ⟨Kc + Km, max (max Ym Yc) (Real.exp 1), ?_⟩
  intro X1 X2 Y Q2 hY0 h1 h2 h3 h4 hQ1 hQ2
  have hYe : Real.exp 1 ≤ Y := le_trans (le_max_right _ _) hY0
  have hYpos : 0 < Y := lt_of_lt_of_le (Real.exp_pos 1) hYe
  have hL : 1 ≤ Real.log Y := by
    rw [← Real.log_exp 1]
    exact Real.log_le_log (Real.exp_pos 1) hYe
  have hX2pos : 0 < X2 := lt_of_lt_of_le hYpos h3
  have hbase : 0 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) := by
    have := Real.rpow_pos_of_pos hX2pos (-(1 / 2) : ℝ)
    positivity
  have hQ : ∀ Bi, Bi ≤ max Bm Bc →
      Q2 ≤ c3 * Y * X2 ^ (-(1 / 2) : ℝ) * Real.log Y ^ (-Bi) := fun Bi hBi =>
    hQ2.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le hL (neg_le_neg hBi)) hbase)
  have bm := hm X1 X2 Y Q2 (le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hY0)
    h1 h2 h3 h4 hQ1 (hQ Bm (le_max_left _ _))
  have bc := hc X1 X2 Y Q2 (le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hY0)
    h1 h2 h3 h4 hQ1 (hQ Bc (le_max_right _ _))
  have hpt : ∀ q2 ∈ Icc 1 ⌊Q2⌋₊,
      ∀ k ∈ (kRange X1 Y).filter (fun k => Sqa (2 * k) q2 a2 = 0),
      ‖∫ α in unitDom X1 ∩ kMajor A C Y, circF X1 X2 Y q2 a2 (2 * k) α‖ ≤
        |binSumAP X2 Y q2 a2 (2 * k)| +
        ‖∫ α in unitDom X1 \ kMajor A C Y, circF X1 X2 Y q2 a2 (2 * k) α‖ := by
    intro q2 _ k hk
    have hid := leaf_circle_identity X1 X2 Y q2 a2 k hYpos h4 (mem_filter.mp hk).1
    rw [← circ_split X1 X2 Y q2 a2 (2 * k) (kMajor A C Y) (majorArcs_measurable _ _)] at hid
    have heq : (∫ α in unitDom X1 ∩ kMajor A C Y, circF X1 X2 Y q2 a2 (2 * k) α) =
        ((binSumAP X2 Y q2 a2 (2 * k) : ℝ) : ℂ) -
          ∫ α in unitDom X1 \ kMajor A C Y, circF X1 X2 Y q2 a2 (2 * k) α := by
      rw [hid]; ring
    rw [heq]
    refine (norm_sub_le _ _).trans (le_of_eq ?_)
    rw [Complex.norm_real, Real.norm_eq_abs]
  have hsub : ∀ q2 ∈ Icc 1 ⌊Q2⌋₊,
      ∑ k ∈ (kRange X1 Y).filter (fun k => Sqa (2 * k) q2 a2 = 0),
        ‖∫ α in unitDom X1 \ kMajor A C Y, circF X1 X2 Y q2 a2 (2 * k) α‖ ≤
      ∑ k ∈ kRange X1 Y,
        ‖∫ α in unitDom X1 \ kMajor A C Y, circF X1 X2 Y q2 a2 (2 * k) α‖ :=
    fun q2 _ => sum_le_sum_of_subset_of_nonneg (filter_subset _ _)
      (fun _ _ _ => norm_nonneg _)
  calc
    _ ≤ ∑ q2 ∈ Icc 1 ⌊Q2⌋₊,
        (∑ k ∈ (kRange X1 Y).filter (fun k => Sqa (2 * k) q2 a2 = 0),
          |binSumAP X2 Y q2 a2 (2 * k)| +
        ∑ k ∈ kRange X1 Y,
          ‖∫ α in unitDom X1 \ kMajor A C Y, circF X1 X2 Y q2 a2 (2 * k) α‖) := by
      refine sum_le_sum fun q2 hq => ?_
      refine (sum_le_sum fun k hk => hpt q2 hq k hk).trans ?_
      rw [sum_add_distrib]
      exact add_le_add le_rfl (hsub q2 hq)
    _ = _ + _ := sum_add_distrib
    _ ≤ Kc * Y ^ 2 * Real.log Y ^ (-A) + Km * Y ^ 2 * Real.log Y ^ (-A) := add_le_add bc bm
    _ = _ := by ring

end LeanLab.Halupczok2012.Decomp598Theorem6LeavesKawadaS136bSigmaZero
