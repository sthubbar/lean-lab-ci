/-
AI-written Lean code, Claude, 2026-10-21, cloud session 20261021T0217Z-cloud56, unit U-6819.
Links MertensRS320 to the P0048 chain: the lab's cited `RSRecipRed.RS320` now follows from the
cited Dusart 2010 θ bound `DusartThm52k2` and the numeric input `MertensRS320.BLe`,
`B ≤ 0.26150` for the Meissel-Mertens constant `B` defined as a limit. KNOWN mathematics.
Goldbach is open.
-/
import LeanLab.AlmostPrimes.RSRecip
import LeanLab.AlmostPrimes.MertensRS320

open LeanLab.AlmostPrimes LeanLab.AlmostPrimes.DDMain LeanLab.Common.ThetaWindow

namespace LeanLab.AlmostPrimes.MertensRS320

/-- **`RS320` discharged to `DusartThm52k2` and `BLe`**. CONDITIONAL ON both. -/
theorem RS320_of_dusart (hD : DusartThm52k2) (hB : BLe) : RSRecipRed.RS320 :=
  RS320_form hD hB

/-- Dudek-Dunn's `RSRecip`, CONDITIONAL ON `DusartThm52k2` and `BLe`. -/
theorem RSRecip_of_dusart (hD : DusartThm52k2) (hB : BLe) : RSRecip :=
  RSRecipRed.RSRecip_of_RS320 (RS320_of_dusart hD hB)

/-- **Theorem 3.3 for `N ≥ 10^200`**, Dudek-Dunn. CONDITIONAL ON `RSHyp`, `DusartThm52k2`,
`BLe`, `SelbergThm13`. -/
theorem theorem3_3_large_of_dusart (hRS : DDLemma21All.RSHyp) (hD : DusartThm52k2) (hB : BLe)
    (hSel : SelbergThm13) (N : ℕ) (hN : (10 : ℝ) ^ 200 ≤ N) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ N = a + b ∧
      (Even N → bigOmega (a * b) ≤ 39) ∧ bigOmega (a * b) ≤ 40 :=
  RSRecipRed.theorem3_3_large_of_RS2 hRS (RS320_of_dusart hD hB) hSel N hN

open Real Finset in
/-- `primesIn w z ⊆ (w - 1, z]`, so its reciprocal sum is at most `S z - S (w - 1)`. -/
theorem primesIn_le_S {w z : ℝ} (hw : 1 ≤ w) (hwz : w < z) :
    ∑ p ∈ DDLemma21.primesIn w z, (1 : ℝ) / p ≤ S z - S (w - 1) := by
  have hBA : (range (⌊w - 1⌋₊ + 1)).filter Nat.Prime ⊆ (range (⌊z⌋₊ + 1)).filter Nat.Prime := by
    intro p hp
    simp only [mem_filter, mem_range] at hp ⊢
    refine ⟨?_, hp.2⟩
    have : ⌊w - 1⌋₊ ≤ ⌊z⌋₊ := Nat.floor_le_floor (by linarith)
    omega
  have hsub : DDLemma21.primesIn w z ⊆
      (range (⌊z⌋₊ + 1)).filter Nat.Prime \ (range (⌊w - 1⌋₊ + 1)).filter Nat.Prime := by
    intro p hp
    simp only [DDLemma21.primesIn, mem_filter, mem_range] at hp
    simp only [mem_sdiff, mem_filter, mem_range, not_and]
    refine ⟨⟨?_, hp.2.1⟩, fun hlt _ => ?_⟩
    · have : p ≤ ⌊z⌋₊ := Nat.le_floor hp.2.2.2.le
      omega
    · have h1 : p ≤ ⌊w - 1⌋₊ := by omega
      have h2 : (p : ℝ) ≤ w - 1 := (Nat.le_floor_iff (by linarith)).1 h1
      linarith [hp.2.2.1]
  have hle := sum_le_sum_of_subset_of_nonneg hsub (fun p _ _ => by positivity)
    (f := fun p : ℕ => (1 : ℝ) / p)
  have hsd := sum_sdiff hBA (f := fun p : ℕ => (1 : ℝ) / p)
  unfold S
  linarith

open Real in
/-- **Rosser-Schoenfeld Theorem 5 in the `RSHyp` form, for `w ≥ 10^10 + 1`**.
CONDITIONAL ON `DusartThm52k2` only. -/
theorem RSHyp_high (hD : DusartThm52k2) {w z : ℝ} (hw : 10 ^ 10 + 1 ≤ w) (hwz : w < z) :
    2 * ∑ p ∈ DDLemma21.primesIn w z, (1 : ℝ) / p ≤
      2 * log (log z / log w) + 1 / (log z) ^ 2 + 1 / (log w) ^ 2 := by
  set a := w - 1 with hadef
  have ha : (10 : ℝ) ^ 10 ≤ a := by rw [hadef]; linarith
  have hz : (10 : ℝ) ^ 10 ≤ z := by linarith
  have ha0 : 0 < a := by linarith
  have hsum := primesIn_le_S (by linarith : (1 : ℝ) ≤ w) hwz
  have hm1 := mertens_explicit hD hz
  have hm2 := mertens_explicit hD ha
  rw [abs_le] at hm1 hm2
  have hLa := seventeen_le_log ha
  set La := log a with hLadef
  set Lw := log w with hLwdef
  set Lz := log z with hLzdef
  have hLaw : La ≤ Lw := Real.log_le_log ha0 (by linarith)
  have hLwz : Lw ≤ Lz := Real.log_le_log (by linarith) hwz.le
  have hLa0 : 0 < La := by linarith
  have hLw0 : 0 < Lw := by linarith
  have hLz0 : 0 < Lz := by linarith
  -- `Lw - La ≤ 1/a`
  have hw_a : Lw - La ≤ 1 / a := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < w / a)
    rw [Real.log_div (by linarith) ha0.ne'] at h
    have : w / a - 1 = 1 / a := by rw [div_sub_one ha0.ne']; congr 1; rw [hadef]; ring
    linarith
  -- `La² ≤ 4a`
  have hsq : La ^ 2 ≤ 4 * a := by
    have h := Real.log_le_sub_one_of_pos (Real.sqrt_pos.2 ha0)
    rw [Real.log_sqrt ha0.le] at h
    have hs : 0 ≤ Real.sqrt a := Real.sqrt_nonneg a
    have h2 : La ≤ 2 * Real.sqrt a := by linarith
    have h3 := pow_le_pow_left₀ hLa0.le h2 2
    rw [mul_pow, Real.sq_sqrt ha0.le] at h3
    linarith
  set v := (La ^ 2)⁻¹ with hvdef
  have hv0 : 0 < v := by positivity
  have hinva : 1 / a ≤ 4 * v := by
    rw [hvdef, div_le_iff₀ ha0]
    rw [show 4 * (La ^ 2)⁻¹ * a = 4 * a / La ^ 2 by ring, le_div_iff₀ (by positivity)]
    linarith
  -- `log Lw - log La ≤ 4/17 · v`
  have hll : log Lw - log La ≤ 4 / 17 * v := by
    have h := Real.log_le_sub_one_of_pos (by positivity : 0 < Lw / La)
    rw [Real.log_div hLw0.ne' hLa0.ne'] at h
    have e : Lw / La - 1 = (Lw - La) * La⁻¹ := by field_simp
    have hinv : La⁻¹ ≤ (17 : ℝ)⁻¹ := inv_anti₀ (by norm_num) hLa
    have hd : 0 ≤ Lw - La := by linarith
    have h1 : (Lw - La) * La⁻¹ ≤ (4 * v) * La⁻¹ :=
      mul_le_mul_of_nonneg_right (by linarith) (by positivity)
    have h2 : (4 * v) * La⁻¹ ≤ (4 * v) * (17 : ℝ)⁻¹ :=
      mul_le_mul_of_nonneg_left hinv (by positivity)
    have : (4 * v) * (17 : ℝ)⁻¹ = 4 / 17 * v := by ring
    linarith
  -- `(17/18)² v ≤ 1/Lw²`
  have hLw_up : Lw ≤ 18 / 17 * La := by
    have : 1 / a ≤ 1 := by rw [div_le_one ha0]; linarith
    linarith
  have hC : (17 / 18) ^ 2 * v ≤ 1 / Lw ^ 2 := by
    have h2 : Lw ^ 2 ≤ (18 / 17 * La) ^ 2 := pow_le_pow_left₀ hLw0.le hLw_up 2
    rw [hvdef, show (17 / 18 : ℝ) ^ 2 * (La ^ 2)⁻¹ = (17 / 18) ^ 2 / La ^ 2 by ring,
      div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith
  have hdivz : log (Lz / Lw) = log Lz - log Lw := Real.log_div hLz0.ne' hLw0.ne'
  have e1 : 0.01 / Lz ^ 2 = 0.01 * (1 / Lz ^ 2) := by ring
  have e2 : 0.01 / La ^ 2 = 0.01 * v := by rw [hvdef]; ring
  have hz2 : 0 ≤ 1 / Lz ^ 2 := by positivity
  rw [hdivz]
  rw [e1] at hm1
  rw [e2] at hm2
  nlinarith [hm1.2, hm2.1]

/-- Rosser-Schoenfeld Theorem 5 in the `RSHyp` form for `286 ≤ w < 10^10 + 1` only. Cited. -/
def RSHypLow : Prop := ∀ w z : ℝ, 286 ≤ w → w < 10 ^ 10 + 1 → w < z →
  2 * ∑ p ∈ DDLemma21.primesIn w z, (1 : ℝ) / p ≤
    2 * Real.log (Real.log z / Real.log w) + 1 / (Real.log z) ^ 2 + 1 / (Real.log w) ^ 2

/-- **`RSHyp` from its low range and Dusart**. CONDITIONAL ON `RSHypLow`, `DusartThm52k2`. -/
theorem RSHyp_of_low (hD : DusartThm52k2) (hL : RSHypLow) : DDLemma21All.RSHyp := by
  intro w z hw hwz
  by_cases h : w < 10 ^ 10 + 1
  · exact hL w z hw h hwz
  · exact RSHyp_high hD (not_lt.1 h) hwz

/-- **Theorem 3.3 for `N ≥ 10^200`**, Dudek-Dunn. CONDITIONAL ON `RSHypLow`, `DusartThm52k2`,
`BLe`, `SelbergThm13`. -/
theorem theorem3_3_large_of_dusart2 (hL : RSHypLow) (hD : DusartThm52k2) (hB : BLe)
    (hSel : SelbergThm13) (N : ℕ) (hN : (10 : ℝ) ^ 200 ≤ N) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ N = a + b ∧
      (Even N → bigOmega (a * b) ≤ 39) ∧ bigOmega (a * b) ≤ 40 :=
  theorem3_3_large_of_dusart (RSHyp_of_low hD hL) hD hB hSel N hN

end LeanLab.AlmostPrimes.MertensRS320

#print axioms LeanLab.AlmostPrimes.MertensRS320.RS320_of_dusart
#print axioms LeanLab.AlmostPrimes.MertensRS320.RSRecip_of_dusart
#print axioms LeanLab.AlmostPrimes.MertensRS320.theorem3_3_large_of_dusart
#print axioms LeanLab.AlmostPrimes.MertensRS320.primesIn_le_S
#print axioms LeanLab.AlmostPrimes.MertensRS320.RSHyp_high
#print axioms LeanLab.AlmostPrimes.MertensRS320.RSHyp_of_low
#print axioms LeanLab.AlmostPrimes.MertensRS320.theorem3_3_large_of_dusart2
