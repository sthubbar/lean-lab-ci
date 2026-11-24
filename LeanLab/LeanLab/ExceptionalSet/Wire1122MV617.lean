import LeanLab.ExceptionalSet.UpJ200.Lemma3MV610Tilde
import LeanLab.ExceptionalSet.UpJ200.Lemma3MV619Weights
import LeanLab.ExceptionalSet.UpJ200.Lemma3MV620
import LeanLab.ExceptionalSet.UpJ200.Lemma3MV616Tilde
import LeanLab.ExceptionalSet.UpJ200.Lemma3MVItildeEval
import LeanLab.ExceptionalSet.Wire1122Lemma55

/-!
# Wiring: P0015 display (6.1̃7) on two named inputs

Burst burst-20261122, Claude cloud session S112, branch claude/ExceptionalSet-wire617, stacked on
claude/ExceptionalSet-mv610_tilde, -mv619_weights, -mv620, -mv616_tilde and -mv64_tilde_split.
Source P0015, Montgomery and Vaughan 1975, display (6.1̃7) page 365, used by P0082 Lemma 3.

Five of the seven leaves of `Lemma3MV617Integral.mv_617_tilde_integral_of_steps` are now proved
in this round: (6.1̃0) both integrals, (6.19), (6.1̃6) and (6.20). The assembly below is the proof
of `mv_617_tilde_integral_of_steps`, copied line for line, with those five leaves replaced by
their proved twins and the two remaining leaves taken as hypotheses: `mv_64_tilde_remainder`,
displays (6.1) to (6.9) with the exceptional additions, and `mv_615_absorbed`, the QUESTION leaf
of (6.13) and (6.14). Then `Lemma3MVSplit.mv_617_tilde` follows with the proved evaluation of
`Ĩ(n)` from `Lemma3MVItildeEval`.

No new definition, no sorry, no statement changed. AI wrote the Lean code. Binary Goldbach is
open.
-/

namespace LeanLab.ExceptionalSet.UpJ200.Wire1122MV617

open LeanLab.ExceptionalSet.UpJ200.Lemma3MV617Integral
open Real Finset Filter
open LeanLab.ExceptionalSet.U1539 (R1 eC)
open LeanLab.ExceptionalSet.UpJ200.Decomp527a (divisorError)
open LeanLab.ExceptionalSet.UpJ200.Decomp559b (SelectedRealZero)
open LeanLab.ExceptionalSet.UpJ200.DQLeafCoprimeSelected (singSeries)
open LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082 (twistedSing)
open LeanLab.ExceptionalSet.UpJ200.DQLeafAbsentSelected (singularSeries)
open LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit
  (T mainWeight arcIntegral ramanujan mv_arc_main_611 mv_singular_series_616
    norm_sum_sub_tsum_le mainWeight_zero)
open LeanLab.ExceptionalSet.UpJ200.Lemma3MVSplit (Ttilde mvWtilde)

set_option maxHeartbeats 1000000 in
/-- P0015 display (6.1̃7) with `Ĩ(n)` the integral of page 364, the exact type of the leaf
`Lemma3MV617Split.mv_617_tilde_integral`, CONDITIONAL ON the two remaining leaves
`mv_64_tilde_remainder` and `mv_615_absorbed` of `Lemma3MV617Integral`. -/
theorem mv_617_tilde_integral_of_two
    (h64 : type_of% @Lemma3MV617Integral.mv_64_tilde_remainder)
    (h615 : type_of% @Lemma3MV617Integral.mv_615_absorbed) :
    type_of% @Lemma3MV617Split.mv_617_tilde_integral := by
  intro a ha
  obtain ⟨C1, hC1, h1⟩ := h64 a ha
  obtain ⟨Ca, hCa, hA⟩ := h615 a ha
  obtain ⟨C2, hC2, h2⟩ := mv_arc_main_611
  obtain ⟨C5, hC5, h5⟩ := Lemma3MV610Tilde.mv_610_tilde_sq_proved
  obtain ⟨C6, hC6, h6⟩ := Lemma3MV610Tilde.mv_610_tilde_cross_proved
  obtain ⟨Cw, hCw, hw⟩ := Lemma3MV619Weights.mv_619_weights_proved
  obtain ⟨C7, hC7, h7⟩ := Lemma3MV620.mv_620_proved
  refine ⟨C1 + (C2 + 1) * Ca + (C5 + 2 * C6 + 3) * Cw + 2 * C7, by positivity,
    fun θ hθ hθ1 => ?_⟩
  obtain ⟨PA, hPA⟩ := h1 θ hθ hθ1
  obtain ⟨PB, hPB⟩ := hA θ hθ hθ1
  obtain ⟨X2, hX2⟩ := h2 (θ / 6) (by positivity) (by linarith)
  have h6θ : 6 * (θ / 6) = θ := by ring
  simp only [h6θ] at hX2
  obtain ⟨X5, hX5⟩ := h5 θ hθ hθ1
  obtain ⟨X6, hX6⟩ := h6 θ hθ hθ1
  set Xm := max (max X2 X5) (max X6 1) with hXm
  refine ⟨max (max PA PB) (Xm ^ θ), ?_⟩
  intro X hX hPX r hr1 hr hrP hsel hNZ χ β hprim hsq hne hβ1 hβ2 hL m hm hmX hev
  have hPA' : PA ≤ X ^ θ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hPX
  have hPB' : PB ≤ X ^ θ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hPX
  have hXm1 : 1 ≤ Xm := le_trans (le_max_right _ _) (le_max_right _ _)
  have hXmX : Xm ≤ X :=
    (Real.rpow_le_rpow_iff (by linarith) hX.le hθ).mp (le_trans (le_max_right _ _) hPX)
  have hX2' : X2 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hXmX
  have hX5' : X5 ≤ X := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hXmX
  have hX6' : X6 ≤ X := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hXmX
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le (by omega : (0 : ℤ) ≤ m)
  have hn : 1 ≤ n := by exact_mod_cast hm
  have hnX : (n : ℝ) ≤ X := by exact_mod_cast hmX
  have hevn : Even n := by exact_mod_cast hev
  have e1 : ((n : ℤ) : ℝ) = (n : ℝ) := Int.cast_natCast n
  have e2 : (n : ℤ).toNat = n := Int.toNat_natCast n
  rw [e2, e1]
  -- notation
  set P := X ^ θ with hPdef
  have hP0 : 0 ≤ P := Real.rpow_nonneg hX.le θ
  set s := Icc 1 ⌊P⌋₊ with hs
  set M := (n : ℝ) / (n.totient : ℝ) with hMdef
  set Wt := mvWtilde β P X χ
  set I := ItildeInt β P X n with hIdef
  set J := Jtilde β P X n with hJdef
  set tS := twistedSing χ (n : ℤ) with htS
  set D1 := (r : ℝ) / P * ∑ q ∈ s.filter (fun q => r ∣ q),
    (q : ℝ) / ((q.totient : ℝ) * ((q / Int.gcd (n : ℤ) q).totient : ℝ)) with hD1
  set D2 := (r : ℝ) * ∑' q : ℕ, (if P < (q : ℝ) ∧ r ∣ q then
    1 / ((q.totient : ℝ) * ((q / Int.gcd (n : ℤ) q).totient : ℝ)) else 0) with hD2
  have hD : divisorError r P (n : ℤ) = D1 + D2 := rfl
  have hD1n : 0 ≤ D1 := by
    apply mul_nonneg (by positivity)
    exact sum_nonneg (fun q _ => by positivity)
  have hD2n : 0 ≤ D2 := by
    apply mul_nonneg (by positivity)
    exact tsum_nonneg (fun q => by split_ifs <;> positivity)
  have hM0 : 0 ≤ M := by positivity
  have hIgoal : (∫ η in (0 : ℝ)..1, Ttilde β P X η ^ 2 * eC (-(η * (n : ℝ)))) = I := rfl
  rw [hIgoal]
  -- the pieces
  have hT1 := hPA X hX hPA' r hr1 hr hrP hsel hNZ χ β hprim hsq hne hβ1 hβ2 hL n hn hnX
  have hAbs := hPB X hX hPB' r hr1 hr hrP hsel hNZ χ β hprim hsq hne hβ1 hβ2 hL n hn hnX hevn
  obtain ⟨h618I, h618J⟩ := mv_618_tilde β P X hβ2.le hX.le n
  obtain ⟨hsE, hhE⟩ := Lemma3MV616Tilde.mv_616_tilde_proved r hNZ χ hprim hsq hne n hn
  obtain ⟨hsK, hK7⟩ := h7 r hNZ χ hprim hsq hne n hn
  have hwq := hw r hNZ χ hprim hsq
  have hqP : ∀ q ∈ s, 1 ≤ q ∧ (q : ℝ) ≤ P := fun q hq =>
    ⟨(mem_Icc.mp hq).1, le_trans (by exact_mod_cast (mem_Icc.mp hq).2) (Nat.floor_le hP0)⟩
  have hEz : ∀ q, ¬ r ∣ q → excWeight χ q n = 0 :=
    fun q h => excWeight_of_tau χ n (tauInd_of_not_dvd χ h)
  have hKz : ∀ q, ¬ r ∣ q → crossWeight χ q n = 0 :=
    fun q h => crossWeight_of_tau χ n (tauInd_of_not_dvd χ h)
  have hE0 : excWeight χ 0 n = 0 := excWeight_of_tau χ n (tauInd_zero χ)
  have hK0 : crossWeight χ 0 n = 0 := crossWeight_of_tau χ n (tauInd_zero χ)
  have hEb : ∀ q, 1 ≤ q → r ∣ q → ‖excWeight χ q n‖ ≤
      Cw * ((r : ℝ) * (1 / ((q.totient : ℝ) * ((q / Int.gcd (n : ℤ) q).totient : ℝ)))) :=
    fun q hq hrq => le_trans (le_add_of_nonneg_right (norm_nonneg _)) (hwq q n hq hrq hn)
  have hKb : ∀ q, 1 ≤ q → r ∣ q → ‖crossWeight χ q n‖ ≤
      Cw * ((r : ℝ) * (1 / ((q.totient : ℝ) * ((q / Int.gcd (n : ℤ) q).totient : ℝ)))) :=
    fun q hq hrq => le_trans (le_add_of_nonneg_left (norm_nonneg _)) (hwq q n hq hrq hn)
  -- T2
  have hT2 : ‖∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ))‖ ≤
      C2 * ((X / P) * ∑ q ∈ s, ‖mainWeight q n‖ * q) := by
    calc ‖∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ))‖
        ≤ ∑ q ∈ s, ‖mainWeight q n‖ * (C2 * q * (X / P)) := by
          refine (norm_sum_le _ _).trans (sum_le_sum (fun q hq => ?_))
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            (hX2 X hX2' q (hqP q hq).1 (hqP q hq).2 n hn hnX) (norm_nonneg _)
      _ = C2 * ((X / P) * ∑ q ∈ s, ‖mainWeight q n‖ * q) := by
          rw [mul_sum, mul_sum]; refine sum_congr rfl (fun q _ => by ring)
  -- T3
  have hT3 : ‖(n : ℂ) * ((∑ q ∈ s, mainWeight q n) - ((singularSeries n : ℝ) : ℂ))‖ ≤
      (n : ℝ) * ∑' q : ℕ, (if P < (q : ℝ) then ‖mainWeight q n‖ else 0) := by
    obtain ⟨hsum, hhas⟩ := mv_singular_series_616 n hn
    have ht := norm_sum_sub_tsum_le hsum hhas s
    have hcongr : ∑' q : ℕ, (if q ∈ s then 0 else ‖mainWeight q n‖) =
        ∑' q : ℕ, (if P < (q : ℝ) then ‖mainWeight q n‖ else 0) := by
      refine tsum_congr (fun q => ?_)
      by_cases hq0 : q = 0
      · subst hq0; simp [mainWeight_zero]
      · have hiff : q ∈ s ↔ ¬ P < (q : ℝ) := by
          rw [hs, mem_Icc, not_lt]
          constructor
          · rintro ⟨_, h⟩; exact le_trans (by exact_mod_cast h) (Nat.floor_le hP0)
          · intro h; exact ⟨by omega, Nat.le_floor h⟩
        by_cases hq : q ∈ s
        · simp [hq, hiff.mp hq]
        · have : P < (q : ℝ) := by by_contra h; exact hq (hiff.mpr h)
          simp [hq, this]
    rw [hcongr] at ht
    rw [norm_mul, Complex.norm_natCast]
    exact mul_le_mul_of_nonneg_left ht (by positivity)
  -- T4 and T6
  have hT4 : ‖∑ q ∈ s, excWeight χ q n * (arcTt β P X q n - I)‖ ≤
      C5 * ((X / P) * ∑ q ∈ s, ‖excWeight χ q n‖ * q) := by
    calc _ ≤ ∑ q ∈ s, ‖excWeight χ q n‖ * (C5 * q * (X / P)) := by
          refine (norm_sum_le _ _).trans (sum_le_sum (fun q hq => ?_))
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            (hX5 X hX5' β hβ2.le q (hqP q hq).1 (hqP q hq).2 n hn hnX) (norm_nonneg _)
      _ = _ := by rw [mul_sum, mul_sum]; refine sum_congr rfl (fun q _ => by ring)
  have hT6 : ‖2 * ∑ q ∈ s, crossWeight χ q n * (arcTTt β P X q n - J)‖ ≤
      2 * C6 * ((X / P) * ∑ q ∈ s, ‖crossWeight χ q n‖ * q) := by
    rw [norm_mul, Complex.norm_ofNat, mul_assoc]
    refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
    calc _ ≤ ∑ q ∈ s, ‖crossWeight χ q n‖ * (C6 * q * (X / P)) := by
          refine (norm_sum_le _ _).trans (sum_le_sum (fun q hq => ?_))
          rw [norm_mul]
          exact mul_le_mul_of_nonneg_left
            (hX6 X hX6' β hβ2.le q (hqP q hq).1 (hqP q hq).2 n hn hnX) (norm_nonneg _)
      _ = _ := by rw [mul_sum, mul_sum]; refine sum_congr rfl (fun q _ => by ring)
  have hEfin : (X / P) * ∑ q ∈ s, ‖excWeight χ q n‖ * q ≤ Cw * X * D1 :=
    fin_weight_le (fun q => ‖excWeight χ q n‖) r P X hP0 hX.le n Cw
      (fun q _ h => by simp [hEz q h]) (fun q hq h => hEb q (hqP q hq).1 h)
  have hKfin : (X / P) * ∑ q ∈ s, ‖crossWeight χ q n‖ * q ≤ Cw * X * D1 :=
    fin_weight_le (fun q => ‖crossWeight χ q n‖) r P X hP0 hX.le n Cw
      (fun q _ h => by simp [hKz q h]) (fun q hq h => hKb q (hqP q hq).1 h)
  -- T5
  have hT5 : ‖I * ((∑ q ∈ s, excWeight χ q n) - ((tS : ℝ) : ℂ))‖ ≤ X * (Cw * D2) := by
    rw [norm_mul]
    have ht := norm_sum_sub_tsum_le hsE hhE s
    have ht2 := tail_weight_le (fun q => excWeight χ q n) r P hP0 n hn Cw hCw.le hE0 hEz hEb hsE
    exact mul_le_mul h618I (ht.trans ht2) (norm_nonneg _) hX.le
  -- T7
  have hT7 : ‖2 * J * ∑ q ∈ s, crossWeight χ q n‖ ≤
      2 * X * (C7 * ‖χ ((n : ℤ) : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M + Cw * D2) := by
    rw [norm_mul, norm_mul, Complex.norm_ofNat]
    have hK := hsK.of_norm.hasSum
    have ht := norm_sum_sub_tsum_le hsK hK s
    have ht2 := tail_weight_le (fun q => crossWeight χ q n) r P hP0 n hn Cw hCw.le hK0 hKz hKb hsK
    have hsplit : ∑ q ∈ s, crossWeight χ q n =
        (∑' q, crossWeight χ q n) + ((∑ q ∈ s, crossWeight χ q n) - ∑' q, crossWeight χ q n) := by
      ring
    have hnorm : ‖∑ q ∈ s, crossWeight χ q n‖ ≤
        C7 * ‖χ ((n : ℤ) : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M + Cw * D2 := by
      rw [hsplit]
      exact (norm_add_le _ _).trans (add_le_add hK7 (ht.trans ht2))
    have hJ := mul_le_mul h618J hnorm (norm_nonneg _) hX.le
    refine le_trans (le_of_eq (mul_assoc _ _ _)) ?_
    refine le_trans (mul_le_mul_of_nonneg_left hJ (by norm_num)) (le_of_eq ?_)
    ring
  -- the identity
  have hS3 : ∑ q ∈ s, (mainWeight q n * arcIntegral P X q n + excWeight χ q n * arcTt β P X q n +
        2 * crossWeight χ q n * arcTTt β P X q n) =
      ∑ q ∈ s, mainWeight q n * arcIntegral P X q n + ∑ q ∈ s, excWeight χ q n * arcTt β P X q n +
        2 * ∑ q ∈ s, crossWeight χ q n * arcTTt β P X q n := by
    rw [sum_add_distrib, sum_add_distrib, mul_sum]
    congr 1
    refine sum_congr rfl (fun q _ => by ring)
  have hA2 : ∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ)) =
      ∑ q ∈ s, mainWeight q n * arcIntegral P X q n - (∑ q ∈ s, mainWeight q n) * (n : ℂ) := by
    rw [sum_mul, ← sum_sub_distrib]; refine sum_congr rfl (fun q _ => by ring)
  have hE4 : ∑ q ∈ s, excWeight χ q n * (arcTt β P X q n - I) =
      ∑ q ∈ s, excWeight χ q n * arcTt β P X q n - (∑ q ∈ s, excWeight χ q n) * I := by
    rw [sum_mul, ← sum_sub_distrib]; refine sum_congr rfl (fun q _ => by ring)
  have hK6 : ∑ q ∈ s, crossWeight χ q n * (arcTTt β P X q n - J) =
      ∑ q ∈ s, crossWeight χ q n * arcTTt β P X q n - (∑ q ∈ s, crossWeight χ q n) * J := by
    rw [sum_mul, ← sum_sub_distrib]; refine sum_congr rfl (fun q _ => by ring)
  have hsplit : R1 P X (n : ℤ) - (((n : ℝ) * singularSeries n : ℝ) : ℂ) - I * ((tS : ℝ) : ℂ) =
      (R1 P X (n : ℤ) - ∑ q ∈ s, (mainWeight q n * arcIntegral P X q n +
          excWeight χ q n * arcTt β P X q n + 2 * crossWeight χ q n * arcTTt β P X q n)) +
        ∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ)) +
        (n : ℂ) * ((∑ q ∈ s, mainWeight q n) - ((singularSeries n : ℝ) : ℂ)) +
        ∑ q ∈ s, excWeight χ q n * (arcTt β P X q n - I) +
        I * ((∑ q ∈ s, excWeight χ q n) - ((tS : ℝ) : ℂ)) +
        2 * ∑ q ∈ s, crossWeight χ q n * (arcTTt β P X q n - J) +
        2 * J * ∑ q ∈ s, crossWeight χ q n := by
    rw [hS3, hA2, hE4, hK6]
    push_cast
    ring
  -- the norm bound
  set WT := Wt * Real.sqrt X + Wt ^ 2 with hWT
  set v := X * ‖χ ((n : ℤ) : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M with hv
  have hv0 : 0 ≤ v := by positivity
  have hw0 : 0 ≤ M * WT := by
    have h0 := le_trans (norm_nonneg _) hT1
    have : C1 * M * WT = C1 * (M * WT) := by ring
    rw [this] at h0
    exact (mul_nonneg_iff_of_pos_left hC1).mp h0
  have hkey : ‖R1 P X (n : ℤ) - (((n : ℝ) * singularSeries n : ℝ) : ℂ) - I * ((tS : ℝ) : ℂ)‖ ≤
      (C1 + (C2 + 1) * Ca + (C5 + 2 * C6 + 3) * Cw + 2 * C7) * X * (D1 + D2) +
        (C1 + (C2 + 1) * Ca + (C5 + 2 * C6 + 3) * Cw + 2 * C7) * v +
        (C1 + (C2 + 1) * Ca + (C5 + 2 * C6 + 3) * Cw + 2 * C7) * (M * WT) := by
    rw [hsplit]
    refine (norm_add7_le _ _ _ _ _ _ _).trans ?_
    simp only [← hPdef] at hAbs
    rw [hD] at hAbs
    have hAbs' : (X / P) * ∑ q ∈ s, ‖mainWeight q n‖ * q +
        (n : ℝ) * ∑' q : ℕ, (if P < (q : ℝ) then ‖mainWeight q n‖ else 0) ≤
        Ca * (X * (D1 + D2)) + Ca * v + Ca * (M * WT) := by
      refine hAbs.trans (le_of_eq ?_); rw [hv]; ring
    have hT1' : ‖R1 P X (n : ℤ) - ∑ q ∈ s, (mainWeight q n * arcIntegral P X q n +
          excWeight χ q n * arcTt β P X q n + 2 * crossWeight χ q n * arcTTt β P X q n)‖ ≤
        C1 * (M * WT) := hT1.trans (le_of_eq (by ring))
    have hT7' : ‖2 * J * ∑ q ∈ s, crossWeight χ q n‖ ≤ 2 * C7 * v + 2 * Cw * (X * D2) :=
      hT7.trans (le_of_eq (by rw [hv]; ring))
    have hT5' : ‖I * ((∑ q ∈ s, excWeight χ q n) - ((tS : ℝ) : ℂ))‖ ≤ Cw * (X * D2) :=
      hT5.trans (le_of_eq (by ring))
    have hXD1 : 0 ≤ X * D1 := mul_nonneg hX.le hD1n
    have hXD2 : 0 ≤ X * D2 := mul_nonneg hX.le hD2n
    have hm0 : 0 ≤ (X / P) * ∑ q ∈ s, ‖mainWeight q n‖ * q :=
      mul_nonneg (div_nonneg hX.le hP0) (sum_nonneg (fun q _ => by positivity))
    have hT45 : ‖∑ q ∈ s, excWeight χ q n * (arcTt β P X q n - I)‖ +
        ‖2 * ∑ q ∈ s, crossWeight χ q n * (arcTTt β P X q n - J)‖ ≤
        (C5 + 2 * C6) * Cw * (X * D1) := by
      exact arith_three C5 C6 Cw _ _ (X * D1) _ _ hC5.le hC6.le hT4 hT6
        (hEfin.trans (le_of_eq (mul_assoc _ _ _))) (hKfin.trans (le_of_eq (mul_assoc _ _ _)))
    have hT23 : ‖∑ q ∈ s, mainWeight q n * (arcIntegral P X q n - (n : ℂ))‖ +
        ‖(n : ℂ) * ((∑ q ∈ s, mainWeight q n) - ((singularSeries n : ℝ) : ℂ))‖ ≤
        (C2 + 1) * (Ca * (X * (D1 + D2)) + Ca * v + Ca * (M * WT)) := by
      have htail0 : 0 ≤ (n : ℝ) * ∑' q : ℕ, (if P < (q : ℝ) then ‖mainWeight q n‖ else 0) :=
        mul_nonneg (by positivity) (tsum_nonneg (fun q => by split_ifs <;> positivity))
      exact arith_two C2 _ _ _ _ _ hC2.le hm0 htail0 hT2 hT3 hAbs'
    have hfin := arith_final C1 C2 Ca C5 C6 Cw C7 (X * D1) (X * D2) v (M * WT) hC1.le hC2.le
      hCa.le hC5.le hC6.le hCw.le hC7.le hXD1 hXD2 hv0 hw0
    have hXD : X * (D1 + D2) = X * D1 + X * D2 := by ring
    rw [hXD] at hT23
    rw [mul_assoc _ X (D1 + D2), hXD]
    linarith [hT1', hT23, hT45, hT5', hT7', hfin]
  have hre : (R1 P X (n : ℤ)).re - ((n : ℝ) * singSeries (n : ℤ) + I.re * tS) =
      (R1 P X (n : ℤ) - (((n : ℝ) * singularSeries n : ℝ) : ℂ) - I * ((tS : ℝ) : ℂ)).re := by
    rw [singSeries_natCast]
    simp [Complex.sub_re, Complex.mul_re]
    ring
  rw [hre]
  refine (Complex.abs_re_le_norm _).trans (hkey.trans (le_of_eq ?_))
  rw [hD, hv]
  ring

/-- P0015 display (6.1̃7), the exact type of the leaf `Lemma3MVSplit.mv_617_tilde`, CONDITIONAL ON
`mv_64_tilde_remainder` and `mv_615_absorbed`; the evaluation of `Ĩ(n)` on page 365 is the
proved `Lemma3MVItildeEval.mv_Itilde_eval_proved`. -/
theorem mv_617_tilde_of_two
    (h64 : type_of% @Lemma3MV617Integral.mv_64_tilde_remainder)
    (h615 : type_of% @Lemma3MV617Integral.mv_615_absorbed) :
    type_of% @Lemma3MVSplit.mv_617_tilde := by
  intro a ha
  obtain ⟨C, hC, h⟩ := mv_617_tilde_integral_of_two h64 h615 a ha
  refine ⟨C, hC, fun θ hθ hθ1 => ?_⟩
  obtain ⟨P₀, hP⟩ := h θ hθ hθ1
  refine ⟨P₀, fun X hX hPX r hr1 hr hrP hsel hNZ χ β hprim hsq hne hβ1 hβ2 hL m hm hmX hev => ?_⟩
  have hI := LeanLab.ExceptionalSet.UpJ200.Lemma3MVItildeEval.mv_Itilde_eval_proved
    β (X ^ θ) X (Real.rpow_nonneg hX.le θ) m hm hmX
  have key := hP X hX hPX r hr1 hr hrP hsel hNZ χ β hprim hsq hne hβ1 hβ2 hL m hm hmX hev
  rw [hI, Complex.ofReal_re] at key
  exact key

section BPLemma3

open LeanLab.ExceptionalSet.UpJ200.DQDisplay21P0082 (Itilde)
open LeanLab.ExceptionalSet.UpJ200.DQCaseIIbP0082 (BPLemma3Hyp)
open LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit (Wchi Wnorm mvW)
open LeanLab.ExceptionalSet.UpJ200.Lemma3MVSplit (w_terms_le)

/-- P0082 page 358 Lemma 3, `BPLemma3Hyp`, CONDITIONAL ON three named leaves: P0015 displays (6.1)
to (6.9) with the exceptional additions, `mv_64_tilde_remainder`; the QUESTION leaf
`mv_615_absorbed` of (6.13) and (6.14); and P0015 display (7.1̃), `Lemma3MVSplit.mv_71_tilde`. The
proof is that of `Lemma3MVSplit.bpLemma3Hyp_of_leaves`, copied line for line, with the leaf
`mv_617_tilde` replaced by `mv_617_tilde_of_two`. -/
theorem bpLemma3Hyp_of_three
    (h64 : type_of% @Lemma3MV617Integral.mv_64_tilde_remainder)
    (h615 : type_of% @Lemma3MV617Integral.mv_615_absorbed)
    (h71 : type_of% @Lemma3MVSplit.mv_71_tilde) :
    BPLemma3Hyp := by
  intro a ha
  obtain ⟨CA, hCA, hA⟩ := mv_617_tilde_of_two h64 h615 a ha
  obtain ⟨B, c₆, hB, hc₆, hW⟩ := h71 a ha
  refine ⟨CA * (1 + B + B ^ 2 * a), c₆, by positivity, hc₆, ?_⟩
  intro θ hθ hθ6
  obtain ⟨PA, hPA⟩ := hA θ hθ hθ6
  obtain ⟨PB, hPB⟩ := hW θ hθ hθ6
  refine ⟨max (max PA PB) 2, ?_⟩
  intro X hX hP r hr1 hr1' hrP hsel hNZ χ β hprim hsq hne hβ hβ1 hL m hm1 hmX hev
  have hPA' : PA ≤ X ^ θ := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hP
  have hPB' : PB ≤ X ^ θ := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hP
  have hP2 : (2 : ℝ) ≤ X ^ θ := le_trans (le_max_right _ _) hP
  have hlogP : 0 < Real.log (X ^ θ) := Real.log_pos (by linarith)
  have hA1 := hPA X hX hPA' r hr1 hr1' hrP hsel hNZ χ β hprim hsq hne hβ hβ1 hL m hm1 hmX hev
  have hW1 := hPB X hX hPB' r hr1 hr1' hrP hsel hNZ χ β hprim hsq hne hβ hβ1 hL
  set P := X ^ θ with hPdef
  set W := mvWtilde β P X χ
  set M := (m.toNat : ℝ) / (m.toNat.totient : ℝ)
  set u := (1 - β) * Real.log P with hu
  set e := Real.exp (-(c₆ / θ)) with he
  have hu0 : 0 ≤ u := mul_nonneg (by linarith) hlogP.le
  have hua : u ≤ a := by
    have h1 : 1 - β ≤ a / Real.log P := by linarith
    exact (le_div_iff₀ hlogP).mp h1
  have he0 : 0 ≤ e := (Real.exp_pos _).le
  have he1 : e ≤ 1 := by
    rw [he, Real.exp_le_one_iff]; exact neg_nonpos.mpr (div_nonneg hc₆.le hθ.le)
  have hW2 : |W| ≤ B * Real.sqrt X * (u * e) := by
    have : B * Real.sqrt X * (1 - β) * e * Real.log P = B * Real.sqrt X * (u * e) := by
      rw [hu]; ring
    rw [← this]; exact hW1
  have hterms := w_terms_le W B X u e a hB.le hX.le hu0 hua he0 he1 hW2
  have hM : 0 ≤ M := by positivity
  have hD : 0 ≤ divisorError r P m := by
    unfold divisorError
    apply add_nonneg
    · apply mul_nonneg (by positivity)
      exact sum_nonneg (fun q _ => by positivity)
    · apply mul_nonneg (by positivity)
      exact tsum_nonneg (fun q => by split_ifs <;> positivity)
  have hchi : 0 ≤ X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M := by positivity
  have hk : 1 ≤ 1 + B + B ^ 2 * a := by
    have := mul_nonneg (sq_nonneg B) ha.le; linarith
  have hCk : CA ≤ CA * (1 + B + B ^ 2 * a) := le_mul_of_one_le_right hCA.le hk
  have hfin : CA * M * (W * Real.sqrt X + W ^ 2) ≤
      CA * (1 + B + B ^ 2 * a) * X * M * (1 - β) * e * Real.log P := by
    have h1 : CA * M * (W * Real.sqrt X + W ^ 2) ≤ CA * M * ((B + B ^ 2 * a) * X * (u * e)) :=
      mul_le_mul_of_nonneg_left hterms (by positivity)
    have h2 : CA * M * ((B + B ^ 2 * a) * X * (u * e)) ≤
        CA * (1 + B + B ^ 2 * a) * X * M * (u * e) := by
      have hY : 0 ≤ CA * X * M * (u * e) := by positivity
      calc CA * M * ((B + B ^ 2 * a) * X * (u * e)) = (B + B ^ 2 * a) * (CA * X * M * (u * e)) := by
            ring
        _ ≤ (1 + B + B ^ 2 * a) * (CA * X * M * (u * e)) :=
            mul_le_mul_of_nonneg_right (by linarith) hY
        _ = CA * (1 + B + B ^ 2 * a) * X * M * (u * e) := by ring
    calc CA * M * (W * Real.sqrt X + W ^ 2) ≤ CA * (1 + B + B ^ 2 * a) * X * M * (u * e) :=
          h1.trans h2
      _ = CA * (1 + B + B ^ 2 * a) * X * M * (1 - β) * e * Real.log P := by rw [hu]; ring
  have hXD : CA * X * divisorError r P m ≤ CA * (1 + B + B ^ 2 * a) * X * divisorError r P m := by
    have h0 : 0 ≤ X * divisorError r P m := mul_nonneg hX.le hD
    calc CA * X * divisorError r P m = CA * (X * divisorError r P m) := by ring
      _ ≤ CA * (1 + B + B ^ 2 * a) * (X * divisorError r P m) := mul_le_mul_of_nonneg_right hCk h0
      _ = CA * (1 + B + B ^ 2 * a) * X * divisorError r P m := by ring
  have hXc : CA * X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M ≤
      CA * (1 + B + B ^ 2 * a) * X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M := by
    have e1 : CA * X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M =
        CA * (X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M) := by ring
    have e2 : CA * (1 + B + B ^ 2 * a) * X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) /
        (r.totient : ℝ) ^ 2 * M =
        CA * (1 + B + B ^ 2 * a) * (X * ‖χ (m : ZMod r)‖ ^ 2 * (r : ℝ) / (r.totient : ℝ) ^ 2 * M) := by
      ring
    rw [e1, e2]; exact mul_le_mul_of_nonneg_right hCk hchi
  calc _ ≤ _ := hA1
    _ ≤ _ := by
      have : CA * X * M * (1 - β) * e * Real.log P =
          CA * X * M * (1 - β) * Real.exp (-(c₆ / θ)) * Real.log P := by rw [he]
      linarith [hfin, hXD, hXc]

end BPLemma3

/-- P0082 page 354 Theorem 1, CONDITIONAL ON six named leaves: `KarLemma1` and `KarLemma2`,
Karacuba 1971 pages 243 and 244; P0015 Lemma 4.3 `mv_gallagher_lemma43`; and, in place of the
single input `BPLemma3Hyp`, the three leaves of P0015 that remain open under it,
`mv_64_tilde_remainder`, `mv_615_absorbed` and `mv_71_tilde`. -/
theorem theorem1_of_six_inputs
    (hK1 : LeanLab.ExceptionalSet.U1539.KaracubaSplit.KarLemma1)
    (hK2 : LeanLab.ExceptionalSet.U1539.KaracubaSplit.KarLemma2)
    (hG43 : type_of% @LeanLab.ExceptionalSet.UpJ200.Lemma2MVSplit.mv_gallagher_lemma43)
    (h64 : type_of% @Lemma3MV617Integral.mv_64_tilde_remainder)
    (h615 : type_of% @Lemma3MV617Integral.mv_615_absorbed)
    (h71 : type_of% @Lemma3MVSplit.mv_71_tilde) :
    LeanLab.ExceptionalSet.BrudernPerelli1998.Theorem1 :=
  LeanLab.ExceptionalSet.Wire1122Lemma55.theorem1_of_four_inputs hK1 hK2 hG43
    (bpLemma3Hyp_of_three h64 h615 h71)

end LeanLab.ExceptionalSet.UpJ200.Wire1122MV617

#print axioms LeanLab.ExceptionalSet.UpJ200.Wire1122MV617.mv_617_tilde_integral_of_two
#print axioms LeanLab.ExceptionalSet.UpJ200.Wire1122MV617.mv_617_tilde_of_two
#print axioms LeanLab.ExceptionalSet.UpJ200.Wire1122MV617.bpLemma3Hyp_of_three
#print axioms LeanLab.ExceptionalSet.UpJ200.Wire1122MV617.theorem1_of_six_inputs
