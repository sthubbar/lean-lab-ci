/-
I-0067, unit U-0939, run 20261018T1103Z-12430, DISCOVER. The Granville, van de Lune, te Riele
quantity p(n) / (log² n log log n) over even n up to 4·10^18.
PROVED, unconditional: any C with p(n) ≤ C log² n log log n for every even n ≥ 16 has
C ≥ 1.52625, from n = 1047610575836828, p(n) = 6469. This sharpens the lab's I-0064 bound 3/2,
which used n = 258549426916149682 with ratio 1.5055.
PROVED, unconditional: every record row of A025018 with 12 ≤ n has p(n) < 1.52635 log² n log log n.
CONDITIONAL ON `RecordsComplete (4 * 10 ^ 18)`, the record list being complete below 4·10^18,
which is the searches of Oliveira e Silva, Herzog and Pardi and earlier authors: every even n
from 12 to 4·10^18 has p(n) ≤ 1.52635 log² n log log n. So the best constant on that range lies
in [1.52625, 1.52635). Because log² n log log n increases, the supremum over a range is always
the maximum over its record rows; that step is the lemma `f_mono`.
KNOWN in substance: sweet.ua.pt/tos/goldbach.html plots the line 1.527 log² S(p) log log S(p)
above its data; the sharp four-decimal value is new to us only as a machine-checked statement.
AI-written Lean code, Claude, 2026-10-18. The GvLtR conjecture is OPEN; binary Goldbach is OPEN.
-/
import Mathlib
import LeanLab.Richstein2001.RatioAll
import LeanLab.Richstein2001.SupRows

namespace LeanLab.Richstein2001

open LeanLab.Verifications LeanLab.Verifications.Top50

theorem one_lt_log_of {n : ℝ} (h : 12 ≤ n) : 1 < Real.log n := by
  rw [Real.lt_log_iff_exp_lt (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

/-- log² t log log t increases from t = 12. -/
theorem f_mono {a b : ℝ} (ha : 12 ≤ a) (hab : a ≤ b) :
    Real.log a ^ 2 * Real.log (Real.log a) ≤ Real.log b ^ 2 * Real.log (Real.log b) := by
  have h1 := one_lt_log_of ha
  have hl : Real.log a ≤ Real.log b := Real.log_le_log (by linarith) hab
  have hll : Real.log (Real.log a) ≤ Real.log (Real.log b) := Real.log_le_log (by linarith) hl
  have hpos : 0 < Real.log (Real.log a) := Real.log_pos h1
  exact mul_le_mul (pow_le_pow_left₀ (by linarith) hl 2) hll hpos.le (by positivity)

theorem le_of_ratio_lt {n p c : ℕ} (hc : c ≤ 15263) (h12 : 12 ≤ n)
    (h : ratio n p < ((2 * c + 1 : ℕ) : ℝ) / (2 * 10 ^ 4)) :
    (p : ℝ) ≤ 30527 / 20000 * Real.log n ^ 2 * Real.log (Real.log n) := by
  have h1 := one_lt_log_of (show (12 : ℝ) ≤ n by exact_mod_cast h12)
  have hf : 0 < Real.log n ^ 2 * Real.log (Real.log n) := by
    have := Real.log_pos h1; positivity
  have hB : ((2 * c + 1 : ℕ) : ℝ) / (2 * 10 ^ 4) ≤ 30527 / 20000 := by
    rw [div_le_div_iff₀ (by norm_num) (by norm_num)]
    have : ((2 * c + 1 : ℕ) : ℝ) ≤ 30527 := by exact_mod_cast (by omega : 2 * c + 1 ≤ 30527)
    nlinarith
  unfold ratio at h
  rw [div_lt_iff₀ hf] at h
  nlinarith

/-- Every record row with 12 ≤ n: p(n) < 1.52635 log² n log log n. -/
theorem rows_bound : ∀ x ∈ recTable, 12 ≤ x.2 →
    (x.1 : ℝ) ≤ 30527 / 20000 * Real.log (x.2 : ℕ) ^ 2 * Real.log (Real.log (x.2 : ℕ)) := by
  intro x hx h12
  simp only [recTable, List.mem_cons, List.mem_nil_iff, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · norm_num at h12
  · norm_num at h12
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_12).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_30).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_98).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_220).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_308).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_556).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_992).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_2642).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_5372).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_7426).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_43532).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_54244).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_63274).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_113672).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_128168).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_194428).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_194470).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_413572).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_503222).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_1077422).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_3526958).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_3807404).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_10759922).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_24106882).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_27789878).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_37998938).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_60119912).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_113632822).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_187852862).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_335070838).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_419911924).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_721013438).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_1847133842).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_7473202036).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_11001080372).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_12703943222).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_21248558888).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_35884080836).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_105963812462).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_244885595672).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_599533546358).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_3132059294006).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_3620821173302).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_4438327672994).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_5320503815888).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_8342945544436).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_10591605900482).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_12982270197518).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_15197900994218).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_28998050650046).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_46878442766282).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_76903574497118).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_184162477860248).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_217361316706568).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_389965026819938).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_1047610575836828).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_6253262345930828).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_24925556008175266).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_31284177910528922).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_121005022304007026).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_255329126688555994).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_258549426916149682).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_555274351556750822).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_887123803077837868).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_906030579562279642).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_2795935116574469638).2
  · exact le_of_ratio_lt (by norm_num) (by norm_num) (ratio_3325581707333960528).2

/-- The record list is complete below B: every even n from 12 to B has p(n) at most the record
of some row at or below n. Cited, the computations of Oliveira e Silva, Herzog, Pardi. -/
def RecordsComplete (B : ℕ) : Prop :=
  ∀ n, Even n → 12 ≤ n → n ≤ B → ∃ x ∈ recTable, 12 ≤ x.2 ∧ x.2 ≤ n ∧ minGB n ≤ x.1

/-- CONDITIONAL ON `RecordsComplete (4 * 10 ^ 18)`. -/
theorem gvltr_sup_of (h : RecordsComplete (4 * 10 ^ 18)) :
    ∀ n, Even n → 12 ≤ n → n ≤ 4 * 10 ^ 18 →
      (minGB n : ℝ) ≤ 30527 / 20000 * Real.log n ^ 2 * Real.log (Real.log n) := by
  intro n hn h12 hB
  obtain ⟨x, hx, hx12, hxn, hle⟩ := h n hn h12 hB
  have hr := rows_bound x hx hx12
  have hm := f_mono (show (12 : ℝ) ≤ (x.2 : ℕ) by exact_mod_cast hx12)
    (show ((x.2 : ℕ) : ℝ) ≤ n by exact_mod_cast hxn)
  have hle' : (minGB n : ℝ) ≤ x.1 := by exact_mod_cast hle
  nlinarith

/-- Unconditional lower bound on the GvLtR constant: C ≥ 1.52625. -/
theorem gvltr_const_ge_15262 (C : ℝ) (h : ∀ n : ℕ, Even n → 16 ≤ n →
    (minGB n : ℝ) ≤ C * Real.log n ^ 2 * Real.log (Real.log n)) : 30525 / 20000 ≤ C := by
  have hn := h 1047610575836828 (by decide) (by norm_num)
  have hm : minGB 1047610575836828 = 6469 :=
    recTable_minGB (6469, 1047610575836828) (by simp [recTable])
  rw [hm] at hn
  have hr := (ratio_1047610575836828).1
  have h1 := one_lt_log_of (show (12 : ℝ) ≤ ((1047610575836828 : ℕ) : ℝ) by norm_num)
  have hf : 0 < Real.log ((1047610575836828 : ℕ) : ℝ) ^ 2 *
      Real.log (Real.log ((1047610575836828 : ℕ) : ℝ)) := by
    have := Real.log_pos h1; positivity
  unfold ratio at hr
  rw [le_div_iff₀ hf] at hr
  norm_num at hr hn hf ⊢
  set F := Real.log 1047610575836828 ^ 2 * Real.log (Real.log 1047610575836828) with hF
  rw [mul_assoc] at hn
  by_contra hC
  push_neg at hC
  have : C * F < 1221 / 800 * F := mul_lt_mul_of_pos_right hC hf
  linarith

end LeanLab.Richstein2001
