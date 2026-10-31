/-
Unit U-1514, T2 FRONTIER, idea I-0112, run PC 20261025T0803Z-22023. AI-written Lean code, Claude.
Checked only by the Lean kernel. KNOWN mathematics, a re-derivation. Binary Goldbach is OPEN.

Ramaré-Saouter 2003 Theorem 3, a prime in `]x (1 - 1/28 314 000), x]` for real
`x > 10 726 905 041`, in the lab's statement form `RS3`, from inputs that do not use
Ramaré-Saouter's own Table 1 row at 10^20 or their Section 7 prime chain:

* `KLRow (4 · 10^18) 36082898`, Kadiri-Lumley 2014 Table 2, for `x > 4 · 10^18`;
* `GapBound1476`, Oliveira e Silva, Herzog, Pardi 2014, on `[41 791 464 000, 4 · 10^18]`,
  since `1476 · 28 314 000 = 41 791 464 000`;
* `RecordGap456`, the maximal gap records, OEIS A002386, for `[12 911 184 000, 41 791 464 000)`,
  since `456 · 28 314 000 = 12 911 184 000`;
* `BottomCheck`, a finite computation: consecutive primes `p < q` with
  `10 726 905 041 < q ≤ 1.3 · 10^10` differ by at most 378, used on
  `]10 726 905 041, 12 911 184 000)`, since `378 · 28 314 000 < 10 726 905 041`.

`rs3_of_short` is a variant where the finite piece shrinks to `q ≤ 10 816 000 000`, with the
record 382 of A002386 as one more cited input.
-/
import Mathlib
import LeanLab.KadiriLumley2014.Statements
import LeanLab.GoldbachGaps.Sumset
import LeanLab.OeSHP2014.OeSHP2014U6818GapInput

namespace LeanLab.Routes.U1514
open LeanLab.KadiriLumley2014 LeanLab.GoldbachGaps.Sumset

/-- Ramaré-Saouter 2003 Theorem 3 in the lab's statement form, the type of
`RamareSaouter2003.theorem3` and the conclusion of `RamareSaouter2003.Smooth.theorem3_of_chain`. -/
def RS3 : Prop :=
  ∀ x : ℝ, 10726905041 < x → ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 28314000) < p ∧ (p : ℝ) ≤ x

/-- Every pair of consecutive primes `p < q` with `L < q ≤ Q` has `q - p ≤ G`. -/
def GapsIn (L Q G : ℕ) : Prop :=
  ∀ p q : ℕ, p.Prime → q.Prime → p < q → L < q → q ≤ Q →
    (∀ r, p < r → r < q → ¬ r.Prime) → q - p ≤ G

/-- Cited, OEIS A002386 and the searches of Nicely and Oliveira e Silva behind it: the record
gap 456 starts at 25 056 082 087 and the next record, 464, starts at 42 652 618 343, so every
gap between consecutive primes with upper prime at most `4.2 · 10^10` is at most 456. -/
def RecordGap456 : Prop := GapsIn 0 (42 * 10 ^ 9) 456

/-- Cited, OEIS A002386: the record 382 starts at 10 726 904 659 and the next record, 384,
starts at 20 678 048 297, so every gap with upper prime at most 20 678 048 297 is at most 382. -/
def RecordGap382 : Prop := GapsIn 0 20678048297 382

/-- Finite check, the named gap below the cited ranges, computed by
Routes/numerics/u1505_gapcheck.py and Routes/numerics/u1514_gapcheck.c, maximal gap 354.
Not a Lean result. -/
def BottomCheck : Prop := GapsIn 10726905041 (13 * 10 ^ 9) 378

/-- The shorter finite check used by `rs3_of_short`. Not a Lean result. -/
def BottomCheckShort : Prop := GapsIn 10726905041 10816000000 378

/-! ### Arithmetic of the ranges, PROVED by norm_num -/

theorem fit_1476 : (1476 : ℝ) * 28314000 = 41791464000 ∧ (41791464000 : ℝ) ≤ 4.18e10 := by
  norm_num

theorem fit_456 : (456 : ℝ) * 28314000 = 12911184000 ∧ (12911184000 : ℝ) ≤ 1.3e10 := by
  norm_num

theorem fit_378 : (378 : ℝ) * 28314000 < 10726905041 := by norm_num

/-- The record 382 ends exactly at Ramaré-Saouter's bound and does not fit there. -/
theorem record382_at_bound : 10726904659 + 382 = 10726905041 ∧
    (10726905041 : ℝ) < 382 * 28314000 := by norm_num

theorem fit_382 : (382 : ℝ) * 28314000 = 10815948000 := by norm_num

theorem kl_delta : (1 : ℝ) / 36082898 < 1 / 28314000 := by norm_num

theorem top_456 : (41791464000 : ℝ) + 1476 ≤ 42 * 10 ^ 9 ∧
    (12911184000 : ℝ) + 1476 ≤ 13 * 10 ^ 9 := by norm_num

/-! ### Consecutive primes around m -/

/-- Below a prime `q0 > m ≥ 2` the primes `p ≤ m < q` adjacent to `m` exist. PROVED. -/
theorem consecutive_around (m : ℕ) (hm : 2 ≤ m) (q0 : ℕ) (hq0 : q0.Prime) (hmq0 : m < q0) :
    ∃ p q : ℕ, p.Prime ∧ q.Prime ∧ p ≤ m ∧ m < q ∧ q ≤ q0 ∧
      ∀ r, p < r → r < q → ¬ r.Prime := by
  classical
  have hexq : ∃ q, q.Prime ∧ m < q := ⟨q0, hq0, hmq0⟩
  let q := Nat.find hexq
  have hq : q.Prime ∧ m < q := Nat.find_spec hexq
  have hqmin : ∀ r, r.Prime → m < r → q ≤ r := fun r hr hmr => Nat.find_min' hexq ⟨hr, hmr⟩
  have hexp : ∃ k, (m - k).Prime ∧ k ≤ m := ⟨m - 2, by
    rw [show m - (m - 2) = 2 by omega]; exact Nat.prime_two, by omega⟩
  let k := Nat.find hexp
  have hk : (m - k).Prime ∧ k ≤ m := Nat.find_spec hexp
  have hkmin : ∀ j, (m - j).Prime → j ≤ m → k ≤ j :=
    fun j hj hjm => Nat.find_min' hexp ⟨hj, hjm⟩
  refine ⟨m - k, q, hk.1, hq.1, by omega, hq.2, hqmin q0 hq0 hmq0, ?_⟩
  intro r hr1 hr2 hrp
  by_cases hrm : r ≤ m
  · have := hkmin (m - r) (by rw [show m - (m - r) = r by omega]; exact hrp) (by omega)
    omega
  · have := hqmin r hrp (by omega)
    omega

/-- A gap bound `G` on consecutive primes with `L < q ≤ Q` gives the Ramaré-Saouter interval at
`x` once `G · 28 314 000 ≤ x`, with `GapBound1476` only to keep the next prime below `Q`.
PROVED as an implication. -/
theorem interval_of_gaps (hG : GapBound1476) {L Q G : ℕ} (hgaps : GapsIn L Q G) {x : ℝ}
    (hLx : (L : ℝ) ≤ x) (h2 : 2 ≤ x) (hxQ : x + 1476 ≤ Q) (hQ : (Q : ℝ) ≤ 4 * 10 ^ 18)
    (hGx : (G : ℝ) * 28314000 ≤ x) :
    ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 28314000) < p ∧ (p : ℝ) ≤ x := by
  have hx0 : 0 ≤ x := by linarith
  set m := ⌊x⌋₊ with hmdef
  have hm_le : (m : ℝ) ≤ x := Nat.floor_le hx0
  have hm_lt : x < m + 1 := Nat.lt_floor_add_one x
  have hm2 : 2 ≤ m := by
    have h2' : ((2 : ℕ) : ℝ) ≤ x := by exact_mod_cast h2
    exact Nat.le_floor h2'
  have hLm : L ≤ m := Nat.le_floor hLx
  obtain ⟨q0, hq0, hmq0, hq0m⟩ := hG (m : ℝ) (by exact_mod_cast hm2) (by linarith)
  have hmq0' : m < q0 := by exact_mod_cast hmq0
  obtain ⟨p, q, hp, hq, hpm, hmq, hqq0, hcons⟩ := consecutive_around m hm2 q0 hq0 hmq0'
  have hqQ : q ≤ Q := by
    have : (q : ℝ) ≤ Q := by
      have : (q : ℝ) ≤ q0 := by exact_mod_cast hqq0
      linarith
    exact_mod_cast this
  have hpq : p < q := by omega
  have hgap := hgaps p q hp hq hpq (by omega) hqQ hcons
  refine ⟨p, hp, ?_, ?_⟩
  · have hqp : (q : ℝ) ≤ p + G := by
      have : q ≤ p + G := by omega
      exact_mod_cast this
    have hmq' : (m : ℝ) + 1 ≤ q := by exact_mod_cast hmq
    have hdiv : (G : ℝ) ≤ x / 28314000 := by
      rw [le_div_iff₀ (by norm_num)]; exact hGx
    have e : x * (1 - 1 / 28314000) = x - x / 28314000 := by ring
    rw [e]
    linarith
  · have : (p : ℝ) ≤ m := by exact_mod_cast hpm
    linarith

/-- The Kadiri-Lumley row covers the tail. PROVED as an implication. -/
theorem tail_of_kl (hKL : KLRow (4 * 10 ^ 18) 36082898) {x : ℝ} (hx : 4 * 10 ^ 18 < x) :
    ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 28314000) < p ∧ (p : ℝ) ≤ x := by
  obtain ⟨p, hp, hl, hu⟩ := hKL x hx
  refine ⟨p, hp, ?_, hu.le⟩
  have hc : (0 : ℝ) < 1 / 28314000 - 1 / 36082898 := by norm_num
  have hx0 : 0 < x := by linarith
  have : x * (1 - 1 / 28314000) < (1 - 1 / 36082898) * x := by nlinarith
  linarith

/-- `GapBound1476` covers `[41 791 464 000, 4 · 10^18]`. PROVED as an implication. -/
theorem middle_of_1476 (hG : GapBound1476) {x : ℝ} (hlo : 41791464000 ≤ x)
    (hhi : x ≤ 4 * 10 ^ 18) :
    ∃ p : ℕ, p.Prime ∧ x * (1 - 1 / 28314000) < p ∧ (p : ℝ) ≤ x := by
  obtain ⟨q, hq, hl, hu⟩ := hG (x - 1476) (by linarith) (by linarith)
  refine ⟨q, hq, ?_, by linarith⟩
  have hdiv : (1476 : ℝ) ≤ x / 28314000 := by
    rw [le_div_iff₀ (by norm_num)]; linarith
  have e : x * (1 - 1 / 28314000) = x - x / 28314000 := by ring
  rw [e]
  linarith

/-- **Headline.** Ramaré-Saouter Theorem 3 CONDITIONAL ON `KLRow (4 · 10^18) 36082898`,
`GapBound1476`, `RecordGap456` and `BottomCheck`. -/
theorem rs3_of_inputs (hKL : KLRow (4 * 10 ^ 18) 36082898) (hG : GapBound1476)
    (h456 : RecordGap456) (hB : BottomCheck) : RS3 := by
  intro x hx
  rcases lt_or_ge (4 * 10 ^ 18 : ℝ) x with h1 | h1
  · exact tail_of_kl hKL h1
  rcases le_or_gt (41791464000 : ℝ) x with h2 | h2
  · exact middle_of_1476 hG h2 h1
  rcases le_or_gt (12911184000 : ℝ) x with h3 | h3
  · exact interval_of_gaps hG h456 (by norm_num; linarith) (by linarith)
      (by push_cast; linarith) (by norm_num) (by push_cast; linarith)
  · exact interval_of_gaps hG hB (by push_cast; linarith) (by linarith)
      (by push_cast; linarith) (by norm_num) (by push_cast; linarith)

/-- The same with OeSHP's maximal gap statement `MaxGap1476` in place of `GapBound1476`,
through `OeSHP2014.GapInput.gapBound1476_of_maxGap`. CONDITIONAL ON `KLRow (4 · 10^18) 36082898`,
`MaxGap1476`, `RecordGap456` and `BottomCheck`. -/
theorem rs3_of_maxGap (hKL : KLRow (4 * 10 ^ 18) 36082898)
    (hM : LeanLab.OeSHP2014.GapInput.MaxGap1476) (h456 : RecordGap456) (hB : BottomCheck) :
    RS3 :=
  rs3_of_inputs hKL (LeanLab.OeSHP2014.GapInput.gapBound1476_of_maxGap hM) h456 hB

/-- Variant with a 25 times shorter finite piece. CONDITIONAL ON `KLRow (4 · 10^18) 36082898`,
`GapBound1476`, `RecordGap456`, `RecordGap382` and `BottomCheckShort`. -/
theorem rs3_of_short (hKL : KLRow (4 * 10 ^ 18) 36082898) (hG : GapBound1476)
    (h456 : RecordGap456) (h382 : RecordGap382) (hB : BottomCheckShort) : RS3 := by
  intro x hx
  rcases lt_or_ge (4 * 10 ^ 18 : ℝ) x with h1 | h1
  · exact tail_of_kl hKL h1
  rcases le_or_gt (41791464000 : ℝ) x with h2 | h2
  · exact middle_of_1476 hG h2 h1
  rcases le_or_gt (20678040000 : ℝ) x with h3 | h3
  · exact interval_of_gaps hG h456 (by norm_num; linarith) (by linarith)
      (by push_cast; linarith) (by norm_num) (by push_cast; linarith)
  rcases le_or_gt (10815948000 : ℝ) x with h4 | h4
  · exact interval_of_gaps hG h382 (by norm_num; linarith) (by linarith)
      (by push_cast; linarith) (by norm_num) (by push_cast; linarith)
  · exact interval_of_gaps hG hB (by push_cast; linarith) (by linarith)
      (by push_cast; linarith) (by norm_num) (by push_cast; linarith)

/-- `BottomCheck` implies `BottomCheckShort`: the short piece is a sub-range. PROVED. -/
theorem bottomShort_of_bottom (h : BottomCheck) : BottomCheckShort :=
  fun p q hp hq hpq hL hQ hc => h p q hp hq hpq hL (by omega) hc

/-- `RecordGap456` does not give `RecordGap382`, but `RecordGap382` restricts `RecordGap456`
only on its own range; the two are separate cited rows. Sanity: both are about the same
`GapsIn` shape, and `GapsIn` is monotone in `Q` and `G`. PROVED. -/
theorem gapsIn_mono {L Q Q' G G' : ℕ} (h : GapsIn L Q G) (hQ : Q' ≤ Q) (hG : G ≤ G') :
    GapsIn L Q' G' :=
  fun p q hp hq hpq hL hq' hc => le_trans (h p q hp hq hpq hL (le_trans hq' hQ) hc) hG

end LeanLab.Routes.U1514
