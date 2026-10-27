/-
# Pintz and Althöfer 2026, (4.15): the gcd sum

Unit U-1126, T2 FRONTIER, idea I-0080, run 20261019T2303Z-16260.

arXiv 2610.15559v1, line after (4.15): "use |c_q(n)| ≤ (q, n), q/φ(q) ≪_δ q^δ, and
(q, n) = Σ_{d | (q,n)} φ(d)". The last identity gives the sum step:

* `sum_gcd_div_totient_le`: for n ≥ 1 and every P,
  Σ_{1 ≤ q ≤ P} (q, n)/φ(q) ≤ τ(n) · Σ_{1 ≤ m ≤ P} 1/φ(m),
  by (q, n) = Σ_{d | (q,n)} φ(d), swapping sums, q = dm and φ(d)φ(m) ≤ φ(dm).

With |c_q(n)| ≤ (q,n) τ((q,n)), PintzAlthofer2026Ram.lean, and q/φ(q) ≤ e(1 + ω(q)),
HeathBrown1985/Elementary.lean, this is the core of Σ_{q≤P} q|c_q(n)|/φ(q)² ≪ X^η.

AI wrote this Lean code. Binary Goldbach is OPEN.
-/
import Mathlib

namespace LeanLab.ExceptionalSet.PintzAlthofer2026Gcd

open Finset

/-- Inner sum: for `d ≥ 1`, `Σ_{q ≤ P, d | q} φ(d)/φ(q) ≤ Σ_{m ≤ P} 1/φ(m)`. -/
lemma inner_le (d P : ℕ) (hd : 1 ≤ d) :
    ∑ q ∈ (Icc 1 P).filter (d ∣ ·), (Nat.totient d : ℝ) / Nat.totient q ≤
      ∑ m ∈ Icc 1 P, (1 : ℝ) / Nat.totient m := by
  set S := (Icc 1 P).filter (d ∣ ·)
  have step1 : ∀ q ∈ S, (Nat.totient d : ℝ) / Nat.totient q ≤ 1 / Nat.totient (q / d) := by
    intro q hq
    simp only [S, mem_filter, mem_Icc] at hq
    obtain ⟨⟨hq1, _⟩, hdq⟩ := hq
    obtain ⟨m, rfl⟩ := hdq
    have hm : 1 ≤ m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · subst h; simp at hq1
      · exact h
    rw [Nat.mul_div_cancel_left m (by omega)]
    have hφd : (0 : ℝ) < Nat.totient d := by exact_mod_cast Nat.totient_pos.2 (by omega)
    have hφm : (0 : ℝ) < Nat.totient m := by exact_mod_cast Nat.totient_pos.2 (by omega)
    have hsup : (Nat.totient d : ℝ) * Nat.totient m ≤ Nat.totient (d * m) := by
      exact_mod_cast Nat.totient_super_multiplicative d m
    have hφdm : (0 : ℝ) < Nat.totient (d * m) := lt_of_lt_of_le (by positivity) hsup
    rw [div_le_div_iff₀ hφdm hφm]
    linarith
  have hinj : Set.InjOn (fun q => q / d) S := by
    intro a ha b hb hab
    simp only [S, coe_filter, Set.mem_ofPred_eq] at ha hb
    obtain ⟨_, ⟨a', rfl⟩⟩ := ha
    obtain ⟨_, ⟨b', rfl⟩⟩ := hb
    simp only at hab
    rw [Nat.mul_div_cancel_left _ (by omega), Nat.mul_div_cancel_left _ (by omega)] at hab
    rw [hab]
  have hsub : S.image (fun q => q / d) ⊆ Icc 1 P := by
    intro m hm
    simp only [mem_image, S, mem_filter, mem_Icc] at hm
    obtain ⟨q, ⟨⟨hq1, hqP⟩, ⟨k, rfl⟩⟩, rfl⟩ := hm
    rw [Nat.mul_div_cancel_left _ (by omega)]
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp at hq1
    · refine mem_Icc.2 ⟨h, le_trans ?_ hqP⟩
      exact Nat.le_mul_of_pos_left k (by omega)
  calc ∑ q ∈ S, (Nat.totient d : ℝ) / Nat.totient q ≤ ∑ q ∈ S, (1 : ℝ) / Nat.totient (q / d) :=
        sum_le_sum step1
    _ = ∑ m ∈ S.image (fun q => q / d), (1 : ℝ) / Nat.totient m := (sum_image (f := fun m => (1 : ℝ) / Nat.totient m) hinj).symm
    _ ≤ ∑ m ∈ Icc 1 P, (1 : ℝ) / Nat.totient m :=
        sum_le_sum_of_subset_of_nonneg hsub fun _ _ _ => by positivity

/-- **The gcd sum of (4.15)**: `Σ_{q≤P} (q, n)/φ(q) ≤ τ(n) Σ_{m≤P} 1/φ(m)` for `n ≥ 1`. -/
theorem sum_gcd_div_totient_le (n P : ℕ) (hn : 1 ≤ n) :
    ∑ q ∈ Icc 1 P, (Nat.gcd q n : ℝ) / Nat.totient q ≤
      (n.divisors.card : ℝ) * ∑ m ∈ Icc 1 P, (1 : ℝ) / Nat.totient m := by
  have hexp : ∀ q ∈ Icc 1 P, (Nat.gcd q n : ℝ) / Nat.totient q =
      ∑ d ∈ n.divisors, if d ∣ q then (Nat.totient d : ℝ) / Nat.totient q else 0 := by
    intro q hq
    have hq1 : 1 ≤ q := (mem_Icc.1 hq).1
    have hg : (Nat.gcd q n : ℝ) = ∑ d ∈ (Nat.gcd q n).divisors, (Nat.totient d : ℝ) := by
      exact_mod_cast (Nat.sum_totient (Nat.gcd q n)).symm
    rw [hg, sum_div, ← sum_filter]
    apply sum_congr _ (fun _ _ => rfl)
    ext d
    simp only [Nat.mem_divisors, mem_filter, Nat.dvd_gcd_iff]
    constructor
    · rintro ⟨⟨h1, h2⟩, _⟩; exact ⟨⟨h2, by omega⟩, h1⟩
    · rintro ⟨⟨h2, _⟩, h1⟩
      exact ⟨⟨h1, h2⟩, (Nat.gcd_pos_of_pos_left n (by omega)).ne'⟩
  rw [sum_congr rfl hexp, sum_comm]
  have hin : ∀ d ∈ n.divisors, (∑ q ∈ Icc 1 P, if d ∣ q then (Nat.totient d : ℝ) / Nat.totient q
      else 0) ≤ ∑ m ∈ Icc 1 P, (1 : ℝ) / Nat.totient m := by
    intro d hd
    rw [← sum_filter]
    exact inner_le d P (Nat.pos_of_mem_divisors hd)
  calc _ ≤ ∑ d ∈ n.divisors, ∑ m ∈ Icc 1 P, (1 : ℝ) / Nat.totient m := sum_le_sum hin
    _ = _ := by rw [sum_const, nsmul_eq_mul]

/-- Vacuity: `n = 1`, `P = 3`: `Σ 1/φ(q) ≤ 1 · Σ 1/φ(m)`, an equality. -/
example : ∑ q ∈ Icc 1 3, (Nat.gcd q 1 : ℝ) / Nat.totient q ≤
    ((1 : ℕ).divisors.card : ℝ) * ∑ m ∈ Icc 1 3, (1 : ℝ) / Nat.totient m :=
  sum_gcd_div_totient_le 1 3 le_rfl

end LeanLab.ExceptionalSet.PintzAlthofer2026Gcd
