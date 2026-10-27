/-
AI-written Lean code, Claude, 2026-10-21, run 20261021T1103Z-29422, unit U-1396.
P0048 Dudek-Dunn, arXiv 2602.22720: the lab's cited `DDLemma21All.RSHyp`, Lemma 2.1 Case 1's
Rosser-Schoenfeld input, derived from Rosser-Schoenfeld 1962 Theorem 5 itself.
Source: J. B. Rosser and L. Schoenfeld, Approximate formulas for some functions of prime
numbers, Illinois J. Math. 6 (1962), Theorem 5, p. 70:
* (3.17)  `log log x + B - 1/(2 log² x) < Σ_{p ≤ x} 1/p`  for `1 < x`;
* (3.18)  `Σ_{p ≤ x} 1/p < log log x + B + 1/(2 log² x)`  for `286 ≤ x`.
RSHyp needs both halves: (3.18) at `z` and (3.17) at `w` from the left. For every value of the
parameter `B`, with the same `B` in both, no numeric side condition is needed.
Goldbach is open.
-/
import Mathlib
import LeanLab.AlmostPrimes.RS1962

open Real Finset Filter Topology
open LeanLab.AlmostPrimes LeanLab.AlmostPrimes.DDLemma21 LeanLab.AlmostPrimes.DDMain
open LeanLab.AlmostPrimes.RS1962

noncomputable section
namespace LeanLab.AlmostPrimes.RSHypFrom318

/-- **Rosser-Schoenfeld 1962, Theorem 5, eq (3.17), p. 70.**
Plain math: for every real `x > 1`, `log log x + B - 1/(2 log² x) < Σ_{p ≤ x} 1/p`.
Quoted: "log log x + B - 1/(2 log² x) < Σ_{p ≤ x} 1/p, if 1 < x", with
`B = 0.26149 72128 47643`, their (2.10). Here `B` is a parameter, as in `RS1962.RS318`. Cited. -/
def RS317 (B : ℝ) : Prop := ∀ x : ℝ, 1 < x →
  log (log x) + B - 1 / (2 * log x ^ 2) < primeRecipSum x

/-- The primes `p ≤ ⌊z⌋` with `p < w`. -/
def lowSet (w z : ℝ) : Finset ℕ := (range (⌊z⌋₊ + 1)).filter (fun p => p.Prime ∧ (p : ℝ) < w)

/-- `Σ_{p < w} 1/p + Σ_{w ≤ p < z} 1/p ≤ Σ_{p ≤ z} 1/p`. -/
lemma split_le (w z : ℝ) (hz : 0 ≤ z) :
    ∑ p ∈ lowSet w z, (1 : ℝ) / p + ∑ p ∈ primesIn w z, (1 : ℝ) / p ≤ primeRecipSum z := by
  have hdisj : Disjoint (lowSet w z) (primesIn w z) := by
    rw [Finset.disjoint_left]
    intro p hp hq
    simp only [lowSet, primesIn, mem_filter] at hp hq
    linarith [hp.2.2, hq.2.2.1]
  rw [← sum_union hdisj]
  apply sum_le_sum_of_subset_of_nonneg _ (fun p _ _ => by positivity)
  intro p hp
  rcases mem_union.1 hp with h | h
  · simp only [lowSet, mem_filter] at h
    exact mem_filter.2 ⟨h.1, h.2.1⟩
  · simp only [primesIn, mem_filter, mem_range] at h
    refine mem_filter.2 ⟨?_, h.2.1⟩
    rw [mem_range, Nat.lt_succ_iff]
    exact Nat.le_floor h.2.2.2.le

/-- For `1 < x < w ≤ z`, `Σ_{p ≤ x} 1/p ≤ Σ_{p < w} 1/p`. -/
lemma le_low {w z x : ℝ} (hx0 : 0 ≤ x) (hxw : x < w) (hwz : w ≤ z) :
    primeRecipSum x ≤ ∑ p ∈ lowSet w z, (1 : ℝ) / p := by
  apply sum_le_sum_of_subset_of_nonneg _ (fun p _ _ => by positivity)
  intro p hp
  simp only [mem_filter, mem_range, Nat.lt_succ_iff] at hp
  have hpx : (p : ℝ) ≤ x := (Nat.le_floor_iff hx0).1 hp.1
  refine mem_filter.2 ⟨?_, hp.2, by linarith⟩
  rw [mem_range, Nat.lt_succ_iff]
  exact Nat.le_floor (by linarith)

/-- **(3.17) at `w` from the left**: `log log w + B - 1/(2 log² w) ≤ Σ_{p < w} 1/p` for `w > 1`,
the limit of (3.17) at `x → w⁻`. -/
lemma low_bound {B w z : ℝ} (h317 : RS317 B) (hw : 1 < w) (hwz : w ≤ z) :
    log (log w) + B - 1 / (2 * log w ^ 2) ≤ ∑ p ∈ lowSet w z, (1 : ℝ) / p := by
  set f : ℝ → ℝ := fun x => log (log x) + B - 1 / (2 * log x ^ 2) with hf
  have hlw : log w ≠ 0 := (log_pos hw).ne'
  have hw0 : w ≠ 0 := by linarith
  have hcont : ContinuousAt f w := by
    have h1 : ContinuousAt log w := continuousAt_log hw0
    have h2 : ContinuousAt (fun x => log (log x)) w := h1.log hlw
    have h3 : ContinuousAt (fun x => 2 * log x ^ 2) w := continuousAt_const.mul (h1.pow 2)
    have h4 : ContinuousAt (fun x => 1 / (2 * log x ^ 2)) w :=
      continuousAt_const.div h3 (by positivity)
    exact (h2.add continuousAt_const).sub h4
  have ht : Tendsto f (𝓝[<] w) (𝓝 (f w)) := hcont.tendsto.mono_left nhdsWithin_le_nhds
  have hev : ∀ᶠ x in 𝓝[<] w, f x ≤ ∑ p ∈ lowSet w z, (1 : ℝ) / p := by
    filter_upwards [Ioo_mem_nhdsLT hw] with x hx
    exact le_trans (h317 x hx.1).le (le_low (by linarith [hx.1]) hx.2 hwz)
  exact le_of_tendsto ht hev

/-- **`RSHyp` from Rosser-Schoenfeld Theorem 5**, (3.17) and (3.18) with the same `B`.
PROVED from the two cited Props, for every `B`. -/
theorem RSHyp_of_RS317_RS318 {B : ℝ} (h317 : RS317 B) (h318 : RS318 B) :
    DDLemma21All.RSHyp := by
  intro w z hw hwz
  have hw1 : (1 : ℝ) < w := by linarith
  have hz : (286 : ℝ) ≤ z := by linarith
  have hlw : 0 < log w := log_pos hw1
  have hlz : 0 < log z := log_pos (by linarith)
  have hsplit := split_le w z (by linarith)
  have hlow := low_bound h317 hw1 hwz.le
  have hup := h318 z hz
  have hdiv : log (log z / log w) = log (log z) - log (log w) := log_div hlz.ne' hlw.ne'
  have ez : 1 / (2 * log z ^ 2) = (1 / log z ^ 2) / 2 := by field_simp
  have ew : 1 / (2 * log w ^ 2) = (1 / log w ^ 2) / 2 := by field_simp
  rw [ez] at hup
  rw [ew] at hlow
  rw [hdiv]
  linarith

/-- **Theorem 3.3 for `N ≥ 10^200`**, Dudek-Dunn. CONDITIONAL ON `RS317 B`, `RS318 B`,
`RS320true B'` with `B' < 0.2614973`, and `SelbergThm13` only. -/
theorem theorem3_3_large_of_RS5 {B B' : ℝ} (h317 : RS317 B) (h318 : RS318 B)
    (hB' : B' < 0.2614973) (h320 : RS320true B') (hSel : SelbergThm13)
    (N : ℕ) (hN : (10 : ℝ) ^ 200 ≤ N) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ N = a + b ∧
      (Even N → bigOmega (a * b) ≤ 39) ∧ bigOmega (a * b) ≤ 40 :=
  theorem3_3_large_of_RS3 (RSHyp_of_RS317_RS318 h317 h318) hB' h320 hSel N hN

/-- **Theorem 3.3 for `N ≥ 10^200` from Theorem 5 alone**: `RSRecip` from (3.18) too.
CONDITIONAL ON `RS317 B`, `RS318 B` with `B < 0.2614973`, and `SelbergThm13` only. -/
theorem theorem3_3_large_of_thm5 {B : ℝ} (hB : B < 0.2614973) (h317 : RS317 B)
    (h318 : RS318 B) (hSel : SelbergThm13) (N : ℕ) (hN : (10 : ℝ) ^ 200 ≤ N) :
    ∃ a b : ℕ, 0 < a ∧ 0 < b ∧ N = a + b ∧
      (Even N → bigOmega (a * b) ≤ 39) ∧ bigOmega (a * b) ≤ 40 :=
  DDNathanson.theorem3_3_large_of_RS (RSHyp_of_RS317_RS318 h317 h318)
    (RSRecip_of_RS318 hB h318) hSel N hN

/-- **Lemma 2.1, K = 3, every real `z > w ≥ 2`**, condition (2) of Theorem 1.3.
CONDITIONAL ON `RS317 B` and `RS318 B` only. -/
theorem dimCond_of_thm5 {B : ℝ} (h317 : RS317 B) (h318 : RS318 B) (N : ℕ) : DimCond N 3 :=
  dimCond_of_RS (RSHyp_of_RS317_RS318 h317 h318) N

/-! ### Vacuity -/

/-- **Vacuity of (3.17)** at `x = 2`, `B = 0.2614972`: `1/2 > log log 2 + B - 1/(2 log² 2)`,
about `-0.79`, since `log log 2 < 0`. -/
theorem rs317_instance_two :
    (1 : ℝ) < 2 ∧ log (log 2) + 0.2614972 - 1 / (2 * log 2 ^ 2) < primeRecipSum 2 := by
  refine ⟨by norm_num, ?_⟩
  rw [primeRecipSum_two]
  have hu := Real.log_two_lt_d9
  have hl := Real.log_two_gt_d9
  have hneg : log (log 2) < 0 := log_neg (by linarith) (by linarith)
  have hp : 0 ≤ 1 / (2 * log 2 ^ 2) := by positivity
  linarith

end LeanLab.AlmostPrimes.RSHypFrom318

end
