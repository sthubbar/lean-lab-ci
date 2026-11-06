import LeanLab.Ricci1937.Decomp338b

/-!
Ricci 1937, actual normalized boundary tail.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary actual normalized tail bound for second memoir page 99 formula 18.3.
Under the cumulative mass budgets, the normalized retained main sum loses at most
the explicit shifted factorial tail times the uniform endpoint correction. -/
lemma decomp338_pair_normalized_tail (h w : ℕ) (heven : Even h)
    (c : ℕ → ℕ) (hc : Antitone c) (hw : c 0 ≤ w) (s n Y : ℕ)
    (hY : 4 ≤ Y) (hbottom : Y ≤ c (s + n))
    (hmass : ∀ i < n,
      (∑ p ∈ (Ioc (c (s + i + 1)) w).filter Nat.Prime, nuN h p) ≤
        (((s + i + 2 : ℕ) : ℝ) + 1) / 2) :
    let E := fun i => ∑ S ∈ decomp305PrimeFamily w c (s + i),
      (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p
    let D := fun i => ∏ p ∈ (Ioc (c (s + i)) w).filter Nat.Prime, (1 - nuN h p)
    E 0 / D 0 - exp (8 / (Y : ℝ)) *
      (∑ i ∈ range n, decomp305CrudeTerm (s + i + 2)) ≤ E n / D n := by
  let E := fun i => ∑ S ∈ decomp305PrimeFamily w c (s + i),
    (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p
  let D := fun i => ∏ p ∈ (Ioc (c (s + i)) w).filter Nat.Prime, (1 - nuN h p)
  let B := fun i => (Ioc (c (s + i + 1)) (c (s + i))).filter Nat.Prime
  let v := fun i => ∏ p ∈ B i, (1 - nuN h p)
  let Φ := fun i => ∑ S ∈ decomp305PrimeFamily w c (s + i),
    (∏ p ∈ S, nuN h p) * LeanLab.PNTSieve.Bonferroni.esymm (nuN h) (B i)
      (2 * (s + i + 1) + 1 - S.card + 1)
  have hD (i : ℕ) : 0 < D i := by
    apply prod_pos
    intro p hp
    exact sub_pos.mpr (nuN_lt_one heven (mem_filter.mp hp).2)
  have hprefix (i : ℕ) : D i = D 0 * ∏ j ∈ range i, v j := by
    simpa [D, v, B] using decomp305_prime_product_iteration (nuN h) w c hc hw s i
  have hraw := decomp305_pair_prime_normalized h w heven c hc hw s n
  change E 0 - (∑ i ∈ range n, Φ i / (∏ j ∈ range (i + 1), v j)) ≤
    E n / (∏ j ∈ range n, v j) at hraw
  have hnorm : E 0 / D 0 - (∑ i ∈ range n, Φ i / D (i + 1)) ≤ E n / D n := by
    calc
      _ = (E 0 - (∑ i ∈ range n, Φ i / (∏ j ∈ range (i + 1), v j))) / D 0 := by
        rw [sub_div]
        congr 1
        rw [sum_div]
        apply sum_congr rfl
        intro i hi
        rw [div_div, mul_comm (∏ j ∈ range (i + 1), v j), ← hprefix (i + 1)]
      _ ≤ (E n / (∏ j ∈ range n, v j)) / D 0 :=
        div_le_div_of_nonneg_right hraw (hD 0).le
      _ = E n / D n := by
        rw [div_div, mul_comm (∏ j ∈ range n, v j), ← hprefix n]
  have hsum : (∑ i ∈ range n, Φ i / D (i + 1)) ≤
      exp (8 / (Y : ℝ)) * ∑ i ∈ range n, decomp305CrudeTerm (s + i + 2) := by
    rw [mul_sum]
    apply sum_le_sum
    intro i hi
    have hin : i < n := mem_range.mp hi
    have hy : Y ≤ c (s + i + 1) := hbottom.trans (hc (by omega : s + i + 1 ≤ s + n))
    have hbound := decomp305_pair_boundary_normalized h w c hc (s + i)
      ((hc (Nat.zero_le _)).trans hw) (by omega) (hmass i hin)
    change Φ i / D (i + 1) ≤ exp (8 / (c (s + i + 1) : ℝ)) *
      decomp305CrudeTerm (s + i + 2) at hbound
    apply hbound.trans
    apply mul_le_mul_of_nonneg_right
    · apply exp_le_exp.mpr
      exact div_le_div_of_nonneg_left (by norm_num) (by exact_mod_cast (by omega : 0 < Y))
        (by exact_mod_cast hy)
    · unfold decomp305CrudeTerm
      positivity
  change E 0 / D 0 - exp (8 / (Y : ℝ)) *
    (∑ i ∈ range n, decomp305CrudeTerm (s + i + 2)) ≤ E n / D n
  linarith


/-- Auxiliary summability needed to compare finite actual tails with second memoir page 99 formula 18.3.
The existing consecutive ratio bound gives the complete later shifted factorial tail. -/
lemma decomp338_crude_tail_summable : Summable (fun k : ℕ => decomp305CrudeTerm (21 + k)) := by
  have hpos (b : ℕ) : 0 ≤ decomp305CrudeTerm b := by unfold decomp305CrudeTerm; positivity
  apply summable_of_ratio_norm_eventually_le (r := (0.86 : ℝ)) (by norm_num)
  apply Eventually.of_forall
  intro k
  rw [Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg (hpos (21 + (k + 1))), abs_of_nonneg (hpos (21 + k))]
  simpa only [Nat.add_assoc] using decomp305_crude_ratio (b := 21 + k) (by omega)

/-- Auxiliary positive normalized actual main sum for second memoir page 99 formula 18.3.
A normalized twenty block head at least 0.04 survives the full later crude tail.
The residual endpoint bound one hundred is auxiliary. -/
lemma decomp338_pair_normalized_positive (h w : ℕ) (heven : Even h)
    (c : ℕ → ℕ) (hc : Antitone c) (hw : c 0 ≤ w) (n Y : ℕ)
    (hY : 100 ≤ Y) (hbottom : Y ≤ c (19 + n))
    (hmass : ∀ i < n,
      (∑ p ∈ (Ioc (c (19 + i + 1)) w).filter Nat.Prime, nuN h p) ≤
        (((19 + i + 2 : ℕ) : ℝ) + 1) / 2)
    (hhead : (0.04 : ℝ) ≤
      (∑ S ∈ decomp305PrimeFamily w c 19,
        (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p) /
      (∏ p ∈ (Ioc (c 19) w).filter Nat.Prime, (1 - nuN h p))) :
    (0.02 : ℝ) ≤
      (∑ S ∈ decomp305PrimeFamily w c (19 + n),
        (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN h p) /
      (∏ p ∈ (Ioc (c (19 + n)) w).filter Nat.Prime, (1 - nuN h p)) := by
  have hraw := decomp338_pair_normalized_tail h w heven c hc hw 19 n Y (by omega) hbottom hmass
  dsimp only at hraw
  have he008 : exp (0.08 : ℝ) ≤ 1.1 := ricci_exp_upper_small
    (by norm_num) (by norm_num) (by norm_num [sum_range_succ, Nat.factorial])
  have he : exp (8 / (Y : ℝ)) ≤ 1.1 := by
    apply le_trans _ he008
    apply exp_le_exp.mpr
    have hYR : (100 : ℝ) ≤ Y := by exact_mod_cast hY
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < Y)]
    linarith
  have htail : (∑ i ∈ range n, decomp305CrudeTerm (19 + i + 2)) < 0.018 := by
    have hh := decomp338_crude_tail_summable.sum_le_tsum (range n)
      (fun i _ => show 0 ≤ decomp305CrudeTerm (21 + i) by unfold decomp305CrudeTerm; positivity)
    have hindex : (∑ i ∈ range n, decomp305CrudeTerm (19 + i + 2)) =
        ∑ i ∈ range n, decomp305CrudeTerm (21 + i) := by
      apply sum_congr rfl
      intro i hi
      congr 1
      omega
    rw [hindex]
    exact hh.trans_lt decomp305_crude_tail_lt
  have htail0 : 0 ≤ ∑ i ∈ range n, decomp305CrudeTerm (19 + i + 2) := by
    apply sum_nonneg
    intro i hi
    unfold decomp305CrudeTerm
    positivity
  have hmul := mul_le_mul he htail.le htail0 (by norm_num : (0 : ℝ) ≤ 1.1)
  norm_num at hmul
  norm_num only [Nat.add_zero] at hraw
  linarith

end
end LeanLab.Ricci1937
