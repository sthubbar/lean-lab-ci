import LeanLab.Ricci1937.Decomp338d

/-!
Ricci 1937, actual normalized twenty block head.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary cumulative mass limit for second memoir pages 109 to 111.
The individual block mass limits sum to the mass of the full retained interval. -/
lemma decomp338_retained_mass_tendsto (h w : ℕ → ℕ) (c : ℕ → ℕ → ℕ)
    (hc : ∀ q, Antitone (c q)) (hw : ∀ q, c q 0 ≤ w q)
    (ht : ∀ i, Tendsto
      (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, nuN (h q) p)
      atTop (nhds ((decomp305HeadMass i : ℝ) / 100))) (n : ℕ) :
    Tendsto (fun q => ∑ p ∈ (Ioc (c q n) (w q)).filter Nat.Prime, nuN (h q) p)
      atTop (nhds (∑ i ∈ range (n + 1), (decomp305HeadMass i : ℝ) / 100)) := by
  have heq (q : ℕ) :
      (∑ i ∈ range (n + 1), ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, nuN (h q) p) =
        ∑ p ∈ (Ioc (c q n) (w q)).filter Nat.Prime, nuN (h q) p := by
    let e : ℕ → ℕ := fun i => match i with
      | 0 => w q
      | j + 1 => c q j
    have he : Antitone e := by
      apply antitone_nat_of_succ_le
      intro i
      cases i with
      | zero => exact hw q
      | succ i => exact hc q (by omega : i ≤ i + 1)
    have hh := decomp338_prime_mass_telescopes (nuN (h q)) e he (n + 1)
    calc
      _ = ∑ i ∈ range (n + 1), ∑ p ∈ (Ioc (e (i + 1)) (e i)).filter Nat.Prime,
          nuN (h q) p := by
        apply sum_congr rfl
        intro i hi
        cases i <;> rfl
      _ = _ := hh
  have hh := tendsto_finsetSum (range (n + 1)) (fun i _ => ht i)
  exact hh.congr' (Eventually.of_forall heq)

/-- Auxiliary normalized finite head limit for second memoir pages 99 and 111.
Any actual prime blocks with the printed moment limits have normalized twenty block head eventually above 0.04. -/
lemma decomp338_normalized_head_of_moments (h w : ℕ → ℕ) (c : ℕ → ℕ → ℕ)
    (heven : ∀ q, Even (h q)) (hc : ∀ q, Antitone (c q)) (hw : ∀ q, c q 0 ≤ w q)
    (ht : ∀ i, Tendsto
      (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, nuN (h q) p)
      atTop (nhds ((decomp305HeadMass i : ℝ) / 100)))
    (hsq : ∀ i, Tendsto
      (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, (nuN (h q) p) ^ 2)
      atTop (nhds 0)) :
    ∀ᶠ q : ℕ in atTop, (0.04 : ℝ) <
      (∑ S ∈ decomp305PrimeFamily (w q) (c q) 19,
        (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN (h q) p) /
      (∏ p ∈ (Ioc (c q 19) (w q)).filter Nat.Prime, (1 - nuN (h q) p)) := by
  let E := fun q => ∑ S ∈ decomp305PrimeFamily (w q) (c q) 19,
    (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN (h q) p
  let M := fun q => ∑ p ∈ (Ioc (c q 19) (w q)).filter Nat.Prime, nuN (h q) p
  let D := fun q => ∏ p ∈ (Ioc (c q 19) (w q)).filter Nat.Prime, (1 - nuN (h q) p)
  have hE := decomp338_prime_head_tendsto (fun q => nuN (h q)) w c hc hw
    (fun q => nuN_nonneg (h q)) ht hsq 19
  change Tendsto E atTop (nhds (decomp305HeadValue 20 : ℝ)) at hE
  have hM : Tendsto M atTop (nhds (10.48 : ℝ)) := by
    have hh := decomp338_retained_mass_tendsto h w c hc hw ht 19
    have hs := decomp305_head_mass_sum (b := 20) (by norm_num)
    norm_num at hs
    change Tendsto M atTop (nhds (∑ i ∈ range 20, (decomp305HeadMass i : ℝ) / 100)) at hh
    rw [hs] at hh
    convert hh using 1 <;> norm_num
  have hD (q : ℕ) : 0 < D q := by
    apply prod_pos
    intro p hp
    exact sub_pos.mpr (nuN_lt_one (heven q) (mem_filter.mp hp).2)
  have hprod (q : ℕ) : D q ≤ exp (-M q) := by
    calc
      _ ≤ ∏ p ∈ (Ioc (c q 19) (w q)).filter Nat.Prime, exp (-nuN (h q) p) := by
        apply prod_le_prod₀
        · intro p hp
          exact (sub_pos.mpr (nuN_lt_one (heven q) (mem_filter.mp hp).2)).le
        · intro p hp
          exact one_sub_le_exp_neg _
      _ = exp (-M q) := by rw [← exp_sum, sum_neg_distrib]
  have hval : (13 / 10000000 : ℝ) < (decomp305HeadValue 20 : ℝ) := by
    have hh : ((13 / 10000000 : ℚ) : ℝ) < (decomp305HeadValue 20 : ℝ) :=
      Rat.cast_lt.mpr decomp305_head20_positive
    norm_num at hh
    exact hh
  have he10 : (2.718 : ℝ) ^ (10 : ℕ) ≤ exp (10 : ℝ) := by
    calc
      _ ≤ exp (1 : ℝ) ^ (10 : ℕ) :=
        pow_le_pow_left₀ (by norm_num) (by linarith [exp_one_gt_d9]) _
      _ = exp (10 : ℝ) := by rw [← exp_nat_mul]; norm_num
  have he048 : (1.48 : ℝ) ≤ exp (0.48 : ℝ) := by linarith [add_one_le_exp (0.48 : ℝ)]
  have he : (31000 : ℝ) ≤ exp (10.48 : ℝ) := by
    calc
      _ ≤ 2.718 ^ (10 : ℕ) * 1.48 := by norm_num
      _ ≤ exp (10 : ℝ) * exp (0.48 : ℝ) :=
        mul_le_mul he10 he048 (by norm_num) (exp_pos _).le
      _ = _ := by rw [← exp_add]; norm_num
  have hmargin : (0.04 : ℝ) < exp (10.48 : ℝ) * (decomp305HeadValue 20 : ℝ) := by
    have hh := mul_le_mul he hval.le (by norm_num : (0 : ℝ) ≤ 13 / 10000000) (exp_pos _).le
    norm_num at hh
    linarith
  have hMexp : Tendsto (fun q => exp (M q)) atTop (nhds (exp (10.48 : ℝ))) :=
    (Real.continuous_exp.tendsto _).comp hM
  have hF := hMexp.mul hE
  have hEpos : ∀ᶠ q : ℕ in atTop, 0 < E q :=
    hE.eventually (eventually_gt_nhds (show (0 : ℝ) < (decomp305HeadValue 20 : ℝ) by linarith))
  filter_upwards [hF.eventually (eventually_gt_nhds hmargin), hEpos] with q hFq hEq
  change (0.04 : ℝ) < E q / D q
  apply lt_of_lt_of_le hFq
  apply (le_div_iff₀ (hD q)).mpr
  have heq : exp (M q) * D q ≤ 1 := by
    calc
      _ ≤ exp (M q) * exp (-M q) := mul_le_mul_of_nonneg_left (hprod q) (exp_pos _).le
      _ = 1 := by rw [← exp_add]; simp
  have hm := mul_le_mul_of_nonneg_left heq hEq.le
  convert hm using 1 <;> ring


/-- Auxiliary normalized actual head construction for second memoir pages 99 and 111.
For every sequence of even gaps there are actual decreasing prime blocks whose
normalized twenty block head is eventually greater than 0.04. This asserts no count. -/
lemma decomp338_normalized_head_sequence (h : ℕ → ℕ) (heven : ∀ q, Even (h q)) :
    ∃ w : ℕ → ℕ, ∃ c : ℕ → ℕ → ℕ,
      (∀ q, Antitone (c q)) ∧ (∀ q, c q 0 ≤ w q) ∧
      (∀ i, Tendsto (fun q => c q i) atTop atTop) ∧
      ∀ᶠ q : ℕ in atTop, (0.04 : ℝ) <
        (∑ S ∈ decomp305PrimeFamily (w q) (c q) 19,
          (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN (h q) p) /
        (∏ p ∈ (Ioc (c q 19) (w q)).filter Nat.Prime, (1 - nuN (h q) p)) := by
  obtain ⟨w, c, hc, hw, hcdiv, ht, hsq⟩ := decomp338_block_moment_sequence h
  exact ⟨w, c, hc, hw, hcdiv,
    decomp338_normalized_head_of_moments h w c heven hc hw ht hsq⟩

end
end LeanLab.Ricci1937
