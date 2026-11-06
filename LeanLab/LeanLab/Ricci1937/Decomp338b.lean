import LeanLab.Ricci1937.Decomp338a

/-!
Ricci 1937, actual decreasing cutoff construction.
AI wrote the Lean code. Binary Goldbach is open.
-/

namespace LeanLab.Ricci1937

open Finset Filter Real
open LeanLab.SchnirelmannGoldbach LeanLab.SchnirelmannGoldbach.S1

noncomputable section
attribute [local instance] Classical.propDecidable

/-- Auxiliary finite cutoff construction for second memoir pages 109 to 111.
Any finite positive mass profile can be realized above any prescribed lower endpoint,
uniformly in the gap, with the logarithmic power support bounds. -/
lemma decomp338_finite_cutoffs (θ : ℕ → ℝ) (hθ : ∀ i, 0 < θ i)
    (ε : ℝ) (hε : 0 < ε) (n Z : ℕ) :
    ∃ W : ℕ, Z ≤ W ∧ ∀ h w : ℕ, W ≤ w → ∃ e : ℕ → ℕ,
      Antitone e ∧ e 0 = w ∧ Z ≤ e n ∧
      ∀ i < n,
        (θ i - ε < ∑ p ∈ (Ioc (e (i + 1)) (e i)).filter Nat.Prime, nuN h p) ∧
        (∑ p ∈ (Ioc (e (i + 1)) (e i)).filter Nat.Prime, nuN h p) ≤ θ i ∧
        (e (i + 1) : ℝ) ≤ (e i : ℝ) ^ exp (-θ i / 2 + ε) := by
  induction n generalizing θ Z with
  | zero =>
    refine ⟨Z, le_rfl, ?_⟩
    intro h w hw
    exact ⟨fun _ => w, antitone_const, rfl, hw, by intro i hi; omega⟩
  | succ n ih =>
    obtain ⟨V, hZV, hV⟩ := ih (fun i => θ (i + 1)) (fun i => hθ (i + 1)) Z
    obtain ⟨Y, hY, hYprop⟩ := decompJ365_pair_block_choose_eventually (θ 0) ε (hθ 0) hε
    obtain ⟨W, hW, hWprop⟩ := hYprop (max Y V) (le_max_left _ _)
    refine ⟨W, hZV.trans ((le_max_right Y V).trans hW), ?_⟩
    intro h w hw
    obtain ⟨y, hy, hyw, hlo, hhi, hpow⟩ := hWprop h w hw
    obtain ⟨d, hd, hd0, hZn, hblocks⟩ := hV h y (by omega)
    let e : ℕ → ℕ := fun i => match i with
      | 0 => w
      | j + 1 => d j
    have he : Antitone e := by
      apply antitone_nat_of_succ_le
      intro i
      cases i with
      | zero => simpa [e, hd0] using hyw
      | succ i => exact hd (by omega : i ≤ i + 1)
    refine ⟨e, he, rfl, hZn, ?_⟩
    intro i hi
    cases i with
    | zero => simpa [e, hd0] using And.intro hlo (And.intro hhi hpow)
    | succ i => simpa [e] using hblocks i (by omega)


/-- The printed lower mass profile is positive at every index, first memoir page 89. -/
lemma decomp338_head_mass_pos (i : ℕ) : 0 < (decomp305HeadMass i : ℝ) / 100 := by
  rcases i with _ | i
  · norm_num [decomp305HeadMass]
  rcases i with _ | i
  · norm_num [decomp305HeadMass]
  rcases i with _ | i
  · norm_num [decomp305HeadMass]
  · norm_num [decomp305HeadMass]

/-- Auxiliary actual block moment construction for second memoir pages 109 to 111.
The printed masses and vanishing square masses are realized by decreasing prime cutoffs. -/
lemma decomp338_block_moment_sequence (h : ℕ → ℕ) :
    ∃ w : ℕ → ℕ, ∃ c : ℕ → ℕ → ℕ,
      (∀ q, Antitone (c q)) ∧ (∀ q, c q 0 ≤ w q) ∧
      (∀ i, Tendsto (fun q => c q i) atTop atTop) ∧
      (∀ i, Tendsto
        (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, nuN (h q) p)
        atTop (nhds ((decomp305HeadMass i : ℝ) / 100))) ∧
      (∀ i, Tendsto
        (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, (nuN (h q) p) ^ 2)
        atTop (nhds 0)) := by
  have hchoose (q : ℕ) : ∃ w : ℕ, ∃ e : ℕ → ℕ,
      Antitone e ∧ e 0 = w ∧ q + 4 ≤ e (q + 1) ∧
      ∀ i < q + 1,
        ((decomp305HeadMass i : ℝ) / 100 - 1 / ((q : ℝ) + 1) <
          ∑ p ∈ (Ioc (e (i + 1)) (e i)).filter Nat.Prime, nuN (h q) p) ∧
        (∑ p ∈ (Ioc (e (i + 1)) (e i)).filter Nat.Prime, nuN (h q) p) ≤
          (decomp305HeadMass i : ℝ) / 100 := by
    obtain ⟨W, hW, hWprop⟩ := decomp338_finite_cutoffs
      (fun i => (decomp305HeadMass i : ℝ) / 100) decomp338_head_mass_pos
      (1 / ((q : ℝ) + 1)) (by positivity) (q + 1) (q + 4)
    obtain ⟨e, he, he0, heq, hblocks⟩ := hWprop (h q) W le_rfl
    exact ⟨W, e, he, he0, heq, fun i hi => ⟨(hblocks i hi).1, (hblocks i hi).2.1⟩⟩
  choose w e he he0 heq hblocks using hchoose
  let c : ℕ → ℕ → ℕ := fun q i => e q (i + 1)
  have hc : ∀ q, Antitone (c q) := fun q i j hij => he q (by omega : i + 1 ≤ j + 1)
  have hw : ∀ q, c q 0 ≤ w q := by
    intro q
    simpa [c, he0 q] using he q (by omega : 0 ≤ 0 + 1)
  have hlow (i : ℕ) : ∀ᶠ q : ℕ in atTop, q + 4 ≤ c q i := by
    filter_upwards [eventually_ge_atTop i] with q hqi
    exact (heq q).trans (he q (by omega : i + 1 ≤ q + 1))
  have hcdiv (i : ℕ) : Tendsto (fun q => c q i) atTop atTop :=
    tendsto_atTop_mono' atTop (hlow i) (tendsto_add_atTop_nat 4)
  have hb (i : ℕ) : ∀ᶠ q : ℕ in atTop,
      ((decomp305HeadMass i : ℝ) / 100 - 1 / ((q : ℝ) + 1) <
        ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, nuN (h q) p) ∧
      (∑ p ∈ decomp338PrimeBlock (w q) (c q) i, nuN (h q) p) ≤
        (decomp305HeadMass i : ℝ) / 100 := by
    filter_upwards [eventually_ge_atTop i] with q hqi
    have hh := hblocks q i (by omega)
    cases i with
    | zero => simpa [decomp338PrimeBlock, c, he0 q] using hh
    | succ i => simpa [decomp338PrimeBlock, c] using hh
  have heps : Tendsto (fun q : ℕ => 1 / ((q : ℝ) + 1)) atTop (nhds 0) :=
    tendsto_one_div_add_atTop_nhds_zero_nat
  have ht (i : ℕ) : Tendsto
      (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, nuN (h q) p)
      atTop (nhds ((decomp305HeadMass i : ℝ) / 100)) := by
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le'
      (by simpa using tendsto_const_nhds.sub heps) tendsto_const_nhds
    · exact (hb i).mono fun q hq => by simpa only [one_div] using hq.1.le
    · exact (hb i).mono fun q hq => hq.2
  have hsq (i : ℕ) : Tendsto
      (fun q => ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, (nuN (h q) p) ^ 2)
      atTop (nhds 0) := by
    have hbound : Tendsto
        (fun q : ℕ => 2 / (c q i : ℝ) * ((decomp305HeadMass i : ℝ) / 100))
        atTop (nhds 0) := by
      have hcR : Tendsto (fun q => (c q i : ℝ)) atTop atTop :=
        tendsto_natCast_atTop_atTop.comp (hcdiv i)
      have hh : Tendsto (fun q => (c q i : ℝ)⁻¹) atTop (nhds 0) :=
        tendsto_inv_atTop_zero.comp hcR
      simpa [div_eq_mul_inv] using (hh.const_mul 2).mul_const
        ((decomp305HeadMass i : ℝ) / 100)
    apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hbound
    · exact Eventually.of_forall fun q => sum_nonneg (fun p _ => sq_nonneg _)
    · filter_upwards [hlow i, hb i] with q hlo hmass
      have hy : 0 < c q i := by omega
      have hpair : (∑ p ∈ decomp338PrimeBlock (w q) (c q) i, (nuN (h q) p) ^ 2) ≤
          2 / (c q i : ℝ) * ∑ p ∈ decomp338PrimeBlock (w q) (c q) i, nuN (h q) p := by
        cases i with
        | zero => exact decompJ365_pair_block_square_upper (h q) (c q 0) (w q) hy
        | succ i => exact decompJ365_pair_block_square_upper (h q) (c q (i + 1)) (c q i) hy
      exact hpair.trans (mul_le_mul_of_nonneg_left hmass.2 (by positivity))
  exact ⟨w, c, hc, hw, hcdiv, ht, hsq⟩

/-- Actual finite head comparison for second memoir page 111 formula 28.11.
For every varying gap sequence there are actual decreasing prime cutoffs whose
retained twenty block head tends to the exact positive factorial head. -/
lemma decomp338_actual_head_sequence (h : ℕ → ℕ) :
    ∃ w : ℕ → ℕ, ∃ c : ℕ → ℕ → ℕ,
      (∀ q, Antitone (c q)) ∧ (∀ q, c q 0 ≤ w q) ∧
      (∀ i, Tendsto (fun q => c q i) atTop atTop) ∧
      Tendsto (fun q => ∑ S ∈ decomp305PrimeFamily (w q) (c q) 19,
        (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN (h q) p) atTop
        (nhds (decomp305HeadValue 20 : ℝ)) ∧
      ∀ᶠ q : ℕ in atTop, (13 / 10000000 : ℝ) <
        ∑ S ∈ decomp305PrimeFamily (w q) (c q) 19,
          (-1 : ℝ) ^ S.card * ∏ p ∈ S, nuN (h q) p := by
  obtain ⟨w, c, hc, hw, hcdiv, ht, hsq⟩ := decomp338_block_moment_sequence h
  have hlim := decomp338_prime_head_tendsto (fun q => nuN (h q)) w c hc hw
    (fun q => nuN_nonneg (h q)) ht hsq 19
  have hpos : (13 / 10000000 : ℝ) < (decomp305HeadValue 20 : ℝ) := by
    have hh : ((13 / 10000000 : ℚ) : ℝ) < (decomp305HeadValue 20 : ℝ) :=
      Rat.cast_lt.mpr decomp305_head20_positive
    norm_num at hh
    exact hh
  exact ⟨w, c, hc, hw, hcdiv, hlim, hlim.eventually (eventually_gt_nhds hpos)⟩


/-- Auxiliary cumulative mass identity for second memoir pages 99 and 109.
Disjoint successive prime intervals telescope to the entire retained prime interval. -/
lemma decomp338_prime_mass_telescopes (x : ℕ → ℝ) (e : ℕ → ℕ)
    (he : Antitone e) (n : ℕ) :
    (∑ i ∈ range n, ∑ p ∈ (Ioc (e (i + 1)) (e i)).filter Nat.Prime, x p) =
      ∑ p ∈ (Ioc (e n) (e 0)).filter Nat.Prime, x p := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, ih]
    have hsets : (Ioc (e (n + 1)) (e 0)).filter Nat.Prime =
        (Ioc (e n) (e 0)).filter Nat.Prime ∪
          (Ioc (e (n + 1)) (e n)).filter Nat.Prime := by
      rw [← filter_union, union_comm, Ioc_union_Ioc_eq_Ioc
        (he (by omega : n ≤ n + 1)) (he (Nat.zero_le n))]
    rw [hsets, sum_union]
    apply disjoint_left.mpr
    intro p hp hq
    have hpI := mem_Ioc.mp (mem_filter.mp hp).1
    have hqI := mem_Ioc.mp (mem_filter.mp hq).1
    omega

/-- Auxiliary cumulative budget for second memoir page 99 formula 18.3.
The printed block upper masses leave the strict margin 0.02 in each later crude budget. -/
lemma decomp338_cumulative_mass_budget (h : ℕ) (e : ℕ → ℕ) (he : Antitone e)
    (n : ℕ) (hn : 3 ≤ n)
    (hm : ∀ i < n, (∑ p ∈ (Ioc (e (i + 1)) (e i)).filter Nat.Prime, nuN h p) ≤
      (decomp305HeadMass i : ℝ) / 100) :
    (∑ p ∈ (Ioc (e n) (e 0)).filter Nat.Prime, nuN h p) ≤
      (n : ℝ) / 2 + 0.48 := by
  rw [← decomp338_prime_mass_telescopes (nuN h) e he n,
    ← decomp305_head_mass_sum hn]
  apply sum_le_sum
  intro i hi
  exact hm i (mem_range.mp hi)

end
end LeanLab.Ricci1937
