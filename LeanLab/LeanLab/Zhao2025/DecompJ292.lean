import LeanLab.Zhao2025.PaperTheorem14
import LeanLab.PNTSieve.BrunTitchmarshAP
import Mathlib

/-!
Decomposition of PaperTheorem14.
Source: Zhao 2025, displays 1.15 and 1.16, page 3.
AI wrote the Lean code. Goldbach is open.
-/
namespace LeanLab.Zhao2025.Task292

open LeanLab.Zhao2025.Task56

/-- Monotonicity of the finite count in display 1.15 on page 3. -/
theorem primeCountAP_mono (q a : ℕ) : Monotone (fun X : ℝ => primeCountAP X q a) := by
  intro X Y hXY
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.range_mono (Nat.add_le_add_right (Nat.floor_mono hXY) 1)

/-- Positivity of display 1.15 is equivalent to a prime witness below the endpoint.
Source: Zhao page 3, the lower bound of display 1.16. -/
theorem primeCountAP_pos_iff (X : ℝ) (q a : ℕ) :
    0 < (primeCountAP X q a : ℝ) ↔
      ∃ p : ℕ, p.Prime ∧ (p : ℝ) ≤ X ∧ p % q = a % q := by
  constructor
  · intro h
    have hn : 0 < primeCountAP X q a := by exact_mod_cast h
    obtain ⟨p, hp⟩ := Finset.card_pos.mp hn
    obtain ⟨hr, hprime, hmod⟩ := Finset.mem_filter.mp hp
    have hle : p ≤ ⌊X⌋₊ := by
      have := Finset.mem_range.mp hr
      omega
    exact ⟨p, hprime, (Nat.le_floor_iff' hprime.ne_zero).mp hle, hmod⟩
  · rintro ⟨p, hprime, hp, hmod⟩
    have hfloor := (Nat.le_floor_iff' hprime.ne_zero).mpr hp
    have hn : 0 < primeCountAP X q a := by
      apply Finset.card_pos.mpr
      exact ⟨p, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by omega), hprime, hmod⟩⟩
    exact_mod_cast hn

/-- A concrete progression has a prime below two to the fifth power.
Source: a nonvacuity model for Zhao page 3, display 1.16. -/
theorem primeCountAP_five_instance :
    Nat.Coprime 1 2 ∧ 0 < (primeCountAP ((2 : ℝ) ^ (5 : ℝ)) 2 1 : ℝ) := by
  refine ⟨by norm_num, (primeCountAP_pos_iff _ _ _).mpr ⟨3, by norm_num, ?_, by norm_num⟩⟩
  norm_num

/-- The sieve coefficient has strict room exactly above the stated cutoff.
Elementary arithmetic for Zhao page 3, display 1.16. -/
theorem sieve_coefficient_lt (theta epsilon : ℝ) (heps : 0 < epsilon)
    (hth : 1 < theta) :
    2 * theta / (theta - 1) < 2 + epsilon ↔ 1 + 2 / epsilon < theta := by
  rw [div_lt_iff₀ (by linarith : 0 < theta - 1)]
  constructor
  · intro h
    have hm : 2 / epsilon < theta - 1 :=
      (div_lt_iff₀ heps).mpr (by nlinarith)
    linarith
  · intro h
    have h' : 2 < (theta - 1) * epsilon := by
      exact (div_lt_iff₀ heps).mp (by linarith)
    nlinarith

/-- The interval sieve with x equal to one counts precisely display 1.15.
Source: Zhao page 3 and the proved lab Brun-Titchmarsh inequality. -/
theorem primeCountAP_sieve (X z : ℝ) (q a : ℕ)
    (hX : 1 < X) (hz : 1 < z) (hq : 0 < q) :
    (primeCountAP X q a : ℝ) ≤
      2 * (X - 1) / ((q.totient : ℝ) * Real.log z) +
        4 * z * (1 + Real.log z) ^ 3 := by
  have h := LeanLab.PNTSieve.BrunTitchmarshAP.brunTitchmarsh_ap
    (x := 1) (y := X - 1) (z := z) (q := q) (a := a)
    (by norm_num) (by linarith) hz hq
  have hset : (Finset.range (⌊X⌋₊ + 1)).filter
      (fun p => Nat.Prime p ∧ p % q = a % q) =
      (Finset.Icc 1 ⌊X⌋₊).filter (fun p => Nat.Prime p ∧ p % q = a % q) := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Icc]
    constructor
    · rintro ⟨hp, hprime, hmod⟩
      exact ⟨⟨hprime.one_lt.le, by omega⟩, hprime, hmod⟩
    · rintro ⟨⟨_, hp⟩, hprime, hmod⟩
      exact ⟨by omega, hprime, hmod⟩
  simpa [primeCountAP, hset, show 1 + (X - 1) = X by ring] using h

open Filter in
/-- The logarithmic sieve loss and error leave the strict coefficient room.
Elementary asymptotic helper for Zhao page 3, display 1.16. -/
theorem sieve_log_budget (c epsilon : ℝ) (hc : 0 < c) (hc1 : c ≤ 1)
    (hgap : 2 / c < 2 + epsilon) :
    ∃ T : ℝ, ∀ t : ℝ, T ≤ t →
      1 ≤ t ∧ 0 < c * t - 5 * Real.log t ∧
      c * t - 5 * Real.log t ≤ t ∧
      2 * t / (c * t - 5 * Real.log t) + 32 / t ≤ 2 + epsilon := by
  have hlog : Tendsto (fun t : ℝ => Real.log t / t) atTop (nhds 0) := by
    simpa using Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero
  have hr : Filter.Tendsto (fun t : ℝ => c - 5 * (Real.log t / t))
      Filter.atTop (nhds c) := by
    simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hlog)
  have hb : Filter.Tendsto (fun t : ℝ => 2 / (c - 5 * (Real.log t / t)) + 32 / t)
      Filter.atTop (nhds (2 / c)) := by
    simpa using (tendsto_const_nhds.div hr (ne_of_gt hc)).add
      (tendsto_const_nhds.div_atTop Filter.tendsto_id)
  have hpos := hr.eventually (lt_mem_nhds hc)
  have hbound := hb.eventually (gt_mem_nhds hgap)
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp
    ((Filter.eventually_ge_atTop (1 : ℝ)).and (hpos.and hbound))
  refine ⟨T, ?_⟩
  intro t ht
  obtain ⟨ht1, hp, hb⟩ := hT t ht
  have ht0 : 0 < t := by linarith
  have htne := ne_of_gt ht0
  have hp' : 0 < c * t - 5 * Real.log t := by
    have := mul_pos hp ht0
    field_simp at this
    nlinarith
  refine ⟨ht1, hp', ?_, ?_⟩
  · have := Real.log_nonneg ht1
    nlinarith [mul_le_mul_of_nonneg_right hc1 ht0.le]
  · have heq : 2 * t / (c * t - 5 * Real.log t) =
        2 / (c - 5 * (Real.log t / t)) := by
      field_simp
    rw [heq]
    exact hb.le

/-- Totient at most q makes the fifth logarithmic power sieve error negligible.
Elementary absorption for Zhao page 3, display 1.16. -/
theorem sieve_absorb (X z epsilon : ℝ) (q a : ℕ)
    (hX : 1 < X) (hz : 1 < z) (hq : 0 < q)
    (ht : 1 ≤ Real.log X) (hlz : Real.log z ≤ Real.log X)
    (hzdef : z = X / (q : ℝ) / Real.log X ^ 5)
    (hbudget : 2 * Real.log X / Real.log z + 32 / Real.log X ≤ 2 + epsilon) :
    (primeCountAP X q a : ℝ) ≤
      (2 + epsilon) * X / ((q.totient : ℝ) * Real.log X) := by
  have hq0 : (0 : ℝ) < q := by exact_mod_cast hq
  have hphi : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr hq
  have hphiq : (q.totient : ℝ) ≤ q := by exact_mod_cast Nat.totient_le q
  have ht0 : 0 < Real.log X := by linarith
  have hlz0 : 0 < Real.log z := Real.log_pos hz
  have hmain : 2 * (X - 1) / ((q.totient : ℝ) * Real.log z) ≤
      (2 * Real.log X / Real.log z) * (X / ((q.totient : ℝ) * Real.log X)) := by
    calc
      _ ≤ 2 * X / ((q.totient : ℝ) * Real.log z) := by gcongr; linarith
      _ = _ := by field_simp
  have herr : 4 * z * (1 + Real.log z) ^ 3 ≤
      (32 / Real.log X) * (X / ((q.totient : ℝ) * Real.log X)) := by
    calc
      _ ≤ 4 * z * (2 * Real.log X) ^ 3 := by
        gcongr
        linarith
      _ = 32 * X / ((q : ℝ) * Real.log X ^ 2) := by
        rw [hzdef]
        field_simp
        ring
      _ ≤ 32 * X / ((q.totient : ℝ) * Real.log X ^ 2) := by gcongr
      _ = _ := by field_simp
  calc
    _ ≤ 2 * (X - 1) / ((q.totient : ℝ) * Real.log z) +
        4 * z * (1 + Real.log z) ^ 3 := primeCountAP_sieve X z q a hX hz hq
    _ ≤ (2 * Real.log X / Real.log z + 32 / Real.log X) *
        (X / ((q.totient : ℝ) * Real.log X)) := by nlinarith [hmain, herr]
    _ ≤ (2 + epsilon) * (X / ((q.totient : ℝ) * Real.log X)) := by
      exact mul_le_mul_of_nonneg_right hbudget (by positivity)
    _ = _ := by ring

/-- The error absorption hypotheses hold for explicit positive sieve parameters.
Source: a nonvacuity instance for Zhao page 3, display 1.16. -/
theorem sieve_absorb_instance :
    let X := Real.exp 100
    let z := X / 2 / Real.log X ^ 5
    1 < X ∧ 1 < z ∧ 1 ≤ Real.log X ∧ Real.log z ≤ Real.log X ∧
      2 * Real.log X / Real.log z + 32 / Real.log X ≤ 2 + (1 : ℝ) := by
  let X := Real.exp 100
  let z := X / 2 / Real.log X ^ 5
  have hX : 1 < X := Real.one_lt_exp_iff.mpr (by norm_num)
  have ht : Real.log X = 100 := Real.log_exp _
  have hz0 : 0 < z := by dsimp [z]; rw [ht]; positivity
  have hlog100 : Real.log 100 ≤ (24 / 5 : ℝ) := by
    apply (Real.log_le_iff_le_exp (by norm_num)).mpr
    have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 24 / 5) 8
    norm_num [Finset.sum_range_succ, Nat.factorial] at h
    linarith
  have hlog2 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  have hlogz : Real.log z = 100 - Real.log 2 - 5 * Real.log 100 := by
    dsimp [z]
    rw [ht, Real.log_div (by positivity) (by norm_num),
      Real.log_div (by positivity) (by norm_num), Real.log_pow, ht]
    norm_num
  have hlo : 75 ≤ Real.log z := by rw [hlogz]; linarith
  have hhi : Real.log z ≤ 100 := by
    rw [hlogz]
    have h1 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have h2 : 0 ≤ Real.log 100 := Real.log_nonneg (by norm_num)
    linarith
  have hz : 1 < z := (Real.log_pos_iff hz0.le).mp (by linarith)
  change 1 < X ∧ 1 < z ∧ 1 ≤ Real.log X ∧ Real.log z ≤ Real.log X ∧ _
  refine ⟨hX, hz, by rw [ht]; norm_num, by rw [ht]; exact hhi, ?_⟩
  change 2 * Real.log X / Real.log z + 32 / Real.log X ≤ 2 + (1 : ℝ)
  rw [ht]
  have hdiv : (200 : ℝ) / Real.log z ≤ 200 / 75 :=
    div_le_div_of_nonneg_left (by norm_num) (by norm_num) hlo
  linarith

/-- The proved Brun-Titchmarsh range of Zhao page 3, display 1.16.
This uses the lab sieve and no cited zero estimates. -/
theorem leaf2_high (theta : ℝ) (hth : 5 ≤ theta) (epsilon : ℝ)
    (heps : 0 < epsilon) (hhigh : 1 + 2 / epsilon < theta) :
  ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 1 ≤ q →
    ∀ a : ℕ, 1 ≤ a → a ≤ q → Nat.Coprime a q →
      (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) ≤
        (2 + epsilon) * (q : ℝ) ^ theta /
          ((Nat.totient q : ℝ) * Real.log ((q : ℝ) ^ theta)) := by
  have htheta : 0 < theta := by linarith
  have htheta1 : 1 < theta := by linarith
  let c := (theta - 1) / theta
  have hc : 0 < c := div_pos (by linarith) htheta
  have hc1 : c ≤ 1 := (div_le_one htheta).mpr (by linarith)
  have hgap : 2 / c < 2 + epsilon := by
    have heq : 2 / c = 2 * theta / (theta - 1) := by dsimp [c]; field_simp
    rw [heq]
    exact (sieve_coefficient_lt theta epsilon heps htheta1).mpr hhigh
  obtain ⟨T, hT⟩ := sieve_log_budget c epsilon hc hc1 hgap
  refine ⟨max 2 ⌈Real.exp (T / theta)⌉₊, ?_⟩
  intro q hq _ a _ _ _
  have hq2 : 2 ≤ q := (le_max_left _ _).trans hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (by omega : 0 < q)
  have hqexp : Real.exp (T / theta) ≤ (q : ℝ) := by
    exact (Nat.le_ceil _).trans (by exact_mod_cast (le_max_right _ _).trans hq)
  let X := (q : ℝ) ^ theta
  have hX0 : 0 < X := Real.rpow_pos_of_pos hq0 _
  have hX : 1 < X := Real.one_lt_rpow (by exact_mod_cast (show 1 < q by omega)) htheta
  have htdef : Real.log X = theta * Real.log (q : ℝ) := Real.log_rpow hq0 _
  have htT : T ≤ Real.log X := by
    have hlog : T / theta ≤ Real.log (q : ℝ) := by
      simpa using Real.log_le_log (Real.exp_pos _) hqexp
    rw [htdef]
    calc T = theta * (T / theta) := by field_simp
         _ ≤ theta * Real.log (q : ℝ) := mul_le_mul_of_nonneg_left hlog htheta.le
  obtain ⟨ht1, hlpos, hlle, hbudget⟩ := hT (Real.log X) htT
  have ht0 : 0 < Real.log X := by linarith
  let z := X / (q : ℝ) / Real.log X ^ 5
  have hz0 : 0 < z := by dsimp [z]; positivity
  have hlogz : Real.log z = c * Real.log X - 5 * Real.log (Real.log X) := by
    dsimp [z]
    rw [Real.log_div (ne_of_gt (div_pos hX0 hq0)) (pow_ne_zero _ (ne_of_gt ht0)),
      Real.log_div (ne_of_gt hX0) (ne_of_gt hq0), Real.log_pow]
    dsimp [c]
    rw [htdef]
    field_simp
  have hz : 1 < z := (Real.log_pos_iff hz0.le).mp (by rw [hlogz]; exact hlpos)
  exact sieve_absorb X z epsilon q a hX hz (by omega) ht1
    (by rw [hlogz]; exact hlle) rfl (by rw [hlogz]; exact hbudget)

/-- In the complementary range the limiting sieve coefficient has no strict room.
This is an obstruction to that estimate, not a negation of Zhao 1.16 on page 3. -/
theorem sieve_coefficient_obstruction (theta epsilon : ℝ) (heps : 0 < epsilon)
    (hth : 1 < theta) (hlow : theta ≤ 1 + 2 / epsilon) :
    2 + epsilon ≤ 2 * theta / (theta - 1) := by
  apply le_of_not_gt
  intro h
  exact not_lt_of_ge hlow ((sieve_coefficient_lt theta epsilon heps hth).mp h)

/-- For epsilon greater than one half the sieve covers every theta at least five.
Elementary corollary of the proved range of Zhao page 3, display 1.16. -/
theorem leaf2_large_epsilon (theta : ℝ) (hth : 5 ≤ theta) (epsilon : ℝ)
    (heps : 1 / 2 < epsilon) :
  ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 1 ≤ q →
    ∀ a : ℕ, 1 ≤ a → a ≤ q → Nat.Coprime a q →
      (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) ≤
        (2 + epsilon) * (q : ℝ) ^ theta /
          ((Nat.totient q : ℝ) * Real.log ((q : ℝ) ^ theta)) := by
  have heps0 : 0 < epsilon := by linarith
  apply leaf2_high theta hth epsilon heps0
  have hdiv : 2 / epsilon < 4 := (div_lt_iff₀ heps0).mpr (by linarith)
  linarith

/-- Both branches have concrete admissible parameters and a reduced residue.
Source: the hypotheses of Zhao page 3, display 1.16. -/
theorem sieve_range_instances :
    5 ≤ (5 : ℝ) ∧ 1 + 2 / (1 : ℝ) < 5 ∧
    0 < (1 / 4 : ℝ) ∧ (5 : ℝ) ≤ 1 + 2 / (1 / 4 : ℝ) ∧
    Nat.Coprime 1 2 ∧ (2 * (5 : ℝ) / (5 - 1) = 5 / 2) := by
  norm_num

open Filter in
/-- A fixed logarithmic modulus range cannot cover the polynomial Linnik range.
This audits the Siegel-Walfisz fallback for Zhao page 3, display 1.16. -/
theorem logarithmic_modulus_range_obstruction (theta A : ℝ) (htheta : 0 < theta) :
    ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q →
      (Real.log ((q : ℝ) ^ theta)) ^ A < (q : ℝ) := by
  have hlog : Tendsto (fun x : ℝ => (Real.log x) ^ A / x) atTop (nhds 0) := by
    simpa using (isLittleO_log_rpow_rpow_atTop A (s := 1) zero_lt_one).tendsto_div_nhds_zero
  have hlim : Tendsto (fun x : ℝ => (theta * Real.log x) ^ A / x) atTop (nhds 0) := by
    have h := (tendsto_const_nhds (x := theta ^ A)).mul hlog
    simp only [mul_zero] at h
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
    rw [Real.mul_rpow htheta.le (Real.log_nonneg hx)]
    ring
  have hn := hlim.comp (tendsto_natCast_atTop_atTop : Tendsto (fun q : ℕ => (q : ℝ)) atTop atTop)
  obtain ⟨Q, hQ⟩ := eventually_atTop.mp (hn.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1)))
  refine ⟨max Q 2, ?_⟩
  intro q hq
  have hq2 : 2 ≤ q := (le_max_right _ _).trans hq
  have hq0 : (0 : ℝ) < q := by exact_mod_cast (show 0 < q by omega)
  rw [Real.log_rpow hq0]
  exact (div_lt_one hq0).mp (hQ q ((le_max_left _ _).trans hq))

/-- LEAF: Zhao page 3, display 1.16 in the complementary range.
Zhao Theorem 1.3 and the analytic Brun-Titchmarsh deduction are missing.
Page 3 cites Maynard 2013 as reference 10. Heath-Brown 1992 supplies the
underlying Linnik method. The pure sieve coefficient has no strict room here. -/
theorem leaf2_low (theta : ℝ) (hth : 5 ≤ theta) (epsilon : ℝ)
    (heps : 0 < epsilon) (hlow : theta ≤ 1 + 2 / epsilon) :
  ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 1 ≤ q →
    ∀ a : ℕ, 1 ≤ a → a ≤ q → Nat.Coprime a q →
      (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) ≤
        (2 + epsilon) * (q : ℝ) ^ theta /
          ((Nat.totient q : ℝ) * Real.log ((q : ℝ) ^ theta)) := by
  sorry

/-- LEAF: Zhao page 3, display 1.16 at exponent five.
The exact exponent five input is cited from Zhao, using the strict zero sum
margin. Xylouris 2011 is the exponent 5.2 precursor, not an exponent five proof.
This cited analytic input remains unproved here. -/
theorem linnik_five :
  ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 1 ≤ q →
    ∀ a : ℕ, 1 ≤ a → a ≤ q → Nat.Coprime a q →
      0 < (primeCountAP ((q : ℝ) ^ (5 : ℝ)) q a : ℝ) := by
  sorry

/-- LEAF: Paper page 3. -/
theorem leaf1 (theta : ℝ) (hth : 5 ≤ theta) (epsilon : ℝ) (heps : 0 < epsilon) :
  ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 1 ≤ q →
    ∀ a : ℕ, 1 ≤ a → a ≤ q → Nat.Coprime a q →
      0 < (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) := by
  have _ := heps
  obtain ⟨Q, hQ⟩ := linnik_five
  refine ⟨Q, ?_⟩
  intro q hq hq1 a ha1 haq hcop
  apply lt_of_lt_of_le (hQ q hq hq1 a ha1 haq hcop)
  have hmono := primeCountAP_mono q a
    (Real.rpow_le_rpow_of_exponent_le (x := (q : ℝ)) (by exact_mod_cast hq1) hth)
  exact_mod_cast hmono

/-- LEAF: Paper page 3. -/
theorem leaf2 (theta : ℝ) (hth : 5 ≤ theta) (epsilon : ℝ) (heps : 0 < epsilon) :
  ∃ Q : ℕ, ∀ q : ℕ, Q ≤ q → 1 ≤ q →
    ∀ a : ℕ, 1 ≤ a → a ≤ q → Nat.Coprime a q →
      (primeCountAP ((q : ℝ) ^ theta) q a : ℝ) ≤
        (2 + epsilon) * (q : ℝ) ^ theta /
          ((Nat.totient q : ℝ) * Real.log ((q : ℝ) ^ theta)) := by
  by_cases hhigh : 1 + 2 / epsilon < theta
  · exact leaf2_high theta hth epsilon heps hhigh
  · exact leaf2_low theta hth epsilon heps (le_of_not_gt hhigh)

/-- Main assembly for PaperTheorem14. -/
theorem PaperTheorem14_assembly : PaperTheorem14 := by
  intro theta hth epsilon heps
  obtain ⟨Q1, hQ1⟩ := leaf1 theta hth epsilon heps
  obtain ⟨Q2, hQ2⟩ := leaf2 theta hth epsilon heps
  use max Q1 Q2
  intro q hq hq1 a ha1 haq hcop
  constructor
  · exact hQ1 q (le_trans (le_max_left Q1 Q2) hq) hq1 a ha1 haq hcop
  · exact hQ2 q (le_trans (le_max_right Q1 Q2) hq) hq1 a ha1 haq hcop

end LeanLab.Zhao2025.Task292
