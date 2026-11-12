import LeanLab.Halupczok2012.Decomp329b

/-!
Corollary 1.3 for the residue class 5 modulo 6.
Source: journal page 333 and the counting proof on pages 345 to 346.
For this residue class every first prime above 3 leaves an eligible even number.
The unrestricted Chen count quoted in the paper suffices.
The analytic count remains an explicit hypothesis.
AI wrote the Lean code. Goldbach is open.
-/

namespace LeanLab.Halupczok2012.Decomp329c

open scoped Classical

/-- Pages 345 to 346, the finite surplus step for n equal to 5 modulo 6.
No exclusion of 3 dividing p + 2 is required in this residue class. -/
theorem representation_of_mod_five_surplus {X1 X2 Y : ℝ} {n : ℕ}
    (hX1 : 3 ≤ X1) (hnonneg : 0 ≤ X2 + Y)
    (hn5 : n % 6 = 5) (hsum : X1 + X2 + 2 * Y ≤ n)
    (hcnt : cor2Exc (((n : ℝ) - X1 - Y) / 2) X2 Y + 2 ≤
      ((kRange X1 Y).filter (fun p => p.Prime ∧ IsP 2 (p + 2))).card) :
    Cor3Sol n X1 X2 Y := by
  let S : Finset ℕ := (kRange X1 Y).filter (fun p => p.Prime ∧ IsP 2 (p + 2))
  have hS : ∀ p ∈ S, p.Prime ∧ X1 < (p : ℝ) ∧ (p : ℝ) ≤ X1 + Y ∧ IsP 2 (p + 2) := by
    intro p hp
    obtain ⟨hkr, hpr, hisp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hlo, hhi⟩ := (Fourier398.window_mem _ _ _).mp hkr
    exact ⟨hpr, hlo, hhi, hisp⟩
  have hnodd : Odd n := ⟨n / 2, by omega⟩
  apply Decomp329a.representation_of_eligible_surplus S hX1 hnonneg hnodd hsum hS ?_ hcnt
  intro p hp
  have hpgt3 : 3 < p := by
    have h : (3 : ℝ) < p := by linarith [(hS p hp).2.1]
    exact_mod_cast h
  have hpn : p ≤ n := by
    have h : (p : ℝ) ≤ n := by linarith [(hS p hp).2.2.1]
    exact_mod_cast h
  have hp3 : p % 3 ≠ 0 := by
    intro h
    have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (hS p hp).1).mp
      (Nat.dvd_of_mod_eq_zero h)
    omega
  omega

/-- Pages 345 to 346, a concrete surplus using a candidate excluded by the restricted Wu set. -/
theorem mod_five_surplus_instance :
    cor2Exc (17 / 2) 6 6 = 0 ∧
      2 ≤ ((kRange 6 6).filter (fun p => p.Prime ∧ IsP 2 (p + 2))).card := by
  have h9 : IsP 2 9 := by
    simpa using isP_mul (isP_prime Nat.prime_three) (isP_prime Nat.prime_three)
  have h9' : IsP 3 9 := isP_mono (by norm_num) h9
  have h13 : IsP 3 13 := isP_mono (by norm_num) (isP_prime (by norm_num))
  constructor
  · unfold cor2Exc
    apply Finset.card_eq_zero.mpr
    apply Finset.filter_eq_empty_iff.mpr
    intro k hk hbad
    rcases hbad with ⟨hmod, hbad⟩
    have hkmem := (Fourier398.window_mem _ _ _).mp hk
    have hklo : 9 ≤ k := by
      have h : (8 : ℝ) < k := by linarith [hkmem.1]
      have hkn : 8 < k := by exact_mod_cast h
      omega
    have hkhi : k ≤ 14 := by
      have h : (k : ℝ) < 15 := by linarith [hkmem.2]
      have hkn : k < 15 := by exact_mod_cast h
      omega
    interval_cases k
    all_goals norm_num at hmod
    · exact hbad ⟨7, 11, by norm_num, by norm_num, by norm_num, h9',
        by norm_num, by norm_num⟩
    · exact hbad ⟨11, 11, by norm_num, by norm_num, by norm_num, h13,
        by norm_num, by norm_num⟩
    · exact hbad ⟨7, 17, by norm_num, by norm_num, by norm_num, h9',
        by norm_num, by norm_num⟩
    · exact hbad ⟨11, 17, by norm_num, by norm_num, by norm_num, h13,
        by norm_num, by norm_num⟩
  · have h13' : IsP 2 13 := isP_mono (by norm_num) (isP_prime (by norm_num))
    have hs : ({7, 11} : Finset ℕ) ⊆ (kRange 6 6).filter
        (fun p => p.Prime ∧ IsP 2 (p + 2)) := by
      intro p hp
      simp only [Finset.mem_insert, Finset.mem_singleton] at hp
      rcases hp with rfl | rfl
      · exact Finset.mem_filter.mpr ⟨(Fourier398.window_mem _ _ _).mpr
          ⟨by norm_num, by norm_num⟩, by norm_num, h9⟩
      · exact Finset.mem_filter.mpr ⟨(Fourier398.window_mem _ _ _).mpr
          ⟨by norm_num, by norm_num⟩, by norm_num, h13'⟩
    simpa using Finset.card_le_card hs

/-- Pages 345 to 346, the Chen candidate 7 is removed by the extra restriction in the sealed leaf. -/
theorem candidate_seven : (7 : ℕ).Prime ∧ IsP 2 (7 + 2) ∧ 3 ∣ (7 + 2) := by
  refine ⟨by norm_num, ?_, by norm_num⟩
  simpa using isP_mul (isP_prime Nat.prime_three) (isP_prime Nat.prime_three)

set_option maxHeartbeats 1000000 in
/-- Pages 333 and 345 to 346, the class 5 conclusion conditional on Corollary 1.2 and the unrestricted count.
This theorem uses the count printed in the article without a restriction at 3. -/
theorem corollary3_mod_five_of_count (hCor2 : Corollary2)
    (c_wu : ℝ) (hc_wu : 0 < c_wu) (Y0_wu : ℝ) (_hY0_wu : 0 < Y0_wu)
    (hwu : ∀ (X Y : ℝ), Y0_wu ≤ Y → X ^ (0.971 : ℝ) ≤ Y → Y ≤ X →
      c_wu * Y / (Real.log Y) ^ 2 ≤
        ((@Finset.filter ℕ (fun (p : ℕ) => p.Prime ∧ IsP 2 (p + 2))
          (Classical.decPred _) (kRange X Y)).card : ℝ)) :
    ∀ ε c : ℝ, 0 < ε → 0 < c → ∃ Y0 : ℝ, ∀ (X1 X2 Y : ℝ) (n : ℕ), Y0 ≤ Y →
      X1 ^ (0.971 : ℝ) ≤ Y → Y ≤ X1 → X2 ^ (0.861 : ℝ) ≤ Y → Y ≤ X2 →
      n % 6 = 5 → X1 + X2 + 2 * Y ≤ n → (n : ℝ) ≤ c * Y ^ (3 / 2 - ε) →
      Cor3Sol n X1 X2 Y := by
  intro ε c hε hc
  obtain ⟨C, Y0c, hcor⟩ := hCor2 3 ε c (by norm_num) hε hc
  let M : ℝ := max C 0 + 2
  obtain ⟨Y0d, _, hdom⟩ := leaf_wu_dominates_exc c_wu M hc_wu
  have hev : ∀ᶠ Y : ℝ in Filter.atTop, (Real.log Y) ^ (3 : ℕ) ≤ Y := by
    have h := (isLittleO_log_rpow_rpow_atTop (s := 1) 3 zero_lt_one).bound zero_lt_one
    filter_upwards [h, Filter.eventually_ge_atTop (0 : ℝ)] with Y hY hY0
    have he : (Real.log Y) ^ (3 : ℝ) = (Real.log Y) ^ (3 : ℕ) := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) by rfl, Real.rpow_natCast]
    have hb : |(Real.log Y) ^ (3 : ℕ)| ≤ Y := by
      simpa only [Real.rpow_one, one_mul, Real.norm_eq_abs, abs_of_nonneg hY0, he] using hY
    exact (le_abs_self _).trans hb
  obtain ⟨Ycube, hcube⟩ := Filter.eventually_atTop.mp hev
  refine ⟨max 4 (max Y0_wu (max Y0c (max Y0d Ycube))), ?_⟩
  intro X1 X2 Y n hY hX1pow hYX1 hX2pow hYX2 hn5 hsum hnupper
  have hY4 : (4 : ℝ) ≤ Y := (le_max_left _ _).trans hY
  have hrest : max Y0_wu (max Y0c (max Y0d Ycube)) ≤ Y := (le_max_right _ _).trans hY
  have hY0wu : Y0_wu ≤ Y := (le_max_left _ _).trans hrest
  have hrest' : max Y0c (max Y0d Ycube) ≤ Y := (le_max_right _ _).trans hrest
  have hY0c : Y0c ≤ Y := (le_max_left _ _).trans hrest'
  have hrest'' : max Y0d Ycube ≤ Y := (le_max_right _ _).trans hrest'
  have hY0d : Y0d ≤ Y := (le_max_left _ _).trans hrest''
  have hYcube : Ycube ≤ Y := (le_max_right _ _).trans hrest''
  have hlog : 0 < Real.log Y := Real.log_pos (by linarith)
  have hL3 : (Real.log Y) ^ (-3 : ℝ) = 1 / (Real.log Y) ^ (3 : ℕ) := by
    rw [Real.rpow_neg hlog.le,
      show (3 : ℝ) = ((3 : ℕ) : ℝ) by rfl, Real.rpow_natCast, one_div]
  have hbase : 1 ≤ Y * (Real.log Y) ^ (-3 : ℝ) := by
    rw [hL3, ← div_eq_mul_one_div, le_div_iff₀ (by positivity)]
    simpa only [one_mul] using hcube Y hYcube
  have hweight : 0 ≤ Y * (Real.log Y) ^ (-3 : ℝ) := by positivity
  let K1 : ℝ := ((n : ℝ) - X1 - Y) / 2
  have hexc : (cor2Exc K1 X2 Y : ℝ) ≤ C * Y * Real.log Y ^ (-3 : ℝ) := by
    apply hcor K1 X2 Y hY0c hX2pow hYX2 <;> dsimp [K1] <;> linarith
  have hcount := hwu X1 Y hY0wu hX1pow hYX1
  have hM : C * Y * Real.log Y ^ (-3 : ℝ) + 2 ≤
      M * Y * Real.log Y ^ (-3 : ℝ) := by
    have hC : C ≤ max C 0 := le_max_left _ _
    have hb := mul_le_mul_of_nonneg_right hC hweight
    dsimp [M]
    nlinarith
  have hcnt : cor2Exc K1 X2 Y + 2 ≤
      ((kRange X1 Y).filter (fun p => p.Prime ∧ IsP 2 (p + 2))).card := by
    have hle : (cor2Exc K1 X2 Y : ℝ) + 2 ≤
        (((kRange X1 Y).filter
          (fun p => p.Prime ∧ IsP 2 (p + 2))).card : ℝ) := by
      calc
        _ ≤ C * Y * Real.log Y ^ (-3 : ℝ) + 2 := by linarith [hexc]
        _ ≤ M * Y * Real.log Y ^ (-3 : ℝ) := hM
        _ ≤ c_wu * Y / (Real.log Y) ^ 2 := (hdom Y hY0d).le
        _ ≤ _ := by
          rw [Finset.filter_congr_decidable] at hcount
          exact hcount
    exact_mod_cast hle
  exact representation_of_mod_five_surplus (by linarith) (by linarith)
    hn5 hsum hcnt


/-- Page 333, an unbounded family satisfying the numerical domain of Corollary 1.3.
Use epsilon one quarter and upper bound constant five. -/
theorem mod_five_domain (m : ℕ) (hm : 2 ≤ m) :
    (3 : ℝ) ≤ 3 * m ∧
    (3 * (m : ℝ)) ^ (0.971 : ℝ) ≤ 3 * m ∧
    (3 * (m : ℝ)) ^ (0.861 : ℝ) ≤ 3 * m ∧
    Odd (12 * m + 5) ∧ (12 * m + 5) % 6 = 5 ∧
    3 * (m : ℝ) + 3 * m + 2 * (3 * m) ≤ (12 * m + 5 : ℕ) ∧
    ((12 * m + 5 : ℕ) : ℝ) ≤ 5 * (3 * (m : ℝ)) ^ (3 / 2 - 1 / 4 : ℝ) := by
  have hmR : (2 : ℝ) ≤ m := by exact_mod_cast hm
  have ht1 : (1 : ℝ) ≤ 3 * m := by linarith
  have hpow1 : (3 * (m : ℝ)) ^ (0.971 : ℝ) ≤ 3 * m := by
    simpa using Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num : (0.971 : ℝ) ≤ 1)
  have hpow2 : (3 * (m : ℝ)) ^ (0.861 : ℝ) ≤ 3 * m := by
    simpa using Real.rpow_le_rpow_of_exponent_le ht1 (by norm_num : (0.861 : ℝ) ≤ 1)
  have hpow3 : 3 * (m : ℝ) ≤ (3 * (m : ℝ)) ^ (3 / 2 - 1 / 4 : ℝ) := by
    simpa using Real.rpow_le_rpow_of_exponent_le ht1
      (by norm_num : (1 : ℝ) ≤ 3 / 2 - 1 / 4)
  refine ⟨by linarith, hpow1, hpow2, ⟨6 * m + 2, by omega⟩, by omega, ?_, ?_⟩
  · push_cast
    linarith
  · push_cast
    linarith

/-- Pages 345 to 346, the exact residue condition needed by the finite counting method.
The restriction at 3 is needed only in the class 3 part of the allowed domain. -/
theorem eligibility_iff {n p : ℕ} (hn : Odd n) (hn6 : n % 6 ≠ 1)
    (hp : p.Prime) (hp3 : 3 < p) (hpn : p ≤ n) :
    (n - p) % 6 ≠ 2 ↔ n % 6 = 5 ∨ ¬ 3 ∣ (p + 2) := by
  have hpodd := hp.odd_of_ne_two (by omega)
  have hp30 : p % 3 ≠ 0 := by
    intro h
    have heq := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp
      (Nat.dvd_of_mod_eq_zero h)
    omega
  obtain ⟨a, ha⟩ := hpodd
  obtain ⟨b, hb⟩ := hn
  have hp2 : p % 2 = 1 := by omega
  have hp62 : (p % 6) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 6)]
    exact hp2
  have hp63 : (p % 6) % 3 ≠ 0 := by
    rw [Nat.mod_mod_of_dvd _ (by norm_num : 3 ∣ 6)]
    exact hp30
  have hp6 : p % 6 = 1 ∨ p % 6 = 5 := by omega
  have hn6' : n % 6 = 3 ∨ n % 6 = 5 := by omega
  rw [Nat.dvd_iff_mod_eq_zero]
  rcases hp6 with h | h <;> rcases hn6' with h' | h' <;> omega

end LeanLab.Halupczok2012.Decomp329c
