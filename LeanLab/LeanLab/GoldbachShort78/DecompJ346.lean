import LeanLab.GoldbachShort78.BHPTiling

open LeanLab.GoldbachShort78

namespace LeanLab.GoldbachShort78

/-!
AI wrote the Lean code, Codex task225. Binary Goldbach is OPEN.
Li, arXiv:2308.04458v8, Theorem 2, p. 2.
https://arxiv.org/abs/2308.04458
The source has positive epsilon and integer x. Both are retained below.
-/

/-- The two rows of Li Theorem 2 p. 2 used in this reduction.
The strict inequalities follow from the strict table bounds for LB. -/
def LiTheoremTwoLower : Prop :=
  ∀ ε : ℝ, 0 < ε → ε ≤ 0.001 → ∃ X : ℝ, 1 < X ∧ ∀ n : ℕ, X ≤ n →
    (0.209 : ℝ) * (n : ℝ) ^ (0.524 + ε : ℝ) / Real.log n <
      ((primeInterval ((n : ℝ) - (n : ℝ) ^ (0.524 + ε : ℝ)) n).card : ℝ) ∧
    (0.249 : ℝ) * (n : ℝ) ^ (0.525 + ε : ℝ) / Real.log n <
      ((primeInterval ((n : ℝ) - (n : ℝ) ^ (0.525 + ε : ℝ)) n).card : ℝ)

/-- LEAF Li arXiv:2308.04458v8, Theorem 2, p. 2, rows 0.524 and 0.525.
Only this published analytic input remains unformalized in the reduction. -/
theorem li_theorem_two_lower : LiTheoremTwoLower := by
  sorry

/-- Bernoulli bounds the shift loss by a power with exponent 2a minus one. -/
theorem bhp_shift_power_bound {t a : ℝ} (ht : 0 < t) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    (t + t ^ a) ^ a ≤ t ^ a + a * t ^ (2 * a - 1) := by
  have hs : -1 ≤ t ^ a / t := le_trans (by norm_num) (by positivity : 0 ≤ t ^ a / t)
  have hb := rpow_one_add_le_one_add_mul_self hs ha0 ha1
  have heq : t + t ^ a = t * (1 + t ^ a / t) := by field_simp
  rw [heq, Real.mul_rpow ht.le (by positivity)]
  have hp : t ^ a * (t ^ a / t) = t ^ (2 * a - 1) := by
    rw [Real.rpow_sub ht, Real.rpow_one, show 2 * a = a + a by ring,
      Real.rpow_add ht]
    ring
  have hm := mul_le_mul_of_nonneg_left hb (Real.rpow_nonneg ht.le a)
  nlinarith [hp]

/-- The number of primes in an interval is at most its length plus one. -/
theorem primeInterval_card_le_length {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    ((primeInterval a b).card : ℝ) ≤ b - a + 1 := by
  classical
  have hb : 0 ≤ b := ha.trans hab
  have hsub : primeInterval a b ⊆ Finset.Ioc ⌊a⌋₊ ⌊b⌋₊ := by
    intro p hp
    obtain ⟨hpa, hpb, _⟩ := mem_primeInterval.mp hp
    exact Finset.mem_Ioc.mpr ⟨(Nat.floor_lt ha).mpr hpa, (Nat.le_floor_iff hb).mpr hpb⟩
  have hc := Finset.card_le_card hsub
  rw [Nat.card_Ioc] at hc
  have hf : ⌊a⌋₊ ≤ ⌊b⌋₊ := Nat.floor_mono hab
  have hcr : ((primeInterval a b).card : ℝ) ≤ (⌊b⌋₊ : ℝ) - ⌊a⌋₊ := by
    exact_mod_cast hc
  have hbl := Nat.floor_le hb
  have hal := Nat.lt_floor_add_one a
  linarith

/-- A backward interval loses at most the trivial count below the forward base. -/
theorem backward_card_le_forward_add {a t x E : ℝ}
    (ha : 0 ≤ a) (hat : a ≤ t) (_htx : t ≤ x) (hE : t - a ≤ E) :
    ((primeInterval a x).card : ℝ) ≤
      (primeInterval t x).card + E + 1 := by
  classical
  have hsub : primeInterval a x ⊆ primeInterval a t ∪ primeInterval t x := by
    intro p hp
    obtain ⟨hpa, hpx, hprime⟩ := mem_primeInterval.mp hp
    by_cases hpt : (p : ℝ) ≤ t
    · exact Finset.mem_union_left _ (mem_primeInterval.mpr ⟨hpa, hpt, hprime⟩)
    · exact Finset.mem_union_right _ (mem_primeInterval.mpr ⟨lt_of_not_ge hpt, hpx, hprime⟩)
  have hc := (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  have hcr : ((primeInterval a x).card : ℝ) ≤
      (primeInterval a t).card + (primeInterval t x).card := by exact_mod_cast hc
  have hl := primeInterval_card_le_length ha hat
  linarith

/-- The integer endpoint just below t plus t^0.525 has only a t^0.05 shift loss. -/
theorem bhp_floor_shift_geometry {t : ℝ} (ht : 2 ≤ t) :
    let n : ℕ := ⌊t + t ^ (0.525 : ℝ)⌋₊
    t ≤ (n : ℝ) ∧ (n : ℝ) ≤ t + t ^ (0.525 : ℝ) ∧
      0 ≤ (n : ℝ) - (n : ℝ) ^ (0.525 : ℝ) ∧
      (n : ℝ) - (n : ℝ) ^ (0.525 : ℝ) ≤ t ∧
      t - ((n : ℝ) - (n : ℝ) ^ (0.525 : ℝ)) ≤ t ^ (0.05 : ℝ) + 1 ∧
      Real.log n ≤ Real.log t + 1 := by
  dsimp only
  let n : ℕ := ⌊t + t ^ (0.525 : ℝ)⌋₊
  change t ≤ (n : ℝ) ∧ (n : ℝ) ≤ t + t ^ (0.525 : ℝ) ∧
    0 ≤ (n : ℝ) - (n : ℝ) ^ (0.525 : ℝ) ∧
    (n : ℝ) - (n : ℝ) ^ (0.525 : ℝ) ≤ t ∧
    t - ((n : ℝ) - (n : ℝ) ^ (0.525 : ℝ)) ≤ t ^ (0.05 : ℝ) + 1 ∧
    Real.log n ≤ Real.log t + 1
  have ht0 : 0 < t := by linarith
  have ht1 : 1 ≤ t := by linarith
  have hpow1 := Real.one_le_rpow ht1 (by norm_num : (0 : ℝ) ≤ 0.525)
  have hpowt := Real.rpow_le_self_of_one_le ht1 (by norm_num : (0.525 : ℝ) ≤ 1)
  have hnle : (n : ℝ) ≤ t + t ^ (0.525 : ℝ) := Nat.floor_le (by positivity)
  have hngt : t + t ^ (0.525 : ℝ) < (n : ℝ) + 1 := Nat.lt_floor_add_one _
  have htn : t ≤ (n : ℝ) := by linarith
  have hn1 : (1 : ℝ) ≤ n := by linarith
  have hn0 : (0 : ℝ) < n := by linarith
  have hnpow := Real.rpow_le_self_of_one_le hn1 (by norm_num : (0.525 : ℝ) ≤ 1)
  have htpow := Real.rpow_le_rpow ht0.le htn (by norm_num : (0 : ℝ) ≤ 0.525)
  have hupper := Real.rpow_le_rpow (Nat.cast_nonneg n) hnle
    (by norm_num : (0 : ℝ) ≤ 0.525)
  have hshift := bhp_shift_power_bound ht0 (by norm_num : (0 : ℝ) ≤ 0.525)
    (by norm_num : (0.525 : ℝ) ≤ 1)
  rw [show (2 : ℝ) * 0.525 - 1 = 0.05 by norm_num] at hshift
  have he0 : 0 ≤ t ^ (0.05 : ℝ) := Real.rpow_nonneg ht0.le _
  refine ⟨htn, hnle, by linarith, by linarith, by linarith, ?_⟩
  calc
    Real.log n ≤ Real.log (2 * t) := Real.log_le_log hn0 (by linarith)
    _ = Real.log 2 + Real.log t := Real.log_mul (by norm_num) ht0.ne'
    _ ≤ Real.log t + 1 := by linarith [Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)]

/-- The trivial shift error is negligible relative to t^0.525 divided by log t. -/
theorem bhp_shift_error_small {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ t : ℝ in Filter.atTop,
      (t ^ (0.05 : ℝ) + 2) * Real.log t < δ * t ^ (0.525 : ℝ) := by
  have hb := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.475)).def
    (show 0 < δ / 4 by positivity)
  filter_upwards [hb, Filter.eventually_ge_atTop (1 : ℝ)] with t ht ht1
  have ht0 : 0 < t := by linarith
  have hl : 0 ≤ Real.log t := Real.log_nonneg ht1
  have he1 : 1 ≤ t ^ (0.05 : ℝ) := Real.one_le_rpow ht1 (by norm_num)
  have hp : t ^ (0.05 : ℝ) * t ^ (0.475 : ℝ) = t ^ (0.525 : ℝ) := by
    rw [← Real.rpow_add ht0]
    norm_num
  simp only [Real.norm_eq_abs, abs_of_nonneg hl,
    abs_of_nonneg (Real.rpow_nonneg ht0.le (0.475 : ℝ))] at ht
  have hm := mul_le_mul_of_nonneg_left ht
    (show 0 ≤ t ^ (0.05 : ℝ) by positivity)
  have hsum : (t ^ (0.05 : ℝ) + 2) * Real.log t ≤
      3 * (t ^ (0.05 : ℝ) * Real.log t) := by nlinarith
  have hp0 : 0 < t ^ (0.525 : ℝ) := Real.rpow_pos_of_pos ht0 _
  nlinarith [hp]

/-- The backward power interval is exactly the prime-counting difference printed by Li. -/
theorem primeInterval_power_card_eq_primeCounting {n : ℕ} {a : ℝ}
    (hn : 1 ≤ n) (ha : a ≤ 1) :
    (primeInterval ((n : ℝ) - (n : ℝ) ^ a) n).card =
      Nat.primeCounting n - Nat.primeCounting ⌊(n : ℝ) - (n : ℝ) ^ a⌋₊ := by
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hpow := Real.rpow_le_self_of_one_le hn1 ha
  have hpos : 0 ≤ (n : ℝ) ^ a := Real.rpow_nonneg (Nat.cast_nonneg n) a
  simpa only [Nat.floor_natCast] using
    primeInterval_card_eq_primeCounting_sub (sub_nonneg.mpr hpow) (sub_le_self _ hpos)

/-- The cited interval input is equivalent to the two printed prime-counting rows. -/
theorem li_theorem_two_lower_iff_primeCounting :
    LiTheoremTwoLower ↔
      ∀ ε : ℝ, 0 < ε → ε ≤ 0.001 → ∃ X : ℝ, 1 < X ∧ ∀ n : ℕ, X ≤ n →
        (0.209 : ℝ) * (n : ℝ) ^ (0.524 + ε : ℝ) / Real.log n <
          ((Nat.primeCounting n - Nat.primeCounting
            ⌊(n : ℝ) - (n : ℝ) ^ (0.524 + ε : ℝ)⌋₊ : ℕ) : ℝ) ∧
        (0.249 : ℝ) * (n : ℝ) ^ (0.525 + ε : ℝ) / Real.log n <
          ((Nat.primeCounting n - Nat.primeCounting
            ⌊(n : ℝ) - (n : ℝ) ^ (0.525 + ε : ℝ)⌋₊ : ℕ) : ℝ) := by
  unfold LiTheoremTwoLower
  constructor
  · intro h ε hε hs
    obtain ⟨X, hX, hC⟩ := h ε hε hs
    refine ⟨X, hX, ?_⟩
    intro n hn
    have hn1 : 1 ≤ n := by
      have : (1 : ℝ) ≤ n := le_trans hX.le hn
      exact_mod_cast this
    have he1 := primeInterval_power_card_eq_primeCounting (a := 0.524 + ε) hn1 (by linarith)
    have he2 := primeInterval_power_card_eq_primeCounting (a := 0.525 + ε) hn1 (by linarith)
    simpa only [he1, he2] using hC n hn
  · intro h ε hε hs
    obtain ⟨X, hX, hC⟩ := h ε hε hs
    refine ⟨X, hX, ?_⟩
    intro n hn
    have hn1 : 1 ≤ n := by
      have : (1 : ℝ) ≤ n := le_trans hX.le hn
      exact_mod_cast this
    have he1 := primeInterval_power_card_eq_primeCounting (a := 0.524 + ε) hn1 (by linarith)
    have he2 := primeInterval_power_card_eq_primeCounting (a := 0.525 + ε) hn1 (by linarith)
    simpa only [he1, he2] using hC n hn

/-- CONDITIONAL ON a backward count with any coefficient strictly above 9/100.
Integer endpoints suffice for the sealed forward count at every large real base. -/
theorem bhp_forward_of_backward {c : ℝ} (hc : (9 / 100 : ℝ) < c)
    (hin : ∃ X : ℝ, ∀ n : ℕ, X ≤ n →
      c * (n : ℝ) ^ (0.525 : ℝ) / Real.log n <
        ((primeInterval ((n : ℝ) - (n : ℝ) ^ (0.525 : ℝ)) n).card : ℝ)) :
    BHPPrintedCount := by
  classical
  obtain ⟨X, hX⟩ := hin
  let d : ℝ := (c - 9 / 100) / 2
  let k : ℝ := 9 / 100 + d
  have hd : 0 < d := by dsimp [d]; linarith
  have hk : 0 < k := by dsimp [k]; linarith
  have hc0 : 0 < c := by linarith
  have hck : c - k = d := by dsimp [k, d]; ring
  have hevent : ∀ᶠ t : ℝ in Filter.atTop,
      (9 / 100 : ℝ) * t ^ (0.525 : ℝ) / Real.log t <
        ((primeInterval t (t + t ^ (0.525 : ℝ))).card : ℝ) := by
    filter_upwards [bhp_shift_error_small hd,
      Real.tendsto_log_atTop.eventually_ge_atTop (k / d),
      Filter.eventually_ge_atTop (max X 2)] with t herr hlog ht
    have htX : X ≤ t := (le_max_left _ _).trans ht
    have ht2 : 2 ≤ t := (le_max_right _ _).trans ht
    have ht0 : 0 < t := by linarith
    have hlt : 0 < Real.log t := Real.log_pos (by linarith)
    let n : ℕ := ⌊t + t ^ (0.525 : ℝ)⌋₊
    obtain ⟨htn, hnx, ha0, hat, hE, hln⟩ := bhp_floor_shift_geometry ht2
    change t ≤ (n : ℝ) at htn
    change (n : ℝ) ≤ t + t ^ (0.525 : ℝ) at hnx
    change 0 ≤ (n : ℝ) - (n : ℝ) ^ (0.525 : ℝ) at ha0
    change (n : ℝ) - (n : ℝ) ^ (0.525 : ℝ) ≤ t at hat
    change t - ((n : ℝ) - (n : ℝ) ^ (0.525 : ℝ)) ≤ t ^ (0.05 : ℝ) + 1 at hE
    change Real.log n ≤ Real.log t + 1 at hln
    have hn1 : (1 : ℝ) < n := by linarith
    have hln0 : 0 < Real.log n := Real.log_pos hn1
    have hpow : t ^ (0.525 : ℝ) ≤ (n : ℝ) ^ (0.525 : ℝ) :=
      Real.rpow_le_rpow ht0.le htn (by norm_num)
    have hcount := hX n (htX.trans htn)
    have hsplit := backward_card_le_forward_add ha0 hat htn hE
    have hsub : primeInterval t n ⊆ primeInterval t (t + t ^ (0.525 : ℝ)) := by
      intro p hp
      obtain ⟨hpt, hpn, hprime⟩ := mem_primeInterval.mp hp
      exact mem_primeInterval.mpr ⟨hpt, hpn.trans hnx, hprime⟩
    have hcard : ((primeInterval t n).card : ℝ) ≤
        (primeInterval t (t + t ^ (0.525 : ℝ))).card := by
      exact_mod_cast Finset.card_le_card hsub
    have hlogmargin : k * (Real.log t + 1) ≤ c * Real.log t := by
      have hmul := (div_le_iff₀ hd).mp hlog
      nlinarith [hck]
    have hmain : k * t ^ (0.525 : ℝ) / Real.log t ≤
        c * (n : ℝ) ^ (0.525 : ℝ) / Real.log n := by
      calc
        k * t ^ (0.525 : ℝ) / Real.log t ≤
            c * t ^ (0.525 : ℝ) / (Real.log t + 1) := by
          apply (div_le_div_iff₀ hlt (by linarith : 0 < Real.log t + 1)).mpr
          nlinarith [mul_nonneg (sub_nonneg.mpr hlogmargin)
            (Real.rpow_nonneg ht0.le (0.525 : ℝ))]
        _ ≤ c * t ^ (0.525 : ℝ) / Real.log n :=
          div_le_div_of_nonneg_left (by positivity) hln0 hln
        _ ≤ c * (n : ℝ) ^ (0.525 : ℝ) / Real.log n :=
          div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hc0.le) hln0.le
    have herror : t ^ (0.05 : ℝ) + 2 < d * t ^ (0.525 : ℝ) / Real.log t :=
      (lt_div_iff₀ hlt).mpr herr
    have hidentity : k * t ^ (0.525 : ℝ) / Real.log t =
        (9 / 100 : ℝ) * t ^ (0.525 : ℝ) / Real.log t +
          d * t ^ (0.525 : ℝ) / Real.log t := by dsimp [k]; ring
    linarith
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp hevent
  exact ⟨max T 2, by have := le_max_right T 2; linarith,
    fun t ht => hT t ((le_max_left _ _).trans ht)⟩

/-- CONDITIONAL ON Li Theorem 2 p. 2. Its 0.524 row with positive slack
supplies exponent 0.525 and coefficient 0.209 for the elementary shift. -/
theorem bhp_forward_of_li (hLi : LiTheoremTwoLower) : BHPPrintedCount := by
  obtain ⟨X, _hX, hcount⟩ := hLi 0.001 (by norm_num) (by norm_num)
  apply bhp_forward_of_backward (c := 0.209) (by norm_num)
  refine ⟨X, ?_⟩
  intro n hn
  have h := (hcount n hn).1
  rw [show (0.524 : ℝ) + 0.001 = 0.525 by norm_num] at h
  exact h

/-- A finite local count certifies that the Li row inequalities have genuine instances. -/
theorem li_backward_local_instance {a c : ℝ} (ha0 : 0 < a) (ha1 : a ≤ 1)
    (hc : c ≤ 0.249) :
    c * (3 : ℝ) ^ a / Real.log 3 <
      ((primeInterval ((3 : ℝ) - (3 : ℝ) ^ a) 3).card : ℝ) := by
  classical
  have hp1 : 1 < (3 : ℝ) ^ a := Real.one_lt_rpow (by norm_num) ha0
  have hp3 : (3 : ℝ) ^ a ≤ 3 := Real.rpow_le_self_of_one_le (by norm_num) ha1
  have hpair : ({2, 3} : Finset ℕ) ⊆ primeInterval ((3 : ℝ) - (3 : ℝ) ^ a) 3 := by
    intro p hp
    simp only [Finset.mem_insert, Finset.mem_singleton] at hp
    rcases hp with rfl | rfl
    · exact mem_primeInterval.mpr ⟨by norm_num; linarith, by norm_num, Nat.prime_two⟩
    · exact mem_primeInterval.mpr ⟨by norm_num; linarith, le_rfl, Nat.prime_three⟩
  have hcard : (2 : ℝ) ≤ (primeInterval ((3 : ℝ) - (3 : ℝ) ^ a) 3).card := by
    have := Finset.card_le_card hpair
    norm_num at this
    exact_mod_cast this
  have hl : (0.6931471803 : ℝ) < Real.log 3 :=
    lt_of_lt_of_le Real.log_two_gt_d9 (Real.log_le_log (by norm_num) (by norm_num))
  have hl0 : 0 < Real.log 3 := by linarith
  have hnum : c * (3 : ℝ) ^ a < 2 * Real.log 3 := by
    have hc' := mul_le_mul_of_nonneg_right hc (show 0 ≤ (3 : ℝ) ^ a from Real.rpow_nonneg (by norm_num) a)
    nlinarith
  exact lt_of_lt_of_le ((div_lt_iff₀ hl0).mpr hnum) hcard

/-- Both source rows hold locally at n equal to three for every allowed epsilon. -/
theorem li_theorem_two_local_instance {ε : ℝ} (hε : 0 < ε) (hs : ε ≤ 0.001) :
    (0.209 : ℝ) * (3 : ℝ) ^ (0.524 + ε : ℝ) / Real.log 3 <
      ((primeInterval ((3 : ℝ) - (3 : ℝ) ^ (0.524 + ε : ℝ)) 3).card : ℝ) ∧
    (0.249 : ℝ) * (3 : ℝ) ^ (0.525 + ε : ℝ) / Real.log 3 <
      ((primeInterval ((3 : ℝ) - (3 : ℝ) ^ (0.525 + ε : ℝ)) 3).card : ℝ) := by
  exact ⟨li_backward_local_instance (by linarith) (by linarith) (by norm_num),
    li_backward_local_instance (by linarith) (by linarith) le_rfl⟩

/-- Exact arithmetic for all six lower rows of Li Table 1 on p. 40.
This checks the displayed loss budgets, not the analytic or numerical integral bounds. -/
theorem li_table_lower_constants :
    (1 : ℝ) - 2 * 0.241 - 0.514 = 0.004 ∧
    (1 : ℝ) - 2 * 0.241 - 0.443 = 0.075 ∧
    (1 : ℝ) - 2 * 0.241 - 0.384 = 0.134 ∧
    (1 : ℝ) - 2 * 0.241 - 0.349 = 0.169 ∧
    (1 : ℝ) - 2 * 0.241 - 0.309 = 0.209 ∧
    (1 : ℝ) - 2 * 0.241 - 0.269 = 0.249 ∧
    (9 / 100 : ℝ) < 0.209 ∧ (9 / 100 : ℝ) < 0.249 := by
  norm_num

/-- The count scale from packing existence windows of exponent 0.52 is too small.
This is a limit comparison only, not a prime-count estimate or a paper error. -/
theorem li_existence_scale_negligible :
    Filter.Tendsto
      (fun t : ℝ => t ^ (0.005 : ℝ) / (t ^ (0.525 : ℝ) / Real.log t))
      Filter.atTop (nhds 0) := by
  have hlim := (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 0.52)).tendsto_div_nhds_zero
  apply hlim.congr'
  filter_upwards [Filter.eventually_gt_atTop (1 : ℝ)] with t ht
  have ht0 : 0 < t := by linarith
  have hp0 : t ^ (0.005 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos ht0 _).ne'
  have hp1 : t ^ (0.525 : ℝ) ≠ 0 := (Real.rpow_pos_of_pos ht0 _).ne'
  have hpower : t ^ (0.52 : ℝ) = t ^ (0.525 : ℝ) / t ^ (0.005 : ℝ) := by
    rw [← Real.rpow_sub ht0]
    norm_num
  rw [hpower, div_div_eq_mul_div, div_div_eq_mul_div]
  ring

/-- LEAF p. 562 display
The main printed count inequality of BHP 2001. -/
theorem leaf_bhp_1 :
  ∃ T : ℝ, 1 < T ∧ ∀ t : ℝ, T ≤ t →
    (9 / 100 : ℝ) * t ^ (0.525 : ℝ) / Real.log t <
      ((primeInterval t (t + t ^ (0.525 : ℝ))).card : ℝ) := by
  exact bhp_forward_of_li li_theorem_two_lower

/-- Assembly of the final printed display from the leaf. -/
theorem bhp_printed_count_assembly : BHPPrintedCount := by
  exact leaf_bhp_1

end LeanLab.GoldbachShort78
