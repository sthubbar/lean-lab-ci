import LeanLab.Halupczok2012.Statements
import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.Field.Basic

open scoped BigOperators
open scoped Classical

namespace LeanLab.Halupczok2012

/-- LEAF: page 345. Wu's Theorem in [17], as used for Corollary 1.3.
The number of `p1 ∈ [X1, X1+Y]` with `p1 + 2 = P_2` and `3 ∤ p1 + 2`
is `≫ Y L^{-2}` if `Y = X1^{θ1}` for `θ1 ≥ 0.971`.
We state it as: there exists `c > 0` such that for large `Y`,
the count is `≥ c Y / (log Y)^2`. -/
theorem leaf_wu_theorem :
  ∃ c > 0, ∃ Y0 > 0, ∀ (X Y : ℝ), Y0 ≤ Y → X ^ (0.971 : ℝ) ≤ Y → Y ≤ X →
    c * Y / (Real.log Y) ^ 2 ≤ (@Finset.filter ℕ (fun (p : ℕ) => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2)) (Classical.decPred _) (kRange X Y)).card := by
  sorry

/-- LEAF: page 346. The number of exceptions in Corollary 1.2 is `≪ Y L^{-A}`.
This directly extracts the bound from `Corollary2`. -/
theorem leaf_cor2_bound (hCor2 : Corollary2) (A ε c : ℝ) (hA : 0 < A) (hε : 0 < ε) (hc : 0 < c) :
  ∃ C Y0 : ℝ, ∀ X1 X2 Y : ℝ, Y0 ≤ Y →
    X2 ^ (0.861 : ℝ) ≤ Y → Y ≤ X2 → X2 + Y ≤ 2 * X1 → 2 * X1 ≤ c * Y ^ (3 / 2 - ε) →
    (cor2Exc X1 X2 Y : ℝ) ≤ C * Y * Real.log Y ^ (-A) := by
  exact hCor2 A ε c hA hε hc

/-- LEAF: page 346. For `A = 3`, `Y L^{-2}` eventually dominates `C Y L^{-3}`. -/
theorem leaf_wu_dominates_exc (c C : ℝ) (hc : 0 < c) :
  ∃ Y0 > 0, ∀ Y : ℝ, Y0 ≤ Y →
    C * Y * Real.log Y ^ (-3 : ℝ) < c * Y / (Real.log Y) ^ 2 := by
  use max (Real.exp (max (C / c) 1)) 2 + 1
  refine ⟨by positivity, ?_⟩
  intro Y hY
  have hY0_pos : 0 < max (Real.exp (max (C / c) 1)) 2 + 1 := by positivity
  have hY_pos : 0 < Y := by linarith
  have hY_gt_e : Real.exp 1 < Y := by
    calc
      Real.exp 1 ≤ Real.exp (max (C / c) 1) := Real.exp_monotone (le_max_right _ _)
      _ ≤ max (Real.exp (max (C / c) 1)) 2 := le_max_left _ _
      _ < max (Real.exp (max (C / c) 1)) 2 + 1 := by linarith
      _ ≤ Y := hY
  have hlogY_gt_1 : 1 < Real.log Y := by
    rw [← Real.log_exp 1]
    exact Real.log_lt_log (Real.exp_pos 1) hY_gt_e
  have hlogY_pos : 0 < Real.log Y := by linarith
  have hY_gt_exp_Cc : Real.exp (C / c) < Y := by
    calc
      Real.exp (C / c) ≤ Real.exp (max (C / c) 1) := Real.exp_monotone (le_max_left _ _)
      _ ≤ max (Real.exp (max (C / c) 1)) 2 := le_max_left _ _
      _ < max (Real.exp (max (C / c) 1)) 2 + 1 := by linarith
      _ ≤ Y := hY
  have hCc_lt_logY : C / c < Real.log Y := by
    rw [← Real.log_exp (C / c)]
    exact Real.log_lt_log (Real.exp_pos _) hY_gt_exp_Cc
  have hC_lt_c_logY : C < c * Real.log Y := by
    have := (div_lt_iff₀ hc).mp hCc_lt_logY
    linarith

  have hC_Y_lt : C * Y < c * Y * Real.log Y := by
    nlinarith

  have eq1 : C * Y * Real.log Y ^ (-3 : ℝ) = (C * Y) / (Real.log Y) ^ (3 : ℝ) := by
    rw [Real.rpow_neg (by linarith)]
    ring

  have eq2 : c * Y / (Real.log Y) ^ 2 = (c * Y * Real.log Y) / (Real.log Y) ^ (3 : ℝ) := by
    have hlogY_cubed : (Real.log Y) ^ (3 : ℝ) = (Real.log Y) ^ 2 * Real.log Y := by
      have : (3 : ℝ) = 2 + 1 := by norm_num
      rw [this, Real.rpow_add (by linarith)]
      simp
    rw [hlogY_cubed]
    have hlogY_ne_zero : Real.log Y ≠ 0 := by linarith
    have h1 : (c * Y * Real.log Y) / ((Real.log Y) ^ 2 * Real.log Y) = c * Y / (Real.log Y) ^ 2 := by
      rw [div_mul_eq_div_div]
      have h2 : (c * Y * Real.log Y) / (Real.log Y) ^ 2 / Real.log Y = (c * Y / (Real.log Y) ^ 2) * (Real.log Y / Real.log Y) := by ring
      rw [h2, div_self hlogY_ne_zero, mul_one]
    exact h1.symm

  rw [eq1, eq2]
  have h_pos3 : 0 < (Real.log Y) ^ (3 : ℝ) := by positivity
  exact (div_lt_div_iff_of_pos_right h_pos3).mpr hC_Y_lt

/-! ### Auxiliary results for the assembly of Corollary 3 -/

/-- Membership in `kRange`: only the two real conditions matter. -/
private theorem kRange_mem {X R : ℝ} {k : ℕ} :
    k ∈ kRange X R ↔ X < (k : ℝ) ∧ (k : ℝ) ≤ X + R := by
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨h1, h2⟩
    refine Finset.mem_filter.mpr ⟨?_, h1, h2⟩
    rw [Finset.mem_Icc]
    exact ⟨Nat.zero_le k, by exact_mod_cast h2.trans (Nat.le_ceil (X + R))⟩

/-- A prime `p > 3` with `3 ∤ p + 2` is `5` modulo `6`. -/
private theorem prime_mod_six {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3)
    (hd : ¬ 3 ∣ (p + 2)) : p % 6 = 5 := by
  obtain ⟨k, hk⟩ := hp.odd_of_ne_two h2
  have hodd : p % 2 = 1 := by omega
  have hp30 : p % 3 ≠ 0 := by
    intro h
    exact h3 (((Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).mp (Nat.dvd_of_mod_eq_zero h)).symm)
  have hp32 : p % 3 = 2 := by
    have h1 : (p % 3) < 3 := Nat.mod_lt _ (by norm_num)
    have h2' : (p + 2) % 3 ≠ 0 := by
      intro h
      exact hd (Nat.dvd_of_mod_eq_zero h)
    rw [Nat.add_mod] at h2'
    have : p % 3 = 0 ∨ p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases this with h | h | h
    · exact absurd h hp30
    · rw [h] at h2'; norm_num at h2'
    · exact h
  have h2'' : (p % 6) % 2 = 1 := by
    rw [Nat.mod_mod_of_dvd _ (by norm_num : 2 ∣ 6)]; exact hodd
  have h3'' : (p % 6) % 3 = 2 := by
    rw [Nat.mod_mod_of_dvd _ (by norm_num : 3 ∣ 6)]; exact hp32
  have hlt : p % 6 < 6 := Nat.mod_lt _ (by norm_num)
  interval_cases p % 6 <;> simp_all

/-- For odd `n ≢ 1 (6)` and such a prime `p ≤ n`, the even number `n - p` is not `2` modulo `6`,
so that `(n - p)/2` is one of the `k` counted by `cor2Exc`. -/
private theorem sub_mod_six_ne_two {n p : ℕ} (hn : Odd n) (hn6 : n % 6 ≠ 1)
    (hpn : p ≤ n) (hp6 : p % 6 = 5) : (n - p) % 6 ≠ 2 := by
  obtain ⟨k, hk⟩ := hn
  have hn' : n % 6 = 3 ∨ n % 6 = 5 := by omega
  rcases hn' with h | h <;> omega

set_option maxHeartbeats 1000000 in
/-- `cor2Exc` is the cardinality of the exception set, in the form used below. -/
private theorem cor2Exc_card (X1 X2 Y : ℝ) :
    ((kRange X1 Y).filter (fun k => (2 * k) % 6 ≠ 2 ∧
      ¬ ∃ p2 p3 : ℕ, p2.Prime ∧ p3.Prime ∧ p2 + p3 = 2 * k ∧ IsP 3 (p2 + 2) ∧
        X2 < p2 ∧ (p2 : ℝ) ≤ X2 + Y)).card = cor2Exc X1 X2 Y := by
  rw [cor2Exc]

set_option maxHeartbeats 1000000 in
/-- `Corollary 3` follows from `Corollary 2` and Wu's theorem.

The parameter of the `Corollary 2` call is the midpoint `K1 = (n - X1 - Y)/2` of the `k1`-range
that the free third prime leaves: with that choice the side condition `X2 + Y ≤ 2 * K1` is
*exactly* the hypothesis `X1 + X2 + 2Y ≤ n`.  Applying `Corollary 2` at the original `X1`, as the
sketch below used to, is not possible: `X2 + Y ≤ 2X1` is not implied by the hypotheses of
`Corollary 3`, and neither is `2X1 ≤ c Y^{3/2-ε}`. -/
private theorem assembly_of_wu (hCor2 : Corollary2)
    (c_wu : ℝ) (hc_wu : 0 < c_wu) (Y0_wu : ℝ) (_hY0_wu : 0 < Y0_wu)
    (hwu : ∀ (X Y : ℝ), Y0_wu ≤ Y → X ^ (0.971 : ℝ) ≤ Y → Y ≤ X →
      c_wu * Y / (Real.log Y) ^ 2 ≤
        ((@Finset.filter ℕ (fun (p : ℕ) => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2))
          (Classical.decPred _) (kRange X Y)).card : ℝ)) : Corollary3 := by
  intro ε c hε hc
  -- `Corollary2` at `A = 3` with twice the constant: the factor `2` pays for the one boundary
  -- point of the `k1`-window that `Corollary 2`'s own window misses.
  obtain ⟨C, Y0c, hcor⟩ := hCor2 3 ε (2 * c) (by norm_num) hε (by positivity)
  set MX : ℝ := max C 1 with hMX
  have hMX1 : 1 ≤ MX := le_max_right _ _
  have hC_le : C ≤ MX := le_max_left _ _
  have hMX0 : 0 ≤ MX := le_trans zero_le_one hMX1
  obtain ⟨Y0d, _hY0d, hdom⟩ := leaf_wu_dominates_exc c_wu (81 * MX) hc_wu
  refine ⟨max (max (max Y0_wu Y0c) Y0d) 4, ?_⟩
  intro X1 X2 Y n hY hX1pow hYX1 hX2pow hYX2 hnodd hn6 hsum hnupper

  -- thresholds
  have hY4 : (4 : ℝ) ≤ Y := by
    have h1 : max (max (max Y0_wu Y0c) Y0d) 4 ≤ Y := hY
    linarith [le_max_right (max (max Y0_wu Y0c) Y0d) (4 : ℝ)]
  have hY0wu : Y0_wu ≤ Y := by
    have h1 : Y0_wu ≤ max Y0_wu Y0c := le_max_left _ _
    have h2 : max Y0_wu Y0c ≤ max (max Y0_wu Y0c) Y0d := le_max_left _ _
    have h3 : max (max Y0_wu Y0c) Y0d ≤ max (max (max Y0_wu Y0c) Y0d) 4 := le_max_left _ _
    linarith
  have hY0c : Y0c ≤ Y := by
    have h1 : Y0c ≤ max Y0_wu Y0c := le_max_right _ _
    have h2 : max Y0_wu Y0c ≤ max (max Y0_wu Y0c) Y0d := le_max_left _ _
    have h3 : max (max Y0_wu Y0c) Y0d ≤ max (max (max Y0_wu Y0c) Y0d) 4 := le_max_left _ _
    linarith
  have hY0d' : Y0d ≤ Y := by
    have h2 : max (max Y0_wu Y0c) Y0d ≤ max (max (max Y0_wu Y0c) Y0d) 4 := le_max_left _ _
    have h4 : Y0d ≤ max (max Y0_wu Y0c) Y0d := le_max_right _ _
    linarith
  have hYpos : 0 < Y := by linarith
  have hlogpos : 0 < Real.log Y := Real.log_pos (by linarith)
  have hlog0 : 0 ≤ Real.log Y := le_of_lt hlogpos
  have hlogcube_pos : 0 < (Real.log Y) ^ 3 := by positivity
  have hX1pos : 0 < X1 := by linarith

  -- `Y ≥ (log Y)^3 / 27`, from `log Y ≤ 3 Y^{1/3}`
  have hY13 : (Y ^ (1 / 3 : ℝ)) ^ 3 = Y := by
    have h1 : (Y ^ (1 / 3 : ℝ)) ^ (3 : ℝ) = Y := by
      rw [← Real.rpow_mul (le_of_lt hYpos), show (1 / 3 : ℝ) * 3 = 1 by norm_num,
        Real.rpow_one]
    calc (Y ^ (1 / 3 : ℝ)) ^ 3 = (Y ^ (1 / 3 : ℝ)) ^ ((3 : ℕ) : ℝ) :=
          (Real.rpow_natCast _ 3).symm
      _ = (Y ^ (1 / 3 : ℝ)) ^ (3 : ℝ) := by norm_num
      _ = Y := h1
  have hlog_le : Real.log Y ≤ 3 * Y ^ (1 / 3 : ℝ) := by
    have h := Real.log_le_rpow_div (le_of_lt hYpos) (show (0 : ℝ) < 1 / 3 by norm_num)
    calc Real.log Y ≤ Y ^ (1 / 3 : ℝ) / (1 / 3) := h
      _ = 3 * Y ^ (1 / 3 : ℝ) := by field_simp
  have hcube : (Real.log Y) ^ 3 ≤ 27 * Y := by
    have h3 : (Real.log Y) ^ 3 ≤ (3 * Y ^ (1 / 3 : ℝ)) ^ 3 :=
      pow_le_pow_left₀ hlog0 hlog_le 3
    calc (Real.log Y) ^ 3 ≤ (3 * Y ^ (1 / 3 : ℝ)) ^ 3 := h3
      _ = 27 * (Y ^ (1 / 3 : ℝ)) ^ 3 := by ring
      _ = 27 * Y := by rw [hY13]
  have hL3 : (Real.log Y) ^ (-3 : ℝ) = ((Real.log Y) ^ 3)⁻¹ := by
    rw [Real.rpow_neg hlog0]
    have h3 : (Real.log Y) ^ (3 : ℝ) = (Real.log Y) ^ 3 := by
      rw [show (3 : ℝ) = ((3 : ℕ) : ℝ) from by norm_num, Real.rpow_natCast]
    rw [h3]
  have hL3nn : 0 ≤ Y * (Real.log Y) ^ (-3 : ℝ) := by
    have : 0 < (Real.log Y) ^ (-3 : ℝ) := Real.rpow_pos_of_pos hlogpos _
    positivity
  -- the key numerical fact: `27 * Y * L^{-3} ≥ 1`
  have hkey0 : 1 ≤ 27 * Y * (Real.log Y) ^ (-3 : ℝ) := by
    have heq : 27 * Y * (Real.log Y) ^ (-3 : ℝ) = 27 * Y / (Real.log Y) ^ 3 := by
      rw [hL3]; field_simp
    rw [heq, le_div_iff₀ hlogcube_pos]
    nlinarith

  set K1 : ℝ := ((n : ℝ) - X1 - Y) / 2 with hK1
  have hK1eq : 2 * K1 = (n : ℝ) - X1 - Y := by rw [hK1]; ring

  -- the `Corollary 2` bound at `K1`
  have hYpos' : 0 < Y ^ (3 / 2 - ε) := Real.rpow_pos_of_pos hYpos _
  have hcp : 0 < c * Y ^ (3 / 2 - ε) := by positivity
  have hexc : (cor2Exc K1 X2 Y : ℝ) ≤ C * Y * Real.log Y ^ (-3 : ℝ) := by
    refine hcor K1 X2 Y hY0c hX2pow hYX2 ?_ ?_
    · rw [hK1eq]; linarith
    · rw [hK1eq]; linarith
  -- Wu's count
  set S : Finset ℕ := (kRange X1 Y).filter (fun (p : ℕ) => p.Prime ∧ IsP 2 (p + 2) ∧ ¬ 3 ∣ (p + 2))
    with hSdef
  have hS : c_wu * Y / (Real.log Y) ^ 2 ≤ (S.card : ℝ) := by
    have h := hwu X1 Y hY0wu hX1pow hYX1
    rw [Finset.filter_congr_decidable] at h
    rwa [hSdef]

  -- the counting contradiction: `S` is bigger than the exception set plus the boundary point
  have hcnt : cor2Exc K1 X2 Y + 2 ≤ S.card := by
    have h1 : C * Y * Real.log Y ^ (-3 : ℝ) ≤ 27 * MX * Y * Real.log Y ^ (-3 : ℝ) := by
      have hC27 : C ≤ 27 * MX := by nlinarith
      nlinarith [mul_le_mul_of_nonneg_right hC27 hL3nn]
    have hkey : 1 ≤ 27 * MX * Y * Real.log Y ^ (-3 : ℝ) := by
      nlinarith [hkey0, hMX1, hL3nn]
    have h2 : C * Y * Real.log Y ^ (-3 : ℝ) + 2 ≤ 81 * MX * Y * Real.log Y ^ (-3 : ℝ) := by
      nlinarith [h1, hkey]
    have hdom2 : 81 * MX * Y * Real.log Y ^ (-3 : ℝ) ≤ c_wu * Y / (Real.log Y) ^ 2 :=
      le_of_lt (hdom Y hY0d')
    have h3 : ((cor2Exc K1 X2 Y : ℕ) : ℝ) + 2 ≤ (S.card : ℝ) := by
      calc ((cor2Exc K1 X2 Y : ℕ) : ℝ) + 2
          ≤ C * Y * Real.log Y ^ (-3 : ℝ) + 2 := by linarith [hexc]
        _ ≤ 81 * MX * Y * Real.log Y ^ (-3 : ℝ) := h2
        _ ≤ c_wu * Y / (Real.log Y) ^ 2 := hdom2
        _ ≤ (S.card : ℝ) := hS
    exact_mod_cast h3

  -- membership in the Wu set
  have hSsub : ∀ p ∈ S, p.Prime ∧ X1 < (p : ℝ) ∧ (p : ℝ) ≤ X1 + Y ∧ ¬ 3 ∣ (p + 2) ∧
      IsP 2 (p + 2) := by
    intro p hp
    rw [hSdef, Finset.mem_filter] at hp
    obtain ⟨hkr, hpr, hisp, hd⟩ := hp
    obtain ⟨h1, h2⟩ := kRange_mem.mp hkr
    exact ⟨hpr, h1, h2, hd, hisp⟩
  have hpgt3 : ∀ p ∈ S, 3 < p := by
    intro p hp
    have h1 : (3 : ℝ) < (p : ℝ) := by linarith [(hSsub p hp).2.1]
    exact_mod_cast h1
  have hpnn : ∀ p ∈ S, p ≤ n := by
    intro p hp
    have h2 : (p : ℝ) ≤ X1 + Y := (hSsub p hp).2.2.1
    have hX2Y : (0 : ℝ) ≤ X2 + Y := by linarith
    have : (p : ℝ) ≤ (n : ℝ) := by linarith
    exact_mod_cast this

  -- the map `p ↦ (n - p)/2`
  set tf : ℕ → ℕ := fun p => (n - p) / 2 with htf
  have ht2 : ∀ p ∈ S, 2 * tf p = n - p := by
    intro p hp
    have hpodd : Odd p := (hSsub p hp).1.odd_of_ne_two (by have := hpgt3 p hp; omega)
    have heven : Even (n - p) := Nat.Odd.sub_odd hnodd hpodd
    have hdvd : 2 ∣ n - p := even_iff_two_dvd.mp heven
    have := Nat.div_mul_cancel hdvd
    simp only [htf]
    omega
  have hmod6 : ∀ p ∈ S, (2 * tf p) % 6 ≠ 2 := by
    intro p hp
    have h2t := ht2 p hp
    have hp6 : p % 6 = 5 :=
      prime_mod_six (hSsub p hp).1 (by have := hpgt3 p hp; omega)
        (by have := hpgt3 p hp; omega) (hSsub p hp).2.2.2.1
    have hmod : (2 * tf p) % 6 = (n - p) % 6 := by rw [h2t]
    rw [hmod]
    exact sub_mod_six_ne_two hnodd hn6 (hpnn p hp) hp6
  have htmem : ∀ p ∈ S, (p : ℝ) < X1 + Y → tf p ∈ kRange K1 Y := by
    intro p hp hplt
    have hpgt : X1 < (p : ℝ) := (hSsub p hp).2.1
    have h2t := ht2 p hp
    have hpn : p ≤ n := hpnn p hp
    rw [kRange_mem]
    have hcast : ((n - p : ℕ) : ℝ) = (n : ℝ) - (p : ℝ) := by
      rw [Nat.cast_sub hpn]
    have ht_eq : ((tf p : ℕ) : ℝ) = ((n : ℝ) - (p : ℝ)) / 2 := by
      have hh : ((2 * tf p : ℕ) : ℝ) = (n : ℝ) - (p : ℝ) := by
        rw [h2t]; exact hcast
      push_cast at hh
      linarith
    constructor <;> rw [ht_eq, hK1] <;> linarith

  -- split `S` into the part below `X1 + Y` (which maps into `kRange K1 Y`) and the rest
  set S' : Finset ℕ := S.filter (fun p => (p : ℝ) < X1 + Y) with hS'def
  set S'' : Finset ℕ := S.filter (fun p => X1 + Y ≤ (p : ℝ)) with hS''def
  have hScover : S ⊆ S' ∪ S'' := by
    intro p hp
    by_cases h : (p : ℝ) < X1 + Y
    · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hp, h⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hp, not_lt.mp h⟩)
  have hS''le : S''.card ≤ 1 := by
    rw [Finset.card_le_one]
    intro a ha b hb
    rw [hS''def, Finset.mem_filter] at ha hb
    have ha2 : (a : ℝ) ≤ X1 + Y := (hSsub a ha.1).2.2.1
    have hb2 : (b : ℝ) ≤ X1 + Y := (hSsub b hb.1).2.2.1
    have : (a : ℝ) = (b : ℝ) := by linarith [ha.2, hb.2]
    exact_mod_cast this
  have hScard : S.card ≤ S'.card + 1 := by
    have h1 : S.card ≤ (S' ∪ S'').card := Finset.card_le_card hScover
    have h2 : (S' ∪ S'').card ≤ S'.card + S''.card := Finset.card_union_le _ _
    omega
  have hinj : Set.InjOn tf ↑S' := by
    intro p hp q hq heq
    have hpS : p ∈ S := (Finset.mem_filter.mp hp).1
    have hqS : q ∈ S := (Finset.mem_filter.mp hq).1
    have h2p := ht2 p hpS
    have h2q := ht2 q hqS
    have hpq : n - p = n - q := by rw [← h2p, ← h2q, heq]
    have := hpnn p hpS
    have := hpnn q hqS
    omega
  have himgcard : (S'.image tf).card = S'.card := Finset.card_image_of_injOn hinj

  -- some Wu prime is not an exception, hence gives the third prime
  set E : Finset ℕ := (kRange K1 Y).filter (fun k => (2 * k) % 6 ≠ 2 ∧
    ¬ ∃ p2 p3 : ℕ, p2.Prime ∧ p3.Prime ∧ p2 + p3 = 2 * k ∧ IsP 3 (p2 + 2) ∧
      X2 < p2 ∧ (p2 : ℝ) ≤ X2 + Y) with hEdef
  have hEcor : E.card = cor2Exc K1 X2 Y := by
    rw [hEdef]
    exact cor2Exc_card K1 X2 Y
  have hnotsub : ¬ (S'.image tf ⊆ E) := by
    intro hsub
    have h1 : (S'.image tf).card ≤ E.card := Finset.card_le_card hsub
    have h2 : E.card = cor2Exc K1 X2 Y := hEcor
    omega
  obtain ⟨k, hkimg, hknot⟩ := Finset.not_subset.mp hnotsub
  obtain ⟨p, hpS', hpk⟩ := Finset.mem_image.mp hkimg
  have hpS : p ∈ S := (Finset.mem_filter.mp hpS').1
  have hplt : (p : ℝ) < X1 + Y := (Finset.mem_filter.mp hpS').2
  have htmem' : tf p ∈ kRange K1 Y := htmem p hpS hplt
  rw [← hpk] at hknot
  have hgood : ¬ ((2 * tf p) % 6 ≠ 2 ∧
      ¬ ∃ p2 p3 : ℕ, p2.Prime ∧ p3.Prime ∧ p2 + p3 = 2 * tf p ∧ IsP 3 (p2 + 2) ∧
        X2 < p2 ∧ (p2 : ℝ) ≤ X2 + Y) := by
    intro hcon
    exact hknot (Finset.mem_filter.mpr ⟨htmem', hcon⟩)
  have hmod' : (2 * tf p) % 6 ≠ 2 := hmod6 p hpS
  have hrep : ∃ p2 p3 : ℕ, p2.Prime ∧ p3.Prime ∧ p2 + p3 = 2 * tf p ∧ IsP 3 (p2 + 2) ∧
      X2 < p2 ∧ (p2 : ℝ) ≤ X2 + Y := by
    by_contra hc'
    exact hgood ⟨hmod', hc'⟩
  obtain ⟨p2, p3, hp2, hp3, hsum23, hisp3, hX2lt, hX2le⟩ := hrep
  have hsum3 : p + p2 + p3 = n := by
    have h2t := ht2 p hpS
    have := hpnn p hpS
    omega
  exact ⟨p, p2, p3, (hSsub p hpS).1, hp2, hp3, hsum3, (hSsub p hpS).2.1, (hSsub p hpS).2.2.1,
    hX2lt, hX2le, (hSsub p hpS).2.2.2.2, hisp3⟩

/-- LEAF: The assembly theorem for Corollary 3.
"So not all of them can be exceptions in Corollary 1.2, so there is at least one of them being the sum of two primes p2 and p3... Note that Corollary 1.2 is applicable since we assumed that X1 + X2 + 2Y <= n << Y^{3/2 - \epsilon}..." -/
theorem corollary_3_assembly_leaf (hCor2 : Corollary2) : Corollary3 := by
  obtain ⟨c_wu, hc_wu, Y0_wu, Y0_wu_pos, hwu⟩ := leaf_wu_theorem
  exact assembly_of_wu hCor2 c_wu hc_wu Y0_wu Y0_wu_pos hwu

/-- The assembly theorem for Corollary 3.
Blocked. -/
theorem corollary_3_assembly (hCor2 : Corollary2) : Corollary3 := corollary_3_assembly_leaf hCor2

end LeanLab.Halupczok2012
