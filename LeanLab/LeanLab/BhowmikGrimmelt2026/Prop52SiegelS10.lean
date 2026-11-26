/-
S10-03 and S10-04, BhowmikGrimmelt2026, P0029 Proposition 5.2 on page 18, route burst
burst-20261124, step prop52siegel.

The two open leaves `leaf_no_siegel_zero_part` and `leaf_siegel_zero_part` of
SPLIT_prop52.lean are the two parts of the lab transcription `Prop52`, which allows every level
`R` up to `N`. `not_prop52_dq4` in DQ4Decisions.lean refutes `Prop52` at `R = N`: the one point
interval at a large prime `p` gives the modulus one character the value `log p - 2` at least,
while the right side is at most `|C|`.

This file states the two leaf bodies as named Props, checks by `rfl` that they are exactly the
leaf types, and proves without any open step:

* `not_both_leaves_S10`: the two leaves cannot both hold, through `prop52_of_leaves_S10`, the
  split assembly with the leaves as hypotheses, and `not_prop52_dq4`.
* `leaf1_forces_siegel_S10`: leaf 1 forces a Siegel zero of level `N` for every large `N`.
  So leaf 1 is false as soon as some arbitrarily large level carries no Siegel zero,
  `leaf1_false_of_sparse_siegel_S10`, for instance under GRH.
* `leaf2_forbids_siegel_S10`: leaf 2 forces that no level `N` with `N` large carries a Siegel
  zero. So leaf 2 is false as soon as Siegel zeros occur at arbitrarily large levels,
  `leaf2_false_of_frequent_siegel_S10`.

Neither leaf is refuted outright: that would decide the Landau Siegel zero question.
FALSE as a pair, FALSE-CONDITIONAL one by one. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BhowmikGrimmelt2026.SPLIT_prop52
import LeanLab.BhowmikGrimmelt2026.DQ4Decisions

namespace LeanLab.BhowmikGrimmelt2026

open ArithmeticFunction

attribute [local instance] Classical.propDecidable

/-- The body of `leaf_no_siegel_zero_part`, part (1) of Proposition 5.2, P0029 page 18,
as transcribed in SPLIT_prop52.lean. -/
def Leaf1BodyS10 : Prop :=
    ∃ c C : ℝ, 0 < c ∧ ∀ (N : ℕ) (R : ℝ),
      2 ≤ Real.exp (Real.sqrt (Real.log N)) →
      Real.exp (Real.sqrt (Real.log N)) ≤ R → R ≤ N →
      (¬ ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
        SiegelZero R r χ β) →
      primSum R (fun _ _ χ => intervalMax N R
        (fun n => (vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0)) ≤
        C * Real.exp (-c * Real.log N / Real.log R)

/-- The body of `leaf_siegel_zero_part`, part (2) of Proposition 5.2, P0029 page 18,
as transcribed in SPLIT_prop52.lean. -/
def Leaf2BodyS10 : Prop :=
    ∃ c C : ℝ, 0 < c ∧ ∀ (N : ℕ) (R : ℝ),
      2 ≤ Real.exp (Real.sqrt (Real.log N)) →
      Real.exp (Real.sqrt (Real.log N)) ≤ R → R ≤ N →
      ∀ (r₀ : ℕ) [NeZero r₀] (χ₀ : DirichletCharacter ℂ r₀) (β : ℝ),
        SiegelZero R r₀ χ₀ β →
      primSum R (fun r _ χ => intervalMax N R
        (fun n => (vonMangoldt n : ℂ) * χ n - (if χ = 1 then 1 else 0) +
          (if r = r₀ ∧ HEq χ χ₀ then (n : ℂ) ^ ((β : ℂ) - 1) else 0))) ≤
        C * (1 - β) * Real.log N * Real.exp (-c * Real.log N / Real.log R)

/-- Match check: `Leaf1BodyS10` is exactly the type of `leaf_no_siegel_zero_part`.
The proof is `rfl` on the type only and does not use the open leaf. -/
theorem leaf1_match_S10 : Leaf1BodyS10 = type_of% leaf_no_siegel_zero_part := rfl

/-- Match check: `Leaf2BodyS10` is exactly the type of `leaf_siegel_zero_part`.
The proof is `rfl` on the type only and does not use the open leaf. -/
theorem leaf2_match_S10 : Leaf2BodyS10 = type_of% leaf_siegel_zero_part := rfl

/-- The split assembly `prop52_split` with the two leaves as hypotheses: they give `Prop52`.
Same proof, using the proved leaves 3 and 4 of SPLIT_prop52.lean. -/
theorem prop52_of_leaves_S10 (h1L : Leaf1BodyS10) (h2L : Leaf2BodyS10) : Prop52 := by
  obtain ⟨c₁, C₁, hc₁, h₁⟩ := h1L
  obtain ⟨c₂, C₂, hc₂, h₂⟩ := h2L
  refine ⟨min c₁ c₂, lt_min hc₁ hc₂, max (max C₁ 0) (max C₂ 0), ?_⟩
  intro N R hN hR hRN
  obtain ⟨hRpos, hNpos⟩ := leaf_range_logs N R hN hR
  have hc : 0 < min c₁ c₂ := lt_min hc₁ hc₂
  have hC₀ : (0 : ℝ) ≤ max (max C₁ 0) (max C₂ 0) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  constructor
  · intro hns
    refine (h₁ N R hN hR hRN hns).trans ?_
    exact leaf_saving_mono hc (min_le_left c₁ c₂) hNpos hRpos
      (le_trans (le_max_left C₁ 0) (le_max_left (max C₁ 0) (max C₂ 0))) hC₀
  · intro r₀ _inst χ₀ β hS
    have hβ : β < 1 := hS.2.2.2.2.1
    have h1β : (0 : ℝ) < 1 - β := by linarith
    have hfac : (0 : ℝ) ≤ (1 - β) * Real.log N := mul_nonneg h1β.le hNpos
    have hC₂ : C₂ ≤ max (max C₁ 0) (max C₂ 0) :=
      le_trans (le_max_left C₂ 0) (le_max_right (max C₁ 0) (max C₂ 0))
    have hCC : C₂ * (1 - β) * Real.log N ≤ max (max C₁ 0) (max C₂ 0) * (1 - β) * Real.log N := by
      calc C₂ * (1 - β) * Real.log N = C₂ * ((1 - β) * Real.log N) := by ring
        _ ≤ max (max C₁ 0) (max C₂ 0) * ((1 - β) * Real.log N) :=
              mul_le_mul_of_nonneg_right hC₂ hfac
        _ = max (max C₁ 0) (max C₂ 0) * (1 - β) * Real.log N := by ring
    have hC' : (0 : ℝ) ≤ max (max C₁ 0) (max C₂ 0) * (1 - β) * Real.log N :=
      mul_nonneg (mul_nonneg hC₀ h1β.le) hNpos
    refine (h₂ N R hN hR hRN r₀ χ₀ β hS).trans ?_
    calc C₂ * (1 - β) * Real.log N * Real.exp (-c₂ * Real.log N / Real.log R)
        = (C₂ * (1 - β) * Real.log N) * Real.exp (-c₂ * Real.log N / Real.log R) := by ring
      _ ≤ (max (max C₁ 0) (max C₂ 0) * (1 - β) * Real.log N) *
            Real.exp (-(min c₁ c₂) * Real.log N / Real.log R) :=
            leaf_saving_mono hc (min_le_right c₁ c₂) hNpos hRpos hCC hC'
      _ = max (max C₁ 0) (max C₂ 0) * (1 - β) * Real.log N *
            Real.exp (-(min c₁ c₂) * Real.log N / Real.log R) := by ring

/-- (a) FALSE as a pair: the two leaves of SPLIT_prop52.lean cannot both hold, by the split
assembly and `not_prop52_dq4`. PROVED, no open step. -/
theorem not_both_leaves_S10 : ¬ (Leaf1BodyS10 ∧ Leaf2BodyS10) :=
  fun h => not_prop52_dq4 (prop52_of_leaves_S10 h.1 h.2)

/-- The range conditions of Proposition 5.2 hold at `R = N` once `log N ≥ 1`. -/
theorem range_at_level_N_S10 {N : ℕ} (h : 1 ≤ Real.log N) :
    2 ≤ Real.exp (Real.sqrt (Real.log N)) ∧ Real.exp (Real.sqrt (Real.log N)) ≤ (N : ℝ) := by
  have hN0 : (0 : ℝ) < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0
      simp at h
      linarith
    · exact_mod_cast h0
  have hsq1 : 1 ≤ Real.sqrt (Real.log N) := Real.le_sqrt_of_sq_le (by nlinarith)
  have hsqle : Real.sqrt (Real.log N) ≤ Real.log N :=
    Real.sqrt_le_iff.mpr ⟨by linarith, by nlinarith⟩
  constructor
  · have h1 := Real.add_one_le_exp (1 : ℝ)
    have h2 := Real.exp_le_exp.mpr hsq1
    linarith
  · calc Real.exp (Real.sqrt (Real.log N)) ≤ Real.exp (Real.log N) := Real.exp_le_exp.mpr hsqle
      _ = N := Real.exp_log hN0

/-- At level `R = N`, the part (1) sum is at least `log p - 2` for every prime `p ≤ N`: the one
point interval at `p` for the modulus one character, P0029 page 18 display (1). -/
theorem leaf1_sum_ge_S10 {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N) :
    Real.log p - 2 ≤ primSum (N : ℝ) (fun _ _ χ => intervalMax N (N : ℝ)
        (fun n => (vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0)) := by
  have hR1 : (1 : ℝ) ≤ N := by exact_mod_cast (hp.one_lt.le.trans hpN)
  have hlow := primSum_ge_modOne_dq4 hR1
    (hF := fun r _ χ => intervalMax_nonneg_dq4 N (by linarith) _)
    (F := fun _ _ χ => intervalMax N (N : ℝ)
      (fun n => (vonMangoldt n : ℂ) * χ n - if χ = 1 then 1 else 0))
  have hpt := intervalMax_ge_point_dq4 (N := N) (p := p) hp.one_lt.le hpN
    (fun n => (vonMangoldt n : ℂ) * (1 : DirichletCharacter ℂ (0 + 1)) n -
      if (1 : DirichletCharacter ℂ (0 + 1)) = 1 then 1 else 0)
  have hval := point_value_ge'_dq4 hp (modOne_char_apply_dq4 1 p)
    (if (1 : DirichletCharacter ℂ (0 + 1)) = 1 then (1 : ℂ) else 0)
    (by split_ifs <;> simp)
  exact hval.trans (hpt.trans hlow)

/-- At level `R = N`, the part (2) sum is at least `log p - 2` for every prime `p ≤ N` and every
second degree term with `β ≤ 1`, P0029 page 18 display (2). -/
theorem leaf2_sum_ge_S10 {N p : ℕ} (hp : p.Prime) (hpN : p ≤ N)
    (r₀ : ℕ) [NeZero r₀] (χ₀ : DirichletCharacter ℂ r₀) {β : ℝ} (hβ : β ≤ 1) :
    Real.log p - 2 ≤ primSum (N : ℝ) (fun r _ χ => intervalMax N (N : ℝ)
        (fun n => (vonMangoldt n : ℂ) * χ n - (if χ = 1 then 1 else 0) +
          (if r = r₀ ∧ HEq χ χ₀ then (n : ℂ) ^ ((β : ℂ) - 1) else 0))) := by
  have hR1 : (1 : ℝ) ≤ N := by exact_mod_cast (hp.one_lt.le.trans hpN)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.one_lt.le
  have hlow := primSum_ge_modOne_dq4 hR1
    (hF := fun r _ χ => intervalMax_nonneg_dq4 N (by linarith) _)
    (F := fun r _ χ => intervalMax N (N : ℝ)
      (fun n => (vonMangoldt n : ℂ) * χ n - (if χ = 1 then 1 else 0) +
        (if r = r₀ ∧ HEq χ χ₀ then (n : ℂ) ^ ((β : ℂ) - 1) else 0)))
  have hpt := intervalMax_ge_point_dq4 (N := N) (p := p) hp.one_lt.le hpN
    (fun n => (vonMangoldt n : ℂ) * (1 : DirichletCharacter ℂ (0 + 1)) n -
      (if (1 : DirichletCharacter ℂ (0 + 1)) = 1 then 1 else 0) +
        (if 0 + 1 = r₀ ∧ HEq (1 : DirichletCharacter ℂ (0 + 1)) χ₀ then
          (n : ℂ) ^ ((β : ℂ) - 1) else 0))
  have hval := point_value_ge_dq4 hp (modOne_char_apply_dq4 1 p)
    (if (1 : DirichletCharacter ℂ (0 + 1)) = 1 then (1 : ℂ) else 0)
    (if 0 + 1 = r₀ ∧ HEq (1 : DirichletCharacter ℂ (0 + 1)) χ₀ then
      (p : ℂ) ^ ((β : ℂ) - 1) else 0)
    (by split_ifs <;> simp)
    (by
      split_ifs
      · rw [Complex.norm_natCast_cpow_of_pos hp.pos]
        apply Real.rpow_le_one_of_one_le_of_nonpos hp1
        simp only [Complex.sub_re, Complex.ofReal_re, Complex.one_re]
        linarith
      · simp)
  exact hval.trans (hpt.trans hlow)

/-- A prime `p` with `|C| + 3 ≤ log p`; every `N ≥ p` then has `|C| + 3 ≤ log N`. -/
theorem large_prime_S10 (C : ℝ) :
    ∃ p : ℕ, p.Prime ∧ ∀ N : ℕ, p ≤ N → |C| + 3 ≤ Real.log p ∧ |C| + 3 ≤ Real.log N := by
  obtain ⟨p, hpge, hp⟩ := Nat.exists_infinite_primes (⌈Real.exp (|C| + 3)⌉₊)
  refine ⟨p, hp, fun N hpN => ?_⟩
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hpR : Real.exp (|C| + 3) ≤ (p : ℝ) :=
    (Nat.le_ceil _).trans (by exact_mod_cast hpge)
  have hlogp : |C| + 3 ≤ Real.log p := by
    have h := Real.log_le_log (Real.exp_pos _) hpR
    rwa [Real.log_exp] at h
  have hlogN : Real.log p ≤ Real.log N :=
    Real.log_le_log hp0 (by exact_mod_cast hpN)
  exact ⟨hlogp, hlogp.trans hlogN⟩

/-- (b) What leaf 1 forces: for every large `N` there is a Siegel zero of level `N`.
PROVED, no open step. -/
theorem leaf1_forces_siegel_S10 (h1L : Leaf1BodyS10) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
        SiegelZero (N : ℝ) r χ β := by
  obtain ⟨c, C, hc, h1⟩ := h1L
  obtain ⟨p, hp, hlog⟩ := large_prime_S10 C
  refine ⟨p, fun N hpN => ?_⟩
  obtain ⟨hlogp, hlogN⟩ := hlog N hpN
  have hC0 := abs_nonneg C
  have hlogNpos : 0 < Real.log N := by linarith
  obtain ⟨hc1, hc2⟩ := range_at_level_N_S10 (N := N) (by linarith)
  by_contra hs
  have hup := h1 N (N : ℝ) hc1 hc2 le_rfl hs
  have hexp : Real.exp (-c * Real.log N / Real.log N) ≤ 1 := by
    rw [mul_div_assoc, div_self hlogNpos.ne', mul_one, Real.exp_le_one_iff]
    linarith
  have hexp0 := Real.exp_pos (-c * Real.log N / Real.log N)
  have hrhs : C * Real.exp (-c * Real.log N / Real.log N) ≤ |C| := by
    calc C * Real.exp (-c * Real.log N / Real.log N)
        ≤ |C| * Real.exp (-c * Real.log N / Real.log N) :=
          mul_le_mul_of_nonneg_right (le_abs_self C) hexp0.le
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hexp hC0
      _ = |C| := mul_one _
  have hlow := leaf1_sum_ge_S10 hp hpN
  linarith

/-- (b) Corollary: leaf 1 is false when Siegel zeros are absent at arbitrarily large levels,
for instance under GRH, where no level carries a Siegel zero. PROVED, no open step. -/
theorem leaf1_false_of_sparse_siegel_S10
    (hsparse : ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ¬ ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
        SiegelZero (N : ℝ) r χ β) :
    ¬ Leaf1BodyS10 := by
  intro h1L
  obtain ⟨N₀, hN₀⟩ := leaf1_forces_siegel_S10 h1L
  obtain ⟨N, hN, hno⟩ := hsparse N₀
  exact hno (hN₀ N hN)

/-- (c) What leaf 2 forces: for every large `N` there is no Siegel zero of level `N`.
PROVED, no open step. -/
theorem leaf2_forbids_siegel_S10 (h2L : Leaf2BodyS10) :
    ∃ N₀ : ℕ, ∀ N : ℕ, N₀ ≤ N →
      ¬ ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
        SiegelZero (N : ℝ) r χ β := by
  obtain ⟨c, C, hc, h2⟩ := h2L
  obtain ⟨p, hp, hlog⟩ := large_prime_S10 C
  refine ⟨p, fun N hpN => ?_⟩
  obtain ⟨hlogp, hlogN⟩ := hlog N hpN
  have hC0 := abs_nonneg C
  have hlogNpos : 0 < Real.log N := by linarith
  obtain ⟨hc1, hc2⟩ := range_at_level_N_S10 (N := N) (by linarith)
  rintro ⟨r₀, hr₀, χ₀, β, hsz⟩
  have hup := h2 N (N : ℝ) hc1 hc2 le_rfl r₀ χ₀ β hsz
  obtain ⟨_, _, _, hβlo, hβhi, _⟩ := hsz
  have hexp : Real.exp (-c * Real.log N / Real.log N) ≤ 1 := by
    rw [mul_div_assoc, div_self hlogNpos.ne', mul_one, Real.exp_le_one_iff]
    linarith
  have hexp0 := Real.exp_pos (-c * Real.log N / Real.log N)
  have hb1 : (1 - β) * Real.log N ≤ 1 := by
    have h := mul_lt_mul_of_pos_right (show 1 - β < 1 / Real.log N by linarith) hlogNpos
    rw [one_div_mul_cancel hlogNpos.ne'] at h
    linarith
  have hb0 : 0 ≤ (1 - β) * Real.log N := mul_nonneg (by linarith) hlogNpos.le
  have hk0 : 0 ≤ (1 - β) * Real.log N * Real.exp (-c * Real.log N / Real.log N) :=
    mul_nonneg hb0 hexp0.le
  have hk1 : (1 - β) * Real.log N * Real.exp (-c * Real.log N / Real.log N) ≤ 1 := by
    nlinarith
  have hrhs : C * (1 - β) * Real.log N * Real.exp (-c * Real.log N / Real.log N) ≤ |C| := by
    calc C * (1 - β) * Real.log N * Real.exp (-c * Real.log N / Real.log N)
        = C * ((1 - β) * Real.log N * Real.exp (-c * Real.log N / Real.log N)) := by ring
      _ ≤ |C| * ((1 - β) * Real.log N * Real.exp (-c * Real.log N / Real.log N)) :=
        mul_le_mul_of_nonneg_right (le_abs_self C) hk0
      _ ≤ |C| * 1 := mul_le_mul_of_nonneg_left hk1 hC0
      _ = |C| := mul_one _
  have hlow := leaf2_sum_ge_S10 hp hpN r₀ χ₀ hβhi.le
  linarith

/-- (c) Corollary: leaf 2 is false when Siegel zeros occur at arbitrarily large levels.
PROVED, no open step. -/
theorem leaf2_false_of_frequent_siegel_S10
    (hfreq : ∀ N₀ : ℕ, ∃ N : ℕ, N₀ ≤ N ∧
      ∃ (r : ℕ) (_ : NeZero r) (χ : DirichletCharacter ℂ r) (β : ℝ),
        SiegelZero (N : ℝ) r χ β) :
    ¬ Leaf2BodyS10 := by
  intro h2L
  obtain ⟨N₀, hN₀⟩ := leaf2_forbids_siegel_S10 h2L
  obtain ⟨N, hN, hyes⟩ := hfreq N₀
  exact hN₀ N hN hyes

/-- (a) again, directly from (b) and (c) at one common large level. PROVED, no open step. -/
theorem not_both_leaves_direct_S10 : ¬ (Leaf1BodyS10 ∧ Leaf2BodyS10) := by
  rintro ⟨h1L, h2L⟩
  obtain ⟨N₁, h₁⟩ := leaf1_forces_siegel_S10 h1L
  obtain ⟨N₂, h₂⟩ := leaf2_forbids_siegel_S10 h2L
  exact h₂ (max N₁ N₂) (le_max_right _ _) (h₁ (max N₁ N₂) (le_max_left _ _))

end LeanLab.BhowmikGrimmelt2026

#print axioms LeanLab.BhowmikGrimmelt2026.leaf1_match_S10
#print axioms LeanLab.BhowmikGrimmelt2026.leaf2_match_S10
#print axioms LeanLab.BhowmikGrimmelt2026.prop52_of_leaves_S10
#print axioms LeanLab.BhowmikGrimmelt2026.not_both_leaves_S10
#print axioms LeanLab.BhowmikGrimmelt2026.range_at_level_N_S10
#print axioms LeanLab.BhowmikGrimmelt2026.leaf1_sum_ge_S10
#print axioms LeanLab.BhowmikGrimmelt2026.leaf2_sum_ge_S10
#print axioms LeanLab.BhowmikGrimmelt2026.large_prime_S10
#print axioms LeanLab.BhowmikGrimmelt2026.leaf1_forces_siegel_S10
#print axioms LeanLab.BhowmikGrimmelt2026.leaf1_false_of_sparse_siegel_S10
#print axioms LeanLab.BhowmikGrimmelt2026.leaf2_forbids_siegel_S10
#print axioms LeanLab.BhowmikGrimmelt2026.leaf2_false_of_frequent_siegel_S10
#print axioms LeanLab.BhowmikGrimmelt2026.not_both_leaves_direct_S10
