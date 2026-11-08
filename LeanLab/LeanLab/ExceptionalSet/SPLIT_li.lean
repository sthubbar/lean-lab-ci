/-
Split of `li` of `LeanLab.ExceptionalSet.Statements` into two leaves.

`li` asserts `PowerBound 0.914`, that is `E X ≤ C X^{0.914}` for every `X ≥ 1`, the δ = 0.086
record for the exceptional set of binary Goldbach. Its proof runs through a *local* count on
short windows and a *cover* of one dyadic block by such windows.

* LEAF 1, the local count: on the window `[N - R, N + R]` of radius `R = ⌊N^{0.99}⌋` around
  `N`, the even `n` that are no sum of two primes number at most `C N^{0.903}`. This is the
  analytic half, the density input on a short interval; the radius is far below `N`, and that
  is what makes it much weaker than a bound holding for every `X`.
* LEAF 2, the cover count: one dyadic block `(Y/2, Y]` is covered by at most `C Y^{0.01}`
  windows of radius `⌊(Y/2)^{0.99}⌋`. This is the bookkeeping half, an elementary estimate
  about floors and powers of the block length, and it says nothing about `E`.

`li_split` covers the block `(Y/2, Y]` by the windows of LEAF 2, charges every window to
LEAF 1, and sums the block bound over the dyadic halvings. The two exponents fit once:
`0.903 + 0.01 = 0.913 < 0.914`, and the sum over the halvings costs only the geometric factor
`1/(1 - 2^{-0.914})`. Neither leaf alone gives `PowerBound 0.914`: LEAF 1 is a local count,
LEAF 2 says nothing about `E`, and with a window exponent above `0.904` their product would
exceed `0.914`.

Every leaf is OPEN. The assembly `li_split` has no sorry and does not use `li`.
Checked only by the Lean kernel. Binary Goldbach itself is OPEN; this is the almost-all bound.
-/
import LeanLab.ExceptionalSet.Statements

namespace LeanLab.ExceptionalSet
open Real Filter Topology

attribute [local instance] Classical.propDecidable

/-- LEAF 1 of 2, the local count: on every window `[N - R, N + R]` with `R = ⌊N^{0.99}⌋` and
`N ≥ N0`, the even `n` of the window that are not a sum of two primes number at most
`C N^{0.903}`, with one constant `C ≥ 0` for all `N`. The radius is far below `N`, so this is
a density bound on a short interval and not a bound for all `X`. -/
theorem leaf_window_count :
    ∃ (C : ℝ) (N0 : ℕ), 0 ≤ C ∧ 1 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      (((Finset.Icc (N - ⌊(N : ℝ) ^ (0.99 : ℝ)⌋₊)
            (N + ⌊(N : ℝ) ^ (0.99 : ℝ)⌋₊)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
        ≤ C * (N : ℝ) ^ (0.903 : ℝ) := by
  sorry

/-- LEAF 2 of 2, the cover count: for `Y ≥ 2` the dyadic block `(Y/2, Y]` is covered by the
`Y / r + 1` windows of radius `r = ⌊(Y/2)^{0.99}⌋` centred at `Y/2 + j r`, `j < Y/r + 1`,
and that number of windows is at most `C Y^{0.01}`. An estimate on `⌊·⌋₊` and powers only,
with no reference to `E`. -/

lemma helper1 (Y : ℕ) (hY : 2 ≤ Y) : (1 : ℝ) ≤ ((Y / 2 : ℕ) : ℝ) := by
  have : 1 ≤ Y / 2 := by omega
  exact_mod_cast this

lemma helper2 (Y : ℕ) (hY : 2 ≤ Y) : (1 : ℝ) ≤ (((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ)) := by
  apply Real.one_le_rpow (helper1 Y hY) (by norm_num)

lemma helper3 (Y : ℕ) (hY : 2 ≤ Y) : 1 ≤ ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ))⌋₊ := by
  have h := helper2 Y hY
  exact (Nat.one_le_floor_iff (((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ))).mpr h

lemma helper4 {Y : ℕ} : ((Y / 2 : ℕ) : ℝ) = (Y : ℝ) / 2 - (((Y % 2 : ℕ) : ℝ) / 2) := by
  have h : (Y : ℝ) = (((Y / 2 : ℕ) : ℝ) * 2) + ((Y % 2 : ℕ) : ℝ) := by
    have h2 : 2 * (Y / 2) + Y % 2 = Y := Nat.div_add_mod Y 2
    have h2' : Y / 2 * 2 + Y % 2 = Y := by omega
    have h3 : ((Y / 2 * 2 + Y % 2 : ℕ) : ℝ) = (Y : ℝ) := by exact_mod_cast h2'
    push_cast at h3
    exact h3.symm
  linarith

lemma helper5 (Y : ℕ) (hY : 2 ≤ Y) : (Y : ℝ) / 4 ≤ ((Y / 2 : ℕ) : ℝ) := by
  have h1 := @helper4 Y
  have h2 : ((Y % 2 : ℕ) : ℝ) ≤ 1 := by
    have : Y % 2 ≤ 1 := by omega
    exact_mod_cast this
  have h3 : (Y : ℝ) ≥ 2 := by exact_mod_cast hY
  linarith

lemma helper6 (a b : ℕ) : ((a / b : ℕ) : ℝ) ≤ (a : ℝ) / (b : ℝ) := by
  by_cases hb : b = 0
  · rw [hb]
    simp
  · have hb_pos : 0 < b := by omega
    have h1 : a / b * b ≤ a := Nat.div_mul_le_self a b
    have h2 : ((a / b * b : ℕ) : ℝ) ≤ (a : ℝ) := by exact_mod_cast h1
    push_cast at h2
    have hb_r_pos : (0 : ℝ) < b := by exact_mod_cast hb_pos
    exact (le_div_iff₀ hb_r_pos).mpr h2

theorem leaf_cover_count :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℕ, 2 ≤ Y →
      ((Y / ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ))⌋₊ + 1 : ℕ) : ℝ)
        ≤ C * (Y : ℝ) ^ (0.01 : ℝ) := by
  use 12
  constructor
  · norm_num
  · intro Y hY
    set r := ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ))⌋₊
    have hr : 1 ≤ r := helper3 Y hY
    have hr_pos : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
    have h1 : ((Y / r + 1 : ℕ) : ℝ) = ((Y / r : ℕ) : ℝ) + 1 := by exact Nat.cast_add_one (Y / r)
    rw [h1]

    have hd1 : ((Y / r : ℕ) : ℝ) ≤ (Y : ℝ) / (r : ℝ) := helper6 Y r

    have hr_lower : (((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ)) / 2 ≤ (r : ℝ) := by
      have h2 := helper2 Y hY
      by_cases h_cases : (((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ)) ≤ 2
      · have : (1 : ℝ) ≥ (((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ)) / 2 := by linarith
        have h1r : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
        linarith
      · have : (((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ)) - 1 ≤ (r : ℝ) := by
          have : (((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ)) < (r : ℝ) + 1 := Nat.lt_floor_add_one (((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ))
          linarith
        have : (((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ)) / 2 ≤ (((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ)) - 1 := by linarith
        linarith

    have hY_pow : ((Y : ℝ) / 4) ^ (0.99 : ℝ) ≤ (((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ)) := by
      apply Real.rpow_le_rpow
      · linarith [show (Y : ℝ) ≥ 2 by exact_mod_cast hY]
      · exact helper5 Y hY
      · norm_num

    have hY_div : (Y : ℝ) ^ (0.99 : ℝ) / (4 : ℝ) ^ (0.99 : ℝ) = ((Y : ℝ) / 4) ^ (0.99 : ℝ) := by
      rw [Real.div_rpow (by linarith [show (Y : ℝ) ≥ 2 by exact_mod_cast hY]) (by norm_num)]

    have hr_lower2 : (Y : ℝ) ^ (0.99 : ℝ) / (2 * (4 : ℝ) ^ (0.99 : ℝ)) ≤ (r : ℝ) := by
      calc (Y : ℝ) ^ (0.99 : ℝ) / (2 * (4 : ℝ) ^ (0.99 : ℝ)) = ((Y : ℝ) ^ (0.99 : ℝ) / (4 : ℝ) ^ (0.99 : ℝ)) / 2 := by ring
      _ = ((Y : ℝ) / 4) ^ (0.99 : ℝ) / 2 := by rw [hY_div]
      _ ≤ (((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ)) / 2 := by linarith
      _ ≤ (r : ℝ) := hr_lower

    have h_final : (Y : ℝ) / (r : ℝ) ≤ (Y : ℝ) / ((Y : ℝ) ^ (0.99 : ℝ) / (2 * (4 : ℝ) ^ (0.99 : ℝ))) := by
      apply div_le_div_of_nonneg_left (by linarith [show (Y : ℝ) ≥ 2 by exact_mod_cast hY])
      · have : (0 : ℝ) < (Y : ℝ) ^ (0.99 : ℝ) := Real.rpow_pos_of_pos (by linarith [show (Y : ℝ) ≥ 2 by exact_mod_cast hY]) _
        positivity
      · exact hr_lower2

    have h_simpl : (Y : ℝ) / ((Y : ℝ) ^ (0.99 : ℝ) / (2 * (4 : ℝ) ^ (0.99 : ℝ))) = (2 * (4 : ℝ) ^ (0.99 : ℝ)) * (Y : ℝ) ^ (0.01 : ℝ) := by
      have hY_pos : (0 : ℝ) < (Y : ℝ) := by linarith [show (Y : ℝ) ≥ 2 by exact_mod_cast hY]
      have h_rpow : (Y : ℝ) / (Y : ℝ) ^ (0.99 : ℝ) = (Y : ℝ) ^ ((1 : ℝ) - (0.99 : ℝ)) := by
        have : (Y : ℝ) = (Y : ℝ) ^ (1 : ℝ) := by exact (Real.rpow_one (Y : ℝ)).symm
        nth_rw 1 [this]
        exact (Real.rpow_sub hY_pos (1 : ℝ) (0.99 : ℝ)).symm
      have : (1 : ℝ) - (0.99 : ℝ) = (0.01 : ℝ) := by norm_num
      rw [this] at h_rpow
      have hd : (Y : ℝ) / ((Y : ℝ) ^ (0.99 : ℝ) / (2 * (4 : ℝ) ^ (0.99 : ℝ))) = (Y : ℝ) * (2 * (4 : ℝ) ^ (0.99 : ℝ)) / (Y : ℝ) ^ (0.99 : ℝ) := by
        exact div_div_eq_mul_div (Y : ℝ) ((Y : ℝ) ^ (0.99 : ℝ)) (2 * (4 : ℝ) ^ (0.99 : ℝ))
      calc (Y : ℝ) / ((Y : ℝ) ^ (0.99 : ℝ) / (2 * (4 : ℝ) ^ (0.99 : ℝ))) = (Y : ℝ) * (2 * (4 : ℝ) ^ (0.99 : ℝ)) / (Y : ℝ) ^ (0.99 : ℝ) := hd
        _ = (2 * (4 : ℝ) ^ (0.99 : ℝ)) * ((Y : ℝ) / (Y : ℝ) ^ (0.99 : ℝ)) := by ring
        _ = (2 * (4 : ℝ) ^ (0.99 : ℝ)) * (Y : ℝ) ^ (0.01 : ℝ) := by rw [h_rpow]

    have hb1 : (2 * (4 : ℝ) ^ (0.99 : ℝ)) ≤ 8 := by
      have : (4 : ℝ) ^ (0.99 : ℝ) ≤ (4 : ℝ) ^ (1 : ℝ) := by
        apply Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
      have : (4 : ℝ) ^ (1 : ℝ) = 4 := by norm_num
      linarith

    have hb2 : (Y : ℝ) / (r : ℝ) ≤ 8 * (Y : ℝ) ^ (0.01 : ℝ) := by
      calc (Y : ℝ) / (r : ℝ) ≤ (2 * (4 : ℝ) ^ (0.99 : ℝ)) * (Y : ℝ) ^ (0.01 : ℝ) := by linarith
        _ ≤ 8 * (Y : ℝ) ^ (0.01 : ℝ) := by
          apply mul_le_mul_of_nonneg_right hb1 (by positivity)

    have hb3 : (1 : ℝ) ≤ (Y : ℝ) ^ (0.01 : ℝ) := by
      apply Real.one_le_rpow (by linarith [show (Y : ℝ) ≥ 2 by exact_mod_cast hY]) (by norm_num)

    linarith


/-! ### The exceptions up to `x` split at `x/2` -/

/-- The exceptions up to `x` are those up to `x/2` together with the block `(x/2, x]`. -/
private theorem E_le_half_add (x : ℕ) :
    E x ≤ E (x / 2) +
      (((Finset.Ioc (x / 2) x).filter (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card) := by
  classical
  unfold E
  set s := (Finset.Icc 4 x).filter (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n) with hs
  set t := (Finset.Icc 4 (x / 2)).filter (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n) with ht
  set b := (Finset.Ioc (x / 2) x).filter (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n) with hb
  have hsub : s ⊆ t ∪ b := by
    intro n hn
    rw [hs, Finset.mem_filter, Finset.mem_Icc] at hn
    obtain ⟨⟨h4, hxle⟩, hP⟩ := hn
    by_cases hle : n ≤ x / 2
    · exact Finset.mem_union_left _
        (by rw [ht, Finset.mem_filter, Finset.mem_Icc]; exact ⟨⟨h4, hle⟩, hP⟩)
    · exact Finset.mem_union_right _
        (by rw [hb, Finset.mem_filter, Finset.mem_Ioc]; exact ⟨⟨by omega, hxle⟩, hP⟩)
  have h1 : s.card ≤ (t ∪ b).card := Finset.card_le_card hsub
  have h2 : (t ∪ b).card ≤ t.card + b.card := Finset.card_union_le t b
  omega

/-! ### The cover of a dyadic block by short windows -/

/-- Every point of `(Y/2, Y]` lies in the window of radius `⌊c^{0.99}⌋` centred at
`c = Y/2 + r · ⌊(k - Y/2) / r⌋` with `r = ⌊(Y/2)^{0.99}⌋`, so the block is covered by
`Y / r + 1` such windows and its count is at most the sum of the window counts. -/
private theorem cover_card_le (Y r : ℕ) (hY : 2 ≤ Y)
    (hr : r = ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ))⌋₊) (hr1 : 1 ≤ r) :
    (((Finset.Ioc (Y / 2) Y).filter (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
      ≤ ∑ j ∈ Finset.range (Y / r + 1),
          (((Finset.Icc (Y / 2 + j * r - ⌊((Y / 2 + j * r : ℕ) : ℝ) ^ (0.99 : ℝ)⌋₊)
              (Y / 2 + j * r + ⌊((Y / 2 + j * r : ℕ) : ℝ) ^ (0.99 : ℝ)⌋₊)).filter
            (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ) := by
  classical
  have hr0 : 0 < r := hr1
  -- the window radius is monotone in the centre
  have hradmono : ∀ c c' : ℕ, 0 < c → c ≤ c' →
      ⌊(c : ℝ) ^ (0.99 : ℝ)⌋₊ ≤ ⌊(c' : ℝ) ^ (0.99 : ℝ)⌋₊ := by
    intro c c' hc hle
    apply Nat.floor_le_floor
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hle) (by norm_num)
  have hsub : ((Finset.Ioc (Y / 2) Y).filter (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)) ⊆
      (Finset.range (Y / r + 1)).biUnion (fun j =>
        (Finset.Icc (Y / 2 + j * r - ⌊((Y / 2 + j * r : ℕ) : ℝ) ^ (0.99 : ℝ)⌋₊)
            (Y / 2 + j * r + ⌊((Y / 2 + j * r : ℕ) : ℝ) ^ (0.99 : ℝ)⌋₊)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)) := by
    intro k hk
    rw [Finset.mem_filter, Finset.mem_Ioc] at hk
    obtain ⟨⟨hk1, hk2⟩, hkP⟩ := hk
    rw [Finset.mem_biUnion]
    have hkY : k - Y / 2 ≤ Y := by omega
    set j : ℕ := (k - Y / 2) / r with hj
    set m : ℕ := (k - Y / 2) % r with hm
    set q : ℕ := j * r with hq
    refine ⟨j, ?_, ?_⟩
    · rw [Finset.mem_range]
      have hle : j ≤ Y / r := Nat.div_le_div_right hkY
      omega
    · have hspec : q + m = k - Y / 2 := by
        rw [hq, hm, hj, Nat.mul_comm]
        exact Nat.div_add_mod (k - Y / 2) r
      have hmr : m < r := by rw [hm]; exact Nat.mod_lt _ hr0
      have hrad : r ≤ ⌊((Y / 2 + q : ℕ) : ℝ) ^ (0.99 : ℝ)⌋₊ := by
        have h1 : ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ))⌋₊
            ≤ ⌊((Y / 2 + q : ℕ) : ℝ) ^ (0.99 : ℝ)⌋₊ := by
          apply hradmono
          · have : 0 < Y / 2 := by omega
            omega
          · omega
        rwa [← hr] at h1
      have hkdecomp : k = Y / 2 + q + m := by omega
      have hradg : r ≤ ⌊((Y / 2 + j * r : ℕ) : ℝ) ^ (0.99 : ℝ)⌋₊ := by
        rw [← hq]
        exact hrad
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hkP⟩
  rw [← Nat.cast_sum]
  exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le

/-! ### The block bound from the two leaves -/

/-- One dyadic block `(Y/2, Y]` holds at most `2 C1 C2 Y^{0.913}` exceptions: the cover of
`cover_card_le` has `C2 Y^{0.01}` windows, each charged `C1 N^{0.903} ≤ 2 C1 Y^{0.903}`
because its centre is at most `2 Y`. -/
private theorem block_le {C1 C2 : ℝ} {N0 : ℕ} (hC1 : 0 ≤ C1)
    (hwin : ∀ N : ℕ, N0 ≤ N →
      (((Finset.Icc (N - ⌊(N : ℝ) ^ (0.99 : ℝ)⌋₊)
            (N + ⌊(N : ℝ) ^ (0.99 : ℝ)⌋₊)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
        ≤ C1 * (N : ℝ) ^ (0.903 : ℝ))
    (hcov : ∀ Y : ℕ, 2 ≤ Y →
      ((Y / ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ))⌋₊ + 1 : ℕ) : ℝ)
        ≤ C2 * (Y : ℝ) ^ (0.01 : ℝ))
    (Y : ℕ) (hY : max (2 * N0) 2 ≤ Y) :
    (((Finset.Ioc (Y / 2) Y).filter (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
      ≤ (2 * C1 * C2) * (Y : ℝ) ^ (0.913 : ℝ) := by
  classical
  have hY2 : 2 ≤ Y := le_trans (le_max_right _ _) hY
  have hYN0 : 2 * N0 ≤ Y := le_trans (le_max_left _ _) hY
  have hYpos : (0 : ℝ) < Y := by
    have : 0 < Y := by omega
    exact_mod_cast this
  set r : ℕ := ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ))⌋₊ with hr
  have hr1 : 1 ≤ r := by
    rw [hr]
    refine (Nat.one_le_floor_iff _).mpr ?_
    have h1 : (1 : ℝ) ≤ ((Y / 2 : ℕ) : ℝ) := by
      have : 1 ≤ Y / 2 := by omega
      exact_mod_cast this
    exact Real.one_le_rpow h1 (by norm_num)
  have hterm : ∀ j ∈ Finset.range (Y / r + 1),
      (((Finset.Icc (Y / 2 + j * r - ⌊((Y / 2 + j * r : ℕ) : ℝ) ^ (0.99 : ℝ)⌋₊)
          (Y / 2 + j * r + ⌊((Y / 2 + j * r : ℕ) : ℝ) ^ (0.99 : ℝ)⌋₊)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
        ≤ C1 * 2 * (Y : ℝ) ^ (0.903 : ℝ) := by
    intro j hj
    rw [Finset.mem_range] at hj
    set c : ℕ := Y / 2 + j * r with hc
    have hcN0 : N0 ≤ c := by
      have : N0 ≤ Y / 2 := by omega
      omega
    have hc2Y : c ≤ 2 * Y := by
      have h1 : j * r ≤ Y := by
        calc j * r ≤ (Y / r) * r := Nat.mul_le_mul_right r (by omega)
          _ ≤ Y := Nat.div_mul_le_self Y r
      omega
    have hw := hwin c hcN0
    have hcast : ((c : ℕ) : ℝ) ≤ 2 * (Y : ℝ) := by exact_mod_cast hc2Y
    calc (((Finset.Icc (c - ⌊(c : ℝ) ^ (0.99 : ℝ)⌋₊)
            (c + ⌊(c : ℝ) ^ (0.99 : ℝ)⌋₊)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
        ≤ C1 * (c : ℝ) ^ (0.903 : ℝ) := hw
      _ ≤ C1 * (2 * (Y : ℝ)) ^ (0.903 : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hC1
          exact Real.rpow_le_rpow (by positivity) hcast (by norm_num)
      _ = C1 * ((2 : ℝ) ^ (0.903 : ℝ) * (Y : ℝ) ^ (0.903 : ℝ)) := by
          rw [Real.mul_rpow (by norm_num) hYpos.le]
      _ ≤ C1 * (2 * (Y : ℝ) ^ (0.903 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hC1
          have h2 : (2 : ℝ) ^ (0.903 : ℝ) ≤ 2 := by
            calc (2 : ℝ) ^ (0.903 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
          nlinarith [Real.rpow_nonneg hYpos.le (0.903 : ℝ)]
      _ = C1 * 2 * (Y : ℝ) ^ (0.903 : ℝ) := by ring
  have hstep := cover_card_le Y r hY2 hr.symm hr1
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hJ : ((Y / r + 1 : ℕ) : ℝ) ≤ C2 * (Y : ℝ) ^ (0.01 : ℝ) := hcov Y hY2
  have hcount : (((Finset.Ioc (Y / 2) Y).filter
      (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
      ≤ ((Y / r + 1 : ℕ) : ℝ) * (C1 * 2 * (Y : ℝ) ^ (0.903 : ℝ)) :=
    hstep.trans hsum
  calc (((Finset.Ioc (Y / 2) Y).filter
        (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
      ≤ ((Y / r + 1 : ℕ) : ℝ) * (C1 * 2 * (Y : ℝ) ^ (0.903 : ℝ)) := hcount
    _ ≤ (C2 * (Y : ℝ) ^ (0.01 : ℝ)) * (C1 * 2 * (Y : ℝ) ^ (0.903 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right hJ
        positivity
    _ = C1 * 2 * C2 * ((Y : ℝ) ^ (0.01 : ℝ) * (Y : ℝ) ^ (0.903 : ℝ)) := by ring
    _ = C1 * 2 * C2 * (Y : ℝ) ^ (0.913 : ℝ) := by
        rw [← Real.rpow_add hYpos]
        norm_num
    _ = (2 * C1 * C2) * (Y : ℝ) ^ (0.913 : ℝ) := by ring

/-! ### Dyadic summation -/

/-- A block bound `≤ C Y^θ` with `0 < θ` gives `PowerBound θ`: `E x ≤ E (x/2) +` the block
count, and the halvings lose the factor `2^{-θ} < 1`. -/
private theorem powerBound_of_block {θ C : ℝ} {Y0 : ℕ} (hθ : 0 < θ)
    (h : ∀ Y : ℕ, Y0 ≤ Y →
      (((Finset.Ioc (Y / 2) Y).filter (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
        ≤ C * (Y : ℝ) ^ θ) :
    PowerBound θ := by
  classical
  have h2 : (0 : ℝ) < 1 - (2 : ℝ) ^ (-θ) := by
    have hlt : (2 : ℝ) ^ (-θ) < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  set K : ℝ := max (Y0 : ℝ) (C / (1 - (2 : ℝ) ^ (-θ))) with hK
  have hK0 : 0 ≤ K := le_trans (Nat.cast_nonneg _) (le_max_left _ _)
  refine ⟨K, ?_⟩
  intro X
  induction X using Nat.strong_induction_on with
  | _ x ih =>
    intro hx
    have hx1 : (1 : ℝ) ≤ x := by exact_mod_cast hx
    have hxθ : (1 : ℝ) ≤ (x : ℝ) ^ θ := Real.one_le_rpow hx1 hθ.le
    by_cases hX0 : x < Y0
    · calc (E x : ℝ) ≤ x := by exact_mod_cast E_le x
        _ ≤ Y0 := by exact_mod_cast hX0.le
        _ ≤ K := le_max_left _ _
        _ ≤ K * (x : ℝ) ^ θ := le_mul_of_one_le_right hK0 hxθ
    · replace hX0 := not_lt.mp hX0
      have hsplit : (E x : ℝ) ≤ (E (x / 2) : ℝ) + (((Finset.Ioc (x / 2) x).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ) := by
        have := E_le_half_add x
        exact_mod_cast this
      have hw := h x hX0
      have hKC : C ≤ K * (1 - (2 : ℝ) ^ (-θ)) := by
        have hle := le_max_right (Y0 : ℝ) (C / (1 - (2 : ℝ) ^ (-θ)))
        rw [← hK] at hle
        rwa [div_le_iff₀ h2] at hle
      have hhalf : (E (x / 2) : ℝ) ≤ K * ((x : ℝ) / 2) ^ θ := by
        rcases Nat.eq_zero_or_pos (x / 2) with h0 | hpos
        · rw [h0]
          have hE0 : E 0 = 0 := by
            unfold E
            rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
            intro n hn
            simp only [Finset.mem_Icc] at hn
            omega
          rw [hE0]
          simp only [Nat.cast_zero]
          positivity
        · have hx2 : x / 2 < x := by omega
          have := ih (x / 2) hx2 hpos
          refine this.trans (mul_le_mul_of_nonneg_left ?_ hK0)
          apply Real.rpow_le_rpow (by positivity) _ hθ.le
          rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
          exact_mod_cast Nat.div_mul_le_self x 2
      have hpow : ((x : ℝ) / 2) ^ θ = (2 : ℝ) ^ (-θ) * (x : ℝ) ^ θ := by
        rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num)]
        ring
      calc (E x : ℝ) ≤ (E (x / 2) : ℝ) + (((Finset.Ioc (x / 2) x).filter
            (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ) := hsplit
        _ ≤ K * ((2 : ℝ) ^ (-θ) * (x : ℝ) ^ θ) + C * (x : ℝ) ^ θ := by rw [← hpow]; linarith
        _ ≤ K * ((2 : ℝ) ^ (-θ) * (x : ℝ) ^ θ) + K * (1 - (2 : ℝ) ^ (-θ)) * (x : ℝ) ^ θ := by
            have hxθ0 : (0 : ℝ) ≤ (x : ℝ) ^ θ := Real.rpow_nonneg (by positivity) θ
            nlinarith [mul_nonneg hxθ0 h2.le]
        _ = K * (x : ℝ) ^ θ := by ring

/-! ### `li`, assembled -/

/-- `li`, assembled from the two leaves: the block count at `0.913` from LEAF 1 and LEAF 2,
its exponent raised to `0.914`, and the dyadic summation. -/
theorem li_split : PowerBound 0.914 := by
  classical
  obtain ⟨C1, N0, hC1, hN0, hwin⟩ := leaf_window_count
  obtain ⟨C2, hC2, hcov⟩ := leaf_cover_count
  have hblk : ∀ Y : ℕ, max (2 * N0) 2 ≤ Y →
      (((Finset.Ioc (Y / 2) Y).filter (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
        ≤ (2 * C1 * C2) * (Y : ℝ) ^ (0.914 : ℝ) := by
    intro Y hY
    have h := block_le hC1 hwin hcov Y hY
    have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by
      have h2 : 2 ≤ Y := le_trans (le_max_right _ _) hY
      have : (1 : ℕ) ≤ Y := by omega
      exact_mod_cast this
    refine h.trans ?_
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    exact Real.rpow_le_rpow_of_exponent_le hY1 (by norm_num)
  exact powerBound_of_block (Y0 := max (2 * N0) 2) (C := 2 * C1 * C2) (by norm_num) hblk

#print axioms li_split

end LeanLab.ExceptionalSet
