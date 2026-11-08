/-
Split of `lu` of `LeanLab.ExceptionalSet.Statements` into two leaves.

`lu` asserts `PowerBound 0.879`, that is `E X ≤ C X^{0.879}` for every `X ≥ 1`, the δ = 0.121
record for the exceptional set of binary Goldbach. Its proof runs through a *local* count on
short windows and a *cover* of one dyadic block by such windows.

* LEAF 1, the local count: on the window `[N - R, N + R]` of radius `R = ⌊N^{0.99979}⌋` around
  `N`, the even `n` that are no sum of two primes number at most `C N^{0.8787026}`. This is the
  analytic half, what the circle method with the sieve input delivers; the window is short
  compared with `N`, and that is what makes it far weaker than a bound holding for all `X`.
* LEAF 2, the cover count: one dyadic block `(Y/2, Y]` is covered by at most `C Y^{0.00021}`
  windows of radius `⌊(Y/2)^{0.99979}⌋`. This is the bookkeeping half, an elementary estimate
  about floors and powers, and it says nothing about `E`.

`lu_split` covers the block `(Y/2, Y]` by the windows of LEAF 2, charges every window to
LEAF 1, and sums the block bound over the dyadic halvings. The two exponents fit together once:
`0.8787026 + 0.00021 = 0.8789126 < 0.879`, and the sum over the halvings loses only the
geometric factor `1/(1 - 2^{-0.879})`. Neither leaf alone gives `PowerBound 0.879`: LEAF 1 is a
local count, LEAF 2 says nothing about `E`, and with a window exponent above `0.87879` their
product exceeds `0.879`.

Every leaf is OPEN. The assembly `lu_split` has no sorry and does not use `lu`.
AI-written Lean code, 2026-11-07. Checked only by the Lean kernel.
Binary Goldbach itself is OPEN; this is the almost-all bound.
-/
import LeanLab.ExceptionalSet.Statements

namespace LeanLab.ExceptionalSet
open Real Filter Topology

attribute [local instance] Classical.propDecidable

/-- LEAF 1 of 2, the local count: on every window `[N - R, N + R]` with `R = ⌊N^{0.99979}⌋` and
`N ≥ N0`, the even `n` of the window that are not a sum of two primes number at most
`C N^{0.8787026}`, with one constant `C ≥ 0` for all `N`. The radius is far below `N`, so this
is a density bound on a short interval and not a bound for all `X`. -/
theorem leaf_window_count :
    ∃ (C : ℝ) (N0 : ℕ), 0 ≤ C ∧ 1 ≤ N0 ∧ ∀ N : ℕ, N0 ≤ N →
      (((Finset.Icc (N - ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)
            (N + ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
        ≤ C * (N : ℝ) ^ (0.8787026 : ℝ) := by
  sorry

/-- For `a ≥ 1` its `Nat.floor` is at least `a / 2`. -/
private theorem half_le_floor {a : ℝ} (ha : 1 ≤ a) : a / 2 ≤ (⌊a⌋₊ : ℝ) := by
  rcases lt_or_ge a 2 with h2 | h2
  · have hfloor : 1 ≤ ⌊a⌋₊ := (Nat.one_le_floor_iff a).mpr ha
    have h1 : (1 : ℝ) ≤ (⌊a⌋₊ : ℝ) := by exact_mod_cast hfloor
    linarith
  · have h := Nat.lt_floor_add_one a
    linarith

/-- LEAF 2, proved: the number of windows covering `(Y/2, Y]` is at most `10 Y^{0.00021}`.
The radius is `r = ⌊(Y/2)^{0.99979}⌋ ≥ Y^{0.99979}/8`, so `Y / r ≤ 8 Y^{0.00021}`, and the
extra `+ 1` costs at most one more `Y^{0.00021}` since `Y ≥ 2`. -/
private theorem cover_count_aux (Y : ℕ) (hY : 2 ≤ Y) :
    ((Y / ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ))⌋₊ + 1 : ℕ) : ℝ)
      ≤ 10 * (Y : ℝ) ^ (0.00021 : ℝ) := by
  classical
  have hYpos : (0 : ℝ) < (Y : ℝ) := by
    have : (0 : ℕ) < Y := by omega
    exact_mod_cast this
  have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by
    have : (1 : ℕ) ≤ Y := by omega
    exact_mod_cast this
  -- the radius is at least `Y^{0.99979} / 8`
  have hrad : (Y : ℝ) ^ (0.99979 : ℝ) / 8
      ≤ (⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ))⌋₊ : ℝ) := by
    have hb1 : (1 : ℝ) ≤ ((Y / 2 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ Y / 2 := by omega
      exact_mod_cast this
    have hy4 : (Y : ℝ) / 4 ≤ ((Y / 2 : ℕ) : ℝ) := by
      have h : Y ≤ 4 * (Y / 2) := by omega
      have : (Y : ℝ) ≤ 4 * ((Y / 2 : ℕ) : ℝ) := by exact_mod_cast h
      linarith
    have hhalf := half_le_floor (a := ((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ))
      (Real.one_le_rpow hb1 (by norm_num))
    have hpow4 : (Y : ℝ) ^ (0.99979 : ℝ) / 4
        ≤ ((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ) := by
      have hmono : ((Y : ℝ) / 4) ^ (0.99979 : ℝ)
          ≤ ((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ) :=
        Real.rpow_le_rpow (by positivity) hy4 (by norm_num)
      have h4le : (4 : ℝ) ^ (0.99979 : ℝ) ≤ 4 := by
        calc (4 : ℝ) ^ (0.99979 : ℝ) ≤ (4 : ℝ) ^ (1 : ℝ) :=
              Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
          _ = 4 := Real.rpow_one 4
      have h4pos : (0 : ℝ) < (4 : ℝ) ^ (0.99979 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
      have hYp : (0 : ℝ) ≤ (Y : ℝ) ^ (0.99979 : ℝ) := Real.rpow_nonneg hYpos.le _
      have hinv : 1 / (4 : ℝ) ≤ 1 / ((4 : ℝ) ^ (0.99979 : ℝ)) :=
        one_div_le_one_div_of_le h4pos h4le
      have hsplit : (Y : ℝ) ^ (0.99979 : ℝ) / 4
          ≤ ((Y : ℝ) / 4) ^ (0.99979 : ℝ) := by
        rw [Real.div_rpow hYpos.le (by norm_num : (0 : ℝ) ≤ 4)]
        calc (Y : ℝ) ^ (0.99979 : ℝ) / 4
            = (Y : ℝ) ^ (0.99979 : ℝ) * (1 / 4) := by ring
          _ ≤ (Y : ℝ) ^ (0.99979 : ℝ) * (1 / (4 : ℝ) ^ (0.99979 : ℝ)) :=
              mul_le_mul_of_nonneg_left hinv hYp
          _ = (Y : ℝ) ^ (0.99979 : ℝ) / (4 : ℝ) ^ (0.99979 : ℝ) := by ring
      linarith
    linarith
  have hrpos : (0 : ℝ) < (⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ))⌋₊ : ℝ) := by
    have h8 : (0 : ℝ) < (Y : ℝ) ^ (0.99979 : ℝ) / 8 := by
      have := Real.rpow_pos_of_pos hYpos (0.99979 : ℝ)
      linarith
    linarith
  have hYp8 : (0 : ℝ) < (Y : ℝ) ^ (0.99979 : ℝ) / 8 := by
    have := Real.rpow_pos_of_pos hYpos (0.99979 : ℝ)
    linarith
  -- `Y / r ≤ Y / (Y^p / 8) = 8 Y^{0.00021}`
  have hKr : ((Y / ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ))⌋₊ : ℕ) : ℝ)
      ≤ 8 * (Y : ℝ) ^ (0.00021 : ℝ) := by
    have hcast : ((Y / ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ))⌋₊ : ℕ) : ℝ)
        ≤ (Y : ℝ) / (⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ))⌋₊ : ℝ) := Nat.cast_div_le
    have hmono : (Y : ℝ) / (⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ))⌋₊ : ℝ)
        ≤ (Y : ℝ) / ((Y : ℝ) ^ (0.99979 : ℝ) / 8) :=
      div_le_div_of_nonneg_left hYpos.le hYp8 hrad
    have hYp : (0 : ℝ) < (Y : ℝ) ^ (0.99979 : ℝ) := Real.rpow_pos_of_pos hYpos _
    have hsub : (Y : ℝ) ^ ((1 : ℝ) - 0.99979)
        = (Y : ℝ) ^ (1 : ℝ) / (Y : ℝ) ^ (0.99979 : ℝ) := Real.rpow_sub hYpos 1 0.99979
    rw [Real.rpow_one] at hsub
    have hexp : ((1 : ℝ) - 0.99979) = (0.00021 : ℝ) := by norm_num
    rw [hexp] at hsub
    have hdiv : (Y : ℝ) / ((Y : ℝ) ^ (0.99979 : ℝ) / 8)
        = 8 * ((Y : ℝ) / (Y : ℝ) ^ (0.99979 : ℝ)) := by
      field_simp
    calc ((Y / ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ))⌋₊ : ℕ) : ℝ)
        ≤ (Y : ℝ) / (⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ))⌋₊ : ℝ) := hcast
      _ ≤ (Y : ℝ) / ((Y : ℝ) ^ (0.99979 : ℝ) / 8) := hmono
      _ = 8 * ((Y : ℝ) / (Y : ℝ) ^ (0.99979 : ℝ)) := hdiv
      _ = 8 * (Y : ℝ) ^ (0.00021 : ℝ) := by rw [← hsub]
  have hYq : (1 : ℝ) ≤ (Y : ℝ) ^ (0.00021 : ℝ) := Real.one_le_rpow hY1 (by norm_num)
  have hsplit : ((Y / ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ))⌋₊ + 1 : ℕ) : ℝ)
      = ((Y / ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ))⌋₊ : ℕ) : ℝ) + 1 := by
    push_cast
    ring
  rw [hsplit]
  have hq0 : (0 : ℝ) ≤ (Y : ℝ) ^ (0.00021 : ℝ) := Real.rpow_nonneg hYpos.le _
  linarith

/-- LEAF 2 of 2, the cover count: for `Y ≥ 2` the dyadic block `(Y/2, Y]` is covered by the
`Y / r + 1` windows of radius `r = ⌊(Y/2)^{0.99979}⌋` centred at `Y/2 + j r`, `j < Y/r + 1`,
and that number of windows is at most `C Y^{0.00021}`. An estimate on `⌊·⌋₊` and powers only,
with no reference to `E`. -/
theorem leaf_cover_count :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℕ, 2 ≤ Y →
      ((Y / ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ))⌋₊ + 1 : ℕ) : ℝ)
        ≤ C * (Y : ℝ) ^ (0.00021 : ℝ) :=
  ⟨10, by norm_num, cover_count_aux⟩

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

/-- Every point of `(Y/2, Y]` lies in the window of radius `⌊c^{0.99979}⌋` centred at
`c = Y/2 + r · ⌊(k - Y/2) / r⌋` with `r = ⌊(Y/2)^{0.99979}⌋`, so the block is covered by
`Y / r + 1` such windows and its count is at most the sum of the window counts. -/
private theorem cover_card_le (Y r : ℕ) (hY : 2 ≤ Y)
    (hr : r = ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ))⌋₊) (hr1 : 1 ≤ r) :
    (((Finset.Ioc (Y / 2) Y).filter (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
      ≤ ∑ j ∈ Finset.range (Y / r + 1),
          (((Finset.Icc (Y / 2 + j * r - ⌊((Y / 2 + j * r : ℕ) : ℝ) ^ (0.99979 : ℝ)⌋₊)
              (Y / 2 + j * r + ⌊((Y / 2 + j * r : ℕ) : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
            (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ) := by
  classical
  have hr0 : 0 < r := hr1
  -- the window radius is monotone in the centre
  have hradmono : ∀ c c' : ℕ, 0 < c → c ≤ c' →
      ⌊(c : ℝ) ^ (0.99979 : ℝ)⌋₊ ≤ ⌊(c' : ℝ) ^ (0.99979 : ℝ)⌋₊ := by
    intro c c' hc hle
    apply Nat.floor_le_floor
    exact Real.rpow_le_rpow (by positivity) (by exact_mod_cast hle) (by norm_num)
  have hsub : ((Finset.Ioc (Y / 2) Y).filter (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)) ⊆
      (Finset.range (Y / r + 1)).biUnion (fun j =>
        (Finset.Icc (Y / 2 + j * r - ⌊((Y / 2 + j * r : ℕ) : ℝ) ^ (0.99979 : ℝ)⌋₊)
            (Y / 2 + j * r + ⌊((Y / 2 + j * r : ℕ) : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
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
      have hrad : r ≤ ⌊((Y / 2 + q : ℕ) : ℝ) ^ (0.99979 : ℝ)⌋₊ := by
        have h1 : ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ))⌋₊
            ≤ ⌊((Y / 2 + q : ℕ) : ℝ) ^ (0.99979 : ℝ)⌋₊ := by
          apply hradmono
          · have : 0 < Y / 2 := by omega
            omega
          · omega
        rwa [← hr] at h1
      have hkdecomp : k = Y / 2 + q + m := by omega
      have hradg : r ≤ ⌊((Y / 2 + j * r : ℕ) : ℝ) ^ (0.99979 : ℝ)⌋₊ := by
        rw [← hq]
        exact hrad
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hkP⟩
  rw [← Nat.cast_sum]
  exact_mod_cast (Finset.card_le_card hsub).trans Finset.card_biUnion_le

/-! ### The block bound from the two leaves -/

/-- One dyadic block `(Y/2, Y]` holds at most `2 C1 C2 Y^{0.8789126}` exceptions: the cover of
`cover_card_le` has `C2 Y^{0.00021}` windows, each charged `C1 N^{0.8787026} ≤ 2 C1 Y^{0.8787026}`
because its centre is at most `2 Y`. -/
private theorem block_le {C1 C2 : ℝ} {N0 : ℕ} (hC1 : 0 ≤ C1)
    (hwin : ∀ N : ℕ, N0 ≤ N →
      (((Finset.Icc (N - ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)
            (N + ⌊(N : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
        ≤ C1 * (N : ℝ) ^ (0.8787026 : ℝ))
    (hcov : ∀ Y : ℕ, 2 ≤ Y →
      ((Y / ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ))⌋₊ + 1 : ℕ) : ℝ)
        ≤ C2 * (Y : ℝ) ^ (0.00021 : ℝ))
    (Y : ℕ) (hY : max (2 * N0) 2 ≤ Y) :
    (((Finset.Ioc (Y / 2) Y).filter (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
      ≤ (2 * C1 * C2) * (Y : ℝ) ^ (0.8789126 : ℝ) := by
  classical
  have hY2 : 2 ≤ Y := le_trans (le_max_right _ _) hY
  have hYN0 : 2 * N0 ≤ Y := le_trans (le_max_left _ _) hY
  have hYpos : (0 : ℝ) < Y := by
    have : 0 < Y := by omega
    exact_mod_cast this
  set r : ℕ := ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99979 : ℝ))⌋₊ with hr
  have hr1 : 1 ≤ r := by
    rw [hr]
    refine (Nat.one_le_floor_iff _).mpr ?_
    have h1 : (1 : ℝ) ≤ ((Y / 2 : ℕ) : ℝ) := by
      have : 1 ≤ Y / 2 := by omega
      exact_mod_cast this
    exact Real.one_le_rpow h1 (by norm_num)
  have hterm : ∀ j ∈ Finset.range (Y / r + 1),
      (((Finset.Icc (Y / 2 + j * r - ⌊((Y / 2 + j * r : ℕ) : ℝ) ^ (0.99979 : ℝ)⌋₊)
          (Y / 2 + j * r + ⌊((Y / 2 + j * r : ℕ) : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
        ≤ C1 * 2 * (Y : ℝ) ^ (0.8787026 : ℝ) := by
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
    calc (((Finset.Icc (c - ⌊(c : ℝ) ^ (0.99979 : ℝ)⌋₊)
            (c + ⌊(c : ℝ) ^ (0.99979 : ℝ)⌋₊)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
        ≤ C1 * (c : ℝ) ^ (0.8787026 : ℝ) := hw
      _ ≤ C1 * (2 * (Y : ℝ)) ^ (0.8787026 : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ hC1
          exact Real.rpow_le_rpow (by positivity) hcast (by norm_num)
      _ = C1 * ((2 : ℝ) ^ (0.8787026 : ℝ) * (Y : ℝ) ^ (0.8787026 : ℝ)) := by
          rw [Real.mul_rpow (by norm_num) hYpos.le]
      _ ≤ C1 * (2 * (Y : ℝ) ^ (0.8787026 : ℝ)) := by
          apply mul_le_mul_of_nonneg_left _ hC1
          have h2 : (2 : ℝ) ^ (0.8787026 : ℝ) ≤ 2 := by
            calc (2 : ℝ) ^ (0.8787026 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
                  Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
              _ = 2 := Real.rpow_one 2
          nlinarith [Real.rpow_nonneg hYpos.le (0.8787026 : ℝ)]
      _ = C1 * 2 * (Y : ℝ) ^ (0.8787026 : ℝ) := by ring
  have hstep := cover_card_le Y r hY2 hr.symm hr1
  have hsum := Finset.sum_le_sum hterm
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul] at hsum
  have hJ : ((Y / r + 1 : ℕ) : ℝ) ≤ C2 * (Y : ℝ) ^ (0.00021 : ℝ) := hcov Y hY2
  have hcount : (((Finset.Ioc (Y / 2) Y).filter
      (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
      ≤ ((Y / r + 1 : ℕ) : ℝ) * (C1 * 2 * (Y : ℝ) ^ (0.8787026 : ℝ)) :=
    hstep.trans hsum
  calc (((Finset.Ioc (Y / 2) Y).filter
        (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
      ≤ ((Y / r + 1 : ℕ) : ℝ) * (C1 * 2 * (Y : ℝ) ^ (0.8787026 : ℝ)) := hcount
    _ ≤ (C2 * (Y : ℝ) ^ (0.00021 : ℝ)) * (C1 * 2 * (Y : ℝ) ^ (0.8787026 : ℝ)) := by
        apply mul_le_mul_of_nonneg_right hJ
        positivity
    _ = C1 * 2 * C2 * ((Y : ℝ) ^ (0.00021 : ℝ) * (Y : ℝ) ^ (0.8787026 : ℝ)) := by ring
    _ = C1 * 2 * C2 * (Y : ℝ) ^ (0.8789126 : ℝ) := by
        rw [← Real.rpow_add hYpos]
        norm_num
    _ = (2 * C1 * C2) * (Y : ℝ) ^ (0.8789126 : ℝ) := by ring

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

/-! ### `lu`, assembled -/

/-- `lu`, assembled from the two leaves: the block count at `0.8789126` from LEAF 1 and LEAF 2,
its exponent raised to `0.879`, and the dyadic summation. -/
theorem lu_split : PowerBound 0.879 := by
  classical
  obtain ⟨C1, N0, hC1, hN0, hwin⟩ := leaf_window_count
  obtain ⟨C2, hC2, hcov⟩ := leaf_cover_count
  have hblk : ∀ Y : ℕ, max (2 * N0) 2 ≤ Y →
      (((Finset.Ioc (Y / 2) Y).filter (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
        ≤ (2 * C1 * C2) * (Y : ℝ) ^ (0.879 : ℝ) := by
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

#print axioms lu_split

end LeanLab.ExceptionalSet
