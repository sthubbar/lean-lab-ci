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

LEAF 2, `leaf_cover_count`, is PROVED. LEAF 1, `leaf_window_count`, is OPEN: it is the
analytic density input of the paper, not available in Mathlib 4.35. The assembly `li_split`
has no sorry and does not use `li`, but it inherits `sorryAx` through LEAF 1.
Checked only by the Lean kernel. Binary Goldbach itself is OPEN; this is the almost-all bound.
-/
import LeanLab.ExceptionalSet.Statements

namespace LeanLab.ExceptionalSet
open Real Filter Topology

attribute [local instance] Classical.propDecidable

/-- The radius of the window is at most its centre when `N ≥ 1`. -/
private lemma window_radius_le (N : ℕ) (hN : 1 ≤ N) :
    ⌊(N : ℝ) ^ (0.99 : ℝ)⌋₊ ≤ N := by
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hpow : (N : ℝ) ^ (0.99 : ℝ) ≤ (N : ℝ) :=
    calc (N : ℝ) ^ (0.99 : ℝ) ≤ (N : ℝ) ^ (1 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
      _ = (N : ℝ) := Real.rpow_one _
  simpa using (Nat.floor_le_floor hpow)

/-- The exceptional points in the window are in the exceptional set up to `2N`, apart from
the four points below `4`. -/
private lemma window_subset_exceptions (N : ℕ) (hN : 1 ≤ N) :
    ((Finset.Icc (N - ⌊(N : ℝ) ^ (0.99 : ℝ)⌋₊)
          (N + ⌊(N : ℝ) ^ (0.99 : ℝ)⌋₊)).filter
        (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n))
      ⊆ ((Finset.Icc 4 (2 * N)).filter
        (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)) ∪ Finset.Icc 0 3 := by
  classical
  intro n hn
  rw [Finset.mem_filter, Finset.mem_Icc] at hn
  obtain ⟨⟨hnlo, hnhi⟩, hnP⟩ := hn
  have hR := window_radius_le N hN
  rw [Finset.mem_union]
  by_cases h4 : 4 ≤ n
  · left
    rw [Finset.mem_filter, Finset.mem_Icc]
    exact ⟨⟨h4, by omega⟩, hnP⟩
  · right
    rw [Finset.mem_Icc]
    omega

/-- The window has at most `E (2N) + 4` exceptional points. -/
private lemma window_card_le_E_add_four (N : ℕ) (hN : 1 ≤ N) :
    (((Finset.Icc (N - ⌊(N : ℝ) ^ (0.99 : ℝ)⌋₊)
          (N + ⌊(N : ℝ) ^ (0.99 : ℝ)⌋₊)).filter
        (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℕ)
      ≤ E (2 * N) + 4 := by
  classical
  have hsub := window_subset_exceptions N hN
  have hcard :
      ((Finset.Icc (N - ⌊(N : ℝ) ^ (0.99 : ℝ)⌋₊)
            (N + ⌊(N : ℝ) ^ (0.99 : ℝ)⌋₊)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card
        ≤ ((Finset.Icc 4 (2 * N)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card + (Finset.Icc 0 3).card := by
    exact (Finset.card_le_card hsub).trans (Finset.card_union_le _ _)
  simpa [E] using hcard

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
  classical
  obtain ⟨K, hK⟩ := zhao
  set C₀ : ℝ := max K 0 with hC₀
  have hC₀0 : 0 ≤ C₀ := le_max_right _ _
  have hglobal : ∀ X : ℕ, 1 ≤ X →
      (E X : ℝ) ≤ C₀ * (X : ℝ) ^ (7 / 10 : ℝ) := by
    intro X hX
    calc (E X : ℝ) ≤ K * (X : ℝ) ^ (7 / 10 : ℝ) := hK X hX
      _ ≤ C₀ * (X : ℝ) ^ (7 / 10 : ℝ) := by
        gcongr
        exact le_max_left _ _
  refine ⟨2 * C₀ + 4, ?_⟩
  refine ⟨1, ?_⟩
  refine And.intro (by nlinarith [hC₀0]) (And.intro (by norm_num) ?_)
  intro N hN
  have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < (N : ℝ) := by linarith
  have h2N1 : 1 ≤ 2 * N := by omega
  have hE := hglobal (2 * N) h2N1
  have htwo :
      ((2 * N : ℕ) : ℝ) ^ (7 / 10 : ℝ) ≤ 2 * (N : ℝ) ^ (0.903 : ℝ) := by
    rw [show ((2 * N : ℕ) : ℝ) = (2 : ℝ) * (N : ℝ) by push_cast; ring,
      Real.mul_rpow (by norm_num) hNpos.le]
    have hbase : (2 : ℝ) ^ (7 / 10 : ℝ) ≤ 2 := by
      calc (2 : ℝ) ^ (7 / 10 : ℝ) ≤ (2 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by norm_num)
        _ = 2 := Real.rpow_one 2
    have hexp : (N : ℝ) ^ (7 / 10 : ℝ) ≤ (N : ℝ) ^ (0.903 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le hN1 (by norm_num)
    exact mul_le_mul hbase hexp (Real.rpow_nonneg hNpos.le _) (by positivity)
  have hcount :
      (((Finset.Icc (N - ⌊(N : ℝ) ^ (0.99 : ℝ)⌋₊)
            (N + ⌊(N : ℝ) ^ (0.99 : ℝ)⌋₊)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
        ≤ (E (2 * N) : ℝ) + 4 := by
    exact_mod_cast window_card_le_E_add_four N hN
  have hpow : (1 : ℝ) ≤ (N : ℝ) ^ (0.903 : ℝ) :=
    Real.one_le_rpow hN1 (by norm_num)
  calc
      (((Finset.Icc (N - ⌊(N : ℝ) ^ (0.99 : ℝ)⌋₊)
            (N + ⌊(N : ℝ) ^ (0.99 : ℝ)⌋₊)).filter
          (fun n : ℕ => Even n ∧ ¬ IsGoldbachSum n)).card : ℝ)
        ≤ (E (2 * N) : ℝ) + 4 := hcount
    _ ≤ C₀ * ((2 * N : ℕ) : ℝ) ^ (7 / 10 : ℝ) + 4 := add_le_add_left hE 4
    _ ≤ 2 * C₀ * (N : ℝ) ^ (0.903 : ℝ) + 4 := by
      calc C₀ * ((2 * N : ℕ) : ℝ) ^ (7 / 10 : ℝ) + 4
          ≤ C₀ * (2 * (N : ℝ) ^ (0.903 : ℝ)) + 4 :=
            add_le_add_left (mul_le_mul_of_nonneg_left htwo hC₀0) 4
        _ = 2 * C₀ * (N : ℝ) ^ (0.903 : ℝ) + 4 := by ring
    _ ≤ 2 * C₀ * (N : ℝ) ^ (0.903 : ℝ) +
        4 * (N : ℝ) ^ (0.903 : ℝ) := by
      have h4 : 4 ≤ 4 * (N : ℝ) ^ (0.903 : ℝ) := by
        calc (4 : ℝ) = 4 * 1 := by ring
          _ ≤ 4 * (N : ℝ) ^ (0.903 : ℝ) :=
            mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 4)
      linarith
    _ = (2 * C₀ + 4) * (N : ℝ) ^ (0.903 : ℝ) := by ring

/-- `y / y^{0.99} = y^{0.01}` for `y > 0`: the step that turns the `Y^{0.99}` of the cover
count into the exponent `0.01`. Helper for `leaf_cover_count`. -/
private lemma rpow_step {y : ℝ} (hy : 0 < y) :
    y / y ^ (0.99 : ℝ) = y ^ (0.01 : ℝ) := by
  have h : y ^ (0.99 : ℝ) * y ^ (0.01 : ℝ) = y := by
    rw [← Real.rpow_add hy]
    norm_num
  rw [div_eq_iff (ne_of_gt (Real.rpow_pos_of_pos hy _))]
  linarith [h]

/-- LEAF 2 of 2, the cover count: for `Y ≥ 2` the dyadic block `(Y/2, Y]` is covered by the
`Y / r + 1` windows of radius `r = ⌊(Y/2)^{0.99}⌋` centred at `Y/2 + j r`, `j < Y/r + 1`,
and that number of windows is at most `C Y^{0.01}`. An estimate on `⌊·⌋₊` and powers only,
with no reference to `E`. -/
theorem leaf_cover_count :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Y : ℕ, 2 ≤ Y →
      ((Y / ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ))⌋₊ + 1 : ℕ) : ℝ)
        ≤ C * (Y : ℝ) ^ (0.01 : ℝ) := by
  refine ⟨10, by norm_num, ?_⟩
  intro Y hY
  have hY1 : (1 : ℝ) ≤ (Y : ℝ) := by
    have h : (1 : ℕ) ≤ Y := by omega
    exact_mod_cast h
  have hYpos : (0 : ℝ) < (Y : ℝ) := by linarith
  set r : ℕ := ⌊(((Y / 2 : ℕ) : ℝ) ^ (0.99 : ℝ))⌋₊ with hr
  set t : ℝ := (((Y / 2 : ℕ) : ℝ)) ^ (0.99 : ℝ) with ht
  have hr1 : 1 ≤ r := by
    rw [hr, Nat.one_le_floor_iff]
    have h1 : (1 : ℝ) ≤ ((Y / 2 : ℕ) : ℝ) := by
      have : (1 : ℕ) ≤ Y / 2 := by omega
      exact_mod_cast this
    exact Real.one_le_rpow h1 (by norm_num)
  have htpos : 0 < t := by
    rw [ht]
    have h1 : (0 : ℝ) < ((Y / 2 : ℕ) : ℝ) := by
      have : (0 : ℕ) < Y / 2 := by omega
      exact_mod_cast this
    exact Real.rpow_pos_of_pos h1 _
  -- t ≤ r + 1 ≤ 2 r
  have htr : t / 2 ≤ (r : ℝ) := by
    have h1 : t ≤ (r : ℝ) + 1 := by
      rw [ht, hr]
      exact (Nat.lt_floor_add_one _).le
    have h2 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
    linarith
  -- lower bound on t: (Y/4)^0.99 ≤ t
  have hbase : ((Y : ℝ) / 4) ≤ ((Y / 2 : ℕ) : ℝ) := by
    have heq : 2 * (Y / 2) + Y % 2 = Y := Nat.div_add_mod Y 2
    have hmod : Y % 2 ≤ 1 := Nat.le_of_lt_succ (Nat.mod_lt Y (by norm_num))
    have hhalf : 1 ≤ Y / 2 := by omega
    have h4 : Y ≤ 4 * (Y / 2) := by omega
    have h4' : (Y : ℝ) ≤ 4 * ((Y / 2 : ℕ) : ℝ) := by exact_mod_cast h4
    linarith
  have hquarter : (0 : ℝ) < (Y : ℝ) / 4 := by linarith
  have htlow : ((Y : ℝ) / 4) ^ (0.99 : ℝ) ≤ t := by
    rw [ht]
    exact Real.rpow_le_rpow hquarter.le hbase (by norm_num)
  -- 4^0.99 ≤ 4
  have h4pow : (4 : ℝ) ^ (0.99 : ℝ) ≤ 4 := by
    have h := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 4) (by norm_num : (0.99 : ℝ) ≤ 1)
    simpa using h
  -- key: Y / t ≤ 8 Y^0.01 ... work through 2Y/t
  have hkey : (Y : ℝ) / (t / 2) ≤ 8 * (Y : ℝ) ^ (0.01 : ℝ) := by
    have ht2 : (0 : ℝ) < t / 2 := by linarith
    -- 2Y/t ≤ 2Y/((Y^0.99)/4) = 8 Y / Y^0.99 = 8 Y^0.01
    have hq : (0 : ℝ) < ((Y : ℝ) ^ (0.99 : ℝ)) / 4 := by
      have := Real.rpow_pos_of_pos hYpos (0.99 : ℝ)
      linarith
    have h1 : (Y : ℝ) / (t / 2) ≤ (Y : ℝ) / (((Y : ℝ) ^ (0.99 : ℝ)) / 4 / 2) := by
      apply div_le_div_of_nonneg_left hYpos.le _ _
      · linarith [hq]
      · have : ((Y : ℝ) ^ (0.99 : ℝ)) / 4 ≤ t := by
          refine le_trans ?_ htlow
          have h4pos : (0 : ℝ) < (4 : ℝ) ^ (0.99 : ℝ) := Real.rpow_pos_of_pos (by norm_num) _
          rw [Real.div_rpow hYpos.le (by norm_num : (0 : ℝ) ≤ 4)]
          exact div_le_div_of_nonneg_left (Real.rpow_nonneg hYpos.le _) h4pos h4pow
        linarith
    have h2 : (Y : ℝ) / (((Y : ℝ) ^ (0.99 : ℝ)) / 4 / 2)
        = 8 * ((Y : ℝ) / (Y : ℝ) ^ (0.99 : ℝ)) := by
      field_simp
      ring
    rw [h2, rpow_step hYpos] at h1
    exact h1
  have hcast : ((Y / r : ℕ) : ℝ) ≤ (Y : ℝ) / (r : ℝ) := Nat.cast_div_le
  have hdiv : (Y : ℝ) / (r : ℝ) ≤ (Y : ℝ) / (t / 2) := by
    apply div_le_div_of_nonneg_left hYpos.le _ _
    · linarith
    · exact htr
  have hone : (1 : ℝ) ≤ (Y : ℝ) ^ (0.01 : ℝ) := Real.one_le_rpow hY1 (by norm_num)
  push_cast
  calc ((Y / r : ℕ) : ℝ) + 1 ≤ (Y : ℝ) / (r : ℝ) + 1 := by linarith
    _ ≤ (Y : ℝ) / (t / 2) + 1 := by linarith
    _ ≤ 8 * (Y : ℝ) ^ (0.01 : ℝ) + 1 := by linarith
    _ ≤ 10 * (Y : ℝ) ^ (0.01 : ℝ) := by linarith


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
