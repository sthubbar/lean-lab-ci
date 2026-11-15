import Mathlib

/-!
The repair record for the branch free-ms-leanstral/task507.

That branch tried to close `LeanLab.KumchevLiu2007.Task516a.eq53_large_eps` by splitting on
`5 / 6 ≤ ε` and claiming that in that case the window set `windowPairs` of display 53 is empty,
so that the error term `err53` vanishes and the count is zero. The claim is false. The window
height is `Y = X ^ (7 / 12 + ε / 2)` and the window set is empty only when the spacing
`Y ^ (1 / 4)` beats `X + H`, whose exponent in `X` is `(7 / 12 + ε / 2) / 4`. At `ε = 5 / 6`
that exponent is `1 / 4`, far below the `1` the branch assumed, and the window set at `X = 2`
contains the pair `(0, 1)`. The two statements below record the refutation, so the branch's two
inner `sorry`s are not a split of the leaf but the gap of a false case split.

The third statement generalizes the first two: the window set is empty for no `X ≥ 2` and
`ε > 0` at all, so the split on `ε` cannot prove `eq53_large_eps` at any epsilon.

`card_windowPairs_le_ceil_sqrt` counts the same set along `v.2` instead, which is the sharper
bound when `Y` is large, and `card_windowPairs_le_min` takes both counts at once.

`card_le_ceil_of_forall_mem_Ico` is the general count: a finite set of naturals inside `[u, u + Y)`
has at most `⌈Y⌉₊` elements. The fourth statement is its use on display 53: `v.1 + v.2 ^ 2 = n`
makes `v.1` determine `v.2`, so a window set has no more pairs than the `a`-window
`X - Y ≤ v.1 < X` has integers.

The fifth statement puts a member of a window set in `[X - Y, X + Y)`, the support of the windows
that the paper uses to reduce the range of `epsilon`, and the sixth carries the cardinality bound
through a further filter, which is how it reaches the rough count inside `err53`.

The seventh statement spends the cardinality bound: the sum over one window set, which is the
singular integral of display 53, is at most `⌈Y⌉₊` times a uniform bound on its summands.

The last six statements are the bookkeeping on the window height `X ^ (7 / 12 + ε / 2)` of page
15: its positivity, its lower bound `1`, its square root as a power of `X`, its monotonicity in
`ε` and in `X`, and the cancellation of `ε / 2` against `X ^ (-(ε / 2))`.

This file is imported by nothing and adds no definition. `Decomp516a` keeps main's blob, so
`eq53_large_eps` stays open with main's single `sorry`.
AI wrote the Lean code. Goldbach is open.
-/

open scoped BigOperators

namespace LeanLab.KumchevLiu2007.Task507

/-- The branch's case `5 / 6 ≤ ε` assumed the window exponent `(7 / 12 + ε / 2) / 4` exceeds
`1`, so that the window spacing `Y ^ (1 / 4)` beats `X + H`. At `ε = 5 / 6` the exponent is
`1 / 4`, so the step fails at the left end of the very case the branch claimed.
Source: arXiv 0801.0130 page 16 display 53, with the window height `Y = X ^ (7 / 12 + ε / 2)`
of page 15. -/
theorem windowExponent_not_gt_one_at_five_sixths :
    ¬ (1 : ℝ) < (7 / 12 + (5 / 6) / 2) * (1 / 4) := by
  norm_num

/-- The window set of display 53 at `X = 2` and `ε = 5 / 6` is not empty: it contains the pair
`(0, 1)`, that is `n = 1` with `v.1 = 0` and `v.2 = 1`. So the branch's
`windowPairs_empty_of_big_eps` fails at `ε = 5 / 6`, and `err53` does not vanish there.
Source: arXiv 0801.0130 page 16 display 53, with window support `X - Y ≤ v.1 < X` and
`Y ^ (1 / 2) / 2 ≤ v.2 < Y ^ (1 / 2)`. -/
theorem windowPairs_nonempty_at_five_sixths :
    ((Finset.range (⌊(2 : ℝ)⌋₊ + 1)).product
        (Finset.range (⌊Real.sqrt ((2 : ℝ) ^ ((7 / 12 : ℝ) + (5 / 6 : ℝ) / 2))⌋₊ + 1))).filter
      (fun v : ℕ × ℕ =>
        (2 : ℝ) - (2 : ℝ) ^ ((7 / 12 : ℝ) + (5 / 6 : ℝ) / 2) ≤ (v.1 : ℝ) ∧
        (v.1 : ℝ) < 2 ∧
        Real.sqrt ((2 : ℝ) ^ ((7 / 12 : ℝ) + (5 / 6 : ℝ) / 2)) / 2 ≤ (v.2 : ℝ) ∧
        (v.2 : ℝ) < Real.sqrt ((2 : ℝ) ^ ((7 / 12 : ℝ) + (5 / 6 : ℝ) / 2)) ∧
        v.1 + v.2 ^ 2 = 1) ≠ ∅ := by
  have hexp : (7 / 12 : ℝ) + (5 / 6) / 2 = 1 := by norm_num
  have hY : (2 : ℝ) ^ ((7 / 12 : ℝ) + (5 / 6 : ℝ) / 2) = 2 := by
    rw [hexp, Real.rpow_one]
  have hs1 : (1 : ℝ) < Real.sqrt 2 := by
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  have hs2 : Real.sqrt 2 < 2 := by
    rw [Real.sqrt_lt' (by norm_num)]
    norm_num
  have hfloor : ⌊Real.sqrt ((2 : ℝ) ^ ((7 / 12 : ℝ) + (5 / 6 : ℝ) / 2))⌋₊ = 1 := by
    rw [hY, Nat.floor_eq_iff (Real.sqrt_nonneg 2)]
    exact ⟨by norm_num, by norm_num⟩
  have hnat : ⌊(2 : ℝ)⌋₊ = 2 := Nat.floor_natCast 2
  intro h
  have hmem : (0, 1) ∈
      ((Finset.range (⌊(2 : ℝ)⌋₊ + 1)).product
        (Finset.range (⌊Real.sqrt ((2 : ℝ) ^ ((7 / 12 : ℝ) + (5 / 6 : ℝ) / 2))⌋₊ + 1))).filter
        (fun v : ℕ × ℕ =>
          (2 : ℝ) - (2 : ℝ) ^ ((7 / 12 : ℝ) + (5 / 6 : ℝ) / 2) ≤ (v.1 : ℝ) ∧
          (v.1 : ℝ) < 2 ∧
          Real.sqrt ((2 : ℝ) ^ ((7 / 12 : ℝ) + (5 / 6 : ℝ) / 2)) / 2 ≤ (v.2 : ℝ) ∧
          (v.2 : ℝ) < Real.sqrt ((2 : ℝ) ^ ((7 / 12 : ℝ) + (5 / 6 : ℝ) / 2)) ∧
          v.1 + v.2 ^ 2 = 1) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.mem_range]
      omega
    · rw [Finset.mem_range]
      omega
    · rw [hY]
      show (2 : ℝ) - 2 ≤ ((0 : ℕ) : ℝ)
      norm_num
    · show ((0 : ℕ) : ℝ) < 2
      norm_num
    · rw [hY]
      show Real.sqrt 2 / 2 ≤ ((1 : ℕ) : ℝ)
      norm_num
      linarith
    · rw [hY]
      show ((1 : ℕ) : ℝ) < Real.sqrt 2
      norm_num
      exact hs1
    · show (0 : ℕ) + 1 ^ 2 = 1
      norm_num
  rw [h] at hmem
  simp at hmem

/-- The window height is strictly above `1` for `X > 1` and `ε > 0`. This is what
`exists_nat_between_half_sqrt` needs to put an integer in the `b`-window, and with the `a`-window
lemma it is why the window set of display 53 is never empty in the paper's range.
Source: arXiv 0801.0130 page 15 window height and page 16 display 53. -/
theorem windowY_one_lt (X ε : ℝ) (hX : 1 < X) (hε : 0 < ε) :
    1 < X ^ ((7 / 12 : ℝ) + ε / 2) :=
  Real.one_lt_rpow hX (by linarith)

/-- In the written range `ε ≤ 5 / 18` of page 16 the window height is at most `X ^ (13 / 18)`,
because `7 / 12 + (5 / 18) / 2 = 13 / 18`. This is the bound the paper's reduction of the range to
the written one uses.
Source: arXiv 0801.0130 page 15 window height and page 16 the written range `epsilon` at most
`5 / 18`. -/
theorem windowY_le_five_eighteenths (X ε : ℝ) (hX : 1 ≤ X) (hε : ε ≤ 5 / 18) :
    X ^ ((7 / 12 : ℝ) + ε / 2) ≤ X ^ (13 / 18 : ℝ) :=
  Real.rpow_le_rpow_of_exponent_le hX (by linarith)

/-- There is a natural number in the `b`-window `[sqrt Y / 2, sqrt Y)` as soon as `Y > 1`. The
interval is open at the top, so the witness is `1` when `sqrt Y ≤ 2` and `⌈sqrt Y / 2⌉₊` otherwise.
This is why a display 53 window set cannot be empty.
Source: arXiv 0801.0130 page 16 display 53, window support `Y ^ (1 / 2) / 2 ≤ v.2 < Y ^ (1 / 2)`. -/
theorem exists_nat_between_half_sqrt (Y : ℝ) (hY : 1 < Y) :
    ∃ b : ℕ, Real.sqrt Y / 2 ≤ (b : ℝ) ∧ (b : ℝ) < Real.sqrt Y := by
  set t : ℝ := Real.sqrt Y with ht
  have ht1 : 1 < t := by
    rw [ht, Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
    exact hY
  rcases le_or_gt t 2 with h2 | h2
  · refine ⟨1, ?_, ?_⟩
    · push_cast
      linarith
    · push_cast
      linarith
  · refine ⟨⌈t / 2⌉₊, Nat.le_ceil (t / 2), ?_⟩
    have h1 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ t / 2 by linarith)
    linarith

/-- There is a natural number in the `a`-window `[X - Y, X)` when `X ≥ 2` and `Y ≥ 1`. The witness
is `⌈X⌉₊ - 1`, which is below `X` because `⌈X⌉₊ < X + 1`, and at least `X - Y` because
`⌈X⌉₊ ≥ X` and `Y ≥ 1`.
Source: arXiv 0801.0130 page 16 display 53, window support `X - Y ≤ v.1 < X`. -/
theorem exists_nat_in_left_window (X Y : ℝ) (hX : 2 ≤ X) (hY : 1 ≤ Y) :
    ∃ a : ℕ, X - Y ≤ (a : ℝ) ∧ (a : ℝ) < X := by
  have hce : 1 ≤ ⌈X⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hcast : ((⌈X⌉₊ - 1 : ℕ) : ℝ) = (⌈X⌉₊ : ℝ) - 1 := by
    rw [Nat.cast_sub hce]
    push_cast
    ring
  refine ⟨⌈X⌉₊ - 1, ?_, ?_⟩
  · rw [hcast]
    have h1 : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
    linarith
  · rw [hcast]
    have h1 : (⌈X⌉₊ : ℝ) < X + 1 := Nat.ceil_lt_add_one (by linarith)
    linarith

/-- The general form of the refutation: for every `X ≥ 2` and every `ε > 0` the display 53 window
set is not empty, so the branch's `windowPairs_empty_of_big_eps` fails for every `ε`, not only at
`ε = 5 / 6`. The witness is `(⌈X⌉₊ - 1, ⌈sqrt Y / 2⌉₊)`, whose `v.1` sits in the `a`-window
`X - Y ≤ v.1 < X` because `Y > 1`, and whose `v.2` sits in the `b`-window
`sqrt Y / 2 ≤ v.2 < sqrt Y` because `sqrt Y > 1`. Since `Y = X ^ (7 / 12 + ε / 2) > 1` for
`X > 1` and `ε > 0`, the window set is empty for no pair in the paper's range, so `err53` never
vanishes by emptiness and the case split on `ε` cannot prove `eq53_large_eps`.
Source: arXiv 0801.0130 page 16 display 53, window support `X - Y ≤ v.1 < X` and
`Y ^ (1 / 2) / 2 ≤ v.2 < Y ^ (1 / 2)`. -/
theorem exists_windowPairs_nonempty_at_any_eps (X ε : ℝ) (hX : 2 ≤ X) (hε : 0 < ε) :
    ∃ n : ℕ,
      ((Finset.range (⌊X⌋₊ + 1)).product
        (Finset.range (⌊Real.sqrt (X ^ ((7 / 12 : ℝ) + ε / 2))⌋₊ + 1))).filter
      (fun v : ℕ × ℕ =>
        X - X ^ ((7 / 12 : ℝ) + ε / 2) ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
        Real.sqrt (X ^ ((7 / 12 : ℝ) + ε / 2)) / 2 ≤ (v.2 : ℝ) ∧
        (v.2 : ℝ) < Real.sqrt (X ^ ((7 / 12 : ℝ) + ε / 2)) ∧
        v.1 + v.2 ^ 2 = n) ≠ ∅ := by
  set Y : ℝ := X ^ ((7 / 12 : ℝ) + ε / 2) with hY
  have hY1 : 1 < Y := by
    rw [hY]
    exact windowY_one_lt X ε (by linarith) hε
  obtain ⟨b, hb_ge, hb_lt⟩ := exists_nat_between_half_sqrt Y hY1
  obtain ⟨a, ha_ge, haX⟩ := exists_nat_in_left_window X Y hX hY1.le
  have ha_range : a < ⌊X⌋₊ + 1 := by
    have h1 : X < (⌊X⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one X
    have h2 : (a : ℝ) < (⌊X⌋₊ : ℝ) + 1 := lt_trans haX h1
    exact_mod_cast h2
  have hb_range : b < ⌊Real.sqrt Y⌋₊ + 1 := by
    have h1 : Real.sqrt Y < (⌊Real.sqrt Y⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one _
    have h2 : (b : ℝ) < (⌊Real.sqrt Y⌋₊ : ℝ) + 1 := lt_trans hb_lt h1
    exact_mod_cast h2
  refine ⟨a + b ^ 2, ?_⟩
  intro h
  have hmem : (a, b) ∈
      ((Finset.range (⌊X⌋₊ + 1)).product
        (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
      (fun v : ℕ × ℕ =>
        X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
        Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧
        (v.2 : ℝ) < Real.sqrt Y ∧
        v.1 + v.2 ^ 2 = a + b ^ 2) := by
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Finset.mem_range]
      exact ha_range
    · rw [Finset.mem_range]
      exact hb_range
    · exact ha_ge
    · exact haX
    · exact hb_ge
    · exact hb_lt
    · rfl
  rw [h] at hmem
  simp at hmem

/-- Counting lemma for a finite set of naturals inside a half open interval: if every element `a`
of `A` satisfies `u ≤ a < u + Y`, then `A` has at most `⌈Y⌉₊` elements. The proof maps nothing: it
compares `max A - min A`, which is below `Y`, with the cardinality, which is at most
`max A - min A + 1`. This is the general form of the bound on one display 53 window set, and it
applies to any integer count over an interval.
AI wrote the Lean code. Goldbach is open. -/
theorem card_le_ceil_of_forall_mem_Ico (A : Finset ℕ) (u Y : ℝ)
    (h : ∀ a ∈ A, u ≤ (a : ℝ) ∧ (a : ℝ) < u + Y) : A.card ≤ ⌈Y⌉₊ := by
  classical
  by_cases hempty : A = ∅
  · rw [hempty]
    simp
  have hne : A.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  have hsub : A ⊆ Finset.Icc (A.min' hne) (A.max' hne) := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨A.min'_le x hx, A.le_max' x hx⟩
  have hAcard : A.card ≤ A.max' hne + 1 - A.min' hne := by
    have h1 := Finset.card_le_card hsub
    rwa [Nat.card_Icc] at h1
  have hmax : (A.max' hne : ℝ) < u + Y := (h _ (A.max'_mem hne)).2
  have hmin : u ≤ (A.min' hne : ℝ) := (h _ (A.min'_mem hne)).1
  have hcast : ((A.max' hne + 1 - A.min' hne : ℕ) : ℝ)
      = (A.max' hne : ℝ) - (A.min' hne : ℝ) + 1 := by
    have hmin' : A.min' hne ≤ A.max' hne + 1 := by
      have h2 : A.min' hne ≤ A.max' hne := A.min'_le _ (A.max'_mem hne)
      omega
    rw [Nat.cast_sub hmin']
    push_cast
    ring
  have hlt : (A.card : ℝ) < Y + 1 := by
    have h1 : (A.card : ℝ) ≤ ((A.max' hne + 1 - A.min' hne : ℕ) : ℝ) := by
      exact_mod_cast hAcard
    rw [hcast] at h1
    linarith
  by_contra hcon
  push Not at hcon
  have h1 : (⌈Y⌉₊ : ℝ) + 1 ≤ (A.card : ℝ) := by
    have h2 : ⌈Y⌉₊ + 1 ≤ A.card := hcon
    exact_mod_cast h2
  have h2 : Y ≤ (⌈Y⌉₊ : ℝ) := Nat.le_ceil Y
  linarith

/-- At most `⌈Y⌉₊` pairs of the display 53 window set belong to one `n`. Two pairs with the same
`v.1` have the same `v.2`, because `v.1 + v.2 ^ 2 = n` forces `v.2 ^ 2 = n - v.1`, so the number
of pairs is at most the number of values of `v.1`, and those live in the `a`-window
`X - Y ≤ v.1 < X` of length `Y`, which `card_le_ceil_of_forall_mem_Ico` counts. This is the count
that the Chebyshev step over the window set spends.
Source: arXiv 0801.0130 page 16 display 53, window support `X - Y ≤ v.1 < X`. -/
theorem card_windowPairs_le_ceil (X Y : ℝ) (n : ℕ) :
    (((Finset.range (⌊X⌋₊ + 1)).product
        (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
      (fun v : ℕ × ℕ =>
        X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
        Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧
        (v.2 : ℝ) < Real.sqrt Y ∧
        v.1 + v.2 ^ 2 = n)).card ≤ ⌈Y⌉₊ := by
  classical
  set s := ((Finset.range (⌊X⌋₊ + 1)).product
        (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
      (fun v : ℕ × ℕ =>
        X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
        Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧
        (v.2 : ℝ) < Real.sqrt Y ∧
        v.1 + v.2 ^ 2 = n) with hs
  by_cases hempty : s = ∅
  · rw [hempty]
    simp
  have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  have hinj : Set.InjOn (fun v : ℕ × ℕ => v.1) ↑s := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    simp only [hs, Finset.mem_filter] at ha hb
    obtain ⟨-, -, -, -, ha5⟩ := ha
    obtain ⟨-, -, -, -, hb5⟩ := hb
    have hab' : a.1 = b.1 := hab
    have hsq : a.2 ^ 2 = b.2 ^ 2 := by omega
    have h2 : a.2 = b.2 := Nat.pow_left_injective (by norm_num : 2 ≠ 0) hsq
    exact Prod.ext hab' h2
  have hcardim : s.card = (s.image (fun v : ℕ × ℕ => v.1)).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hbound : (s.image (fun v : ℕ × ℕ => v.1)).card ≤ ⌈Y⌉₊ := by
    refine card_le_ceil_of_forall_mem_Ico _ (X - Y) Y ?_
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨v, hv, hveq⟩ := ha
    simp only [hs, Finset.mem_filter] at hv
    rw [← hveq]
    exact ⟨hv.2.1, by linarith [hv.2.2.1]⟩
  rw [hcardim]
  exact hbound

/-- The same window set, counted along the other axis: at most `⌈sqrt Y / 2⌉₊` pairs belong to one
`n`, because `v.1 + v.2 ^ 2 = n` makes `v.2` determine `v.1`, and the `b`-window
`sqrt Y / 2 ≤ v.2 < sqrt Y` has length `sqrt Y / 2`. This is the sharper of the two bounds when
`Y` is large, since it grows like `sqrt Y` rather than `Y`.
Source: arXiv 0801.0130 page 16 display 53, window support `Y ^ (1 / 2) / 2 ≤ v.2 < Y ^ (1 / 2)`. -/
theorem card_windowPairs_le_ceil_sqrt (X Y : ℝ) (n : ℕ) :
    (((Finset.range (⌊X⌋₊ + 1)).product
        (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
      (fun v : ℕ × ℕ =>
        X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
        Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧
        (v.2 : ℝ) < Real.sqrt Y ∧
        v.1 + v.2 ^ 2 = n)).card ≤ ⌈Real.sqrt Y / 2⌉₊ := by
  classical
  set s := ((Finset.range (⌊X⌋₊ + 1)).product
        (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
      (fun v : ℕ × ℕ =>
        X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
        Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧
        (v.2 : ℝ) < Real.sqrt Y ∧
        v.1 + v.2 ^ 2 = n) with hs
  by_cases hempty : s = ∅
  · rw [hempty]
    simp
  have hne : s.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
  have hinj : Set.InjOn (fun v : ℕ × ℕ => v.2) ↑s := by
    intro a ha b hb hab
    rw [Finset.mem_coe] at ha hb
    simp only [hs, Finset.mem_filter] at ha hb
    obtain ⟨-, hpa⟩ := ha
    obtain ⟨-, hpb⟩ := hb
    have hab' : a.2 = b.2 := hab
    have hsum : a.1 = b.1 := by
      have h1 : a.1 + a.2 ^ 2 = b.1 + b.2 ^ 2 := by rw [hpa.2.2.2.2, hpb.2.2.2.2]
      rw [hab'] at h1
      omega
    exact Prod.ext hsum hab'
  have hcardim : s.card = (s.image (fun v : ℕ × ℕ => v.2)).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hbound : (s.image (fun v : ℕ × ℕ => v.2)).card ≤ ⌈Real.sqrt Y / 2⌉₊ := by
    refine card_le_ceil_of_forall_mem_Ico _ (Real.sqrt Y / 2) (Real.sqrt Y / 2) ?_
    intro a ha
    rw [Finset.mem_image] at ha
    obtain ⟨v, hv, hveq⟩ := ha
    simp only [hs, Finset.mem_filter] at hv
    obtain ⟨-, hp⟩ := hv
    rw [← hveq]
    exact ⟨hp.2.2.1, by linarith [hp.2.2.2.1]⟩
  rw [hcardim]
  exact hbound

/-- Both counts together: a window set of display 53 has at most `min ⌈Y⌉₊ ⌈sqrt Y / 2⌉₊` pairs for
each `n`, the `a`-axis bound and the `b`-axis bound at once.
Source: arXiv 0801.0130 page 16 display 53, window support on both coordinates. -/
theorem card_windowPairs_le_min (X Y : ℝ) (n : ℕ) :
    (((Finset.range (⌊X⌋₊ + 1)).product
        (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
      (fun v : ℕ × ℕ =>
        X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
        Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧
        (v.2 : ℝ) < Real.sqrt Y ∧
        v.1 + v.2 ^ 2 = n)).card ≤ min ⌈Y⌉₊ ⌈Real.sqrt Y / 2⌉₊ :=
  le_min (card_windowPairs_le_ceil X Y n) (card_windowPairs_le_ceil_sqrt X Y n)

/-- The support of the windows: a pair of the display 53 window set forces its `n = v.1 + v.2 ^ 2`
into `[X - Y, X + Y)`. Both bounds come from the set: `X - Y ≤ v.1` and `0 ≤ v.2 ^ 2` give the
lower one, and `v.1 < X` with `v.2 < sqrt Y` gives `v.2 ^ 2 < Y` and so `n < X + Y`. This is the
support statement that the paper cites on page 16 for its remark that, for `epsilon` at most
`5 / 18`, the range reduces to the written one by the support of the windows.
Source: arXiv 0801.0130 page 16 display 53, window support `X - Y ≤ v.1 < X` and
`Y ^ (1 / 2) / 2 ≤ v.2 < Y ^ (1 / 2)`. -/
theorem windowPairs_support (X Y : ℝ) (n : ℕ) (v : ℕ × ℕ)
    (hv : v ∈ ((Finset.range (⌊X⌋₊ + 1)).product
        (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
      (fun v : ℕ × ℕ =>
        X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
        Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧
        (v.2 : ℝ) < Real.sqrt Y ∧
        v.1 + v.2 ^ 2 = n)) :
    X - Y ≤ (n : ℝ) ∧ (n : ℝ) < X + Y := by
  simp only [Finset.mem_filter] at hv
  obtain ⟨-, ha1, ha2, -, hb2, hsum⟩ := hv
  have hsq : (v.2 : ℝ) ^ 2 < Y := (Real.lt_sqrt (by positivity : (0 : ℝ) ≤ (v.2 : ℝ))).mp hb2
  have hn : (n : ℝ) = (v.1 : ℝ) + (v.2 : ℝ) ^ 2 := by
    rw [← hsum]
    push_cast
    ring
  constructor
  · rw [hn]
    nlinarith [sq_nonneg (v.2 : ℝ)]
  · rw [hn]
    linarith

/-- Any further filter of a display 53 window set, and in particular the rough count of display 53
which keeps the pairs with `v.1` prime and with all prime divisors of `v.2` above
`Y ^ (1 / 4) * P ^ (-2)`, still has at most `⌈Y⌉₊` members. This is the form in which the
cardinality bound enters `err53`: `roughCount X Y P n ≤ ⌈Y⌉₊` for every `n`.
Source: arXiv 0801.0130 page 16 display 53, the rough count inside `err53`. -/
theorem card_filter_windowPairs_le_ceil (X Y : ℝ) (n : ℕ) (p : ℕ × ℕ → Prop) [DecidablePred p] :
    ((((Finset.range (⌊X⌋₊ + 1)).product
        (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
      (fun v : ℕ × ℕ =>
        X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
        Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧
        (v.2 : ℝ) < Real.sqrt Y ∧
        v.1 + v.2 ^ 2 = n)).filter p).card ≤ ⌈Y⌉₊ :=
  (Finset.card_filter_le _ _).trans (card_windowPairs_le_ceil X Y n)

/-- The sum over one display 53 window set is at most `⌈Y⌉₊` times a uniform bound `M` on its
summands. This is how the cardinality bound is spent: the singular integral of display 53 is
`∑ v ∈ windowPairs X Y n, (1 / log v.1) * f2Weight (Y ^ (1 / 4) * P ^ (-2)) v.2`, whose summand is
`≤ M` once the weight is bounded below by `Y ^ (1 / 4) * P ^ (-2)`, and this lemma turns that into
`singInt X Y P n ≤ ⌈Y⌉₊ * M` for every `n`.
Source: arXiv 0801.0130 page 16 display 53, the singular integral `singInt` inside `err53`. -/
theorem sum_windowPairs_le_ceil_mul (X Y : ℝ) (n : ℕ) (g : ℕ × ℕ → ℝ) (M : ℝ)
    (hM : 0 ≤ M)
    (hg : ∀ v ∈ ((Finset.range (⌊X⌋₊ + 1)).product
        (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
      (fun v : ℕ × ℕ =>
        X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
        Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧
        (v.2 : ℝ) < Real.sqrt Y ∧
        v.1 + v.2 ^ 2 = n), g v ≤ M) :
    ∑ v ∈ ((Finset.range (⌊X⌋₊ + 1)).product
        (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
      (fun v : ℕ × ℕ =>
        X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
        Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧
        (v.2 : ℝ) < Real.sqrt Y ∧
        v.1 + v.2 ^ 2 = n), g v ≤ ⌈Y⌉₊ * M := by
  classical
  set s := ((Finset.range (⌊X⌋₊ + 1)).product
        (Finset.range (⌊Real.sqrt Y⌋₊ + 1))).filter
      (fun v : ℕ × ℕ =>
        X - Y ≤ (v.1 : ℝ) ∧ (v.1 : ℝ) < X ∧
        Real.sqrt Y / 2 ≤ (v.2 : ℝ) ∧
        (v.2 : ℝ) < Real.sqrt Y ∧
        v.1 + v.2 ^ 2 = n) with hs
  have hg' : ∀ v ∈ s, g v ≤ M := hg
  have hc : (s.card : ℝ) ≤ ⌈Y⌉₊ := by
    rw [hs]
    exact_mod_cast card_windowPairs_le_ceil X Y n
  calc ∑ v ∈ s, g v ≤ s.card • M := Finset.sum_le_card_nsmul s g M hg'
    _ = (s.card : ℝ) * M := by rw [nsmul_eq_mul]
    _ ≤ (⌈Y⌉₊ : ℝ) * M := mul_le_mul_of_nonneg_right hc hM
    _ = ⌈Y⌉₊ • M := by rw [nsmul_eq_mul]
    _ = ⌈Y⌉₊ * M := by rw [nsmul_eq_mul]

/-- The window height `windowY X ε = X ^ (7 / 12 + ε / 2)` of display 53 is positive away from
`X = 0`, which is what lets the window set be read with `sqrt` and with `log`.
Source: arXiv 0801.0130 page 15 window height. -/
theorem windowY_pos (X ε : ℝ) (hX : 0 < X) : 0 < X ^ ((7 / 12 : ℝ) + ε / 2) :=
  Real.rpow_pos_of_pos hX _

/-- The window height is at least `1` for `X ≥ 1` and `ε ≥ 0`, the range in which display 53 is
used. Combined with `exists_windowPairs_nonempty_at_any_eps` this is why the window set can never
be empty in that range.
Source: arXiv 0801.0130 page 15 window height and page 16 display 53. -/
theorem windowY_one_le (X ε : ℝ) (hX : 1 ≤ X) (hε : 0 ≤ ε) :
    1 ≤ X ^ ((7 / 12 : ℝ) + ε / 2) :=
  Real.one_le_rpow hX (by linarith)

/-- The square root of the window height is again a power of `X`, with exponent `7 / 24 + ε / 4`.
The `b`-window of display 53 is written with `sqrt (windowY X ε)`, so this is the identity that
turns its bounds into powers of `X`.
Source: arXiv 0801.0130 page 15 window height and page 16 display 53 window support. -/
theorem sqrt_windowY (X ε : ℝ) (hX : 0 ≤ X) :
    Real.sqrt (X ^ ((7 / 12 : ℝ) + ε / 2)) = X ^ ((7 / 24 : ℝ) + ε / 4) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_mul hX]
  congr 1
  ring

/-- The window height increases with `ε` for `X ≥ 1`, so a larger `ε` gives a wider `a`-window
`X - windowY ≤ v.1 < X`.
Source: arXiv 0801.0130 page 16 display 53 window support. -/
theorem windowY_mono_eps (X ε₁ ε₂ : ℝ) (hX : 1 ≤ X) (hε : ε₁ ≤ ε₂) :
    X ^ ((7 / 12 : ℝ) + ε₁ / 2) ≤ X ^ ((7 / 12 : ℝ) + ε₂ / 2) :=
  Real.rpow_le_rpow_of_exponent_le hX (by linarith)

/-- The window height increases with `X` for `ε ≥ 0`, which is how windows at the two ends of the
interval `(X, X + H]` are compared.
Source: arXiv 0801.0130 page 16 display 53 window support. -/
theorem windowY_mono_X (X₁ X₂ ε : ℝ) (hX : 0 ≤ X₁) (hX12 : X₁ ≤ X₂) (hε : 0 ≤ ε) :
    X₁ ^ ((7 / 12 : ℝ) + ε / 2) ≤ X₂ ^ ((7 / 12 : ℝ) + ε / 2) :=
  Real.rpow_le_rpow hX hX12 (by linarith)

/-- The `ε / 2` that display 53 puts in the window height cancels against `X ^ (-(ε / 2))`, leaving
the fixed `X ^ (7 / 12)`. This is the form in which the mean square estimate and the window height
are compared.
Source: arXiv 0801.0130 page 15 window height and page 16 display 53. -/
theorem windowY_mul_rpow_neg (X ε : ℝ) (hX : 1 ≤ X) :
    X ^ ((7 / 12 : ℝ) + ε / 2) * X ^ (-(ε / 2)) = X ^ (7 / 12 : ℝ) := by
  rw [← Real.rpow_add (by linarith : (0 : ℝ) < X)]
  congr 1
  ring

end LeanLab.KumchevLiu2007.Task507
