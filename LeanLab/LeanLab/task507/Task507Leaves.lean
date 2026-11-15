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

The fourth statement bounds the cardinality of one window set by `⌈Y⌉₊`: the `v.1 + v.2 ^ 2 = n`
of display 53 makes `v.1` determine `v.2`, so a window set has no more pairs than the `a`-window
`X - Y ≤ v.1 < X` has integers.

The fifth statement puts a member of a window set in `[X - Y, X + Y)`, the support of the windows
that the paper uses to reduce the range of `epsilon`, and the sixth carries the cardinality bound
through a further filter, which is how it reaches the rough count inside `err53`.

The seventh statement spends the cardinality bound: the sum over one window set, which is the
singular integral of display 53, is at most `⌈Y⌉₊` times a uniform bound on its summands.

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
  set t : ℝ := Real.sqrt Y with ht
  have he : 0 < (7 / 12 : ℝ) + ε / 2 := by linarith
  have hY1 : 1 < Y := by
    rw [hY]
    exact Real.one_lt_rpow (by linarith : 1 < X) he
  have ht1 : 1 < t := by
    rw [ht, Real.lt_sqrt (by norm_num : (0 : ℝ) ≤ 1)]
    norm_num
    exact hY1
  set b : ℕ := ⌈t / 2⌉₊ with hb
  have hb_ge : t / 2 ≤ (b : ℝ) := by
    rw [hb]
    exact Nat.le_ceil (t / 2)
  have hb_lt : (b : ℝ) < t := by
    rcases le_or_gt t 2 with h2 | h2
    · have hble : b ≤ 1 := by
        rw [hb]
        refine Nat.ceil_le.mpr ?_
        push_cast
        linarith
      have hbge : 1 ≤ b := by
        rw [Nat.one_le_iff_ne_zero]
        intro h0
        have h0' : (b : ℝ) = 0 := by exact_mod_cast h0
        linarith
      have hone : b = 1 := le_antisymm hble hbge
      rw [hone]
      push_cast
      linarith
    · have h1 := Nat.ceil_lt_add_one (show (0 : ℝ) ≤ t / 2 by linarith)
      rw [hb]
      linarith
  set a : ℕ := ⌈X⌉₊ - 1 with ha
  have hce : 1 ≤ ⌈X⌉₊ := Nat.one_le_ceil_iff.mpr (by linarith)
  have hcast : (a : ℝ) = (⌈X⌉₊ : ℝ) - 1 := by
    rw [ha]
    push_cast [hce]
    ring
  have haX : (a : ℝ) < X := by
    have h1 : (⌈X⌉₊ : ℝ) < X + 1 := Nat.ceil_lt_add_one (by linarith)
    rw [hcast]
    linarith
  have ha_ge : X - Y ≤ (a : ℝ) := by
    have h1 : X ≤ (⌈X⌉₊ : ℝ) := Nat.le_ceil X
    rw [hcast]
    linarith
  have ha_range : a < ⌊X⌋₊ + 1 := by
    have h1 : ⌈X⌉₊ ≤ ⌊X⌋₊ + 1 := Nat.ceil_le_floor_add_one X
    rw [ha]
    omega
  have hb_range : b < ⌊t⌋₊ + 1 := by
    have h1 : t < (⌊t⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one t
    have h2 : (b : ℝ) < (⌊t⌋₊ : ℝ) + 1 := lt_trans hb_lt h1
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
    · rw [Finset.mem_range, ← ht]
      exact hb_range
    · exact ha_ge
    · exact haX
    · rw [← ht]
      exact hb_ge
    · rw [← ht]
      exact hb_lt
    · rfl
  rw [h] at hmem
  simp at hmem

/-- At most `⌈Y⌉₊` pairs of the display 53 window set belong to one `n`. Two pairs with the same
`v.1` have the same `v.2`, because `v.1 + v.2 ^ 2 = n` forces `v.2 ^ 2 = n - v.1`, so the number
of pairs is at most the number of values of `v.1`, and those live in the `a`-window
`X - Y ≤ v.1 < X`, whose length is `Y`. This is the count that the Chebyshev step over the
window set spends: the sum over `windowPairs X Y n` has at most `⌈Y⌉₊` terms.
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
  have hcard : s.card = (s.image (fun v : ℕ × ℕ => v.1)).card :=
    (Finset.card_image_of_injOn hinj).symm
  have hAne : (s.image (fun v : ℕ × ℕ => v.1)).Nonempty := hne.image _
  have hlo : X - Y ≤ ((s.image (fun v : ℕ × ℕ => v.1)).min' hAne : ℝ) := by
    have hm := (s.image (fun v : ℕ × ℕ => v.1)).min'_mem hAne
    rw [Finset.mem_image] at hm
    obtain ⟨v, hv, hveq⟩ := hm
    simp only [hs, Finset.mem_filter] at hv
    rw [← hveq]
    exact hv.2.1
  have hhi : ((s.image (fun v : ℕ × ℕ => v.1)).max' hAne : ℝ) < X := by
    have hm := (s.image (fun v : ℕ × ℕ => v.1)).max'_mem hAne
    rw [Finset.mem_image] at hm
    obtain ⟨v, hv, hveq⟩ := hm
    simp only [hs, Finset.mem_filter] at hv
    rw [← hveq]
    exact hv.2.2.1
  set A := s.image (fun v : ℕ × ℕ => v.1) with hAdef
  have hsub : A ⊆ Finset.Icc (A.min' hAne) (A.max' hAne) := by
    intro x hx
    exact Finset.mem_Icc.mpr ⟨A.min'_le x hx, A.le_max' x hx⟩
  have hAcard : A.card ≤ A.max' hAne + 1 - A.min' hAne := by
    have h1 := Finset.card_le_card hsub
    rwa [Nat.card_Icc] at h1
  have hcast : ((A.max' hAne + 1 - A.min' hAne : ℕ) : ℝ)
      = (A.max' hAne : ℝ) - (A.min' hAne : ℝ) + 1 := by
    have hmin : A.min' hAne ≤ A.max' hAne + 1 := by
      have h1 : A.min' hAne ≤ A.max' hAne := A.min'_le _ (A.max'_mem hAne)
      omega
    rw [Nat.cast_sub hmin]
    push_cast
    ring
  have hlt : (A.card : ℝ) < Y + 1 := by
    have h1 : (A.card : ℝ) ≤ ((A.max' hAne + 1 - A.min' hAne : ℕ) : ℝ) := by
      exact_mod_cast hAcard
    rw [hcast] at h1
    linarith
  rw [hcard]
  by_contra hcon
  push Not at hcon
  have h1 : (⌈Y⌉₊ : ℝ) + 1 ≤ (A.card : ℝ) := by
    have h2 : ⌈Y⌉₊ + 1 ≤ A.card := hcon
    exact_mod_cast h2
  have h2 : Y ≤ (⌈Y⌉₊ : ℝ) := Nat.le_ceil Y
  linarith

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

end LeanLab.KumchevLiu2007.Task507
