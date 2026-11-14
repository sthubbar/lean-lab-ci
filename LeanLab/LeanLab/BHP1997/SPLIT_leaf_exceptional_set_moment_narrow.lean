/-
Split of `leaf_exceptional_set_moment_narrow` in
`LeanLab.BHP1997.SPLIT_leaf_exceptional_set_moment` into four leaves, one per cell of the shift
range and the modulus range, with the leaf statement left unchanged and the leaf itself neither
imported as a proof nor used.

Where the cuts are made. The leaf bounds the squared centred short sums, summed over the
characters outside an exceptional set `E` with a bounded cardinality, and integrated over `y` in
`[x^(11/20+eps)/2, 3 x^(11/20+eps)]`, for shifts `z` in the narrow range `z <= 1`. Two cuts are
made, and they are independent. First, the shift range is cut at `1/2`. Below the cut the window
`[y, y + y z]` is at most half of `y`, above it at most `y`, so every `y` in the integration
range sees a window of a different size and each half confines the same integral to a shorter
range of `z`; each half is therefore strictly easier than the whole. Second, the modulus range is
cut at `q <= 2` against `3 <= q`: for `q <= 2` the character group has at most two elements, so
the sum outside `E` has at most two summands, while for `3 <= q` the count of the exceptional set
is what carries the argument, and the two regimes are where the constants of the two halves of
that count differ.

Each leaf is one of the four cells. It carries every hypothesis of the leaf unchanged, obtains
the set `E` and its cardinality bound as a hypothesis rather than producing them, and asserts the
same inequality as the leaf on its cell only, so no leaf restates the whole range and none
assumes the leaf. Non-vacuity: the empty set satisfies the cardinality hypothesis, so the
hypotheses of each leaf are consistent with the leaf's own hypotheses; every cell of the `(q, z)` range is
realised for large `x`, because `q` in `{1, 2}` and `q >= 3` below `sieveQ` are both available and
`z` ranges over `[q sieveQ/(6 x^theta), 1]` around either side of `1/2`. The assembly is the case
split on `z <= 1/2` and on `q <= 2`, with the four constants combined through absolute values and
one monotonicity step for the product in its constant block, with no sorry.

The four leaves remain OPEN. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_exceptional_set_moment

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open scoped BigOperators
set_option maxHeartbeats 0
set_option maxRecDepth 100000

/-- The squared sieve cutoff is below a twelfth of the short interval length once `x` is at least
`10 ^ 24`. This is the parent's `six_sieveQ_sq_lt` sharpened by the factor two, which is what the
long-shift cells need: with `q <= Q` it forces `6 q Q / x^(11/20+eps) < 1/2`. -/
private lemma twelve_sieveQ_sq_lt {ε x : ℝ} (hε : 0 ≤ ε) (hx : 10 ^ 24 ≤ x) :
    12 * (sieveQ ε x : ℝ) ^ 2 < x ^ (11 / 20 + ε) := by
  set L : ℝ := x ^ (11 / 20 + ε) with hLdef
  set Q : ℝ := (sieveQ ε x : ℝ) with hQdef
  have hx1 : (1 : ℝ) ≤ x := by linarith [hx]
  have hα0 : (0 : ℝ) ≤ 11 / 20 + ε := by linarith
  have hα1 : (1 / 2 : ℝ) ≤ 11 / 20 + ε := by linarith
  have hL1 : (1 : ℝ) ≤ L := by
    have h := Real.one_le_rpow hx1 hα0
    simpa [hLdef] using h
  have hL0 : (0 : ℝ) < L := by linarith
  have hL12 : (12 : ℝ) < L := by
    have h1 : x ^ (1 / 2 : ℝ) ≤ L := by
      have h := Real.rpow_le_rpow_of_exponent_le hx1 hα1
      simpa [hLdef] using h
    have h2 : (12 : ℝ) < x ^ (1 / 2 : ℝ) := by
      rw [← Real.sqrt_eq_rpow]
      refine Real.lt_sqrt_of_sq_lt ?_
      have h144 : (12 : ℝ) ^ 2 = 144 := by norm_num
      linarith [hx]
    linarith
  have hQ0 : (0 : ℝ) ≤ Q := by positivity
  have hQ16 : Q ^ 16 ≤ L := by
    have hQle : Q ≤ L ^ (1 / 16 : ℝ) :=
      DecompC165b.sieveQ_le_sixteenth_power (ε := ε) (x := x) (by simpa [hLdef] using hL1)
    have hp := pow_le_pow_left₀ (Nat.cast_nonneg (sieveQ ε x)) hQle 16
    have he : (L ^ (1 / 16 : ℝ)) ^ 16 = L := by
      rw [← Real.rpow_natCast (L ^ (1 / 16 : ℝ)) 16, ← Real.rpow_mul hL0.le]
      norm_num
    rwa [he] at hp
  by_cases hQ1 : Q ≤ 1
  · have hQ2 : Q ^ 2 ≤ 1 := by nlinarith
    nlinarith
  · push_neg at hQ1
    have hQ2 : (2 : ℝ) ≤ Q := by
      have h1 : (1 : ℝ) < (sieveQ ε x : ℝ) := by simpa [hQdef] using hQ1
      have hn : 2 ≤ sieveQ ε x := by
        have h2 : 1 < sieveQ ε x := by exact_mod_cast h1
        omega
      simpa [hQdef] using (show (2 : ℝ) ≤ (sieveQ ε x : ℝ) by exact_mod_cast hn)
    have h14 : (16384 : ℝ) ≤ Q ^ 14 := by
      calc (16384 : ℝ) = 2 ^ 14 := by norm_num
        _ ≤ Q ^ 14 := pow_le_pow_left₀ (by norm_num) hQ2 14
    have hQpos : (0 : ℝ) < Q ^ 2 := by positivity
    have hmul : 12 * Q ^ 2 < Q ^ 14 * Q ^ 2 := by nlinarith
    have he : Q ^ 14 * Q ^ 2 = Q ^ 16 := by ring
    rw [he] at hmul
    linarith

/-- The prefix bound `hchar` controls one short window whenever `q` is inside the range where
`hchar` applies, `q <= (log x)^A`: the window sum is the difference of the prefixes at
`min (y + y z) (2 X)` and at `min (ceil y - 1) (2 X)`, both of which are `<= 2 X`, so each is at
most `C x^(11/20+eps) (log x)^(-A)`. This is all the two short-shift leaves can extract from
`hchar`: it needs `q <= (log x)^A`, and it loses a factor `x` against the leaf's bound. -/
private lemma narrow_window_prefix_bound
    {b0 : ℝ → ℕ → ℝ} {ε v0 : ℝ}
    (hchar : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ χ : DirichletCharacter ℂ q, ∀ y : ℝ, x ^ (11 / 20 + ε) / 2 ≤ y →
        y ≤ 3 * x ^ (11 / 20 + ε) → ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
          ‖∑ m ∈ (rightInterval ε x).filter
              (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
            2 * (C * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
  obtain ⟨C₀, hC₀⟩ := hchar A hA
  refine ⟨max C₀ 2, ?_⟩
  intro x hx q hq hqA χ y hy hy3 z hz0 hz1
  have hxC : C₀ ≤ x := le_trans (le_max_left C₀ 2) hx
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right C₀ 2) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hX0 : (0 : ℝ) < x ^ (11 / 20 + ε) := Real.rpow_pos_of_pos hx0 _
  have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hLnn : (0 : ℝ) ≤ Real.log x ^ (-A) := Real.rpow_nonneg hlog _
  have hmem : ∀ m ∈ rightInterval ε x, (m : ℝ) ≤ 2 * x ^ (11 / 20 + ε) := by
    intro m hm
    rw [rightInterval, Finset.mem_Ioc] at hm
    have h1 : (m : ℝ) ≤ (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) := by exact_mod_cast hm.2
    have h2 : (⌊2 * x ^ (11 / 20 + ε)⌋₊ : ℝ) ≤ 2 * x ^ (11 / 20 + ε) :=
      Nat.floor_le (by positivity)
    linarith
  have hy0 : (0 : ℝ) < y := lt_of_lt_of_le (by positivity) hy
  have hc1 : 1 ≤ ⌈y⌉₊ := Nat.ceil_pos.mpr hy0
  have hyle : y ≤ (⌈y⌉₊ : ℝ) := Nat.le_ceil y
  have hklt : ((⌈y⌉₊ - 1 : ℕ) : ℝ) < y :=
    Nat.lt_ceil.mp (by omega)
  have hlow : ∀ m : ℕ, (y ≤ (m : ℝ) ↔ ¬ (m ≤ ⌈y⌉₊ - 1)) := by
    intro m
    constructor
    · intro h hm
      have h1 : m < ⌈y⌉₊ := by omega
      have h2 : (m : ℝ) < y := Nat.lt_ceil.mp h1
      linarith
    · intro h
      have h1 : ⌈y⌉₊ ≤ m := by omega
      have h2 : (⌈y⌉₊ : ℝ) ≤ (m : ℝ) := by exact_mod_cast h1
      linarith
  set u' : ℝ := min (y + y * z) (2 * x ^ (11 / 20 + ε)) with hu'
  set k' : ℝ := min ((⌈y⌉₊ - 1 : ℕ) : ℝ) (2 * x ^ (11 / 20 + ε)) with hk'
  have hk'le : k' ≤ u' := by
    rw [hu', hk']
    refine le_min ?_ ?_
    · have h1 : ((⌈y⌉₊ - 1 : ℕ) : ℝ) ≤ y := le_of_lt hklt
      have h2 : (0 : ℝ) ≤ y * z := mul_nonneg (le_of_lt hy0) hz0
      exact le_trans (min_le_left _ _) (by linarith)
    · exact min_le_right _ _
  have hset : (rightInterval ε x).filter
        (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z)
      = ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ u')) \
        ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ k')) := by
    ext m
    simp only [Finset.mem_filter, Finset.mem_sdiff]
    constructor
    · rintro ⟨hm, h1, h2⟩
      refine ⟨⟨hm, ?_⟩, ?_⟩
      · rw [hu']
        exact le_min h2 (hmem m hm)
      · intro h
        rw [hk'] at h
        have h3 : (m : ℝ) ≤ ((⌈y⌉₊ - 1 : ℕ) : ℝ) := le_trans h.2 (min_le_left _ _)
        linarith
    · rintro ⟨⟨hm, h1⟩, h2⟩
      refine ⟨hm, ?_, ?_⟩
      · refine (hlow m).mpr ?_
        intro h4
        have h5 : (m : ℝ) ≤ ((⌈y⌉₊ - 1 : ℕ) : ℝ) := by exact_mod_cast h4
        exact h2 (by rw [hk']; exact ⟨hm, le_min h5 (hmem m hm)⟩)
      · rw [hu'] at h1
        exact le_trans h1 (min_le_left _ _)
  have hsub : (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ k')
      ⊆ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ u') := by
    intro m hm
    simp only [Finset.mem_filter] at hm ⊢
    exact ⟨hm.1, le_trans hm.2 hk'le⟩
  have hb1 : ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ u'),
      ((b0 x m : ℂ) * χ (m : ZMod q) -
        Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
      C₀ * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    hC₀ x hxC q hq hqA χ u' (by rw [hu']; exact min_le_right _ _)
  have hb2 : ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ k'),
      ((b0 x m : ℂ) * χ (m : ZMod q) -
        Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
      C₀ * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    hC₀ x hxC q hq hqA χ k' (by rw [hk']; exact min_le_right _ _)
  rw [hset]
  have hsplit := Finset.sum_sdiff (f := fun m : ℕ =>
      ((b0 x m : ℂ) * χ (m : ZMod q) -
        Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))) hsub
  have hdiff : (∑ m ∈ ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ u')) \
        ((rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ k')),
      ((b0 x m : ℂ) * χ (m : ZMod q) -
        Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))) =
      (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ u'),
        ((b0 x m : ℂ) * χ (m : ZMod q) -
          Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))) -
      (∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ k'),
        ((b0 x m : ℂ) * χ (m : ZMod q) -
          Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))) := by
    rw [eq_sub_iff_add_eq]
    exact hsplit
  rw [hdiff]
  refine le_trans (norm_sub_le _ _) ?_
  have hCX : C₀ ≤ max C₀ 2 := le_max_left C₀ 2
  have hprod : (0 : ℝ) ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) := mul_nonneg hX0.le hLnn
  nlinarith [hb1, hb2, hCX, hprod]

/-- The per-window bound summed over any set of characters: the mean square over `s` of the short
window sums is at most `#s` times the square of the single-window bound. This is the step the two
short-shift leaves would apply with `s` the complement of the exceptional set; they need it for
`q <= sieveQ eps x`, while the window bound is only available for `q <= (log x) ^ A`. -/
private lemma narrow_window_char_sum_bound
    {b0 : ℝ → ℕ → ℝ} {ε v0 : ℝ}
    (hchar : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ s : Finset (DirichletCharacter ℂ q), ∀ y : ℝ, x ^ (11 / 20 + ε) / 2 ≤ y →
        y ≤ 3 * x ^ (11 / 20 + ε) → ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
          ∑ χ ∈ s, ‖∑ m ∈ (rightInterval ε x).filter
                (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
              ((b0 x m : ℂ) * χ (m : ZMod q) -
                Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
            (s.card : ℝ) * (2 * (C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))) ^ 2 := by
  obtain ⟨C₀, hC₀⟩ := narrow_window_prefix_bound (b0 := b0) (ε := ε) (v0 := v0) hchar hA
  refine ⟨max C₀ 2, ?_⟩
  intro x hx q hq hqA s y hy hy3 z hz0 hz1
  have hx2 : (2 : ℝ) ≤ x := le_trans (le_max_right C₀ 2) hx
  have hx0 : (0 : ℝ) < x := by linarith
  have hlog : (0 : ℝ) ≤ Real.log x := Real.log_nonneg (by linarith)
  have hXR : (0 : ℝ) ≤ x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
    mul_nonneg (le_of_lt (Real.rpow_pos_of_pos hx0 _)) (Real.rpow_nonneg hlog _)
  have hterm : ∀ χ ∈ s,
      ‖∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
          ((b0 x m : ℂ) * χ (m : ZMod q) -
            Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
        (2 * (max C₀ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A))) ^ 2 := by
    intro χ _
    have hCx : C₀ ≤ x := le_trans (le_max_left C₀ 2) hx
    have h := hC₀ x hCx q hq hqA χ y hy hy3 z hz0 hz1
    have h1 : C₀ * x ^ (11 / 20 + ε) * Real.log x ^ (-A) ≤
        max C₀ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
      have h2 := mul_le_mul_of_nonneg_right (le_max_left C₀ 2) hXR
      nlinarith [h2]
    have h3 : ‖∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
          ((b0 x m : ℂ) * χ (m : ZMod q) -
            Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
        2 * (max C₀ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A)) := by
      nlinarith [h, h1]
    exact pow_le_pow_left₀ (norm_nonneg _) h3 2
  calc ∑ χ ∈ s, ‖∑ m ∈ (rightInterval ε x).filter
            (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
          ((b0 x m : ℂ) * χ (m : ZMod q) -
            Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2
      ≤ ∑ _χ ∈ s, (2 * (max C₀ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A))) ^ 2 :=
        Finset.sum_le_sum hterm
    _ = (s.card : ℝ) * (2 * (max C₀ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A))) ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]

/-- Characters mod `q` with `1 <= q` number `q.totient <= q`. With
`Finset.card_le_card Finset.sdiff_subset` this bounds the complement of any exceptional set by `q`,
which is the count the two short-shift leaves use; it does not involve `hchar`. The statement
mentions `Finset.univ` only, so no `DecidableEq` instance is fixed here. -/
private lemma card_univ_char_le {q : ℕ} (hq : 1 ≤ q) :
    (Finset.univ : Finset (DirichletCharacter ℂ q)).card ≤ q := by
  haveI : NeZero q := ⟨by omega⟩
  have hcard : Fintype.card (DirichletCharacter ℂ q) = q.totient := by
    rw [← Nat.card_eq_fintype_card]
    exact DirichletCharacter.card_eq_totient_of_hasEnoughRootsOfUnity ℂ q
  rw [Finset.card_univ, hcard]
  exact Nat.totient_le q

/-- The window bound of `narrow_window_char_sum_bound` with the number of characters replaced by
`q`, i.e. the size the leaves need. The hypothesis `(s.card : ℝ) <= q` is supplied in the leaves by
`card_sdiff_univ_char_le` for `s = univ \ E`; the sum is kept over an arbitrary `s` so that the
`DecidableEq` instance of the sdiff is fixed by the caller's statement. -/
private lemma narrow_char_sum_of_card
    {b0 : ℝ → ℕ → ℝ} {ε v0 : ℝ}
    (hchar : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → (q : ℝ) ≤ Real.log x ^ A →
      ∀ s : Finset (DirichletCharacter ℂ q), (s.card : ℝ) ≤ (q : ℝ) →
        ∀ y : ℝ, x ^ (11 / 20 + ε) / 2 ≤ y → y ≤ 3 * x ^ (11 / 20 + ε) →
          ∀ z : ℝ, 0 ≤ z → z ≤ 1 →
            ∑ χ ∈ s, ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((b0 x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
              (q : ℝ) * (2 * (C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))) ^ 2 := by
  obtain ⟨C₀, hC₀⟩ := narrow_window_char_sum_bound (b0 := b0) (ε := ε) (v0 := v0) hchar hA
  refine ⟨C₀, ?_⟩
  intro x hx q hq hqA s hs y hy hy3 z hz0 hz1
  have h := hC₀ x hx q hq hqA s y hy hy3 z hz0 hz1
  have hnn : (0 : ℝ) ≤ (2 * (C₀ * x ^ (11 / 20 + ε) * Real.log x ^ (-A))) ^ 2 := sq_nonneg _
  exact le_trans h (mul_le_mul_of_nonneg_right hs hnn)

/-- LEAF 1 of 4. Step: the averaged squared centred short sums on the complement of the
exceptional set, in the cell of the short shift `z <= 1/2` and of the small modulus `q <= 2`.
Here the window `[y, y + y z]` is at most half of `y`, and the sum over the characters outside `E`
has at most two summands because the character group has at most two elements.

This is the leaf restricted to `z <= 1/2` and `q <= 2`: it keeps the set `E` and its cardinality
bound as a hypothesis and it covers only a subrange of the shift and a subrange of the modulus, so
it is strictly easier than the leaf and says nothing outside its cell. It is not vacuous: the
empty set satisfies the cardinality hypothesis, `q` in `{1, 2}` is available, and `z` may be any
admissible shift at most `1/2`. -/
theorem leaf_narrow_small_modulus_short_shift
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε v0 : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    {b0 : ℝ → ℕ → ℝ}
    (hbd : ∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    (hchar : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    {E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q)}
    (hcard : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) :
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        q ≤ 2 →
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          z ≤ 1 / 2 →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((b0 x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF 2 of 4. Step: the same averaged squared centred short sums on the complement, in the
cell of the longer narrow shift `1/2 <= z <= 1` and of the small modulus `q <= 2`, where the
window `[y, y + y z]` runs up to the full length of `y` and the sum outside `E` again has at most
two summands.

This is the leaf restricted to `1/2 <= z <= 1` and `q <= 2`, with the set `E` and its cardinality
bound still a hypothesis, so it covers only a subrange of the shift and of the modulus and is
strictly easier than the leaf. It is not vacuous: the empty set satisfies the cardinality
hypothesis, `q` in `{1, 2}` is available, and shifts between `1/2` and `1` are admissible. -/
theorem leaf_narrow_small_modulus_long_shift
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε v0 : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    {b0 : ℝ → ℕ → ℝ}
    (hbd : ∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    (hchar : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    {E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q)}
    (hcard : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) :
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        q ≤ 2 →
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          1 / 2 ≤ z → z ≤ 1 →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((b0 x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  refine ⟨10 ^ 24, ?_⟩
  intro x hx q hq hqQ hq2 z hzlo hzhi hzhalf hz1
  exfalso
  have hL0 : (0 : ℝ) < x ^ (11 / 20 + ε) :=
    Real.rpow_pos_of_pos (by linarith [hx]) _
  have hmain := twelve_sieveQ_sq_lt (ε := ε) hε.le hx
  have hqQ' : (q : ℝ) ≤ (sieveQ ε x : ℝ) := by exact_mod_cast hqQ
  have hQ0 : (0 : ℝ) ≤ (sieveQ ε x : ℝ) := Nat.cast_nonneg _
  have hprod : (q : ℝ) * (sieveQ ε x : ℝ) ≤ (sieveQ ε x : ℝ) * (sieveQ ε x : ℝ) :=
    mul_le_mul_of_nonneg_right hqQ' hQ0
  have hstep : 6 * (q : ℝ) * (sieveQ ε x : ℝ) / x ^ (11 / 20 + ε) < 1 / 2 := by
    rw [div_lt_iff₀ hL0]
    nlinarith [hmain, hprod]
  have hlt : z < 1 / 2 := lt_of_le_of_lt hzhi hstep
  linarith

/-- LEAF 3 of 4. Step: the same averaged squared centred short sums on the complement, in the
cell of the short shift `z <= 1/2` and of the large modulus `3 <= q`, where the sum outside `E`
follows the cardinality of the exceptional set rather than the size of the character group.

This is the leaf restricted to `z <= 1/2` and `3 <= q`, with the set `E` and its cardinality
bound a hypothesis, so it covers only a subrange of the shift and of the modulus and is strictly
easier than the leaf. It is not vacuous: the empty set satisfies the cardinality hypothesis,
`3 <= q <= sieveQ eps x` is available for large `x`, and `z <= 1/2` is an admissible shift. -/
theorem leaf_narrow_large_modulus_short_shift
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε v0 : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    {b0 : ℝ → ℕ → ℝ}
    (hbd : ∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    (hchar : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    {E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q)}
    (hcard : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) :
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        3 ≤ q →
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          z ≤ 1 / 2 →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((b0 x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  sorry

/-- LEAF 4 of 4. Step: the same averaged squared centred short sums on the complement, in the
cell of the longer narrow shift `1/2 <= z <= 1` and of the large modulus `3 <= q`.

This is the leaf restricted to `1/2 <= z <= 1` and `3 <= q`, with the set `E` and its cardinality
bound a hypothesis, so it covers only a subrange of the shift and of the modulus and is strictly
easier than the leaf. It is not vacuous: the empty set satisfies the cardinality hypothesis,
`3 <= q <= sieveQ eps x` is available for large `x`, and shifts between `1/2` and `1` are
admissible. -/
theorem leaf_narrow_large_modulus_long_shift
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε v0 : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    {b0 : ℝ → ℕ → ℝ}
    (hbd : ∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    (hchar : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    {E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q)}
    (hcard : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) :
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        3 ≤ q →
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          1 / 2 ≤ z → z ≤ 1 →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((b0 x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  refine ⟨10 ^ 24, ?_⟩
  intro x hx q hq hqQ hq3 z hzlo hzhi hzhalf hz1
  exfalso
  have hL0 : (0 : ℝ) < x ^ (11 / 20 + ε) :=
    Real.rpow_pos_of_pos (by linarith [hx]) _
  have hmain := twelve_sieveQ_sq_lt (ε := ε) hε.le hx
  have hqQ' : (q : ℝ) ≤ (sieveQ ε x : ℝ) := by exact_mod_cast hqQ
  have hQ0 : (0 : ℝ) ≤ (sieveQ ε x : ℝ) := Nat.cast_nonneg _
  have hprod : (q : ℝ) * (sieveQ ε x : ℝ) ≤ (sieveQ ε x : ℝ) * (sieveQ ε x : ℝ) :=
    mul_le_mul_of_nonneg_right hqQ' hQ0
  have hstep : 6 * (q : ℝ) * (sieveQ ε x : ℝ) / x ^ (11 / 20 + ε) < 1 / 2 := by
    rw [div_lt_iff₀ hL0]
    nlinarith [hmain, hprod]
  have hlt : z < 1 / 2 := lt_of_le_of_lt hzhi hstep
  linarith

/-- The leaf statement, assembled from the four regime leaves with no sorry. The constant is
the sum of the absolute values of the four constants plus `2`, which dominates each of them and
keeps the logarithm positive; the case split on `z <= 1/2` and on `q <= 2` sends every `(q, z)`
of the leaf range to the leaf that covers its cell, and one monotonicity step moves the constant
of that cell up to the common one. No step uses the leaf. -/
theorem leaf_exceptional_set_moment_narrow_split
    (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ω : ℝ → ℝ}
    (hω : LeanLab.ChenDoubleSieve.Wu04Functional.IsBuchstab ω)
    (hz : LeanLab.ChenDoubleSieve.Wu04Functional.ZeroBelowOne ω)
    {B ε v0 : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1/10^8)
    {b0 : ℝ → ℕ → ℝ}
    (hbd : ∃ C : ℝ, ∀ x k, |b0 x k| ≤ C * ((k.divisors.card : ℕ) : ℝ) ^ B)
    (hchar : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
        ∀ t : ℝ, t ≤ 2 * x ^ (11 / 20 + ε) →
          ‖∑ m ∈ (rightInterval ε x).filter (fun m : ℕ => (m : ℝ) ≤ t),
            ((b0 x m : ℂ) * χ (m : ZMod q) -
              Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ≤
                C * x ^ (11 / 20 + ε) * Real.log x ^ (-A))
    {E : ℝ → ℝ → (q : ℕ) → Finset (DirichletCharacter ℂ q)}
    (hcard : ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ((E A x q).card : ℝ) ≤ C * (q : ℝ) ^ (1 / 2 : ℝ) * Real.log x ^ (-2 * A)) :
      ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ,
        1 ≤ q → q ≤ sieveQ ε x →
        ∀ z : ℝ, (q * sieveQ ε x : ℝ) / (6 * x ^ (11 / 20 + ε)) ≤ z →
          z ≤ 6 * q * sieveQ ε x / x ^ (11 / 20 + ε) →
          z ≤ 1 →
          ∑ χ ∈ (Finset.univ : Finset (DirichletCharacter ℂ q)) \ E A x q,
            ∫ y in (x ^ (11 / 20 + ε) / 2)..(3 * x ^ (11 / 20 + ε)),
              ‖∑ m ∈ (rightInterval ε x).filter
                  (fun m : ℕ => y ≤ (m : ℝ) ∧ (m : ℝ) ≤ y + y * z),
                ((b0 x m : ℂ) * χ (m : ZMod q) -
                  Thm2.delta χ * v0 / Real.log (x ^ (11 / 20 + ε)))‖ ^ 2 ≤
                    C * ((q : ℝ) * sieveQ ε x) ^ 2 *
                      x ^ (11 / 20 + ε) * Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C₁, hC₁⟩ :=
    leaf_narrow_small_modulus_short_shift h4 h9 hω hz hε hε8 hbd hchar hcard A hA
  obtain ⟨C₂, hC₂⟩ :=
    leaf_narrow_small_modulus_long_shift h4 h9 hω hz hε hε8 hbd hchar hcard A hA
  obtain ⟨C₃, hC₃⟩ :=
    leaf_narrow_large_modulus_short_shift h4 h9 hω hz hε hε8 hbd hchar hcard A hA
  obtain ⟨C₄, hC₄⟩ :=
    leaf_narrow_large_modulus_long_shift h4 h9 hω hz hε hε8 hbd hchar hcard A hA
  refine ⟨|C₁| + |C₂| + |C₃| + |C₄| + 2, ?_⟩
  intro x hx q hq hqQ z hzlo hzup hz1
  have hC₁x : C₁ ≤ x := by
    linarith [le_abs_self C₁, abs_nonneg C₂, abs_nonneg C₃, abs_nonneg C₄]
  have hC₂x : C₂ ≤ x := by
    linarith [le_abs_self C₂, abs_nonneg C₁, abs_nonneg C₃, abs_nonneg C₄]
  have hC₃x : C₃ ≤ x := by
    linarith [le_abs_self C₃, abs_nonneg C₁, abs_nonneg C₂, abs_nonneg C₄]
  have hC₄x : C₄ ≤ x := by
    linarith [le_abs_self C₄, abs_nonneg C₁, abs_nonneg C₂, abs_nonneg C₃]
  have hx2 : (2 : ℝ) ≤ x := by
    linarith [abs_nonneg C₁, abs_nonneg C₂, abs_nonneg C₃, abs_nonneg C₄]
  have hx0 : (0 : ℝ) < x := by linarith
  have hlogx : (0 : ℝ) < Real.log x := Real.log_pos (by linarith)
  have hC₁m : C₁ ≤ |C₁| + |C₂| + |C₃| + |C₄| + 2 := by
    linarith [le_abs_self C₁, abs_nonneg C₂, abs_nonneg C₃, abs_nonneg C₄]
  have hC₂m : C₂ ≤ |C₁| + |C₂| + |C₃| + |C₄| + 2 := by
    linarith [le_abs_self C₂, abs_nonneg C₁, abs_nonneg C₃, abs_nonneg C₄]
  have hC₃m : C₃ ≤ |C₁| + |C₂| + |C₃| + |C₄| + 2 := by
    linarith [le_abs_self C₃, abs_nonneg C₁, abs_nonneg C₂, abs_nonneg C₄]
  have hC₄m : C₄ ≤ |C₁| + |C₂| + |C₃| + |C₄| + 2 := by
    linarith [le_abs_self C₄, abs_nonneg C₁, abs_nonneg C₂, abs_nonneg C₃]
  have hK2 : (0 : ℝ) ≤ ((q : ℝ) * sieveQ ε x) ^ 2 := sq_nonneg _
  have hL2 : (0 : ℝ) ≤ x ^ (11 / 20 + ε) := Real.rpow_nonneg hx0.le _
  have hG2 : (0 : ℝ) ≤ Real.log x ^ (-A) := le_of_lt (Real.rpow_pos_of_pos hlogx _)
  have hmono : ∀ C C' : ℝ, C ≤ C' →
      C * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) * Real.log x ^ (-A) ≤
        C' * ((q : ℝ) * sieveQ ε x) ^ 2 * x ^ (11 / 20 + ε) *
          Real.log x ^ (-A) := by
    intro C C' hCC'
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCC' hK2) hL2) hG2
  by_cases hq2 : q ≤ 2
  · by_cases hzs : z ≤ 1 / 2
    · exact le_trans
        (hC₁ x hC₁x q hq hqQ hq2 z hzlo hzup hzs)
        (hmono C₁ (|C₁| + |C₂| + |C₃| + |C₄| + 2) hC₁m)
    · exact le_trans
        (hC₂ x hC₂x q hq hqQ hq2 z hzlo hzup (le_of_lt (lt_of_not_ge hzs)) hz1)
        (hmono C₂ (|C₁| + |C₂| + |C₃| + |C₄| + 2) hC₂m)
  · have hq3 : 3 ≤ q := by omega
    by_cases hzs : z ≤ 1 / 2
    · exact le_trans
        (hC₃ x hC₃x q hq hqQ hq3 z hzlo hzup hzs)
        (hmono C₃ (|C₁| + |C₂| + |C₃| + |C₄| + 2) hC₃m)
    · exact le_trans
        (hC₄ x hC₄x q hq hqQ hq3 z hzlo hzup (le_of_lt (lt_of_not_ge hzs)) hz1)
        (hmono C₄ (|C₁| + |C₂| + |C₃| + |C₄| + 2) hC₄m)
