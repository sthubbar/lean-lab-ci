/-
Split of `leaf_section4Block_upper_block_mean_value` in
LeanLab.BHP1997.SPLIT_leaf_section4Block_mean_value_negative_small. burst-20261122 S84 feed1122, worker A1.

The parent asks for the integral mean value of display 4.1, P0069 page 24, for the
concrete tapered block of pages 26 and 27, at the negative height, over the height range
from T0 to T1, with the sum over the upper half block from x to 2x, in the region the repaired grouping max m n at most 0.46, compare 3.39 and 4.9.

The paper never proves an integral bound directly. Lemma 12, page 27, says "apply
Lemma 10 and 11", and Lemma 10, page 23, delivers the discrete bound 3.9 of page 12,
a sum of absolute values of the polynomial over a well spaced set of heights in the
sense of page 11, with all heights in one dyadic shell `[T/2, T]`, `T0 < T < T1`, as in
3.37. The proof of 3.9 on page 12 opens with "by a simple dyadic argument". The passage
from such shell sums to the integral 4.1 that Lemma 11 consumes is left implicit.
This split proves that passage and leaves only the shell bound open:

* Glue `leaf_section4Block_upper_block_mean_value_discretize`, PROVED: for a continuous nonnegative function, the integral
  over an interval is at most twice its sum over some finite one separated set of
  points of that interval.
* Glue `leaf_section4Block_upper_block_mean_value_dyadic`, PROVED: a sum over a finite set of points of `[1, H]` is at
  most `logb 2 H + 2` times a uniform bound for its sums over dyadic shells.
* LEAF `leaf_section4Block_upper_block_mean_value_well_spaced_shell`, Class HARD, the one open leaf: the bound 3.9 for this block over every
  one separated set of heights of the range lying in one dyadic shell, from Lemma 10
  under its region hypothesis after the decomposition of page 27.
* Glue: continuity in the height and the logarithm count, PROVED.
* Assembly `leaf_section4Block_upper_block_mean_value_split`: the parent statement, binder for binder, from the leaves and
  the glue, with no sorry. The shell leaf is used at `A + 1`, the extra logarithm pays
  for the number of shells, and the constant becomes `8 |C|`.

The parent keeps its own sorry, as this file imports it; folder convention, see
STATEMENTS.md near line 3151. AI wrote the Lean code. Goldbach is open.
-/
import LeanLab.BHP1997.SPLIT_leaf_section4Block_mean_value_negative_small

namespace LeanLab.BHP1997.Decomp528a
open Classical Filter DecompC165b Decomp312c
open scoped BigOperators

/-- Glue, PROVED. The implicit passage from well spaced sums to the integral of display
4.1, P0069 page 24, used on page 27 when Lemma 10 feeds Lemma 11. For a continuous
nonnegative `f` and any reals `a, b`, the integral of `f` from `a` to `b` is at most
twice the sum of `f` over a finite set of points of `[a, b]` any two of which are at
distance at least one: cut into unit pieces, take a maximizer on each, keep the even
or the odd pieces. -/
theorem leaf_section4Block_upper_block_mean_value_discretize (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    (a b : ℝ) :
    ∃ S : Finset ℝ, (∀ t ∈ S, a ≤ t ∧ t ≤ b) ∧
      (∀ t ∈ S, ∀ u ∈ S, t ≠ u → 1 ≤ |t - u|) ∧
      (∫ t in a..b, f t) ≤ 2 * ∑ t ∈ S, f t := by
  rcases le_or_gt b a with hba | hab
  · refine ⟨∅, by simp, by simp, ?_⟩
    rw [intervalIntegral.integral_symm]
    simp only [Finset.sum_empty, mul_zero, neg_nonpos]
    exact intervalIntegral.integral_nonneg hba (fun t _ => hf0 t)
  · set N := ⌈b - a⌉₊ with hN
    set e : ℕ → ℝ := fun r => min (a + r) b with he
    have he_mono : Monotone e := by
      intro r s h
      simp only [he]
      have : (r : ℝ) ≤ s := by exact_mod_cast h
      exact min_le_min_right _ (by linarith)
    have hmax : ∀ r : ℕ, ∃ p ∈ Set.Icc (e r) (e (r + 1)),
        IsMaxOn f (Set.Icc (e r) (e (r + 1))) p := fun r =>
      isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.mpr (he_mono (Nat.le_succ r)))
        hf.continuousOn
    choose p hp hpmax using hmax
    have hlt : ∀ s ∈ Finset.range N, a + (s : ℝ) < b := by
      intro s hs
      have h1 : s < ⌈b - a⌉₊ := Finset.mem_range.mp hs
      have h2 : (s : ℝ) < b - a := Nat.lt_ceil.mp h1
      linarith
    have hes : ∀ s ∈ Finset.range N, e s = a + s := fun s hs =>
      min_eq_left (hlt s hs).le
    have hsplit : (∫ t in a..b, f t) =
        ∑ r ∈ Finset.range N, ∫ t in e r..e (r + 1), f t := by
      rw [intervalIntegral.sum_integral_adjacent_intervals
        (fun r _ => hf.intervalIntegrable _ _)]
      have h0 : e 0 = a := by simp [he, hab.le]
      have hNe : e N = b := by
        simp only [he]
        apply min_eq_right
        have := Nat.le_ceil (b - a)
        linarith
      rw [h0, hNe]
    have hpiece : ∀ r, (∫ t in e r..e (r + 1), f t) ≤ f (p r) := by
      intro r
      have hle := he_mono (Nat.le_succ r)
      have hlen : e (r + 1) - e r ≤ 1 := by
        simp only [he]
        push_cast
        rcases min_cases (a + (r : ℝ)) b with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1]
          have := min_le_left (a + ((r : ℝ) + 1)) b
          linarith
        · rw [h1]
          have := min_le_right (a + ((r : ℝ) + 1)) b
          linarith
      calc (∫ t in e r..e (r + 1), f t) ≤ ∫ t in e r..e (r + 1), f (p r) :=
            intervalIntegral.integral_mono_on hle (hf.intervalIntegrable _ _)
              intervalIntegrable_const (fun t ht => hpmax r ht)
        _ = (e (r + 1) - e r) * f (p r) := by
            simp [intervalIntegral.integral_const, smul_eq_mul]
        _ ≤ 1 * f (p r) := mul_le_mul_of_nonneg_right hlen (hf0 _)
        _ = f (p r) := one_mul _
    -- separation for indices at least two apart
    have hsep : ∀ r ∈ Finset.range N, ∀ s ∈ Finset.range N, r + 2 ≤ s →
        p r + 1 ≤ p s := by
      intro r _ s hs hrs
      have h1 : p r ≤ e (r + 1) := (hp r).2
      have h2 : e (r + 1) ≤ a + ((r + 1 : ℕ) : ℝ) := min_le_left _ _
      have h3 : e s ≤ p s := (hp s).1
      rw [hes s hs] at h3
      have h4 : ((r + 2 : ℕ) : ℝ) ≤ s := by exact_mod_cast hrs
      push_cast at h2 h4
      linarith
    have hmem : ∀ r ∈ Finset.range N, a ≤ p r ∧ p r ≤ b := by
      intro r hr
      constructor
      · have := (hp r).1
        rw [hes r hr] at this
        have : (0 : ℝ) ≤ r := Nat.cast_nonneg r
        linarith
      · exact le_trans (hp r).2 (min_le_right _ _)
    have hgood : ∀ F ⊆ Finset.range N,
        (∀ r ∈ F, ∀ s ∈ F, r ≠ s → r + 2 ≤ s ∨ s + 2 ≤ r) →
        (∀ t ∈ F.image p, a ≤ t ∧ t ≤ b) ∧
        (∀ t ∈ F.image p, ∀ u ∈ F.image p, t ≠ u → 1 ≤ |t - u|) ∧
        ∑ t ∈ F.image p, f t = ∑ r ∈ F, f (p r) := by
      intro F hF hgap
      refine ⟨?_, ?_, ?_⟩
      · intro t ht
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
        exact hmem r (hF hr)
      · intro t ht u hu htu
        obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp ht
        obtain ⟨s, hs, rfl⟩ := Finset.mem_image.mp hu
        have hrs : r ≠ s := fun h => htu (by rw [h])
        rcases hgap r hr s hs hrs with h | h
        · have := hsep r (hF hr) s (hF hs) h
          rw [abs_sub_comm, abs_of_nonneg (by linarith)]
          linarith
        · have := hsep s (hF hs) r (hF hr) h
          rw [abs_of_nonneg (by linarith)]
          linarith
      · apply Finset.sum_image
        intro r hr s hs hrs
        by_contra hne
        rcases hgap r hr s hs hne with h | h
        · have := hsep r (hF hr) s (hF hs) h
          rw [hrs] at this
          linarith
        · have := hsep s (hF hs) r (hF hr) h
          rw [hrs] at this
          linarith
    set E := (Finset.range N).filter (fun r => r % 2 = 0) with hE
    set O := (Finset.range N).filter (fun r => ¬ r % 2 = 0) with hO
    have hEg : ∀ r ∈ E, ∀ s ∈ E, r ≠ s → r + 2 ≤ s ∨ s + 2 ≤ r := by
      intro r hr s hs hrs
      have := (Finset.mem_filter.mp hr).2
      have := (Finset.mem_filter.mp hs).2
      omega
    have hOg : ∀ r ∈ O, ∀ s ∈ O, r ≠ s → r + 2 ≤ s ∨ s + 2 ≤ r := by
      intro r hr s hs hrs
      have := (Finset.mem_filter.mp hr).2
      have := (Finset.mem_filter.mp hs).2
      omega
    have htot : (∫ t in a..b, f t) ≤ ∑ r ∈ E, f (p r) + ∑ r ∈ O, f (p r) := by
      rw [hsplit, hE, hO, Finset.sum_filter_add_sum_filter_not]
      exact Finset.sum_le_sum (fun r _ => hpiece r)
    rcases le_total (∑ r ∈ O, f (p r)) (∑ r ∈ E, f (p r)) with hc | hc
    · obtain ⟨h1, h2, h3⟩ := hgood E (Finset.filter_subset _ _) hEg
      exact ⟨E.image p, h1, h2, by rw [h3]; linarith⟩
    · obtain ⟨h1, h2, h3⟩ := hgood O (Finset.filter_subset _ _) hOg
      exact ⟨O.image p, h1, h2, by rw [h3]; linarith⟩

/-- Glue, PROVED. The dyadic reduction that opens the proof of 3.9, "by a simple dyadic argument
we may suppose", P0069 page 12 after display 3.9, with the shells `|t| ∈ [T/2, T]` of
Lemma 10, page 23 display 3.37. For a nonnegative `g`, `H ≥ 1` and a finite set `S` of
points of `[1, H]`, if every subset of `S` lying in one shell `[T/2, T]` has `g` sum at
most `K`, then the `g` sum over `S` is at most `(logb 2 H + 2) K`. Proof idea: the
point `t` lies in the shell with `T = 2^(j+1)`, `j = ⌊logb 2 t⌋₊`, and `j` takes at
most `logb 2 H + 1` values; `K ≥ 0` from the empty subset. A pure counting
statement. -/
theorem leaf_section4Block_upper_block_mean_value_dyadic (g : ℝ → ℝ) (_hg : ∀ t, 0 ≤ g t) (H K : ℝ) (hH : 1 ≤ H)
    (S : Finset ℝ) (hS : ∀ t ∈ S, 1 ≤ t ∧ t ≤ H)
    (hK : ∀ T : ℝ, ∀ S' ⊆ S, (∀ t ∈ S', T / 2 ≤ t ∧ t ≤ T) → ∑ t ∈ S', g t ≤ K) :
    ∑ t ∈ S, g t ≤ (Real.logb 2 H + 2) * K := by
  have hK0 : 0 ≤ K := by
    have := hK 1 ∅ (Finset.empty_subset _) (by simp)
    simpa using this
  set J := ⌊Real.logb 2 H⌋₊ + 1 with hJ
  let j : ℝ → ℕ := fun t => ⌊Real.logb 2 t⌋₊
  have hmaps : ∀ t ∈ S, j t ∈ Finset.range J := by
    intro t ht
    apply Finset.mem_range.mpr
    have h1 : Real.logb 2 t ≤ Real.logb 2 H :=
      Real.logb_le_logb_of_le (by norm_num) (by linarith [(hS t ht).1]) (hS t ht).2
    have h2 : j t ≤ ⌊Real.logb 2 H⌋₊ := Nat.floor_mono h1
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hfib : ∀ i ∈ Finset.range J, ∑ t ∈ S with j t = i, g t ≤ K := by
    intro i _
    apply hK ((2 : ℝ) ^ ((i : ℝ) + 1)) _ (Finset.filter_subset _ _)
    intro t ht
    obtain ⟨htS, hti⟩ := Finset.mem_filter.mp ht
    have ht1 := (hS t htS).1
    have ht0 : 0 < t := by linarith
    have hl0 : 0 ≤ Real.logb 2 t := Real.logb_nonneg (by norm_num) ht1
    have hlo : (i : ℝ) ≤ Real.logb 2 t := by
      rw [← hti]; exact Nat.floor_le hl0
    have hhi : Real.logb 2 t < (i : ℝ) + 1 := by
      rw [← hti]; exact Nat.lt_floor_add_one _
    have hrt : (2 : ℝ) ^ Real.logb 2 t = t := Real.rpow_logb (by norm_num) (by norm_num) ht0
    constructor
    · have : (2 : ℝ) ^ ((i : ℝ) + 1) / 2 = (2 : ℝ) ^ (i : ℝ) := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one]
        field_simp
      rw [this]
      calc (2 : ℝ) ^ (i : ℝ) ≤ (2 : ℝ) ^ Real.logb 2 t :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hlo
        _ = t := hrt
    · calc t = (2 : ℝ) ^ Real.logb 2 t := hrt.symm
        _ ≤ (2 : ℝ) ^ ((i : ℝ) + 1) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) hhi.le
  calc ∑ i ∈ Finset.range J, ∑ t ∈ S with j t = i, g t
      ≤ ∑ _i ∈ Finset.range J, K := Finset.sum_le_sum hfib
    _ = (J : ℝ) * K := by simp
    _ ≤ (Real.logb 2 H + 2) * K := by
        apply mul_le_mul_of_nonneg_right _ hK0
        have hl0 : 0 ≤ Real.logb 2 H := Real.logb_nonneg (by norm_num) hH
        have := Nat.floor_le hl0
        rw [hJ]; push_cast
        linarith

/-- LEAF: Lemma 10 for this block, the bound 3.9 over one dyadic shell of well spaced
heights. P0069 page 23 Lemma 10 with 3.37 and the repaired grouping max m n at most 0.46, compare 3.39 and 4.9; page 12 display 3.9; page 27,
the block as `M1 N L` summed over dyadic `D`. For every `T` and every finite one
separated set `S` of heights in the parent range and in `[T/2, T]`, the sum over `S` of
the block polynomial norms at `1/2 - i t` is `O (x^(1/2) (log x)^(-A))`, with the
parent threshold, region, coefficient and modulus hypotheses. Smaller than the
parent: no integral and one shell only. Not vacuous: met by the zero family.
Class: HARD -/
theorem leaf_section4Block_upper_block_mean_value_well_spaced_shell
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n →
      max m n ≤ 0.46 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
          ∀ T : ℝ, ∀ S : Finset ℝ,
            (∀ t ∈ S, Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ t ∧ t ≤ x ^ (0.45 - 2 * ε / 3) ∧ T / 2 ≤ t ∧ t ≤ T) →
            (∀ t ∈ S, ∀ u ∈ S, t ≠ u → 1 ≤ |t - u|) →
            (∑ t ∈ S, ‖∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half (-t)‖) ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  sorry

/-- Glue, PROVED. The integrand is continuous in the height: every index is a positive
integer, so `(k : ℂ) ^ Thm4.half (-t)` is a nonvanishing continuous function of `t`,
and the index set is finite. -/
private theorem leaf_section4Block_upper_block_mean_value_summand_continuous (s : Finset ℕ) (c : ℕ → ℂ)
    (hc : ∀ k ∈ s, k ≠ 0) (q : ℕ) (χ : DirichletCharacter ℂ q) :
    Continuous fun t : ℝ =>
      ‖∑ k ∈ s, c k * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖ := by
  refine Continuous.norm (continuous_finsetSum _ ?_)
  intro k hk
  have hk0 : (k : ℂ) ≠ 0 := by
    have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hc k hk
    exact_mod_cast hk'
  have hbase : Continuous fun z : ℂ => (k : ℂ) ^ z := continuous_const_cpow' hk0
  have hhalf : Continuous fun t : ℝ => Thm4.half (-t) := by
    unfold Thm4.half
    fun_prop
  have hden : Continuous fun t : ℝ => (k : ℂ) ^ Thm4.half (-t) := hbase.comp hhalf
  have hne : ∀ t : ℝ, (k : ℂ) ^ Thm4.half (-t) ≠ 0 := fun t =>
    Complex.cpow_ne_zero_iff.mpr (Or.inl hk0)
  exact continuous_const.div hden hne

/-- Glue, PROVED from the dyadic glue. Shell bounds at exponent `A + 1` give the bound at
exponent `A` for a set of heights in `[lo, hi]` with `1 ≤ lo` and `1 ≤ hi ≤ x`: the
number of shells is at most `logb 2 hi + 2 ≤ 4 log x`. -/
private theorem leaf_section4Block_upper_block_mean_value_shells_to_set (g : ℝ → ℝ) (hg : ∀ t, 0 ≤ g t)
    (x lo hi C A : ℝ) (hx1 : 1 ≤ x) (hlog1 : 1 ≤ Real.log x) (hlo1 : 1 ≤ lo)
    (hhi1 : 1 ≤ hi) (hhix : hi ≤ x) (S : Finset ℝ) (hS : ∀ t ∈ S, lo ≤ t ∧ t ≤ hi)
    (hshell : ∀ T : ℝ, ∀ S' ⊆ S, (∀ t ∈ S', T / 2 ≤ t ∧ t ≤ T) →
      ∑ t ∈ S', g t ≤ C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-(A + 1))) :
    ∑ t ∈ S, g t ≤ 4 * |C| * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  have hlogpos : 0 < Real.log x := by linarith
  have hP : 0 ≤ x ^ (1 / 2 : ℝ) * Real.log x ^ (-(A + 1)) :=
    mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg hlogpos.le _)
  have hK : ∀ T : ℝ, ∀ S' ⊆ S, (∀ t ∈ S', T / 2 ≤ t ∧ t ≤ T) →
      ∑ t ∈ S', g t ≤ |C| * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-(A + 1))) := by
    intro T S' hS' hT
    refine (hshell T S' hS' hT).trans ?_
    rw [mul_assoc]
    exact mul_le_mul_of_nonneg_right (le_abs_self _) hP
  have hd := leaf_section4Block_upper_block_mean_value_dyadic g hg hi (|C| * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-(A + 1)))) hhi1 S
    (fun t ht => ⟨hlo1.trans (hS t ht).1, (hS t ht).2⟩) hK
  have hlb : 0 ≤ Real.logb 2 hi := Real.logb_nonneg (by norm_num) hhi1
  have hlb2 : Real.logb 2 hi ≤ 2 * Real.log x := by
    unfold Real.logb
    have hl2 : (1 / 2 : ℝ) < Real.log 2 := by
      have := Real.log_two_gt_d9
      linarith
    have hlh : Real.log hi ≤ Real.log x := Real.log_le_log (by linarith) hhix
    have hlh0 : 0 ≤ Real.log hi := Real.log_nonneg hhi1
    rw [div_le_iff₀ (by linarith)]
    nlinarith
  have hrp : Real.log x * Real.log x ^ (-(A + 1)) = Real.log x ^ (-A) := by
    rw [show -A = 1 + (-(A + 1)) by ring, Real.rpow_add hlogpos, Real.rpow_one]
  calc ∑ t ∈ S, g t ≤ (Real.logb 2 hi + 2) *
        (|C| * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-(A + 1)))) := hd
    _ ≤ (4 * Real.log x) * (|C| * (x ^ (1 / 2 : ℝ) * Real.log x ^ (-(A + 1)))) :=
        mul_le_mul_of_nonneg_right (by linarith) (mul_nonneg (abs_nonneg _) hP)
    _ = 4 * |C| * x ^ (1 / 2 : ℝ) * (Real.log x * Real.log x ^ (-(A + 1))) := by ring
    _ = 4 * |C| * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by rw [hrp]

/-- The assembly, with no sorry. The parent statement binder for binder, from the leaves
above and never from the parent. The threshold is the leaf threshold capped at one half,
so that both ends of the height range are at least one. For each `x, q, χ` the
discretization glue gives a one separated set of heights in the range, the shell leaf
at `A + 1` bounds every shell of it, the dyadic glue adds the shells, and the constant
of the conclusion is `8 |C|`. -/
theorem leaf_section4Block_upper_block_mean_value_split
    (h4 : Thm4.Theorem4Paper) (B : ℝ) (hB : 0 ≤ B) :
    ∃ η : ℝ, 0 < η ∧ ∀ ε : ℝ, 0 < ε → ε < η →
      ∀ m n : ℝ, 0 ≤ m → 0 ≤ n → max m n ≤ 0.46 →
      ∀ a b : ℝ → ℕ → ℝ,
        (∀ x k, |a x k| ≤ (k.divisors.card : ℝ) ^ B) →
        (∀ x k, |b x k| ≤ (k.divisors.card : ℝ) ^ B) →
        ∀ A : ℝ, 0 < A → ∃ C X : ℝ, ∀ x : ℝ, X ≤ x → ∀ q : ℕ,
          1 ≤ q → (q : ℝ) ≤ Real.log x ^ A → ∀ χ : DirichletCharacter ℂ q,
            (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
              ‖∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊,
                (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
                  (k : ℂ) ^ Thm4.half (-t)‖) ≤
            C * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by
  obtain ⟨η, hη, H⟩ := leaf_section4Block_upper_block_mean_value_well_spaced_shell h4 B hB
  refine ⟨min η (1 / 2), lt_min hη (by norm_num), ?_⟩
  intro ε hε hεη m n hm0 hn0 hreg a b ha hb A hA
  have hεη' : ε < η := hεη.trans_le (min_le_left _ _)
  have hε2 : ε < 1 / 2 := hεη.trans_le (min_le_right _ _)
  obtain ⟨C, X, hC⟩ := H ε hε hεη' m n hm0 hn0 hreg a b ha hb (A + 1) (by linarith)
  refine ⟨8 * |C|, max X (Real.exp 1), ?_⟩
  intro x hx q hq hlog χ
  have hxX : X ≤ x := le_trans (le_max_left _ _) hx
  have hxe : Real.exp 1 ≤ x := le_trans (le_max_right _ _) hx
  have hlog1 : 1 ≤ Real.log x := by
    have h := Real.log_le_log (Real.exp_pos 1) hxe
    rwa [Real.log_exp] at h
  have hx1 : 1 ≤ x := le_trans (Real.one_le_exp (by norm_num)) hxe
  have hq' : (q : ℝ) ≤ Real.log x ^ (A + 1) :=
    hlog.trans (Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith))
  have he0 : (0 : ℝ) ≤ (0.45 - 2 * ε / 3) := by linarith
  have he1 : (0.45 - 2 * ε / 3) ≤ 1 := by linarith
  have hhi1 : 1 ≤ x ^ (0.45 - 2 * ε / 3) := Real.one_le_rpow hx1 he0
  have hhix : x ^ (0.45 - 2 * ε / 3) ≤ x :=
    (Real.rpow_le_rpow_of_exponent_le hx1 he1).trans_eq (Real.rpow_one x)
  have hlo1 : 1 ≤ Real.exp (Real.log x ^ (1 / 3 : ℝ)) := Real.one_le_exp (Real.rpow_nonneg (Real.log_nonneg hx1) _)
  obtain ⟨S, hS, hsp, hint⟩ := leaf_section4Block_upper_block_mean_value_discretize
    (fun t : ℝ => ‖∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊,
      (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖)
    (leaf_section4Block_upper_block_mean_value_summand_continuous _ _ (fun k hk => by
      have hk1 := (Finset.mem_Ioc.mp hk).1
      omega) q χ)
    (fun t => norm_nonneg _) (Real.exp (Real.log x ^ (1 / 3 : ℝ))) (x ^ (0.45 - 2 * ε / 3))
  have hsum := leaf_section4Block_upper_block_mean_value_shells_to_set
    (fun t : ℝ => ‖∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊,
      (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) / (k : ℂ) ^ Thm4.half (-t)‖)
    (fun t => norm_nonneg _) x (Real.exp (Real.log x ^ (1 / 3 : ℝ))) (x ^ (0.45 - 2 * ε / 3)) C A hx1 hlog1 hlo1 hhi1 hhix S hS
    (fun T S' hS' hT => hC x hxX q hq hq' χ T S'
      (fun t ht => ⟨(hS t (hS' ht)).1, (hS t (hS' ht)).2, (hT t ht).1, (hT t ht).2⟩)
      (fun t ht u hu htu => hsp t (hS' ht) u (hS' hu) htu))
  calc (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (0.45 - 2 * ε / 3)),
        ‖∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊,
          (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
            (k : ℂ) ^ Thm4.half (-t)‖)
      ≤ 2 * ∑ t ∈ S, ‖∑ k ∈ Finset.Ioc ⌊x⌋₊ ⌊2 * x⌋₊,
          (section4Block ε m n a b x k : ℂ) * χ (k : ZMod q) /
            (k : ℂ) ^ Thm4.half (-t)‖ := hint
    _ ≤ 2 * (4 * |C| * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A)) :=
        mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ = 8 * |C| * x ^ (1 / 2 : ℝ) * Real.log x ^ (-A) := by ring

end LeanLab.BHP1997.Decomp528a
