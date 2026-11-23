/-
P0069 Baker Harman Pintz 1997, pages 43, 47, 48 and 53, read from the page images in
papers/P0069-original.pdf. Burst burst-20261122, unit P1122-0089: the route leaf upD_kept_52 of
the branch claude/BHP1997-upper_normalized_raw_conditions_slack-p2, display 5.2 on page 43 for
the kept part of k_m and the principal character, from Lemma 33 on page 48.

The paper's route. Page 53 keeps the terms of k_m for which Lemma 33 applies to some arrangement
of the variables. The proof of Lemma 33 on page 48 ends: "Thus ||LMN||_2^2 << Y L^-A if t is in
[T, T + T2] for (chi, t) in S, which leads directly to (5.1) and (5.2)", where ||.||_2 is the sum
over a well-spaced set S as in Section 3 and T2 = Y/qQ as on page 43. This file cuts that
sentence into three pieces: the bound itself for the kept part, the one LEAF; the passage from
the well-spaced sum to the integral over one block of length T2, PROVED; and the summation over
consecutive blocks against the kernel 1/(T2^2 + t^2) of 5.2, PROVED. Also PROVED, for the
HARD lane: the shift of a block into [-T, T] that Theorem 4 needs. The declaration
kept52_of_leaves has the exact statement of upD_kept_52 and no sorry of its own.

New file, no new definition, no existing statement changed. AI wrote the Lean code.
Goldbach is open.
-/
import LeanLab.BHP1997.UpperShortC165Leaves
import LeanLab.BHP1997.Prep1122KeptWellspacedSplit52

namespace LeanLab.BHP1997.DecompC165d
open Classical Complex Decomp132 DecompC165b
open MeasureTheory

/-- P0069 page 48, end of the proof of Lemma 33, "||LMN||_2^2 << Y L^-A if t is in
[T, T + T2]", read for the kept part of k_m on page 53 and the principal character: a
well-spaced set in one block of length at most T2 = Y/qQ inside T0 <= |t| <= Y has sum of
|K(1/2 + it, chi0)|^2 << Y L^-A. Paper's proof: dyadic split of p1, p2, p3, n4, then Theorem 4
with X = Y^2, using N^2 L, LM, M for R and M^2 N, L^2, N for P1, after a shift by the block
centre. CONDITIONAL on Theorem 4 and Lemma 9; (3.2) on T0 <= |t| also needs a cited
zero-free region, see the notes. Formerly a LEAF, now closed by kept52_wellspaced_split from
the four LEAFs of Prep1122KeptWellspacedSplit52, burst-20261122 WAVE 3. -/
theorem kept52_wellspaced (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      ∀ a b : ℝ, a ≤ b → b - a ≤ x ^ (11 / 20 + ε) / (q * sieveQ ε x) →
      ((Real.exp (Real.log x ^ (1 / 3 : ℝ)) ≤ a ∧ b ≤ x ^ (11 / 20 + ε)) ∨
        (-x ^ (11 / 20 + ε) ≤ a ∧ b ≤ -Real.exp (Real.log x ^ (1 / 3 : ℝ)))) →
      ∀ S : Finset ℝ, (∀ t ∈ S, a ≤ t ∧ t ≤ b) →
        (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) →
        ∑ t ∈ S, ‖∑ m ∈ rightInterval ε x, (upperKept ε (x ^ (11 / 20 + ε)) m : ℂ) *
            (1 : DirichletCharacter ℂ q) (m : ZMod q) /
              (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 ≤
          C * x ^ (11 / 20 + ε) * Real.log x ^ (-A) :=
  kept52_wellspaced_split h4 h9 hε hε8

/-- P0069 Section 3 page 11 and page 48, the passage from a well-spaced sum to an integral
behind "which leads directly to (5.1) and (5.2)" in the proof of Lemma 33. Cut [a, b] into unit
pieces and take a point of maximum of f in each; the points of the even pieces, and those of the
odd pieces, form well-spaced sets, and each piece has length at most 1, so for f continuous and
nonnegative the integral is at most twice any bound V for the well-spaced sums. Elementary real
analysis, no cited input. PROVED. -/
theorem kept52_block_le_two_wellspaced (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    {a b V : ℝ} (hab : a ≤ b)
    (hV : ∀ S : Finset ℝ, (∀ t ∈ S, a ≤ t ∧ t ≤ b) →
      (∀ t ∈ S, ∀ t' ∈ S, t ≠ t' → 1 ≤ |t - t'|) → ∑ t ∈ S, f t ≤ V) :
    ∫ t in a..b, f t ≤ 2 * V := by
  set N := ⌈b - a⌉₊ with hN
  obtain ⟨h, hh⟩ : ∃ h : ℕ → ℝ, ∀ k, h k = min (a + k) b := ⟨_, fun _ => rfl⟩
  have hmono : ∀ k, h k ≤ h (k+1) := fun k => by
    rw [hh, hh]; exact min_le_min_right _ (by push_cast; linarith)
  have hex : ∀ k, ∃ t ∈ Set.Icc (h k) (h (k+1)), IsMaxOn f (Set.Icc (h k) (h (k+1))) t :=
    fun k => isCompact_Icc.exists_isMaxOn (Set.nonempty_Icc.2 (hmono k)) hf.continuousOn
  choose t ht htmax using hex
  have hlt : ∀ k, k < N → a + k < b := fun k hk => by
    have := (Nat.lt_ceil).1 hk; linarith
  have hhk : ∀ k, k < N → h k = a + k := fun k hk => by rw [hh]; exact min_eq_left (hlt k hk).le
  have hh1 : ∀ k, h (k+1) ≤ a + k + 1 := fun k => by
    rw [hh]; exact (min_le_left _ _).trans (by push_cast; linarith)
  have ht_lo : ∀ k, k < N → a + k ≤ t k := fun k hk => by
    have := (ht k).1; rw [hhk k hk] at this; exact this
  have ht_hi : ∀ k, t k ≤ a + k + 1 := fun k => (ht k).2.trans (hh1 k)
  have ht_b : ∀ k, t k ≤ b := fun k => by
    have := (ht k).2; rw [hh] at this; exact this.trans (min_le_right _ _)
  have ht_a : ∀ k, k < N → a ≤ t k := fun k hk => by
    have := ht_lo k hk; have : (0:ℝ) ≤ k := Nat.cast_nonneg k; linarith
  have hsep : ∀ j k, j < N → k < N → j % 2 = k % 2 → j ≠ k → 1 ≤ |t j - t k| := by
    intro j k hj hk hpar hne
    rcases (show j + 2 ≤ k ∨ k + 2 ≤ j by omega) with h2 | h2
    · have : ((j:ℝ)) + 2 ≤ k := by exact_mod_cast h2
      have := ht_lo k hk; have := ht_hi j
      rw [abs_sub_comm, abs_of_nonneg (by linarith)]; linarith
    · have : ((k:ℝ)) + 2 ≤ j := by exact_mod_cast h2
      have := ht_lo j hj; have := ht_hi k
      rw [abs_of_nonneg (by linarith)]; linarith
  have hpart : ∀ s : Finset ℕ, s ⊆ Finset.range N → (∀ j ∈ s, ∀ k ∈ s, j % 2 = k % 2) →
      ∑ k ∈ s, f (t k) ≤ V := by
    intro s hs hp
    have hinj : Set.InjOn t s := by
      intro j hj k hk hjk
      by_contra hne
      have := hsep j k (Finset.mem_range.1 (hs hj)) (Finset.mem_range.1 (hs hk)) (hp j hj k hk) hne
      rw [hjk, sub_self, abs_zero] at this; linarith
    rw [← Finset.sum_image hinj]
    apply hV
    · intro x hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hx
      exact ⟨ht_a k (Finset.mem_range.1 (hs hk)), ht_b k⟩
    · intro x hx y hy hxy
      obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
      obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hy
      exact hsep j k (Finset.mem_range.1 (hs hj)) (Finset.mem_range.1 (hs hk)) (hp j hj k hk)
        (fun e => hxy (e ▸ rfl))
  have hpiece : ∀ k, k < N → ∫ x in h k..h (k+1), f x ≤ f (t k) := by
    intro k hk
    have hle := hmono k
    calc ∫ x in h k..h (k+1), f x ≤ ∫ x in h k..h (k+1), f (t k) :=
          intervalIntegral.integral_mono_on hle (hf.intervalIntegrable _ _) intervalIntegrable_const
            (fun x hx => htmax k hx)
      _ = (h (k+1) - h k) * f (t k) := by simp
      _ ≤ 1 * f (t k) := by
          apply mul_le_mul_of_nonneg_right _ (hf0 _)
          rw [hhk k hk]; have := hh1 k; linarith
      _ = f (t k) := one_mul _
  have hsum : ∫ x in a..b, f x = ∑ k ∈ Finset.range N, ∫ x in h k..h (k+1), f x := by
    rw [intervalIntegral.sum_integral_adjacent_intervals (fun k _ => hf.intervalIntegrable _ _)]
    congr 1
    · rw [hh]; simp [hab]
    · rw [hh]; exact (min_eq_right (by have := Nat.le_ceil (b - a); linarith)).symm
  rw [hsum]
  calc _ ≤ ∑ k ∈ Finset.range N, f (t k) :=
        Finset.sum_le_sum fun k hk => hpiece k (Finset.mem_range.1 hk)
    _ = ∑ k ∈ (Finset.range N).filter (fun k => k % 2 = 0), f (t k) +
          ∑ k ∈ (Finset.range N).filter (fun k => ¬ k % 2 = 0), f (t k) :=
        (Finset.sum_filter_add_sum_filter_not _ _ _).symm
    _ ≤ V + V := by
        apply add_le_add
        · apply hpart _ (Finset.filter_subset _ _)
          intro j hj k hk
          simp only [Finset.mem_filter] at hj hk; omega
        · apply hpart _ (Finset.filter_subset _ _)
          intro j hj k hk
          simp only [Finset.mem_filter] at hj hk; omega
    _ = 2 * V := by ring

/-- The integrand |K(1/2 + it, chi0)|^2 of 5.2 on page 43 is continuous in t, since every m in J
is at least 1, so each m^(1/2 + it) is a nonzero continuous function of t. PROVED. -/
theorem kept52_continuous (ε x : ℝ) (q : ℕ) (c : ℕ → ℝ) :
    Continuous fun t : ℝ => ‖∑ m ∈ rightInterval ε x, (c m : ℂ) *
        (1 : DirichletCharacter ℂ q) (m : ZMod q) /
          (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 := by
  refine (continuous_norm.comp (continuous_finsetSum _ fun m hm => ?_)).pow 2
  have hm0 : (m : ℂ) ≠ 0 := by
    have hpos : 0 < m := by
      unfold rightInterval at hm
      exact lt_of_le_of_lt (Nat.zero_le _) (Finset.mem_Ioc.mp hm).1
    exact_mod_cast hpos.ne'
  have hexp : Continuous fun t : ℝ => (1 / 2 : ℂ) + (t : ℂ) * I :=
    continuous_const.add (Complex.continuous_ofReal.mul continuous_const)
  refine continuous_const.div (hexp.const_cpow (Or.inl hm0)) fun t h => ?_
  exact hm0 ((Complex.cpow_eq_zero_iff _ _).mp h).1

/-- The finite sums of 1/(1 + k^2) are at most 3 - 2/(n + 1). PROVED. -/
theorem kept52_sum_inv_sq (n : ℕ) :
    ∑ k ∈ Finset.range (n + 1), 1 / (1 + (k : ℝ) ^ 2) ≤ 3 - 2 / ((n : ℝ) + 1) := by
  induction n with
  | zero => norm_num
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have key : 1 / (1 + ((n : ℝ) + 1) ^ 2) + 2 / ((n : ℝ) + 1 + 1) ≤ 2 / ((n : ℝ) + 1) := by
      rw [div_add_div _ _ (by positivity) (by positivity),
        div_le_div_iff₀ (by positivity) (by positivity)]
      nlinarith [sq_nonneg (n : ℝ)]
    push_cast
    linarith

/-- The finite sums of 1/(1 + k^2) are at most 3. PROVED. -/
theorem kept52_sum_le_three (n : ℕ) :
    ∑ k ∈ Finset.range n, 1 / (1 + (k : ℝ) ^ 2) ≤ 3 := by
  rcases n with _ | n
  · simp
  · have h := kept52_sum_inv_sq n
    have h2 : 0 ≤ 2 / ((n : ℝ) + 1) := by positivity
    linarith

/-- P0069 page 48, "which leads directly to (5.1) and (5.2)", and display 5.2 on page 43: the
summation of the block bounds over consecutive blocks of length T2 against the kernel
1/(T2^2 + t^2). On the block that starts at T0 + k T2 the kernel is at most 1/(T2^2 (1 + k^2)),
and the sum over k of 1/(1 + k^2) is at most 3. PROVED. -/
theorem kept52_block_sum (f : ℝ → ℝ) (hf : Continuous f) (hf0 : ∀ t, 0 ≤ f t)
    {T0 Y T2 V : ℝ} (hT0 : 0 ≤ T0) (hT2 : 0 < T2) (hV : 0 ≤ V)
    (hblk : ∀ a b : ℝ, T0 ≤ a → a ≤ b → b ≤ Y → b - a ≤ T2 → ∫ t in a..b, f t ≤ V) :
    ∫ t in T0..Y, f t / (T2 ^ 2 + t ^ 2) ≤ 3 * V / T2 ^ 2 := by
  have hwc : Continuous fun t : ℝ => f t / (T2 ^ 2 + t ^ 2) :=
    hf.div (continuous_const.add (continuous_pow 2)) fun t => by positivity
  have hw0 : ∀ t, 0 ≤ f t / (T2 ^ 2 + t ^ 2) := fun t => div_nonneg (hf0 t) (by positivity)
  have hint : ∀ u v : ℝ, IntervalIntegrable (fun t : ℝ => f t / (T2 ^ 2 + t ^ 2)) volume u v :=
    fun u v => hwc.intervalIntegrable u v
  -- one block
  have hpiece : ∀ n : ℕ, ∫ t in min Y (T0 + n * T2)..min Y (T0 + (n + 1 : ℕ) * T2),
      f t / (T2 ^ 2 + t ^ 2) ≤ V / T2 ^ 2 * (1 / (1 + (n : ℝ) ^ 2)) := by
    intro n
    have hrhs : 0 ≤ V / T2 ^ 2 * (1 / (1 + (n : ℝ) ^ 2)) := by positivity
    have hstep : T0 + n * T2 ≤ T0 + (n + 1 : ℕ) * T2 := by
      push_cast; nlinarith
    by_cases hY : Y ≤ T0 + n * T2
    · rw [min_eq_left hY, min_eq_left (hY.trans hstep), intervalIntegral.integral_same]
      exact hrhs
    · push_neg at hY
      rw [min_eq_right hY.le]
      set a := T0 + n * T2 with ha
      set b := min Y (T0 + (n + 1 : ℕ) * T2) with hb
      have hab : a ≤ b := le_min hY.le hstep
      have hbY : b ≤ Y := min_le_left _ _
      have hba : b - a ≤ T2 := by
        have : b ≤ T0 + (n + 1 : ℕ) * T2 := min_le_right _ _
        push_cast at this; linarith
      have ha0 : (n : ℝ) * T2 ≤ a := by rw [ha]; linarith
      have hn0 : 0 ≤ (n : ℝ) * T2 := by positivity
      have hk : 0 < T2 ^ 2 * (1 + (n : ℝ) ^ 2) := by positivity
      calc ∫ t in a..b, f t / (T2 ^ 2 + t ^ 2)
          ≤ ∫ t in a..b, f t / (T2 ^ 2 * (1 + (n : ℝ) ^ 2)) := by
            refine intervalIntegral.integral_mono_on hab (hint a b)
              ((hf.div_const _).intervalIntegrable a b) fun t ht => ?_
            refine div_le_div_of_nonneg_left (hf0 t) hk ?_
            have ht0 : (n : ℝ) * T2 ≤ t := ha0.trans ht.1
            have : ((n : ℝ) * T2) ^ 2 ≤ t ^ 2 := pow_le_pow_left₀ hn0 ht0 2
            nlinarith
        _ = (∫ t in a..b, f t) / (T2 ^ 2 * (1 + (n : ℝ) ^ 2)) :=
            intervalIntegral.integral_div _ _
        _ ≤ V / (T2 ^ 2 * (1 + (n : ℝ) ^ 2)) :=
            div_le_div_of_nonneg_right (hblk a b (by rw [ha]; linarith) hab hbY hba) hk.le
        _ = V / T2 ^ 2 * (1 / (1 + (n : ℝ) ^ 2)) := by
            field_simp
  -- the partial integrals
  have hpart : ∀ n : ℕ, ∫ t in T0..min Y (T0 + n * T2), f t / (T2 ^ 2 + t ^ 2) ≤
      V / T2 ^ 2 * ∑ k ∈ Finset.range n, 1 / (1 + (k : ℝ) ^ 2) := by
    intro n
    induction n with
    | zero =>
      simp only [CharP.cast_eq_zero, zero_mul, add_zero, Finset.range_zero, Finset.sum_empty,
        mul_zero]
      rw [intervalIntegral.integral_symm, neg_nonpos]
      exact intervalIntegral.integral_nonneg (min_le_right _ _) fun t _ => hw0 t
    | succ n ih =>
      rw [← intervalIntegral.integral_add_adjacent_intervals (hint _ _) (hint _ _),
        Finset.sum_range_succ, mul_add]
      exact add_le_add ih (hpiece n)
  -- enough blocks to reach Y
  obtain ⟨n, hn⟩ : ∃ n : ℕ, Y ≤ T0 + n * T2 := by
    obtain ⟨n, hn⟩ := exists_nat_ge ((Y - T0) / T2)
    refine ⟨n, ?_⟩
    rw [div_le_iff₀ hT2] at hn
    linarith
  have h := hpart n
  rw [min_eq_left hn] at h
  calc _ ≤ V / T2 ^ 2 * ∑ k ∈ Finset.range n, 1 / (1 + (k : ℝ) ^ 2) := h
    _ ≤ V / T2 ^ 2 * 3 :=
        mul_le_mul_of_nonneg_left (kept52_sum_le_three n) (by positivity)
    _ = 3 * V / T2 ^ 2 := by ring

/-- P0069 page 53 with Lemma 33 on page 48: display 5.2 on page 43 for the kept part of k_m and
the principal character, the exact statement of upD_kept_52 on the branch
claude/BHP1997-upper_normalized_raw_conditions_slack-p2. From the LEAF kept52_wellspaced, the
PROVED kept52_block_le_two_wellspaced and the PROVED block summation, on each of the two tails
T0 <= t <= Y and -Y <= t <= -T0, the second by t to -t. PROVED from the one LEAF, so
CONDITIONAL on it and on the cited Theorem 4 and Lemma 9. -/
theorem kept52_of_leaves (h4 : Thm4.Theorem4Paper) (h9 : MeanValue132.Lemma9)
    {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 1 / 10 ^ 8) :
    ∀ A : ℝ, 0 < A → ∃ C : ℝ, ∀ x : ℝ, C ≤ x → ∀ q : ℕ, 1 ≤ q → q ≤ sieveQ ε x →
      (∫ t in (-x ^ (11 / 20 + ε))..(-Real.exp (Real.log x ^ (1 / 3 : ℝ))),
          ‖∑ m ∈ rightInterval ε x, (upperKept ε (x ^ (11 / 20 + ε)) m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) +
        (∫ t in (Real.exp (Real.log x ^ (1 / 3 : ℝ)))..(x ^ (11 / 20 + ε)),
          ‖∑ m ∈ rightInterval ε x, (upperKept ε (x ^ (11 / 20 + ε)) m : ℂ) *
              (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2 /
            ((x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2 + t ^ 2)) ≤
        C * (x ^ (11 / 20 + ε) / (x ^ (11 / 20 + ε) / (q * sieveQ ε x)) ^ 2) *
          Real.log x ^ (-A) := by
  intro A hA
  obtain ⟨C, hC⟩ := kept52_wellspaced h4 h9 hε hε8 A hA
  refine ⟨max (12 * max C 0) (max C 1), fun x hx q hq1 hqQ => ?_⟩
  have hxC : C ≤ x := (le_max_left C 1).trans (hx.trans' (le_max_right _ _))
  have hx1 : 1 ≤ x := (le_max_right C 1).trans (hx.trans' (le_max_right _ _))
  have hx0 : 0 < x := lt_of_lt_of_le one_pos hx1
  set Y := x ^ (11 / 20 + ε) with hYdef
  set T0 := Real.exp (Real.log x ^ (1 / 3 : ℝ)) with hT0def
  set T2 := x ^ (11 / 20 + ε) / (q * sieveQ ε x) with hT2def
  set Lg := Real.log x ^ (-A) with hLg
  set F : ℝ → ℝ := fun t => ‖∑ m ∈ rightInterval ε x, (upperKept ε Y m : ℂ) *
      (1 : DirichletCharacter ℂ q) (m : ZMod q) / (m : ℂ) ^ ((1 / 2 : ℂ) + (t : ℂ) * I)‖ ^ 2
    with hFdef
  have hY0 : 0 < Y := Real.rpow_pos_of_pos hx0 _
  have hL0 : 0 ≤ Lg := Real.rpow_nonneg (Real.log_nonneg hx1) _
  have hQ1 : (1 : ℝ) ≤ (sieveQ ε x : ℝ) := by exact_mod_cast hq1.trans hqQ
  have hq1' : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hT2 : 0 < T2 := by rw [hT2def]; positivity
  have hT0 : 0 ≤ T0 := (Real.exp_pos _).le
  have hFc : Continuous F := kept52_continuous ε x q (fun m => upperKept ε Y m)
  have hF0 : ∀ t, 0 ≤ F t := fun t => sq_nonneg _
  set M := max C 0 with hM
  have hV : 0 ≤ 2 * (M * Y * Lg) := by positivity
  -- the block bound from the two leaves
  have hblock : ∀ a b : ℝ, a ≤ b → b - a ≤ T2 →
      ((T0 ≤ a ∧ b ≤ Y) ∨ (-Y ≤ a ∧ b ≤ -T0)) → ∫ t in a..b, F t ≤ 2 * (M * Y * Lg) := by
    intro a b hab hba hrange
    have h1 := kept52_block_le_two_wellspaced F hFc hF0 hab
      (hC x hxC q hq1 hqQ a b hab hba hrange)
    have h2 : C * Y * Lg ≤ M * Y * Lg :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (le_max_left _ _) hY0.le) hL0
    linarith
  -- the positive tail
  have hpos : ∫ t in T0..Y, F t / (T2 ^ 2 + t ^ 2) ≤ 3 * (2 * (M * Y * Lg)) / T2 ^ 2 :=
    kept52_block_sum F hFc hF0 hT0 hT2 hV fun a b ha hab hb hba =>
      hblock a b hab hba (Or.inl ⟨ha, hb⟩)
  -- the negative tail, by t to -t
  have hneg : ∫ t in -Y..-T0, F t / (T2 ^ 2 + t ^ 2) ≤ 3 * (2 * (M * Y * Lg)) / T2 ^ 2 := by
    have hc := intervalIntegral.integral_comp_neg (a := T0) (b := Y)
      (fun t => F t / (T2 ^ 2 + t ^ 2))
    simp only [neg_sq] at hc
    rw [← hc]
    refine kept52_block_sum (fun t => F (-t)) (hFc.comp continuous_neg) (fun t => hF0 _)
      hT0 hT2 hV fun a b ha hab hb hba => ?_
    have hc2 := intervalIntegral.integral_comp_neg (a := a) (b := b) F
    rw [hc2]
    exact hblock (-b) (-a) (by linarith) (by linarith) (Or.inr ⟨by linarith, by linarith⟩)
  have hmain : 3 * (2 * (M * Y * Lg)) / T2 ^ 2 + 3 * (2 * (M * Y * Lg)) / T2 ^ 2 =
      12 * M * (Y / T2 ^ 2) * Lg := by ring
  have hfin : 12 * M * (Y / T2 ^ 2) * Lg ≤ max (12 * M) (max C 1) * (Y / T2 ^ 2) * Lg :=
    mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)) hL0
  calc _ ≤ 3 * (2 * (M * Y * Lg)) / T2 ^ 2 + 3 * (2 * (M * Y * Lg)) / T2 ^ 2 :=
        add_le_add hneg hpos
    _ = 12 * M * (Y / T2 ^ 2) * Lg := hmain
    _ ≤ _ := hfin

/-- P0069 page 48, the step "if t is in [T, T + T2]" in the proof of Lemma 33. Theorem 4 on
page 12 needs its well-spaced set inside [-T, T]; a block of height T is moved there by the
twist of the coefficients by n^(-iT), since the polynomial at 1/2 + i(t + T) equals the twisted
polynomial at 1/2 + it. The twist is multiplicative, so it is the same for every factor of a
product. PROVED. -/
theorem kept52_dirPoly_shift {q : ℕ} (a : ℕ → ℂ) (c₁ c₂ F : ℝ) (χ : DirichletCharacter ℂ q)
    (t T : ℝ) :
    Thm4.dirPoly a c₁ c₂ F χ (Thm4.half (t + T)) =
      Thm4.dirPoly (fun n => a n * (n : ℂ) ^ (-((T : ℂ) * I))) c₁ c₂ F χ (Thm4.half t) := by
  unfold Thm4.dirPoly Thm4.half
  refine Finset.sum_congr rfl fun n _ => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · have h1 : (1 / 2 + ((t + T : ℝ) : ℂ) * I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    have h2 : (1 / 2 + (t : ℂ) * I) ≠ 0 := by
      intro h; have := congrArg Complex.re h; simp at this
    simp only [Nat.cast_zero]
    rw [Complex.zero_cpow h1, Complex.zero_cpow h2, div_zero, div_zero]
  · have hn' : (n : ℂ) ≠ 0 := by exact_mod_cast hn
    have hsplit : (n : ℂ) ^ (1 / 2 + ((t + T : ℝ) : ℂ) * I) =
        (n : ℂ) ^ (1 / 2 + (t : ℂ) * I) * (n : ℂ) ^ ((T : ℂ) * I) := by
      rw [← Complex.cpow_add _ _ hn']; congr 1; push_cast; ring
    have hne1 : (n : ℂ) ^ (1 / 2 + (t : ℂ) * I) ≠ 0 :=
      fun h => hn' ((Complex.cpow_eq_zero_iff _ _).mp h).1
    have hne2 : (n : ℂ) ^ ((T : ℂ) * I) ≠ 0 :=
      fun h => hn' ((Complex.cpow_eq_zero_iff _ _).mp h).1
    simp only []
    rw [hsplit, Complex.cpow_neg]
    field_simp

/-- P0069 page 11, display 3.1 is kept by the twist of kept52_dirPoly_shift, since
|n^(-iT)| is at most 1 for every natural n. PROVED. -/
theorem kept52_coeffBound_shift {a : ℕ → ℂ} {B : ℝ} (ha : Thm4.CoeffBound a B) (T : ℝ) :
    Thm4.CoeffBound (fun n => a n * (n : ℂ) ^ (-((T : ℂ) * I))) B := by
  intro n
  have h1 : ‖(n : ℂ) ^ (-((T : ℂ) * I))‖ ≤ 1 := by
    rcases eq_or_ne n 0 with rfl | hn
    · by_cases hT : T = 0
      · simp [hT]
      · have : -((T : ℂ) * I) ≠ 0 := by
          intro h; apply hT; have := congrArg Complex.im h; simpa using this
        simp [Complex.zero_cpow this]
    · rw [Complex.norm_natCast_cpow_of_pos (Nat.pos_of_ne_zero hn)]
      simp
  calc ‖a n * (n : ℂ) ^ (-((T : ℂ) * I))‖ = ‖a n‖ * ‖(n : ℂ) ^ (-((T : ℂ) * I))‖ := norm_mul _ _
    _ ≤ ‖a n‖ * 1 := mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
    _ ≤ _ := by rw [mul_one]; exact ha n

end LeanLab.BHP1997.DecompC165d
